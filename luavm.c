#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdarg.h>
#include <assert.h>
#include <setjmp.h>
#include <time.h>
#include <math.h>
#define LUA_PAGE_SIZE          4096u
#define LUA_FREELIST_BUCKETS   40
#define LUA_MEMCATS            256
#define LUA_UDATA_TAGS         128
#define LUA_MAX_TMNAME         21
#define LUA_MAX_TTNAME         11
#define LUA_MAX_MT             11
#define LUA_STRING_TABLE_SIZE  512
#define LUA_REGISTRY_FREE_MAX  1024
#define LUA_STACK_MAX          256
#ifndef LUAI_GCMETRICS
#define LUAI_GCMETRICS 1
#endif
#define PAGE_CELL_GRANULARITY  16u
#define PAGE_CELL_MAX          (LUA_FREELIST_BUCKETS * PAGE_CELL_GRANULARITY)
typedef uint8_t  u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;
#define LUA_UNUSED(x) ((void)(x))
typedef struct GCObject    GCObject;
typedef struct lua_State   lua_State;
typedef struct global_State global_State;
typedef struct lua_Page    lua_Page;
typedef struct TString     TString;
typedef struct LuaTable    LuaTable;
typedef struct UpVal       UpVal;
typedef struct Proto       Proto;
typedef struct lua_jmpbuf  lua_jmpbuf;
typedef enum {
    LUA_TNIL = 0,
    LUA_TBOOLEAN,
    LUA_TLIGHTUSERDATA,
    LUA_TNUMBER,
    LUA_TVECTOR,
    LUA_TSTRING,
    LUA_TTABLE,
    LUA_TFUNCTION,
    LUA_TUSERDATA,
    LUA_TTHREAD,
    LUA_TBUFFER,
    LUA_TOTALTAGS
} LuaTag;

typedef enum {
    TM_INDEX = 0, TM_NEWINDEX, TM_CALL, TM_ADD, TM_SUB, TM_MUL, TM_DIV,
    TM_MOD, TM_POW, TM_UNM, TM_LT, TM_LE, TM_EQ, TM_CONCAT, TM_LEN,
    TM_TYPE, TM_ITER, TM_TOSTRING, TM_NAME, TM_GC, TM_MODE,
    LUA_TM_COUNT
} TMS;

_Static_assert(LUA_TM_COUNT == LUA_MAX_TMNAME, "TMS count mismatch");

typedef struct {
    union {
        void*     p;
        u64       n;
        int       b;
        GCObject* gc;
    } v;
    u32 tag;
    u32 _pad;
} TValue;

typedef struct { u64 key[4]; } PtrEnc;
static void ptrenc_init(PtrEnc* pe, u64 seed) {
    u64 x = seed;
    for (int i = 0; i < 4; ++i) {
        x += 0x9E3779B97F4A7C15ull;
        u64 z = x;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
        pe->key[i] = z ^ (z >> 31);
    }
}

static inline u64 ptrenc_tweak(const PtrEnc* pe, const void* slot) {
    u64 a = (u64)(uintptr_t)slot;
    a ^= pe->key[0] * 0x9E3779B97F4A7C15ull;
    a  = (a ^ (a >> 30)) * 0xBF58476D1CE4E5B9ull;
    a  = (a ^ (a >> 27)) * 0x94D049BB133111EBull;
    return a ^ (a >> 31);
}

static inline u64 ptrenc_encrypt(const PtrEnc* pe, const void* p, const void* slot) {
    u64 raw = (u64)(uintptr_t)p;
    u64 t   = ptrenc_tweak(pe, slot);
    u64 r   = raw ^ pe->key[0] ^ t;
    r = (r << 13) | (r >> 51);
    r ^= pe->key[1];
    r = (r << 7)  | (r >> 57);
    r ^= pe->key[2];
    r = (r << 17) | (r >> 47);
    r ^= pe->key[3];
    return r;
}

static inline void* ptrenc_decrypt(const PtrEnc* pe, u64 c, const void* slot) {
    u64 r = c ^ pe->key[3];
    r = (r >> 17) | (r << 47);
    r ^= pe->key[2];
    r = (r >> 7)  | (r << 57);
    r ^= pe->key[1];
    r = (r >> 13) | (r << 51);
    u64 t = ptrenc_tweak(pe, slot);
    r ^= pe->key[0] ^ t;
    return (void*)(uintptr_t)r;
}

typedef enum {
    MC_UNKNOWN = 0, MC_GC_OBJECT, MC_STRING, MC_TABLE, MC_FUNCTION,
    MC_USERDATA, MC_THREAD, MC_PAGE, MC_MISC, MC_CATEGORY_COUNT
} MemoryCategory;

static const char* mc_name[MC_CATEGORY_COUNT] = {
    "unknown", "gcobject", "string", "table", "function",
    "userdata", "thread", "page", "misc"
};

struct lua_Page {
    lua_Page* next;
    lua_Page* prev;
    u8*       base;
    u32       used;
    u32       capacity;
    u32       live;
    u32       cells;
    u32       bucket;
    u32       flags;
};

typedef struct {
    lua_Page* pages[LUA_FREELIST_BUCKETS];
} PageAllocator;

static u32 size_to_bucket(size_t sz) {
    if (sz == 0) sz = 1;
    u32 b = (u32)((sz + PAGE_CELL_GRANULARITY - 1) / PAGE_CELL_GRANULARITY);
    if (b >= LUA_FREELIST_BUCKETS) b = LUA_FREELIST_BUCKETS - 1;
    return b;
}
static u32 bucket_to_size(u32 bucket) {
    return (bucket + 1) * PAGE_CELL_GRANULARITY;
}

static lua_Page* page_new(PageAllocator* pa, u32 bucket) {
    LUA_UNUSED(pa);
    size_t need = sizeof(lua_Page) + LUA_PAGE_SIZE;
    size_t total = ((need + LUA_PAGE_SIZE - 1) / LUA_PAGE_SIZE) * LUA_PAGE_SIZE;
    lua_Page* pg = NULL;
    u32 flags = 0;
#if defined(__STDC_VERSION__) && __STDC_VERSION__ >= 201112L
    pg = (lua_Page*)aligned_alloc(LUA_PAGE_SIZE, total);
#endif
    if (!pg) {
        void* raw = malloc(total + LUA_PAGE_SIZE);
        if (!raw) return NULL;
        uintptr_t a = ((uintptr_t)raw + LUA_PAGE_SIZE - 1) & ~(uintptr_t)(LUA_PAGE_SIZE - 1);
        ((void**)a)[-1] = raw;
        pg = (lua_Page*)a;
        flags |= 1u;
    }
    memset(pg, 0, sizeof(lua_Page));
    pg->base = (u8*)pg + sizeof(lua_Page);
    uintptr_t b = (uintptr_t)pg->base;
    b = (b + PAGE_CELL_GRANULARITY - 1) & ~(uintptr_t)(PAGE_CELL_GRANULARITY - 1);
    pg->base = (u8*)b;
    pg->bucket = bucket;
    pg->capacity = (u32)((u8*)pg + LUA_PAGE_SIZE - pg->base);
    pg->flags = flags;
    return pg;
}

static void page_free(lua_Page* pg) {
    if (!pg) return;
    if (pg->flags & 1u) {
        void* raw = ((void**)pg)[-1];
        free(raw);
    } else {
        free(pg);
    }
}

typedef enum {
    GC_WHITE0 = 0, GC_WHITE1, GC_GRAY, GC_BLACK, GC_FIXED
} GCColor;

typedef enum {
    GCT_STRING = 1, GCT_TABLE, GCT_FUNCTION, GCT_USERDATA,
    GCT_THREAD, GCT_UPVAL, GCT_PROTO
} GCObjectType;

struct GCObject {
    GCObject* next;
    GCObject* gnext;
    u8        type;
    u8        color;
    u8        memcat;
    u8        flags;
    u32       size;
    void*     data;
    lua_Page* page;
    u32       cell_bucket;
    u32       _pad;
};

struct TString {
    GCObject header;
    TString* next;
    u32      hash;
    u32      len;
    char*    data;
};

typedef struct {
    TString* buckets[LUA_STRING_TABLE_SIZE];
    u32      count;
    u64      bytes;
} stringtable;

typedef struct LuaNode {
    TValue key;
    TValue val;
    struct LuaNode* next;
} LuaNode;

struct LuaTable {
    GCObject header;
    LuaNode** buckets;
    u32       nbuckets;
    u32       count;
    LuaTable* metatable;
    u8        is_weak;
    u8        _pad[3];
};

typedef struct lua_Userdata {
    GCObject header;
    LuaTable* metatable;
    int       tag;
    void*     userdata;
    void      (*destructor)(void*);
    u8        payload[];
} lua_Userdata;

typedef void (*lua_Destructor)(void*);
typedef void (*lua_AllocHook)(void* ud, void* ptr, size_t osize, size_t nsize);
typedef void (*lua_GCHook)(void* ud, int phase);
typedef void (*lua_InterruptHook)(lua_State* L, int gc);
typedef void (*lua_UserdataHook)(lua_State* L, void* ud);
typedef struct {
    lua_AllocHook     onalloc;
    lua_GCHook        ongcstep;
    lua_InterruptHook oninterrupt;
    lua_UserdataHook  onuserdata;
    void*             ud;
} lua_Callbacks;

typedef enum {
    ECB_SCRIPT_BEGIN = 0, ECB_SCRIPT_END, ECB_REQUIRE, ECB_INSTANCE,
    ECB_DEBUG, ECB_ERROR, ECB_COUNT
} ECBSlot;

typedef void (*lua_ECBHandler)(lua_State* L, void* ar, void* ud);

typedef struct {
    lua_ECBHandler handlers[ECB_COUNT];
    void*          ud[ECB_COUNT];
    u32            depth;
} lua_ExecutionCallbacks;

typedef struct {
    int pause;
    int stepmul;
    int stepsize;
    int emergency;
    int minormajor;
} GCParams;

typedef struct {
    u64 collections;
    u64 cycles_completed;
    u64 objects_freed;
    u64 pauses;
    u64 steps;
    u64 finalizers_run;
    u64 weak_clears;
    u64 barriers_back;
    u64 barriers_forward;
} GCStats;

#if LUAI_GCMETRICS
typedef struct {
    u64 phase_ns[8];
    u64 mark_visits;
    u64 sweep_pages;
    u64 promotion_count;
    u64 alloc_count;
    u64 alloc_bytes;
} GCMetrics;
static const char* gc_phase_name[8] = {
    "pause", "propagate", "atomic", "sweep", "finalize", "free", "unknown", "idle"
};
#endif

struct lua_jmpbuf {
    jmp_buf          buf;
    lua_jmpbuf*      prev;
    int              status;
    void           (*unwind)(void*);
    void*            unwind_ud;
};

typedef struct {
    GCObject* gray;
    GCObject* grayagain;
    GCObject* weak;
    GCObject* allgc;
    GCObject* finobj;
    GCObject* tobefnz;
    size_t totalbytes;
    size_t GCthreshold;
    size_t GCdebt;
    size_t GCestimate;
    void*  (*frealloc)(void* ud, void* ptr, size_t osize, size_t nsize);
    void*  alloc_ud;
    stringtable strt;
    lua_State* mainthread;
    UpVal*     uvhead;
    GCParams  gcparams;
    int       gcgoal;
    int       gcstepsize;
    int       gcstepmul;
    u8  currentwhite;
    u8  gcstate;
    u8  gcstop;
    u8  _padding[5];
    lua_Page* sweepgcopage;
    lua_Page* allgcopages;
    lua_Page* allpages;
    lua_Page* freegcopages[LUA_FREELIST_BUCKETS];
    lua_Page* freepages[LUA_FREELIST_BUCKETS];
    LuaTable* mt[LUA_MAX_MT];
    TString*  tmname[LUA_MAX_TMNAME];
    TString*  ttname[LUA_MAX_TTNAME];
    TValue pseudotemp;
    TValue registry;
    int    registryfree;
    u32    registry_slots[LUA_REGISTRY_FREE_MAX];
    PtrEnc ptrenc;
    lua_jmpbuf* errorjmp;
    lua_Callbacks          cb;
    lua_ExecutionCallbacks ecb;
    union {
        max_align_t _align;
        u8 bytes[512];
    } ecbdata;
    size_t          memcatbytes[LUA_MEMCATS];
    lua_Destructor  udatagc[LUA_UDATA_TAGS];
    LuaTable*       udatamt[LUA_UDATA_TAGS];
    TString*        lightuserdataname[LUA_UDATA_TAGS];
    GCStats gcstats;
#if LUAI_GCMETRICS
    GCMetrics gcmetrics;
#endif
    PageAllocator palloc;
    size_t peak_totalbytes;
    u64    allocations;
    u64    frees;
    u64    bytes_freed_total;
    bool   trace;
    FILE*  trace_fp;
} global_State;

typedef enum {
    GCST_PAUSE = 0, GCST_PROPAGATE, GCST_ATOMIC, GCST_SWEEP,
    GCST_FINALIZE, GCST_FREE, GCST_IDLE
} GCState;

typedef struct {
    TValue   val;
    TString* name;
} StackSlot;

struct lua_State {
    GCObject      header;
    global_State* G;
    StackSlot*    stack;
    int           top;
    int           base;
    lua_State*    prev;
    lua_State*    next;
    int           status;
    lua_jmpbuf*   errorjmp;
};

struct UpVal {
    GCObject header;
    TValue*  v;
    TValue   closed;
};

static void* vm_alloc(global_State* G, size_t size, MemoryCategory cat);
static void  vm_free (global_State* G, void* ptr, size_t size, MemoryCategory cat);
static void  gc_step(global_State* G, size_t bytes);
static void  gc_full(global_State* G);
static void  gc_barrier_back(global_State* G, GCObject* o);
static void  gc_barrier_forward(global_State* G, GCObject* o);
static void  gc_mark_value(global_State* G, const TValue* v);
static void  gc_mark_object(global_State* G, GCObject* o);
static void  table_set_raw(global_State* G, LuaTable* t, const TValue* k, const TValue* v);

static u64 now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (u64)ts.tv_sec * 1000000000ull + (u64)ts.tv_nsec;
}

static void* default_frealloc(void* ud, void* ptr, size_t osize, size_t nsize) {
    LUA_UNUSED(ud); LUA_UNUSED(osize);
    if (nsize == 0) { free(ptr); return NULL; }
    return realloc(ptr, nsize);
}

static void* vm_alloc(global_State* G, size_t size, MemoryCategory cat) {
    if (!G->frealloc) G->frealloc = default_frealloc;
    void* p = G->frealloc(G->alloc_ud, NULL, 0, size);
    if (!p) { fprintf(stderr, "vm_alloc: OOM (%zu bytes)\n", size); abort(); }
    G->totalbytes += size;
    if (G->totalbytes > G->peak_totalbytes) G->peak_totalbytes = G->totalbytes;
    G->memcatbytes[cat] += size;
    G->allocations++;
#if LUAI_GCMETRICS
    G->gcmetrics.alloc_count++;
    G->gcmetrics.alloc_bytes += size;
#endif
    if (G->cb.onalloc) G->cb.onalloc(G->cb.ud, NULL, 0, size);

    G->GCdebt += size;
    size_t step = (size_t)1 << G->gcparams.stepsize;
    if (!G->gcstop && G->GCdebt > step) {
        gc_step(G, G->GCdebt);
        G->GCdebt = 0;
    }
    return p;
}

static void vm_free(global_State* G, void* ptr, size_t size, MemoryCategory cat) {
    if (!ptr) return;
    if (!G->frealloc) G->frealloc = default_frealloc;
    G->frealloc(G->alloc_ud, ptr, size, 0);
    G->totalbytes -= size;
    if (G->memcatbytes[cat] >= size) G->memcatbytes[cat] -= size;
    else G->memcatbytes[cat] = 0;
    G->frees++;
    G->bytes_freed_total += size;
    if (G->cb.onalloc) G->cb.onalloc(G->cb.ud, ptr, size, 0);
}

static GCObject* gc_alloc_object(global_State* G, size_t payload_size, GCObjectType type) {
    u32 bucket = size_to_bucket(sizeof(GCObject) + payload_size);
    lua_Page* pg = G->palloc.pages[bucket];
    u32 cell_sz = bucket_to_size(bucket);
    if (!pg || pg->used + cell_sz > pg->capacity) {
        pg = page_new(&G->palloc, bucket);
        if (!pg) return NULL;
        pg->next = G->allpages;
        if (G->allpages) G->allpages->prev = pg;
        G->allpages = pg;
        G->palloc.pages[bucket] = pg;
    }
    GCObject* o = (GCObject*)(pg->base + pg->used);
    pg->used += cell_sz;
    pg->cells++;
    pg->live++;

    memset(o, 0, sizeof(GCObject));
    o->type        = (u8)type;
    o->color       = G->currentwhite;
    o->memcat      = MC_GC_OBJECT;
    o->size        = cell_sz;
    o->page        = pg;
    o->cell_bucket = bucket;
    o->next        = G->allgc;
    G->allgc       = o;

    G->totalbytes += cell_sz;
    if (G->totalbytes > G->peak_totalbytes) G->peak_totalbytes = G->totalbytes;
    G->memcatbytes[MC_PAGE] += cell_sz;
    return o;
}

static inline bool is_black(global_State* G, GCObject* o) {
    return o && (o->color == GC_BLACK ||
                 (o->color != G->currentwhite && o->color != GC_GRAY && o->color != GC_FIXED));
}

static void gc_barrier_back(global_State* G, GCObject* o) {
    if (!o) return;
    if (o->color == GC_BLACK) {
        o->color = GC_GRAY;
        o->gnext = G->grayagain;
        G->grayagain = o;
        G->gcstats.barriers_back++;
    }
}

static void gc_barrier_forward(global_State* G, GCObject* o) {
    if (!o) return;
    if (o->color == G->currentwhite) {
        o->color = GC_GRAY;
        o->gnext = G->gray;
        G->gray = o;
        G->gcstats.barriers_forward++;
    }
}

static void gc_barrier_table(global_State* G, LuaTable* t, const TValue* v) {
    gc_barrier_back(G, (GCObject*)t);
    if (v->tag == LUA_TSTRING || v->tag == LUA_TTABLE || v->tag == LUA_TUSERDATA ||
        v->tag == LUA_TFUNCTION || v->tag == LUA_TTHREAD) {
        gc_barrier_forward(G, v->v.gc);
    }
}

static u32 hash_string(const char* s, size_t len) {
    u32 h = 2166136261u;
    for (size_t i = 0; i < len; ++i) { h ^= (u8)s[i]; h *= 16777619u; }
    return h;
}

static TString* string_new(global_State* G, const char* s, size_t len) {
    u32 h = hash_string(s, len);
    u32 idx = h & (LUA_STRING_TABLE_SIZE - 1);
    for (TString* t = G->strt.buckets[idx]; t; t = t->next) {
        if (t->hash == h && t->len == len && memcmp(t->data, s, len) == 0) return t;
    }
    GCObject* o = gc_alloc_object(G, sizeof(TString), GCT_STRING);
    if (!o) return NULL;
    TString* t = (TString*)o;
    t->header.data = t;
    t->hash = h;
    t->len  = (u32)len;
    t->data = (char*)vm_alloc(G, len + 1, MC_STRING);
    memcpy(t->data, s, len);
    t->data[len] = '\0';
    t->next = G->strt.buckets[idx];
    G->strt.buckets[idx] = t;
    G->strt.count++;
    G->strt.bytes += len + 1;
    return t;
}

static u32 hash_tvalue(const TValue* v) {
    switch (v->tag) {
        case LUA_TNIL:     return 0;
        case LUA_TBOOLEAN: return (u32)v->v.b * 2654435761u;
        case LUA_TNUMBER:  { u64 n; memcpy(&n, &v->v.n, 8); return (u32)(n * 2654435761u); }
        case LUA_TSTRING:  return ((TString*)v->v.gc)->hash;
        default:           return (u32)((uintptr_t)v->v.p * 2654435761u);
    }
}

static bool tvalue_equal(const TValue* a, const TValue* b) {
    if (a->tag != b->tag) return false;
    switch (a->tag) {
        case LUA_TNIL:     return true;
        case LUA_TBOOLEAN: return a->v.b == b->v.b;
        case LUA_TNUMBER:  return a->v.n == b->v.n;
        case LUA_TSTRING:  return a->v.gc == b->v.gc;
        default:           return a->v.p == b->v.p;
    }
}

static LuaTable* table_new(global_State* G, u32 nbuckets) {
    GCObject* o = gc_alloc_object(G, sizeof(LuaTable), GCT_TABLE);
    if (!o) return NULL;
    LuaTable* t = (LuaTable*)o;
    t->header.data = t;
    if (nbuckets < 4) nbuckets = 4;
    u32 p = 4; while (p < nbuckets) p <<= 1;
    t->nbuckets = p;
    t->buckets = (LuaNode**)vm_alloc(G, p * sizeof(LuaNode*), MC_TABLE);
    memset(t->buckets, 0, p * sizeof(LuaNode*));
    return t;
}

static void table_set_raw(global_State* G, LuaTable* t, const TValue* k, const TValue* v) {
    u32 idx = hash_tvalue(k) & (t->nbuckets - 1);
    for (LuaNode* n = t->buckets[idx]; n; n = n->next) {
        if (tvalue_equal(&n->key, k)) { n->val = *v; return; }
    }
    LuaNode* n = (LuaNode*)vm_alloc(G, sizeof(LuaNode), MC_TABLE);
    n->key = *k;
    n->val = *v;
    n->next = t->buckets[idx];
    t->buckets[idx] = n;
    t->count++;
}

static TValue* table_set(global_State* G, LuaTable* t, const TValue* k, const TValue* v) {
    table_set_raw(G, t, k, v);
    gc_barrier_table(G, t, v);
    return NULL;
}

static TValue* table_get(global_State* G, LuaTable* t, const TValue* k) {
    LUA_UNUSED(G);
    u32 idx = hash_tvalue(k) & (t->nbuckets - 1);
    for (LuaNode* n = t->buckets[idx]; n; n = n->next) {
        if (tvalue_equal(&n->key, k)) return &n->val;
    }
    return NULL;
}

static lua_Userdata* udata_new(global_State* G, int tag, size_t payload_size,
                               void (*dtor)(void*)) {
    if (tag < 0 || tag >= LUA_UDATA_TAGS) return NULL;
    GCObject* o = gc_alloc_object(G, sizeof(lua_Userdata) + payload_size, GCT_USERDATA);
    if (!o) return NULL;
    lua_Userdata* u = (lua_Userdata*)o;
    u->header.data = u;
    u->tag = tag;
    u->metatable = G->udatamt[tag];
    u->destructor = dtor ? dtor : G->udatagc[tag];
    u->userdata = u->payload;
    memset(u->payload, 0, payload_size);
    return u;
}

static void cb_set_alloc(global_State* G, lua_AllocHook h, void* ud) {
    G->cb.onalloc = h; G->cb.ud = ud;
}
static void cb_set_gc(global_State* G, lua_GCHook h) { G->cb.ongcstep = h; }
static void cb_set_interrupt(global_State* G, lua_InterruptHook h) { G->cb.oninterrupt = h; }

static void ecb_register(global_State* G, ECBSlot slot, lua_ECBHandler h, void* ud) {
    if (slot >= ECB_COUNT) return;
    G->ecb.handlers[slot] = h;
    G->ecb.ud[slot] = ud;
}
static void ecb_dispatch(global_State* G, ECBSlot slot, lua_State* L, void* ar) {
    if (slot >= ECB_COUNT || !G->ecb.handlers[slot]) return;
    G->ecb.depth++;
    G->ecb.handlers[slot](L, ar, G->ecb.ud[slot]);
    G->ecb.depth--;
}

static void throw_error(global_State* G, const char* msg) {
    if (G->errorjmp) {
        G->errorjmp->status = -1;
        longjmp(G->errorjmp->buf, 1);
    }
    fprintf(stderr, "unrecoverable: %s\n", msg);
    abort();
}

#define VM_TRY(L, name)                                                        \
    lua_jmpbuf name;                                                          \
    name.prev = (L)->G->errorjmp;                                             \
    name.status = 0;                                                          \
    name.unwind = NULL;                                                       \
    name.unwind_ud = NULL;                                                    \
    (L)->G->errorjmp = &name;                                                 \
    if (setjmp(name.buf) == 0)

#define VM_ENDTRY(L, name)                                                     \
    do { (L)->G->errorjmp = name.prev; } while (0)

static void gc_trace(global_State* G, const char* fmt, ...) {
    if (!G->trace || !G->trace_fp) return;
    va_list ap;
    va_start(ap, fmt);
    vfprintf(G->trace_fp, fmt, ap);
    va_end(ap);
    fputc('\n', G->trace_fp);
    fflush(G->trace_fp);
}

#if LUAI_GCMETRICS
#define GCM_TIME_BEGIN(v) do { (v) = now_ns(); } while (0)
#define GCM_TIME_END(phase, t0) do {                                           \
    u64 _t = now_ns();                                                         \
    G->gcmetrics.phase_ns[phase] += _t - (t0);                                 \
} while (0)
#else
#define GCM_TIME_BEGIN(v) do { (v) = 0; } while (0)
#define GCM_TIME_END(phase, t0) do { LUA_UNUSED(phase); LUA_UNUSED(t0); } while (0)
#endif

static inline void mark_gray(global_State* G, GCObject* o, bool again) {
    if (!o) return;
    if (o->color != G->currentwhite && o->color != GC_GRAY) return;
    o->color = GC_GRAY;
    if (again) {
        o->gnext = G->grayagain;
        G->grayagain = o;
    } else {
        o->gnext = G->gray;
        G->gray = o;
    }
}

static inline bool is_collectable(const TValue* v) {
    switch (v->tag) {
        case LUA_TSTRING: case LUA_TTABLE: case LUA_TUSERDATA:
        case LUA_TFUNCTION: case LUA_TTHREAD: return true;
        default: return false;
    }
}

static void gc_mark_value(global_State* G, const TValue* v) {
    if (is_collectable(v)) mark_gray(G, v->v.gc, false);
}

static void gc_mark_object(global_State* G, GCObject* o) {
    if (o) mark_gray(G, o, false);
}

static void traverse_object(global_State* G, GCObject* o) {
    switch (o->type) {
        case GCT_TABLE: {
            LuaTable* t = (LuaTable*)o;
            bool wk = (t->is_weak & 1) != 0;
            bool wv = (t->is_weak & 2) != 0;
            for (u32 i = 0; i < t->nbuckets; ++i) {
                for (LuaNode* n = t->buckets[i]; n; n = n->next) {
                    if (wk) {
                        if (!is_collectable(&n->key) ||
                            n->key.v.gc->color == GC_BLACK) {
                            if (!wv) gc_mark_value(G, &n->val);
                        }
                    } else {
                        gc_mark_value(G, &n->key);
                        if (!wv) gc_mark_value(G, &n->val);
                    }
                }
            }
            if (t->metatable) mark_gray(G, (GCObject*)t->metatable, false);
            break;
        }
        case GCT_USERDATA: {
            lua_Userdata* u = (lua_Userdata*)o;
            if (u->metatable) mark_gray(G, (GCObject*)u->metatable, false);
            break;
        }
        case GCT_THREAD: {
            lua_State* L = (lua_State*)o;
            for (int i = 0; i < L->top; ++i) gc_mark_value(G, &L->stack[i].val);
            break;
        }
        case GCT_UPVAL: {
            UpVal* uv = (UpVal*)o;
            gc_mark_value(G, &uv->closed);
            break;
        }
        case GCT_PROTO: {
            break;
        }
        default: break;
    }
}

static void mark_roots(global_State* G) {
    if (G->mainthread) mark_gray(G, (GCObject*)G->mainthread, false);
    if (G->registry.v.gc) mark_gray(G, G->registry.v.gc, false);
    for (int i = 0; i < LUA_MAX_MT; ++i)
        if (G->mt[i]) mark_gray(G, (GCObject*)G->mt[i], false);
    for (int i = 0; i < LUA_UDATA_TAGS; ++i)
        if (G->udatamt[i]) mark_gray(G, (GCObject*)G->udatamt[i], false);
    for (u32 i = 0; i < LUA_STRING_TABLE_SIZE; ++i)
        for (TString* t = G->strt.buckets[i]; t; t = t->next)
            mark_gray(G, (GCObject*)t, false);
}

static void propagate(global_State* G) {
    while (G->gray) {
        GCObject* o = G->gray;
        G->gray = o->gnext;
        o->gnext = NULL;
        if (o->color == GC_GRAY) {
            o->color = GC_BLACK;
#if LUAI_GCMETRICS
            G->gcmetrics.mark_visits++;
#endif
            traverse_object(G, o);
        }
    }
}

static void clear_weak_table(global_State* G, LuaTable* t) {
    bool wk = (t->is_weak & 1) != 0;
    bool wv = (t->is_weak & 2) != 0;
    u64 cleared = 0;
    for (u32 i = 0; i < t->nbuckets; ++i) {
        LuaNode** pp = &t->buckets[i];
        while (*pp) {
            LuaNode* n = *pp;
            bool dead = false;
            if (wk && is_collectable(&n->key) &&
                n->key.v.gc->color == G->currentwhite) dead = true;
            if (wv && is_collectable(&n->val) &&
                n->val.v.gc->color == G->currentwhite) dead = true;
            if (dead) {
                *pp = n->next;
                vm_free(G, n, sizeof(LuaNode), MC_TABLE);
                if (t->count) t->count--;
                cleared++;
            } else {
                pp = &n->next;
            }
        }
    }
    G->gcstats.weak_clears += cleared;
    gc_trace(G, "[weak] cleared %llu entries", (unsigned long long)cleared);
}

static void atomic_flush(global_State* G) {
    while (G->grayagain) {
        GCObject* o = G->grayagain;
        G->grayagain = o->gnext;
        o->gnext = NULL;
        if (o->color == GC_WHITE0 || o->color == GC_WHITE1) {
            o->color = GC_GRAY;
            mark_gray(G, o, false);
        }
    }
    propagate(G);
    GCObject* wk = G->weak;
    G->weak = NULL;
    while (wk) {
        GCObject* next = wk->gnext;
        wk->gnext = NULL;
        if (wk->type == GCT_TABLE) clear_weak_table(G, (LuaTable*)wk);
        wk = next;
    }
}

static void run_finalizer(global_State* G, GCObject* o) {
    LuaTable* mt = NULL;
    if (o->type == GCT_TABLE) mt = ((LuaTable*)o)->metatable;
    else if (o->type == GCT_USERDATA) mt = ((lua_Userdata*)o)->metatable;
    if (!mt) return;
    TString* gc_name = G->tmname[TM_GC];
    TValue k; k.tag = LUA_TSTRING; k.v.gc = (GCObject*)gc_name;
    TValue* v = table_get(G, mt, &k);
    if (!v || v->tag == LUA_TNIL) return;
    G->gcstats.finalizers_run++;
    gc_trace(G, "[finalize] object %p type=%u", (void*)o, o->type);
}

static void free_object(global_State* G, GCObject* o) {
    if (o->type == GCT_USERDATA) {
        lua_Userdata* u = (lua_Userdata*)o;
        if (u->destructor) u->destructor(u->userdata);
        if (G->cb.onuserdata && G->mainthread)
            G->cb.onuserdata(G->mainthread, u->userdata);
    } else if (o->type == GCT_STRING) {
        TString* t = (TString*)o;
        u32 idx = t->hash & (LUA_STRING_TABLE_SIZE - 1);
        TString** pp = &G->strt.buckets[idx];
        while (*pp && *pp != t) pp = &(*pp)->next;
        if (*pp) *pp = t->next;
        if (G->strt.count) G->strt.count--;
        if (G->strt.bytes >= (u64)t->len + 1) G->strt.bytes -= t->len + 1;
        vm_free(G, t->data, t->len + 1, MC_STRING);
    } else if (o->type == GCT_TABLE) {
        LuaTable* t = (LuaTable*)o;
        for (u32 i = 0; i < t->nbuckets; ++i) {
            LuaNode* n = t->buckets[i];
            while (n) { LuaNode* nx = n->next; vm_free(G, n, sizeof(LuaNode), MC_TABLE); n = nx; }
        }
        vm_free(G, t->buckets, t->nbuckets * sizeof(LuaNode*), MC_TABLE);
    } else if (o->type == GCT_THREAD) {
        lua_State* L = (lua_State*)o;
        if (L->stack) vm_free(G, L->stack, LUA_STACK_MAX * sizeof(StackSlot), MC_THREAD);
    }
    if (o->page) o->page->live--;
    G->gcstats.objects_freed++;
}

static void sweep(global_State* G) {
    u8 dead = G->currentwhite;
    GCObject** pp = &G->allgc;
    u8 nextwhite = (u8)(dead ^ 1);
    for (GCObject* o = G->allgc; o; o = o->next) {
        if (o->color == dead && (o->flags & 1) == 0) {
            run_finalizer(G, o);
            o->flags |= 1;
        }
    }
    while (*pp) {
        GCObject* o = *pp;
        if (o->color == dead && o->color != GC_FIXED) {
            *pp = o->next;
            free_object(G, o);
        } else {
            if (o->color == GC_BLACK) o->color = nextwhite;
            else if (o->color == GC_WHITE0 || o->color == GC_WHITE1)
                o->color = nextwhite;
            pp = &o->next;
        }
    }
#if LUAI_GCMETRICS
    G->gcmetrics.sweep_pages++;
#endif
}

static void page_sweep(global_State* G) {
    lua_Page* pg = G->allpages;
    while (pg) {
        lua_Page* next = pg->next;
        if (pg->live == 0 && pg->cells > 0) {
            if (pg->prev) pg->prev->next = pg->next; else G->allpages = pg->next;
            if (pg->next) pg->next->prev = pg->prev;
            lua_Page** pp = &G->palloc.pages[pg->bucket];
            while (*pp && *pp != pg) pp = &(*pp)->next;
            if (*pp) *pp = pg->next;
            page_free(pg);
        }
        pg = next;
    }
}

static const char* gcstate_name(int s) {
    switch (s) {
        case GCST_PAUSE: return "pause";
        case GCST_PROPAGATE: return "propagate";
        case GCST_ATOMIC: return "atomic";
        case GCST_SWEEP: return "sweep";
        case GCST_FINALIZE: return "finalize";
        case GCST_FREE: return "free";
        case GCST_IDLE: return "idle";
        default: return "?";
    }
}

static void gc_step(global_State* G, size_t bytes) {
    LUA_UNUSED(bytes);
    u64 t0;
    switch (G->gcstate) {
        case GCST_PAUSE: {
            GCM_TIME_BEGIN(t0);
            G->currentwhite ^= 1;
            G->gcstate = GCST_PROPAGATE;
            mark_roots(G);
            G->gcstats.pauses++;
            gc_trace(G, "[gc] pause -> propagate (white=%u)", G->currentwhite);
            GCM_TIME_END(0, t0);
            break;
        }
        case GCST_PROPAGATE: {
            GCM_TIME_BEGIN(t0);
            propagate(G);
            if (!G->gray && !G->grayagain) {
                G->gcstate = GCST_ATOMIC;
                gc_trace(G, "[gc] propagate -> atomic");
            }
            GCM_TIME_END(1, t0);
            break;
        }
        case GCST_ATOMIC: {
            GCM_TIME_BEGIN(t0);
            atomic_flush(G);
            G->gcstate = GCST_SWEEP;
            gc_trace(G, "[gc] atomic -> sweep");
            GCM_TIME_END(2, t0);
            break;
        }
        case GCST_SWEEP: {
            GCM_TIME_BEGIN(t0);
            sweep(G);
            page_sweep(G);
            G->GCestimate = G->totalbytes;
            G->gcstate = GCST_PAUSE;
            G->gcstats.collections++;
            G->gcstats.cycles_completed++;
            gc_trace(G, "[gc] sweep -> pause (live=%zu)", G->totalbytes);
            GCM_TIME_END(3, t0);
            break;
        }
        default:
            G->gcstate = GCST_PAUSE;
            break;
    }
    G->gcstats.steps++;
    if (G->cb.ongcstep) G->cb.ongcstep(G->cb.ud, G->gcstate);
}

static void gc_full(global_State* G) {
    int safety = 0;
    while (safety++ < 100) {
        bool had_white = false;
        for (GCObject* o = G->allgc; o; o = o->next) {
            if (o->color == G->currentwhite) { had_white = true; break; }
        }
        gc_step(G, 0);
        while (G->gcstate != GCST_PAUSE) gc_step(G, 0);
        if (!had_white) break;
    }
    gc_step(G, 0);
    while (G->gcstate != GCST_PAUSE) gc_step(G, 0);
}

static void gc_stop(global_State* G)  { G->gcstop = 1; }
static void gc_start(global_State* G) { G->gcstop = 0; }
static void gc_set_pause(global_State* G, int p)    { if (p >= 0) G->gcparams.pause = p; }
static void gc_set_stepmul(global_State* G, int m)  { if (m > 0)  G->gcparams.stepmul = m; }
static void gc_set_stepsize(global_State* G, int s) {
    if (s < 8) s = 8;
    if (s > 30) s = 30;
    G->gcparams.stepsize = s;
}

static const char* tm_strings[LUA_TM_COUNT] = {
    "__index", "__newindex", "__call", "__add", "__sub", "__mul", "__div",
    "__mod", "__pow", "__unm", "__lt", "__le", "__eq", "__concat", "__len",
    "__type", "__iter", "__tostring", "__name", "__gc", "__mode"
};

static const char* tt_strings[LUA_MAX_TTNAME] = {
    "nil", "boolean", "userdata", "number", "vector",
    "string", "table", "function", "userdata", "thread", "buffer"
};

static void init_caches(global_State* G) {
    for (int i = 0; i < LUA_TM_COUNT; ++i)
        G->tmname[i] = string_new(G, tm_strings[i], strlen(tm_strings[i]));
    for (int i = 0; i < LUA_MAX_TTNAME; ++i)
        G->ttname[i] = string_new(G, tt_strings[i], strlen(tt_strings[i]));
}

static lua_State* state_new(global_State* G) {
    GCObject* o = gc_alloc_object(G, sizeof(lua_State), GCT_THREAD);
    if (!o) return NULL;
    lua_State* L = (lua_State*)o;
    L->header.data = L;
    L->G = G;
    L->stack = (StackSlot*)vm_alloc(G, LUA_STACK_MAX * sizeof(StackSlot), MC_THREAD);
    memset(L->stack, 0, LUA_STACK_MAX * sizeof(StackSlot));
    return L;
}

static global_State* global_new(void) {
    global_State* G = (global_State*)calloc(1, sizeof(global_State));
    if (!G) return NULL;
    G->frealloc = default_frealloc;
    G->alloc_ud = NULL;
    G->gcparams.pause    = 200;
    G->gcparams.stepmul  = 200;
    G->gcparams.stepsize = 17;
    G->gcparams.emergency = 64 * 1024 * 1024;
    G->gcparams.minormajor = 20;
    G->gcgoal     = G->gcparams.pause;
    G->gcstepsize = (int)((size_t)1 << G->gcparams.stepsize);
    G->gcstepmul  = G->gcparams.stepmul;
    G->currentwhite = GC_WHITE0;
    G->gcstate = GCST_PAUSE;
    G->gcstop  = 0;
    G->GCthreshold = 1024 * 1024;
    G->GCestimate  = 0;
    ptrenc_init(&G->ptrenc, (u64)now_ns() ^ (u64)(uintptr_t)G);
    G->registry.tag = LUA_TTABLE;
    G->registry.v.gc = (GCObject*)table_new(G, 16);
    G->pseudotemp.tag = LUA_TNIL;
    G->mainthread = state_new(G);
    init_caches(G);
    return G;
}

static void global_free(global_State* G) {
    if (!G) return;
    gc_full(G); gc_full(G); gc_full(G);
    lua_Page* pg = G->allpages;
    while (pg) {
        lua_Page* next = pg->next;
        page_free(pg);
        pg = next;
    }
    free(G);
}

static void print_memory_report(const global_State* G) {
    printf("=== memory report ===\n");
    printf("total bytes       : %zu\n", G->totalbytes);
    printf("peak bytes        : %zu\n", G->peak_totalbytes);
    printf("allocations       : %llu\n", (unsigned long long)G->allocations);
    printf("frees             : %llu\n", (unsigned long long)G->frees);
    printf("bytes freed total : %llu\n", (unsigned long long)G->bytes_freed_total);
    printf("live strings      : %u\n", G->strt.count);
    u64 counts[16] = {0};
    for (GCObject* o = G->allgc; o; o = o->next)
        if (o->type < 16) counts[o->type]++;
    printf("live objects by type:\n");
    static const char* tnames[] = { "-", "string", "table", "function",
                                    "userdata", "thread", "upval", "proto" };
    for (int i = 1; i < 8; ++i)
        if (counts[i]) printf("  %-10s : %llu\n", tnames[i], (unsigned long long)counts[i]);

    printf("per-category bytes:\n");
    for (int i = 0; i < MC_CATEGORY_COUNT; ++i) {
        if (G->memcatbytes[i] == 0) continue;
        printf("  %-10s : %zu\n", mc_name[i], G->memcatbytes[i]);
    }

    u32 pages = 0, live_pages = 0, live_cells = 0, total_cells = 0;
    for (lua_Page* p = G->allpages; p; p = p->next) {
        pages++;
        if (p->live > 0) live_pages++;
        live_cells += p->live;
        total_cells += p->cells;
    }
    printf("pages             : %u (%u live)\n", pages, live_pages);
    printf("cells             : %u live / %u total\n", live_cells, total_cells);
    if (total_cells) printf("page utilization  : %.1f%%\n",
                            100.0 * live_cells / total_cells);
    printf("=====================\n");
}

static void print_gc_report(const global_State* G) {
    printf("=== gc report ===\n");
    printf("collections       : %llu\n", (unsigned long long)G->gcstats.collections);
    printf("objects freed     : %llu\n", (unsigned long long)G->gcstats.objects_freed);
    printf("pauses            : %llu\n", (unsigned long long)G->gcstats.pauses);
    printf("steps             : %llu\n", (unsigned long long)G->gcstats.steps);
    printf("finalizers run    : %llu\n", (unsigned long long)G->gcstats.finalizers_run);
    printf("weak clears       : %llu\n", (unsigned long long)G->gcstats.weak_clears);
    printf("barriers back     : %llu\n", (unsigned long long)G->gcstats.barriers_back);
    printf("barriers forward  : %llu\n", (unsigned long long)G->gcstats.barriers_forward);
#if LUAI_GCMETRICS
    printf("--- metrics ---\n");
    printf("mark visits       : %llu\n", (unsigned long long)G->gcmetrics.mark_visits);
    printf("sweep pages       : %llu\n", (unsigned long long)G->gcmetrics.sweep_pages);
    printf("alloc count       : %llu\n", (unsigned long long)G->gcmetrics.alloc_count);
    printf("alloc bytes       : %llu\n", (unsigned long long)G->gcmetrics.alloc_bytes);
    for (int i = 0; i < 8; ++i)
        if (G->gcmetrics.phase_ns[i])
            printf("phase %-10s : %llu ns\n", gc_phase_name[i],
                   (unsigned long long)G->gcmetrics.phase_ns[i]);
#endif
    printf("=================\n");
}

static void print_stats_json(const global_State* G) {
    printf("{\n");
    printf("  \"totalbytes\": %zu,\n", G->totalbytes);
    printf("  \"peak_totalbytes\": %zu,\n", G->peak_totalbytes);
    printf("  \"allocations\": %llu,\n", (unsigned long long)G->allocations);
    printf("  \"frees\": %llu,\n", (unsigned long long)G->frees);
    printf("  \"live_strings\": %u,\n", G->strt.count);
    printf("  \"gc\": {\n");
    printf("    \"collections\": %llu,\n", (unsigned long long)G->gcstats.collections);
    printf("    \"objects_freed\": %llu,\n", (unsigned long long)G->gcstats.objects_freed);
    printf("    \"pauses\": %llu,\n", (unsigned long long)G->gcstats.pauses);
    printf("    \"steps\": %llu,\n", (unsigned long long)G->gcstats.steps);
    printf("    \"finalizers_run\": %llu,\n", (unsigned long long)G->gcstats.finalizers_run);
    printf("    \"weak_clears\": %llu,\n", (unsigned long long)G->gcstats.weak_clears);
    printf("    \"barriers_back\": %llu,\n", (unsigned long long)G->gcstats.barriers_back);
    printf("    \"barriers_forward\": %llu,\n", (unsigned long long)G->gcstats.barriers_forward);
    printf("    \"phase_ns\": [");
    for (int i = 0; i < 8; ++i) {
        if (i) printf(", ");
        printf("%llu", (unsigned long long)G->gcmetrics.phase_ns[i]);
    }
    printf("]\n  }\n}\n");
}

static TValue make_number(double d) {
    TValue v; memset(&v, 0, sizeof(v));
    v.tag = LUA_TNUMBER;
    u64 bits; memcpy(&bits, &d, 8); v.v.n = bits;
    return v;
}
static TValue make_bool(int b) {
    TValue v; memset(&v, 0, sizeof(v));
    v.tag = LUA_TBOOLEAN; v.v.b = b; return v;
}
static TValue make_string(TString* s) {
    TValue v; memset(&v, 0, sizeof(v));
    v.tag = LUA_TSTRING; v.v.gc = (GCObject*)s; return v;
}
static TValue make_table(LuaTable* t) {
    TValue v; memset(&v, 0, sizeof(v));
    v.tag = LUA_TTABLE; v.v.gc = (GCObject*)t; return v;
}
static TValue make_udata(lua_Userdata* u) {
    TValue v; memset(&v, 0, sizeof(v));
    v.tag = LUA_TUSERDATA; v.v.gc = (GCObject*)u; return v;
}
static double number_double(const TValue* v) {
    double d; memcpy(&d, &v->v.n, 8); return d;
}

static void table_set_weak(LuaTable* t, bool wk, bool wv) {
    t->is_weak = (wk ? 1 : 0) | (wv ? 2 : 0);
}

static void register_weak_table(global_State* G, LuaTable* t) {
    t->header.gnext = G->weak;
    G->weak = (GCObject*)t;
}

static int registry_ref(global_State* G, TValue v) {
    int id;
    if (G->registryfree > 0) {
        G->registryfree--;
        id = (int)G->registry_slots[G->registryfree];
    } else {
        id = ++G->registryfree;
        G->registryfree = 0;
        static int next_id = 1;
        id = next_id++;
    }
    TValue k = make_number((double)id);
    table_set(G, (LuaTable*)G->registry.v.gc, &k, &v);
    return id;
}

static void registry_unref(global_State* G, int id) {
    TValue k = make_number((double)id);
    TValue nil; memset(&nil, 0, sizeof(nil)); nil.tag = LUA_TNIL;
    table_set(G, (LuaTable*)G->registry.v.gc, &k, &nil);
    if (G->registryfree < LUA_REGISTRY_FREE_MAX) {
        G->registry_slots[G->registryfree++] = (u32)id;
    }
}

static int g_dtor_count = 0;
static void my_dtor(void* ud) { LUA_UNUSED(ud); g_dtor_count++; }
static void demo_build(void) {
    global_State* G = global_new();
    TString* s1 = string_new(G, "hello", 5);
    TString* s2 = string_new(G, "world", 5);
    TString* s3 = string_new(G, "hello", 5);
    printf("interning: s1=%p s3=%p (equal? %s)\n", (void*)s1, (void*)s3,
           s1 == s3 ? "yes" : "no");
    TValue slot; memset(&slot, 0, sizeof(slot));
    slot.tag = LUA_TTABLE;
    slot.v.gc = (GCObject*)s1;
    u64 cipher = ptrenc_encrypt(&G->ptrenc, slot.v.gc, &slot);
    void* plain = ptrenc_decrypt(&G->ptrenc, cipher, &slot);
    printf("ptrenc: plain=%p cipher=0x%llx decrypt=%p ok=%s\n",
           (void*)s1, (unsigned long long)cipher, plain,
           plain == (void*)s1 ? "yes" : "NO");
    G->udatagc[7] = my_dtor;
    lua_Userdata* u = udata_new(G, 7, 64, NULL);
    printf("userdata tag=%d payload=%p dtor=%p\n",
           u->tag, u->payload, (void*)u->destructor);
    LuaTable* wt = table_new(G, 8);
    table_set_weak(wt, false, true);
    register_weak_table(G, wt);
    {
        LuaTable* tmp = table_new(G, 4);
        TValue k = make_string(s2);
        TValue v = make_table(tmp);
        table_set(G, wt, &k, &v);
    }

    LuaTable* mt = table_new(G, 4);
    TValue gc_k = make_string(G->tmname[TM_GC]);
    TValue gc_v; memset(&gc_v, 0, sizeof(gc_v)); gc_v.tag = LUA_TNIL;
    TValue fn; memset(&fn, 0, sizeof(fn)); fn.tag = LUA_TFUNCTION; fn.v.p = (void*)1;
    table_set(G, mt, &gc_k, &fn);
    {
        LuaTable* target = table_new(G, 4);
        target->metatable = mt;
        (void)target;
    }
    TValue rv = make_string(s2);
    int rid = registry_ref(G, rv);
    printf("registry ref id=%d\n", rid);
    registry_unref(G, rid);
    s1 = s2 = s3 = NULL; u = NULL;
    (void)rid;
    print_memory_report(G);
    gc_full(G);
    print_memory_report(G);
    print_gc_report(G);
    printf("userdata destructors called: %d\n", g_dtor_count);
    global_free(G);
}

static void demo_bench(void) {
    printf("=== benchmark ===\n");
    global_State* G = global_new();
    const int N = 20000;
    u64 t0, t1, t2, t3;
    t0 = now_ns();
    TString* last = NULL;
    for (int i = 0; i < N; ++i) {
        char buf[32];
        int n = snprintf(buf, sizeof(buf), "str_%d", i);
        last = string_new(G, buf, (size_t)n);
    }
    t1 = now_ns();
    for (int i = 0; i < N; ++i) {
        LuaTable* t = table_new(G, 8);
        TValue k = make_string(last);
        TValue v = make_number((double)i);
        table_set(G, t, &k, &v);
    }
    t2 = now_ns();
    gc_full(G);
    t3 = now_ns();
    printf("strings  : %d in %llu us (%.2f us/op)\n", N,
           (unsigned long long)((t1 - t0) / 1000),
           (double)(t1 - t0) / 1000.0 / N);
    printf("tables   : %d in %llu us (%.2f us/op)\n", N,
           (unsigned long long)((t2 - t1) / 1000),
           (double)(t2 - t1) / 1000.0 / N);
    printf("full GC  :     %llu us\n", (unsigned long long)((t3 - t2) / 1000));
    printf("total    :     %llu us\n", (unsigned long long)((t3 - t0) / 1000));
    print_memory_report(G);
    print_gc_report(G);
    global_free(G);
}

static void demo_stress(void) {
    printf("=== stress test ===\n");
    global_State* G = global_new();
    G->trace = false;
    LuaTable* root = table_new(G, 256);
    TValue rootv = make_table(root);
    int rid = registry_ref(G, rootv);
    const int N = 50000;
    for (int i = 0; i < N; ++i) {
        LuaTable* t = table_new(G, 8);
        TString* s = NULL;
        char buf[32];
        snprintf(buf, sizeof(buf), "key_%d", i % 1024);
        s = string_new(G, buf, strlen(buf));
        TValue k = make_string(s);
        TValue v = make_table(t);
        table_set(G, root, &k, &v);
    }
    gc_full(G);
    gc_full(G);
    int found = 0;
    for (int i = 0; i < 1024; ++i) {
        char buf[32];
        snprintf(buf, sizeof(buf), "key_%d", i);
        TString* s = string_new(G, buf, strlen(buf));
        TValue k = make_string(s);
        if (table_get(G, root, &k)) found++;
    }
    printf("after GC: root has %d/1024 entries\n", found);
    registry_unref(G, rid);
    print_memory_report(G);
    print_gc_report(G);
    global_free(G);
}

static int g_failures = 0;
#define CHECK(cond, msg) do {                                                  \
    if (!(cond)) {                                                             \
        fprintf(stderr, "FAIL: %s (%s:%d)\n", (msg), __FILE__, __LINE__);      \
        g_failures++;                                                          \
    }                                                                          \
} while (0)

static void test_ptrenc(void) {
    PtrEnc pe; ptrenc_init(&pe, 0x12345678);
    for (int i = 0; i < 1000; ++i) {
        void* p = (void*)(uintptr_t)(0x1000 + i * 0x100);
        u64 c = ptrenc_encrypt(&pe, p, &pe);
        void* q = ptrenc_decrypt(&pe, c, &pe);
        CHECK(p == q, "ptrenc round-trip");
    }
}

static void test_interning(void) {
    global_State* G = global_new();
    u32 initial = G->strt.count;
    TString* a = string_new(G, "abc", 3);
    TString* b = string_new(G, "abc", 3);
    TString* c = string_new(G, "abd", 3);
    CHECK(a == b, "identical strings intern");
    CHECK(a != c, "different strings do not intern");
    CHECK(G->strt.count == initial + 2, "string table count grows by 2");
    global_free(G);
}

static void test_table(void) {
    global_State* G = global_new();
    LuaTable* t = table_new(G, 8);
    TString* k = string_new(G, "key", 3);
    TValue kv = make_string(k);
    TValue vv = make_number(42.0);
    table_set(G, t, &kv, &vv);
    TValue* got = table_get(G, t, &kv);
    CHECK(got != NULL, "table get found");
    CHECK(got && number_double(got) == 42.0, "table get value");
    global_free(G);
}

static void test_gc(void) {
    global_State* G = global_new();
    g_dtor_count = 0;
    G->udatagc[3] = my_dtor;
    u32 initial_strings = G->strt.count;
    for (int i = 0; i < 100; ++i) {
        (void)table_new(G, 8);
        (void)udata_new(G, 3, 32, NULL);
    }
    gc_full(G);
    gc_full(G);
    CHECK(g_dtor_count == 100, "userdata destructors ran");
    CHECK(G->strt.count == initial_strings, "string table restored");
    global_free(G);
}

static void test_weak(void) {
    global_State* G = global_new();
    LuaTable* wt = table_new(G, 8);
    table_set_weak(wt, false, true);
    register_weak_table(G, wt);
    {
        TString* k = string_new(G, "keep", 4);
        TString* v = string_new(G, "drop", 4);
        TValue kv = make_string(k);
        TValue vv = make_string(v);
        table_set(G, wt, &kv, &vv);
        int rid = registry_ref(G, kv);
        gc_full(G);
        gc_full(G);
        TValue* got = table_get(G, wt, &kv);
        CHECK(got == NULL, "weak value cleared after GC");
        registry_unref(G, rid);
    }
    global_free(G);
}

static void test_barriers(void) {
    global_State* G = global_new();
    LuaTable* t = table_new(G, 8);
    int rid = registry_ref(G, make_table(t));
    gc_step(G, 0);
    while (G->gcstate != GCST_PAUSE) gc_step(G, 0);
    LuaTable* fresh = table_new(G, 4);
    TString* k = string_new(G, "k", 1);
    TValue kv = make_string(k);
    TValue fv = make_table(fresh);
    table_set(G, t, &kv, &fv);
    gc_full(G);
    gc_full(G);
    TValue* got = table_get(G, t, &kv);
    CHECK(got != NULL && got->tag == LUA_TTABLE,
          "barrier preserved newly-inserted value");
    registry_unref(G, rid);
    global_free(G);
}

static int run_selftest(void) {
    g_failures = 0;
    printf("running self-test...\n");
    test_ptrenc();
    test_interning();
    test_table();
    test_gc();
    test_weak();
    test_barriers();
    if (g_failures == 0) { printf("all tests passed\n"); return 0; }
    printf("%d test(s) failed\n", g_failures);
    return 1;
}

static void usage(const char* argv0) {
    printf("usage: %s [command]\n", argv0);
    printf("commands:\n");
    printf("  (none)        run the demo\n");
    printf("  --bench       run the benchmark\n");
    printf("  --selftest    run the self-test\n");
    printf("  --stress      GC stress test (write barriers + weak)\n");
    printf("  --trace       demo with GC trace log on stderr\n");
    printf("  --stats-json  print machine-readable stats\n");
    printf("  --help        this message\n");
}

int main(int argc, char** argv) {
    if (argc <= 1) { demo_build(); return 0; }
    const char* c = argv[1];
    if (strcmp(c, "--bench") == 0)      { demo_bench(); return 0; }
    if (strcmp(c, "--selftest") == 0)   { return run_selftest(); }
    if (strcmp(c, "--stress") == 0)     { demo_stress(); return 0; }
    if (strcmp(c, "--trace") == 0) {
        global_State* G = global_new();
        G->trace = true; G->trace_fp = stderr;
        demo_build();
        global_free(G);
        return 0;
    }
    if (strcmp(c, "--stats-json") == 0) {
        global_State* G = global_new();
        for (int i = 0; i < 1000; ++i) (void)table_new(G, 8);
        gc_full(G);
        print_stats_json(G);
        global_free(G);
        return 0;
    }
    if (strcmp(c, "--help") == 0 || strcmp(c, "-h") == 0) { usage(argv[0]); return 0; }
    fprintf(stderr, "unknown command: %s\n", c);
    usage(argv[0]);
    return 2;
}
