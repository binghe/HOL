#include <math.h>
#include <sys/times.h>
#include <time.h>

typedef struct bdd {
   unsigned dfield;
   struct bdd *left, *right, *next;
} bdd_rec, *bdd_ptr;

#ifndef NULL
#define NULL 0
#endif

extern bdd_ptr ZERO,ONE;

/* Data structure for the key table */
typedef struct {
   int n;
   int elements_in_table;
   bdd_ptr *hash_table_buf;
} keytable_rec, *keytable_ptr;

/* Data structure for apply record */
typedef struct {
  int op;
  bdd_ptr arg1,arg2,res;
} apply_rec;



/* Bits packed as follows:                                   */
/* NOT USED  --- id    (0 to IDMASK : depth first id)            */
/* 30:0 --- level (0 to LEAFLEVEL)                          */
/* 31   --- mark  (TRUE or FALSE : used in graph traversal) */

 /* Used to be 500 */
#define MAXSTVARS 5000

#ifdef REORDER
/* Used to be 1000 */
#define NLEVELS 100000
#endif

/* This is never used. */
/* #define IDMASK    0X0000FFFF */
 /* Increased to 31 bits (2GB levels) */
#define LEVELMASK 0X7FFFFFFF
#define MARKMASK  0X80000000

/* #define IDLOW    0 */
  /* This has changed as well */
#define LEVELLOW 0
#define MARKLOW  31

#define LEAFLEVEL 0X7FFFFFFF /* ... and this. */
#define ISLEAF(d) (GETLEVEL(d) == LEAFLEVEL)

#define GETFIELD(var, mask, low) ((int) ((var & mask) >> low))
#define PUTFIELD(var, val, mask, low) \
        (var = (var & ~(mask)) | (((unsigned) val) << low))

     /* #define GETID(d)        ((d)->dfield & IDMASK)
      * #define SETID(d, idval) (PUTFIELD((d)->dfield, idval, IDMASK, IDLOW))
      */

#define GETLEVEL(d) (GETFIELD((d)->dfield, LEVELMASK, LEVELLOW))
#define SETLEVEL(d, lval) (PUTFIELD((d)->dfield, lval, LEVELMASK, LEVELLOW))

#define SETMARK(d)   ((d)->dfield |= MARKMASK)
#define CLEARMARK(d) ((d)->dfield &= ~MARKMASK)
#define TESTMARK(d)  (((d)->dfield & MARKMASK) != 0X0)


#define AND_OP 1
#define OR_OP 2
#define XOR_OP 3
#define FORSOME_OP 4
#define NEXT_OP 11
#define PREV_OP 12
#define COMP_OP 6
#define SIMP_OP 7
#define COUNT_OP 8
#define COUNT_OP_LOG 18
#define ELIM_OP 9
#define SATISFY_OP 10

#ifdef OTHER_SIMP

#define SIMP_OP2 13
#define USE_BIG_CACHE 14
#define BDDS_IN_MB (1024*1024/sizeof(bdd_rec))

#else /* not OTHER_SIMP */

#define USE_BIG_CACHE 11

#endif /* OTHER_SIMP */

/* functions we provide */

void init_bdd(void);
bdd_ptr find_bdd(register int level, register bdd_ptr d1, register bdd_ptr d2);
void sweep_reduce(void);
void save_apply(int op, register bdd_ptr d1, register bdd_ptr d2);
void insert_apply(int op, register bdd_ptr d1, register bdd_ptr d2, register bdd_ptr d);
bdd_ptr find_apply(int op, register bdd_ptr d1, register bdd_ptr d2);
void flush_apply(void);
void repairmark(register bdd_ptr d);
void renumber(register bdd_ptr d, register int* pcount);
int size_bdd(register bdd_ptr d);
void mark_bdd(register bdd_ptr d);
bdd_ptr and_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr or_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr xor_bdd(bdd_ptr a, bdd_ptr b);
bdd_ptr not_bdd(bdd_ptr d);
bdd_ptr forsome(bdd_ptr a, bdd_ptr b);
#ifdef OTHER_SIMP
bdd_ptr simplify_assuming2(bdd_ptr a, bdd_ptr b);
#endif
bdd_ptr simplify_assuming(bdd_ptr a, bdd_ptr b);
bdd_ptr sat_bdd(bdd_ptr d);
double count_bdd(bdd_ptr d);
double n_count_bdd(bdd_ptr d, int n);
bdd_ptr save_bdd(bdd_ptr d);
void release_bdd(bdd_ptr d);
bdd_ptr leaf_bdd(bdd_ptr n);
bdd_ptr atomic_bdd(int n);
bdd_ptr r_shift(bdd_ptr a);
bdd_ptr f_shift(bdd_ptr a);
bdd_ptr r_collapse(bdd_ptr a, bdd_ptr b);
bdd_ptr collapse(bdd_ptr a, bdd_ptr b);
bdd_ptr apply_bdd(int (*f)(), bdd_ptr a, bdd_ptr b);
bdd_ptr if_then_else_bdd(bdd_ptr a, bdd_ptr b, bdd_ptr c);

bdd_ptr bdd_trim_to_level(bdd_ptr d, int n);
int var_level(node_ptr v);

#define IS_CURRENT_VAR(s) (((s)&1)==0)
#define IS_NEXT_VAR(s) (((s)&1)==1)
#define THE_CURRENT_VAR(s) (((s)<<1))
#define THE_NEXT_VAR(s) (((s)<<1)+1)
#define VAR_NUM(s) ((s)>>1)
#define NEXT_TO_CURRENT(s) ((s)-1)
#define CURRENT_TO_NEXT(s) ((s)+1)

int get_bdd_nodes_allocated(void);
void reset_maxnodes(void);
void set_variable_names(void);
void pr_status(void);
void walk_leaves(void (*f)(), bdd_ptr d);
int lowest_var_bdd(bdd_ptr d);
