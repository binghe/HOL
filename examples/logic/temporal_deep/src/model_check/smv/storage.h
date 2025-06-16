typedef struct rec {
  struct rec *link;
} rec_rec, *rec_ptr;

typedef struct mgr{
    rec_rec free;
    int  rec_size;
    int count;
    void (*free_hook)();
} mgr_rec, *mgr_ptr;

#define ALLOCSIZE (2<<15)

void init_storage(void);
mgr_ptr new_mgr(int rec_size);
rec_ptr new_rec(register mgr_ptr mp);
rec_ptr dup_rec(mgr_ptr mp, rec_ptr r);
void free_rec(register mgr_ptr mp, rec_ptr r);
