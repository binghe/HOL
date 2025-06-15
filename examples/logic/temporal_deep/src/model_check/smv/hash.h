typedef struct hash {
  int size;
  int (*hash_fun)();
  int (*eq_fun)();
  mgr_ptr mgr;
  rec_ptr *tab;
} hash_rec,*hash_ptr;

hash_ptr new_hash(int init_size, int (*hash_fun)(), int (*eq_fun)(), mgr_ptr mgr);
rec_ptr find_hash(hash_ptr hash, rec_ptr rec);
rec_ptr insert_hash(hash_ptr hash, rec_ptr rec);
void clear_hash(hash_ptr hash);
void remove_hash(hash_ptr hash, rec_ptr rec);
