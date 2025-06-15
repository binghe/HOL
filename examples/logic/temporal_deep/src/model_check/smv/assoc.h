typedef struct assoc{
  struct assoc *link;
  node_ptr x;
  node_ptr y;
} assoc_rec,*assoc_ptr;

void init_assoc(void);
hash_ptr new_assoc(void);
node_ptr find_assoc(hash_ptr hash, node_ptr x);
void insert_assoc(hash_ptr hash, node_ptr x, node_ptr y);
