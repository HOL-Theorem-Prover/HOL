typedef struct hash {
  int size;
  int (*hash_fun)();
  int (*eq_fun)();
  mgr_ptr mgr;
  rec_ptr *tab;
} hash_rec,*hash_ptr;

hash_ptr new_hash();
rec_ptr find_hash(),insert_hash();
void clear_hash();
