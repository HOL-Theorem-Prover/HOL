#include <storage.h>
#include <hash.h>


hash_ptr new_hash(init_size,hash_fun,eq_fun,mgr)
int init_size;
int (*hash_fun)(),(*eq_fun)();
mgr_ptr mgr;
{
  hash_ptr res = (hash_ptr)smv_malloc(sizeof(struct hash));
  res->size = init_size;
  res->hash_fun = hash_fun;
  res->eq_fun = eq_fun;
  res->mgr = mgr;
  res->tab = (rec_ptr *)smv_malloc(init_size * sizeof(rec_ptr));
  bzero(res->tab,init_size * sizeof(rec_ptr));
  return(res);
}

void clear_hash(hash)
hash_ptr hash;
{
  int i;
  for(i=0;i<hash->size;i++){
    rec_ptr p = hash->tab[i];
    while(p){
      rec_ptr q = p;
      p = p->link;
      free_rec(hash->mgr,q);
    }
    hash->tab[i] = 0;
  }
}

rec_ptr find_hash(hash,rec)
hash_ptr hash;
rec_ptr rec;
{
  int (*eq_fun)() = hash->eq_fun;
  rec_ptr *p = hash->tab + (((unsigned)(*hash->hash_fun)(rec)) % hash->size);
  while(*p){
    if((*eq_fun)(*p,rec))return(*p);
    p = &((*p)->link);
  }
  return(0);
}

rec_ptr insert_hash(hash,rec)
hash_ptr hash;
rec_ptr rec;
{
  int (*eq_fun)() = hash->eq_fun;
  rec_ptr *p = hash->tab + (((unsigned)(*hash->hash_fun)(rec)) % hash->size);
  while(*p){
    if((*eq_fun)(*p,rec))return(*p);
    p = &((*p)->link);
  }
  *p = dup_rec(hash->mgr,rec);
  return(*p);
}


void remove_hash(hash,rec)
hash_ptr hash;
rec_ptr rec;
{
  int (*eq_fun)() = hash->eq_fun;
  rec_ptr *p = hash->tab + (((unsigned)(*hash->hash_fun)(rec)) % hash->size);
  while(*p){
    if((*eq_fun)(*p,rec)){
      rec_ptr q = *p;
      *p = (*p)->link;
      free_rec(hash->mgr,q);
      return;
    }
    p = &((*p)->link);
  }
  catastrophe("remove_hash: record not found");
}

