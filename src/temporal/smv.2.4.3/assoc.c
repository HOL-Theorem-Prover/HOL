#include <storage.h>
#include <hash.h>
#include <node.h>
#include <assoc.h>

static mgr_ptr assoc_mgr;
#define ASSOC_HASH_SIZE 127


void init_assoc()
{
  assoc_mgr = new_mgr(sizeof(struct assoc));
}

static int assoc_hash_fun(assoc)
assoc_ptr assoc;
{
  return((int)(assoc->x));
}

static int assoc_eq_fun(a1,a2)
assoc_ptr a1,a2;
{
  return((a1->x) == (a2->x));
}

hash_ptr new_assoc()
{
  return(new_hash(ASSOC_HASH_SIZE,assoc_hash_fun,assoc_eq_fun,assoc_mgr));
}

node_ptr find_assoc(hash,x)
hash_ptr hash;
node_ptr x;
{
  assoc_rec a;
  assoc_ptr b;
  a.x = x;
  b=(assoc_ptr)find_hash(hash,&a);
  if(b)return(b->y);
  else return(NIL);
}

void insert_assoc(hash,x,y)
hash_ptr hash;
node_ptr x,y;
{
  assoc_rec a,*b;
  a.x = x;
  a.y = y;
  b = (assoc_ptr)insert_hash(hash,&a);
  b->y = y;
}

void remove_assoc(hash,x,y)
hash_ptr hash;
node_ptr x,y;
{
  assoc_rec a;
  a.x = x;
  a.y = y;
  remove_hash(hash,&a);
}

void (*assoc_free_hook)();
void free_assoc(a)
assoc_ptr a;
{
  if(assoc_free_hook)(*assoc_free_hook)(a->y);
}

void clear_assoc(hash,free_hook)
hash_ptr hash;
void (*free_hook)();
{
  assoc_free_hook = free_hook;
  assoc_mgr->free_hook = free_assoc;
  clear_hash(hash);
  assoc_mgr->free_hook = 0;
}

