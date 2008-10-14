#include <storage.h>
#include <hash.h>
#include <string.h>

static mgr_ptr string_mgr;
static hash_ptr string_hash;
#define STRING_HASH_SIZE 511


static int string_hash_fun(string)
string_ptr string;
{
  char *p = string->text;
  unsigned h = 0;
  while(*p)h = (h<<1) + *(p++);
  return(h);
}

static int string_eq_fun(a1,a2)
string_ptr a1,a2;
{
  return(strcmp(a1->text,a2->text)==0);
}

void init_string()
{
  string_mgr = new_mgr(sizeof(struct string));
  string_hash = new_hash(STRING_HASH_SIZE,string_hash_fun,
			 string_eq_fun,string_mgr);
}

string_ptr find_string(x)
char *x;
{
  string_rec a,*res;
  a.text = x;
  if(res = (string_ptr)find_hash(string_hash,&a))return(res);
  a.text = (char *)strcpy((char *)smv_malloc(strlen(x)+1),x);
  return((string_ptr)insert_hash(string_hash,&a));
}

