#include <stdio.h>
#include <sys/types.h>
#include <storage.h>
static char *addrlimit;
static char *addrfree;

/* this routine initializes the storage manager */
void init_storage()
{
#ifdef MACH
  mach_init();		/* needed to make sbrk() work */
#endif MACH
  /* addrfree points to the first free byte
     addrlimit points to the memory limit */
    addrfree = addrlimit = (char *) sbrk(0);
}

/* get ALLOCSIZE more bytes from the O.S. */
static getmore()
{
  char *na;
/*  fprintf(stderr,"Getting %d more bytes\n",ALLOCSIZE); */
  if(addrlimit != (char *)sbrk(0)){ /* in case someone else did sbrk */
    sbrk((4 - (sbrk(0) % 4)) % 4);
    addrfree = addrlimit = (char *)sbrk(0);
    if(((unsigned)addrlimit) % 4 != 0)
      rpterr("Failed to allocate %d bytes: addrlimit = %xH, na = %xH\n",
	     ALLOCSIZE,(int)addrlimit,(int)na);
  }
  if((na = (char *)sbrk(ALLOCSIZE)) != addrlimit)
    rpterr("Failed to allocate %d bytes: addrlimit = %xH, na = %xH\n",
	   ALLOCSIZE,(int)addrlimit,(int)na);
  addrlimit += ALLOCSIZE;
}

/* provide malloc for miscellaneuos storage allocation */
char *smv_malloc(n)
int n;
{
  if(n % 4)n=n+4-(n%4);  /* always allocate multiple of four bytes */
  while(addrfree + n > addrlimit)getmore();
  {
    char *r = addrfree;
    addrfree += n;
    return(r);
  }
}

/* very simple implementation of free */
void free(p)
char *p;
{
  return;
}

/* initialize a record manager.
   sets the free list to NULL,
   and makes sure the record size
   is at least big enough for a pointer */

mgr_ptr new_mgr(rec_size)
int rec_size;
{
  register mgr_ptr mp = (mgr_ptr)malloc(sizeof(struct mgr));
  mp->free.link = 0;
  mp->rec_size = rec_size;
  mp->count = 0;
  mp->free_hook = 0;
  return(mp);
}



/* get a new record. if the free list
   is not empty, pull the first record off this
   list. else get ALLOCSIZE more bytes and
   make a new block of records. Link all
   of these record into a free list.
   then get the first element of this list
   by calling new_rec recursively. */

rec_ptr new_rec(mp)
register mgr_ptr mp;
{
  register rec_ptr p1;
  if(mp->free.link){
    rec_ptr r = mp->free.link;
    mp->free.link = (mp->free.link)->link;
    r->link = 0;
    return(r);
  }
  getmore();
  p1 = &(mp->free);
  while(addrlimit-addrfree >= mp->rec_size){
    p1->link = (rec_ptr)addrfree;
    p1 = (rec_ptr)addrfree;
    addrfree += mp->rec_size;
  }
  return(new_rec(mp));
}

/* put a record on the free list */
void free_rec(mp,r)
register mgr_ptr mp;
rec_ptr r;
{
  register rec_ptr rp = r;
  if(mp->free_hook)(*(mp->free_hook))(rp);
  rp->link = mp->free.link;
  mp->free.link = rp;
}

rec_ptr dup_rec(mp,r)
mgr_ptr mp;
rec_ptr r;
{
  register rec_ptr res = new_rec(mp);
  bcopy(r,res,mp->rec_size);
  res->link = 0;
  return(res);
}

