#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <strings.h>

#include "node.h"
#include "init.h"
#include "storage.h"

static char *addrlimit;
static char *addrfree;

/* this routine initializes the storage manager */
void init_storage()
{
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

  p1 = &(mp->free);
  while(addrlimit-addrfree >= mp->rec_size){
    p1->link = (rec_ptr)addrfree;
    p1 = (rec_ptr)addrfree;
    addrfree += mp->rec_size;
  }
/* link field of the last record should be NIL (by Hiromi, 1998.5.5) */
  p1->link = ((rec_ptr)0);
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
