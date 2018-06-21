#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <assert.h>
#include <ctype.h>

#ifndef TRUE
#define TRUE  1
#endif
#ifndef FALSE
#define FALSE 0
#endif

#define stat xv6_stat  // avoid clash with host struct stat
#include "types.h"
#include "fs.h"
#include "stat.h"
#include "param.h"

#ifndef static_assert
#define static_assert(a, b) do { switch (0) case 0: case (a): ; } while (0)
#endif

#define NINODES 200

// Disk layout:
// [ boot block | sb block | log | inode blocks | free bit map | data blocks ]

int nbitmap = FSSIZE/(BSIZE*8) + 1;
int ninodeblocks = NINODES / IPB + 1;
int nlog = LOGSIZE;
int nmeta;    // Number of meta blocks (boot, sb, nlog, inode, bitmap)
int nblocks;  // Number of data blocks

int fsfd;
struct superblock sb;
char zeroes[BSIZE];
uint freeinode = 1;
uint freeblock;

void balloc(int used);
void wsect(uint sec, void *buf);
void winode(uint inum, struct dinode *ip);
void rinode(uint inum, struct dinode *ip);
void rsect(uint sec, void *buf);
uint ialloc(ushort type);
void iappend(uint inum, void *p, int n);
void dirappend(uint inum, struct dirent *dir);
void btinsert(struct dinode *din, struct dirent *dir);
void btprint(uint inum);
uint _btalloc(struct dirnode *dnode);
void _btinsert(struct dirnode *dnode, uint db, struct dirent *dir);
uint _btsplit(struct dirnode *parent, uint pb, int idx, struct dirnode *child, uint cb, struct dirnode *nchild);
void _btprint(uint b, int lvl);
void _direntcp(struct dirent *dst, struct dirent *src);
void _direntinsert(struct dirnode *dnode, int idx, struct dirent *dir, int cidx, uint cb,
                   ushort nchildren);
ushort _countchildren(struct dirnode *dnode);
void dirdelete(uint inum, struct dirent *dir);
void btdelete(struct dinode *din, struct dirent *dir);
void _btdelete(struct dirnode *dnode, uint db, struct dirent *dir, struct dirent *replace, int release);
void _btmerge(struct dirnode *parent, uint pb, int idx, struct dirnode *pchild, uint pcb, struct dirnode *nchild,
              uint ncb);
void _btpexchange(struct dirnode *parent, uint pb, int idx, struct dirnode *child, int cb, struct dirnode *pchild, int pcb);
void _btnexchange(struct dirnode *parent, uint pb, int idx, struct dirnode *child, int cb, struct dirnode *nchild, int ncb);
void _direntdelete(struct dirnode *dnode, int idx, int cidx);
#if DO_READ
int dirread(uint inum, char *buf, int off, int len);
int btread(struct dirnode *dnode, char *buf, uint off, uint start, uint end);
#endif

// convert to intel byte order
ushort
xshort(ushort x)
{
  ushort y;
  uchar *a = (uchar*)&y;
  a[0] = x;
  a[1] = x >> 8;
  return y;
}

uint
xint(uint x)
{
  uint y;
  uchar *a = (uchar*)&y;
  a[0] = x;
  a[1] = x >> 8;
  a[2] = x >> 16;
  a[3] = x >> 24;
  return y;
}

int
main(int argc, char *argv[])
{
  int i, cc, fd;
  uint rootino, inum;
  struct dirent de;
  char buf[BSIZE];

  static_assert(sizeof(int) == 4, "Integers must be 4 bytes!");

  if(argc < 2){
    fprintf(stderr, "Usage: mkfs fs.img files...\n");
    exit(1);
  }

  assert((BSIZE % sizeof(struct dinode)) == 0);
  assert((BSIZE % sizeof(struct dirnode)) == 0);

  fsfd = open(argv[1], O_RDWR|O_CREAT|O_TRUNC, 0666);
  if(fsfd < 0){
    perror(argv[1]);
    exit(1);
  }

  // 1 fs block = 1 disk sector
  nmeta = 2 + nlog + ninodeblocks + nbitmap;
  nblocks = FSSIZE - nmeta;

  sb.size = xint(FSSIZE);
  sb.nblocks = xint(nblocks);
  sb.ninodes = xint(NINODES);
  sb.nlog = xint(nlog);
  sb.logstart = xint(2);
  sb.inodestart = xint(2+nlog);
  sb.bmapstart = xint(2+nlog+ninodeblocks);

  printf("nmeta %d (boot, super, log blocks %u inode blocks %u, bitmap blocks %u) blocks %d total %d\n",
         nmeta, nlog, ninodeblocks, nbitmap, nblocks, FSSIZE);

  freeblock = nmeta;     // the first free block that we can allocate

  for(i = 0; i < FSSIZE; i++)
    wsect(i, zeroes);

  memset(buf, 0, sizeof(buf));
  memmove(buf, &sb, sizeof(sb));
  wsect(1, buf);

  rootino = ialloc(T_DIR);
  assert(rootino == ROOTINO);

  bzero(&de, sizeof(de));
  de.inum = xshort(rootino);
  strcpy(de.name, ".");
  dirappend(rootino, &de);

  bzero(&de, sizeof(de));
  de.inum = xshort(rootino);
  strcpy(de.name, "..");
  dirappend(rootino, &de);

  for(i = 2; i < argc; i++){
    assert(index(argv[i], '/') == 0);

    if((fd = open(argv[i], 0)) < 0){
      perror(argv[i]);
      exit(1);
    }

    // Skip leading _ in name when writing to file system.
    // The binaries are named _rm, _cat, etc. to keep the
    // build operating system from trying to execute them
    // in place of system binaries like rm and cat.
    if(argv[i][0] == '_')
      ++argv[i];

    inum = ialloc(T_FILE);

    bzero(&de, sizeof(de));
    de.inum = xshort(inum);
    strncpy(de.name, argv[i], DIRSIZ);
    dirappend(rootino, &de);

    while((cc = read(fd, buf, sizeof(buf))) > 0) {
      iappend(inum, buf, cc);
    }
    
    close(fd);
  }

  balloc(freeblock);
  
  exit(0);
}

void
wsect(uint sec, void *buf)
{
  if(lseek(fsfd, sec * BSIZE, 0) != sec * BSIZE){
    perror("lseek");
    exit(1);
  }
  if(write(fsfd, buf, BSIZE) != BSIZE){
    perror("write");
    exit(1);
  }
}

void
winode(uint inum, struct dinode *ip)
{
  char buf[BSIZE];
  uint bn;
  struct dinode *dip;

  bn = IBLOCK(inum, sb);
  rsect(bn, buf);
  dip = ((struct dinode*)buf) + (inum % IPB);
  *dip = *ip;
  wsect(bn, buf);
}

void
rinode(uint inum, struct dinode *ip)
{
  char buf[BSIZE];
  uint bn;
  struct dinode *dip;

  bn = IBLOCK(inum, sb);
  rsect(bn, buf);
  dip = ((struct dinode*)buf) + (inum % IPB);
  *ip = *dip;
}

void
rsect(uint sec, void *buf)
{
  if(lseek(fsfd, sec * BSIZE, 0) != sec * BSIZE){
    perror("lseek");
    exit(1);
  }
  if(read(fsfd, buf, BSIZE) != BSIZE){
    perror("read");
    exit(1);
  }
}

uint
ialloc(ushort type)
{
  uint inum = freeinode++;
  struct dinode din;

  bzero(&din, sizeof(din));
  din.type = xshort(type);
  din.nlink = xshort(1);
  din.size = xint(0);
  winode(inum, &din);
  return inum;
}

void
balloc(int used)
{
  uchar buf[BSIZE];
  int i;

  printf("balloc: first %d blocks have been allocated\n", used);
  assert(used < BSIZE*8);
  bzero(buf, BSIZE);
  for(i = 0; i < used; i++){
    buf[i/8] = buf[i/8] | (0x1 << (i%8));
  }
  printf("balloc: write bitmap block at sector %d\n", sb.bmapstart);
  wsect(xint(sb.bmapstart), buf);
}

#define min(a, b) ((a) < (b) ? (a) : (b))

void
iappend(uint inum, void *xp, int n)
{
  char *p = (char*)xp;
  uint fbn, off, n1;
  struct dinode din;
  char buf[BSIZE];
  uint indirect[NINDIRECT];
  uint x;

  rinode(inum, &din);
  off = xint(din.size);
  // printf("append inum %d at off %d sz %d\n", inum, off, n);
  while(n > 0){
    fbn = off / BSIZE;
    assert(fbn < MAXFILE);
    if(fbn < NDIRECT){
      if(xint(din.addrs[fbn]) == 0){
        din.addrs[fbn] = xint(freeblock++);
      }
      x = xint(din.addrs[fbn]);
    } else {
      if(xint(din.addrs[NDIRECT]) == 0){
        din.addrs[NDIRECT] = xint(freeblock++);
      }
      rsect(xint(din.addrs[NDIRECT]), (char*)indirect);
      if(indirect[fbn - NDIRECT] == 0){
        indirect[fbn - NDIRECT] = xint(freeblock++);
        wsect(xint(din.addrs[NDIRECT]), (char*)indirect);
      }
      x = xint(indirect[fbn-NDIRECT]);
    }
    n1 = min(n, (fbn + 1) * BSIZE - off);
    rsect(x, buf);
    bcopy(p, buf + off - (fbn * BSIZE), n1);
    wsect(x, buf);
    n -= n1;
    off += n1;
    p += n1;
  }
  din.size = xint(off);
  winode(inum, &din);
}

void
dirappend(uint inum, struct dirent *dir)
{
  struct dinode din;

  rinode(inum, &din);
  btinsert(&din, dir);
  winode(inum, &din);
}

void
btinsert(struct dinode *din, struct dirent *dir)
{
  struct dirnode root, dnode, nchild;
  uint db, rb, ncb;

  if(xint(din->addrs[0]) == 0) {
    rb = _btalloc(&root);
    root.leaf = TRUE;
    din->addrs[0] = xint(rb);
  } else {
      rb = xint(din->addrs[0]);
      rsect(xint(din->addrs[0]), &root);
  }
  if(root.ndirs == 2 * BTDEGREE - 1) {
    db = _btalloc(&dnode);
    dnode.children[0] = xint(rb);
    dnode.nchildren[0] = _countchildren(&root);
    // new root
    din->addrs[0] = xint(db);
    ncb = _btsplit(&dnode, xint(db), 0, &root, rb, &nchild);
    if(strncmp(dir->name, dnode.dirs[0].name, DIRSIZ) > 0) {
      // account for child being inserted
      (dnode.nchildren[1])++;
      wsect(xint(rb), &root);
      _btinsert(&nchild, xint(ncb), dir);
    } else {
      // account for child being inserted
      (dnode.nchildren[0])++;
      wsect(xint(ncb), &nchild);
      _btinsert(&root, xint(rb), dir);
    }
    wsect(xint(db), &dnode);
          
  } else {
    _btinsert(&root, xint(rb), dir);
  }
  din->size += sizeof(*dir);
}

uint
_btalloc(struct dirnode *dnode)
{
  bzero(dnode, sizeof(*dnode));
  return freeblock++;
}

void
_btinsert(struct dirnode *dnode, uint db, struct dirent *dir)
{
  struct dirnode child, nchild;
  uint cb, ncb;
  int i;

  i = dnode->ndirs - 1;
  while(i >= 0 && strncmp(dir->name, dnode->dirs[i].name, DIRSIZ) < 0) {
    i--;
  }
  if(dnode->leaf) {
    _direntinsert(dnode, i + 1, dir, -1, 0, 0);
  } else {
    // insert into appropriate leaf node rooted at this subtree
    i++;
    cb = xint(dnode->children[i]);
    rsect(cb, &child);
    if(child.ndirs == 2 * BTDEGREE - 1) {
      // split a full child into two smaller ones before descending
      ncb = _btsplit(dnode, db, i, &child, cb, &nchild);
      if(strncmp(dir->name, dnode->dirs[i].name, DIRSIZ) > 0) {
        (dnode->nchildren[i + 1])++;
        wsect(xint(cb), &child);
        _btinsert(&nchild, ncb, dir);
      } else {
        (dnode->nchildren[i])++;
        wsect(xint(ncb), &nchild);
        _btinsert(&child, cb, dir);
      }
    } else {
      (dnode->nchildren[i])++;
      _btinsert(&child, cb, dir);
    }
  }
  wsect(xint(db), dnode);
}

uint
_btsplit(struct dirnode *parent, uint pb, int idx, struct dirnode *child, uint pcb, struct dirnode *nchild)
{
  int i;
  uint ncb;
  // number of children moved
  ushort nchildren;

  ncb = _btalloc(nchild);
  nchild->leaf = child->leaf;
  nchild->ndirs = BTDEGREE - 1;
  // move BTDEGREE - 1 dirents and, if leaf, BTDEGREE children
  nchildren = 0;
  for(i = 0; i < BTDEGREE - 1; i++) {
    nchildren++;
    _direntcp(&nchild->dirs[i], &child->dirs[i + BTDEGREE]);
  }
  if(!child->leaf) {
    for(i = 0; i < BTDEGREE; i++) {
      nchildren += child->nchildren[i + BTDEGREE];
      nchild->children[i] = xint(child->children[i + BTDEGREE]);
      nchild->nchildren[i] = xint(child->nchildren[i + BTDEGREE]);
    }
  }
  child->ndirs = BTDEGREE - 1;
  // insert median dirent into parent
  _direntinsert(parent, idx, &child->dirs[BTDEGREE - 1], idx + 1, ncb, nchildren);
  // adjust nchildren in parent, accounting for median dirent that was moved up to the parent
  parent->nchildren[idx] -= (nchildren + 1);
  return ncb;
}


void
_direntcp(struct dirent *dst, struct dirent *src)
{
  *dst = *src;
  dst->inum = xshort(src->inum);
}

void
_direntinsert(struct dirnode *dnode, int idx, struct dirent *dir, int cidx, uint cb,
              ushort nchildren)
{
  int i;
  
  for(i = dnode->ndirs - 1; i >= idx; i--) {
    _direntcp(&dnode->dirs[i + 1], &dnode->dirs[i]);
  }
  _direntcp(&dnode->dirs[idx], dir);
  if(cidx >= 0) {
    for(i = dnode->ndirs; i >= cidx; i--) {
      dnode->children[i + 1] = xint(dnode->children[i]);
      dnode->nchildren[i + 1] = xint(dnode->nchildren[i]);
    }
    dnode->children[cidx] = xint(cb);
    dnode->nchildren[cidx] = nchildren;
  }
  (dnode->ndirs)++;
}

ushort _countchildren(struct dirnode *dnode)
{
  int i, nchildren;

  nchildren = 0;
  for(i = 0; i < dnode->ndirs; i++) {
    nchildren++;
  }
  if(!dnode->leaf) {
    for(i = 0; i <= dnode->ndirs; i++) {
      nchildren += dnode->nchildren[i];
    }
  }
  return nchildren;
}


