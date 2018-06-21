// File system implementation.  Five layers:
//   + Blocks: allocator for raw disk blocks.
//   + Log: crash recovery for multi-step updates.
//   + Files: inode allocator, reading, writing, metadata.
//   + Directories: inode with special contents (list of other inodes!)
//   + Names: paths like /usr/rtm/xv6/fs.c for convenient naming.
//
// This file contains the low-level file system manipulation
// routines.  The (higher-level) system call implementations
// are in sysfile.c.

#include "types.h"
#include "defs.h"
#include "param.h"
#include "stat.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "buf.h"
#include "file.h"

#define min(a, b) ((a) < (b) ? (a) : (b))
static void itrunc(struct inode*);
// there should be one superblock per disk device, but we run with
// only one device
struct superblock sb;

// Read the super block.
void
readsb(int dev, struct superblock *sb)
{
  struct buf *bp;

  bp = bread(dev, 1);
  memmove(sb, bp->data, sizeof(*sb));
  brelse(bp);
}

// Zero a block.
static void
bzero(int dev, int bno)
{
  struct buf *bp;

  bp = bread(dev, bno);
  memset(bp->data, 0, BSIZE);
  log_write(bp);
  brelse(bp);
}

// Blocks.

// Allocate a zeroed disk block.
static uint
balloc(uint dev)
{
  int b, bi, m;
  struct buf *bp;

  bp = 0;
  for(b = 0; b < sb.size; b += BPB){
    bp = bread(dev, BBLOCK(b, sb));
    for(bi = 0; bi < BPB && b + bi < sb.size; bi++){
      m = 1 << (bi % 8);
      if((bp->data[bi/8] & m) == 0){  // Is block free?
        bp->data[bi/8] |= m;  // Mark block in use.
        log_write(bp);
        brelse(bp);
        bzero(dev, b + bi);
        return b + bi;
      }
    }
    brelse(bp);
  }
  panic("balloc: out of blocks");
}

// Free a disk block.
static void
bfree(int dev, uint b)
{
  struct buf *bp;
  int bi, m;

  readsb(dev, &sb);
  bp = bread(dev, BBLOCK(b, sb));
  bi = b % BPB;
  m = 1 << (bi % 8);
  if((bp->data[bi/8] & m) == 0)
    panic("freeing free block");
  bp->data[bi/8] &= ~m;
  log_write(bp);
  brelse(bp);
}

// Inodes.
//
// An inode describes a single unnamed file.
// The inode disk structure holds metadata: the file's type,
// its size, the number of links referring to it, and the
// list of blocks holding the file's content.
//
// The inodes are laid out sequentially on disk at
// sb.startinode. Each inode has a number, indicating its
// position on the disk.
//
// The kernel keeps a cache of in-use inodes in memory
// to provide a place for synchronizing access
// to inodes used by multiple processes. The cached
// inodes include book-keeping information that is
// not stored on disk: ip->ref and ip->valid.
//
// An inode and its in-memory representation go through a
// sequence of states before they can be used by the
// rest of the file system code.
//
// * Allocation: an inode is allocated if its type (on disk)
//   is non-zero. ialloc() allocates, and iput() frees if
//   the reference and link counts have fallen to zero.
//
// * Referencing in cache: an entry in the inode cache
//   is free if ip->ref is zero. Otherwise ip->ref tracks
//   the number of in-memory pointers to the entry (open
//   files and current directories). iget() finds or
//   creates a cache entry and increments its ref; iput()
//   decrements ref.
//
// * Valid: the information (type, size, &c) in an inode
//   cache entry is only correct when ip->valid is 1.
//   ilock() reads the inode from
//   the disk and sets ip->valid, while iput() clears
//   ip->valid if ip->ref has fallen to zero.
//
// * Locked: file system code may only examine and modify
//   the information in an inode and its content if it
//   has first locked the inode.
//
// Thus a typical sequence is:
//   ip = iget(dev, inum)
//   ilock(ip)
//   ... examine and modify ip->xxx ...
//   iunlock(ip)
//   iput(ip)
//
// ilock() is separate from iget() so that system calls can
// get a long-term reference to an inode (as for an open file)
// and only lock it for short periods (e.g., in read()).
// The separation also helps avoid deadlock and races during
// pathname lookup. iget() increments ip->ref so that the inode
// stays cached and pointers to it remain valid.
//
// Many internal file system functions expect the caller to
// have locked the inodes involved; this lets callers create
// multi-step atomic operations.
//
// The icache.lock spin-lock protects the allocation of icache
// entries. Since ip->ref indicates whether an entry is free,
// and ip->dev and ip->inum indicate which i-node an entry
// holds, one must hold icache.lock while using any of those fields.
//
// An ip->lock sleep-lock protects all ip-> fields other than ref,
// dev, and inum.  One must hold ip->lock in order to
// read or write that inode's ip->valid, ip->size, ip->type, &c.

struct {
  struct spinlock lock;
  struct inode inode[NINODE];
} icache;

void
iinit(int dev)
{
  int i = 0;
  
  initlock(&icache.lock, "icache");
  for(i = 0; i < NINODE; i++) {
    initsleeplock(&icache.inode[i].lock, "inode");
  }

  readsb(dev, &sb);
  cprintf("sb: size %d nblocks %d ninodes %d nlog %d logstart %d\
 inodestart %d bmap start %d\n", sb.size, sb.nblocks,
          sb.ninodes, sb.nlog, sb.logstart, sb.inodestart,
          sb.bmapstart);
}

static struct inode* iget(uint dev, uint inum);

//PAGEBREAK!
// Allocate an inode on device dev.
// Mark it as allocated by  giving it type type.
// Returns an unlocked but allocated and referenced inode.
struct inode*
ialloc(uint dev, short type)
{
  int inum;
  struct buf *bp;
  struct dinode *dip;

  for(inum = 1; inum < sb.ninodes; inum++){
    bp = bread(dev, IBLOCK(inum, sb));
    dip = (struct dinode*)bp->data + inum%IPB;
    if(dip->type == 0){  // a free inode
      memset(dip, 0, sizeof(*dip));
      dip->type = type;
      log_write(bp);   // mark it allocated on the disk
      brelse(bp);
      return iget(dev, inum);
    }
    brelse(bp);
  }
  panic("ialloc: no inodes");
}

// Copy a modified in-memory inode to disk.
// Must be called after every change to an ip->xxx field
// that lives on disk, since i-node cache is write-through.
// Caller must hold ip->lock.
void
iupdate(struct inode *ip)
{
  struct buf *bp;
  struct dinode *dip;

  bp = bread(ip->dev, IBLOCK(ip->inum, sb));
  dip = (struct dinode*)bp->data + ip->inum%IPB;
  dip->type = ip->type;
  dip->major = ip->major;
  dip->minor = ip->minor;
  dip->nlink = ip->nlink;
  dip->size = ip->size;
  memmove(dip->addrs, ip->addrs, sizeof(ip->addrs));
  log_write(bp);
  brelse(bp);
}

// Find the inode with number inum on device dev
// and return the in-memory copy. Does not lock
// the inode and does not read it from disk.
static struct inode*
iget(uint dev, uint inum)
{
  struct inode *ip, *empty;

  acquire(&icache.lock);

  // Is the inode already cached?
  empty = 0;
  for(ip = &icache.inode[0]; ip < &icache.inode[NINODE]; ip++){
    if(ip->ref > 0 && ip->dev == dev && ip->inum == inum){
      ip->ref++;
      release(&icache.lock);
      return ip;
    }
    if(empty == 0 && ip->ref == 0)    // Remember empty slot.
      empty = ip;
  }

  // Recycle an inode cache entry.
  if(empty == 0)
    panic("iget: no inodes");

  ip = empty;
  ip->dev = dev;
  ip->inum = inum;
  ip->ref = 1;
  ip->valid = 0;
  release(&icache.lock);

  return ip;
}

// Increment reference count for ip.
// Returns ip to enable ip = idup(ip1) idiom.
struct inode*
idup(struct inode *ip)
{
  acquire(&icache.lock);
  ip->ref++;
  release(&icache.lock);
  return ip;
}

// Lock the given inode.
// Reads the inode from disk if necessary.
void
ilock(struct inode *ip)
{
  struct buf *bp;
  struct dinode *dip;

  if(ip == 0 || ip->ref < 1)
    panic("ilock");

  acquiresleep(&ip->lock);

  if(ip->valid == 0){
    bp = bread(ip->dev, IBLOCK(ip->inum, sb));
    dip = (struct dinode*)bp->data + ip->inum%IPB;
    ip->type = dip->type;
    ip->major = dip->major;
    ip->minor = dip->minor;
    ip->nlink = dip->nlink;
    ip->size = dip->size;
    memmove(ip->addrs, dip->addrs, sizeof(ip->addrs));
    brelse(bp);
    ip->valid = 1;
    if(ip->type == 0)
      panic("ilock: no type");
  }
}

// Unlock the given inode.
void
iunlock(struct inode *ip)
{
  if(ip == 0 || !holdingsleep(&ip->lock) || ip->ref < 1)
    panic("iunlock");

  releasesleep(&ip->lock);
}

// Drop a reference to an in-memory inode.
// If that was the last reference, the inode cache entry can
// be recycled.
// If that was the last reference and the inode has no links
// to it, free the inode (and its content) on disk.
// All calls to iput() must be inside a transaction in
// case it has to free the inode.
void
iput(struct inode *ip)
{
  acquiresleep(&ip->lock);
  if(ip->valid && ip->nlink == 0){
    acquire(&icache.lock);
    int r = ip->ref;
    release(&icache.lock);
    if(r == 1){
      // inode has no links and no other references: truncate and free.
      itrunc(ip);
      ip->type = 0;
      iupdate(ip);
      ip->valid = 0;
    }
  }
  releasesleep(&ip->lock);

  acquire(&icache.lock);
  ip->ref--;
  release(&icache.lock);
}

// Common idiom: unlock, then put.
void
iunlockput(struct inode *ip)
{
  iunlock(ip);
  iput(ip);
}

//PAGEBREAK!
// Inode content
//
// The content (data) associated with each inode is stored
// in blocks on the disk. The first NDIRECT block numbers
// are listed in ip->addrs[].  The next NINDIRECT blocks are
// listed in block ip->addrs[NDIRECT].

// Return the disk block address of the nth block in inode ip.
// If there is no such block, bmap allocates one.
static uint
bmap(struct inode *ip, uint bn)
{
  uint addr, *a;
  struct buf *bp;

  if(bn < NDIRECT){
    if((addr = ip->addrs[bn]) == 0)
      ip->addrs[bn] = addr = balloc(ip->dev);
    return addr;
  }
  bn -= NDIRECT;

  if(bn < NINDIRECT){
    // Load indirect block, allocating if necessary.
    if((addr = ip->addrs[NDIRECT]) == 0)
      ip->addrs[NDIRECT] = addr = balloc(ip->dev);
    bp = bread(ip->dev, addr);
    a = (uint*)bp->data;
    if((addr = a[bn]) == 0){
      a[bn] = addr = balloc(ip->dev);
      log_write(bp);
    }
    brelse(bp);
    return addr;
  }

  panic("bmap: out of range");
}

// Truncate inode (discard contents).
// Only called when the inode has no links
// to it (no directory entries referring to it)
// and has no in-memory reference to it (is
// not an open file or current directory).
static void
itrunc(struct inode *ip)
{
  int i, j;
  struct buf *bp;
  uint *a;

  for(i = 0; i < NDIRECT; i++){
    if(ip->addrs[i]){
      bfree(ip->dev, ip->addrs[i]);
      ip->addrs[i] = 0;
    }
  }

  if(ip->addrs[NDIRECT]){
    bp = bread(ip->dev, ip->addrs[NDIRECT]);
    a = (uint*)bp->data;
    for(j = 0; j < NINDIRECT; j++){
      if(a[j])
        bfree(ip->dev, a[j]);
    }
    brelse(bp);
    bfree(ip->dev, ip->addrs[NDIRECT]);
    ip->addrs[NDIRECT] = 0;
  }

  ip->size = 0;
  iupdate(ip);
}

// Copy stat information from inode.
// Caller must hold ip->lock.
void
stati(struct inode *ip, struct stat *st)
{
  st->dev = ip->dev;
  st->ino = ip->inum;
  st->type = ip->type;
  st->nlink = ip->nlink;
  st->size = ip->size;
}

//PAGEBREAK!
// Read data from inode.
// Caller must hold ip->lock.
int
readi(struct inode *ip, char *dst, uint off, uint n)
{
  uint tot, m;
  struct buf *bp; 

  if(ip->type == T_DEV){
    if(ip->major < 0 || ip->major >= NDEV || !devsw[ip->major].read)
      return -1;
    return devsw[ip->major].read(ip, dst, n);
  }

  if(off > ip->size || off + n < off)
    return -1;
  if(off + n > ip->size)
    n = ip->size - off;

  if(ip->type == T_DIR){
    dirread(ip, dst, off, n);
  } else {
    for(tot=0; tot<n; tot+=m, off+=m, dst+=m){
      bp = bread(ip->dev, bmap(ip, off/BSIZE));
      m = min(n - tot, BSIZE - off%BSIZE);
      memmove(dst, bp->data + off%BSIZE, m);
      brelse(bp);
    }
  }
  return n;
}

// PAGEBREAK!
// Write data to inode.
// Caller must hold ip->lock.
int
writei(struct inode *ip, char *src, uint off, uint n)
{
  uint tot, m;
  struct buf *bp;

  if(ip->type == T_DEV){
    if(ip->major < 0 || ip->major >= NDEV || !devsw[ip->major].write)
      return -1;
    return devsw[ip->major].write(ip, src, n);
  }

  if(off > ip->size || off + n < off)
    return -1;
  if(off + n > MAXFILE*BSIZE)
    return -1;

  for(tot=0; tot<n; tot+=m, off+=m, src+=m){
    bp = bread(ip->dev, bmap(ip, off/BSIZE));
    m = min(n - tot, BSIZE - off%BSIZE);
    memmove(bp->data + off%BSIZE, src, m);
    log_write(bp);
    brelse(bp);
  }

  if(n > 0 && off > ip->size){
    ip->size = off;
    iupdate(ip);
  }
  return n;
}

//PAGEGREAK!
// Directories
struct btnode {
  struct inode *dp;
  struct buf *bp;
  struct dirnode dnode;
};

int
namecmp(const char *s, const char *t)
{
  return strncmp(s, t, DIRSIZ);
}

static void
namecpy(char *s, const char *t)
{
  memmove(s, t, DIRSIZ);
}

struct {
  struct spinlock lock;
  struct btnode btnode[NBTNODE];
} btcache;

static ushort
btcntchildren(struct btnode *btp)
{
  int i, nchildren;

  nchildren = 0;
  for(i = 0; i < btp->dnode.ndirs; i++) {
    nchildren++;
  }
  if(!btp->dnode.leaf) {
    for(i = 0; i <= btp->dnode.ndirs; i++) {
      nchildren += btp->dnode.nchildren[i];
    }
  }
  return nchildren;
}

static void
btrelse(struct btnode *btp)
{
  brelse(btp->bp);

  acquire(&btcache.lock);
  btp->bp = 0;
  release(&btcache.lock);
}

static void
btfree(struct btnode *btp)
{
  uint dev, blockno;

  dev = btp->dp->dev;
  blockno = btp->bp->blockno;
  btrelse(btp);
  bfree(dev, blockno);
}

static struct btnode*
btget(void)
{
  struct btnode *btp;
  int i;

  acquire(&btcache.lock);
  for(i = 0; i < NBTNODE; i++) {
    if(btcache.btnode[i].bp == 0) {
      btp = &btcache.btnode[i];
      break;
    }
  }
  release(&btcache.lock);
  
  if(i == NBTNODE) {
    panic("btget: no btnodes");
  }
  return btp;
  
}

static struct btnode*
btload(struct inode *dp, uint addr)
{
  struct btnode *btp;

  btp = btget();
  btp->bp = bread(dp->dev, addr);
  btp->dp = dp;
  memmove(&btp->dnode, btp->bp->data, sizeof(btp->bp->data));

  return btp;
}

static struct btnode*
btalloc(struct inode *dp)
{
  struct btnode *btp;
  uint addr;

  addr = balloc(dp->dev);
  btp = btload(dp, addr);
  memset(&btp->dnode, 0, sizeof(btp->dnode));

  return btp;
}

static void
btwrite(struct btnode *btp)
{
  memmove(btp->bp->data, &btp->dnode, sizeof(btp->dnode));
  bwrite(btp->bp);
}

static void
btwrelse(struct btnode *btp)
{
  btwrite(btp);
  btrelse(btp);
}

static void
direntinsert(struct btnode *btp, int idx, struct dirent *dir, int cidx, uint cb,
             ushort nchildren)
{
  int i;
  
  for(i = btp->dnode.ndirs - 1; i >= idx; i--) {
    btp->dnode.dirs[i + 1] = btp->dnode.dirs[i];
  }
  btp->dnode.dirs[idx] = *dir;
  if(cidx >= 0) {
    for(i = btp->dnode.ndirs; i >= cidx; i--) {
      btp->dnode.children[i + 1] = btp->dnode.children[i];
      btp->dnode.nchildren[i + 1] = btp->dnode.nchildren[i];
    }
    btp->dnode.children[cidx] = cb;
    btp->dnode.nchildren[cidx] = nchildren;
  }
  (btp->dnode.ndirs)++;
}

static void
direntdelete(struct btnode *btp, int idx, int cidx)
{
  int i;
  
  for(i = idx; i < btp->dnode.ndirs - 1; i++) {
    btp->dnode.dirs[i] = btp->dnode.dirs[i + 1];
  }
  if(cidx >= 0) {
      for(i = cidx; i < btp->dnode.ndirs; i++) {
        btp->dnode.children[i] = btp->dnode.children[i + 1];
        btp->dnode.nchildren[i] = btp->dnode.nchildren[i + 1];
      }
  }
  (btp->dnode.ndirs)--;
}

/*
static 
void btprint(struct btnode *btp, int lvl)
{
  int i, j;
  struct btnode *btcp;

  if(!btp->dnode.leaf) {
    btcp = btload(btp->dp, btp->dnode.children[btp->dnode.ndirs]);
    btprint(btcp, lvl + 1);
  }
  for(i = btp->dnode.ndirs - 1; i >= 0; i--) {
    for (j = 0; j < lvl; j++) {
      cprintf(" ");
    }
    if(i == 0 && !btp->dnode.leaf) {
      cprintf("(%d)%s", btp->dnode.nchildren[0], btp->dnode.dirs[i].name);
    } else {
      cprintf("%s", btp->dnode.dirs[i].name);
    }
    if(!btp->dnode.leaf) {
      cprintf("(%d)\n", btp->dnode.nchildren[i + 1]);
      btcp = btload(btp->dp, btp->dnode.children[i]);
      btprint(btcp, lvl + 1);
    } else {
      cprintf("\n");
    }
  }
  btrelse(btp);
}
*/

static struct inode*
btlookup(struct btnode *btp, char *name)
{
  struct inode *ip;
  struct btnode *btcp;
  int i, c;

  i = 0;
  while(i < btp->dnode.ndirs && (c = namecmp(name, btp->dnode.dirs[i].name)) > 0) {
    i++;
  }
  if(i < btp->dnode.ndirs && c == 0) {
    ip = iget(btp->dp->dev, btp->dnode.dirs[i].inum);
    btrelse(btp);
    return ip;
  }
  if(btp->dnode.leaf) {
    btrelse(btp);
    return 0;
  }
  btcp = btload(btp->dp, btp->dnode.children[i]);
  ip = btlookup(btcp, name);
  btrelse(btp);
  
  return ip;
}

static struct btnode *
btsplit(struct btnode *btpp, int idx, struct btnode *btcp)
{
  struct btnode *btncp;
  int i;
  
  // number of children moved
  ushort nchildren;

  btncp = btalloc(btpp->dp);
  btncp->dnode.leaf = btcp->dnode.leaf;
  btncp->dnode.ndirs = BTDEGREE - 1;
  // move BTDEGREE - 1 dirents and, if leaf, BTDEGREE children
  nchildren = 0;
  for(i = 0; i < BTDEGREE - 1; i++) {
    nchildren++;
    btncp->dnode.dirs[i] = btcp->dnode.dirs[i + BTDEGREE];
  }
  if(!btcp->dnode.leaf) {
    for(i = 0; i < BTDEGREE; i++) {
      nchildren += btcp->dnode.nchildren[i + BTDEGREE];
      btncp->dnode.children[i] = btcp->dnode.children[i + BTDEGREE];
      btncp->dnode.nchildren[i] = btcp->dnode.nchildren[i + BTDEGREE];
    }
  }
  btcp->dnode.ndirs = BTDEGREE - 1;
  // insert median dirent into parent
  direntinsert(btpp, idx, &btcp->dnode.dirs[BTDEGREE - 1], idx + 1, btncp->bp->blockno, nchildren);
  // adjust nchildren in parent, accounting for median dirent that was moved up to the parent
  btpp->dnode.nchildren[idx] -= (nchildren + 1);
  return btncp;
}

static void
btinsert(struct btnode *btp, struct dirent *dir)
{
  struct btnode *btcp, *btncp;
  int i;

  i = btp->dnode.ndirs - 1;
  while(i >= 0 && strncmp(dir->name, btp->dnode.dirs[i].name, DIRSIZ) < 0) {
    i--;
  }
  if(btp->dnode.leaf) {
    direntinsert(btp, i + 1, dir, -1, 0, 0);
  } else {
    // insert into appropriate leaf node rooted at this subtree
    i++;
    btcp = btload(btp->dp, btp->dnode.children[i]);
    if(btcp->dnode.ndirs == 2 * BTDEGREE - 1) {
      // split a full child into two smaller ones before descending
      btncp = btsplit(btp, i, btcp);
      if(strncmp(dir->name, btp->dnode.dirs[i].name, DIRSIZ) > 0) {
        (btp->dnode.nchildren[i + 1])++;
        btwrelse(btcp);
        btinsert(btncp, dir);
      } else {
        (btp->dnode.nchildren[i])++;
        btwrelse(btncp);
        btinsert(btcp, dir);
      }
    } else {
      (btp->dnode.nchildren[i])++;
      btinsert(btcp, dir);
    }
  }
  btwrelse(btp);
}

// TODO check naming convention
static void
btmerge(struct btnode *btp, int idx, struct btnode *btcp, struct btnode *btncp)
{
  int i;
  // number of children moved
  ushort nchildren;
  
  btcp->dnode.dirs[btcp->dnode.ndirs] = btp->dnode.dirs[idx];
  (btcp->dnode.ndirs)++;

  // move all of next child's dirents and, if internal node, children
  nchildren = 0;
  for(i = 0; i < btncp->dnode.ndirs; i++) {
    nchildren++;
    btcp->dnode.dirs[btcp->dnode.ndirs + i] = btncp->dnode.dirs[i];
  }
  if(!btcp->dnode.leaf) {
    for(i = 0; i <= btncp->dnode.ndirs; i++) {
      nchildren += btncp->dnode.nchildren[i];
      btcp->dnode.children[btcp->dnode.ndirs + i] = btncp->dnode.children[i];
      btcp->dnode.nchildren[btcp->dnode.ndirs + i] = btncp->dnode.nchildren[i];
    }
  }
  btcp->dnode.ndirs += btncp->dnode.ndirs;
  direntdelete(btp, idx, idx + 1);
  // adjust nchildren in parent, accounting for the median dirent was moved down from the parent
  btp->dnode.nchildren[idx] += (nchildren + 1);
  // next child no longer needed and search will proceed from child
  btfree(btncp);
}

static void
btpexchange(struct btnode *btp, int idx, struct btnode *btcp, struct btnode *btpcp)
{
  // number of children moved
  uint nchildren;
  
  nchildren = (btpcp->dnode.nchildren[btpcp->dnode.ndirs] + 1);
  direntinsert(btcp, 0, &btp->dnode.dirs[idx], 0, btpcp->dnode.children[btpcp->dnode.ndirs], btpcp->dnode.nchildren[btpcp->dnode.ndirs]);
  btp->dnode.dirs[idx] = btpcp->dnode.dirs[btpcp->dnode.ndirs - 1];
  direntdelete(btpcp, btpcp->dnode.ndirs - 1, btpcp->dnode.ndirs);
  // adjust nchildren in parent, accounting for the previous child's last dirent and its it's children that were just moved
  btp->dnode.nchildren[idx] -= nchildren;
  btp->dnode.nchildren[idx + 1] += nchildren;
  btwrelse(btpcp);
}

static void
btnexchange(struct btnode *btp, int idx, struct btnode *btcp, struct btnode *btncp)
{
  // number of children moved
  uint nchildren;
  
  nchildren = (btncp->dnode.nchildren[0] + 1);
  direntinsert(btcp, btcp->dnode.ndirs, &btp->dnode.dirs[idx], btcp->dnode.ndirs + 1, btncp->dnode.children[0], btncp->dnode.nchildren[0]);
  btp->dnode.dirs[idx] = btncp->dnode.dirs[0];
  direntdelete(btncp, 0, 0);
  // adjust nchildren in parent, accounting for the next child's first dirent and its children that were just moved
  btp->dnode.nchildren[idx] += nchildren;
  btp->dnode.nchildren[idx + 1] -= nchildren;
  btwrelse(btncp);
}

static void
btdelete(struct btnode *btp, char *name, struct dirent *replace, int release)
{
  struct btnode *btcp, *btncp, *btpcp;
  int i, c, exchanged = 0;

  i = btp->dnode.ndirs - 1;
  while(i >= 0 && (c = strncmp(name, btp->dnode.dirs[i].name, DIRSIZ)) < 0) {
    i--;
  }
  if(c == 0) {
    // dirent was found
    if(btp->dnode.leaf) {
      direntdelete(btp, i, -1);
    } else {
      btcp = btload(btp->dp, btp->dnode.children[i]);
      if(btcp->dnode.ndirs >= BTDEGREE) {
        (btp->dnode.nchildren[i])--;
        btdelete(btcp, name, &btp->dnode.dirs[i], 1);
      }
      else {
        btncp = btload(btp->dp, btp->dnode.children[i + 1]);
        if(btncp->dnode.ndirs >= BTDEGREE) {
          btrelse(btcp);
          (btp->dnode.nchildren[i + 1])--;
          btdelete(btncp, name, &btp->dnode.dirs[i], 1);
        } else {
          btmerge(btp, i, btcp, btncp);
          (btp->dnode.nchildren[i])--;
          btdelete(btcp, name, 0, 1);
        }
      }
    }
  } else {
    // dirent was not found
    if(btp->dnode.leaf) {
      if(replace != 0) {
        if(i < 0) {
          *replace = btp->dnode.dirs[0];
          direntdelete(btp, 0, -1);
        } else {
          *replace = btp->dnode.dirs[i];
          direntdelete(btp, i, -1);
        }
      }
    } else {
      i++;
      btcp = btload(btp->dp, btp->dnode.children[i]);
      if(btcp->dnode.ndirs < BTDEGREE) {
        if(i > 0) {
          btpcp = btload(btp->dp, btp->dnode.children[i - 1]);
          if(btpcp->dnode.ndirs >= BTDEGREE) {
            btpexchange(btp, i - 1, btcp, btpcp);
            (btp->dnode.nchildren[i])--;
            btdelete(btcp, name, replace, 1);
            exchanged = 1;
          }
        }
        if(!exchanged) {
          if(i < btp->dnode.ndirs) {
            btncp = btload(btp->dp, btp->dnode.children[i + 1]);
            if(btncp->dnode.ndirs >= BTDEGREE) {
              if(i > 0) {
                btrelse(btpcp);
              }
              btnexchange(btp, i, btcp, btncp);
              (btp->dnode.nchildren[i])--;
              btdelete(btcp, name, replace, 1);
              exchanged = 1;
            }
          }
        }
        if(!exchanged) {
          if(i > 0) {
            if(i < btp->dnode.ndirs) {
              btrelse(btncp);
            }
            btmerge(btp, i - 1, btpcp, btcp);
            (btp->dnode.nchildren[i - 1])--;
            btdelete(btpcp, name, replace, 1);
          } else if(i < btp->dnode.ndirs) {
            btmerge(btp, i, btcp, btncp);
            (btp->dnode.nchildren[i])--;
            btdelete(btcp, name, replace, 1);
          } else {
            panic("btdelete not enough children");
          }
        }
      } else {
        (btp->dnode.nchildren[i])--;
        btdelete(btcp, name, replace, 1);
      }
    }
  }
  if(release) {
    btwrelse(btp);
  }
}

static 
int btread(struct btnode *btp, char *dst, uint off, uint start, uint end)
{
  uint offend;
  int i, cnt, total;
  struct btnode *btcp;
  uchar *src;

  total = 0;
  for(i = 0; i < btp->dnode.ndirs; i++) {
    if(!btp->dnode.leaf) {
      offend = off + btp->dnode.nchildren[i] * sizeof(btp->dnode.dirs[i]);
      if(end > off && start < offend) {
        // child overlap
        btcp = btload(btp->dp, btp->dnode.children[i]);
        cnt = btread(btcp, dst, off, start, end);
        dst += cnt;
        total += cnt;
      }
      off = offend;
    }
    offend = off + sizeof(btp->dnode.dirs[i]);
    if(end > off && start < offend) {
      // overlap, start copying
      cnt = sizeof(btp->dnode.dirs[i]);
      if(off >= start) {
        // starting before dirent
        src = (uchar*)&btp->dnode.dirs[i];
      } else {
        // starting after dirent starts
        src = (uchar*)&btp->dnode.dirs[i] + (start - off);
        cnt -= (start - off);
      }
      if (end < offend) {
        // finishing before the end of dirent
        cnt -= (offend - end);
      }
      memmove(dst, src, cnt);
      dst += cnt;
      total += cnt;
    }
    off = offend;
  }
  if(!btp->dnode.leaf) {
    offend = off + btp->dnode.nchildren[i] * sizeof(btp->dnode.dirs[i]);
    if(end > off && start < offend) {
      // final child overlap
      btcp = btload(btp->dp, btp->dnode.children[i]);
      total += btread(btcp, dst, off, start, end);
    }
  }
  btrelse(btp);

  return total;
}

/*
void
dirprint(struct inode *dp)
{
  struct btnode *btrp;
  
  if(dp->addrs[0] == 0) {
    return;
  }

  btrp = btload(dp, dp->addrs[0]);
  btprint(btrp, 0);
}
*/

// Write a new directory entry (name, inum) into the directory dp.
int
dirlink(struct inode *dp, char *name, uint inum)
{
  struct inode *ip;
  struct btnode *btrp, *btp, *btncp;
  struct dirent dir;

  // Check that name is not present.
  if((ip = dirlookup(dp, name)) != 0){
    iput(ip);
    return -1;
  }

  namecpy(dir.name, name);
  dir.inum = inum;
  
  if(dp->addrs[0] == 0) {
    // empty root
    btrp = btalloc(dp);
    btrp->dnode.leaf = 1;
    dp->addrs[0] = btrp->bp->blockno;
  } else {
    btrp = btload(dp, dp->addrs[0]);
  }

  if(btrp->dnode.ndirs == 2 * BTDEGREE - 1) {
    btp = btalloc(dp);
    btp->dnode.children[0] = btrp->bp->blockno;
    btp->dnode.nchildren[0] = btcntchildren(btrp);
    // new root
    dp->addrs[0] = btp->bp->blockno;
    btncp = btsplit(btp, 0, btrp);
    if(strncmp(name, btp->dnode.dirs[0].name, DIRSIZ) > 0) {
      (btp->dnode.nchildren[1])++;
      btwrelse(btrp);
      btinsert(btncp, &dir);
    } else {
      (btp->dnode.nchildren[0])++;
      btwrelse(btncp);
      btinsert(btrp, &dir);
    }
    btwrelse(btp);
  } else {
    btinsert(btrp, &dir);
  }

  dp->size += sizeof(dir);
  iupdate(dp);
  
  return 0;
}

// Look for a directory entry in a directory.
struct inode *
dirlookup(struct inode *ip, char *name)
{
  struct btnode *btrp;

  if(ip->type != T_DIR) {
    panic("dirlookup not DIR");
  }
  if(ip->addrs[0] == 0) {
    return 0;
  }
  btrp = btload(ip, ip->addrs[0]);
  
  return btlookup(btrp, name);

}

int
dirremove(struct inode *dp, char *name)
{
  // name checked for existence before calling this
  // function
  struct btnode *btrp;

  // don't release root as it's needed below
  btrp = btload(dp, dp->addrs[0]);
  btdelete(btrp, name, 0, 0);
  if(btrp->dnode.ndirs == 0) {
    if(btrp->dnode.leaf) {
      // no more entries
      dp->addrs[0] = 0;
      btfree(btrp);
    } else {
      // adjust root
      dp->addrs[0] = btrp->dnode.children[0];
      btwrelse(btrp);      
    }
  } else {
     btwrelse(btrp);
  }

  dp->size -= sizeof(struct dirent);
  iupdate(dp);

  return 0;
}

void
dirread(struct inode *dp, char *dst, uint off, uint n)
{
  // off and n verified in range before calling this function
  struct btnode *btrp;

  if(dp->addrs[0] == 0) {
    return;
  }

  btrp = btload(dp, dp->addrs[0]);
  btread(btrp, dst, 0, off, off + n);
}

//PAGEBREAK!
// Paths

// Copy the next path element from path into name.
// Return a pointer to the element following the copied one.
// The returned path has no leading slashes,
// so the caller can check *path=='\0' to see if the name is the last one.
// If no name to remove, return 0.
//
// Examples:
//   skipelem("a/bb/c", name) = "bb/c", setting name = "a"
//   skipelem("///a//bb", name) = "bb", setting name = "a"
//   skipelem("a", name) = "", setting name = "a"
//   skipelem("", name) = skipelem("////", name) = 0
//
static char*
skipelem(char *path, char *name)
{
  char *s;
  int len;

  while(*path == '/')
    path++;
  if(*path == 0)
    return 0;
  s = path;
  while(*path != '/' && *path != 0)
    path++;
  len = path - s;
  if(len >= DIRSIZ)
    memmove(name, s, DIRSIZ);
  else {
    memmove(name, s, len);
    name[len] = 0;
  }
  while(*path == '/')
    path++;
  return path;
}

// Look up and return the inode for a path name.
// If parent != 0, return the inode for the parent and copy the final
// path element into name, which must have room for DIRSIZ bytes.
// Must be called inside a transaction since it calls iput().
static struct inode*
namex(char *path, int nameiparent, char *name)
{
  struct inode *ip, *next;

  if(*path == '/')
    ip = iget(ROOTDEV, ROOTINO);
  else
    ip = idup(myproc()->cwd);

  while((path = skipelem(path, name)) != 0){
    ilock(ip);
    if(ip->type != T_DIR){
      iunlockput(ip);
      return 0;
    }
    if(nameiparent && *path == '\0'){
      // Stop one level early.
      iunlock(ip);
      return ip;
    }
    if((next = dirlookup(ip, name)) == 0){
      iunlockput(ip);
      return 0;
    }
    iunlockput(ip);
    ip = next;
  }
  if(nameiparent){
    iput(ip);
    return 0;
  }
  return ip;
}

struct inode*
namei(char *path)
{
  char name[DIRSIZ];
  return namex(path, 0, name);
}

struct inode*
nameiparent(char *path, char *name)
{
  return namex(path, 1, name);
}

