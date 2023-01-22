/* Weronika Tarnawska 331171 */
#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

// best sbrk_min = 512
#define SBRK_MIN 512
#define MIN(x, y) (x < y) ? x : y
/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */

// #define CHECKHEAP
#define VERBOSE 0
// #define DEBUG

#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
#endif

#ifdef CHECKHEAP
#define checkheap() mm_checkheap(VERBOSE)
#else
#define checkheap()
#endif

#define __unused __attribute__((unused))

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* !DRIVER */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */

static word_t *free_list; /* Pointer to the first block in free list */

static int start_class;
#define LISTNUM_MAX 8192 // 16384

/* one list of free blocks + pointers to the following size classes on the list
 */
static word_t *list16;  /* block size <= 16 bytes */
static word_t *list32;  /* <= 32 */
static word_t *list64;  /* <= 64 */
static word_t *list128; /* etc */
static word_t *list256;
static word_t *list512;
static word_t *list1024;
static word_t *list2048;
static word_t *list4096;
// static word_t *list8192;
static word_t *list_more; /* block size > 4096 */

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

static inline size_t bt_size(word_t *bt) {
  return *bt & -ALIGNMENT;
}

static inline bt_flags bt_getflags(word_t *bt) {
  return *bt & ~(-ALIGNMENT);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  *bt = size | flags;
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  word_t *next = (void *)bt + bt_size(bt);
  if (next == heap_end)
    return NULL;
  return next;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  if (bt == heap_start)
    return NULL;
  if (!bt_get_prevfree(bt))
    return NULL;
  word_t *prev_footer = (void *)bt - sizeof(word_t);
  return (void *)prev_footer - bt_size(prev_footer) + sizeof(word_t);
}

/* --=[ free list ]=-------------------------------------------- */

/* round up to nearest power of 2; if result > LISTNUM_MAX return LISTNUM_MAX */
static inline size_t clp2(size_t x) {
  x = x - 1;
  x = x | (x >> 1);
  x = x | (x >> 2);
  x = x | (x >> 4);
  x = x | (x >> 8);
  x = x | (x >> 16);
  x = x | (x >> 32);
  return MIN(x + 1, LISTNUM_MAX);
}

/* select a suitable list for the block of given size_class */
static inline word_t **choose_class(size_t size_class) {
  debug("size class: %ld", size_class);
  word_t **result = NULL;
  switch (size_class) {
    case 16:
      result = &list16;
      // result = &list32;
      break;
    case 32:
      result = &list32;
      break;
    case 64:
      result = &list64;
      break;
    case 128:
      result = &list128;
      break;
    case 256:
      result = &list256;
      break;
    case 512:
      result = &list512;
      break;
    case 1024:
      result = &list1024;
      break;
    case 2048:
      result = &list2048;
      break;
    case 4096:
      result = &list4096;
      break;
    // case 8192:
    //   result = &list8192;
    //   break;
    default:
      result = &list_more;
      break;
  }
  return result;
}

/* next block in the free list */
static inline word_t *fl_next(word_t *bt) {
  word_t *ptr = (void *)bt + sizeof(word_t);
  word_t *next = (void *)heap_start + *ptr;
  return next;
}

/* previous block in the free list */
static inline word_t *fl_prev(word_t *bt) {
  word_t *ptr = (void *)bt + 2 * sizeof(word_t);
  word_t *prev = (void *)heap_start + *ptr;
  return prev;
}

static inline void fl_set_next(word_t *bt, word_t *next) {
  word_t *ptr = (void *)bt + sizeof(word_t);
  *ptr = (void *)next - (void *)heap_start;
}

static inline void fl_set_prev(word_t *bt, word_t *prev) {
  word_t *ptr = (void *)bt + sizeof(word_t) + sizeof(word_t);
  *ptr = (void *)prev - (void *)heap_start;
}

/* search free list for the given block, return true if it's there */
static inline int fl_search(word_t *bt) {
  if (!free_list)
    return 0;
  word_t *i = free_list;
  do {
    if (i == bt)
      return 1;
    i = fl_next(i);
  } while (i != free_list);
  return 0;
}

/* add block to free list */
static inline void fl_add(word_t *bt) {
  size_t listnum = clp2(bt_size(bt));
  word_t **list = choose_class(listnum);
  if (!free_list) {
    /* no free blocks yet */
    fl_set_next(bt, bt);
    fl_set_prev(bt, bt);
    free_list = bt;
    *list = bt;
    return;
  } else {
    word_t *next = NULL;
    if (*list) {
      /* put the block at the front of it's free list */
      next = *list;
    } else {
      /* no blocks on this free list yet */
      /* if there is a list of larger blocks, put the block before the larger
       * size class */
      for (size_t i = listnum; !next && i <= LISTNUM_MAX; i *= 2) {
        word_t **nextlist = choose_class(i);
        next = *nextlist;
      }
      /* if there are no larger blocks, put the block at the end of free list */
      if (!next) {
        next = free_list;
      }
    }
    word_t *prev = fl_prev(next);
    fl_set_next(prev, bt);
    fl_set_next(bt, next);
    fl_set_prev(bt, prev);
    fl_set_prev(next, bt);
    *list = bt;
    if (listnum < start_class) {
      start_class = listnum;
      free_list = bt;
    }
  }
}

/* remove block from the free list */
static inline void fl_remove(word_t *bt) {
  size_t listnum = clp2(bt_size(bt));
  word_t **list = choose_class(listnum);
  if (!free_list) {
  } else if (bt == fl_next(bt)) {
    /* remove last block */
    free_list = NULL;
    *list = NULL;
  } else {
    word_t *prev = fl_prev(bt);
    word_t *next = fl_next(bt);
    fl_set_prev(next, prev);
    fl_set_next(prev, next);
    if (free_list == bt)
      free_list = next;
    if (*list == bt) {
      if (clp2(bt_size(next)) == listnum) {
        *list = next;
      } else {
        *list = NULL;
      }
    }
  }
}

/* coalescing */
static inline void merge_blocks(word_t *a, word_t *b) {
  size_t siz = bt_size(a) + bt_size(b);
  bt_flags flags = bt_getflags(a);
  word_t *footer = (void *)a + siz - sizeof(word_t);
  bt_make(a, siz, flags);
  bt_make(footer, siz, flags);
  if (b == last)
    last = a;
}

/* splitting */
static inline void split_block(word_t *bt, size_t size) {
  fl_remove(bt);
  size_t oldsz = bt_size(bt);
  bt_flags flags = bt_getflags(bt);
  bt_make(bt, size, flags);

  word_t *p = bt_next(bt);
  bt_make(p, oldsz - size, flags | PREVFREE);
  bt_make(bt_footer(p), oldsz - size, flags | PREVFREE);
  if (bt == last)
    last = p;

  bt_make(bt_footer(bt), size, flags);
  fl_add(bt);
  fl_add(p);
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return (size + sizeof(word_t) + ALIGNMENT - 1) & -ALIGNMENT;
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {
  void *ptr = morecore(ALIGNMENT - sizeof(word_t));
  if (!ptr)
    return -1;
  heap_start = NULL;
  heap_end = NULL;
  last = NULL;
  free_list = NULL;
  list16 = NULL;
  list32 = NULL;
  list64 = NULL;
  list128 = NULL;
  list256 = NULL;
  list512 = NULL;
  list1024 = NULL;
  list2048 = NULL;
  list4096 = NULL;
  // list8192 = NULL;
  list_more = NULL;
  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

static word_t *alloc_with_sbrk(size_t reqsz) {
  msg("alloc using morecore\n");

  if (!heap_start) {
    msg("\n!heap_start!\n");
    if (reqsz < SBRK_MIN) {
      msg("small block\n");
      word_t *res = morecore(SBRK_MIN);
      word_t *next = (void *)res + reqsz;
      heap_start = res;
      last = next;
      heap_end = (void *)res + SBRK_MIN;
      bt_make(res, reqsz, USED);
      bt_make(next, SBRK_MIN - reqsz, FREE);
      bt_make(bt_footer(next), SBRK_MIN - reqsz, FREE);
      fl_add(next);
      return res;
    }
    word_t *res = morecore(reqsz);
    last = res;
    heap_end = (void *)last + reqsz;
    heap_start = res;
    bt_make(res, reqsz, USED);
    return res;
  }

  if (reqsz < SBRK_MIN) {
    msg("small block\n");
    word_t *res = morecore(SBRK_MIN);
    word_t *next = (void *)res + reqsz;
    bt_flags pf = bt_free(last);
    last = next;
    heap_end = (void *)res + SBRK_MIN;
    bt_make(res, reqsz, USED);
    if (pf)
      bt_set_prevfree(res);
    else
      bt_clr_prevfree(res);
    bt_make(next, SBRK_MIN - reqsz, FREE);
    bt_make(bt_footer(next), SBRK_MIN - reqsz, FREE);
    fl_add(next);
    return res;
  }

  bt_flags pf = bt_free(last);
  word_t *res = morecore(reqsz);
  last = res;
  heap_end = (void *)last + reqsz;
  bt_make(res, reqsz, USED);
  if (pf)
    bt_set_prevfree(res);
  else
    bt_clr_prevfree(res);

  return res;
}

/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {

  if (free_list) {
    size_t size_class = clp2(reqsz);
    debug("req size: %ld, size class: %ld", reqsz, size_class);
    word_t *bt = NULL;
    for (size_t i = size_class; !bt && i <= LISTNUM_MAX; i *= 2) {
      word_t **nextlist = choose_class(i);
      bt = *nextlist;
    }

    while (bt) {
      // msg("loop\n");
      if (bt_size(bt) == reqsz) {
        msg("free block of exact size\n");
        fl_remove(bt);
        bt_flags flags = bt_get_prevfree(bt) | USED;
        bt_make(bt, reqsz, flags);
        return bt;
      } else if (bt_size(bt) > reqsz) {
        msg("alloc with split\n");
        split_block(bt, reqsz);
        bt_flags flags = bt_get_prevfree(bt) | USED;
        bt_make(bt, reqsz, flags);
        fl_remove(bt);
        return bt;
      }
      bt = fl_next(bt);
      if (bt == free_list)
        break;
    }
  }
  return NULL;
}

void *malloc(size_t size) {
  size_t reqsz = blksz(size);
  debug("MALLOC size: %ld", reqsz);
  word_t *fit = find_fit(reqsz);
  if (!fit) {
    fit = alloc_with_sbrk(reqsz);
  }
  word_t *next = bt_next(fit);
  if (next)
    bt_clr_prevfree(next);
  msg("malloced :)\n");
  checkheap();
  return bt_payload(fit);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  if (!ptr)
    return;

  word_t *bt = bt_fromptr(ptr);
  debug("FREE offset: %ld, size: %ld", (long)bt - (long)heap_start,
        bt_size(bt));
  bt_make(bt, bt_size(bt), FREE | bt_get_prevfree(bt));
  word_t *footer = bt_footer(bt);
  bt_make(footer, bt_size(bt), FREE | bt_get_prevfree(bt));

  word_t *next = bt_next(bt);
  if (next && bt_free(next)) {
    fl_remove(next);
    merge_blocks(bt, next);
  }
  if (bt_get_prevfree(bt)) {
    word_t *prev = bt_prev(bt);
    fl_remove(prev);
    merge_blocks(prev, bt);
    bt = prev;
  }
  fl_add(bt);
  next = bt_next(bt);
  if (next) {
    bt_set_prevfree(next);
  }
  msg("freed :)\n");
  checkheap();
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  debug("REALLOC offset: %ld, old size: %ld, new size %ld",
        (long)bt_fromptr(old_ptr) - (long)heap_start,
        bt_size(bt_fromptr(old_ptr)), blksz(size));

  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  /* If old block is enough, we can just return it */
  word_t *bt = bt_fromptr(old_ptr);
  if (bt_size(bt) - sizeof(word_t) >= size)
    return old_ptr;

  /* If it's the last block we can use morecore */
  // if (bt == last) {
  //   size_t reqsz = blksz(size - bt_size(bt));
  //   morecore(reqsz);
  //   bt_make(bt, bt_size(bt) + reqsz, bt_getflags(bt));
  //   heap_end = (void *)bt + bt_size(bt);
  // }
  /* That turned out to be a bad idea :( */

  /* If next block is free we can merge it with old block */
  word_t *next = bt_next(bt);
  size_t reqsz = blksz(size);
  if (next && bt_free(next) &&
      bt_size(bt) + bt_size(next) - sizeof(word_t) >= reqsz) {
    size_t addsize = reqsz - bt_size(bt);
    if (bt_size(next) - addsize > 0) {
      split_block(next, addsize);
    }

    fl_remove(next);
    merge_blocks(bt, next);

    next = bt_next(bt);
    if (next)
      bt_clr_prevfree(next);
    checkheap();
    return old_ptr;
  }

  void *new_ptr = malloc(size);
  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  // word_t *bt = bt_fromptr(old_ptr);
  size_t old_size = bt_size(bt);
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/* --=[ calloc ]=----------------------------------------------------------- */

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) { /* verbose=0: check only; verbose=1: print and
                                    check; verbose=2: print only */
  /* Print heap state and list of free blocks */
  if (verbose) {
    int i = 0;
    msg("\nHEAP\n");
    for (word_t *b = heap_start; b; b = bt_next(b), i++) {
      debug("block number %d, offset: %ld, size: %ld, used: %d, prevfree: %d",
            i, (long)b - (long)heap_start, bt_size(b), bt_used(b),
            bt_get_prevfree(b));
    }

    msg("\n");

    if (list16) {
      debug("list16 offset %ld", (long)list16 - (long)heap_start);
    }
    if (list32) {
      debug("list32 offset %ld", (long)list32 - (long)heap_start);
    }
    if (list64) {
      debug("list64 offset %ld", (long)list64 - (long)heap_start);
    }
    if (list128) {
      debug("list128 offset %ld", (long)list128 - (long)heap_start);
    }
    if (list256) {
      debug("list256 offset %ld", (long)list256 - (long)heap_start);
    }
    if (list512) {
      debug("list512 offset %ld", (long)list512 - (long)heap_start);
    }
    if (list1024) {
      debug("list1024 offset %ld", (long)list1024 - (long)heap_start);
    }
    if (list2048) {
      debug("list2048 offset %ld", (long)list2048 - (long)heap_start);
    }
    if (list4096) {
      debug("list4096 offset %ld", (long)list4096 - (long)heap_start);
    }
    if (list_more) {
      debug("list more offset %ld", (long)list_more - (long)heap_start);
    }

    i = 0;
    word_t *b = free_list;
    if (free_list) {
      msg("\nFREE LIST\n");
      do {
        debug("free block number %d, offset: %ld, size: %ld, next offset %ld, "
              "prev offset %ld",
              i, (long)b - (long)heap_start, bt_size(b),
              (long)fl_next(b) - (long)heap_start,
              (long)fl_prev(b) - (long)heap_start);
        b = fl_next(b);
        i++;
      } while (b != free_list);
    }
    msg("\n");
  }
  if (verbose < 2) {

    /* If prevfree is set then previous block is free and if the block is free
     * then prevfree is set in the next block */
    for (word_t *b = heap_start; b; b = bt_next(b)) {
      word_t *n = bt_next(b);
      if (bt_free(b) && n && !bt_get_prevfree(n)) {
        debug("%d", *b);
        perror("block free, but prevfree not set in the next block\n");
        exit(EXIT_FAILURE);
      }
      if (bt_used(b) && n && bt_get_prevfree(n)) {
        perror("prevfree set, but previous block is used\n");
        exit(EXIT_FAILURE);
      }
    }

    /* Every block on the free list is marked FREE */
    word_t *b = free_list;
    if (free_list) {
      do {
        if (bt_used(b)) {
          perror("used block in free list\n");
          exit(EXIT_FAILURE);
        }
        b = fl_next(b);
      } while (b != free_list);
    }

    /* Every free block is on the free list */
    for (word_t *b = heap_start; b; b = bt_next(b)) {
      if (bt_free(b) && !fl_search(b)) {
        perror("free block not in free list\n");
        exit(EXIT_FAILURE);
      }
    }

    /* There are no two consecutive free blocks */
    for (word_t *b = heap_start; b; b = bt_next(b)) {
      if (!heap_start)
        break;
      if (bt_free(b) && bt_get_prevfree(b)) {
        perror("two contiguous free blocks\n");
        exit(EXIT_FAILURE);
      }
    }

    /* next and prev pointers point to addresses inside head boundaries*/
    for (word_t *b = heap_start; b; b = bt_next(b)) {
      if (!heap_start)
        break;
      word_t *p = bt_prev(b);
      word_t *n = bt_next(b);
      if ((p && (void *)p < (void *)heap_start) ||
          (n && (void *)n > (void *)heap_end)) {
        perror("address outside the heap\n");
        exit(EXIT_FAILURE);
      }
    }

    // Ostatni blok faktycznie jest ostatni
    /* last is actually the last block */
    if (last && bt_next(last)) {
      perror("last does not point to the last block\n");
      exit(EXIT_FAILURE);
    }
  }
}
