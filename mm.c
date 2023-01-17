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

/* If you want debugging output, use the following macro.
 * When you hand in, remove the #define DEBUG line. */
#define VERBOSE 0
// #define DEBUG
#ifdef DEBUG
#define debug(fmt, ...) printf("%s: " fmt "\n", __func__, __VA_ARGS__)
#define msg(...) printf(__VA_ARGS__)
#else
#define debug(fmt, ...)
#define msg(...)
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
  debug("%d", *bt);
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  debug("%d", *bt);
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  word_t *next = (void *)bt + bt_size(bt);
  if (/*bt == last ||*/ next == heap_end)
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

static inline word_t *fl_next(word_t *bt) {
  // debug("%d", *bt);
  word_t **ptr = (void *)bt + sizeof(word_t);
  word_t *next = *ptr;
  return next;
}

static inline word_t *fl_prev(word_t *bt) {
  // debug("%d", *bt);
  word_t **ptr = (void *)bt + sizeof(word_t) + sizeof(word_t *);
  word_t *prev = *ptr;
  return prev;
}

static inline void fl_set_next(word_t *bt, word_t *next) {
  // debug("%d", *bt);
  word_t **ptr = (void *)bt + sizeof(word_t);
  *ptr = next;
}

static inline void fl_set_prev(word_t *bt, word_t *prev) {
  // debug("%d", *bt);
  word_t **ptr = (void *)bt + sizeof(word_t) + sizeof(word_t *);
  *ptr = prev;
}

static inline int fl_search(word_t *bt) {
  // debug("%d", *bt);
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

static inline void fl_add(word_t *bt) {
  debug("%d", *bt);
  if (free_list) {
    word_t *prev = fl_prev(free_list);
    fl_set_next(prev, bt);
    fl_set_next(bt, free_list);
    fl_set_prev(bt, prev);
    fl_set_prev(free_list, bt);
    free_list = bt;
  } else {
    fl_set_next(bt, bt);
    fl_set_prev(bt, bt);
    free_list = bt;
  }
}

static inline void fl_remove(word_t *bt) {
  // debug("%d", *bt);
  // if (!fl_search(bt)) {
  //   msg("no such block on the list :(\n");
  //   exit(EXIT_FAILURE);
  // }

  if (!free_list) {
  } else if (bt == fl_next(bt)) {
    msg("free list: remove last\n");
    free_list = NULL;
  } else {
    msg("free list remove - basic case\n");
    word_t *prev = fl_prev(bt);
    // word_t *prev = bt;
    word_t *next = fl_next(bt);
    // debug("%d, %d\n", *prev, *next);
    fl_set_prev(next, prev);
    fl_set_next(prev, next);
    if (free_list == bt)
      free_list = next;
  }
}

static inline void merge_blocks(word_t *a, word_t *b) {
  // fl_remove(b);
  size_t siz = bt_size(a) + bt_size(b);
  bt_flags flags = bt_getflags(a);
  word_t *footer = (void *)a + siz - sizeof(word_t);
  bt_make(a, siz, flags);
  bt_make(footer, siz, flags);
  if (b == last)
    last = a;
}

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

  // word_t *n = bt_next(p);
  // if (n)
  //   bt_set_prevfree(n);
}

/* --=[ miscellanous procedures ]=------------------------------------------ */

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  // return (size + ((sizeof(word_t)) << 1) + ALIGNMENT - 1) & -ALIGNMENT; //
  // header + footer
  size_t siz = (size + sizeof(word_t) + ALIGNMENT - 1) & -ALIGNMENT;
  // header only
  if (siz < (sizeof(word_t *) + sizeof(word_t)) * 2) {
    return (sizeof(word_t *) * 2 + sizeof(word_t) * 2 + ALIGNMENT - 1) &
           -ALIGNMENT;
  }
  // header footer prev_ptr next_ptr
  return siz;
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
  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

#if 1
/* First fit startegy. */
static word_t *find_fit(size_t reqsz) {
  if (!heap_start) {
    word_t *res = morecore(reqsz);
    last = res;
    heap_end = (void *)last + reqsz;
    heap_start = res;
    bt_make(res, reqsz, USED);
    return res;
  }

  if (free_list) {
    word_t *bt = free_list;
    do {
      // msg("loop\n");
      if (bt_size(bt) == reqsz) {
        msg("free block of exact size\n");
        fl_remove(bt);
        bt_flags flags = bt_get_prevfree(bt) | USED;
        bt_make(bt, reqsz, flags);
        return bt;
      } else if (bt_size(bt) > reqsz) {
        msg("alloc with split\n");
        if (bt_size(bt) - reqsz > (sizeof(word_t *) * 2 + sizeof(word_t) * 2)) {
          split_block(bt, reqsz);
          bt_flags flags = bt_get_prevfree(bt) | USED;
          bt_make(bt, reqsz, flags);
        } else {
          bt_flags flags = bt_get_prevfree(bt) | USED;
          bt_make(bt, bt_size(bt), flags);
        }
        fl_remove(bt);
        return bt;
      } else {
        bt = fl_next(bt);
      }
    } while (bt != free_list);
  }
  msg("alloc using morecore\n");
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
#else
/* Best fit startegy. */
static word_t *find_fit(size_t reqsz) {
  if (!heap_start) {
    word_t *res = morecore(reqsz);
    last = res;
    heap_end = (void *)last + reqsz;
    heap_start = res;
    return res;
  }

  word_t *bt = heap_start;
  word_t *res = NULL;
  int best = 0x7FFFFFFF;

  while (bt) {
    // msg("loop\n");
    if (bt_free(bt) && bt_size(bt) == reqsz) {
      msg("free block of exact size\n");
      return bt;
    } else if (bt_free(bt) && bt_size(bt) > reqsz) {
      int val = bt_size(bt) - reqsz;
      if (val < best) {
        // msg("new bestfit");
        best = val;
        res = bt;
      }
    }
    bt = bt_next(bt);
  }
  if (res) {
    msg("alloc with split\n");
    split_block(res, reqsz);
    return res;
  }

  msg("alloc using morecore\n");
  bt_flags pf = bt_free(last);
  // debug("last free? %d", pf);
  res = morecore(reqsz);
  last = res;
  heap_end = (void *)last + reqsz;
  if (pf)
    bt_set_prevfree(res);
  else
    bt_clr_prevfree(res);

  return res;
}
#endif

void *malloc(size_t size) {
  size_t reqsz = blksz(size);
  debug("size: %ld, required size: %ld", size, reqsz);
  word_t *fit = find_fit(reqsz);
  // msg(":)\n");

  word_t *next = bt_next(fit);
  if (next)
    bt_clr_prevfree(next);
  // word_t *foot = bt_footer(fit);
  // bt_make(foot, reqsz, flags);
  // mm_checkheap(VERBOSE);
  return bt_payload(fit);
}

/* --=[ free ]=------------------------------------------------------------- */

void free(void *ptr) {
  if (!ptr)
    return;

  word_t *bt = bt_fromptr(ptr);
  debug("free %ld", (long)bt - (long)heap_start);
  bt_make(bt, bt_size(bt), FREE | bt_get_prevfree(bt));
  word_t *footer = bt_footer(bt);
  bt_make(footer, bt_size(bt), FREE | bt_get_prevfree(bt));
  msg("freed\n");

  word_t *next = bt_next(bt);
  if (next && bt_free(next)) {
    msg("next free\n");
    fl_remove(next);
    merge_blocks(bt, next);
    msg("merged with next\n");
  }
  if (bt_get_prevfree(bt)) {
    word_t *prev = bt_prev(bt);
    msg("prev free\n");
    fl_remove(prev);
    merge_blocks(prev, bt);
    bt = prev;
    msg("merged with prev\n");
  }
  fl_add(bt);
  next = bt_next(bt);
  if (next) {
    msg("\tsetprevfree\n");
    bt_set_prevfree(next);
  }
  // mm_checkheap(VERBOSE);
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  word_t *bt = bt_fromptr(old_ptr);
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

void mm_checkheap(int verbose) {
  // Printy
  if (verbose) {
    int i = 0;
    for (word_t *b = heap_start; b; b = bt_next(b), i++) {
      debug("block number %d, size: %ld, used: %d, prevfree: %d", i, bt_size(b),
            bt_used(b), bt_get_prevfree(b));
    }

    i = 0;
    word_t *b = free_list;
    if (free_list) {
      do {
        debug("free block number %d, size: %ld, next bt %d, prev bt %d", i,
              bt_size(b), *fl_next(b), *fl_prev(b));
        b = fl_prev(b);
        i++;
      } while (b != free_list);
    }
  }

  // rozmiar bloku >= 32
  for (word_t *b = heap_start; b; b = bt_next(b)) {
    if (!heap_start)
      break;
    if (bt_size(b) < 32) {
      msg("block too small to fit pointers and boundary tags\n");
      exit(EXIT_FAILURE);
    }
  }

  // If prevfree is set then previous block is free
  // and if the block is free then prevfree is set in the next block
  for (word_t *b = heap_start; b; b = bt_next(b)) {
    word_t *n = bt_next(b);
    if (bt_free(b) && n && !bt_get_prevfree(n)) {
      debug("%d", *b);
      msg("block free, but prevfree not set in the next block\n");
      exit(EXIT_FAILURE);
    }
    if (bt_used(b) && n && bt_get_prevfree(n)) {
      msg("prevfree set, but previous block is used\n");
      exit(EXIT_FAILURE);
    }
  }

  // Każdy blok na liście wolnych bloków jest oznaczony jako wolny.
  word_t *b = free_list;
  if (free_list) {
    do {
      if (bt_used(b)) {
        msg("used block in free list\n");
        exit(EXIT_FAILURE);
      }
      b = fl_next(b);
    } while (b != free_list);
  }

  // Każdy blok oznaczony jako wolny jest na liście wszystkich wolnych bloków.
  for (word_t *b = heap_start; b; b = bt_next(b)) {
    if (bt_free(b) && !fl_search(b)) {
      msg("free block not in free list\n");
      exit(EXIT_FAILURE);
    }
  }

  // Nie istnieją dwa przyległe do siebie bloki, które są wolne.
  for (word_t *b = heap_start; b; b = bt_next(b)) {
    if (!heap_start)
      break;
    if (bt_free(b) && bt_get_prevfree(b)) {
      msg("two contiguous free blocks\n");
      exit(EXIT_FAILURE);
    }
  }

  // Wskaźnik na poprzedni i następny blok odnoszą się do adresów należących do
  // zarządzanej sterty.
  for (word_t *b = heap_start; b; b = bt_next(b)) {
    if (!heap_start)
      break;
    word_t *p = bt_prev(b);
    word_t *n = bt_next(b);
    if ((p && (void *)p < (void *)heap_start) ||
        (n && (void *)n > (void *)heap_end)) {
      // debug("prev %d, this %d, next %d", *p, *b, *n);
      msg("address not in heap\n");
      exit(EXIT_FAILURE);
    }
  }

  // Wskaźniki na liście wolnych bloków wskazują na początki wolnych bloków.

  // Ostatni blok faktycznie jest ostatni
  if (last && bt_next(last)) {
    msg("last does not point to the last block\n");
  }
}
