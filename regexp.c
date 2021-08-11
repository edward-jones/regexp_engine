#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define REX_ERR_PRINT(...) fprintf(stderr, __VA_ARGS__)
#ifndef NDEBUG
# define REX_DEBUG(exp) exp
# define REX_DEBUG_PRINT(...) fprintf(stderr, __VA_ARGS__)
#else
# define REX_DEBUG(exp)
# define REX_DEBUG_PRINT(...)
#endif

typedef enum {
  kEmptySet,
  kEpsilon,
  kLiteral,
  kUnion,
  kConcat,
  kKleene,
  kInvalid,
} ExpType;

enum {
  kEmptySetID = 256,
  kEpsilonID,
  kLastInternedExpID = kEpsilonID,
  kFirstNonInternedExpID,
};

typedef struct {
  unsigned short type    : 15;
  unsigned short gc_mark : 1;
  unsigned short n_subexp;
  uint_least16_t subexp[];
} Exp;

typedef struct {
  struct {
    Exp *base;
    size_t size;
    unsigned short next_offset;
  } heap;

  struct {
    size_t size;
    uint_least16_t root_id;
  } exp_tree;
} ExpContext;

static void dump_exp(ExpContext *ctx, unsigned exp_id, int indent);

static unsigned exp_id_to_offset(unsigned i) {
  assert(i >= kFirstNonInternedExpID);
  return i - kFirstNonInternedExpID;
}
static unsigned offset_to_exp_id(unsigned i) {
  return i + kFirstNonInternedExpID;
}

static int is_interned(unsigned i) { return i < kFirstNonInternedExpID; }
static int is_binary(ExpType type) { return type == kUnion || type == kConcat; }
static int is_unary(ExpType type) { return type == kKleene; }

static Exp *get_exp(ExpContext *ctx, unsigned i) {
  assert(!is_interned(i));
  return &ctx->heap.base[exp_id_to_offset(i)];
}

static ExpType get_exp_type(ExpContext *ctx, unsigned i) {
  if (is_interned(i)) {
    if (i < 256)
      return kLiteral;
    else if (i == kEmptySetID)
      return kEmptySet;
    else if (i == kEpsilonID)
      return kEpsilon;

    assert(0 && "Cannot get type of interned expression");
  }

  return get_exp(ctx, i)->type;
}

static unsigned next_exp_offset(unsigned offset, unsigned n_subexp) {
  unsigned size = sizeof(Exp) + n_subexp * sizeof(uint_least16_t);
  return offset + (size + sizeof(Exp) - 1) / sizeof(Exp);
}

static unsigned alloc_exp(ExpContext *ctx, ExpType type, unsigned n_subexp) {
  assert(is_unary(type) || is_binary(type));
  assert(!is_unary(type) || (n_subexp == 1));
  assert(n_subexp > 0);

  unsigned offset = ctx->heap.next_offset;
  unsigned next_offset = next_exp_offset(offset, n_subexp);
  assert(next_offset < ctx->heap.size);

  ctx->heap.next_offset = next_offset;
  unsigned exp_id = offset_to_exp_id(offset);
  Exp *exp = get_exp(ctx, exp_id);
  exp->type = type;
  exp->gc_mark = 0;
  exp->n_subexp = n_subexp;
  return exp_id;
}

static unsigned new_exp_n(ExpContext *ctx, ExpType type, unsigned n_subexp,
                          unsigned *subexp) {
  assert(subexp != NULL);
  unsigned exp_id = alloc_exp(ctx, type, n_subexp);
  Exp *exp = get_exp(ctx, exp_id);
  for (unsigned i = 0; i < n_subexp; i++)
    exp->subexp[i] = subexp[i];
  return exp_id;
}

static unsigned new_exp_1(ExpContext *ctx, ExpType type, unsigned subexp_id) {
  return new_exp_n(ctx, type, 1, &subexp_id);
}

static unsigned new_exp_2(ExpContext *ctx, ExpType type, unsigned exp0,
                          unsigned exp1) {
  unsigned subexp[2] = {exp0, exp1};
  return new_exp_n(ctx, type, 2, &subexp[0]);
}

static unsigned new_concat_from_string(ExpContext *ctx, const char *str,
                                       unsigned len) {
  unsigned exp_id = alloc_exp(ctx, kConcat, len);
  Exp *exp = get_exp(ctx, exp_id);
  for (unsigned i = 0; i < len; i++)
    exp->subexp[i] = (uint_least16_t)str[i];
  return exp_id;
}

static unsigned copy_exp(ExpContext *ctx, unsigned exp_id) {
  if (is_interned(exp_id))
    return exp_id;

  Exp *exp = get_exp(ctx, exp_id);

  unsigned res_id = alloc_exp(ctx, exp->type, exp->n_subexp);
  Exp *res = get_exp(ctx, res_id);
  for (unsigned i = 0; i < exp->n_subexp; i++)
    res->subexp[i] = copy_exp(ctx, exp->subexp[i]);
  return res_id;
}

static void dump_exp_id(ExpContext *ctx, unsigned exp_id) {
  switch (get_exp_type(ctx, exp_id)) {
  default:
    assert(0 && "Unknown expression type");
  case kEmptySet:
    REX_ERR_PRINT("{ }");
    break;
  case kEpsilon:
    REX_ERR_PRINT("<e>");
    break;
  case kLiteral:
    if (isprint(exp_id))
      REX_ERR_PRINT("'%c'", exp_id);
    else
      REX_ERR_PRINT("0x%x", exp_id);
    break;
  case kUnion:
    REX_ERR_PRINT("union");
    break;
  case kConcat:
    REX_ERR_PRINT("concat");
    break;
  case kKleene:
    REX_ERR_PRINT("kleene");
    break;
  }
}

static void dump_exp(ExpContext *ctx, unsigned exp_id, int indent) {
  for (int i = 0; i < indent; i++)
    REX_ERR_PRINT(". ");

  dump_exp_id(ctx, exp_id);
  REX_ERR_PRINT("\n");

  if (is_interned(exp_id))
    return;

  Exp *exp = get_exp(ctx, exp_id);
  for (unsigned i = 0; i < exp->n_subexp; i++)
    dump_exp(ctx, exp->subexp[i], indent + 1);
}

//===------------------------- Garbage Collection -------------------------===//

typedef struct {
  uint_least16_t start_id;
  uint_least16_t end_id;
  uint_least16_t adjust;
} ExpIDAdjustEntry;

typedef struct {
  size_t n_entries;
  size_t n_alloc;
  ExpIDAdjustEntry *data;
} ExpIDAdjustMap;

static void init_exp_id_adjust_map(ExpIDAdjustMap *map,
                                   ExpIDAdjustEntry *data,
                                   size_t n_entries) {
  map->n_entries = 0;
  map->n_alloc = n_entries;
  map->data = data;
}

static void clear_exp_id_adjust_map(ExpIDAdjustMap *map) {
  map->n_entries = 0;
}

static unsigned exp_id_adjust_map_find(ExpIDAdjustMap *map, unsigned exp_id) {
  if (map->n_entries == 0)
    return 0;

  unsigned low = 0;
  unsigned high = map->n_entries;

  while (low < high) {
    unsigned mid = (low + high) / 2;
    unsigned mid_id = map->data[mid].start_id;
    if (exp_id > mid_id)
      low = mid + 1;
    else if (exp_id < mid_id)
      high = mid - 1;
    else
      return mid;
  }
  return low;
}

static void exp_id_adjust_map_insert(ExpIDAdjustMap *map, unsigned start_id,
                                     unsigned end_id, unsigned adjust) {
  unsigned insert_pos = exp_id_adjust_map_find(map, start_id);
  if (insert_pos < map->n_entries)
    assert (map->data[insert_pos].start_id != start_id);

  // Allocate space in the exp_id map, then shuffle everything after the
  // insert position to make room
  map->n_entries++;
  assert (map->n_entries <= map->n_alloc);
  memmove(map->data + insert_pos + 1, map->data + insert_pos,
          (map->n_entries - insert_pos) * sizeof(*map->data));

  ExpIDAdjustEntry *entry = &map->data[insert_pos];
  entry->start_id = start_id;
  entry->end_id = end_id;
  entry->adjust = adjust;
}

static void gc_mark(ExpContext *ctx, unsigned exp_id, int mark) {
  if (is_interned(exp_id))
    return;

  Exp *exp = get_exp(ctx, exp_id);
  exp->gc_mark = mark;
  for (unsigned i = 0; i < exp->n_subexp; i++)
    gc_mark(ctx, exp->subexp[i], mark);
}

static unsigned gc_compute_exp_id_adjustments(ExpContext *ctx,
                                              ExpIDAdjustMap *map,
                                              unsigned *offset,
                                              unsigned *adjust) {
  int done = 1;
  clear_exp_id_adjust_map(map);

  // Add mappings until we run out of space or we're reached the end of the heap
  while (map->n_entries < map->n_alloc
         && *offset < ctx->heap.next_offset) {

    // Iterate until we find an expression with the gc mark set, this is
    // the first id in the range to be adjusted
    int gc_mark = 0;
    unsigned next_offset = 0;
    while (!gc_mark && *offset < ctx->heap.next_offset) {
      Exp *exp = get_exp(ctx, offset_to_exp_id(*offset));
      next_offset = next_exp_offset(*offset, exp->n_subexp);
      if (!exp->gc_mark) {
        *adjust += next_offset - *offset;
        *offset = next_offset;
      } else
        gc_mark = 1;
    }
    if (!gc_mark)
      continue;
    assert (next_offset >= *offset);
    unsigned start_id = offset_to_exp_id(*offset);

    // Now keep iterating until the next expression doesn't have the gc mark
    // set. This will be the end of the range.
    *offset = next_offset;
    unsigned end_id = offset_to_exp_id(*offset);

    while (gc_mark && *offset < ctx->heap.next_offset) {
      unsigned exp_id = offset_to_exp_id(*offset);
      Exp *exp = get_exp(ctx, exp_id);
      if (!exp->gc_mark) {
        gc_mark = 0;
        break;
      }
      *offset = next_exp_offset(*offset, exp->n_subexp);
      end_id = offset_to_exp_id(*offset);
    }

    REX_DEBUG_PRINT("  [Start: %d, End: %d, Adjust: %d]\n",
                    start_id, end_id, -*adjust);

    // Add the entry to the map
    done = 0;
    exp_id_adjust_map_insert(map, start_id, end_id, *adjust);
  }

#ifndef NDEBUG
  for (size_t i = 0; i < map->n_entries; i++)
    REX_ERR_PRINT("  [%d, %d, %d]\n", map->data[i].start_id,
                  map->data[i].end_id, map->data[i].adjust);
  if (done)
    REX_ERR_PRINT("... No adjustments to make\n");
#endif

  return !done;
}

static unsigned gc_rewrite_exp_ids(ExpContext *ctx, ExpIDAdjustMap *map,
                                   unsigned exp_id) {
  if (is_interned(exp_id))
    return exp_id;

  // Recursively rewrite subexpressions
  Exp *exp = get_exp(ctx, exp_id);
  for (unsigned i = 0; i < exp->n_subexp; i++)
    exp->subexp[i] = gc_rewrite_exp_ids(ctx, map, exp->subexp[i]);

  // Get the entry in the adjustment map which covers this expression id
  //
  // The map is sorted by the start of the range covered by the entry. If
  // the find operation doesn't return an exact match then the adjustment
  // to be applied for a given expression id will actually be found in the
  // *previous* entry in the map.
  //
  // Below we determine the appropriate entry, with particular care around
  // the boundary conditions.
  unsigned index = exp_id_adjust_map_find(map, exp_id);

  ExpIDAdjustEntry *entry;
  if (index >= map->n_entries)
    entry = map->data + index - 1;
  else {
    entry = map->data + index;
    if (entry->start_id != exp_id && index > 0)
      entry = map->data + index - 1;
  }
  if (entry->start_id > exp_id || exp_id >= entry->end_id)
    return exp_id;

  REX_DEBUG_PRINT("  %d -> %d\n", exp_id, exp_id - entry->adjust);
  return exp_id - entry->adjust;
}

static void gc_compact(ExpContext *ctx, ExpIDAdjustMap *map) {
  for (unsigned i = 0; i < map->n_entries; i++) {
    ExpIDAdjustEntry *entry = &map->data[i];
    Exp *start = &ctx->heap.base[exp_id_to_offset(entry->start_id)];
    Exp *end   = &ctx->heap.base[exp_id_to_offset(entry->end_id)];
    Exp *dst   = start - entry->adjust;
    size_t size = (end - start) * sizeof(Exp);
    memmove(dst, start, size);

    REX_DEBUG_PRINT("   (Copy) %zu bytes from expression id %d to %d\n",
                    size, entry->start_id, entry->start_id - entry->adjust);
#ifndef NDEBUG
    unsigned clear_start_id = entry->end_id - entry->adjust;
    size_t clear_size = entry->adjust * sizeof(Exp);
    REX_DEBUG_PRINT("  (Clear) %zu bytes from expression id %d to %d\n",
                    clear_size, clear_start_id, entry->end_id);
    for (unsigned i = 0; i < clear_size; i++) {
      unsigned offset = exp_id_to_offset(clear_start_id + i);
      Exp *exp = &ctx->heap.base[offset];
      exp->type = kInvalid;
      exp->n_subexp = 0;
    }
#endif
  }
}

static unsigned gc_calculate_next_offset(ExpContext *ctx, unsigned exp_id) {
                                         
  if (is_interned(exp_id))
    return 0;

  Exp *exp = get_exp(ctx, exp_id);
  unsigned max_offset = next_exp_offset(exp_id_to_offset(exp_id),
                                        exp->n_subexp);

  for (unsigned i = 0; i < exp->n_subexp; i++) {
    unsigned tmp = gc_calculate_next_offset(ctx, exp->subexp[i]);
    if (tmp > max_offset)
      max_offset = tmp;
  }
  return max_offset;
}

static void dump_heap(ExpContext *ctx) {
  unsigned offset = 0;
  while (offset < ctx->heap.next_offset) {
    unsigned exp_id = offset_to_exp_id(offset);
    Exp *exp = get_exp(ctx, exp_id);

    fprintf (stderr, exp->gc_mark ? "      " : "<dead>");
    fprintf (stderr, " (%d) ", exp_id);

    fprintf (stderr, " [");
    dump_exp_id(ctx, exp_id);
    for (unsigned i = 0; i < exp->n_subexp; i++) {
      fprintf (stderr, " ");
      if (is_interned(exp->subexp[i]))
        dump_exp_id(ctx, exp->subexp[i]);
      else
        REX_ERR_PRINT("%d", exp->subexp[i]);
    }
    REX_ERR_PRINT("]\n");
    offset = next_exp_offset (offset, exp->n_subexp);
  }
}

static void garbage_collect(ExpContext *ctx) {
  REX_DEBUG_PRINT("##== Garbage collect ==##\n\n");

  // Mark expressions reachable from the root
  gc_mark(ctx, ctx->exp_tree.root_id, /*mark=*/1);

  REX_DEBUG(dump_heap(ctx));

  // Iteratively compact the heap. This could be done in a single pass but
  // then the size of the ExpID adjustment map could only be determined at
  // runtime.
  ExpIDAdjustEntry exp_id_adjust_entry[32];
  ExpIDAdjustMap   exp_id_adjust_map;
  init_exp_id_adjust_map(&exp_id_adjust_map, exp_id_adjust_entry, 32);

  unsigned offset = 0;
  unsigned adjust = 0;
  unsigned iterations = 0;
  while (1) {
    // Compute a set of adjustments to the heap
    REX_DEBUG_PRINT("\n~> Computing expression id adjustments\n");
    int res = gc_compute_exp_id_adjustments(ctx, &exp_id_adjust_map, &offset,
                                            &adjust);
    if (!res)
      break;

    iterations++;

    // Offset adjustments have been computed, walk through the expression
    // tree from the root and rewrite expressions
    REX_DEBUG_PRINT("\n~> Rewriting expression ids\n");
    ctx->exp_tree.root_id = gc_rewrite_exp_ids(ctx, &exp_id_adjust_map,
                                               ctx->exp_tree.root_id);

    // Finally we can compact the expression tree based on the offset
    // adjustments
    REX_DEBUG_PRINT("\n~> Compacting heap\n");
    gc_compact(ctx, &exp_id_adjust_map);
  }
  if (iterations == 0) {
    REX_DEBUG_PRINT("\n");
    return;
  }

  // If the heap was compacted, then compute the new top of the heap
  ctx->heap.next_offset = gc_calculate_next_offset(ctx, ctx->exp_tree.root_id);

  REX_DEBUG_PRINT("\n~> Final heap\n\n");
  REX_DEBUG(dump_heap(ctx));
  REX_DEBUG_PRINT("\n");

  // Clear the gc mark now we're done
  gc_mark(ctx, ctx->exp_tree.root_id, /*mark=*/0);
}

static int compare(ExpContext *ctx, unsigned lhs_id, unsigned rhs_id) {
  // First try and sort by type
  ExpType lhs_type = get_exp_type(ctx, lhs_id);
  ExpType rhs_type = get_exp_type(ctx, rhs_id);
  if (lhs_type != rhs_type) {
    if (lhs_type < rhs_type)
      return -1;
    else
      return 1;
  }

  // If both are literals then compare by the id, which is equal to the
  // literal value
  if (lhs_type == kLiteral) {
    if (lhs_id < rhs_id)
      return -1;
    else if (lhs_id > rhs_id)
      return 1;
    else
      return 0;
  }

  // For unary or binary expressions, compare first by the number of
  // subexpressions and then by each subexpression in turn.
  if (is_unary(lhs_type) || is_binary(rhs_type)) {
    Exp *lhs = get_exp(ctx, lhs_id);
    Exp *rhs = get_exp(ctx, rhs_id);

    if (lhs->n_subexp != rhs->n_subexp) {
      if (lhs->n_subexp < rhs->n_subexp)
        return -1;
      else
        return 1;
    }

    for (unsigned i = 0; i < lhs->n_subexp; i++) {
      int res = compare(ctx, lhs->subexp[i], rhs->subexp[i]);
      if (res != 0)
        return res;
    }
  }

  return 0;
}

static void merge_sort_exp(ExpContext *ctx, uint_least16_t *exp_list,
                           unsigned n_subexp, unsigned depth) {
  if (n_subexp == 1)
    return;

  unsigned lhs_n_subexp = n_subexp / 2;
  unsigned rhs_n_subexp = n_subexp - lhs_n_subexp;

  uint_least16_t *lhs = exp_list;
  uint_least16_t *rhs = exp_list + lhs_n_subexp;

  merge_sort_exp(ctx, lhs, lhs_n_subexp, depth + 2);
  merge_sort_exp(ctx, rhs, rhs_n_subexp, depth + 2);

  // Do a merge of the two sorted sublists *in place*
  uint_least16_t *next_lhs = exp_list;
  uint_least16_t *next_rhs = rhs;
  uint_least16_t *exp_list_end = exp_list + n_subexp;

  while (next_lhs < exp_list_end
         && next_rhs < exp_list_end
         && next_lhs < next_rhs) {
    int res = compare (ctx, *next_lhs, *next_rhs);

    // Already sorted, just increase the left pointer
    if (res < 0) {
      next_lhs++;
      continue;
    }

    // Make space for the right element and then copy it back to the left
    unsigned insert_id = *next_rhs;
    size_t size = (next_rhs - next_lhs) * sizeof(*next_lhs);
    if (size != 0)
      memmove(next_lhs + 1, next_lhs, size);

    *next_lhs = insert_id;
    next_lhs++;
    next_rhs++;
  }
}

static int is_nullable(ExpContext *ctx, unsigned exp_id) {
  switch (get_exp_type(ctx, exp_id)) {
  default:
    assert(0 && "Unhandled expression type");
  case kEmptySet:
    return 0;
  case kEpsilon:
    return 1;
  case kLiteral:
    return 0;
  case kUnion: {
    Exp *exp = get_exp(ctx, exp_id);
    for (unsigned i = 0; i < exp->n_subexp; i++) {
      if (is_nullable(ctx, exp->subexp[i]))
        return 1;
    }
    return 0;
  }
  case kConcat: {
    Exp *exp = get_exp(ctx, exp_id);
    for (unsigned i = 0; i < exp->n_subexp; i++) {
      if (!is_nullable(ctx, exp->subexp[i]))
        return 0;
    }
    return 1;
  }
  case kKleene:
    return 0;
  }
}

static unsigned derive_exp(ExpContext *ctx, unsigned exp_id, unsigned char c) {
  switch (get_exp_type(ctx, exp_id)) {
  default:
    assert(0 && "Unhandled expression type!");

  case kEmptySet:
  case kEpsilon:
    return kEmptySetID;

  case kLiteral:
    if (exp_id == c)
      return kEpsilonID;
    else
      return kEmptySetID;

  case kUnion: {
    Exp *exp = get_exp(ctx, exp_id);
    unsigned res_id = alloc_exp(ctx, kUnion, exp->n_subexp);
    Exp *res = get_exp(ctx, res_id);
    for (unsigned i = 0; i < exp->n_subexp; i++)
      res->subexp[i] = derive_exp(ctx, exp->subexp[i], c);
    return res_id;
  }

  case kConcat: {
    Exp *exp = get_exp(ctx, exp_id);

    unsigned res_n_subexp = 1;
    while (is_nullable(ctx, exp->subexp[res_n_subexp - 1]))
      res_n_subexp++;

    unsigned res_id = alloc_exp(ctx, kUnion, res_n_subexp);
    Exp *res = get_exp(ctx, res_id);
    for (unsigned subexp_offset = 0; subexp_offset < res->n_subexp;
         subexp_offset++) {
      unsigned concat_n_subexp = exp->n_subexp - subexp_offset;
      unsigned concat_id = alloc_exp(ctx, kConcat, concat_n_subexp);

      Exp *concat = get_exp(ctx, concat_id);
      concat->subexp[0] = derive_exp(ctx, exp->subexp[subexp_offset], c);
      for (unsigned i = 1; i < concat_n_subexp; i++)
        concat->subexp[i] = copy_exp(ctx, exp->subexp[subexp_offset + i]);

      res->subexp[subexp_offset] = concat_id;
    }
    return res_id;
  }
  case kKleene: {
    Exp *exp = get_exp(ctx, exp_id);
    assert(exp->n_subexp == 1);
    return new_exp_2(ctx, kConcat, derive_exp(ctx, exp->subexp[0], c),
                     new_exp_1(ctx, kKleene, copy_exp(ctx, exp->subexp[0])));
  }
  }
}

static void derive(ExpContext *ctx, unsigned char c) {
  REX_DEBUG_PRINT("##== Deriving ==##\n\n");

#ifndef NDEBUG
  REX_ERR_PRINT("~> Input character: ");
  if (isprint(c))
    REX_ERR_PRINT("'%c'\n", c);
  else
    REX_ERR_PRINT("0x%x\n", c);

  REX_ERR_PRINT("~> Initial expression tree:\n\n");
  dump_exp(ctx, ctx->exp_tree.root_id, 0);
#endif

  ctx->exp_tree.root_id = derive_exp(ctx, ctx->exp_tree.root_id, c);

#ifndef NDEBUG
  REX_ERR_PRINT("\n~> Derived expression tree:\n\n");
  dump_exp(ctx, ctx->exp_tree.root_id, 0);
  REX_ERR_PRINT("\n");
#endif
}

static unsigned simplify_exp(ExpContext *ctx, unsigned exp_id) {
  // Interned expressions need no simplification
  if (is_interned(exp_id))
    return exp_id;

  Exp *exp = get_exp(ctx, exp_id);
  assert (exp->n_subexp > 0);

  // Simplify all of the subexpressions in turn
  {
    unsigned res_id = alloc_exp(ctx, exp->type, exp->n_subexp);
    Exp *res = get_exp(ctx, res_id);
    for (unsigned i = 0; i < exp->n_subexp; i++)
      res->subexp[i] = simplify_exp(ctx, exp->subexp[i]);
    exp = res;
    exp_id = res_id;
  }

  // Now perform simplifications on the expression

  // If any of the subexpressions are of the same type as the expression, then
  // create a new expression with the subexpressions flattened into it
  // First count the total number of subexpressions
  unsigned n_subexp = exp->n_subexp;
  for (unsigned i = 0; i < exp->n_subexp; i++) {
    if (get_exp_type(ctx, exp->subexp[i]) == exp->type) {
      Exp *subexp = get_exp(ctx, exp->subexp[i]);
      n_subexp += subexp->n_subexp - 1;
    }
  }
  if (n_subexp != exp->n_subexp) {
    // Flatten the subexpressions into a new result expressions
    unsigned res_id = alloc_exp(ctx, exp->type, n_subexp);
    Exp *res = get_exp(ctx, res_id);
    for (unsigned i = 0, out_index = 0; i < exp->n_subexp; i++) {
      if (get_exp_type(ctx, exp->subexp[i]) == exp->type) {
        Exp *subexp = get_exp(ctx, exp->subexp[i]);
        for (unsigned j = 0; j < subexp->n_subexp; j++)
          res->subexp[out_index++] = subexp->subexp[j];
      } else
        res->subexp[out_index++] = exp->subexp[i];
    }
    exp = res;
    exp_id = res_id;
  }

  // Union simplification
  if (exp->type == kUnion) {
    if (exp->n_subexp == 1)
      return exp->subexp[0];

    // First sort the union subexpressions in place
    if (exp->n_subexp >= 2)
      merge_sort_exp(ctx, &exp->subexp[0], exp->n_subexp, 2);

    // Try and simplify by removing duplicates and empty set expressions.
    // First just count how many subexpressions we'll end up with
    unsigned n_subexp = 0;
    for (unsigned i = 0; i < exp->n_subexp; i++) {
      if (exp->subexp[i] == kEmptySetID)
        continue;
      if (i > 0 && !compare(ctx, exp->subexp[i-1], exp->subexp[i]))
        continue;

      n_subexp++;
    }
    if (n_subexp != exp->n_subexp) {
      if (n_subexp == 0)
        return kEmptySetID;

      // Allocate a new expressions with empty set and duplicate expressions
      // removed
      unsigned res_id = alloc_exp(ctx, exp->type, n_subexp);
      Exp *res = get_exp(ctx, res_id);
      for (unsigned i = 0, out_index = 0; i < exp->n_subexp; i++) {
        if (exp->subexp[i] == kEmptySetID)
          continue;
        if (i > 0 && !compare(ctx, exp->subexp[i-1], exp->subexp[i]))
          continue;

        res->subexp[out_index++] = exp->subexp[i];
      }
      exp = res;
      exp_id = res_id;
    }

    assert (exp->n_subexp > 0);
    if (exp->n_subexp == 1)
      return exp->subexp[0];
    else
      return exp_id;
  }

  // Concat simplification
  if (exp->type == kConcat) {
    if (n_subexp == 1)
      return exp->subexp[0];

    // Count the number of subexpressions before we encounter an empty set
    unsigned n_subexp = 0;
    while (exp->subexp[n_subexp] != kEmptySetID && n_subexp < exp->n_subexp)
      n_subexp++;

    if (n_subexp != exp->n_subexp) {
      if (n_subexp == 0)
        return kEmptySetID;

      // if it wasn't the last subexpression which was the empty set, then
      // allocate a new expression which stops after the empty set
      if (n_subexp != exp->n_subexp - 1) {
        n_subexp += 1;
        unsigned res_id = alloc_exp(ctx, exp->type, n_subexp);
        Exp *res = get_exp(ctx, res_id);
        for (unsigned i = 0; i < n_subexp; i++)
          res->subexp[i] = exp->subexp[i];
        exp = res;
        exp_id = res_id;
      }
    }
    return exp_id;
  }

  return exp_id;
}

static void simplify(ExpContext *ctx) {
  REX_DEBUG_PRINT("##== Simplifying ==##\n\n");
#ifndef NDEBUG
  REX_ERR_PRINT("~> Original expression tree:\n\n");
  dump_exp(ctx, ctx->exp_tree.root_id, 0);
#endif

  ctx->exp_tree.root_id = simplify_exp(ctx, ctx->exp_tree.root_id);

#ifndef NDEBUG
  REX_ERR_PRINT("\n~> Simplified expression tree:\n\n");
  dump_exp(ctx, ctx->exp_tree.root_id, 0);
  REX_ERR_PRINT("\n");
#endif
}

int match_regexp(ExpContext *ctx, const char *str, size_t strlen) {
  for (size_t i = 0; i < strlen; i++) {
#ifndef NDEBUG
    dump_exp(ctx, ctx->exp_tree.root_id, 0);
    REX_ERR_PRINT("\n");

    REX_ERR_PRINT("%s\n", str);
    for (size_t j = 0; j < i; j++)
      REX_ERR_PRINT(" ");
    REX_ERR_PRINT("^\n\n");
#endif

    // Derive against the next character
    derive(ctx, str[i]);
    garbage_collect(ctx);

    // Simplify the expression tree
    simplify(ctx);
    garbage_collect(ctx);

    // If we've collapsed to the empty set then there's no way we can match
    if (ctx->exp_tree.root_id == kEmptySetID) {
      REX_DEBUG_PRINT("~> Expression collapsed to the empty set, no match\n");
      return 0;
    }

    if (is_nullable(ctx, ctx->exp_tree.root_id)) {
      REX_DEBUG_PRINT("~> Expression is nullable, found match!\n");
      return 1;
    }
  }
  REX_DEBUG_PRINT("~> Reached end of string with no match\n");
  return 0;
}

int main(void) {
  static Exp exp_heap[8192];

  ExpContext ctx;

  ctx.heap.base = exp_heap;
  ctx.heap.size = 8192;
  ctx.heap.next_offset = 0;

#if 0
  ExpIDAdjustMap map;
  ExpIDAdjustEntry data[32];
  init_exp_id_adjust_map(&map, &data[0], 32);

  exp_id_adjust_map_insert(&map, 255, 0, 0);
  exp_id_adjust_map_insert(&map, 254, 0, 0);
  exp_id_adjust_map_insert(&map, 253, 0, 0);
  exp_id_adjust_map_insert(&map, 252, 0, 0);
  exp_id_adjust_map_insert(&map, 251, 0, 0);
  exp_id_adjust_map_insert(&map, 250, 0, 0);
  return 0;
#endif

#if 0
  unsigned concat_id = alloc_exp(&ctx, kConcat, 6);
  Exp *c = get_exp(&ctx, concat_id);
  c->subexp[0] = 'a';
  c->subexp[1] = 'b';
  c->subexp[2] = 'c';
  c->subexp[3] = 'd';
  c->subexp[4] = 'e';
  c->subexp[5] = '5';

  alloc_exp(&ctx, kUnion, 3);
  alloc_exp(&ctx, kUnion, 3);

  unsigned union_id = alloc_exp(&ctx, kUnion, 5);
  Exp *u = get_exp(&ctx, union_id);

  u->subexp[0] = copy_exp(&ctx, concat_id);

  alloc_exp(&ctx, kKleene, 1);
  alloc_exp(&ctx, kUnion, 1);

  u->subexp[1] = copy_exp(&ctx, concat_id);
  u->subexp[2] = copy_exp(&ctx, concat_id);

  copy_exp(&ctx, concat_id);

  u->subexp[3] = copy_exp(&ctx, concat_id);
  u->subexp[4] = copy_exp(&ctx, concat_id);
  
  alloc_exp(&ctx, kUnion, 1);

  ctx.exp_tree.root_id = union_id;

  garbage_collect(&ctx);
#endif
  

#if 1

  ctx.exp_tree.root_id =
      new_exp_2(&ctx, kUnion,
                new_concat_from_string(&ctx, "hello", 5),
                new_concat_from_string(&ctx, "world", 5));

  dump_exp(&ctx, ctx.exp_tree.root_id, 0);

  match_regexp(&ctx, "world", 5);
#endif

  return 0;
}
