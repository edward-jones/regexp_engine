#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef enum {
  kEmptySet,
  kEpsilon,
  kLiteral,
  kUnion,
  kConcat,
  kKleene,
} ExpType;

enum {
  kEmptySetID = 256,
  kEpsilonID,
  kLastInternedExpID = kEpsilonID,
  kFirstNonInternedExpID,
};

typedef struct {
  ExpType type;
  uint_least16_t n_subexp;
  uint_least16_t subexp[];
} Exp;

typedef struct {
  struct {
    Exp *base;
    size_t size;
    uint_least16_t next_offset;
  } buffer;

  struct {
    uint_least16_t base_offset;
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
  return &ctx->buffer.base[exp_id_to_offset(i)];
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

  unsigned offset = ctx->buffer.next_offset;
  unsigned next_offset = next_exp_offset(offset, n_subexp);
  assert(next_offset < ctx->buffer.size);

  ctx->buffer.next_offset = next_offset;
  unsigned exp_id = offset_to_exp_id(offset);
  Exp *exp = get_exp(ctx, exp_id);
  exp->type = type;
  exp->n_subexp = n_subexp;
  return exp_id;
}

static unsigned new_exp_n(ExpContext *ctx, ExpType type, unsigned n_subexp,
                          unsigned *subexp) {
  assert(subexp != NULL);
  unsigned res_id = alloc_exp(ctx, type, n_subexp);
  Exp *exp = get_exp(ctx, res_id);
  for (unsigned i = 0; i < n_subexp; i++)
    exp->subexp[i] = subexp[i];
  return res_id;
}

static unsigned new_exp_1(ExpContext *ctx, ExpType type, unsigned subexp_id) {
  return new_exp_n(ctx, type, 1, &subexp_id);
}

static unsigned new_exp_2(ExpContext *ctx, ExpType type, unsigned exp0,
                          unsigned exp1) {
  unsigned subexp[2] = {exp0, exp1};
  return new_exp_n(ctx, type, 1, &subexp[0]);
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

// Garbage collect dead expressions and compact the reachable expressions
// at the start of the buffer.
static void garbage_collect(ExpContext *ctx) {
  // Move the expression tree back to the start of the buffer
  memmove(ctx->buffer.base, &ctx->buffer.base[ctx->exp_tree.base_offset],
          ctx->exp_tree.size * sizeof(Exp));

  // Walk through all of the expressions in the tree and fixup any indices
  unsigned adjust = ctx->exp_tree.base_offset;
  for (size_t offset = 0; offset < ctx->exp_tree.size;) {
    unsigned exp_id = offset_to_exp_id(offset);
    Exp *exp = get_exp(ctx, exp_id);

    for (unsigned j = 0; j < exp->n_subexp; j++) {
      // Don't update any subexpressions which are interned
      if (!is_interned(exp->subexp[j]))
        exp->subexp[j] -= adjust;
    }
    offset = next_exp_offset(offset, exp->n_subexp);
  }

  // Also fixup indices in the context
  ctx->exp_tree.base_offset -= adjust;
  if (!is_interned(ctx->exp_tree.root_id))
    ctx->exp_tree.root_id -= adjust;
  ctx->buffer.next_offset -= adjust;
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

static void sort_exp(ExpContext *ctx, unsigned exp_id) {
  if (is_interned(exp_id))
    return;

  // Recursively sort subexpressions
  Exp *exp = get_exp(ctx, exp_id);
  for (unsigned i = 0; i < exp->n_subexp; i++)
    sort_exp(ctx, exp->subexp[i]);

  // Merge sort any union expression with more than two subexpressions
  if (exp->type != kUnion || exp->n_subexp < 2)
    return;
  merge_sort_exp(ctx, &exp->subexp[0], exp->n_subexp, 2);
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
  unsigned new_base_offset = ctx->buffer.next_offset;
  unsigned new_root_id = derive_exp(ctx, ctx->exp_tree.root_id, c);
  unsigned new_size = ctx->buffer.next_offset - new_base_offset;

  ctx->exp_tree.base_offset = new_base_offset;
  ctx->exp_tree.root_id = new_root_id;
  ctx->exp_tree.size = new_size;
}

static unsigned flatten_exp(ExpContext *ctx, ExpType type, unsigned exp_id,
                            uint_least16_t *res_id) {
  if (is_interned(exp_id)) {
    if (res_id)
      *res_id = exp_id;
    return 1;
  }

  Exp *exp = get_exp(ctx, exp_id);
  assert(exp->n_subexp > 0);

  if (exp->type == type) {
    unsigned n_res_added = 0;
    for (unsigned i = 0; i < exp->n_subexp; i++) {
      unsigned n = flatten_exp(ctx, type, exp->subexp[i], res_id);
      if (res_id)
        res_id += n;
      n_res_added += n;
    }
    return n_res_added;
  }

  assert(exp->type != type);
  if (res_id) {
    unsigned res_n_subexp = flatten_exp(ctx, exp->type, exp_id, NULL);
    *res_id = alloc_exp(ctx, exp->type, res_n_subexp);
    Exp *res = get_exp(ctx, *res_id);
    flatten_exp(ctx, exp->type, exp_id, &res->subexp[0]);
  }
  return 1;
}

static void flatten(ExpContext *ctx) {
  uint_least16_t new_root_id;
  unsigned new_base_offset = ctx->buffer.next_offset;
  flatten_exp(ctx, kEmptySet, ctx->exp_tree.root_id, &new_root_id);
  unsigned new_size = ctx->buffer.next_offset - new_base_offset;

  ctx->exp_tree.base_offset = new_base_offset;
  ctx->exp_tree.root_id = new_root_id;
  ctx->exp_tree.size = new_size;
}

static unsigned simplify_exp(ExpContext *ctx, unsigned exp_id, int *modified) {
  assert(modified);
  if (is_interned(exp_id))
    return exp_id;

  Exp *exp = get_exp(ctx, exp_id);

  if (is_binary(exp->type) && exp->n_subexp == 1) {
    *modified = 1;
    return simplify_exp(ctx, exp->subexp[0], modified);
  }

  if (exp->type == kUnion) {
    unsigned n_non_empty_set = 0;
    unsigned non_empty_set_subexp_id = 0;
    for (unsigned i = 0; i < exp->n_subexp; i++)
      if (exp->subexp[i] != kEmptySetID) {
        non_empty_set_subexp_id = exp->subexp[i];
        n_non_empty_set++;
      }

    if (n_non_empty_set == 0) {
      *modified = 1;
      return kEmptySetID;
    }

    if (n_non_empty_set == 1) {
      *modified = 1;
      return simplify_exp(ctx, non_empty_set_subexp_id, modified);
    }

    if (n_non_empty_set != exp->n_subexp) {
      unsigned res_id = alloc_exp(ctx, kUnion, n_non_empty_set);
      Exp *res = get_exp(ctx, res_id);
      for (unsigned i = 0, j = 0; i < exp->n_subexp; i++)
        if (exp->subexp[i] != kEmptySetID)
          res->subexp[j++] = simplify_exp(ctx, exp->subexp[i], modified);

      *modified = 1;
      return res_id;
    }
  }

  if (exp->type == kConcat) {
    unsigned n_non_empty_set = 0;
    while (exp->subexp[n_non_empty_set] != kEmptySetID &&
           n_non_empty_set < exp->n_subexp)
      n_non_empty_set++;

    if (n_non_empty_set == 0) {
      *modified = 1;
      return kEmptySetID;
    }

    if (n_non_empty_set == 1) {
      *modified = 1;
      return simplify_exp(ctx, exp->subexp[0], modified);
    }

    if (n_non_empty_set != exp->n_subexp) {
      unsigned res_id = alloc_exp(ctx, kConcat, n_non_empty_set);
      Exp *res = get_exp(ctx, res_id);
      for (unsigned i = 0; i < res->n_subexp; i++)
        res->subexp[i] = simplify_exp(ctx, exp->subexp[i], modified);

      *modified = 1;
      return res_id;
    }
  }

  unsigned res_id = alloc_exp(ctx, exp->type, exp->n_subexp);
  Exp *res = get_exp(ctx, res_id);
  for (unsigned i = 0; i < exp->n_subexp; i++)
    res->subexp[i] = simplify_exp(ctx, exp->subexp[i], modified);

  return res_id;
}

static int simplify(ExpContext *ctx) {
  int modified = 0;

  unsigned new_base_offset = ctx->buffer.next_offset;
  unsigned new_root_id = simplify_exp(ctx, ctx->exp_tree.root_id, &modified);
  unsigned new_size = ctx->buffer.next_offset - new_base_offset;

  ctx->exp_tree.base_offset = new_base_offset;
  ctx->exp_tree.root_id = new_root_id;
  ctx->exp_tree.size = new_size;

  return modified;
}

static void dump_exp(ExpContext *ctx, unsigned exp_id, int indent) {
  for (int i = 0; i < indent; i++)
    fprintf(stderr, ". ");

  switch (get_exp_type(ctx, exp_id)) {
  default:
    assert(0 && "Unknown expression type");
  case kEmptySet:
    fprintf(stderr, "{ }\n");
    break;
  case kEpsilon:
    fprintf(stderr, "<e>\n");
    break;
  case kLiteral:
    if (isprint(exp_id))
      fprintf(stderr, "'%c'\n", exp_id);
    else
      fprintf(stderr, "0x%x\n", exp_id);
    break;
  case kUnion: {
    Exp *exp = get_exp(ctx, exp_id);
    fprintf(stderr, "union\n");
    for (unsigned j = 0; j < exp->n_subexp; j++)
      dump_exp(ctx, exp->subexp[j], indent + 1);
    break;
  }
  case kConcat: {
    Exp *exp = get_exp(ctx, exp_id);
    fprintf(stderr, "concat\n");
    for (unsigned j = 0; j < exp->n_subexp; j++)
      dump_exp(ctx, exp->subexp[j], indent + 1);
    break;
  }
  case kKleene: {
    Exp *exp = get_exp(ctx, exp_id);
    fprintf(stderr, "kleene\n");
    dump_exp(ctx, exp->subexp[0], indent + 1);
    break;
  }
  }
}

int match_regexp(ExpContext *ctx, const char *str, size_t strlen) {
  for (size_t i = 0; i < strlen; i++) {
#ifndef NDEBUG
    dump_exp(ctx, ctx->exp_tree.root_id, 0);
    fputc('\n', stderr);

    fprintf(stderr, "%s\n", str);
    for (size_t j = 0; j < i; j++)
      fputc(' ', stderr);
    fprintf(stderr, "^\n\n");
#endif

    // Derive against the next character
    derive(ctx, str[i]);
    garbage_collect(ctx);

    // Flatten the resultant expression tree
    flatten(ctx);
    garbage_collect(ctx);

    int modified = 1;
    while (modified) {
      modified = simplify(ctx);
      garbage_collect(ctx);
    }

    if (is_nullable(ctx, ctx->exp_tree.root_id)) {
#ifndef NDEBUG
      fprintf(stderr, "Found match!\n");
#endif
      return 1;
    }
  }

#ifndef NDEBUG
  fprintf(stderr, "No match!\n");
#endif
  return 0;
}

int main(void) {
  static Exp exp_buffer[8192];

  ExpContext ctx;

  ctx.buffer.base = exp_buffer;
  ctx.buffer.size = 8192;
  ctx.buffer.next_offset = 0;

#if 0
  ctx.exp_tree.root_id =
    new_kleene_star(&ctx,
      new_kleene_star(&ctx,
        new_kleene_star(&ctx,
          new_concat(&ctx,
            'a',
            new_concat(&ctx,
              'b',
              new_concat(&ctx,
                'c',
                new_union(&ctx,
                  new_union(&ctx, '1',
                    new_union(&ctx, '2',
                      new_concat(&ctx, 'd',
                        new_concat(&ctx, 'e',
                          new_concat(&ctx, 'f',
                            new_union(&ctx, '3', '4')))))),
                  '5')))))));

  dump_exp(&ctx, ctx.exp_tree.root_id, 0);


  Exp *root = get_exp(&ctx, ctx.exp_tree.root_id);
  unsigned n_subexp = flatten_exp(&ctx, root->type, ctx.exp_tree.root_id, NULL);
  unsigned new_root_id = alloc_exp(&ctx, root->type, n_subexp);
  Exp *new_root = get_exp(&ctx, new_root_id);
  flatten_exp(&ctx, root->type, ctx.exp_tree.root_id, new_root->subexp);

  dump_exp(&ctx, new_root_id, 0);
#endif

  /*ctx.exp_tree.root_id =
    new_concat(&ctx,
      'a',
      new_concat(&ctx,
        'b',
        'c'));
  */

  ctx.exp_tree.root_id = alloc_exp(&ctx, kConcat, 5);
  Exp *root = get_exp(&ctx, ctx.exp_tree.root_id);
  root->subexp[4] = 'a';
  root->subexp[3] = 'c';
  root->subexp[2] = 'c';
  root->subexp[1] = 'c';
  root->subexp[0] = 'e';

  sort_exp(&ctx, ctx.exp_tree.root_id);
  dump_exp(&ctx, ctx.exp_tree.root_id, 0);

  //match_regexp(&ctx, "abcde", 5);

  return 0;
}
