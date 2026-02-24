#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <inttypes.h>

#include <pari/pari.h>

GEN
long_max_abs()
{
  GEN res = cgetipos(3);
  if (LONG_MAX+LONG_MIN <= 0)
    *((unsigned long *) (res+2)) = (unsigned long) LONG_MAX;
  else
    *((unsigned long *) (res+2)) = -((unsigned long) LONG_MIN);
  return res;
}

typedef struct {
  long M;
  GEN U;
  void *data;
  void (*f)(void *, GEN, GEN, long);
  int n;
  GEN e; /* long** */
  GEN b; /* long* */
  GEN c; /* long* */
  GEN doc; /* long* */
  GEN docp1; /* long* */
  GEN mu; /* long* */
  GEN lambda; /* long* */
  GEN tlob; /* long** */
  GEN x; /* long* */
} eqfminim_ctx;

static void
eqfminim_rec(int i, long Ni, int zero_so_far, eqfminim_ctx *ctx)
{
  int j;
  long r, in_xi, Nim1, dNim1, in_Nim1, in_dNim1, S;
  if (Ni<0) return;
  //pari_printf("eqfminim_rec for i=%d, Ni=%ld\n", i, Ni);
  if (i<=0) {
    if (zero_so_far)
      return;
    ctx->f(ctx->data, ctx->U, ctx->x, ctx->M-Ni);
    return;
  }
  S = 0;
  for(j=i+1; j<=ctx->n; j++)
    S -= gel(ctx->e, i)[j-i]*ctx->x[j];
  /* the following two lines should be optimized by compiler */
  in_xi = S/ctx->b[i];
  r = S%ctx->b[i];
  if (r<0) { /* stupid C, truncating towards 0 */
    in_xi--;
    r += ctx->b[i];
  }
  in_Nim1 = (Ni*ctx->docp1[i]-ctx->mu[i]*r*r)/ctx->doc[i];
  in_dNim1 = -ctx->tlob[i]*r + ctx->lambda[i];
  /* negative direction */
  ctx->x[i] = in_xi;
  Nim1 = in_Nim1;
  dNim1 = in_dNim1;
  while (Nim1 >= 0) {
    //pari_printf("x[%d]=%ld, Nim1=%ld\n", i, ctx->x[i], Nim1);
    if (zero_so_far) {
      if (ctx->x[i] < 0)
	break;
      eqfminim_rec(i-1, Nim1, ctx->x[i]==0, ctx);
    } else {
      eqfminim_rec(i-1, Nim1, 0, ctx);
    }
    ctx->x[i]--;
    dNim1 -= 2*ctx->lambda[i];
    Nim1 += dNim1;
  }
  /* positive direction */
  ctx->x[i] = in_xi+1;
  dNim1 = -in_dNim1;
  Nim1 = in_Nim1 + dNim1;
  while (Nim1 >= 0) {
    //pari_printf("x[%d]=%ld, Nim1=%ld\n", i, ctx->x[i], Nim1);
    if (zero_so_far) {
      if (ctx->x[i] >= 0)
	eqfminim_rec(i-1, Nim1, ctx->x[i]==0, ctx);
    } else {
      eqfminim_rec(i-1, Nim1, 0, ctx);
    }
    ctx->x[i]++;
    dNim1 -= 2*ctx->lambda[i];
    Nim1 += dNim1;
  }
}

static void
eqfminim_run(eqfminim_ctx *ctx, int up_to_sign_nozero)
{
  eqfminim_rec(ctx->n, ctx->M, up_to_sign_nozero, ctx);
}

static GEN
ZV_to_zv_block(GEN a){
  long N = lg(a), i;
  GEN b = cgetg_block(N, t_VECSMALL);
  for(i=1; i<N; i++)
    b[i] = itos(gel(a,i));
  return b;
}

static void
eqfminim_init(eqfminim_ctx *ctx, long M, GEN U, GEN c, GEN d,
	      GEN b, GEN mu, GEN e, GEN lambda, GEN tlob,
	      void *data, void (*f)(void *, GEN, GEN, long))
{
  int i, N;
  ctx->data = data;
  ctx->f = f;
  N = lg(d); /* TODO: check that it fits and N>0 */
  ctx->n = N-1;
  ctx->M = M;
  ctx->U = U;
  ctx->c = ZV_to_zv_block(c);
  ctx->b = ZV_to_zv_block(b);
  ctx->mu = ZV_to_zv_block(mu);
  ctx->lambda = ZV_to_zv_block(lambda);
  ctx->tlob = ZV_to_zv_block(tlob);
  ctx->doc = cgetg_block(N, t_VECSMALL);
  ctx->docp1 = cgetg_block(N, t_VECSMALL);
  for(i=1; i<N; i++) {
    ctx->doc[i] = itos(gel(d,i))/ctx->c[i];
    ctx->docp1[i] = itos(gel(d,i))/ctx->c[i+1];
  }
  ctx->x = cgetg_block(N, t_VECSMALL);
  ctx->e = cgetg_block(N, t_VEC);
  for(i=1; i<N; i++)
    gel(ctx->e, i) = ZV_to_zv_block(gel(e, i));
}

static void
eqfminim_free(eqfminim_ctx *ctx)
{
  long N = lg(ctx->e), i;
  killblock(ctx->c);
  killblock(ctx->b);
  killblock(ctx->mu);
  killblock(ctx->lambda);
  killblock(ctx->tlob);
  killblock(ctx->doc);
  killblock(ctx->docp1);
  killblock(ctx->x);
  for(i=1; i<N; i++)
    killblock(gel(ctx->e, i));
  killblock(ctx->e);
}

static void
inc_for_count_eqfminim(void *data, GEN U, GEN x, long norm)
{
  GEN c = (GEN) data;
  if (norm < 0 || norm+1 > lg(c)-1)
    pari_err(e_MISC, "invalid norm in inc_for_count_eqfminim");
  c[norm+1] += 2;
}

GEN
eqfminim_count_sub(GEN M, GEN c, GEN d, GEN b, GEN mu, GEN e, GEN lambda, GEN tlob)
{
  eqfminim_ctx ctx;
  long Mlong = itos(M);
  GEN res = zero_zv(1+Mlong);

  res[1] = 1;
  eqfminim_init(&ctx, Mlong, NULL, c, d, b, mu, e, lambda, tlob,
		(void *) res, &inc_for_count_eqfminim);
  eqfminim_run(&ctx, 1);
  eqfminim_free(&ctx);
  settyp(res, t_VEC);
  for(long i=0; i<=Mlong; i++)
    gel(res, i+1) = stoi(res[i+1]);
  return res;
}

typedef struct {
  size_t len;
  size_t cap;
  long *v;
} longs;

static void
init_longs(longs *dst)
{
  dst->len = 0;
  dst->cap = 0;
  dst->v = NULL;
}

static long *
push_longs(longs *dst, const long *src, size_t n)
{
  long *res;
  while (n > dst->cap || (dst->len > dst->cap - n)) {
    if (dst->cap) {
      dst->cap *= 2;
      pari_realloc_ip((void **) &dst->v, dst->cap*sizeof(long));
    } else {
      dst->cap = 128;
      dst->v = pari_malloc(dst->cap*sizeof(long));
    }
  }
  res = dst->v + dst->len;
  memcpy(res, src, n*sizeof(long));
  dst->len += n;
  return res;
}

typedef struct {
  long M;
  longs *svs;
} eqfminim_list_ctx;

static void
init_eqfminim_list_ctx(eqfminim_list_ctx *elc, eqfminim_ctx *ctx)
{
  elc->M = ctx->M;
  elc->svs = pari_malloc(elc->M*sizeof(longs));
  for(long i=0; i<elc->M; i++)
    init_longs(elc->svs+i);
}

static void
free_eqfminim_list_ctx(eqfminim_list_ctx *elc)
{
  for(long i=0; i<elc->M; i++) {
    if (elc->svs[i].v != NULL)
      pari_free(elc->svs[i].v);
  }
  pari_free(elc->svs);
}

static void
append_eqfminim(void *data, GEN U, GEN x, long norm)
{
  eqfminim_list_ctx *elc = (eqfminim_list_ctx *) data;
  if (norm<=0 || norm>elc->M)
    pari_err(e_MISC, "impossible norm");
  (void) push_longs(elc->svs+(norm-1), x+1, lg(x)-1);
}

static GEN
vecsmall_per(const long *v, GEN per)
{
  long n = lg(per)-1;
  GEN res = cgetg(n+1, t_VECSMALL);
  for(long i=0; i<n; i++)
    res[per[i+1]] = v[i];
  return res;
}

static GEN
vecsmall_per_canrepr(const long *v, GEN per)
{
  long n=lg(per)-1;
  long i;
  GEN res = vecsmall_per(v, per);
  for(i=1; i<n && res[i]==0; i++);
  if (res[i]<0) {
    for(; i<=n; i++)
      res[i] = -res[i];
  }
  return res;
}

/* copied from bibli1.c */
static GEN
ZC_canon(GEN V)
{
  long l = lg(V), j;
  for (j = 1; j < l  &&  signe(gel(V,j)) == 0; ++j);
  return (j < l  &&  signe(gel(V,j)) < 0)? ZC_neg(V): V;
}

static GEN
ZM_zc_mul_canrepr(GEN U, const long *v)
{
  pari_sp av = avma;
  long n = lg(U)-1;
  GEN vp = cgetg(n+1, t_VECSMALL);
  memcpy(vp+1, v, n*sizeof(long));
  return gerepileupto(av, ZC_canon(ZM_zc_mul(U, vp)));
}

static void
zc_to_ZC_inplace(GEN c)
{
  long n = lg(c)-1;
  settyp(c, t_COL);
  for(long i=1; i<=n; i++)
    gel(c, i) = stoi(c[i]);
}

static GEN
eqfminim_collect(GEN U, const longs *svs, long want_small)
{
  GEN res;
  size_t i;
  long *p = svs->v;
  long n = lg(U)-1, len;
  if (n) {
    if (svs->len%n)
      pari_err(e_MISC, "invalid length");
    len = svs->len/n;
  } else {
    len = 0;
  }
  if (typ(U)==t_VECSMALL) {
    res = cgetg(len+1, want_small ? t_VEC : t_MAT);
    for(i=1; i<=len; i++, p+=n) {
      gel(res, i) = vecsmall_per_canrepr(p, U);
      if (!want_small)
        zc_to_ZC_inplace(gel(res,i));
    }
    return res;
  }
  if (want_small)
    pari_err(e_MISC, "incompatible choices");
  if (typ(U)!=t_MAT)
    pari_err(e_MISC, "expected U to be a matrix");
  res = cgetg(len+1, t_MAT);
  for(i=1; i<=len; i++, p+=n)
    gel(res, i) = ZM_zc_mul_canrepr(U, p);
  return res;
}

GEN
eqfminim_sub(GEN M, GEN U, GEN c, GEN d, GEN b, GEN mu, GEN e, GEN lambda, GEN tlob,
	     long want_small)
{
  eqfminim_ctx ctx;
  eqfminim_list_ctx elc;
  GEN res;
  long Mlong = itos(M);

  eqfminim_init(&ctx, Mlong, U, c, d, b, mu, e, lambda, tlob,
		(void *) &elc, &append_eqfminim);
  init_eqfminim_list_ctx(&elc, &ctx);
  eqfminim_run(&ctx, 1);
  eqfminim_free(&ctx);
  res = cgetg(1+Mlong, t_VEC);
  for(long i=0; i<Mlong; i++)
    gel(res, i+1) = eqfminim_collect(U, elc.svs+i, want_small);
  free_eqfminim_list_ctx(&elc);
  return res;
}

/*
  faster inv_rs_pre:
  - rs_pre is [iso, V] where
    - iso is a vec of vecsmalls [type, rk, mult]
    - V is a vec of vecsmalls = v~*gram for v a simple root
*/

static void
flip_vec(long *v, long l)
{
  long i, j, p;
  for(i=0, j=l-1; i<j; i++, j--) {
    p = v[i];
    v[i] = v[j];
    v[j] = p;
  }
}

static void
sort_inv_rs_irr(long t, long *v, long l)
{
  long i, j, p;
  if (t==0) { /* A */
    for(i=0, j=l-1; i<j; i++, j--) {
      if (v[i]>v[j]) {
	flip_vec(v, l);
	return;
      }
      if (v[i]<v[j])
	return;
    }
    return;
  }
  if (t==1) { /* D */
    if (l==4) {
      if (v[1]>v[2]) {
        p = v[1];
	v[1] = v[2];
	v[2] = p;
      }
      if (v[2]>v[3]) {
        p = v[2];
	v[2] = v[3];
	v[3] = p;
      }
      if (v[1]>v[2]) {
        p = v[1];
	v[1] = v[2];
	v[2] = p;
      }
    } else {
      if (v[2]<v[1]) {
        p = v[1];
	v[1] = v[2];
	v[2] = p;
      }
    }
    return;
  } /* E */
  if (l==6 && (v[2]>v[4] || (v[2]==v[4] && v[3]>v[5]))) {
    p = v[2];
    v[2] = v[4];
    v[4] = p;
    p = v[3];
    v[3] = v[5];
    v[5] = p;
  }
  return;
}

static void
small_swap(long *a, long *b, long l)
{
  long i, p;
  for(i=0; i<l; i++) {
    p = *a;
    *(a++) = *b;
    *(b++) = p;
  }
}

static int
small_lex(long *a, long *b, long l)
{
  long i;
  for(i=0; i<l; i++) {
    if (a[i]<b[i])
      return -1;
    if (b[i]<a[i])
      return 1;
  }
  return 0;
}

static long *
min_small_lex(long *v, long rk, long mult)
{
  long *m = v;
  long i;
  for(i=1; i<mult; i++) {
    v += rk;
    if (small_lex(v, m, rk)<0)
      m = v;
  }
  return m;
}

static void
small_lex_sort(long *v, long rk, long mult)
{
  long *m;
  while (mult>1) {
    m = min_small_lex(v, rk, mult);
    if (m!=v)
      small_swap(m, v, rk);
    v += rk;
    mult--;
  }
}

static long *
sort_inv_rs_isot(long t, long *v, long rk, long mult)
{
  long i;
  long *w;
  for(i=0, w=v; i<mult; i++, w+=rk)
    sort_inv_rs_irr(t, w, rk);
  small_lex_sort(v, rk, mult);
  return w;
}

static void
inv_rs_sort(long *inv, GEN rs_class)
{
  long l = lg(rs_class)-1, i;
  long *p = inv+1;
  for(i=1; i<=l; i++) {
    GEN isot = gel(rs_class, i);
    long t = isot[1], rk = isot[2], mult = isot[3];
    p = sort_inv_rs_isot(t, p, rk, mult);
  }
}

static void
inv_rs_noalloc(long *inv, GEN rs_pre, long *v, long n, long nor)
{
  GEN W;
  long l, i, j;
  long *p, *q;
  W = gel(rs_pre, 2);
  l = lg(W)-1;
  inv[0] = nor;
  for(i=1; i<=l; i++) {
    p = gel(W,i)+1;
    q = v;
    inv[i] = *(p++)*(*(q++));
    for(j=2; j<=n; j++)
      inv[i] += *(p++)*(*(q++));
    /*if (debug)
      pari_printf("%ld-th dot prod is %ld\n", i, inv[i]);*/
  }
  inv_rs_sort(inv, gel(rs_pre,1));
}

GEN
inv_rs(GEN rs_pre, GEN v, long nor)
{
  GEN res;
  if (typ(v) != t_VECSMALL)
    pari_err(e_MISC, "v not vecsmall in inv_rs");
  res = cgetg(lg(gel(rs_pre,2))+1, t_VECSMALL);
  inv_rs_noalloc(res+1, rs_pre, v+1, lg(v)-1, nor);
  return res;
}


/* crude arenas, could perhaps be replaced by pari stacks */

typedef struct {
  char *beg;
  char *end;
} arena;

#define new(...)            newx(__VA_ARGS__,new3,new2)(__VA_ARGS__)
#define newx(a,b,c,d,...)   d
#define new2(a, t)          (t *)alloc(a, sizeof(t), _Alignof(t), 1)
#define new3(a, t, n)       (t *)alloc(a, sizeof(t), _Alignof(t), n)

void *alloc(arena *a, ptrdiff_t size, ptrdiff_t align, ptrdiff_t count)
{
  ptrdiff_t avail = a->end - a->beg;
  ptrdiff_t padding = -(uintptr_t)a->beg & (align - 1);
  if (count > (avail - padding)/size) {
    pari_err(e_MISC, "arena overflow");
  }
  ptrdiff_t total = size * count;
  char *p = a->beg + padding;
  a->beg += padding + total;
  //pari_printf("alloc'd %lx at %p\n", (unsigned long) total, p);
  return p;
}

/* dynamic arrays of uint32_t's, use up to twice their length */

typedef struct {
  uint64_t *v;
  ptrdiff_t len;
  ptrdiff_t cap;
} u64s;

static void
init_u64s(arena *a, u64s *s, ptrdiff_t cap)
{
  s->len = 0;
  s->cap = cap;
  if (cap)
    s->v = new(a, uint64_t, cap);
  else
    s->v = NULL;
}

static void
push_u64s(arena *a, u64s *s, uint64_t x)
{
  if (s->len >= s->cap) {
    if (s->cap > 0) {
      s->cap *= 2;
      uint64_t *newv = new(a, uint64_t, s->cap);
      memcpy(newv, s->v, s->len*sizeof(uint64_t));
      s->v = newv;
    } else {
      s->v = new(a, uint64_t, 1024);
      s->cap = 1024;
    }
  }
  s->v[s->len++] = x;
}


/* begin fast_marked_HBV */

typedef struct {
  arena are;
  char *are_data;
  int n;
  uint64_t *gram2; /* gram mod 2 */
  uint64_t *U2; /* lines of U mod 2 */
  u64s svs; /* short vectors */
  u64s sv_pwms; /* their pairings with marked vecs, compactly encoded */
  GEN mark;
  uint64_t *incmat;
} fmHBV_ctx;

/* parity of coeffs of vec */
static uint64_t
vec2u64(GEN v)
{
  long i, l = lg(v)-1;
  uint64_t res = 0;
  if (l>64)
    pari_err(e_MISC, "dim>64 in vec2u64");
  for(i=1; i<=l; i++)
    res |= (((uint64_t) itos(gel(v,i))) & 1)<<(i-1);
  return res;
}

static uint64_t
vecsmall2u64(GEN v)
{
  long i, l = lg(v)-1;
  uint64_t res = 0;
  if (l>64)
    pari_err(e_MISC, "dim>64 in vecsmall2u64");
  for(i=1; i<=l; i++)
    res |= (((uint64_t) v[i]) & 1)<<(i-1);
  return res;
}

static uint64_t
u64_mat_act_vec(int n, uint64_t *M, uint64_t x)
{
  uint64_t res = 0;
  int i;
  for(i=0; i<n; i++)
    res |= ((uint64_t) __builtin_popcountl(*(M++)&x)&1)<<i;
  return res;
}

static void
init_fmHBV_ctx(fmHBV_ctx *f, GEN gram, GEN U, GEN mark)
{
  if(lg(gram)>65)
    pari_err(e_MISC, "dim>64 in init_fmHBV_ctx");
  f->n = lg(gram)-1;
  f->are_data = pari_malloc(1UL<<30); /* 256MB */
  f->are.beg = f->are_data;
  f->are.end = f->are.beg + (1UL<<30);
  f->gram2 = new(&f->are, uint64_t, f->n);
  for(int i=0; i<f->n; i++)
    f->gram2[i] = vec2u64(gel(gram,i+1));
  if (lg(mark) > 22) /* 3 bits each */
    pari_err(e_MISC, "too many marked vectors");
  f->mark = mark;
  init_u64s(&f->are, &f->svs, 1024);
  init_u64s(&f->are, &f->sv_pwms, 1024);
  f->incmat = NULL;
}

static void
append_eqfminim_fmHBV(void *data, GEN U, GEN x, long norm)
{
  fmHBV_ctx *f = (fmHBV_ctx *) data;
  long pwm, epsilon=0;
  uint64_t pwms=0;
  pari_sp av = avma;
  long v[65];

  v[0] = x[0];
  for(long i=1; i<lg(x); i++)
    v[U[i]] = x[i];
  push_u64s(&f->are, &f->svs, vecsmall2u64(v));
  for(int i=1; i<lg(f->mark); i++) {
    pwm = zv_dotproduct(gel(f->mark,i), v); /* between -2 and 2 */
    if (!epsilon && pwm) {
      if (pwm > 0) epsilon = 1;
      else epsilon = -1;
    }
    pwms = pwms<<3 | ((uint64_t) (pwm*epsilon + 3));
  }
  push_u64s(&f->are, &f->sv_pwms, pwms);
  set_avma(av);
}

static uint32_t
dot_prod_bits(ptrdiff_t len, uint64_t *x, uint64_t *y)
{
  uint32_t res = 0;
  while(len--)
    res += __builtin_popcountl(*(x++)&*(y++));
  return res;
}

static int
cmp_u32(const void *pa, const void *pb)
{
  uint32_t a = *((uint32_t *) pa), b = *((uint32_t *) pb);
  if (a<b)
    return -1;
  if (a>b)
    return 1;
  return 0;
}

static int
cmp_u64(const void *pa, const void *pb)
{
  uint64_t a = *((uint64_t *) pa), b = *((uint64_t *) pb);
  if (a<b)
    return -1;
  if (a>b)
    return 1;
  return 0;
}

/* faster invariants for (odd) unimodular lattices with marked vectors */
ulong
fast_marked_HBV_sub(GEN gram, GEN M, GEN U, GEN c, GEN d, GEN b, GEN mu, GEN e,
		    GEN lambda, GEN tlob, GEN mark, GEN verbg)
{
  eqfminim_ctx ctx;
  fmHBV_ctx f;
  uint64_t h;
  uint64_t *incmat, *p, *q, *hashes;
  uint32_t *line;
  ptrdiff_t incmat_sz, i, j;
  int k;
  pari_timer T;
  long verb = itos(verbg);

  if (sizeof(ulong)!=sizeof(uint64_t) || sizeof(unsigned int)!=sizeof(uint32_t))
    pari_err(e_MISC, "unexpected bit widths in fast_marked_HBV_sub");
  if (typ(U) != t_VECSMALL)
    pari_err(e_MISC, "U must be a Vecsmall");
  if (verb)
    timer_start(&T);
  eqfminim_init(&ctx, itos(M), U, c, d, b, mu, e, lambda, tlob,
		(void *) &f, &append_eqfminim_fmHBV);
  init_fmHBV_ctx(&f, gram, U, mark);
  eqfminim_run(&ctx, 1);
  eqfminim_free(&ctx);
  if (verb)
    timer_printf(&T, "enumerated %ld short vectors", (long) f.svs.len);
  incmat_sz = f.svs.len/64;
  if (f.svs.len%64)
    incmat_sz++;
  incmat = new(&f.are, uint64_t, f.svs.len*incmat_sz);
  p = incmat;
  //pari_printf("incidence matrix (incmat_sz=%ld):\n", (long) incmat_sz);
  for(i=0; i<f.svs.len; i++) {
    uint64_t x = u64_mat_act_vec(f.n, f.gram2, f.svs.v[i]);
    for(j=0, k=0; j<f.svs.len; j++) {
      if (k==0)
	*p = 0;
      *p |= ((uint64_t) __builtin_popcountl(f.svs.v[j]&x)&1)<<(k++);
      if (k==64) {
	k = 0;
	p++;
      }
    }
    if (k)
      p++;
    //pari_printf("\n");
  }
  /*pari_printf("as u64's:\n");
  for(i=0; i<f.svs.len; i++)
  pari_printf("%lx\n", (unsigned long) incmat[i]);*/
  if (verb)
    timer_printf(&T, "computed incidence matrix (each line has %ld u64's)",
		 (long) incmat_sz);
  hashes = new(&f.are, uint64_t, f.svs.len);
  line = new(&f.are, uint32_t, f.svs.len);
  /* line will hold a line of the square of the incidence matrix */
  for(p=incmat, i=0; i<f.svs.len; i++, p+=incmat_sz) {
    /*if ((((unsigned long) i) & 127UL) == 0)
      pari_printf("i=%ld\n", (long) i);*/
    h = 13282407956253574712UL;
    h = (h^((uint64_t) f.sv_pwms.v[i]))*1111111111111111111UL;
    for(q=incmat, j=0; j<f.svs.len; j++, q+=incmat_sz)
      line[j] = dot_prod_bits(incmat_sz, p, q);
    qsort(line, f.svs.len, sizeof(uint32_t), cmp_u32);
    /*pari_printf("i=%ld, v=", (long) i);
    print_u32_bin(f.n, f.svs.v[i]);
    for(j=0; j<f.svs.len; j++) {
      pari_printf(",%lx", (unsigned long) line[j]);
    }
    pari_printf("\n");*/
    for(j=0; j<f.svs.len; j++)
      h = (h^((uint64_t) line[j]))*1111111111111111111UL;
    hashes[i] = h;
  }
  if (verb)
    timer_printf(&T, "computed hashes");
  qsort(hashes, f.svs.len, sizeof(uint64_t), cmp_u64);
  /*pari_printf("hashes:\n");
  for(i=0; i<f.svs.len; i++)
  pari_printf(" %lx\n", hashes[i]);*/
  //timer_printf(&T, "sorted hashes");
  h = 13282407956253574712UL;
  for(i=0; i<f.svs.len; i++)
    h = (h^hashes[i])*1111111111111111111UL;
  /*if (verb)
    pari_printf("used %ld bytes from arena (%ld short vectors)\n",
    (long) (f.are.beg-f.are_data), (long) f.svs.len);*/
  pari_free(f.are_data);
  return h;
}

/* end fast_marked_HBV */

/* begin qfautors with vector sums */

/*
  - enumerate vectors with same invariants as basis vectors:
    - compute invariants of basis vectors, sort them -> invv
    - run eqfminim_rec with a callback f computing invariants,
      keeping vectors invariant in invv (dynamic array or list)
    - for each inv in invv, sum these vectors, keep the nonzero sums
      (slightly better: use LLL as below to find a basis)
    - refine each list of vectors with given invariant according to
      scalar products with these sums.  This gives a finer invariant,
      again we only keep the ones corresponding to the basis vectors
      -> finvv
  - fingerprint and corresponding permutation
    (with these lists by "fine invariant")
    Somehow evaluate if we should bother with vector sums?
  - Compute vector sums: for each basis vector b, each fine invariant
    fi in finvv, and each s, compute the sum S(b,fi,s) of all v having
    fine invariant fi and s.t. v.b==s
    The number of relevant pairs (fi,s) may be quite large so we seek
    a basis of the Z-module generated by the S(b,fi,s). qfauto (in
    gen_comb) applies LLL for this: in pari, lllall(G, LLL_IM | LLL_GRAM)
    for G = qfeval(gram, (S(b,fi,s))_{fi,s}) which gives the coefficients
    of a basis.
    Let N be the number of such sums, r the rank, d the lattice dim.
    G has dim (N,N) so if N is big this LLL is expensive.  This problem
    should not exist because if N is big then we probably don't need vector
    sums (NB: qfauto with no flag imposes 2r<=d+1).  Perhaps try to increase
    the number of vectors as long as N is at most some parameter times d?
    With a candidate instead of b: after computing the N sums, O(drN)
    operations to extract the basis, O(dr(r+1)/2) operations to compute
    their Gram matrix, O((N-r)rd) operations to check the rest of the
    sums, so O(Nd^2) operations in total.
 */

static void
inv_of_basis_vectors(GEN *bvinvs, GEN *bvii, GEN gram_diag, GEN rs_pre)
{
  GEN W = gel(rs_pre, 2);
  long i, j;
  long n = lg(gram_diag)-1;
  long r = lg(W)-1;
  *bvinvs = cgetg(n+1, t_VEC);
  setlg(*bvinvs, 1);
  *bvii = cgetg(n+1, t_VECSMALL);
  for(i=1; i<=n; i++) {
    pari_sp av = avma;
    GEN inv = cgetg(r+2, t_VECSMALL);
    long ind;
    inv[1] = gram_diag[i];
    for(j=1; j<=r; j++)
      inv[j+1] = gel(W,j)[i];
    inv_rs_sort(inv+1, gel(rs_pre,1));
    ind = vecvecsmall_search(*bvinvs, inv);
    if (ind > 0) {
      (*bvii)[i] = ind;
      set_avma(av);
      continue;
    }
    ind = -ind;
    setlg(*bvinvs, lg(*bvinvs)+1);
    for(j=lg(*bvinvs)-1; j>ind; j--)
      gel(*bvinvs, j) = gel(*bvinvs, j-1);
    gel(*bvinvs, ind) = inv;
    (*bvii)[i] = ind;
    for(j=1; j<i; j++) {
      if ((*bvii)[j] >= ind)
	(*bvii)[j]++;
    }
  }
}

static GEN
small_diag(GEN M)
{
  long n = lg(M)-1;
  GEN d = cgetg(n+1, t_VECSMALL);
  for(; n>0; n--)
    d[n] = itos(gcoeff(M, n, n));
  return d;
}

typedef struct {
  GEN ZMgram;
  GEN gram;
  GEN rspU;
  pari_sp gav;
  GEN bvinvs; /* sorted vec of invariants (vecsmalls) of basis vectors b_i */
  GEN bvii; /* bv_invs[bvii[i]] is the invariant of b_i */
  GEN V;
  /* V is a vec of linked lists, implemented as NULL or t_VECSMALL
     with "hidden" pointer after the last element */
  GEN Vlen;
  GEN Vsums;
  GEN scratch;
  GEN fp; /* fingerprint */
  GEN per; /* permutation optimizing fingerprint */
  GEN vecsums;
  long depth;
  pari_timer T;
} qfautors_ctx;

/* the following three functions are from pari/src/basemath/qfisom.c */
static long
Z_trunc(GEN z)
{
  long s = signe(z);
  return s==0 ? 0: (long)(s*mod2BIL(z));
}

static GEN
ZV_trunc_to_zv(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) x[i] = Z_trunc(gel(z,i));
  return x;
}

static GEN
ZM_trunc_to_zm(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = ZV_trunc_to_zv(gel(z,i));
  return x;
}

static void
init_qfautors_ctx(qfautors_ctx *fqc, GEN gram, GEN rs_pre, GEN rspU)
{
  long i;
  long n = lg(gram)-1;
  GEN W = gel(rs_pre, 2);

  fqc->ZMgram = gram;
  fqc->gram = ZM_trunc_to_zm(gram);
  fqc->rspU = rspU;
  fqc->gav = avma;
  inv_of_basis_vectors(&fqc->bvinvs, &fqc->bvii, small_diag(gram), rs_pre);
  fqc->V = cgetg(lg(fqc->bvinvs), t_VEC);
  fqc->Vsums = cgetg(lg(fqc->bvinvs), t_VEC);
  fqc->Vlen = cgetg(lg(fqc->bvinvs), t_VECSMALL);
  for(i=1; i<lg(fqc->bvinvs); i++) {
    gel(fqc->V, i) = NULL;
    gel(fqc->Vsums, i) = zero_zv(n);
    fqc->Vlen[i] = 0;
  }
  fqc->scratch = cgetg(n+2, t_VECSMALL);
  if (lg(W)-1 > n)
    pari_err(e_MISC, "impossible: more than dim simple roots");
  setlg(fqc->scratch, lg(W)+1);
  /* scratch will be used for temporary invariants, +1 for norm */
}

static void
append_eqfminim_qfautors(void *data, GEN U, GEN x, long norm)
{
  qfautors_ctx *fqc = (qfautors_ctx *) data;
  long n = lg(x)-1, i, pos;

  inv_rs_noalloc(fqc->scratch+1, fqc->rspU, x+1, n, norm);
  pos = vecvecsmall_search(fqc->bvinvs, fqc->scratch);
  if (pos > 0) {
    GEN y = new_chunk(n+2);
    y[0] = x[0];
    ((GEN *) y)[n+1] = gel(fqc->V, pos);
    gel(fqc->V, pos) = y;
    for(i=1; i<=n; i++)
      y[U[i]] = x[i];
    fqc->Vlen[pos]++;
    /* TODO (optimization for small root systems): if invariant is 0, return
       It will be necessary to handle this case separately elsewhere as well
     */
    for(i=1; i<=n; i++)
      gel(fqc->Vsums, pos)[i] += y[i];
  }
  /* compute invariant of -x */
  for(i=2; i<lg(fqc->scratch); i++)
    fqc->scratch[i] = -fqc->scratch[i];
  inv_rs_sort(fqc->scratch+1, gel(fqc->rspU,1));
  pos = vecvecsmall_search(fqc->bvinvs, fqc->scratch);
  if (pos > 0) {
    GEN y = new_chunk(n+2);
    y[0] = x[0];
    ((GEN *) y)[n+1] = gel(fqc->V, pos);
    gel(fqc->V, pos) = y;
    for(i=1; i<=n; i++)
      y[U[i]] = -x[i];
    fqc->Vlen[pos]++;
    for(i=1; i<=n; i++)
      gel(fqc->Vsums, pos)[i] += y[i];
  }
}

/*
  v is a zm, gram a Gram matrix (ZM) for which the columns of
  v are expected to be "small", compute gram*(basis of v),
  truncated to longs (i.e. reduce mod 2^N)
*/
static GEN
zm_basis_trunc(GEN gram, GEN v)
{
  pari_sp av = avma;
  GEN V = zm_to_ZM(v);
  GEN R = lllgramint(ZM_transmultosym(V, ZM_mul(gram, V)));
  return gerepileupto(av, ZM_trunc_to_zm(ZM_mul(gram,ZM_mul(V, R))));
}

static GEN
hash_pairs_GEN(hashtable *h)
{
  long k = 1;
  ulong i;
  hashentry *e;
  GEN v = cgetg(h->nb+1, t_VEC);
  for (i = 0; i < h->len; i++)
  {
    for (e = h->table[i]; e != NULL; e = e->next)
      gel(v, k++) = mkvec2((GEN) e->key, (GEN) e->val);
  }
  return v;
}

static int
cmp_first_vecsmall(void *ignored, GEN a, GEN b)
{
  return vecsmall_lexcmp(gel(a,1), gel(b,1));
}

static GEN
sorted_hash_pairs_GEN(hashtable *h)
{
  GEN hp = hash_pairs_GEN(h);
  gen_sort_inplace(hp, NULL, &cmp_first_vecsmall, NULL);
  return hp;
}

#define MAX_FINE_INV 10

/*
  Divide the linked list gel(fqc->V,i) (corresponding to
  invariant gel(fqc->bvinvs,i)) according to refined invariant
  with respect to B
  First compute this refined invariant for the basis vectors e_j
  such that fqc->bvii[j]==i
  Only keep at most MAX_FINE_INV additional fine invariants
*/
static GEN
refine_inv_i(qfautors_ctx *fqc, GEN B, long i)
{
  long j, k, lB = lg(B)-1;
  long n = lg(fqc->bvii)-1;
  long efic = 0; /* number of extra fine inv */
  GEN v, nextv;
  ulong h;
  /* key: dot prods with B (vecsmall),
     val: vecsmall [length, linked list of vecs] */
  hashtable ht;
  hashentry *e;
  //pari_printf("computing pairs for i=%ld\n", i);
  hash_init_GEN(&ht, n+MAX_FINE_INV, zv_equal, 1);
  for(j=1; j<=n; j++) {
    if (fqc->bvii[j]!=i) continue;
    pari_sp av = avma;
    GEN finv = cgetg(lB+1, t_VECSMALL), val;
    for(k=1; k<=lB; k++)
      finv[k] = gel(B,k)[j];
    h = hash_GEN(finv);
    e = hash_search2(&ht, (void *) finv, h);
    if (e != NULL) {
      //pari_printf("j=%ld, fine inv already in ht\n", j);
      set_avma(av);
      continue;
    }
    //pari_printf("j=%ld, new fine inv\n", j);
    val = cgetg(3, t_VECSMALL);
    val[1] = 0;
    val[2] = (long) NULL;
    hash_insert2(&ht, finv, val, h);
  }
  for(v = gel(fqc->V,i); v!=NULL; v = nextv) {
    //pari_printf("v=%Ps\n", v);
    pari_sp av = avma;
    GEN finv = cgetg(lB+1, t_VECSMALL);
    nextv = (GEN) v[n+1];
    for(j=1; j<=lB; j++)
      finv[j] = zv_dotproduct(v, gel(B,j));
    h = hash_GEN(finv);
    e = hash_search2(&ht, (void *) finv, h);
    if (e != NULL) {
      GEN val = (GEN) e->val;
      val[1]++;
      v[n+1] = val[2];
      val[2] = (long) v;
      set_avma(av);
    } else if (efic < MAX_FINE_INV) {
      GEN val = cgetg(3, t_VECSMALL);
      efic++;
      val[1] = 1;
      val[2] = (long) v;
      v[n+1] = (long) NULL;
      hash_insert2(&ht, finv, val, h);
    }
  }
  return sorted_hash_pairs_GEN(&ht);
}

static GEN
my_vecsmall_copy(GEN v)
{
  long l = lg(v)-1;
  GEN res = cgetg(l+1, t_VECSMALL);
  memcpy(res+1, v+1, l*sizeof(long));
  return res;
}

static int
vecsmall_prefixcmp_nodata(void *ignored, GEN a, GEN b)
{
  return vecsmall_prefixcmp(a, b);
}

/* adapted from gen_search */
static long
vecsmall_search_fst(GEN T, GEN finv)
{
  long u = lg(T)-1, i, l, s;

  if (!u) return -1;
  l = 1;
  do
  {
    i = (l+u) >> 1; s = vecsmall_prefixcmp(finv, gmael(T,i,1));
    if (!s) return i;
    if (s < 0) u = i-1; else l = i+1;
  } while (u >= l);
  return -((s < 0)? i: i+1);
}

static void
refine_inv(qfautors_ctx *fqc, GEN B)
{
  long i, j, k, l, n = lg(fqc->bvii)-1, finvc = 0;
  GEN filist, dummy, newbvii, finv, newbvinvs, newV, v;
  pari_sp av;
  filist = cgetg(n+1, t_VEC);
  //pari_printf("#bvinvs=%ld\n", lg(fqc->bvinvs)-1);
  for(i=1; i<lg(fqc->bvinvs); i++) {
    GEN pairs = refine_inv_i(fqc, B, i);
    gel(filist, i) = pairs;
    finvc += lg(pairs)-1;
  }
  //pari_printf("computed pairs\n");
  dummy = cgetg(4, t_VEC);
  newbvii = cgetg(n+1, t_VECSMALL);
  gel(dummy, 1) = newbvii;
  av = avma;
  finv = cgetg(lg(B), t_VECSMALL);
  for(i=1; i<=n; i++) {
    for(j=1; j<lg(B); j++)
      finv[j] = gel(B,j)[i];
    newbvii[i] = vecsmall_search_fst(gel(filist, fqc->bvii[i]), finv);
    if (newbvii[i] <= 0)
      pari_err(e_MISC, "impossible in refine_inv");
    for(j=1; j<fqc->bvii[i]; j++)
      newbvii[i] += lg(gel(filist,j))-1;
  }
  set_avma(av);
  //pari_printf("computed new bvii: %Ps\n", newbvii);
  /* collect in just one list, sort vector lists */
  newbvinvs = cgetg(finvc+1, t_VEC);
  gel(dummy, 2) = newbvinvs;
  newV = cgetg(finvc+1, t_VEC);
  gel(dummy, 3) = newV;
  k=0;
  for(i=1; i<lg(fqc->bvinvs); i++) {
    GEN L = gel(filist, i);
    for(j=1; j<lg(L); j++) {
      /* gel(L,j) is [finv, [length, linked list]] */
      k++;
      gel(newbvinvs,k) = shallowconcat(gel(fqc->bvinvs,i), gmael(L,j,1));
      gel(newV,k) = cgetg(1+gmael(L,j,2)[1], t_VEC);
      for(l=1,v=gmael3(L,j,2,2); v!=NULL; l++,v=(GEN)v[n+1])
	gmael(newV, k, l) = my_vecsmall_copy(v);
      gen_sort_inplace(gel(newV, k), NULL, &vecsmall_prefixcmp_nodata, NULL);
    }
  }
  if (k != finvc)
    pari_err(e_MISC, "k != finvc");
  dummy = gerepileupto(fqc->gav, dummy);
  fqc->bvii = gel(dummy, 1);
  fqc->bvinvs = gel(dummy, 2);
  fqc->V = gel(dummy, 3);
}

static void
qfautors_fingerprint(qfautors_ctx *fqc)
{
  long n = lg(fqc->gram)-1, i;
  GEN per = cgetg(n+1, t_VECSMALL);
  for(i=1; i<=n; i++) per[i] = i;
  fqc->fp = cgetg(n+1, t_VECSMALL);
  for(i=1; i<=n; i++) {
    //pari_printf("i=%ld\n", i);
    /* per[1], ..., per[i-1] already chosen, choose next among
       per[i], ..., per[n] */
    long m=-1, j, jm=-1;
    for(j=i; j<=n; j++) {
      long pj = per[j], c=0, k, l;
      GEN L = gel(fqc->V, fqc->bvii[pj]);
      //pari_printf("j=%ld, per[j]=%ld, %ld vectors\n", j, pj, lg(L)-1);
      for(l=1; l<lg(L); l++) {
	c++;
	for(k=1; k<i; k++) {
	  GEN Gk = gel(fqc->gram, per[k]);
	  if (zv_dotproduct(Gk, gel(L,l)) != Gk[pj]) {
	    c--;
	    break;
	  }
	}
      }
      if (j==i || c<m) {
	m = c;
	jm = j;
      }
    }
    if (m <= 0)
      pari_err(e_MISC, "qfautors_fingerprint: no extension");
    fqc->fp[i] = m;
    m = per[i];
    per[i] = per[jm];
    per[jm] = m;
  }
  fqc->per = per;
}

/*
  sorted (by first coord) vec of
  [[inv(v), e_{per[i]}.v, ..., e_{per[i-l+1]}.v], sum of such v]
  where l = min(fqc->depth,i)
*/
static GEN
qfautors_vecsums_i(qfautors_ctx *fqc, long i)
{
  GEN shp, scps, M, T, B, BI, gramB;
  long j, k, l, m, n=lg(fqc->gram)-1;
  hashtable ht;
  hashentry *e;
  ulong h;
  pari_sp av = avma;
  l = (i >= fqc->depth) ? fqc->depth : i;
  hash_init_GEN(&ht, 100, zv_equal, 1); /* TODO: replace 100 */
  for(j=1; j<lg(fqc->V); j++) {
    GEN V = gel(fqc->V, j);
    /* TODO: if lg(V) is huge, skip this one */
    for(k=1; k<lg(V); k++) {
      GEN v = gel(V,k), vsum;
      pari_sp subav = avma;
      GEN scp = cgetg(l+2, t_VECSMALL);
      scp[1] = j;
      for(m=0; m<l; m++) /* v.e_{per[i-m]} */
	scp[m+2] = zv_dotproduct(gel(fqc->gram, fqc->per[i-m]), v);
      h = hash_GEN(scp);
      e = hash_search2(&ht, (void *) scp, h);
      if (e != NULL) {
	vsum = e->val;
	for(m=1; m<=n; m++)
	  vsum[m] += v[m];
	set_avma(subav);
	continue;
      }
      vsum = my_vecsmall_copy(v);
      hash_insert2(&ht, scp, vsum, h);
    }
  }
  shp = sorted_hash_pairs_GEN(&ht);
  scps = cgetg(lg(shp), t_VEC);
  for(j=1; j<lg(shp); j++)
    gel(scps, j) = gmael(shp, j, 1);
  /* TODO: ensure that not too big, otherwise need to reduce depth */
  /* the following is pretty much identical to gen_comb in qfisom.c */
  M = cgetg(lg(shp), t_MAT);
  for(j=1; j<lg(shp); j++)
    gel(M, j) = vecsmall_to_col(gmael(shp, j, 2));
  T = lllgramint(ZM_transmultosym(M, ZM_mul(fqc->ZMgram, M)));
  B = ZM_mul(M, T);
  BI = RgM_inv(B);
  gramB = ZM_mul(fqc->ZMgram, B);
  /*
    sorted list of [inv(v), v.e_i, ...]: scps
    coefficients of a basis: ZM_trunc_to_zm(T)
    Gram matrix of this basis: ZM_trunc_to_zm(ZM_transmultosym(B, gramB))
    coefficients of all vecsums in this basis: ZM_trunc_to_zm(RgM_mul(BI,M))
    scalar products with respect to e_1, ..., e_n (will only use <i): ZM_trunc_to_zm(gramB)
  */
  return gerepilecopy(av, mkvec5(scps, ZM_trunc_to_zm(T),
				 ZM_trunc_to_zm(ZM_transmultosym(B, gramB)),
				 ZM_trunc_to_zm(RgM_mul(BI,M)),
				 ZM_trunc_to_zm(gramB)));
}

static void
qfautors_vecsums(qfautors_ctx *fqc, long depth)
{
  long i, n=lg(fqc->gram)-1;
  fqc->depth = depth;
  if (depth <= 0)
    return;
  fqc->vecsums = cgetg(n+1, t_VEC);
  for(i=1; i<=n; i++)
    gel(fqc->vecsums, i) = qfautors_vecsums_i(fqc, i);
}

static int
qfautors_ck_vecsums(qfautors_ctx *fqc, long i, GEN g, GEN spwg)
{
  long n = lg(fqc->gram)-1, j, k, l, m;
  pari_sp av = avma;
  GEN scps, scp, vecsums, T, B, gramB, gramB0, tBgramB0, ccoef;
  int res = 1;
  if (i+1 >= n)
    return 0;
  scps = gmael(fqc->vecsums, i, 1);
  l = (i >= fqc->depth) ? fqc->depth : i;
  scp = cgetg(l+2, t_VECSMALL);
  vecsums = cgetg(lg(scps), t_VEC);
  for(j=1; j<lg(scps); j++)
    gel(vecsums, j) = zero_zv(n);
  for(j=1; j<lg(fqc->V); j++) {
    GEN V = gel(fqc->V, j);
    for(k=1; k<lg(V); k++) {
      GEN v = gel(V,k);
      long pos;
      scp[1] = j;
      for(m=0; m<l; m++) /* v.g[per[i-m]] */
	scp[m+2] = zv_dotproduct(gel(spwg, fqc->per[i-m]), v);
      if ((pos = vecvecsmall_search(scps, scp)) <= 0) {
	goto end;
      }
      for(m=1; m<=n; m++)
	gel(vecsums, pos)[m] += v[m];
    }
  }
  T = gmael(fqc->vecsums, i, 2);
  B = zm_mul(vecsums, T);
  gramB = zm_mul(fqc->gram, B); /* TODO: zm_transmul */
  /* check transp(B)*gramB against gmael(fqc->vecsums, i, 3) */
  tBgramB0 = gmael(fqc->vecsums, i, 3);
  for(j=1; j<lg(B); j++) {
    for(k=j; k<lg(B); k++) {
      if (zv_dotproduct(gel(B,j),gel(gramB,k)) != gel(tBgramB0,j)[k]) {
	goto end;
      }
    }
  }
  /* check vecsums against B*gmael(fqc->vecsums, i, 4) */
  ccoef = gmael(fqc->vecsums, i, 4);
  for(j=1; j<lg(vecsums); j++) {
    GEN vs = gel(vecsums, j);
    GEN coe = gel(ccoef, j);
    for(k=1; k<=n; k++) {
      long c = 0;
      for(m=1; m<lg(B); m++)
	c += gel(B,m)[k]*coe[m];
      if (c != vs[k]) {
	goto end;
      }
    }
  }
  /* for 1<=k<=i-l check g[per[k]]~*gramB against line per[k] of
     gmael(fqc->vecsums, i, 5)
     Note: same for i-l+1<=k<=i would amount to just counting
     Note: this seems to be useless?
  */
  gramB0 = gmael(fqc->vecsums, i, 5);
  for(k=1; k<=i-l; k++) {
    long pk = fqc->per[k];
    for(j=1; j<lg(B); j++) {
      if (zv_dotproduct(gel(g,pk),gel(gramB,j)) != gel(gramB0,j)[pk]) {
	goto end;
      }
    }
  }
  /* TODO: save gramB for additional checks (per[i+1], ..., per[n]) later? */
  res = 0;
 end:
  set_avma(av);
  return res;
}

static int
qfautors_extends(qfautors_ctx *fqc, long i, GEN v, GEN spwg)
{
  long j, pi = fqc->per[i];
  GEN row = gel(fqc->gram, pi);
  for(j=1; j<i; j++) {
    long pj = fqc->per[j];
    if (zv_dotproduct(gel(spwg,pj),v) != row[pj])
      return 0;
  }
  return 1;
}

/*
  select vectors among candidates for g[per[i]] having correct scalar
  product with first i-1 vectors, but only if we have the expected
  amount (fingerprint), otherwise NULL (caller is also expected to clean
  up in this case)
*/
static GEN
qfautors_poss(qfautors_ctx *fqc, long i, GEN g, GEN spwg)
{
  long pi=fqc->per[i], fpi=fqc->fp[i], j, k=0;
  GEN poss, candidates = gel(fqc->V, fqc->bvii[pi]);
  if (i == 1)
    return candidates;
  poss = cgetg(fpi+1, t_VEC);
  for(j=1; j<lg(candidates); j++) {
    GEN v = gel(candidates, j);
    if(qfautors_extends(fqc, i, v, spwg)) {
      if (++k > fpi)
	return NULL;
      gel(poss, k) = v;
    }
  }
  if (k != fpi)
    return NULL;
  return poss;
}

/*
  search for one automorphism extending g[per[1]], ..., g[per[i-1]]
  return 1 if it exists, 0 otherwise, and put the result in g
  pre-allocated spwg is for gram*g
*/
static int
qfautors_search(qfautors_ctx *fqc, long i, GEN g, GEN spwg)
{
  int res=0;
  long pi = fqc->per[i], j, k=0, n=lg(fqc->gram)-1;
  pari_sp av = avma;
  GEN poss;
  if ((poss = qfautors_poss(fqc, i, g, spwg)) == NULL)
    goto end;
  if (i == n) {
    memcpy(gel(g,pi)+1, gel(poss,1)+1, n*sizeof(long));
    res = 1;
    goto end;
  }
  for(j=1; j<lg(poss); j++) {
    memcpy(gel(g,pi)+1, gel(poss,j)+1, n*sizeof(long));
    for(k=1; k<=n; k++)
      gel(spwg,pi)[k] = zv_dotproduct(gel(fqc->gram,k), gel(g,pi));
    if ((fqc->depth > 0) && qfautors_ck_vecsums(fqc, i, g, spwg))
      continue;
    if (qfautors_search(fqc, i+1, g, spwg)) {
      res = 1;
      goto end;
    }
  }
 end:
  set_avma(av);
  return res;
}

static long *
push_long(long x)
{
  long *res = new_chunk(1);
  *res = x;
  return res;
}

static void
update_orbit_mainloop(long *newelts, long numnewelts, GEN Vs, GEN seen,
		      GEN orb, long *orblen, GEN gens, GEN v)
{
  GEN g;
  long i, j, n=lg(v)-1;
  int in_orb;
  while (numnewelts > 0) {
    numnewelts--;
    i = *newelts;
    set_avma((pari_sp) ++newelts); /* pop */
    if (i > 0) {
      in_orb = 1;
    } else {
      in_orb = 0;
      i = -i;
    }
    for(g=gens; lg(g)==3; g=gel(g,2)) {
      for(j=1; j<=n; j++)
	v[j] = zv_dotproduct(gmael(g,1,j), gel(Vs,i));
      if ((j = vecvecsmall_search(Vs, v)) <= 0)
	pari_err(e_MISC, "g*v not found in update_orbit_mainloop");
      if (F2v_coeff(seen, j))
	continue;
      F2v_set(seen, j);
      numnewelts++;
      newelts = push_long(in_orb ? j : -j);
      if (in_orb) {
	F2v_set(orb, j);
	(*orblen)++;
      }
    }
  }
}

/* the head of gens is a newly found automorphism
   update seen, orb and *orblen accordingly */
static void
update_orbit_newgen(GEN Vs, GEN seen, GEN orb, long *orblen, GEN gens)
{
  GEN g = gel(gens,1);
  long n = lg(g)-1, i, j, numnewelts=0;
  long *newelts = NULL;
  pari_sp av = avma;
  GEN v = cgetg(n+1, t_VECSMALL);
  for(i=1; i<lg(Vs); i++) {
    if (F2v_coeff(seen,i)) {
      ulong in_orb = F2v_coeff(orb, i);
      for(j=1; j<=n; j++) /* g*v */
	v[j] = zv_dotproduct(gel(g,j), gel(Vs,i));
      if ((j = vecvecsmall_search(Vs, v)) <= 0)
	pari_err(e_MISC, "g*v not found in update_orbit_newgen");
      if (F2v_coeff(orb,j)) {
	pari_err(e_MISC, "update_orbit_newgen: should not be already in orbit");
      }
      numnewelts++;
      newelts = push_long(in_orb ? j : -j);
    }
  }
  if (numnewelts == 0)
    pari_err(e_MISC, "nothing new in update_orbit_newgen");
  for(i=0; i<numnewelts; i++) {
    j = newelts[i];
    if (j > 0) {
      F2v_set(orb, j);
      (*orblen)++;
    } else {
      j = -j;
    }
    F2v_set(seen, j);
  }
  update_orbit_mainloop(newelts, numnewelts, Vs, seen, orb, orblen, gens, v);
  set_avma(av);
}

/* gel(Vs,i) is not in orbit under automorphism group, propagate this
   information to its orbit under the subgroup generated by gens */
static void
update_orbit_not(GEN Vs, GEN seen, GEN gens, long i)
{
  long n = lg(gel(Vs,1))-1;
  pari_sp av = avma;
  GEN v = cgetg(n+1, t_VECSMALL);
  F2v_set(seen, i);
  update_orbit_mainloop(push_long(-i), 1, Vs, seen, NULL, NULL, gens, v);
  set_avma(av);
}

static GEN
zm_transpose_to_ZM(GEN M)
{
  long i, j, lM=lg(M), rM;
  GEN res;
  if (lM == 1)
    return cgetg(1, t_MAT);
  rM = lgcols(M);
  res = cgetg(rM, t_MAT);
  for(i=1; i<rM; i++) {
    gel(res, i) = cgetg(lM, t_COL);
    for(j=1; j<lM; j++)
      gmael(res, i, j) = stoi(gel(M,j)[i]);
  }
  return res;
}

static GEN
gens2vec(GEN gens, long n) {
  long l=0;
  GEN g, res;
  for(g=gens; lg(g)==3; g=gel(g,2))
    l++;
  if (l == 0)
    return mkvec(matid(n));
  res = cgetg(l+1, t_VEC);
  for(l=1, g=gens; lg(g)==3; g=gel(g,2), l++)
    gel(res, l) = zm_transpose_to_ZM(gel(g,1));
  return res;
}

static long
guess_depth(qfautors_ctx *fqc)
{
  long d;
  pari_sp av = avma;
  GEN pfp = vecsmall_prod(fqc->fp);
  if (cmpsi(100000, pfp) < 0)
    d = 1;
  else
    d = 0;
  set_avma(av);
  return d;
}

GEN
qfautors_sub(GEN gram, GEN M, GEN U, GEN c, GEN d, GEN b, GEN mu, GEN e,
	     GEN lambda, GEN tlob, GEN rs_pre, GEN rspU, long depth)
{
  eqfminim_ctx ctx;
  qfautors_ctx fqc;
  GEN B, g, spwg, gens, orblens, res;
  long i, j, n=lg(gram)-1;
  pari_sp av = avma;

  if (typ(U) != t_VECSMALL)
    pari_err(e_MISC, "U should be a permutation");
  eqfminim_init(&ctx, itos(M), U, c, d, b, mu, e, lambda, tlob,
		(void *) &fqc, &append_eqfminim_qfautors);
  init_qfautors_ctx(&fqc, gram, rs_pre, rspU);
  eqfminim_run(&ctx, 1);
  eqfminim_free(&ctx);
  /* basis of sums of vectors having same invariant */
  B = zm_basis_trunc(gram, fqc.Vsums);
  refine_inv(&fqc, B);
  qfautors_fingerprint(&fqc);

  if (depth < 0)
    depth = guess_depth(&fqc);
  qfautors_vecsums(&fqc, depth);

  g = cgetg(n+1, t_VEC);
  spwg = cgetg(n+1, t_VEC);
  for(i=1; i<=n; i++) {
    gel(g,i) = zero_zv(n);
    gel(g,i)[i] = 1;
    gel(spwg,i) = my_vecsmall_copy(gel(fqc.gram,i));
  }
  orblens = cgetg(n+1, t_VECSMALL);
  gens = cgetg(1, t_VEC); /* nil */
  for(j=n; j>=1; j--) {
    long pj=fqc.per[j], k;
    GEN seen, orb;
    pari_sp subav = avma;
    GEN poss = qfautors_poss(&fqc, j, g, spwg);
    if (poss == NULL)
      pari_err(e_MISC, "impossible fingerprint in qfautors_sub");
    if ((k = vecvecsmall_search(poss, gel(g, pj))) <= 0)
      pari_err(e_MISC, "basis vector not in list in qfautors_sub");
    seen = F2v_ei(lg(poss)-1, k);
    orb = F2v_ei(lg(poss)-1, k);
    orblens[j] = 1;
    for(i=1; i<lg(poss); i++) {
      int works = 1;
      if (F2v_coeff(seen, i))
	continue;
      memcpy(gel(g,pj)+1, gel(poss,i)+1, n*sizeof(long));
      if (j < n) {
	for(k=1; k<=n; k++)
	  gel(spwg,pj)[k] = zv_dotproduct(gel(fqc.gram,k), gel(poss,i));
	if (((fqc.depth > 0) && qfautors_ck_vecsums(&fqc, j, g, spwg))
	    || !qfautors_search(&fqc, j+1, g, spwg))
	  works = 0;
      }
      if (works) {
	gens = mkvec2(zm_transpose(g), gens); /* cons */
	update_orbit_newgen(poss, seen, orb, orblens+j, gens);
      } else {
	update_orbit_not(poss, seen, gens, i);
      }
    }
    gens = gerepilecopy(subav, gens);
  }

  /* [order, gens, per, orblens, fp] */
  res = cgetg(6, t_VEC);
  orblens = zv_to_ZV(orblens);
  gel(res, 4) = orblens;
  gel(res, 1) = ZV_prod(orblens);
  gel(res, 3) = my_vecsmall_copy(fqc.per);
  gel(res, 2) = gens2vec(gens, n);
  gel(res, 5) = zv_to_ZV(fqc.fp);
  return gerepileupto(av, res);
}

/* end qfautors with vector sums */


/* for good_bases.gp */

static long
qfeval_zm_zv(GEN gram, GEN v)
{
  long n=lg(v)-1, res = gel(gram,1)[1]*v[1]*v[1];
  for(long i=2; i<=n; i++) {
    GEN c = gel(gram,i);
    long s = c[1]*v[1];
    for(long j=2; j<i; j++)
      s += c[j]*v[j];
    s = 2*s + c[i]*v[i];
    res += s*v[i];
  }
  return res;
}

GEN
cpct_latt_helper(GEN T, GEN svs)
{
  pari_sp av=avma;
  long maxd=0, ind=0, len=lg(svs)-1;
  if (lg(T)<=1)
    return 0;
  T = ZM_to_zm(T);
  for(long i=1; i<=len; i++) {
    long d;
    d = qfeval_zm_zv(T, gel(svs,i));
    if (d>0 && (maxd==0 || d<maxd)) {
      ind = i;
      maxd = d;
    }
  }
  set_avma(av);
  return mkvecsmall2(ind, maxd);
}
