#include <stdint.h>
#include <pari/pari.h>

/*
static uint32_t
popcnt_parity(uint32_t x)
{
  x ^= x>>16;
  x ^= x>>8;
  x ^= x>>4;
  x ^= x>>2;
  return (x^(x>>1))&((uint32_t) 1);
}
*/

static uint32_t
popcnt_parity(uint32_t x)
{
  return (__builtin_popcount(x))&((uint32_t) 1);
}

static uint32_t
matact(uint32_t *M, uint32_t x, int n)
{
  int i;
  uint32_t res=0;
  /*print_mat(M, n);
  pari_printf("* ");
  print_vec(x, n);*/
  for(i=0; i<n; i++)
    res |= popcnt_parity((*(M++))&x)<<i;
  /*pari_printf("= ");
    print_vec(res, n);*/
  return res;
}

static unsigned int
is_new(uint32_t x, uint32_t *seen)
{
  uint32_t a = x>>5;
  uint32_t b = ((uint32_t) 1)<<(x&31);
  if (seen[a]&b) return 0;
  seen[a] |= b;
  return 1;
}

static void
check_seen(uint32_t *seen, int n)
{
  size_t i;
  if (n < 5) {
    if (*seen != (1UL<<(1UL<<n))-1)
      pari_err(e_MISC, "not really finished");
    return;
  }
  for(i=0; i<(1ULL<<(n-5)); i++) {
    if (seen[i]!=~((uint32_t) 0))
      pari_err(e_MISC, "not really finished");
  }
}

/* assumes that all elements before x are already visited */
static uint32_t
find_next_after(uint32_t x, uint32_t *seen)
{
  uint32_t y;
  x >>= 5;
  while ((y = seen[x]) == ~((uint32_t) 0))
    x++;
  x <<= 5;
  while (y&1) {
    x++;
    y >>= 1;
  }
  seen[x>>5] |= ((uint32_t) 1)<<(x&31);
  return x;
}

static uint32_t *
red_gens_mod2(GEN G)
{
  uint32_t *res, *p;
  long l, n, i, j, k;
  if (typ(G)!=t_VEC || lg(G)<2 || typ(gel(G,1))!=t_MAT)
    pari_err(e_MISC, "invalid input");
  l = lg(G)-1;
  n = lg(gel(G,1))-1;
  if (n > 32)
    pari_err(e_MISC, "dimension > 32 not implemented");
  for(j=1; j<=l; j++) {
    if (lg(gel(G,j))!=n+1)
      pari_err(e_MISC, "invalid input");
    for(k=1; k<=n; k++) {
      if(lg(gmael(G,j,k))!=n+1)
	pari_err(e_MISC, "invalid input");
    }
  }
  res = pari_malloc(n*l*sizeof(uint32_t));
  p = res;
  for(i=1; i<=l; i++) {
    for(j=1; j<=n; j++) {
      *p = 0;
      for(k=1; k<=n; k++)
	*p |= ((uint32_t) mpodd(gmael3(G,i,k,j)))<<(k-1);
      p++;
    }
  }
  return res;
}

/*
  for each orbit, vecsmall [length, representative] (3 longs)
 */
GEN
orbmod2(GEN G)
{
  long i, ngens;
  int n;
  uint32_t *gens, *seen, *todo;
  uint32_t seen_cnt=1, next=0, x, y, orb_len=1, seen_cap;
  size_t todo_len=0;
  long res_len = 0;
  GEN res;
  long *p, *tmp_res;
  
  gens = red_gens_mod2(G);
  n = lg(gel(G,1))-1;
  ngens = lg(G)-1;
  seen_cap = 1ULL<<(n>=5 ? n-5 : 0);
  /* TODO: check for overflow */
  seen = pari_malloc(seen_cap*sizeof(uint32_t));
  for(x=0; x<seen_cap; x++)
    seen[x] = 0;
  todo = pari_malloc((1ULL<<n)*sizeof(uint32_t));
  tmp_res = pari_malloc(3*sizeof(long)*(1ULL<<n));
  seen[0] = 1;
  for(;;) {
    if (todo_len) {
      x = todo[todo_len-1];
      todo_len--;
      for(i=0; i<ngens; i++) {
	y = matact(gens+i*n, x, n);
	if (is_new(y, seen)) {
	  todo[todo_len++] = y;
	  seen_cnt++;
	  orb_len++;
	}
      }
    } else {
      tmp_res[3*res_len] = evaltyp(t_VECSMALL) | evallg(3);
      tmp_res[3*res_len+1] = orb_len;
      tmp_res[3*res_len+2] = next;
      res_len++;
      if (seen_cnt == (((uint32_t) 1)<<n)) {
	check_seen(seen, n);
	break;
      }
      next = find_next_after(next, seen);
      seen_cnt++;
      todo[0] = next;
      todo_len = 1;
      orb_len = 1;
    }
  }
  pari_free(seen);
  pari_free(todo);
  pari_free(gens);
  res = cgetg(res_len+1, t_VEC);
  p = new_chunk(3*res_len);
  memcpy(p, tmp_res, 3*sizeof(long)*res_len);
  pari_free(tmp_res);
  for(i=1; i<=res_len; i++)
    gel(res, i) = p+3*(i-1);
  return res;
}

/*
  in gp: fororbmod2(gens, V, code using V) where V is
  [olen, vector]
  install("fororbmod2", "vGVI", "fororbmod2", "./orbmod2.so");
 */
void
fororbmod2(GEN G, GEN code)
{
  long i, ngens;
  int n;
  uint32_t *gens, *seen, *todo;
  uint32_t seen_cnt=1, next=0, x, y, orb_len=1, seen_cap;
  size_t todo_len=0;
  pari_sp av;
  GEN pair;

  push_lex(gen_0, code);
  gens = red_gens_mod2(G);
  n = lg(gel(G,1))-1;
  ngens = lg(G)-1;
  seen_cap = 1ULL<<(n>=5 ? n-5 : 0);
  seen = pari_malloc(seen_cap*sizeof(uint32_t));
  for(x=0; x<seen_cap; x++)
    seen[x] = 0;
  todo = pari_malloc((1ULL<<n)*sizeof(uint32_t));
  seen[0] = 1;
  for(;;) {
    if (todo_len) {
      x = todo[todo_len-1];
      todo_len--;
      for(i=0; i<ngens; i++) {
	y = matact(gens+i*n, x, n);
	if (is_new(y, seen)) {
	  todo[todo_len++] = y;
	  seen_cnt++;
	  orb_len++;
	}
      }
    } else {
      av = avma;
      pair = cgetg(3, t_VEC);
      gel(pair, 1) = stoi((long) orb_len);
      gel(pair, 2) = cgetg(n+1, t_VEC);
      for(i=1; i<=n; i++)
	gmael(pair, 2, i) = ((next>>(i-1))&((uint32_t) 1)) ? gen_1 : gen_0;
      i = gp_evalvoid((void *) code, pair);
      set_avma(av);
      if (i)
	break;
      if (seen_cnt == (((uint32_t) 1)<<n)) {
	check_seen(seen, n);
	break;
      }
      next = find_next_after(next, seen);
      seen_cnt++;
      todo[0] = next;
      todo_len = 1;
      orb_len = 1;
    }
  }
  pari_free(seen);
  pari_free(todo);
  pari_free(gens);
  pop_lex(1);
}

/*
  affine version
 */
static int
red_gens_mod2_aff(uint32_t **genslin, uint32_t **genstrans, GEN G)
{
  uint32_t *p, *q;
  long l, n, i, j, k;
  if (typ(G)!=t_VEC || lg(G)<2 || typ(gel(G,1))!=t_VEC || typ(gmael(G,1,1))!=t_MAT)
    pari_err(e_MISC, "invalid input");
  l = lg(G)-1;
  n = lg(gmael(G,1,1))-1;
  if (n > 32)
    pari_err(e_MISC, "dimension > 32 not implemented");
  for(j=1; j<=l; j++) {
    GEN Gj=gel(G,j);
    if (lg(Gj)!=3)
      pari_err(e_MISC, "invalid input");
    if (typ(gel(Gj,1))!=t_MAT || lg(gel(Gj,1))!=n+1)
      pari_err(e_MISC, "invalid input");
    for(k=1; k<=n; k++) {
      if(lg(gmael(Gj,1,k))!=n+1)
	pari_err(e_MISC, "invalid input");
    }
    if ((typ(gel(Gj,2))!=t_VEC && typ(gel(Gj,2))!=t_COL) || lg(gel(Gj,2))!=n+1)
      pari_err(e_MISC, "invalid input");
  }
  *genslin = (n>0) ? pari_malloc(n*l*sizeof(uint32_t)) : NULL;
  *genstrans = pari_malloc(l*sizeof(uint32_t));
  p = *genslin;
  q = *genstrans;
  for(i=1; i<=l; i++, q++) {
    GEN Gilin = gmael(G,i,1);
    GEN Gitrans = gmael(G,i,2);
    *q = 0;
    for(j=1; j<=n; j++, p++) {
      *q |= ((uint32_t) mpodd(gel(Gitrans,j)))<<(j-1);
      *p = 0;
      for(k=1; k<=n; k++)
	*p |= ((uint32_t) mpodd(gmael2(Gilin,k,j)))<<(k-1);
    }
  }
  return n;
}

void
fororbmod2aff(GEN G, GEN code)
{
  long i, ngens;
  int n;
  uint32_t *genslin, *genstrans, *seen, *todo;
  uint32_t seen_cnt=1, next=0, x, y, orb_len=1, seen_cap;
  size_t todo_len=1;
  pari_sp av;
  GEN pair;

  push_lex(gen_0, code);
  n = red_gens_mod2_aff(&genslin, &genstrans, G);
  ngens = lg(G)-1;
  seen_cap = 1ULL<<(n>=5 ? n-5 : 0);
  /* TODO: check for overflow */
  seen = pari_malloc(seen_cap*sizeof(uint32_t));
  for(x=0; x<seen_cap; x++)
    seen[x] = 0;
  todo = pari_malloc((1ULL<<n)*sizeof(uint32_t));
  todo[0] = 0;
  seen[0] = 1;
  for(;;) {
    if (todo_len) {
      x = todo[todo_len-1];
      todo_len--;
      for(i=0; i<ngens; i++) {
	y = matact(genslin+i*n, x, n) ^ genstrans[i];
	if (is_new(y, seen)) {
	  todo[todo_len++] = y;
	  seen_cnt++;
	  orb_len++;
	}
      }
    } else {
      av = avma;
      pair = cgetg(3, t_VEC);
      gel(pair, 1) = stoi((long) orb_len);
      gel(pair, 2) = cgetg(n+1, t_VEC);
      for(i=1; i<=n; i++)
	gmael(pair, 2, i) = ((next>>(i-1))&((uint32_t) 1)) ? gen_1 : gen_0;
      i = gp_evalvoid((void *) code, pair);
      set_avma(av);
      if (i)
	break;
      if (seen_cnt == (((uint32_t) 1)<<n)) {
	check_seen(seen, n);
	break;
      }
      next = find_next_after(next, seen);
      seen_cnt++;
      todo[0] = next;
      todo_len = 1;
      orb_len = 1;
    }
  }
  pari_free(seen);
  pari_free(todo);
  if (n>0)
    pari_free(genslin);
  pari_free(genstrans);
  pop_lex(1);
}
