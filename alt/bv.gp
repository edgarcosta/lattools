\\
\\ BV lattice invariant -- PARI/GP implementation
\\ Portable output format matching bv.py (Sage) and bv.m (Magma).
\\
\\ Uses PARI's qfminim convention: v^T * gram * v <= d.
\\
\\ Load: \r alt/bv.gp
\\

install("FpM_mul","GGG");

graph(gram, d) = {
  my(S);
  S = qfminim(gram, d)[3];
  if(#S == 0, return(0));
  lift(FpM_mul(S~*gram, S, 2));
};

\\ sorted (value, count) pairs for a vector
col_sig(v) = {
  my(s = vecsort(v), result = List(), current, count);
  if(#s == 0, return([]));
  current = s[1]; count = 1;
  for(i = 2, #s,
    if(s[i] == current, count++,
      listput(result, [current, count]);
      current = s[i]; count = 1;
    );
  );
  listput(result, [current, count]);
  Vec(result);
};

\\ BV invariant (output format: [[sig, count], ...])
BV(gram, d) = {
  my(G = graph(gram, d));
  if(G === 0, return([]));
  my(m = #G, p, S, cols, result, current, count);
  p = nextprime(m+1); \\ smallest prime > m, matching Sage next_prime(m)
  S = lift(FpM_mul(G, G, p));
  cols = vector(m, j, col_sig(Vec(S[,j])));
  cols = vecsort(cols);
  result = List();
  current = cols[1]; count = 1;
  for(j = 2, m,
    if(cols[j] == current, count++,
      listput(result, [current, count]);
      current = cols[j]; count = 1;
    );
  );
  listput(result, [current, count]);
  Vec(result);
};

\\ Portable polynomial hash (matches bv.py HBV_poly)
HBV_poly(bv) = {
  my(M = 2^61 - 1, h = 0, sig, cnt);
  for(i = 1, #bv,
    sig = bv[i][1];
    cnt = bv[i][2];
    for(j = 1, #sig,
      h = (h * 1000003 + sig[j][1]) % M;
      h = (h * 1000003 + sig[j][2]) % M;
    );
    h = (h * 1000003 + cnt) % M;
  );
  h;
};

\\ Portable XOR-multiply hash (matches bv.py HBV_xor)
HBV_xor(bv) = {
  my(M = 2^64, MULT = 1111111111111111111, h = 13282407956253574712, sig, cnt);
  for(i = 1, #bv,
    sig = bv[i][1];
    cnt = bv[i][2];
    for(j = 1, #sig,
      h = (bitxor(h, sig[j][1]) * MULT) % M;
      h = (bitxor(h, sig[j][2]) * MULT) % M;
    );
    h = (bitxor(h, cnt) * MULT) % M;
  );
  h;
};

HBV(gram, d) = HBV_poly(BV(gram, d));
