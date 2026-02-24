install("long_max_abs","","long_max_abs","./eqfminim.so");
install("eqfminim_count_sub","GGGGGGGG","eqfminim_count_sub","./eqfminim.so");
install("eqfminim_sub","GGGGGGGGGL","eqfminim_sub","./eqfminim.so");
install("inv_rs","GGL","inv_rs","./eqfminim.so");
install("qfautors_sub","GGGGGGGGGGGGD-1,L,","qfautors_sub","./eqfminim.so");
install("fast_marked_HBV_sub","uGGGGGGGGGGGG","fast_marked_HBV_sub","./eqfminim.so");

slf(l) = l~*l;

\\ like qfgaussred except that at each step of the induction
\\ we select the shortest basis vector, and we compute denominators
perqfgaussred_denom(gram) = {
  my(mi=1, m=gram[1,1], n=#gram, subgram, lin, per, subper, subres, subd, d);
  if(n==1, return([Vecsmall([mi]), [[m, []]], [denominator(m), 1]]));
  for(i=2, n,
    if(gram[i,i]<m,
      m = gram[i,i];
      mi = i;
    );
  );
  d = lcm(concat(vector(n, i, vector(i, j, denominator(gram[i,j])))));
  subgram = gram[^mi,^mi];
  lin = gram[mi,^mi];
  subgram -= slf(lin)/m;
  lin /= m;
  [subper, subres, subd] = perqfgaussred_denom(subgram);
  per = Vecsmall(0, #subper+1);
  per[1] = mi;
  for(i=1, #subper,
    my(s=subper[i]);
    if(s<mi, per[i+1]=s, per[i+1]=s+1);
  );
  [per, concat([[m, vecextract(lin, subper)]], subres), concat([d], subd)];
};

prepare_eqfminim(gram, M, dolll=1) = {
  my(n=#gram, T, U, per, R, c, d, b, mu, e, lambda, tlob, dgi, ub, ubx, tlll, tpqgr, trem);
  tlll = getabstime();
  if(dolll,
    U = qflllgram(gram);
    gram = qfeval(gram, U);
  );
  tlll = getabstime() - tlll;
  tpqgr = getabstime();
  [per, R, c] = perqfgaussred_denom(gram);
  if(dolll,
    U = matconcat([U[,i] | i<-per]); \\ Cholesky(qfeval(gram,U))=R
  ,
    U = per;
  );
  tpqgr = getabstime() - tpqgr;
  trem = getabstime();
  d = vector(n, i, lcm(c[i], c[i+1]));
  b = vector(n, i, lcm([denominator(qij) | qij <- R[i][2]]));
  mu = vector(n, i, d[i]*R[i][1]/b[i]^2);
  e = vector(n, i, vector(n-i, j, b[i]*R[i][2][j]));
  lambda = vector(n, i, c[i]*R[i][1]);
  tlob = vector(n, i, 2*lambda[i]/b[i]);
  trem = getabstime() - trem;
  if(M<=0, error("what are you doing!?"));
  dgi = diag(gram^-1);
  ub = max(M*vecmax(d), 2*vecmax(lambda));
  ub = max(ub, max(vecmax(b), vecmax(tlob)));
  ub = max(ub, vecmax(mu));
  ubx = vector(n, i, sqrtint(M*dgi[i]));
  ub = max(ub, 1+vecmax(ubx));
  if(n>1,
    ub = max(ub, vecmax(vector(n-1, i, vecmax(e[i]))));
    ub = max(ub, vecmax(vector(n-1, i, sum(j=i+1, n, abs(e[i][j-i])*ubx[j]))));
  );
  ub = max(ub, vecmax(vector(n, i, mu[i]*(b[i]-1)^2)));
  ub = max(ub, vecmax(vector(n, i, sqrtint(4*lambda[i]*c[i]*M)+lambda[i])));
  if(ub>long_max_abs(), error("cannot guarantee that eqfminim will perform correctly"));
  [U, R, c, d, b, mu, e, lambda, tlob, tlll, tpqgr, trem, ub];
};

/*
  count the # of x in Z^n satisfying qfeval(gram, x) <= M
  gram must have integral entries, M must be an integer
*/
count_eqfminim(gram, M, dolll=1) = {
  my(n=#gram, U, R, c, d, b, mu, e, lambda, tlob);
  [U, R, c, d, b, mu, e, lambda, tlob] =
      prepare_eqfminim(gram, M, dolll)[1..10];
  eqfminim_count_sub(M, c, d, b, mu, e, lambda, tlob);
};

eqfminim(gram, M, small=0, dolll=1) = {
  my(n=#gram, U, R, c, d, b, mu, e, lambda, tlob);
  [U, R, c, d, b, mu, e, lambda, tlob] =
      prepare_eqfminim(gram, M, dolll)[1..10];
  eqfminim_sub(M, U, c, d, b, mu, e, lambda, tlob, small);
};

\\ the following is used in rs_pre, used in qfautors
ADE2int(t) = {
  if(t=="A", 0,
     t=="D", 1,
             2);
};

\\ precompute datum to quickly compute invariants wrt
\\ based root system, see inv_rs in eqfminim.c
rs_pre(gram, rs) = {
  my(isocla, V, k);
  isocla = [Vecsmall([ADE2int(iso[1]), #iso[2][1], #iso[2]]) | iso <- rs];
  V = vector(sum(i=1, #rs, #rs[i][2][1]*#rs[i][2]));
  foreach(rs, iso,
    foreach(iso[2], L,
      foreach(L, v,
        k++;
        V[k] = Vecsmall(v~*gram);
      );
    );
  );
  [isocla, V];
};

\\ assume that gram is already in a good basis
qfautors(gram, depth=-1) = {
  my(U, R, c, d, b, mu, e, lambda, tlob, M, rsp, rspU, Rplus);
  M = maxdiag(gram);
  [U, R, c, d, b, mu, e, lambda, tlob] =
      prepare_eqfminim(gram, max(M,2), 0)[1..10];
  Rplus = eqfminim_sub(2, U, c, d, b, mu, e, lambda, tlob, 0)[2];
  rsp = rs_pre(gram, root_system_vec_Rplus(gram,Rplus));
  rspU = [rsp[1], [Vecsmall([v[i] | i<-U]) | v<-rsp[2]]];
  qfautors_sub(gram, M, U, c, d, b, mu, e, lambda, tlob, rsp, rspU, depth);
};

fast_marked_HBV(gram, mark, M=3, verb=0, dolll=1) = {
  my(B, n=#gram, U, R, c, d, b, mu, e, lambda, tlob);
  if(dolll,
    my(B);
    B = qflllgram(gram);
    gram = qfeval(gram, B);
    if(#mark,
      my(Binv=B^-1);
      mark = [Binv*v | v<-mark];
    );
  );
  /* afterthought: should have allowed linear forms instead of vectors */
  if(#mark,
    mark = [Vecsmall(gram*v) | v<-mark];
  );
  [U, R, c, d, b, mu, e, lambda, tlob] = prepare_eqfminim(gram, M, 0)[1..10];
  fast_marked_HBV_sub(gram, M, U, c, d, b, mu, e, lambda, tlob, mark, verb);
};
