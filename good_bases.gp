\\ find good bases (short vectors) of lattices

\\ random approach
reduce(q, B, t=10000) = {
  my(svs=eqfminim(q,B), M=matconcat(svs), n=#M, d=#q);
  if(n==0,
    return(0));
  if(matrank(M*Mod(1,2))!=#q || matdet(mathnfmod(M,matdetint(M)))!=1,
    return(0));
  my(W=matconcat(svs[1..B-1]), m=#W, kstart);
  if (m==0, kstart=d, kstart=1);
  for(k=kstart, d,
    for(i=1, t,
      my(N,D);
      N = Mat(vector(d,i,if(i>k,W[,random(m)+1],M[,random(n)+1])));
      if(matdet(N)==1,return(N))));
};

good_basis_rand(gram, target=4, even=is_even(gram), verb=0)={
  my(P,L,m);
  P = qflllgram(gram);
  L = qfeval(gram,P);
  m = maxdiag(L);
  if(m<=target,return([P,m]));
  if(verb, print("qflllgram max : ",m) );
  forstep(i=2, m-if(even,2,1), if(even,2,1),
    my(Q=reduce(gram,i));
    if(Q, 
      if(verb, print("reduce max ",i) ); 
      return([Q,i])
    );
  );
  [P,m]
};

\\ now we introduce some determinism

install("cpct_latt_helper","GG","cpct_latt_helper","./eqfminim.so");

compact_latt(gram, svs, M) = {
  my(n=#gram, B=Mat(), T=gram, d=1, bound=long_max_abs());
  for(i=1, n,
    my(ind, newd);
    if(d*M>bound, break);
    [ind, newd] = cpct_latt_helper(T,svs);
    if(ind,
      B = matconcat([B, Col(svs[ind])]);
      T = (newd*T - slf(Vec(svs[ind])*T))/d;
      d = newd;
    ,
      break;
    );
  );
  B
};

\\ paranoia
check_upper_triang(G) = {
  my(ncols,nrows);
  [nrows, ncols] = matsize(G);
  if(nrows!=ncols, error("check_upper_triang: not square"));
  for(i=2, nrows,
    for(j=1, i-1,
      if(G[i,j], error("not upper triangular"));
    );
  );
};

partial_lll_red(gram, k) = {
  my(n=#gram, R, q, GS, B);
  B = matid(n);
  R = qfgaussred(gram);
  check_upper_triang(R);
  q = vector(n, i, R[i,i]);
  for(i=1, n, R[i,i]=1); /* cols of R^-1 give Gram-Schmidt orth. */
  GS = R^-1;
  for(i=n-k+1, n,
    forstep(j=i-1, 1, -1,
      B[j,i] -= round(qfeval(gram, B[,i], GS[,j]) / q[j]);
    );
  );
  B;
};

/*
 assume that LLL has already been done, and is deemed not good enough
 relies on tqfminim.gp
 */
good_basis_hybrid(gram, target=4, even=is_even(gram), mult=20, codim=-1) = {
  my(Q, Qsmall, Qbig, Qwn, m, B, H, n=#gram, it, sB);
  Q = eqfminim(gram,target,1,0);
  if(codim==-1,
    my(fatQ=matconcat([Col(c) | c<-concat(Q)]));
    codim = #matsnf(fatQ,4);
    if(codim>1, return(good_basis_rand(gram, target, even)[1]));
  );
  Qsmall = concat(Q[1..target-1]);
  Qbig = Q[target];
  if(#Qbig==0,
    if(#Q==0, error("no short vectors"));
    return(good_basis_hybrid(gram, if(even,target-2,target-1), even, mult, codim));
  );
  B = [];
  sB = [2];
  while(#B<n-codim || (codim && sB!=[0]) || (codim==0 && sB!=[]),
    B = compact_latt(gram, concat(Qsmall, vector(mult*n,i,Qbig[random(#Qbig)+1])), target);
    sB = matsnf(B,4);
    if(codim && #B==n && #sB==1,
      my(succ);
      forstep(i=n, 1, -1,
        sB = matsnf(B[,^i],4);
        if(sB==[0],
          succ = 1;
          B = B[,^i];
          break;);
      );
      if(!succ, B=[]; sB=[2]);
    );
    if(it>=30,
      if(codim==0, return(good_basis_hybrid(gram, target, even, mult, 1)));
      return(good_basis_rand(gram, target, even)[1]));
    it++;
  );
  if(codim,
    my(u,v,d,newgram,S,x,C);
    [u,v,d] = matsnf(B,1);
    B = matconcat([B,u^-1*vector(n,i,i==1)~]);
    B = B*partial_lll_red(qfeval(gram,B), 1);
    x = short_vector_fixed_coord(qfeval(gram,B), codim, [1],
                                 target+if(even,2,1), even);
    C = matid(n);
    for(i=1, n-1, C[i,n] = x[i]);
    B = B*C;
  );
  if(!is_unimod(B), error("good_basis_hybrid failed"));
  B
};
