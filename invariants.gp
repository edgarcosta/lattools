\\
\\ this file contains all the lattice invariants used in hdiscp
\\
\\		such as
\\
\\  BV1(gram,p), BV2(gram,p), BV3(gram,p) and BVhdiscp(gram)
\\ 
\\
\\ make_uni_from_det3or6, make_uni_from_det5or10, make_uni_from_det7or14
\\ fast_inv_even_det3, fast_inv_even_det5, fast_inv_even_det7
\\ make_det2_from_det6, make_det2_from_det10, make_det2_from_det14
\\ make_det3_from_det6, make_det5_from_det10, make_det7_from_det14
\\ super_fast_inv_even_det6, super_fast_inv_even_det10, super_fast_inv_even_det14
\\ absBVdual
\\
\\



\\ make unimodular lattices from detp or 2p, p=3,5,7

make_uni_from_det3or6(L, fl=0)={
  my(n=#L, d=matdet(L));
  if(n%4==0, return());
  my(s, w, M, P);
  s = (d*L^-1)%d;
  if(n%2==0,
    for(i=1, n,
      if(s[,i]%3, w=s[,i]/3; break));
     if(!w, error("mistake"));
     if(n%8==2,
       M = concatgram( [L, matid(1)*3] );
       w = concat(w, [1/3]~);
     , \\ n%8==6
       P = [2, 1; 1, 2];
       M = concatgram([L, P]);
       w = concat(w, [2/3, -1/3]~);
     );
  , \\ n%2==1
    for(i=1, n,
      if(s[,i]%2 && s[,i]%3, w = s[,i]/6; break)); 
    if(!w,
      my(a,b);
      for(i=1, n,
        if(s[,i]%3, a=s[,i]; break));
      for(i=1, n,
        if(s[,i]%2, b=s[,i]; break));
      if(!a || !b, error("mistake"));
      w = a/3 - b/2; 
    );
    if(n%8==1 || n%8==3,
      M = concatgram( [L, Mat(2), Mat(3)] );
      w = concat(w, [1/2, 1/3]~);
    , n%8==5,
      M = concatgram( [L, Mat(6)] );
      w = concat(w, [1/6]~);
    , \\ n%8==7
      M = concatgram([L, [2,-1;-1,2], Mat(2)]);
      w = concat(w, [2/3, 1/3, 1/2]~);
    );
  );  
  my(basis, m=#M);
  basis = mathnf(d*matconcat([matid(m),w]))/d;
  if(fl,
    my(mark = matrix(m, m-n, i, j, i==n+j));
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis))
};

make_uni_from_det5or10(L, fl=0, alt=0)={
  my(n=#L, d=matdet(L) );
  if(n%4==2, return() );
  my(s, w, M, P, valres, e);
  s = (d*L^-1)%d;
  if(n%2==0,
     for(i=1, n,
       if( s[,i]%5, w=s[,i]/5; break)
     );
     if(!w, error("mistake"));
     valres=(5*qfeval(L,w))%5;
     if(n%8==4,
       M = concatgram( [L, Mat(5)] );
       if(valres==4, e=[1/5]~,
          valres==1, e=[2/5]~, 
          error("mistake")
       );
       w = concat(w, e),
       n%8==0,
       P = [2, 1; 1, 3];
       M = concatgram( [L, P] );
       if(valres==2, e=[3/5, -1/5]~,
          valres==3, e=[-1/5, 2/5]~, 
          error("mistake")
       );
       w = concat(w, e)
     ),
    n%2==1,
    for(i=1, n,
      if(s[,i]%2 && s[,i]%5, w = s[,i]/10; break)
    ); 
    if(!w,
      my(a,b);
      for(i=1, n,
        if( s[,i]%5, a=s[,i]; break)
      );
      for(i=1, n,
        if( s[,i]%2, b=s[,i]; break)
      );
      if(!a || !b, error("mistake"));
      w = a/5 - b/2; 
    );
    valres=(10*qfeval(L,w))%10;
    if(
        n%8==1,
      M = concatgram( [L, Mat(10)] );
      if(valres==9, e=[1/10]~,
         valres==1, e=[3/10]~, 
         error("mistake")
      );
      w = concat(w, e),
        n%8==3 || n%8==5,
      M = concatgram( [L, Mat(2), Mat(5)] );
      if(valres==7, e=[1/2, 2/5]~,
         valres==3, e=[1/2, 1/5]~, 
         error("mistake")
      );
      w = concat(w, e), 
        n%8==7 && alt==0,
      M = concatgram( [L, Mat(2), [2,1;1,3] ] );
      if(valres==1, e=[1/2, -1/5, 2/5]~,
         valres==9, e=[1/2, 3/5, -1/5]~, 
         error("mistake")
      );
      w = concat(w, e),
        n%8==7 && alt,
      M = concatgram( [L, Mat(10) ] );
      if(valres==9, e=[1/10]~,
         valres==1, e=[3/10]~, 
         error("mistake")
      );
      w = concat(w, e)
    );
  );  
  my(basis, m=#M);
  basis = mathnf(d*matconcat([matid(m),w]))/d;
  if(fl,
    my(mark = matrix(m, m-n, i, j, i==n+j) );
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis)
  )
};

make_uni_from_det7or14(L, fl=0)={
  my(n=#L, d=matdet(L) );
  if(n%4==0, return() );
  my(s, w, M, P, valres, e);
  s = (d*L^-1)%d;
  if(n%2==0,
     for(i=1, n,
       if( s[,i]%7, w=s[,i]/7; break)
     );
     if(!w, error("mistake"));
     valres=(7*qfeval(L,w))%7;
     if(n%8==2,
       M = concatgram( [L, [2, 1, 1; 1, 2, 1; 1, 1, 3]] );
       if(valres==4, e=[-1/7, -1/7, 3/7]~,
          valres==2, e=2*[-1/7, -1/7, 3/7]~, 
	  valres==1, e=3*[-1/7, -1/7, 3/7]~,
          error("mistake")
       );
       w = concat(w, e),
       n%8==6,
       M = concatgram( [L, Mat(7)] );
       if(valres==6, e=[1/7]~,
	  valres==3, e=[2/7]~,
          valres==5, e=[3/7]~, 
          error("mistake")
       );
       w = concat(w, e)
     ),
    n%2==1,
    for(i=1, n,
      if(s[,i]%2 && s[,i]%7, w = s[,i]/14; break)
    ); 
    if(!w,
      my(a,b);
      for(i=1, n,
        if( s[,i]%7, a=s[,i]; break)
      );
      for(i=1, n,
        if( s[,i]%2, b=s[,i]; break)
      );
      if(!a || !b, error("mistake"));
      w = a/7 - b/2; 
    );
    valres=(14*qfeval(L,w))%14;
    if(
        n%8==1 || n%8==3,
      M = concatgram( [L, Mat(2), [2, 1, 1; 1, 2, 1; 1, 1, 3] ] );
      if(
	 valres==11, e=[1/2, 5/7, -2/7, -1/7]~,
	 valres==1, e=3*[1/2, 5/7, -2/7, -1/7]~,
         valres==9, e=5*[1/2, 5/7, -2/7, -1/7]~, 
         error("mistake")
      );
      w = concat(w, e),
        n%8==5,
      M = concatgram( [L, Mat(14)] );
      if(valres==13, e=[1/14]~,
         valres==5, e=[3/14]~,
	 valres==3, e=[5/14]~, 
         error("mistake")
      );
      w = concat(w, e), 
        n%8==7,
      M = concatgram( [L, Mat(2), Mat(7) ] );
      if(valres==5, e=[1/2, 1/7]~,
	 valres==3, e=3*[1/2, 1/7]~,
         valres==13, e=5*[1/2, 1/7]~, 
         error("mistake")
      );
      w = concat(w, e)
    );
  );  
  my(basis, m=#M);
  basis = mathnf(d*matconcat([matid(m),w]))/d;
  if(fl,
    my(mark = matrix(m, m-n, i, j, i==n+j) );
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis)
  )
};


\\
\\ corresponding marked invariants BV1
\\

fast_inv_even_det3(gram) = {
  my(uni, mark);
  [uni, mark] = make_uni_from_det3or6(gram, 1);
  fast_marked_HBV(uni, mark);
};


fast_inv_even_det5(gram,alt=0) = {
  my(uni, mark);
  [uni, mark] = make_uni_from_det5or10(gram, 1,alt);
  fast_marked_HBV(uni, mark);
};

fast_inv_even_det7(gram) = {
  my(uni, mark);
  [uni, mark] = make_uni_from_det7or14(gram, 1);
  fast_marked_HBV(uni, mark);
};

BV1(gram,p)={
 if(p==3, fast_inv_even_det3(gram),
    p==5, fast_inv_even_det5(gram),
    p==7, fast_inv_even_det7(gram)
 );
};

\\
\\ make det 2 lattices from det 2p, p=3,5,7
\\

make_det2_from_det6(L, fl=0)={
  my(n=#L, d=matdet(L));
  if(n%4==2, return());
  my(s, w, M, P);
  s = (d*L^-1)%d;
  for(i=1, n,
    if(s[,i]%3, w=s[,i]/3; break)
  );
  if(!w, error("mistake"));
  if(n%8==1 || n%8==3,
    M = concatgram( [L, Mat(3)] );
    w = concat(w, [1/3]~);
  , n%8==5 || n%8==7,
    M = concatgram([L, [2,-1;-1,2] ]);
    w = concat(w, [2/3, 1/3]~);
  ); 
  my(basis, m=#M);
  basis = mathnf(d*matconcat([matid(m),w]))/d;
  if(fl,
    my(mark = matrix(m, m-n, i, j, i==n+j));
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis)
  )
};


make_det2_from_det10(L, fl=0,alt=0)={
  my(n=#L, d=matdet(L) );
  if(n%2==0, return() );
  my(s, w, M, P, valres, e);
  s = (d*L^-1)%d;
  for(i=1, n,
    if(s[,i]%5, w = s[,i]/5; break)
  ); 
  if(!w, error("mistake") );
  valres=(5*qfeval(L,w))%5;
  if(
      n%8==3 || n%8==5,
    M = concatgram( [L, Mat(5)] );
    if(valres==1, e=[2/5]~,
       valres==4, e=[1/5]~, 
       error("mistake")
    );
    w = concat(w, e), 
      n%8==1 || n%8==7 || alt==0,
    M = concatgram( [L, [2,1;1,3] ] );
    if(valres==2, e=[3/5, -1/5]~,
       valres==3, e=2*[3/5, -1/5]~, 
       error("mistake")
    );
    w = concat(w, e),
      n%8==1 || n%8==7 || alt,
    M = concatgram( [L, [2, -1, 1, 1, 1, 1, 1; -1, 2, 0, -1, 0, -1, 0; 1, 0, 2, 1, 1, 1, 0; 1, -1, 1, 2, 0, 1, 0; 1, 0, 1, 0, 2, 1, 0; 1, -1, 1, 1, 1, 2, 0; 1, 0, 0, 0, 0, 0, 3] ] );
    if(valres==2, e=[3/5, 4/5, -2/5, -2/5, -4/5, 7/5, -1/5]~,
       valres==3, e=2*[3/5, 4/5, -2/5, -2/5, -4/5, 7/5, -1/5]~, 
       error("mistake")
    );
    w = concat(w, e)
  );  
  my(basis, m=#M);
  basis = mathnf(d*matconcat([matid(m),w]))/d;
  if(fl,
    my(mark = matrix(m, m-n, i, j, i==n+j) );
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis)
  )
};



make_det2_from_det14(L, fl=0)={
  my(n=#L, d=matdet(L) );
  if(n%2==0, return() );
  my(s, w, M, P, valres, e);
  s = (d*L^-1)%d;
  for(i=1, n,
    if(s[,i]%7, w = s[,i]/7; break)
  ); 
  if(!w, error("mistake") );
  valres=(7*qfeval(L,w))%7;
  if(
      n%8==1 || n%8==3,
    M = concatgram( [L, [2, 1, 1; 1, 2, 1; 1, 1, 3] ] );
    if(valres==2, e=[5/7, -2/7, -1/7]~,
       valres==1, e=2*[5/7, -2/7, -1/7]~,
       valres==4, e=3*[5/7, -2/7, -1/7]~, 
       error("mistake")
    );
    w = concat(w, e),
      n%8==5 || n%8==7,
    M = concatgram( [L, Mat(7)] );
    if(valres==6, e=[1/7]~,
       valres==3, e=[2/7]~,
       valres==5, e=[3/7]~, 
       error("mistake")
    );
    w = concat(w, e), 
  );  
  my(basis, m=#M);
  basis = mathnf(d*matconcat([matid(m),w]))/d;
  if(fl,
    my(mark = matrix(m, m-n, i, j, i==n+j) );
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis)
  )
};


\\
\\ corresponding marked invariants BV2
\\


super_fast_inv_even_det6(gram,alt=0) = {
  my(uni, mark);
  if(alt==0,
    [uni, mark] = make_det2_from_det6(gram, 1),
     alt,
    [uni, mark] = make_det3_from_det6(gram, 1)
  );
  fast_marked_HBV(uni, mark);
};

super_fast_inv_even_det10(gram,alt1=0,alt2=0) = {
  my(uni, mark);
  if(alt1==0,
    [uni, mark] = make_det2_from_det10(gram, 1,alt2),
     alt1,
    [uni, mark] = make_det5_from_det10(gram, 1)
  );
  fast_marked_HBV(uni, mark);
};

super_fast_inv_even_det14(gram,alt=0) = {
  my(uni, mark);
  if(alt==0,
    [uni, mark] = make_det2_from_det14(gram, 1),
     alt,
    [uni, mark] = make_det7_from_det14(gram, 1)
  );
  fast_marked_HBV(uni, mark);
};

BV2(gram,p)={
 if( (#gram)%2==0, return());
 if(p==3, super_fast_inv_even_det6(gram),
    p==5, super_fast_inv_even_det10(gram),
    p==7, super_fast_inv_even_det14(gram)
 );
};

\\
\\ make det p lattices from det 2p, p=3,5,7
\\

make_det3_from_det6(L, fl=0)={
  my(n=#L, d=6);
  if(n%2==0, return() );
  my(s, w, M, e);
  s = (d*L^-1)%d;
  for(i=1, n,
    if(s[,i]%2, w = s[,i]/2; break)
  ); 
  if(!w, error("mistake") );
  M = concatgram( [L, Mat(2)] );
  w = concat(w, [1/2]~); 
  my(basis);
  basis = mathnf(d*matconcat([matid(n+1),w]))/d;
  if(fl,
    my(mark = matrix(n+1, 1, i, j, i==n+j) );
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis)
  )
};


make_det5_from_det10(L, fl=0, alt=0)={
  my(n=#L, d=10);
  if(n%2==0, return() );
  my(s, w, M, e);
  s = (d*L^-1)%d;
  for(i=1, n,
    if(s[,i]%2, w = s[,i]/2; break)
  ); 
  if(!w, error("mistake") );
  M = concatgram( [L, Mat(2)] );
  w = concat(w, [1/2]~); 
  my(basis);
  basis = mathnf(d*matconcat([matid(n+1),w]))/d;
  if(fl,
    my(mark = matrix(n+1, 1, i, j, i==n+j) );
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis)
  )
};



make_det7_from_det14(L, fl=0)={
  my(n=#L, d=14);
  if(n%2==0, return() );
  my(s, w, M, e);
  s = (d*L^-1)%d;
  for(i=1, n,
    if(s[,i]%2, w = s[,i]/2; break)
  ); 
  if(!w, error("mistake") );
  M = concatgram( [L, Mat(2)] );
  w = concat(w, [1/2]~); 
  my(basis);
  basis = mathnf(d*matconcat([matid(n+1),w]))/d;
  if(fl,
    my(mark = matrix(n+1, 1, i, j, i==n+j) );
    [qfeval(M, basis), basis^-1*mark]
  ,
    qfeval(M, basis)
  )
};


\\
\\ corresponding marked invariants BV3
\\

BV3(gram,p)={
 if( (#gram)%2==0, return());
 if(p==3, super_fast_inv_even_det6(gram,1),
    p==5, super_fast_inv_even_det10(gram,1),
    p==7, super_fast_inv_even_det14(gram,1)
 );
};

\\ for BV dual, absolute version
install("FpM_mul","GGG");
install("hash_GEN", "uG");

graphdualabs(L,n)=
{
  my(S, LL=matdet(L)*L^-1);
  S = matconcat(eqfminim(LL,n));
  if(#S==0, error("unexpected"));
  abs(S~*LL*S)
};

absBVdual(L,n,p=1009)=
{
  my(G,S,M);
  G=graphdualabs(L,n);
  S=FpM_mul(G,G,p);
  M=vector(#S,i,matreduce(S[,i]));
  hash_GEN(matreduce(M))
};

\\ exceptional case (23,5)
inv23_10(x) = {
  my(inva);
  inva = super_fast_inv_even_det10(x);
  if(inva==6051732844143389941 || inva==7177145167242759070,
    return(bitxor(inva,absBVdual(x,24)));
  ,
    return(inva));
};

\\ final BV invariant for our purposes

halfdet(gram)={
 my(n=#gram, d=matdet(gram));
 if(n%2==0, d, d/2)
};

BVhdiscp(gram,p=halfdet(gram),n=#gram)={
 if(p==3 && n<=22,
   return(root_system(gram)),
    p==3 && n==26,
   return(BV1(gram,p)),
    p==3 && n==23, 
   return(BV3(gram,p)),
    p==3 && (n==25 || n==27),
   return(BV2(gram,p)),
    p==5 && n<19,
   return(root_system(gram)),
    p==5 && (n==20 || n==24 || n==28),
   return(BV1(gram,p)),
    p==5 && (n==19 || n==21),
   return(BV3(gram,p)),
    p==5 && (n==25 || n==27),
   return(bitxor(BV2(gram,p), BV3(gram,p))),
    p==5 && n==23,
   return(inv23_10(gram)), 
    p==7 && n<17,
   return(root_system(gram)),
    p==7 && (n==17 || n==18),
   return([root_system(gram),count_eqfminim(gram,4)[5]]),
    p==7 && (n==22 || n==26),
   return(BV1(gram,p)),
    p==7 && (n==19 || n==21 || n==23),
   return(BV2(gram,p)),
    p==7 && n==25,
   return(bitxor(BV2(gram,p), BV3(gram,p))),
   error("not implemented")
 )
};
