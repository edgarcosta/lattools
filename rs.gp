/* root systems */

branch(s, T, a=0, acc=List(s)) = {
  my(n);
  n = [x | x <- T[s], x!=a];
  if(#n==0, return(acc));
  if(#n>1, error("not a branch"));
  n = n[1];
  listput(~acc, n);
  return(branch(n, T, s, acc));
};

gather_irr_rs(L) = {
  my(prev=["H",0], res=List(), cur);
  foreach(L, x,
    if(x[1]==prev[1] && #x[2]==prev[2],
      listput(~cur, x[2]);
    ,
      if(#cur, listput(~res, [prev[1], Vec(cur)]));
      prev = [x[1], #x[2]];
      cur = List([x[2]]);
    );
  );
  if(#cur, listput(~res, [prev[1], Vec(cur)]));
  Vec(res);
};

irr_comp_rs(T) = {
  my(S, list_comp, new_comp, threes, branches, ends, i, t);
  if(#T==0,return());
  S = Set(vector(#T,u,u));
  list_comp=List();
  threes = [x | x <- S, #T[x]>2];
  foreach(threes, x,
    branches = vecsort([Vec(branch(y, T, x)) | y <- T[x]], length);
    if(#branches[1]!=1 || #branches[2]>2, error("not type D or E"));
    if(#branches[2]==1, t="D", t="E");
    new_comp = concat([x], concat(branches));
    listput(~list_comp, [t, new_comp]);
    S = setminus(S, Set(new_comp));
  );
  while(#S,
    i = 1;
    while(#T[S[i]]>1, i += 1);
    new_comp = branch(S[i], T);
    listput(list_comp, ["A", new_comp]);
    S = setminus(S, Set(new_comp));
  );
  return(gather_irr_rs(vecsort(list_comp, x->[x[1],#x[2]])));
};

\\ paranoia
check_Rplus(Rplus) = {
  my(a,b);
  [a,b] = matsize(Rplus);
  for(j=1, b,
    for(i=1, a,
      if(Rplus[i,j]>0, break);
      if(Rplus[i,j]<0, error("check_Rplus"));
    );
  );
};

root_system_vec_Rplus(gram, Rplus) = {
  my(rho, heights, ind_basis, basis, X, rank, vec_nei, T);
  check_Rplus(Rplus);
  if(#Rplus==0, return([]));
  rho = 1/2*Rplus*matrix(#Rplus,1,i,j,1);
  heights = Rplus~*gram*rho;
  ind_basis = select(x->heights[x,1]==1,vector(#Rplus,u,u));
  rank = #ind_basis;
  basis = vector(rank,i,Rplus[,ind_basis[i]]);
  vec_nei = vector(rank,u,List());
  for(i=1,rank,
    X = basis[i]~*gram;
    for(j=i+1,rank,
      if(X*basis[j],
        listput(vec_nei[i],j);
	listput(vec_nei[j],i));
    );
  );
  [[x[1], [vecextract(Rplus, [ind_basis[i] | i <- y]) | y <- x[2]]] | x <- irr_comp_rs(vec_nei)];
};

root_system_vec(gram) = root_system_vec_Rplus(gram, eqfminim(gram,2)[2]);

rsv2name(L) = {
  my(res="", m);
  foreach(L, c,
    if(#res, res = concat(res, " "));
    m = #c[2];
    if(m>1, res = concat(res, Str(m)));
    res = concat(res, Str(c[1], #c[2][1]));
  );
  res;
};

root_system(gram) = rsv2name(root_system_vec(gram));

order_weyl_irr(letter, n) = {
  if(n<1, error("rank is < 1"));
  if(letter=="A", (n+1)!,
     letter=="D", 2^(n-1)*n!,
     letter=="E", if(n==8, 696729600,
                     n==7, 2903040,
                     n==6, 51840,
                     error("invalid root system")),
     error("invalid root system"))
};

index_ADE(v) = {
  for(i=1, #v-1,
    if(v[i]=="A" || v[i]=="D" || v[i]=="E",
      return(i)));
  error("unexpected")
};

isot_str2vec(s) = {
  my(v=Vec(s), i, mult, rank);
  i = index_ADE(v);
  mult = if(i==1, 1, eval(strjoin(v[1..i-1])));
  rank = eval(strjoin(v[i+1..#v]));
  [mult, v[i], rank]
};

rs_to_vec(s) = {
  if(#s, apply(isot_str2vec, strsplit(s, " ")), [])
};

order_weyl(v) = {
  v = rs_to_vec(v);
  prod(i=1, #v, order_weyl_irr(v[i][2],v[i][3])^(v[i][1]))
};
