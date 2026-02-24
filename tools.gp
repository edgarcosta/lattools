diag(M) = vector(#M,i,M[i,i]);

maxdiag(M) = vecmax(diag(M));

is_even(gram) = !(diag(gram)%2);

concatgram(g)={
  my(res=matid(0),m,n,p,q);
  for(u=1, #g,
    [m,n] = matsize(res);
    [p,q] = matsize(g[u]);
    res = matrix(m+p, n+q, i, j,
                 if(j<=n && i<=m, res[i,j], j>n && i>m, g[u][i-m,j-n]));
  );
  res
};

\\ shorten a gram matrix (m_ii) as a vector
\\  diagonal, first diagonal, second diagonal, ...
gram_to_vec(gram, n=#gram) = {
 my(ind=1, res);
 res = vector(n*(n+1)/2);
 for(d=0, n-1,
   for(i=1, n-d,
     res[ind] = gram[i,i+d];
     ind++
   );
 );
 res
};

tri_to_int(n) = {
 for(i=1, n,
   if(i*(i+1)/2==n, return(i)));
 error("not a triangular number")
};

vec_to_gram(vec, n=tri_to_int(#vec))={
 my(ind=1, gram);
 gram = matrix(n,n);
 for(d=0, n-1,
   for(i=1, n-d,
     gram[i,i+d] = vec[ind];
     gram[d+i,i] = vec[ind];
     ind++;
   );
 );
 gram
};

random_elem(n) = {
  my(i,j,l,res);
  if(n<=1, return(matid(1)));
  i = random(n)+1;
  j = random(n-1)+1;
  if(j>=i, j++);
  res = matid(n);
  res[i,j] = random(21)-10;
  res;
};

\\ used to test invariance of invariants (!)
random_unimod(n) = {
  my(res=matid(n));
  for(i=1, 4*n, res = res*random_elem(n));
  for(i=1, n, if(random(2),
    for(j=1, n, res[i,j] = -res[i,j]);
  ));
  res;
};

is_unimod(M) = {
  my(d=matdet(M));
  if(d==1 || d==-1, return(1));
  0
};

I_nei(v,d,t=0) = {
  my(n, a, N, nei);
  n=#v~;
  if(d%2,
    a = (v~*v)[1,1]*(d+1)/(2*d),
    a = (v~*v)[1,1]/(2*d)+t*d/2);
  N = matconcat([matid(n), v/d]);
  N[1,1] = d;
  N[1,n+1] = N[1,n+1]-a;
  for(i=2, n,
    N[1,i] = -v[i,1]);
  nei = 1/d*mathnf(d*N);
  return(nei~*nei);
};

nei(v) = I_nei(v[2],v[1],v[3]);
