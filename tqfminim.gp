\\ (slow, but exact) variants of qfminim

tqfminim_rec(n, A, U, i, M, Mi, x, f, ~fpar) = {
  my(xi, y, z, S, bound, newx);
  if(Mi<0, return(0));
  if(i<=0, return(f(~fpar, x~, M-Mi)));
  S = U[i] + sum(j=i+1, n, A[i,j]*x[j]);
  bound = Mi/A[i,i];
  newx = vector(n, j, if(j>i, x[j]));
  y = floor(-S); /* largest y such that y+S <= 0 */
  xi = y;
  z = (xi+S)^2;
  while(z <= bound,
    newx[i] = xi;
    if(tqfminim_rec(n, A, U, i-1, M, Mi-A[i,i]*z, newx, f, ~fpar),
      return(1));
    xi -= 1;
    z = (xi+S)^2;
  );
  xi = y+1;
  z = (xi+S)^2;
  while(z <= bound,
    newx[i] = xi;
    if(tqfminim_rec(n, A, U, i-1, M, Mi-A[i,i]*z, newx, f, ~fpar),
      return(1));
    xi += 1;
    z = (xi+S)^2;
  );
};

/*
  evaluate f(~fpar, x, q) for each pair (x, q)
  where x in Z^n and q := qfeval(gram, x+u) <= M
  stop if f(...) evaluates to true
*/
tqfminim(gram, u, M, f, ~fpar) = {
  my(A=qfgaussred(gram), U, n=#gram);
  check_upper_triang(A);
  U = vector(n, i, u[i]+sum(j=i+1, n, A[i,j]*u[j]));
  tqfminim_rec(n, A, U, n, M, M, vector(n), f, ~fpar);
};

/*
  apply f to each pair (x, q)
  where x in Z^n and q := qfeval(gram, x) satisfy:
  1. qfeval(gram,x,w) = qfeval(gram,v,w) for each column w of F
  2. q = qfeval(gram,v)
  stop when f returns !=0
*/
qfminim_fixed(gram, v, F, f, ~fpar) = {
  my(B, G, u, M);
  B = matkerint(F~*gram);
  G = B~*gram*B;
  /* qfeval(gram,v,B*x) == qfeval(G,u,x) */
  u = G^-1*B~*gram*v;
  /* want x=v+B*y with qfeval(G,y)+2*qfeval(gram,v,B*y)==0, i.e. qfeval(G,y+u)==qfeval(G,u) */
  M = qfeval(G,u);
  tqfminim(G, u, M, (~p,x,q)->if(q==M, f(~p, v+B*x)), ~fpar);
};

listput_ret1(~L, x) = {
  listput(~L, x);
  1;
};

/*
  find a vector of minimal norm among those
  whose last codim coordinates are given by v
  assume that this minimal norm is at least M
*/
short_vector_fixed_coord(gram, codim, v, M, even) = {
  my(n=#gram, S, res, vext, u, A, U);
  S = gram[1..(n-codim), 1..(n-codim)];
  res = List();
  vext = concat(Col(vector(n-codim)), Col(v));
  u = S^-1*(gram*vext)[1..(n-codim)];
  M += qfeval(S,u) - qfeval(gram,vext);
  A = qfgaussred(S);
  check_upper_triang(A);
  U = vector(n-codim, i, u[i]+sum(j=i+1, n-codim, A[i,j]*u[j]));
  while(!#res,
    tqfminim_rec(n-codim, A, U, n-codim, M, M, vector(n-codim),
                 (~p,x,ign)->listput_ret1(~p,x), ~res);
    M += if(even,2,1);
  );
  concat(res[1], Col(v));
};
