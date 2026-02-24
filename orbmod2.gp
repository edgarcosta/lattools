install("orbmod2", "G", "orbmod2", "./orbmod2.so");
install("fororbmod2", "vGVI", "fororbmod2", "./orbmod2.so");
install("fororbmod2aff", "vGVI", "fororbmod2aff", "./orbmod2.so");

binvec2int(v) = vecsum(vector(#v, i, if(v[i], 1<<(i-1), 0)));
int2binvec(x, n) = vector(n, i, bittest(x,i-1));
