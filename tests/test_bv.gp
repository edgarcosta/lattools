\\
\\ Test BV invariant -- PARI/GP
\\ Run: sage -gp -q < tests/test_bv.gp   (from repo root)
\\
\\ Test data read from tests/test_bv_data.txt.
\\

default(parisize, 256000000); \\ 256 MB stack
\r alt/bv.gp

\\ ---- Load test data ----

{
my(lines, parts, entries, n, gram, ep, ex, td = List());
lines = externstr("grep -v '^#' tests/test_bv_data.txt | grep -v '^[[:space:]]*$'");
for(k = 1, #lines,
  parts = strsplit(lines[k], ":");
  entries = eval(parts[1]);
  n = sqrtint(#entries);
  if(n*n != #entries, error("entry count not a perfect square: ", #entries));
  gram = matrix(n, n, i, j, entries[n*(i-1)+j]);
  ep = eval(parts[2]);
  ex = eval(parts[3]);
  listput(td, [gram, ep, ex]);
);
test_data = Vec(td);
}

\\ ---- Tests ----

D = 4;

print("============================================================");
print("BV invariant test -- GP");
print("============================================================");

{
my(ok = 1, gram, ep, ex, bv, hp, hx, n,
   t0, t1, t2, t3, tot_bv = 0, tot_poly = 0, tot_xor = 0);
t0 = getabstime();
for(i = 1, #test_data,
  gram = test_data[i][1];
  ep = test_data[i][2];
  ex = test_data[i][3];
  n = #gram;
  if(gram != gram~, error("Matrix ", i, " not symmetric"));
  t1 = getabstime();
  bv = BV(gram, D);
  t2 = getabstime();
  hp = HBV_poly(bv);
  t3 = getabstime();
  hx = HBV_xor(bv);
  my(t4 = getabstime());
  tot_bv += t2 - t1; tot_poly += t3 - t2; tot_xor += t4 - t3;
  print("  Matrix ", i, " (", n, "x", n, "): poly = ", hp, "  xor = ", hx,
        "  (BV ", t2-t1, "ms  poly ", t3-t2, "ms  xor ", t4-t3, "ms)");
  if(hp != ep,
    print("FAIL: matrix ", i, " poly hash mismatch: got ", hp, ", expected ", ep);
    ok = 0;
  );
  if(hx != ex,
    print("FAIL: matrix ", i, " xor hash mismatch: got ", hx, ", expected ", ex);
    ok = 0;
  );
);
print("  Total: ", getabstime() - t0, "ms  (BV ", tot_bv, "ms  poly ", tot_poly, "ms  xor ", tot_xor, "ms)");
if(ok, print("PASS: all hashes match expected values (cross-implementation verified)"));
}

\\ ---- C-level fast_marked_HBV comparison ----
\\ Load the C shared library (run from repo root where eqfminim.so lives)
\r tools.gp
\r rs.gp
\r eqfminim.gp

print("");
print("============================================================");
print("C-level fast_marked_HBV (eqfminim.so) -- timing comparison");
print("============================================================");

{
my(t0 = getabstime(), gram, h, t1, n);
for(i = 1, #test_data,
  gram = test_data[i][1];
  n = #gram;
  t1 = getabstime();
  h = fast_marked_HBV(gram, [], D);
  my(dt = getabstime() - t1);
  print("  Matrix ", i, " (", n, "x", n, "): C hash = ", h, "  (", dt, "ms)");
);
print("  Total: ", getabstime() - t0, "ms");
}
