"""
Test BV invariant -- Sage
Run: sage -python tests/test_bv.py [test_data_file]   (from repo root)

Uses PARI's qfminim convention (v^T * M * v <= d) to match test_bv.gp and test_bv.m.
Defaults to tests/test_bv_data.txt if no file is specified.
"""
import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'alt'))
from bv import BV, HBV_poly, HBV_xor
from sage.all import Matrix, ZZ

def load_test_data(path):
    """Parse test_bv_data.txt -> list of (gram, expected_poly, expected_xor)."""
    data = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            gram_str, poly_str, xor_str = line.split(':')
            # parse [a,b,...] -> list of ints
            entries = list(map(int, gram_str.strip().strip('[]').split(',')))
            n = int(len(entries)**0.5)
            assert n * n == len(entries), f"entry count {len(entries)} is not a perfect square"
            gram = Matrix(ZZ, n, n, entries)
            data.append((gram, int(poly_str.strip()), int(xor_str.strip())))
    return data

D = 4  # short vector bound
if len(sys.argv) > 1:
    data_path = sys.argv[1]
else:
    data_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'test_bv_data.txt')
test_data = load_test_data(data_path)

print("=" * 60)
print("BV invariant test -- Sage")
print("=" * 60)

t0 = time.time()
total_bv = total_poly = total_xor = 0
ok = True
for i, (gram, exp_poly, exp_xor) in enumerate(test_data):
    assert gram == gram.T, f"Matrix {i+1} is not symmetric"
    t1 = time.time()
    bv = BV(gram, D)
    t2 = time.time()
    hp = HBV_poly(bv)
    t3 = time.time()
    hx = HBV_xor(bv)
    t4 = time.time()
    total_bv += t2 - t1
    total_poly += t3 - t2
    total_xor += t4 - t3
    print(f"  Matrix {i+1} ({gram.nrows()}x{gram.ncols()}): poly = {hp}  xor = {hx}  (BV {t2-t1:.4f}s  poly {t3-t2:.4f}s  xor {t4-t3:.4f}s)")
    if hp != exp_poly:
        print(f"FAIL: matrix {i+1} poly hash mismatch: got {hp}, expected {exp_poly}")
        ok = False
    if hx != exp_xor:
        print(f"FAIL: matrix {i+1} xor hash mismatch: got {hx}, expected {exp_xor}")
        ok = False
print(f"  Total: {time.time() - t0:.3f}s  (BV {total_bv:.3f}s  poly {total_poly:.4f}s  xor {total_xor:.4f}s)")

if ok:
    print("PASS: all hashes match expected values (cross-implementation verified)")
