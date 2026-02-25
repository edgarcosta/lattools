"""
Compute BV hashes for Gram matrices.

Usage: sage -python alt/compute_hashes.py input_file [D]

Reads a file with one Gram matrix per line (as [a,b,...] flat row-major)
and outputs test data in the format used by tests/test_bv_data.txt:

    [gram_flat]:HBV_poly:HBV_xor

D defaults to 4 (short vector bound).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bv import BV, HBV_poly, HBV_xor
from sage.all import Matrix, ZZ

if len(sys.argv) < 2:
    print(__doc__.strip(), file=sys.stderr)
    sys.exit(1)

input_file = sys.argv[1]
D = int(sys.argv[2]) if len(sys.argv) > 2 else 4

with open(input_file) as f:
    lines = [l.strip() for l in f if l.strip() and l.strip().startswith('[')]

for line in lines:
    entries = list(map(int, line.strip().strip('[]').split(',')))
    n = int(len(entries)**0.5)
    assert n * n == len(entries), f"Not a perfect square: {len(entries)}"
    gram = Matrix(ZZ, n, n, entries)
    assert gram == gram.T, "Not symmetric"
    bv = BV(gram, D)
    hp = HBV_poly(bv)
    hx = HBV_xor(bv)
    flat = ','.join(str(e) for e in entries)
    print(f"[{flat}]:{hp}:{hx}")
