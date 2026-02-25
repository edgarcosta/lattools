from collections import Counter

from sage.all import GF, Matrix, ZZ, next_prime, pari


def graph(gram, d):
    r"""
    Build the mod 2 adjacency matrix from short vectors of a lattice.

    Uses PARI's ``qfminim`` convention: enumerates vectors with
    ``0 < v^T * gram * v <= d``, one per `\{v, -v\}` pair.

    INPUT:

    - ``gram`` -- a Gram matrix (symmetric, positive-definite, over ZZ)
    - ``d`` -- a positive integer; enumerate vectors with 0 < v*gram*v <= d

    OUTPUT:

    A matrix over GF(2) equal to ``S * gram * S^T mod 2``, where S is the
    matrix whose rows are the short vectors (one per {v, -v} pair).

    EXAMPLES:

    A2 root lattice has 3 roots up to sign, forming a complete graph::

        sage: from bv import graph
        sage: A2 = Matrix(ZZ, [[2,1],[1,2]])
        sage: G = graph(A2, 2)
        sage: G.base_ring()
        Finite Field of size 2
        sage: G.nrows(), G.ncols()
        (3, 3)
        sage: G == G.T
        True
        sage: all(G[i,i] == 0 for i in range(3))  # even lattice
        True
        sage: G.rank()
        2

    E8 lattice has 120 roots up to sign::

        sage: E8 = Matrix(ZZ, [
        ....:   [2,0,0,0,0,0,0,1],
        ....:   [0,2,1,0,0,0,0,0],
        ....:   [0,1,2,1,0,0,0,0],
        ....:   [0,0,1,2,1,0,0,0],
        ....:   [0,0,0,1,2,1,0,0],
        ....:   [0,0,0,0,1,2,1,0],
        ....:   [0,0,0,0,0,1,2,1],
        ....:   [1,0,0,0,0,0,1,2],
        ....: ])
        sage: graph(E8, 2).ncols()
        120

    No short vectors when d is too small::

        sage: graph(A2, 1).ncols()
        0

    Odd lattice has nonzero diagonal entries::

        sage: I2 = Matrix(ZZ, [[1,0],[0,1]])
        sage: G = graph(I2, 2)
        sage: G.ncols()
        4
        sage: any(G[i,i] != 0 for i in range(G.nrows()))
        True
    """
    S = pari(gram).qfminim(d)[2]  # columns are short vectors
    S = Matrix(ZZ, S).T  # rows are short vectors
    m = S.nrows()
    if m == 0:
        return Matrix(GF(2), 0, 0)
    return (S * gram * S.T).change_ring(GF(2))


def BV(gram, d):
    r"""
    Compute the BV invariant of a lattice.

    INPUT:

    - ``gram`` -- a Gram matrix (symmetric, positive-definite, over ZZ)
    - ``d`` -- a positive integer; short vector bound

    OUTPUT:

    A canonical tuple-of-tuples representing the multiset of column multisets
    of ``graph(gram, d)^2 mod p``, where ``p`` is the smallest prime
    greater than the number of short vectors.

    EXAMPLES:

    A2 has a single column signature with multiplicity 3 (all roots
    are equivalent by symmetry)::

        sage: from bv import BV
        sage: A2 = Matrix(ZZ, [[2,1],[1,2]])
        sage: bv = BV(A2, 2)
        sage: len(bv)
        1
        sage: bv[0][1]
        3

    Isometry invariance: a unimodular change of basis preserves BV::

        sage: U = Matrix(ZZ, [[1,1],[0,1]])
        sage: A2b = U.T * A2 * U
        sage: BV(A2b, 2) == BV(A2, 2)
        True

    Distinguishes non-isomorphic lattices::

        sage: I2 = Matrix(ZZ, [[1,0],[0,1]])
        sage: BV(A2, 2) == BV(I2, 2)
        False

    No short vectors returns an empty tuple::

        sage: BV(A2, 1)
        ()
    """
    G = graph(gram, d)
    m = G.ncols()
    if m == 0:
        return ()
    p = next_prime(m)
    Gp = G.change_ring(GF(p))
    G2 = Gp * Gp
    # For each column, compute a canonical signature: sorted (value, count) pairs
    cols = []
    for j in range(m):
        col = tuple(int(G2[i, j]) for i in range(m))
        sig = tuple(sorted(Counter(col).items()))
        cols.append(sig)
    # Outer multiset: sorted (signature, count) pairs
    return tuple(sorted(Counter(cols).items()))


def _bv_int_stream(bv):
    r"""
    Yield the integers of a BV canonical form in a fixed traversal order.

    For each ``(signature, count)`` in the outer sorted multiset, yield
    each ``(value, multiplicity)`` pair in the signature, then the count.

    EXAMPLES::

        sage: from bv import BV, _bv_int_stream
        sage: A2 = Matrix(ZZ, [[2,1],[1,2]])
        sage: list(_bv_int_stream(BV(A2, 2)))
        [0, 1, 1, 2, 3]
    """
    for sig, count in bv:
        for value, multiplicity in sig:
            yield int(value)
            yield int(multiplicity)
        yield int(count)


def HBV_poly(bv):
    r"""
    Portable polynomial hash of a BV canonical form.

    Uses ``h = (h * 1000003 + x) mod (2^61 - 1)`` over the integer stream
    of ``bv``.  All intermediate values are non-negative and less than
    ``2^61 - 1``, so this is trivially reproducible in GP, Magma, or any
    language with 64-bit signed arithmetic.

    INPUT:

    - ``bv`` -- output of :func:`BV`

    OUTPUT:

    A non-negative integer less than ``2^61 - 1``.

    EXAMPLES::

        sage: from bv import BV, HBV_poly
        sage: A2 = Matrix(ZZ, [[2,1],[1,2]])
        sage: 0 <= HBV_poly(BV(A2, 2)) < 2^61 - 1
        True

    Isometry invariance::

        sage: U = Matrix(ZZ, [[1,1],[0,1]])
        sage: HBV_poly(BV(U.T * A2 * U, 2)) == HBV_poly(BV(A2, 2))
        True

    Distinguishes non-isomorphic lattices::

        sage: I2 = Matrix(ZZ, [[1,0],[0,1]])
        sage: HBV_poly(BV(A2, 2)) == HBV_poly(BV(I2, 2))
        False

    Empty BV hashes to 0::

        sage: HBV_poly(())
        0
    """
    M = (1 << 61) - 1  # Mersenne prime 2^61 - 1
    h = 0
    for x in _bv_int_stream(bv):
        h = (h * 1000003 + x) % M
    return h


def HBV_xor(bv):
    r"""
    Portable XOR-multiply hash of a BV canonical form.

    Uses ``h = ((h ^ x) * 1111111111111111111) mod 2^64`` over the integer
    stream of ``bv``, matching the hash function in ``eqfminim.c``.
    Requires unsigned 64-bit arithmetic; in GP or Magma, apply
    ``% 2^64`` after each operation.

    INPUT:

    - ``bv`` -- output of :func:`BV`

    OUTPUT:

    A non-negative integer less than ``2^64``.

    EXAMPLES::

        sage: from bv import BV, HBV_xor
        sage: A2 = Matrix(ZZ, [[2,1],[1,2]])
        sage: 0 <= HBV_xor(BV(A2, 2)) < 2^64
        True

    Isometry invariance::

        sage: U = Matrix(ZZ, [[1,1],[0,1]])
        sage: HBV_xor(BV(U.T * A2 * U, 2)) == HBV_xor(BV(A2, 2))
        True

    Distinguishes non-isomorphic lattices::

        sage: I2 = Matrix(ZZ, [[1,0],[0,1]])
        sage: HBV_xor(BV(A2, 2)) == HBV_xor(BV(I2, 2))
        False

    Empty BV hashes to the init constant::

        sage: HBV_xor(())
        13282407956253574712
    """
    MASK = (1 << 64) - 1
    MULT = 1111111111111111111
    h = 13282407956253574712
    for x in _bv_int_stream(bv):
        h = ((h ^ x) * MULT) & MASK
    return h


def HBV(gram, d):
    r"""
    Portable hash of the BV invariant (polynomial variant).

    INPUT:

    - ``gram`` -- a Gram matrix (symmetric, positive-definite, over ZZ)
    - ``d`` -- a positive integer; short vector bound

    OUTPUT:

    A non-negative integer less than ``2^61 - 1``, equal to
    ``HBV_poly(BV(gram, d))``.

    EXAMPLES::

        sage: from bv import BV, HBV, HBV_poly
        sage: A2 = Matrix(ZZ, [[2,1],[1,2]])
        sage: HBV(A2, 2) == HBV_poly(BV(A2, 2))
        True

    Isometry invariance::

        sage: U = Matrix(ZZ, [[1,1],[0,1]])
        sage: HBV(U.T * A2 * U, 2) == HBV(A2, 2)
        True
    """
    return HBV_poly(BV(gram, d))
