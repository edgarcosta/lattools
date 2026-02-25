/*
 * BV lattice invariant -- Magma implementation
 * Portable output format matching bv.py (Sage) and test_bv.gp (PARI/GP).
 *
 * Uses PARI's qfminim convention: v^T * gram * v <= d.
 * Magma's LatticeWithGram + ShortVectors uses the same convention.
 *
 * Load: load "bv.m";
 */

function LatticeGraph(gram, d)
    L := LatticeWithGram(gram);
    S := ShortVectors(L, d);
    if #S eq 0 then
        return Matrix(Integers(), 0, 0, []);
    end if;
    m := #S;
    R := Matrix(GF(2), m, m,
         [InnerProduct(S[i][1], S[j][1]) : i in [1..m], j in [1..m]]);
    return ChangeRing(R, Integers());
end function;

// Sorted (value, count) pairs for a column -- stored as [[val,cnt], ...]
function ColSig(col)
    sorted := Sort(col);
    result := [];
    current := sorted[1];
    count := 1;
    for i := 2 to #sorted do
        if sorted[i] eq current then
            count +:= 1;
        else
            Append(~result, [current, count]);
            current := sorted[i];
            count := 1;
        end if;
    end for;
    Append(~result, [current, count]);
    return result;
end function;

// BV invariant -- returns [ <sig, count>, ... ]
function BV(gram, d)
    G := LatticeGraph(gram, d);
    m := Nrows(G);
    if m eq 0 then return []; end if;
    p := NextPrime(m);
    Gp := ChangeRing(G, GF(p));
    S := Gp^2;
    cols := [ColSig(Sort([Integers()!S[i,j] : i in [1..m]])) : j in [1..m]];
    Sort(~cols);
    result := [];
    current := cols[1];
    count := 1;
    for j := 2 to m do
        if cols[j] eq current then
            count +:= 1;
        else
            Append(~result, <current, count>);
            current := cols[j];
            count := 1;
        end if;
    end for;
    Append(~result, <current, count>);
    return result;
end function;

// Portable polynomial hash matching bv.py HBV_poly
function HBV_poly(bv)
    M := 2^61 - 1;
    h := 0;
    for i := 1 to #bv do
        sig := bv[i][1];
        cnt := bv[i][2];
        for j := 1 to #sig do
            h := (h * 1000003 + sig[j][1]) mod M;
            h := (h * 1000003 + sig[j][2]) mod M;
        end for;
        h := (h * 1000003 + cnt) mod M;
    end for;
    return h;
end function;

// Portable XOR-multiply hash matching bv.py HBV_xor
function HBV_xor(bv)
    M := 2^64;
    MULT := 1111111111111111111;
    h := 13282407956253574712;
    for i := 1 to #bv do
        sig := bv[i][1];
        cnt := bv[i][2];
        for j := 1 to #sig do
            h := (BitwiseXor(h, sig[j][1]) * MULT) mod M;
            h := (BitwiseXor(h, sig[j][2]) * MULT) mod M;
        end for;
        h := (BitwiseXor(h, cnt) * MULT) mod M;
    end for;
    return h;
end function;

function HBV(gram, d)
    return HBV_poly(BV(gram, d));
end function;
