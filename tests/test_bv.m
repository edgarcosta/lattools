/*
 * Test BV invariant -- Magma
 * Run: magma -b tests/test_bv.m   (from repo root)
 *
 * Test data read from tests/test_bv_data.txt.
 */

SetColumns(0);

load "alt/bv.m";

function LoadTestData(path)
    data := [* *];
    F := Open(path, "r");
    while true do
        line := Gets(F);
        if IsEof(line) then break; end if;
        line := StripWhiteSpace(line);
        if #line eq 0 or line[1] eq "#" then continue; end if;
        parts := Split(line, ":");
        gram_str := StripWhiteSpace(parts[1]);
        // strip [ and ]
        gram_str := gram_str[2..#gram_str-1];
        entries := [StringToInteger(StripWhiteSpace(x)) : x in Split(gram_str, ",")];
        n := Isqrt(#entries);
        assert n^2 eq #entries;
        gram := Matrix(Integers(), n, n, entries);
        poly_h := StringToInteger(StripWhiteSpace(parts[2]));
        xor_h := StringToInteger(StripWhiteSpace(parts[3]));
        Append(~data, <gram, poly_h, xor_h>);
    end while;
    return data;
end function;

// ---- Tests ----

D := 4;
data := LoadTestData("tests/test_bv_data.txt");

printf "============================================================\n";
printf "BV invariant test -- Magma\n";
printf "============================================================\n";

t0 := Cputime();
tot_bv := 0.0; tot_poly := 0.0; tot_xor := 0.0;
ok := true;
for i := 1 to #data do
    gram := data[i][1];
    exp_poly := data[i][2];
    exp_xor := data[i][3];
    n := Nrows(gram);
    assert gram eq Transpose(gram);
    t1 := Cputime();
    bv := BV(gram, D);
    t2 := Cputime();
    hp := HBV_poly(bv);
    t3 := Cputime();
    hx := HBV_xor(bv);
    t4 := Cputime();
    tot_bv +:= t2 - t1; tot_poly +:= t3 - t2; tot_xor +:= t4 - t3;
    printf "  Matrix %o (%ox%o): poly = %o  xor = %o  (BV %os  poly %os  xor %os)\n",
           i, n, n, hp, hx, t2-t1, t3-t2, t4-t3;
    if hp ne exp_poly then
        printf "FAIL: matrix %o poly hash mismatch: got %o, expected %o\n", i, hp, exp_poly;
        ok := false;
    end if;
    if hx ne exp_xor then
        printf "FAIL: matrix %o xor hash mismatch: got %o, expected %o\n", i, hx, exp_xor;
        ok := false;
    end if;
end for;
printf "  Total: %os  (BV %os  poly %os  xor %os)\n", Cputime(t0), tot_bv, tot_poly, tot_xor;

if ok then
    printf "PASS: all hashes match expected values (cross-implementation verified)\n";
end if;

quit;
