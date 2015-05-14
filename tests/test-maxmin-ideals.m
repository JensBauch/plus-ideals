// An example using number fields.
Attach("lib/+IdealsNF.m");
Attach("lib/Polynomials.m");

Z := Integers();
Zx<x> := PolynomialRing(Z);


function testRandomIdeal(g, p, pol_name, params)
    
    K<a> := NumberField(g);
    Montes(K, p);
    exponents := [ Random(-100, 100) : omrep in K`PrimeIdeals[p] ];
    I := &*[ K`PrimeIdeals[p,i]^exponents[i] : i in [1..#exponents] ];
    printf "[MaxMin ideals] g = %o(%o), p = %o for ideal I = %o.\n", pol_name, params, p, I`FactorizationString;

    nums, dexp := pBasis(I, p : Separated:=true);
    for i in [1..#K`PrimeIdeals[p]] do
        UpdateLastLevel(~K`PrimeIdeals[p,i],
                        K`PrimeIdeals[p,i]`Type[#K`PrimeIdeals[p,i]`Type]`Phi);
    end for;

    norm := &+[ K`PrimeIdeals[p,i]`f * exponents[i] : i in [1..#exponents] ];
    if norm ne K`LocalIndex[p] - &+(dexp) then
        printf "[MaxMin ideals] Error: Incoherent indices!.\n";
        return false;
    end if;

    for i in [1..#nums] do
        alpha := K![ Coefficient(nums[i], j) : j in [0..Degree(g)-1] ];
        nu := dexp[i];
        //printf "g_%o = %o.\n", i-1, nums[i]; 
        for j in [1..#K`PrimeIdeals[p]] do
            omrep := K`PrimeIdeals[p,j];
            val := PValuation(alpha, omrep);
            //printf "v_P_%o(g_%o) = %o <=> %o * %o + %o.\n", j, i-1, val, nu, omrep`e, exponents[j];
            if val lt (nu * omrep`e) + exponents[j] then
                printf "[MaxMin] Error: g_%o(theta) is not integral for omreps[%o]!\n", i-1, omrep`Position;
                return false;
            end if;
        end for;
    end for;

    return true;
end function;

function testA(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialA([], x);

        success := testRandomIdeal(g, p, "A", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testAm(num_tests)
    
    for i in [1..num_tests] do
        g, p, params := polynomialAm([], x);

        success := testRandomIdeal(g, p, "Am", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testB(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialB([], x);

        success := testRandomIdeal(g, p, "B", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testC(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialC([], x);

        success := testRandomIdeal(g, p, "C", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testD(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialD([], x);

        success := testRandomIdeal(g, p, "D", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testE(num_tests)
    for i in [1..num_tests] do
        p := RandomPrime(12);
        while p le 3 do
            p := RandomPrime(12);
        end while;
        
        for j in [3..8] do
            g, p, params := polynomialE([p, j], x);

            success := testRandomIdeal(g, p, "E", params);
            if success eq false then
                break;
            end if;
        end for;
    end for;

    return success;
end function;


success := testB(5);
quit;

