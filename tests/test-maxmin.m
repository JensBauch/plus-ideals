// An example using number fields.
Attach("lib/+IdealsNF.m");
Attach("lib/Polynomials.m");

Z := Integers();
Zx<x> := PolynomialRing(Z);


function testMaximalOrder(g, p, pol_name, params)
    printf "[MaxMin] g = %o(%o), p = %o.\n", pol_name, params, p;
    
    K<a> := NumberField(g);
    nums, dexp := pBasis(ideal(K, K!1), p : Separated:=true);

    local_index := &+(dexp);
    if local_index ne K`LocalIndex[p] then
        printf "[MaxMin] Error: sum(dexp) = %o != local index = %o.\n", local_index, K`LocalIndex[p];
        return false;
    end if;

    for i in [1..#nums] do
        alpha := K![ Coefficient(nums[i], j) : j in [0..Degree(g)-1] ];
        nu := dexp[i];
        for omrep in K`PrimeIdeals[p] do
            val := PValuation(alpha, omrep);
            if val lt nu * omrep`e then
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

        success := testMaximalOrder(g, p, "A", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testAm(num_tests)
    
    for i in [1..num_tests] do
        g, p, params := polynomialAm([], x);

        success := testMaximalOrder(g, p, "Am", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testB(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialB([], x);

        success := testMaximalOrder(g, p, "B", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testC(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialC([], x);

        success := testMaximalOrder(g, p, "C", params);
        if success eq false then
            break;
        end if;
    end for;

    return success;
end function;

function testD(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialD([], x);

        success := testMaximalOrder(g, p, "D", params);
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

            success := testMaximalOrder(g, p, "E", params);
            if success eq false then
                break;
            end if;
        end for;
    end for;

    return success;
end function;


success := testAm(5);

//g, p, params := polynomialB([3181, 91], x);
//success := testMaximalOrder(g, p, "B", params);

