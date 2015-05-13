// An example using number fields.
Attach("lib/+IdealsNF.m");
Attach("lib/Polynomials.m");

Z := Integers();
Zx<x> := PolynomialRing(Z);


function testPolynomial(g, p, pol_name, params, prec)
    printf "[SFL] g = %o(%o), p = %o, prec = %o.\n", pol_name, params, p, prec;
    factors := pAdicFactors(g, p, prec);

    f := &*[ F : F in factors ];
    if f eq g then
        return true;
    end if;

    val := Minimum([ Valuation(c, p) : c in Coefficients(g - f) ]);

    if val lt prec then
        success := false;
        printf "[SFL] Error: w(g - f) = %o < %o = prec.\n", val, prec;
    else
        success := true;
    end if;

    return success;
end function;

function testA(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialA([], x);

        for prec in [100, 500, 1000, 5000] do
            success := testPolynomial(g, p, "A", params, prec);
            if success eq false then
                break;
            end if;
        end for;
    end for;

    return success;
end function;

function testAm(num_tests)
    
    for i in [1..num_tests] do
        g, p, params := polynomialAm([], x);

        for prec in [100, 500, 1000, 5000] do
            success := testPolynomial(g, p, "Am", params, prec);
            if success eq false then
                break;
            end if;
        end for;
    end for;

    return success;
end function;

function testB(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialB([], x);

        for prec in [100, 500, 1000, 5000] do
            success := testPolynomial(g, p, "B", params, prec);
            if success eq false then
                break;
            end if;
        end for;
    end for;

    return success;
end function;

function testC(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialC([], x);

        for prec in [100, 500, 1000, 5000] do
            success := testPolynomial(g, p, "C", params, prec);
            if success eq false then
                break;
            end if;
        end for;
    end for;

    return success;
end function;

function testD(num_tests)
    for i in [1..num_tests] do
        g, p, params := polynomialD([], x);

        for prec in [100, 500, 1000, 5000] do
            success := testPolynomial(g, p, "D", params, prec);
            if success eq false then
                break;
            end if;
        end for;
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

            for prec in [100, 500, 1000, 5000] do
                success := testPolynomial(g, p, "E", params, prec);
                if success eq false then
                    break;
                end if;
            end for;
        end for;
    end for;

    return success;
end function;


success := testE(3);
