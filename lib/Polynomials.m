
intrinsic polynomialA(P, x) -> RngUPolElt, RngIntElt
    { Polynomial A from "Single-factor lifting" [GNP11]. }

    if #P eq 0 then
        p := RandomPrime(12);
        n := Random(4, 30);
        k := Random(n+1, 10*n);
        while GCD(n, k) ne 1 do
            k := Random(n+1, 10*n);
        end while;
        r := Random(0, Floor(k/n));
        P := [p, n, k, r];
    else
        p := P[1];
        n := P[2];
        k := P[3];
        r := P[4];
    end if;

    return (x + &+[p^i : i in [0..r]])^n + p^k, p, P;
end intrinsic;

intrinsic polynomialAm(P, x) -> RngUPolElt, RngIntElt
    { Polynomial Am from "Single-factor lifting" [GNP11]. }

    if #P eq 0 then
        p := RandomPrime(10);
        n := Random(4, 30);
        k := Maximum(n*Valuation(n, p), n) + 1;
        m := Random(2, Floor(Minimum(p/2, 300/n)));
        P := [p, n, k, m];
    else 
        p := P[1];
        n := P[2];
        k := P[3];
        m := P[4];
    end if;
    require p gt 3: "Am-polynomial: p >= 3.";
    require GCD(n, k) eq 1: "Am-polynomial: n and k are not coprime.";
    require k gt n * Valuation(n, p): "Am-polynomial: k <= n * v_p(n).";
    require m gt 1 and 2*m lt p: "Am-polynomial: m is not 1 < m < p/2.";


    g := &*[ (x + 2*j)^n + 2*p^k : j in [0..m-1] ] + 2*p^(m*n*k);

    return g, p, P;
end intrinsic;

intrinsic polynomialB(P, x) -> RngUPolElt, RngIntElt
    { Polynomial B from "Single-factor lifting" [GNP11]. }

    if #P eq 0 then
        p := RandomPrime(12);
        while p mod 3 ne 1 do
            p := RandomPrime(12);
        end while;
        k := Random(5, 100);
        while k mod 3 eq 0 do
            k := Random(5, 100);
        end while;
        P := [p, k];
    else
        p := P[1];
        k := P[2];
    end if;

    require IsPrime(p): "B-polynomial: p not prime.";
    if Type(p) eq RngIntElt then
        require p mod 3 eq 1: "B-polynomial: p mod 3 != 1.";
    end if;
    require k mod 3 ne 0: "B-polynomial: k mod 3 = 0.";

    return (x^2 - 2*x + 4)^3 + p^k, p, P;
end intrinsic;

intrinsic polynomialC(P, x) -> RngUPolElt, RngIntElt
    { Polynomial C from "Single-factor lifting" [GNP11]. }

    if #P eq 0 then
        p := RandomPrime(12);
        while p mod 12 ne 5 do
            p := RandomPrime(12);
        end while;
        k := Random(19, 100);
        P := [p, k];
    else
        p := P[1];
        k := P[2];
    end if;

    require IsPrime(p): "C-polynomial: p not prime.";
    if Type(p) eq RngIntElt then
        require p mod 12 eq 5: "C-polynomial: p mod 12 != 5.";
    end if;
    require k gt 18: "C-polynomial: k <= 18.";

    return ((x^6 + 4*p*x^3 + 3*p^2*x^2 + 4*p^2)^2 + p^6)^3 + p^k, p, P;
end intrinsic;

intrinsic polynomialD(P, x) -> RngUPolElt, RngIntElt
    { Polynomial D from "Single-factor lifting" [GNP11]. }

    if #P eq 0 then
        p := RandomPrime(12);
        ell := RandomPrime(6);
        while p eq ell do
            ell := RandomPrime(6);
        end while;
        n := Random(1, 20);
        k := Random(19, 100);
        while GCD(n, k) ne 1 do
            k := Random(19, 100);
        end while;
        P := [ell, p, n, k];
    else
        ell := P[1];
        p := P[2];
        n := P[3];
        k := P[4];
    end if;

    require IsPrime(ell): "D-polynomial: ell not prime.";
    require IsPrime(p): "D-polynomial: p not prime.";
    require ell ne p: "D-polynomial: ell = p.";
    require Gcd(n, k) eq 1: "D-polynomial: n and k are not co-prime.";
    h := &+[ x^i : i in [0..ell-1] ];
    g := h^n + p^k;

    return g, p, P;
end intrinsic;

intrinsic polynomialE(P, x) -> RngUPolElt, RngIntElt
    { Polynomials E from "Single-factor lifting" [GNP11]. }

    if #P eq 1 then
        p := RandomPrime(12);
        while p le 3 do
            p := RandomPrime(12);
        end while;
        Insert(P, 1, p); 
    else
        p := P[1];
    end if;
    n := P[2];

    require IsPrime(p): "E-polynomial: p not prime.";
    require p gt 3: "E-polynomial: p <= 3.";

    E1 := x^2 + p;
    if n eq 1 then
        return E1, p, P;
    end if;

    E2 := E1^2 + (p - 1)*p^3*x;
    if n eq 2 then
        return E2, p, P;
    end if;

    E3 := E2^3 + p^11;
    if n eq 3 then
        return E3, p, P;
    end if;

    E4 := E3^3 + p^29*x*E2;
    if n eq 4 then
        return E4, p, P;
    end if;

    E5 := E4^2 + (p-1)*p^42*x*E3^2*E1;
    if n eq 5 then
        return E5, p, P;
    end if;

    E6 := E5^2 + p^88*x*E4*E3;
    if n eq 6 then
        return E6, p, P;
    end if;

    E7 := E6^3 + p^295*E5*E4*E2;
    if n eq 7 then
        return E7, p, P;
    end if;

    E8 := E7^2 + (p - 1)*p^632*x*E6*E3^2*E2^2*E1;
    if n eq 8 then
        return E8, p, P;
    end if;

    print "We don't go beyond E8.";
    return 0, p, P;
end intrinsic;

intrinsic polynomialEC(P, x) -> RngUPolElt, RngIntElt
    { Combination of E and C polynomials from SFL paper. }

    p := P[1];
    j := P[2];
    require IsPrime(p): "EC-polynomial: p is not prime.";
    require j ge 1 and j le 8: "EC-polynomial: j < 1 or j > 8.";
    g := polynomialE([* p, j *], x);
    h := polynomialC([* p, 28 *], x);

    return g*h + p^900, p;
end intrinsic; // polynomialEC

intrinsic Fordpols(P, x) -> RngUPolElt, RngIntElt
    { Fordpols }

    i := P[1];

    Fordpols := [
        x^9-2*x^4-10*x^3+x-2,
        x^9-2*x^5+17*x^3+4,
        x^9-2*x^3-10,
        x^10+7*x^9-2*x^8-2*x^7-3*x^5+x^4+1,
        x^10-4*x^9-8*x^5+5*x^4+1,
        x^10-2*x^9-15,
        x^11+x^8-2*x^2+4,
        x^11-x^6-2*x^3-12*x^2-6,
        x^11-x^10-x^4-4,
        x^12-3*x^9+4*x^8-x^6-x^2+10,
        x^12+4*x^11+5*x^10+6*x^6-3*x^4+12,
        x^12+x^9-9*x^7-2*x^6-9*x^5-6,
        x^13+6*x^10-10*x^5+9*x^2-2,
        x^13+x^10+x^9-4*x^8-x^4+x^2-1,
        x^13+x^11-8,
        x^14-x^12-x^7+10*x^5-4,
        x^14+2*x^8+6*x-1,
        x^14-8*x^7+418,
        x^15+4*x^11+12*x^10+x^3-4,
        x^15+9*x^5+1,
        x^15-13*x^5-2,
        x^15-30*x^13+360*x^11-2200*x^9+7200*x^7-12096*x^5+8960*x^3-120*x-249,
        x^15-30*x^13+360*x^11-2200*x^9+7200*x^7-12096*x^5+8960*x^3-120*x-257,
        x^16+132*x^14+6868*x^12+179570*x^10+2394972*x^8+18111820*x^6+65000173*x^4+102234000*x^2+46240000,
        x^21-42*x^19+756*x^17-7616*x^15+47040*x^13-183456*x^11+448448*x^9-658944*x^7+532224*x^5-197120*x^3+21504*x-1691,
        x^12- 181170*x^11 + 13676070375*x^10-564635734535475*x^9 +14120575648656756795*x^8-224213861531349946866060*x^7+2299324928127100837257833640*x^6-15120132032108410885407953780505*x^5+61607021939453175254804920116967515*x^4-144536083330213614666317706146365094565*x^3+170426077617455313511361437803852538934904*x^2-83139235455474245627641509862888062014092560*x +12253655221465755667504199645608996691723374656,
        x^16-12*x^14-84*x^13 - 196*x^12 + 2856*x^11 + 6328*x^10- 42336*x^9 - 64820*x^8 + 352464*x^7 + 298928*x^6 - 1776096*x^5- 262416*x^4 + 5458656*x^3 - 1875872*x^2 - 6688416*x + 7866576,
        x^16 - 432*x^14 + 68688*x^12 - 4717440*x^10 + 112637304*x^8+ 409406400*x^6 + 2774305728*x^4 + 4041156096*x^2 + 11224978704,
        x^24+ 57*x^22 + 1197*x^20 + 13681*x^18 + 136854*x^16 + 1048044*x^14+ 4603892*x^12 + 11460015*x^10 + 16001100*x^8 + 11131014*x^6+ 2739339*x^4 - 368793*x^2 - 7569,
        x^32+16,
        x^32+160*x^30+11216*x^28+455360*x^26+11928052*x^24+212540000*x^22+2645190320*x^20+ 23223642560*x^18+143402547926*x^16+613283590880*x^14+1764753386480*x^12+3275906117440*x^10+3788371498452*x^8+2940754348320*x^6+1769278869776*x^4+73445288000*x^2+87782430961,
        x^40-2*x^39-22*x^37+26*x^36-2*x^35+185*x^34-120*x^33-270*x^32-1232*x^31+689*x^30+1972*x^29+4298*x^28-2588*x^27-6040*x^26-5558*x^25+19939*x^24+21850*x^23+12277*x^22-20890*x^21+4071*x^20+28388*x^19+35210*x^18+10304*x^17+18728*x^16+1408*x^15-3352*x^14-16288*x^13+20512*x^12+16320*x^11-37728*x^10-13312*x^9-7168*x^8+2560*x^7-1280*x^6-7680*x^5+10496*x^4+7168*x^3+512*x^2+2048*x+1024
    ];

    Fordprimes := [
        2, 2,  3, 3, 2, 2, 2, 5,  2, 1289, 2, 3, 11, 17, 2, 2, // 16
        2, 7, 71, 3, 5, 3, 3, 2, 47,   61, 2, 3,  3,  2, 2, 2    // 32
    ];

    return Fordpols[i], Fordprimes[i];
end intrinsic;

intrinsic phipols(P, x) -> RngUPolElt, RngIntElt
    { Chain of phis }

    i := P[1];

    phi1 := x^2+2*x+4;
    phi2 := phi1^2+16*x*phi1+1024;
    phi3 := phi2^2+2^11*(x+2)*phi2+2^18*x*phi1;
    phi4 := phi3^2+2^25*x*phi3+2^35*phi1*phi2;
    phi5 := phi4^3+2^29*phi3*phi4^2+2^139*phi3+2^153*phi2;
    phi6 := phi5^2+2^141*phi3*phi5+2^279*phi4;
    phi7 := phi6^3+2^998*phi1+2^1003;
    phi8 := phi7^2+2^1505*(phi5+2^167)*phi6;
    phi9 := phi8^2+(((((((((2^683)*x)*phi1+((2^688)*x))*phi2+(((2^696))*phi1+((2^700)*x)))*phi3+((((2^710))*phi1+((2^714)*x))*phi2+(((2^721)*x)*phi1+((2^726)*x))))*phi4^2+(((((2^743)*x))*phi2+(((2^750)*x)*phi1+((2^755)*x)))*phi3+((((2^769)*x+(2^770)))*phi2+(((2^776)*x+(2^777))*phi1+((2^782)))))*phi4+(((((2^793)*x+(2^794))*phi1)*phi2+(((2^806))*phi1+((2^810)*x)))*phi3+((((2^819)*x)*phi1+((2^824)*x))*phi2+(((2^832))*phi1))))*phi5+((((((2^867)*x+(2^868))))*phi3+((((2^877))*phi1+((2^881)*x))*phi2+(((2^888)*x+(2^889))*phi1+((2^893)*x+(2^894)))))*phi4^2+(((((2^905)*x+(2^906))*phi1+((2^911)))*phi2+(((2^917)*x+(2^918))*phi1))*phi3+((((2^936)*x+(2^937)))*phi2+(((2^943)*x+(2^944))*phi1)))*phi4+(((((2^960)*x)*phi1+((2^966)))*phi2+(((2^972)*x)*phi1+((2^977)*x)))*phi3+((((2^986)*x+(2^987))*phi1+((2^991)*x))*phi2+(((2^999))*phi1+((2^1003)*x+(2^1004))))))))*phi7)*phi8+(((((((((2^3364)*x+(2^3365)))*phi2+(((2^3376)*x+(2^3377))))*phi3+((((2^3386))*phi1+((2^3391)))*phi2+(((2^3397)*x+(2^3398))*phi1)))*phi4^2+(((((2^3420)))*phi2+(((2^3426)*x+(2^3427))*phi1+((2^3431)*x+(2^3432))))*phi3+((((2^3440)*x+(2^3441))*phi1+((2^3445)*x))*phi2+(((2^3453))*phi1+((2^3457)*x))))*phi4+(((((2^3469)*x)*phi1)*phi2+(((2^3482))*phi1+((2^3486)*x)))*phi3+((((2^3495)*x)*phi1+((2^3500)*x+(2^3501)))*phi2+(((2^3507)*x+(2^3508))*phi1+((2^3512)*x)))))*phi5+((((((2^3531)*x+(2^3532)))*phi2+(((2^3538)*x)*phi1+((2^3543)*x+(2^3544))))*phi3+((((2^3553))*phi1+((2^3557)*x+(2^3558)))*phi2+(((2^3565))*phi1+((2^3569)*x+(2^3570)))))*phi4^2+(((((2^3582))*phi1+((2^3587)))*phi2+(((2^3598)*x)))*phi3+((((2^3607)*x+(2^3608))*phi1+((2^3612)*x+(2^3613)))*phi2))*phi4+(((((2^3641)*x+(2^3642)))*phi2+(((2^3654))))*phi3+((((2^3662)*x)*phi1+((2^3667)*x))*phi2+(((2^3675))*phi1+((2^3679)*x+(2^3680)))))))*phi6));

    phi:=[phi1, phi2, phi3, phi4, phi5, phi6, phi7, phi8, phi9];
    p := 2;
    
    return phi[i], p;
end intrinsic; // phipols

intrinsic plspols(P, x) -> RngUPolElt, RngIntElt
    { pls pols }

    i := P[1];

    pl1:=x^2+13^2*x+13^4*3;
    pl2:=pl1^3+13^18*2;
    pl3:=pl2^10+13^89*(x+13^2)*pl2^5+13^176*pl1;
    pl4:=pl3^2+13^248*(12*(x+13^2)*pl1+13^8)*pl2^6+13^335*12*pl1^2*pl2;
    pls:=[&*[Evaluate(pl4,x+k): k in [0..j]]+13^5000 :j in [0..12]];

    p := 13;
    j := i - 1;
    g := &*[Evaluate(pl4,x+k): k in [0..j]] + 13^5000;

    return g, p;
end intrinsic; // plsPols

intrinsic indpols(P, x) -> RngUPolElt, RngIntElt
    { ind pols }

    p := P[1];
    j := P[2];

    phi0:=x;
    phi1:=x^2+p;
    phi2:=phi1^2+p^3*(p-1)*x;
    phi3:=phi2^3+p^11;
    phi4:=phi3^3+p^29*x*phi2;
    phi5:=phi4^2+(p-1)*p^42*x*phi1*phi3^2;
    phi6:=phi5^2+p^88*x*phi3*phi4;
    phi7:=phi6^3+p^295*phi2*phi4*phi5;
    phi8:=phi7^2+(p-1)*p^632*x*phi1*phi2^2*phi3^2*phi6;

    l:=[phi1,phi2,phi3,phi4,phi5,phi6,phi7,phi8];

    return l[j], p;
end intrinsic; // indpols

intrinsic articleExample(P, x) -> RngUPolElt, RngIntElt
    {}

    p := 2;
    f := x^12 + p^2*x^6 + p^4*x^3 + p^6;

    return f, p;
end intrinsic; // articleExample

