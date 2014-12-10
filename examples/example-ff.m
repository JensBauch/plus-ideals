// An example using function fields.
Attach("lib/+IdealsFF.m");

Fq := FiniteField(7);
Fqt<t> := PolynomialRing(Fq);
KT<T> := RationalFunctionField(Fq);
KTx<x> := PolynomialRing(KT);

// Define a monic irreducible polynomial.
p := t+1;
q := t+4;
f := x^6 + p*q^2*x^2 + p^2*q^3;

K<a> := FunctionField(f);

// Compute a triangular p-integral basis.
p_basis := pBasisTriangular(K, p);

print p_basis;

quit;

