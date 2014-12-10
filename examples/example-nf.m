// An example using number fields.
Attach("lib/+IdealsNF.m");

Z := Integers();
Zx<x> := PolynomialRing(Z);

// Define a monic irreducible polynomial.
p := 2;
q := 3;
f := x^6 + p*q^2*x^2 + p^3*q*3;


K<a> := NumberField(f);

// Compute a triangular p-integral basis.
p_basis := pBasisTriangular(K, p);

print p_basis;

quit;
