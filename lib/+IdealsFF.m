//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//    MontesFF Package 
//    Jens-Dietrich Bauch 
//    April 2010
//    (C) 2013 Jens-Dietrich Bauch
//    Distributed under the terms of the GNU General Public License 
//    http://www.gnu.org/licenses/gpl.txt  
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

//Attach("Doctorado/Magma/SpecFile/Attaches.m");

declare verbose montestalk, 4;
declare verbose hds, 4;
declare attributes FldFun: 
pBasis, Discriminant, FactorizedDiscriminant, FactorizedPrimes, IntegralBasis,
LocalIndex, pHermiteBasis, PrimeIdeals, TreesIntervals, localbasedata,maxorderfinite,
Times, SFLCount;
		
		
//Attributes for dealing with places at infinity

AddAttribute(FldFun,"PlacesAtInfinity");
AddAttribute(FldFun,"Cf");
AddAttribute(FldFun,"IsomorphicFunctionField");
AddAttribute(FldFun,"Fin");
AddAttribute(FldFun,"Genus");
AddAttribute(FldFun,"Index");
AddAttribute(FldFun,"IndexBases");
//Records for places and Divisors

PlaceRecord:=recformat<
    FiniteIdeal: Rec, 
    InfiniteIdeal: Rec,
    FactorizationString:  MonStgElt
    >;

//Records for montes algorithm
		
		
		
PrimeIdealRecord:=recformat<
Type: SeqEnum,
Parent: FldFun,
Pol: RngUPolElt,
IntegerGenerator: RngUPolElt,
e: Integers(),
f: Integers(),
exponent: RngIntElt,
LocalGenerator: FldFunElt,
LogLG: ModTupRngElt,
Generator: FldFunElt,
CrossedValues: SeqEnum,
Position: Integers()

>;



IdealRecord:=recformat<
Generators: SeqEnum , 
Norm: RngUPolElt,
Parent: FldFun,
Radical: SeqEnum,
IsIntegral: BoolElt,
IsPrime: BoolElt,
Factorization: List,
FactorizationString:  MonStgElt,
IntegerGenerator: RngUPolElt,
Generator: FldFunElt,
Basis: SeqEnum,
PBasis: SeqEnum,            /* only for prime ideals */
PBasisVals: SeqEnum,        /* only for prime ideals */
Position: Integers(),       /* only for prime ideals */  
Type: SeqEnum,              /* only for prime ideals */
e: Integers(),              /* only for prime ideals */
f: Integers(),              /* only for prime ideals */
exponent: RngIntElt,       /* only for prime ideals */
LocalGenerator: FldFunElt,  /* only for prime ideals */
LogLG: ModTupRngElt,        /* only for prime ideals */
CrossedValues: SeqEnum      /* only for prime ideals */
>;


TypeLevel:=recformat<
Phi: RngUPolElt,
V: Integers(),
h: Integers(),
e: Integers(),
f: Integers(),
prode: Integers(),  /* e1*...*e(k-1) */
prodf: Integers(),  /* f1*...*f(k-1) */
invh: Integers(),
slope,
psi: RngUPolElt,
Fq: FldFin,
FqY:RngUPol,
z: FldFinElt,
omega: Integers(),
cuttingslope: Integers(),
Refinements: List, 
alpha: Integers(),
logPi: ModTupRngElt,
logPhi: ModTupRngElt,
logGamma: ModTupRngElt,
IntegerGenerator : RngUPolElt,     /* only in level 1 */   // should be Prime!!
Pol : RngUPolElt,       /* only in level 1 */
ProdQuots: SeqEnum,     /* only in level 1 */
ProdQuotsVals: SeqEnum, /* only in level 1 */
Phiadic: SeqEnum,       /* only in level 1 */
sfl: SeqEnum,            /* only in level 1 */
Redmap: Map,
map: Map
>;

//Record for ideals

/*
IdealRecord:=recformat<
    Generators: SeqEnum , 
    Norm: Rationals(),
    Parent: FldFun,
    Radical: SeqEnum,
    IsIntegral: BoolElt,
    IsPrime: BoolElt,
    Factorization: List,
    FactorizationString:  MonStgElt,
    IntegerGenerator: RngUPolElt,
    Generator: FldFunElt
>;
*/

OkutsuFrameLevel := recformat<
    degree: RngIntElt,
    index: RngIntElt,
    values: List,
    polynomial: RngUPolElt
>;


//////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////Helpfunction for function fields /////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
/////////////////kann eigentlich raus in meiner MAGMA version///////////////////////////////////

intrinsic 'mod'(alpha:: FldFunElt, p:: RngUPolElt)->FldFinElt
{Compute the reduction map ZK--> ZK/pZK}
// It's a copy of Reduction, with better name

R:=Parent(p);

return Parent(alpha)![R!i mod p:i in Eltseq(alpha)];

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////



/*//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Numerator(z:: FldFunElt)->FldFunElt
{Determines the Nominator of a FldFunElt z}
if z eq 0 then return 0;end if;
F:=Parent(z);
k:=BaseField(F);
kx:=PolynomialRing(k);
temp:=ElementToSequence(z);
length:=#temp;
Num:=F!LCM([Denominator(i):i in ElementToSequence(kx!temp)]);
return z*Num; 

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Denominator(z:: FldFunElt)->FldFunElt
{Terminates the denominator of z}
if z eq 0 then return 1,z; end if;
F:=Parent(z);
k:=BaseField(F);
kx:=PolynomialRing(k);
temp:=ElementToSequence(z);
length:=#temp;
return F!LCM([Denominator(i):i in ElementToSequence(kx!temp)]);

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////*/

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Numerator(z:: FldFunElt)->FldFunElt
{Determines the Nominator of a FldFunElt z}

return Parent(z)!Numerator(z,EquationOrderFinite(Parent(z)));


end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Denominator(z:: FldFunElt)->FldFunElt
{Terminates the denominator of z}

return Parent(z)!Denominator(z,EquationOrderFinite(Parent(z)));

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic InftyField(F::FldFun)->FldFun
{Input: Function field F with indeterminate T, outpout: Function field F with indeterminate 1/T}

F`Fin:=1;
if not assigned F`IsomorphicFunctionField or not assigned F`Cf or true then
kt:=PolynomialRing(ConstantField(F));
t:=kt.1;
T:=BaseField(F).1;
f:=DefiningPolynomial(F);
n:=Degree(f);
Coeff:=Coefficients(f);

Cf:=Maximum([Ceiling(Degree(Coeff[j])/(-j+n+1)): j in [1..#Coeff-1]]);//Florians Formel. Stimmt mit meinem Ergebnis Ã¼berein.
CoeffList:=Eltseq(T^(-n*Cf)*PolynomialRing(Parent(T))!Evaluate(f,t^Cf*Parent(f).1));//CoeffList:=Eltseq(T^(-n*Cf)*Evaluate(f,t^Cf*Parent(f).1));
CoeffNewf:=[];
for i in CoeffList do
	TMP:=0;
	for j in Terms(Numerator(i)) do 
		TMP:=TMP+LeadingCoefficient(j)*t^(Degree(Denominator(i))-Degree(j));
	end for;
	Append(~CoeffNewf,TMP);
end for;
Newf:=Parent(f)!CoeffNewf;

F`IsomorphicFunctionField:=FunctionField(Newf);
F`Cf:=Cf;
end if;
F`IsomorphicFunctionField`Fin:=0;
F`IsomorphicFunctionField`IsomorphicFunctionField:=F;
F`IsomorphicFunctionField`Cf:=F`Cf;
return F`IsomorphicFunctionField,F`Cf;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic BinaryRep(n::RngIntElt)->SeqEnum
{Compute binary representation of an integer n}
L:=[];
if n lt 0 then 
	n:=Abs(n);
	help:=-1;
else;
	help:=1;
end if;

while n gt 0 do
	Append(~L,help*Integers()!(n mod 2));
	n:=n div 2;
end while;

return L;

end intrinsic;
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic TransMap(z::FldFunElt,F::FldFun)->FldFunElt
{Input: z element of function field F with indeterminate T, output: z element of function field F with indeterminate 1/T }

K:=Parent(z);
KT:=BaseField(K);
T:=KT.1;
Coeffs:=Eltseq(z);
d:=K`Cf;
Newz:=F![Evaluate(Coeffs[i],1/T)*(1/T)^(d*(i-1)):i in [1..Degree(F)]];

return Newz;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



intrinsic Eval(F::FldFun,z::RngUPolElt)->FldFunElt
{Evaluates Polynomial in F.1}

L:=Eltseq(z);
if #L gt Degree(F) then
	print"Error in Eval";
	return z;
end if;

return F!(L cat [0:i in [1..Degree(F)-#L]]);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////End of  Helpfunction for function fields /////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////Helpfunction for Lists////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////

//Remark: Since the idealfactors are represented by [p(x),1,2] we have to deal with lists!
//////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Sort(L::SeqEnum,SortL::SeqEnum)->SeqEnum
{Gives Bijection between L and SortL}

Per:=[];
for i in [1..#L] do

	j:=Position(L,SortL[i]);
	Append(~Per,j);
	L[j]:=-2;

end for;

return Per;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Sort(L::List)->List
{Sorts a list}

Level1:=[**];
L1:=[i[1]: i in L];
Sort1:=Sort(L1);
for i in Sort1 do
	Append(~Level1,L[Position(L1,i)]);
	L1[Position(L1,i)]:=0;
end for;
Level2:=[**];
j:=1;
for p in SetToSequence(Set(Sort1)) do
	TempP:=[];
	while p eq  Sort1[j] do
		Append(~TempP,Level1[j]);	
		if j eq #Sort1 then break; end if;
		j:=j+1;
	end while;
	L2:=[i[2]: i in TempP];
	Sort2:=Sort(L2);
	
	for i in Sort2 do
		Append(~Level2,TempP[Position(L2,i)]);
		L2[Position(L2,i)]:=0;
	end for;
end for;

return Level2;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic Sort2(L::List)->List
{Helpmethod for Sort}

Step1:=Sort(SetToSequence(Set([i[1]:i in L])));
HelpList:=[*[* *]:i in [1..#Step1]*];
for j in [1..#Step1] do
	for i in L do
		if i[1] eq Step1[j] then
			Append(~HelpList[j],i);
		end if;
	end for;
	Step2:=Sort(SetToSequence(Set([ii[2]:ii in HelpList[j]])));
	HelpList2:=[**];
	for kk in [1..#Step2] do

	for mm in HelpList[j]   do
		if mm[2] eq Step2[kk] then 
			Append(~HelpList2,mm);
		end if;
	end for;
	
	end for;
HelpList[j]:=HelpList2;
end for;
temp:=[* *];
for i in HelpList do
	temp:=temp cat i;
end for;
return temp;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic Compare(list:: SeqEnum)->RngIntElt
{compares two lists}
Pols:=Set([i[1]:i in list]);
Numbers:=[];
run:=0;
    for i in Pols do
      temp:=[];
      for j in list do
      	if i eq j[1] then temp:=Append(temp,j[2]);end if;
      end for;
      Append(~Numbers,Set(temp));
    end for; 
return #&join Numbers;

end intrinsic

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic 'in'(L1::List,L2::List)->BoolElt
{Some special helpfunction}

if #L2 eq 0 or #L1 eq 0 then return false,0; end if;
for i in [1..#L2] do
	if L1[1] eq L2[i][1] and L1[2] eq L2[i][2] then return true,i; end if;  
end for;

return false,0;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
/////////Divisor Arithmetic///////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Place(P::Rec)->Rec
{}

require IsPrimeIdeal(P): "Argument should be a prime ideal";

K:=P`Parent;
if not assigned K`IsomorphicFunctionField then
	K`IsomorphicFunctionField:=InftyField(K);
end if;

if not assigned K`Fin then

	K`IsomorphicFunctionField:=InftyField(K);
	return rec<PlaceRecord|FiniteIdeal:=P,InfiniteIdeal:=ideal(K`IsomorphicFunctionField,K`IsomorphicFunctionField!1),FactorizationString:=SumListToString((P^1)`Factorization)>;
	
else

	if K`Fin eq 1 then
	
	return rec<PlaceRecord|FiniteIdeal:=P,InfiniteIdeal:=ideal(K`IsomorphicFunctionField,K`IsomorphicFunctionField!1),FactorizationString:=SumListToString((P^1)`Factorization)>;	
	else	
	return rec<PlaceRecord|FiniteIdeal:=ideal(K`IsomorphicFunctionField,K`IsomorphicFunctionField!1),InfiniteIdeal:=P,FactorizationString:=Sprintf( "P(%o,%o)", 1/P`Parent!P`IntegerGenerator,P`Position)  >;
	
	end if;
	
end if;	

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic '+'(D1::Rec,D2::Rec)->Rec
{}

Dfin:=D1`FiniteIdeal*D2`FiniteIdeal;
Dinf:=D1`InfiniteIdeal*D2`InfiniteIdeal;

temp1:=SumListToString(Dfin`Factorization);
temp2:=SumListToString2(Dinf`Factorization);

if #temp1 gt 0 and #temp2 gt 0 then
	D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
else
	D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat temp2>;
end if;
return D;


end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic '-'(D1::Rec,D2::Rec)->Rec
{}

Dfin:=D1`FiniteIdeal*(D2`FiniteIdeal)^-1;
Dinf:=D1`InfiniteIdeal*(D2`InfiniteIdeal)^-1;

temp1:=SumListToString(Dfin`Factorization);
temp2:=SumListToString2(Dinf`Factorization);

if #temp1 gt 0 and #temp2 gt 0 then
	D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
else
	D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat temp2>;
end if;
return D;


end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic '*'(k::RngIntElt,D::Rec)->Rec
{}

Dfin:=D`FiniteIdeal^k;
Dinf:=D`InfiniteIdeal^k;

temp1:=SumListToString(Dfin`Factorization);
temp2:=SumListToString2(Dinf`Factorization);

if #temp1 gt 0 and #temp2 gt 0 then
	D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
else
	D:=rec<PlaceRecord|FiniteIdeal:=Dfin,InfiniteIdeal:=Dinf,FactorizationString:=temp1 cat temp2>;
end if;
return D;


end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Divisor(I::Rec)->Rec
{}
K:=I`Parent;
if not assigned K`Fin then
	K`Fin:=1;
end if;
if not assigned  K`IsomorphicFunctionField then
	K`IsomorphicFunctionField:=InftyField(K);
end if;
if not assigned (I^1)`Factorization and K`Fin eq 1 then 
	return rec<PlaceRecord|FiniteIdeal:=ideal(K,K!1),InfiniteIdeal:=ideal(K`IsomorphicFunctionField,K`IsomorphicFunctionField!1),FactorizationString:="">;
end if;
if not assigned (I^1)`Factorization and K`Fin eq 0 then 
	return rec<PlaceRecord|FiniteIdeal:=ideal(K`IsomorphicFunctionField,K`IsomorphicFunctionField!1),InfiniteIdeal:=ideal(K,K!1),FactorizationString:="">;
end if;
if K`Fin eq 1 then 
	return rec<PlaceRecord|FiniteIdeal:=I,InfiniteIdeal:=ideal(K`IsomorphicFunctionField,K`IsomorphicFunctionField!1),FactorizationString:=SumListToString((I^1)`Factorization)>;
else	
	return rec<PlaceRecord|FiniteIdeal:=ideal(K`IsomorphicFunctionField,K`IsomorphicFunctionField!1),InfiniteIdeal:=I,FactorizationString:=SumListToString2((I^1)`Factorization)>;
end if;

end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic Divisor(z::FldFunElt)->Rec
{}
K:=Parent(z);
if z eq 0 then return Divisor(K!1);end if;
Ifin:=ideal(K,z)^1;
Iinf:=&*[i^(PValuation(z,i)): i in PlacesAtInfinity(K)];

temp1:=SumListToString(Ifin`Factorization);
temp2:=SumListToString2(Iinf`Factorization);

if #temp1 gt 0 and #temp2 gt 0 then
	D:=rec<PlaceRecord|FiniteIdeal:=Ifin,InfiniteIdeal:=Iinf,FactorizationString:=temp1 cat "+(" cat temp2 cat " )">;
else
	D:=rec<PlaceRecord|FiniteIdeal:=Ifin,InfiniteIdeal:=Iinf,FactorizationString:=temp1 cat temp2>;
end if;
return D;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

/*//////////////////////////////////////////////////////////////////////
intrinsic InfDiv(z::FldFunElt)->Rec
{}
K:=Parent(z);
if z eq 0 then return Divisor(K!1);end if;
return Divisor(&*[i^(PValuation(z,i)): i in PlacesAtInfinity(K)]);

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////*/
intrinsic PolDiv(z::FldFunElt)->Rec
{}
F:=Parent(z);
if z eq 0 then return Divisor(F!1);end if;

Finteprimes:=[];
Infinteprimes:=[];
L1,L2:=Support(Divisor(z));

for i in [1..#L2] do
	if L2[i] lt 0 then
		if L1[i] in PlacesAtInfinity(F) then
			Append(~Infinteprimes,L1[i]^(-L2[i]));
		else
			Append(~Finteprimes,L1[i]^(-L2[i]));
		end if;	
	end if;
	
end for;
if #Finteprimes eq 0 then

	Dfin:=Divisor(F!1);
	else
	Dfin:=Divisor(&*Finteprimes);
end if;

if #Infinteprimes eq 0 then

	Dinf:=Divisor(F!1);
	else
	Dinf:=Divisor(&*Infinteprimes);
end if;



return Dfin+Dinf;


end intrinsic;

/*//////////////////////////////////////////////////////////////////////
intrinsic HeightDiv(z::FldFunElt)->Rec
{}
F:=Parent(z);
if z eq 0 then return Divisor(F!1);end if;

Finteprimes:=[];
Infinteprimes:=[];
L1,L2:=Support(Divisor(z));

for i in [1..#L2] do

		if not L1[i]`Parent eq F then
			Append(~Infinteprimes,L1[i]^(Abs(L2[i])));
		else
			Append(~Finteprimes,L1[i]^(Abs(L2[i])));
		end if;	
	
end for;
if #Finteprimes eq 0 then

	Dfin:=Divisor(F!1);
	else
	Dfin:=Divisor(&*Finteprimes);
end if;

if #Infinteprimes eq 0 then

	Dinf:=Divisor(F!1);
	else
	Dinf:=Divisor(&*Infinteprimes);
end if;



return Dfin+Dinf;


end intrinsic;
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
*/

intrinsic Support2(z::FldFunElt)->SeqEnum
{}
D:=Divisor(z);
F:=D`FiniteIdeal`Parent;
I:=(D`FiniteIdeal);
Lfin:=RationalRadical(I);
FinitePrimes:=[];
FiniteExponents:=[];
for i in Lfin do
	TMP:=	[PValuation(z,J):J in F`PrimeIdeals[i]];
	for j in [1..#TMP] do
		if TMP[j] gt 0 then
				Append(~FinitePrimes,F`PrimeIdeals[i,j]);
				Append(~FiniteExponents,TMP[j]);
		end if;
	end for;

end for;


InfinitePrimes:=[];
InfiniteExponents:=[];
for i in PlacesAtInfinity(F) do
	a:=PValuation(z,i) ;
	if a gt 0 then
	Append(~InfinitePrimes,i);
	Append(~InfiniteExponents,a);
	end if;
end for;

return InfinitePrimes cat FinitePrimes,InfiniteExponents cat FiniteExponents;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Support(D::Rec)->SeqEnum
{}
K:=D`FiniteIdeal`Parent;
L1:=((D`FiniteIdeal)^1)`Factorization;
FinitePrimes:=[];
FiniteExponents:=[];
for i in L1 do
	Append(~FinitePrimes,K`PrimeIdeals[i[1],i[2]]);
	Append(~FiniteExponents,i[3]);
end for;

L2:=((D`InfiniteIdeal)^1)`Factorization;
PAI:=PlacesAtInfinity(K);
InfinitePrimes:=[];
InfiniteExponents:=[];
for i in L2 do
	Append(~InfinitePrimes,PAI[i[2]]);
	Append(~InfiniteExponents,i[3]);
end for;

return InfinitePrimes cat FinitePrimes,InfiniteExponents cat FiniteExponents;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic DEGREE(D::Rec)->RngIntElt
{Determines the Degree of the divisor D}
K:=D`FiniteIdeal`Parent;
L1:=((D`FiniteIdeal)^1)`Factorization;
if #L1 gt 0 then
	dfin:=&+[i[3]*Degree(K`PrimeIdeals[i[1],i[2]]): i in L1];
else
	dfin:=0;
end if;

L2:=((D`InfiniteIdeal)^1)`Factorization;
if #L2 gt 0 then
PAI:=PlacesAtInfinity(K);
	dinf:=&+[i[3]*Degree(PAI[i[2]]): i in L2];
else
	dinf:=0;
end if;	

return dfin+dinf;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Hight(D::Rec)->RngIntElt
{}

Supp,Expos:=Support(D);
if #Expos eq 0 then
	return 0,0;
else
	return &+[Abs(Expos[i])*Degree(Supp[i]):i in [1..#Expos]],Maximum([Degree(Supp[i]):i in [1..#Expos]]);
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
////////////////Divisor-Reduction/////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ElementaryReductionFast(D::Rec,A::Rec)->Rec
{}

//print"D",D`FactorizationString;

if DEGREE(A) eq 0 then  
	return D,0,D`FiniteIdeal`Parent!0;
end if;

r:=Floor(DEGREE(D)/Degree(D`FiniteIdeal`Parent));
//print"JOOOOOOOOOO",DEGREE(D-r*A);

B,succMin:=RRSpace(D-r*A);

//print"succ min",succMin;
k:=-Maximum(0,Ceiling(succMin[1]));
r:=r+k;
return D+Divisor(B[1])-r*A,r,B[1];
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ElementaryReductionFast(D::DivFunElt,A::DivFunElt)->Rec
{}
F:=FunctionField(D);
//print"D",D`FactorizationString;
if Degree(A) eq 0 then  
	return D,0,F!0;
end if;

r:=Floor(Degree(D)/Degree(F));
//print"JOOOOOOOOOO",DEGREE(D-r*A);

B,_,_,_,succMin:=RRSpace(D-r*A);

//print"succ min",succMin;
k:=-Maximum(0,Ceiling(succMin[1]));
r:=r+k;

return D+PrincipalDivisor(B[1])-r*A,r,B[1];
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Summands(D::Rec)->SeqEnum
{Binary dissction of a divosor}
K:=D`FiniteIdeal`Parent;
Divis,Coeffs:=Support(D);
TheDi:=[];

BinaryCeoffs:=[BinaryRep(i):i in Coeffs];

max:=Maximum([#ii:ii in BinaryCeoffs]);
L:=[1..#Coeffs];
H:=[];
for i in [1..max] do

	temp:=Divisor(K!1);
	L:=SetToSequence(Set(L) diff Set(H));
	for j in L do
		
		if IsDefined(BinaryCeoffs[j],i) then
			if Abs(BinaryCeoffs[j,i]) eq 1 then
			
				temp:=temp+BinaryCeoffs[j,i]*Place(Divis[j]);
			end if;
		else
			Append(~H,j);
		end if;
		
	end for;
	if #temp`FactorizationString gt 0 then
	TheDi[i]:=temp;
	end if;
end for;

return TheDi;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Summands(D::DivFunElt)->SeqEnum
{Binary dissction of a divosor in the Magma setting}
K:=FunctionField(D);
Divis,Coeffs:=Support(D);
TheDi:=[];

BinaryCeoffs:=[BinaryRep(i):i in Coeffs];

max:=Maximum([#ii:ii in BinaryCeoffs]);
L:=[1..#Coeffs];
H:=[];
for i in [1..max] do

	temp:=PrincipalDivisor(K!1);
	L:=SetToSequence(Set(L) diff Set(H));
	for j in L do
		
		if IsDefined(BinaryCeoffs[j],i) then
			if Abs(BinaryCeoffs[j,i]) eq 1 then
			
				temp:=temp+BinaryCeoffs[j,i]*Divis[j];
			end if;
		else
			Append(~H,j);
		end if;
		
	end for;
	if #Support(temp) gt 0 then
	TheDi[i]:=temp;
	end if;
end for;

return TheDi;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic SupportReduction(D::Rec,A::Rec)->Rec
{}
K:=D`FiniteIdeal`Parent;
Divis,Coeffs:=Support(D);
if #Divis le 1 then
	return D,0,K!1;
end if;

DD:=Divisor(K!1);
TheRs:=[];
TheAs:=[];

for i in [1..#Coeffs] do
		DD,r,a:=ElementaryReductionFast(Coeffs[i]*Place(Divis[i])+DD,A);
		//print"supp";DD`FactorizationString;
		TheRs[i]:=r;
		TheAs[i]:=a;

end for;

return DD,&+[TheRs[i]:i in [1..#TheRs]],&*[ TheAs[i]:i in [1..#TheAs]];


end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic SupportReduction(D::DivFunElt,A::DivFunElt)->DivFunElt
{Support reduction in Magma setting}
K:=FunctionField(D);
Divis,Coeffs:=Support(D);
if #Divis le 1 then
	return D,0,K!1;
end if;

DD:=PrincipalDivisor(K!1);
TheRs:=[];
TheAs:=[];

for i in [1..#Coeffs] do
		DD,r,a:=ElementaryReductionFast(Coeffs[i]*Divis[i]+DD,A);
		//print"supp";DD`FactorizationString;
		TheRs[i]:=r;
		TheAs[i]:=a;

end for;

return DD,&+[TheRs[i]:i in [1..#TheRs]],&*[ TheAs[i]:i in [1..#TheAs]];


end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic HightReduction(D::Rec,A::Rec)->Rec
{}
K:=D`FiniteIdeal`Parent;
TheDi:=Summands(D);
TheRs:=[];
TheAs:=[];

for i in [1..#TheDi] do
	if IsDefined(TheDi,i) then
		DD,r,a:=SupportReduction(TheDi[i],A);
		TheDi[i]:=DD;
		TheRs[i]:=r;
		TheAs[i]:=a;
	else
		TheRs[i]:=0;
		TheAs[i]:=K!1;
	end if;
end for;
//print"zwischencheck1",TheRs,TheAs;

//DD:=Divisor(K!1);
DD:=TheDi[#TheDi];
fac:=2;
for j:=#TheDi-1 to 1 by  -1 do
	if IsDefined(TheDi,j) then
		DD,r,a:=ElementaryReductionFast(TheDi[j]+fac*DD,A);
	//	print"test";r,a,(TheDi[j]+fac*DD)`FactorizationString;
		TheRs[j]:=TheRs[j]+r;
		TheAs[j]:=TheAs[j]*a;
		fac:=2;
	else
		TheRs[j]:=0;
		TheAs[j]:=K!1;
		fac:=fac*2;
	end if;
end for;
//print"zwischencheck2",TheRs,TheAs;

if not IsDefined(TheDi,1) then 
	DD:=Integers()!(fac/2)*DD;
end if;
if #TheRs eq 0 then
	return DD,0,K!1;
else
	return DD,&+[2^(i-1)*TheRs[i]:i in [1..#TheRs]],&*[ TheAs[i]^(2^(i-1)):i in [1..#TheAs]];
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic HightReduction(D::DivFunElt,A::DivFunElt)->DivFunElt
{Hight Reduction in the magma setting}
K:=FunctionField(D);
TheDi:=Summands(D);
TheRs:=[];
TheAs:=[];

for i in [1..#TheDi] do
	if IsDefined(TheDi,i) then
		DD,r,a:=SupportReduction(TheDi[i],A);
		TheDi[i]:=DD;
		TheRs[i]:=r;
		TheAs[i]:=a;
	else
		TheRs[i]:=0;
		TheAs[i]:=K!1;
	end if;
end for;
//print"zwischencheck1",TheRs,TheAs;

//DD:=Divisor(K!1);
DD:=TheDi[#TheDi];
fac:=2;
for j:=#TheDi-1 to 1 by  -1 do
	if IsDefined(TheDi,j) then
		DD,r,a:=ElementaryReductionFast(TheDi[j]+fac*DD,A);
	//	print"test";r,a,(TheDi[j]+fac*DD)`FactorizationString;
		TheRs[j]:=TheRs[j]+r;
		TheAs[j]:=TheAs[j]*a;
		fac:=2;
	else
		TheRs[j]:=0;
		TheAs[j]:=K!1;
		fac:=fac*2;
	end if;
end for;
//print"zwischencheck2",TheRs,TheAs;

if not IsDefined(TheDi,1) then 
	DD:=Integers()!(fac/2)*DD;
end if;
if #TheRs eq 0 then
	return DD,0,K!1;
else
	return DD,&+[2^(i-1)*TheRs[i]:i in [1..#TheRs]],&*[ TheAs[i]^(2^(i-1)):i in [1..#TheAs]];
end if;
end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic SumListToString(list)->MonStgElt
{Technical function to write down a factorization in pretty form. For internal use only}
if #list eq 0 then return ""; end if;
R<t>:=Parent(list[1,1]);
str:="";
run:=0;
for x in list do
	run:=run+1;	
  if x[3] ne 1 then str:= str cat Sprintf(" %o*",x[3]) ; end if;
 	 if run eq #list then
	  str:=str cat Sprintf( "P(%o,%o)", R!x[1],x[2]);
	  else
	  str:=str cat Sprintf( "P(%o,%o)+", R!x[1],x[2]);
      end if;
end for;
return Substring(str,1,#str);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic SumListToString2(list)->MonStgElt
{Technical function to write down a factorization in pretty form. For internal use only.
This is for the infinite part of the Divisor}
if #list eq 0 then return ""; end if;
str:="";
run:=0;
for x in list do
	run:=run+1;	
  if x[3] ne 1 then str:= str cat Sprintf(" %o*",x[3]) ; end if;
 	 if run eq #list then
	  str:=str cat Sprintf( "P(1/t,%o)", x[2]);
	  else
	  str:=str cat Sprintf( "P(1/t,%o)+",x[2]);
      end if;
end for;
return Substring(str,1,#str);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
/////End Divisor Arithmetic///////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
/////Weak Approximation Theorem///////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////	
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

/*intrinsic 'in'(P::Rec,L::SeqEnum)->BoolElt
{}

for i in L do
	if P eq i then return true; end if;
end for;
return false;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic WeakApp(Elements::SeqEnum,InfPlaces::SeqEnum,FinPlaces::SeqEnum,Values::SeqEnum,q::RngUPolElt)->FldFunElt
{}
if not #Elements eq #InfPlaces+#FinPlaces or not #Values eq #InfPlaces+#FinPlaces or #Elements eq 0 then
	print "Number of sequences are not compatible";
	return 0;
end if;

K:=Parent(Elements[1]);
kt:=PolynomialRing(ConstantField(K));
Kinf:=InftyField(K);
PrimePols:=SetToSequence(Set([i`IntegerGenerator:i in FinPlaces]));
for p in PrimePols do
	Generators(K,p);
end for;

if not q eq 0 then 
	Generators(Kinf,kt.1);
end if;


FinElements:=[Elements[i]:i in [1..#FinPlaces]];
FinVals:=[Values[i]:i in [1..#FinPlaces]];
FinHelpVals:=[];
for i in FinVals do
	if i gt -1 then 
		Append(~FinHelpVals,i+1);
	else
		Append(~FinHelpVals,1);
	end if;
end for;

InfElements:=[TransMap(Elements[i],Kinf):i in [#FinPlaces+1..#InfPlaces+#FinPlaces]];
min:=Minimum( &cat[[Floor(PValuation(j,i)/i`e):j in InfElements]:i  in PlacesAtInfinity(K)]);
InfVals:=[Values[i]:i in [#FinPlaces+1..#InfPlaces+#FinPlaces]];
min2:=Minimum([Floor(i/InfPlaces[i]`e):i in [1..#InfVals]]);
InfHelpVals:=[];
InfHelpVals2:=[];
for i in [1..#InfPlaces] do
	if min2 lt 0 then
	
		if InfVals[i] gt -1 then
			Append(~InfHelpVals2,InfVals[i]+1-min2*InfPlaces[i]`e);
		else 
			Append(~InfHelpVals2,1-min2*InfPlaces[i]`e);
		end if;	
	else	
		if InfVals[i] gt -1 then
			Append(~InfHelpVals2,InfVals[i]+1);
		else 
			Append(~InfHelpVals2,1);
		end if;	
	end if;
	
	
	if min lt 0 then
	
		if InfVals[i] gt -1 then
			Append(~InfHelpVals,InfVals[i]+1-min*InfPlaces[i]`e);
		else 
			Append(~InfHelpVals,1-min*InfPlaces[i]`e);
		end if;	
			InfElements[i]:=InfElements[i]*kt.1^-min;
	else	
		if InfVals[i] gt -1 then
			Append(~InfHelpVals,InfVals[i]+1);
		else 
			Append(~InfHelpVals,1);
		end if;	
	end if;
end for;

if min lt 0 then 
	min:=-min;
else
	min:=0;
end if;

if min2 lt 0 then 
	min2:=-min2;
else
	min2:=0;
end if;

RestElements:=[];
RestVals:=[];
for jj in Kinf`PrimeIdeals[kt.1] do
	if not jj in InfPlaces then 
		Append(~RestElements,Kinf!0);
		Append(~RestVals,jj`e*min);
		Append(~InfPlaces,jj);
	end if;
end for;

print"Testi",InfHelpVals;
//Produce z_infty
alpha:=CRT(InfElements cat RestElements,[InfPlaces[j]^(InfHelpVals cat RestVals)[j]:j in [1..#InfPlaces]]);
beta:=CRT([InfPlaces[jj]`Generator^(InfVals)[jj]*kt.1^min2:jj in [1..#InfPlaces]] cat RestElements,[InfPlaces[j]^(InfHelpVals cat RestVals)[j]:j in [1..#InfPlaces]]);
z_inf:=alpha/Kinf!kt.1^min+beta/Kinf!kt.1^min2;

return TransMap(z_inf,K),alpha,beta;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////*/

intrinsic CompensateValue(~K,p,tree,exponents,~beta)
{tree is an interval [i..j] inside [1..#K`PrimeIdeals[p]] and exponents is a sequence of integers of length #tree.
The output is a power of the greatest common phi-polynomial of the tree, such that v_P >= exponents[P] for all P in the tree}

if &and[x le 0: x in exponents] then
    beta:=K!1;
    return;
end if;
level:=0;
phi:=0;
Values:=0;
GCPhi(~K,p,tree,~level,~phi,~Values);
mx:=Max([exponents[k]/Values[k]: k in [1..#tree]]);
if mx le 1 and #tree eq 1 then
    M:=Ceiling(exponents[1]/K`PrimeIdeals[p,tree[1]]`e);
    beta:=Eval(K,phi mod p^M);
else
    beta:=Eval(K,phi)^Ceiling(mx);
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Construct(i,~type,respol,s,u,~Ppol)
{This routine constructs a polynomial Ppol with integer coefficients such that: 
deg Ppol<m_i+1 and y^nu*R_i(Ppol)(y)=respol(y), where nu=ord_y(respol).
The non-negative integers s,u are the coordinates of the left endpoint of a segment of slope -type[i]`slope supporting N_i(Ppol).
}

require i le #type: "the first input is too large";
require Degree(respol) lt type[i]`f: "the degree of the 3rd argument is too large"; 
require u+s*type[i]`slope ge type[i]`f*(type[i]`e*type[i]`V+type[i]`h): "the point (s,u) is too low";
var:=type[i]`Phi^type[i]`e;
Ppol:=0;
if i eq 1 then
	height:=u-Degree(respol)*type[i]`h;
	p:=type[1]`IntegerGenerator;
	mappitemp:=type[1]`Redmap;
	Ftemp:=Codomain(mappitemp);
	mappi:=mappitemp^(-1); 
    for a in Reverse(Coefficients(respol)) do
	lift:= PolynomialRing(Parent(p))![mappi(j):j in Eltseq(a,Ftemp)]; 
	Ppol:=Ppol*var+lift*type[1]`IntegerGenerator^height;
	height:=height+type[1]`h;
    end for; 
else	
    step:=type[i]`e*type[i]`V+type[i]`h;
    newV:=u-Degree(respol)*step-s*type[i]`V;
    im1:=i-1;
    for a in Reverse(Coefficients(respol)) do
	Pj:=0;
	if a ne 0 then
	    txp,sa:=Quotrem(type[im1]`invh*newV,type[im1]`e);
	    ua:=(newV-sa*type[im1]`h) div type[im1]`e; 
	    newrespol:=type[im1]`FqY!Eltseq(a*type[i]`z^txp,type[im1]`Fq);
	    Construct(im1,~type,newrespol,sa,ua,~Pj);
	end if;
	Ppol:=Ppol*var+Pj;
	newV:=newV+step;
    end for;
end if;        
Ppol:=Ppol*type[i]`Phi^s;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic ConvertLogs(~type,log,~class)
{log[1] is not used. The product of all Phi_i^log[i] for i>0 should have integer value M.
The output is the class of this product divided by p^M }
//wurde noch nicht Ã¼bersetzt.


vector:=log;
z:=0;
class:=PrimeField(type[1]`Fq)!1;
for i:=Degree(vector)-1 to 1 by -1 do
    ti:=vector[i+1] div type[i]`e;
    Z(~type,i,~z);
    class*:=z^ti;
    vector:=vector-ti*type[i]`logGamma;
    Truncate(~vector);
end for;
end intrinsic;

///////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic CrossedValues(~K,p)
{Rows of Mat indexed by phi_Q and columns by w_P:=v_P/e(P/p)
}

for tree in K`TreesIntervals[p] do
    position:=tree[1]-1;
    Mat:=Matrix(Rationals(),#tree,#tree,[]);
    for j:=1 to #tree-1 do
	t1:=position+j;
	m1:=Degree(K`PrimeIdeals[p,t1]`Type[#K`PrimeIdeals[p,t1]`Type]`Phi);
	for k:=j+1 to #tree do
	    t2:=position+k;
	    inc:=0;
	    IndexOfCoincidence(~K`PrimeIdeals[p,t1]`Type,~K`PrimeIdeals[p,t2]`Type,~inc);
	    Ref1:=Append(K`PrimeIdeals[p,t1]`Type[inc]`Refinements,[* K`PrimeIdeals[p,t1]`Type[inc]`Phi,K`PrimeIdeals[p,t1]`Type[inc]`slope *]);
	    Ref2:=Append(K`PrimeIdeals[p,t2]`Type[inc]`Refinements,[* K`PrimeIdeals[p,t2]`Type[inc]`Phi,K`PrimeIdeals[p,t2]`Type[inc]`slope *]);
	    minlength:=Min(#Ref1,#Ref2);
	    ii:=2;
	    while ii le minlength and Ref1[ii,1] eq Ref2[ii,1] do 
		ii+:=1;    
	    end while;
	    minslope:=Min([Ref1[ii-1,2],Ref2[ii-1,2]]);
	    entry:=(K`PrimeIdeals[p,t1]`Type[inc]`V+minslope)/(K`PrimeIdeals[p,t1]`Type[inc]`prode*Degree(K`PrimeIdeals[p,t1]`Type[inc]`Phi));
	    Mat[k,j]:=Degree(K`PrimeIdeals[p,t2]`Type[#K`PrimeIdeals[p,t2]`Type]`Phi)*entry;
	    Mat[j,k]:=m1*entry;
	end for;
    end for;
    for t in tree do
	K`PrimeIdeals[p,t]`CrossedValues:=RowSequence(Mat)[t-position];
    end for;
end for;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic CRT(elements::SeqEnum[FldFunElt],ideals::SeqEnum[Rec])->FldFunElt
{
Compute  x congruent  to elements[j] mod ideals[j] for every j.
Integrality of the given elements is not checked!
}


r:=#ideals;
require r eq #elements: "The two lists must have the same length";
if r eq 0 then return 0; end if;
if r eq 1 then return elements[1]; end if;
K:=Parent(elements[1]);
kt:=PolynomialRing(ConstantField(K));
require &and[x in K: x in elements]: "Elements should belong to the same number field";
//require &and[IsIntegralM(x): x in elements]: "Elements should all be integral";
require &and[K eq x`Parent: x in ideals]: "The number field of ideals and elements should be the same";
//require &and[IsIntegral(x): x in ideals]: "Ideals should be all integral";
ids:=[x^1: x in ideals]; // We assure they are IdealRecords
S:=[* *];
PrimePols:={@ @};
total:=0;
for i:=1 to r do
    list:=[Prune(x): x in ids[i]`Factorization];
    total+:=#list;
	for entries in list do
		if not entries in S then 
			Append(~S,entries);
		end if;
	end for;
   // S join:=Set(list);
    PrimePols join:={@ x[1]: x in list @};
end for;
require #S eq total: "Ideals must be pairwise coprime.";
if #PrimePols eq 0 then return 0; end if;
ListMaxExps:=[];
MaxMaxExps:=[];
Allcp:=[];
cps:=0;
for p in PrimePols do
    cp:=[K!0: i in [1..r]];
    nprimes:=#K`PrimeIdeals[p];
    exponents:=[0: i in [1..nprimes]];
    indices:=exponents;
    MaxExps:=[0: i in [1..r]];
    for i in [1..r] do
	list:=[x:x in ids[i]`Factorization| x[1] eq p];
	if #list gt 0 then 
	    MaxExps[i]:=Ceiling(Max([x[3]/K`PrimeIdeals[p,x[2]]`e: x in list]));
	    for x in list do
		exponents[x[2]]:=x[3];
		indices[x[2]]:=i;
	    end for;
	end if;
    end for;
    Append(~ListMaxExps,MaxExps);
    Append(~MaxMaxExps,p^(Max(MaxExps)));
    LocalCRT(~K,p,exponents,~cps);
    for i:=1 to r do
        list:=[cps[k]: k in [1..nprimes]|indices[k] eq i];
	if #list gt 0 then 
	    cp[i]:=&+list; 
	end if;
    end for;
    Append(~Allcp,cp);
end for;
solution:=K!0;
for i:=1 to r do
    ci:=K!0;
    for k in [1..#PrimePols] do
	   zeros:=[kt!0: i in [1..#PrimePols]] ;
	   zeros[k]:=1;
	   list:=MaxMaxExps;
	   list[k]:=PrimePols[k]^ListMaxExps[k,i];
	   ci+:=Allcp[k,i]*CRT(zeros,list);
     end for;
     solution+:=ci*elements[i];
end for;
den:=kt!Denominator(solution);
module:=den*&*MaxMaxExps;
num:=Eltseq(Numerator(solution));
num:=PolynomialRing(kt)![kt!x mod module: x in num];
solution:=Evaluate(num,K.1)/K!den;    
return solution;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic Different(~type,~different)
{}

e:=type[#type]`prode;
mu:=0;
if #type gt 1 then 
    nu:=&+[type[j]`slope/type[j]`prode: j in [1..#type-1]];
    mu:=(type[#type]`V/e)-nu;
end if;
ve:=Valuation(e,type[1]`IntegerGenerator);
rho:=0;
if ve ne 0 then 
    SFL(~type,e*ve);
    val:=0;
    dev:=[* *];
    Value(#type,~type,Derivative(type[#type]`Phi),~dev,~val);
    rho:=val-e*mu;
end if;
different:=e-1+rho;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic EqualizeLogs(~log1,~log2)
{}

d:=Degree(log1)-Degree(log2);
if d ne 0 then
    tail:=[0: i in [1..Abs(d)]];
    if d gt 0 then
	log2:=Vector(Eltseq(log2) cat tail);
    else
	log1:=Vector(Eltseq(log1) cat tail);
    end if;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic GCPhi(~K,p,tree,~node,~phi,~Values)
{the output phi is the greatest common phi-polynomial of the tree.
Values is the sequence of all v_P(phi(theta)) for P in the tree.  
node is the level of phi}

i:=0;
node:=#K`PrimeIdeals[p,tree[1]]`Type;
if #tree gt 1 then
    for k in Exclude(tree,tree[1]) do
	IndexOfCoincidence(~K`PrimeIdeals[p,tree[1]]`Type,~K`PrimeIdeals[p,k]`Type,~i);
	if node gt i then
	    node:=i;
	end if;
    end for;
end if;
level:=K`PrimeIdeals[p,tree[1]]`Type[node];
if #level`Refinements eq 0 then
    phi:=level`Phi;
else
    phi:=level`Refinements[1,1];
end if;
Values:=[];
for i in tree do
    leveli:=K`PrimeIdeals[p,i]`Type[node];
    if #leveli`Refinements eq 0 then
	firstslope:=leveli`slope;
    else
	firstslope:=leveli`Refinements[1,2];	
    end if;
Append(~Values,(K`PrimeIdeals[p,i]`e div level`prode)*(level`V+firstslope));
end for;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Generators(K,p)
{}

_, _ := Montes(K,p);
nprimes:=#K`PrimeIdeals[p];
if nprimes eq 1 then 
    K`PrimeIdeals[p,1]`Generator:=K`PrimeIdeals[p,1]`LocalGenerator;
    return;
end if;

for tree in K`TreesIntervals[p] do
    pos:=tree[1];
    if #tree eq 1 and K`PrimeIdeals[p,pos]`e eq 1 then
	level:=K`PrimeIdeals[p,pos]`Type[1];
	gen:=Eval(K,level`Phi);
	if level`slope gt 1 then 
	    gen+:=p;
	end if;
	K`PrimeIdeals[p,pos]`Generator:=gen;
    end if;
end for;

if &and[assigned P`Generator: P in K`PrimeIdeals[p]] then
    return;
end if;


//print "ara multiplicadors";
// Computation of the multipliers
bps:=0;
LocalCRT(~K,p,[2: i in [1..nprimes]],~bps: Generators:=true);

//print "fets multiplicadors";
//   Computation of the generators
for i in [1..nprimes] do
    if not assigned K`PrimeIdeals[p,i]`Generator then
	gen:=K`PrimeIdeals[p,i]`LocalGenerator*bps[i];
	K`PrimeIdeals[p,i]`Generator:=gen+&+[bps[x]: x in Exclude([1..nprimes],i)];
    end if;
end for;

//Smaller size generators
for i in [1..nprimes] do
    numgen:=Numerator(K`PrimeIdeals[p,i]`Generator);
    dengen:=Parent(p)!Denominator(K`PrimeIdeals[p,i]`Generator);
    val:=Valuation(dengen,p)+1;
    if K`PrimeIdeals[p,i]`e eq 1 then 
	val+:=1; 
    end if;
    numcoeffs:=[(Parent(p)!i) mod p^val:i in Eltseq(numgen)];
    gcd:=GCD(numcoeffs);
    numcoeffs:=[x div gcd: x in numcoeffs];
    gen:=Evaluate(PolynomialRing(Parent(p))!numcoeffs,K.1)/dengen;
    //   gen:=Evaluate(PolynomialRing(Integers())!numcoeffs,K.1)/dengen;	
    if gen eq 1 then 
	gen:=K!p; 
    end if;
K`PrimeIdeals[p,i]`Generator:=gen;      
end for;
//print "fi generadors";
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic IndexOfCoincidence(~t1,~t2,~i)
{the types must correspond to different prime ideals}

require t1[1]`IntegerGenerator eq t2[1]`IntegerGenerator: "types attached to different prime numbers";
if t1[1]`Phi mod t1[1]`IntegerGenerator ne t2[1]`Phi mod t1[1]`IntegerGenerator then 
    i:=0;
else

i:=1;
while t1[i]`Phi eq t2[i]`Phi and t1[i]`slope eq t2[i]`slope and t1[i]`psi eq t2[i]`psi do
    i+:=1;
end while;	
end if;

end intrinsic;

intrinsic IndexOfCoincidence(t1::Rec, t2::Rec)-> RngIntElt
    { The index of coincidence of types t1 and t2. }

    i := 0;
    IndexOfCoincidence(~t1`Type, ~t2`Type, ~i);

    return i;
end intrinsic;

intrinsic IndexOfCoincidence(t1::SeqEnum, t2::SeqEnum)-> RngIntElt
    { }

    i := 0;
    IndexOfCoincidence(~t1, ~t2, ~i);

    return i;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic InitialLevel(map,p,Pol,psi,power: BAS:=false)-> Rec
{psi is a monic irreducible factor of Pol modulo p and power=ord_psi(Pol mod p)}

Kt<t>:=Parent(p);
Ktx<x>:=PolynomialRing(Kt);
map2:=map^(-1);
phi:=Ktx  ![map2(j):j in Coefficients(psi)];
level:=rec<TypeLevel| 
Phi:=phi, V:=0, prode:=1, prodf:=Degree(psi), omega:=power, cuttingslope:=0, Refinements:=[**], 
logPi:=Vector([1,0]), logPhi:=Vector([0,1]), IntegerGenerator:=p, Pol:=Pol, Phiadic:=[Ktx!0,Ktx!0,Ktx!0,Ktx!0],
sfl:=[0,0,0,0]
>;
level`Fq,level`map:=ResidueClassField(psi);
level`Redmap:=map;

if level`prodf gt 1 then  
    mmm,nnn:=HasAttribute(level`Fq,"PowerPrinting");
    if mmm and nnn then 
	AssertAttribute(level`Fq, "PowerPrinting", false); 
    end if;
    level`z:=(level`Fq).1;
    AssignNames(~(level`Fq),["z" cat IntegerToString(0)]);
else
    level`z:=-Coefficient(psi,0);
end if;
level`FqY:=PolynomialRing(level`Fq:Global:=false);
AssignNames(~(level`FqY),["Y" cat IntegerToString(0)]);
if BAS then 
    level`ProdQuots:=[Ktx.1^k: k in [0..level`prodf-1]];
    level`ProdQuotsVals:=[Rationals()!0:k in [1..level`prodf]];
end if;
return level;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
/*
intrinsic IntegralBasis(K::FldFun)->SeqEnum
{Compute a basis  of the maximal order ZK of K and the discriminant of K.}

if assigned K`IntegralBasis then 
    return K`IntegralBasis; 
end if;
d:=Discriminant(PolynomialRing(PolynomialRing(ConstantField(K)))!DefiningPolynomial(K));
print"disc",d;
h:=Factorization(d);
print"factorized disc",h;
primelist:=[i[1]: i in h];
K`IntegralBasis:=SIntegralBasis(K,primelist);
K`FactorizedDiscriminant:=[];
for p in primelist do
    d:=d div p^(2*K`LocalIndex[p]);
    Append(~K`FactorizedDiscriminant,[p, Valuation(d,p)]);
end for;
K`Discriminant:=d;
return K`IntegralBasis;
end intrinsic;*/

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Inversionloop(p,A,~xnum,~xden,phi,precision)
{}
anum:=A[1];
aden:=A[2];
pi:=p;
//zqq:=quo<Zp|pi^precision>;
piq:=p;
//zqqt<t>:=PolynomialRing(zqq);
Phip:=phi mod pi^precision; 
xnum :=xnum mod pi^precision;
x1num,x1den:=reduce(p,(2*piq^(xden+aden)-((anum mod pi^precision)*xnum)mod pi^precision) mod Phip,xden+aden); 
xnum,xden:=reduce(p,((xnum*x1num) mod pi^precision) mod Phip, xden+x1den);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic IsIntegralM(alpha::FldFunElt)->BoolElt
{}

K:=Parent(alpha);
DeNom:=PolynomialRing(ConstantField(K))!Denominator(alpha);
Facs:=Factorization(DeNom);
primes:=[i[1]:i in Facs];
for p in primes do
    _, _ := Montes(Parent(alpha),p);
    for P in Parent(alpha)`PrimeIdeals[p] do
	if PValuation(alpha,P) lt 0 then
	    return false;
	end if;
    end for;
end for;
return true;
end intrinsic;

//////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*intrinsic SearchPoles(alpha::FldFunElt)->SeqEnum
{}

K:=Parent(alpha);
DeNom:=PolynomialRing(ConstantField(K))!Denominator(alpha);
Facs:=Factorization(DeNom);
primes:=[i[1]:i in Facs];
Poles:=[* *];
Expos:=[];
for p in primes do
    MontesH(Parent(alpha),p);
    j:=0;
    for P in Parent(alpha)`PrimeIdeals[p] do
	j:=j+1;
	temp:=PValuation(alpha,P);
	if temp lt 0 then
	    Append(~Poles,[*p,j*]);
	    Append(~Expos,temp);
	end if;
    end for;
end for;
return Poles,Expos;
end intrinsic;

//////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////*/

intrinsic LastLevel(Phiadic,~type,side,dev: Lastpsi:=true)
{in type[1]`sfl[1] we store the exponent of the irreducible factor}

ord:=#type;
type[ord]`e:=1;
if ord gt 1 then 
    nur:=&+[type[j]`slope/type[j]`prode: j in [1..ord-1]]; 
    type[1]`sfl[1]:=Floor((type[ord]`V/type[ord]`prode)-nur);
end if;
if side[2] eq 0 then
    slope:=-side[1];
    type[ord]`h:=Integers()!slope;
    type[1]`Phiadic[1]:=Phiadic[1];
    type[1]`Phiadic[2]:=Phiadic[2];
    if Lastpsi then
	psi:=0;
	ResidualPolynomial(ord,~type,~dev,~psi);
	type[ord]`psi:=psi/LeadingCoefficient(psi);
	type[ord]`logGamma:=type[ord]`logPhi-type[ord]`h*type[ord]`logPi;
    end if;
else
    slope:=Infinity();
end if;
type[ord]`slope:=slope;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic Lift(class,P)->FldFunElt
{}

return Lift([class],P,1);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic Lift(class,P,m)->FldNumElt
{}
print"Muss noch Ã¼bersetzt werden Lift";
require m gt 0: "the third argument must be positive";
ll:=LocalLift(class,P,m);
exp:=Valuation(Denominator(ll),P`IntegerGenerator);
exponents:=[Q`e*exp: Q in P`Parent`PrimeIdeals[P`IntegerGenerator]];
exponents[P`Position]:=m;
mult:=0;
Multiplicator(~P,exponents,~mult);
return ll*mult;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic LocalCRT(~K,p,exponents,~Multiplicators: Generators:=false)
{}


nprimes:=#K`PrimeIdeals[p];
ntrees:=#K`TreesIntervals[p];
Pieces:=[K!0: i in [1..nprimes]];
MaxVTC:=[];
N:=0;
piece:=0;
for tree in K`TreesIntervals[p] do
    ValuesToCompensate:=[0: k in [1..#tree]]; 
    for t in tree do
	if exponents[t] gt 0 then
	    j:=t-tree[1]+1;
	    if Generators then
		extraden:=Max([0,-K`PrimeIdeals[p,t]`LogLG[1]]);
	    else
		extraden:=K`PrimeIdeals[p,t]`exponent;
	    end if;
	    expsTree:=[exponents[t]+extraden*K`PrimeIdeals[p,t]`e:t in tree];
	    MultPiece(~K`PrimeIdeals[p,t],tree,expsTree,~N,~piece);
	    Pieces[t]:=piece;
	    ValuesToCompensate[j]:=N+extraden;
	end if;
    end for;
Append(~MaxVTC,Max(ValuesToCompensate));
end for;
if ntrees eq 1 then
    Betas:=[K!1];
else   
    Compensations:=[];
    beta:=0;
    for i:=1 to ntrees do
	tree:=K`TreesIntervals[p,i];
	max:=Max([MaxVTC[k]: k in Exclude([1..ntrees],i)]);
	expsTree:=[exponents[t]+max*K`PrimeIdeals[p,t]`e: t in tree];
	CompensateValue(~K,p,tree,expsTree,~beta);
	Append(~Compensations,beta);
    end for;
    universe:=&*Compensations;
    Betas:=[universe/x: x in Compensations];
end if;
Multiplicators:=[K!0: i in [1..nprimes]];
for i:=1 to ntrees do
    for t in K`TreesIntervals[p,i] do
	if exponents[t] gt 0 then
	    mult:=Pieces[t]*Betas[i];
	    if Generators then
		extraden:=Max([0,-K`PrimeIdeals[p,t]`LogLG[1]]);
	    else
		extraden:=0;
		MultiplyByInverse(~mult,~K`PrimeIdeals[p,t],exponents[t]);
	    end if;
// simplification
//print "mult",mult;
	    den:=Parent(p)!Denominator(mult);
	    mx:=Max([Ceiling((exponents[k]+extraden)/K`PrimeIdeals[p,k]`e): k in [1..nprimes]]);
	    module:=den*p^mx;
	    num:=PolynomialRing(Parent(p))!Eltseq(Numerator(mult));
	    mult:=Evaluate(num mod module,K.1)/den;    
	    Multiplicators[t]:=mult;
//print "simplication",mult;
	end if;
    end for;
end for;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic Localize(alpha,p)->RngIntElt,RngIntElt,RngUPolElt
{output=den,exp,Pol such that alpha = (1/den)*Pol(theta)*p^exp, and den is coprime to p}

if alpha eq 0 then 
    return 1,0,PolynomialRing(Integers())!0;
end if;
num:=[Parent(p)!i:i in Eltseq(Numerator(alpha))];
valnum:=Min([Valuation(x,p): x in num]);
Denom:=Parent(p)!Denominator(alpha);
valden:=Valuation(Denom,p);//h2
den:=Parent(p)!(Denom/p^valden);

return den,valnum-valden,PolynomialRing(Parent(p))!num div p^valnum;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic LocalLift(~type,class,~numlift,~denlift)
{class should belong to the residue class field  type[r]`Fq. 
The output is a pair g,e such that g(theta)/p^e is a lift to a P-integral element in K
and deg g(x)<n_P}

require class in type[#type]`Fq: "Second argument must lie in the residue field of first argument";
i:=1;
while class notin type[i]`Fq do
	i+:=1;
end while;
if i eq 1 then 
    p:=type[1]`IntegerGenerator;
	mappitemp:=type[1]`Redmap;
	Ftemp:=Codomain(mappitemp);
	mappi:=mappitemp^(-1);
	numlift:= PolynomialRing(Parent(p))![mappi(j):j in Eltseq(class,Ftemp)];
	denlift:=0;
else
    expden:=Ceiling(type[i]`V/type[i]`prode);
    V:=type[i]`prode*expden;
    log:=V*type[i]`logPi;
    newclass:=0;
    ConvertLogs(~type,log,~newclass);
    H:=V div type[i-1]`e;
    elt:=type[i]`z^(type[i-1]`invh*H)*class*newclass^(-1);
    varphi:=type[i-1]`FqY!Eltseq(type[i]`Fq!elt,type[i-1]`Fq);
    lift:=0;
    Construct(i-1,~type,varphi,0,H,~lift);
    v1lift:=Min([Valuation(x,type[1]`IntegerGenerator): x in Coefficients(lift)]);
    numlift:=lift div type[1]`IntegerGenerator^v1lift;
    denlift:=expden-v1lift;
end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic LocalLift(class,P)->FldFunElt
{class should belong to the residue class field Z_K/P. 

The output is a lift to a P-integral element in K}
print"muss noch Ã¼bersetzt werden!!!!";

numlift:=0;
denlift:=0;
LocalLift(~P`Type,class,~numlift,~denlift);
return  Eval(P`Parent,numlift)/P`IntegerGenerator^denlift;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic LocalLift(class,P,m)->FldNumElt
{}
print"muss noch Ã¼bersetzt werden!!!!";

require m gt 0: "the third argument must be positive";
precision:=2*P`exponent+Ceiling(m/P`e);
SFL(~P`Parent,~P,precision*P`e-P`Type[#P`Type]`V);
Zp:=pAdicRing(P`IntegerGenerator,precision);
Zpx:=PolynomialRing(Zp);
phi:=Zpx!P`Type[#P`Type]`Phi;
pi:=UniformizingElement(Zp);
LGnum:=Zpx!Eltseq(Numerator(P`LocalGenerator),Integers());
LGden:=Max([0,-P`LogLG[1]]);
lftnum:=Zpx!0;
lftden:=0;
num:=0;
den:=0;
//Horner's rule
for i:=m to 1 by -1 do
    LocalLift(~P`Type,class[i],~num,~den);
    lftnum,lftden:=reduce((lftnum*LGnum) mod phi,lftden+LGden:QUO:=false);
    lftnum,lftden:=reduce(lftnum*pi^den+Zpx!num*pi^lftden,lftden+den:QUO:=false);
end for;
lftnum:=PolynomialRing(Integers())!lftnum;
if P`exponent ne 0 then
    lftnum:=lftnum mod Integers()!(pi^(lftden+Ceiling(m/P`e)));
end if;
return Evaluate(lftnum,P`Parent.1)/Integers()!(pi^lftden);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

// TIMINGS: Added output
intrinsic Montes(K::FldFun,p::RngUPolElt: Basis:=false)-> SeqEnum, SeqEnum
{}
require IsPrime(p): "First argument must be a prime polynomial";
Rt:=Parent(p);
Rxt<x>:=PolynomialRing(Rt);
RXT<T>:=BaseField(K);
Pol:=Rxt!DefiningPolynomial(K);
//require (CoefficientRing(Pol) eq Integers() and IsMonic(Pol)): "Number Field must be defined by a monic integral polynomial";

if not assigned K`localbasedata then
    K`localbasedata:=AssociativeArray();
    K`IndexBases:=AssociativeArray();
    //K`maxorderfinite:=AssociativeArray();
end if;   
if not assigned K`FactorizedPrimes then
    K`FactorizedPrimes:=[];
    K`PrimeIdeals:=AssociativeArray();
    K`LocalIndex:=AssociativeArray();
    K`TreesIntervals:=AssociativeArray();
    K`pBasis:=AssociativeArray();
    K`pHermiteBasis:=AssociativeArray();
    K`Times := [ ];
    K`SFLCount := 0;
end if;    
if p in K`FactorizedPrimes and (not Basis or IsDefined(K`pBasis,p)) then
    // TIMINGS: Added output
    return [], [];
end if;

Fp,map:=ResidueClassField(p);
Fpy<y>:=PolynomialRing(Fp:Global := false);
fa:=Factorization(Fpy![map(i): i in Coefficients(Pol)]);
totalindex:=0;   
OMReprs:=[];
TreesIntervals:=[];
right:=0;
BasisNums:=[];
BasisDens:=[];
for factor in fa do
    vprint montestalk,2: "Analyzing irreducible factor modulo p: ",factor[1];
    level:=InitialLevel(map,p,Pol,factor[1],factor[2]: BAS:=Basis);
    Leaves:=[];
    Montesloop(level,~Leaves,~totalindex,~BasisNums,~BasisDens: Basisloop:=Basis);
    Append(~TreesIntervals,[right+1..right+#Leaves]);  
    right+:=#Leaves;
    OMReprs cat:=Leaves;  
end for;
if #OMReprs eq 1 then
    OMReprs[1,#OMReprs[1]]`Phi:=Pol;
    OMReprs[1,#OMReprs[1]]`slope:=Infinity();
end if;
K`PrimeIdeals[p]:=[];
Psi:=0;
logLG:=0;
primeid:=rec<PrimeIdealRecord|Parent:=K,Pol:=Pol,IntegerGenerator:=p>;
for k:=1 to #OMReprs do
    primeid`Position:=k;
    primeid`Type:=OMReprs[k];
    primeid`e:=OMReprs[k][#OMReprs[k]]`prode;
    primeid`f:=OMReprs[k][#OMReprs[k]]`prodf; 
    PrescribedValue(~OMReprs[k],1,~Psi,~logLG);
    primeid`LocalGenerator:=Eval(K,Psi)*RXT!p^logLG[1];
    primeid`LogLG:=logLG;
    primeid`exponent:=OMReprs[k,1]`sfl[1];
    Append(~K`PrimeIdeals[p],primeid); 
end for;
Append(~K`FactorizedPrimes,p);
Sort(~K`FactorizedPrimes);
K`LocalIndex[p]:=totalindex;
K`TreesIntervals[p]:=TreesIntervals;
CrossedValues(~K,p);
if Basis then
	// war vorher drauÃŸen aus der if-schleife
    BasisDexp := [ Floor(x) : x in BasisDens ];
    K`pBasis[p]:=[Evaluate(BasisNums[k],K.1)/p^BasisDexp[k]: k in [1..Degree(K)]];
    // TIMINGS: Added output
    return BasisNums, BasisDexp;
else
    // TIMINGS: Added output
    return [], [];
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Montesloop(level,~Leaves,~totalindex,~BasisNums,~BasisDens: Basisloop:=false)
{}
	
Stack:=[[level]];
while #Stack gt 0 do	  
    type:=Stack[#Stack];
    Prune(~Stack);
    r:=#type;
vprint montestalk,2:  "Analyzing type of order ",r;
vprint montestalk,2:  "Phir=",type[r]`Phi;
    Phiadic,Quotients:=Taylor(type[1]`Pol,type[r]`Phi,type[r]`omega);
    sides:=[];
    devsEachSide:=[* *];
    Newton(r,~type,~Phiadic,~sides,~devsEachSide);
    vprint montestalk,3: "Sides of Newton polygon:",sides;
    lengthN:=type[r]`omega;
    indexN:=-type[r]`cuttingslope*(lengthN*(lengthN-1) div 2); 
    if lengthN eq 1 then
	vprint montestalk,2:  "Found a factor of depth  ",r-1;
	LastLevel(Phiadic,~type,sides[1],devsEachSide[1]);
	Append(~Leaves,type);  
	sides:=[];
	if Basisloop and r eq 1 and type[1]`cuttingslope eq 0 then
	    BasisNums cat:=[Quotients[1]*x: x in type[1]`ProdQuots];
	    BasisDens cat:=type[1]`ProdQuotsVals;
	end if;
    end if;
    prevh:=0;	
    for i:=#sides to 1 by -1 do  // GRAN FOR SIDES
	side:=sides[i];
	vprint montestalk,2:  "Analyzing side ",side;        
	type[r]`h:=-Numerator(side[1]);
	type[r]`e:=Denominator(side[1]);
	type[r]`slope:=-side[1];
	type[r]`invh:=InverseMod(type[r]`h,type[r]`e);
	lprime:=(1-type[r]`invh*type[r]`h) div type[r]`e;
	newPi:=Eltseq(type[r]`invh*type[r]`logPhi+lprime*type[r]`logPi);
	Append(~newPi,0);  
	type[r]`logGamma:=type[r]`e*type[r]`logPhi-type[r]`h*type[r]`logPi;
   	Ei:=Integers()!(side[4]-side[2]);
	Hi:=Integers()!(side[3]-side[5]);
	indexN+:=Ei*prevh+((Ei*Hi-Ei-Hi+(Ei div type[r]`e))div 2);

	prevh+:=Hi;
	respol:=0;
	ResidualPolynomial(r,~type,~devsEachSide[i],~respol);
        respol:=respol/LeadingCoefficient(respol);
	factors:=Factorization(respol);
//if terminal side we add a piece of basis
	if Basisloop then
	    lengthPQ:=#type[1]`ProdQuots;
	    terminals:=[Degree(x[1]): x in factors|x[2] eq 1];
	    nonterminals:=[Degree(x[1]): x in factors|x[2] ne 1];
	    efS:=0;
	    efrest:=0;
	    if #terminals gt 0 then 
		efS:=type[r]`e*&+terminals; 
	    end if;
	    if #nonterminals gt 0 then 
		efrest:=type[r]`e*Max(nonterminals); 
	    end if;
	    efmax:=Max([efS,efrest]);
	    step:=(type[r]`slope+type[r]`V)/type[r]`prode;
	    height:=(side[5]-side[4]*type[r]`V)/type[r]`prode;
	    lastabscissa:=Integers()!side[4];
	    EnlargePQ:=[];
	    EnlargePQVals:=[];
	    for abscissa:=lastabscissa to lastabscissa-efmax+1 by -1 do
		EnlargePQ cat:=[Quotients[abscissa]*x mod type[1]`Pol: x in type[1]`ProdQuots];
		EnlargePQVals cat:=[height+x: x in type[1]`ProdQuotsVals];
		height:=height+step;
	    end for;
	    if efS gt 0 and Basisloop then// hier war kein basisloop in der if-abfrage
		BasisNums cat:=EnlargePQ[1..lengthPQ*efS];
		BasisDens cat:=EnlargePQVals[1..lengthPQ*efS];              
		vprint montestalk,3: "Terminal side. Basis updated to ",BasisNums," with valuations ",BasisDens;                      
	    end if;
	end if;
	vprint montestalk,2: "Monic Residual Polynomial=",respol;
        vprint montestalk,3:  "Factors of R.P.:=",factors;            
// PETIT FOR FACTORS	
        for factor in factors do       
	    vprint montestalk,2: "Analyzing factor of the Res.Pol.",factor[1];
            ta:=type;  
            ta[r]`psi:=factor[1];
	    ta[r]`f:=Degree(ta[r]`psi);
	    Representative(~ta);
// IF REFINA-AVANÃ‡A
	    if Degree(ta[r]`Phi) eq Degree(ta[r+1]`Phi) then
		vprint montestalk,2:  "Refining. Cuttingslope=",-side[1];
		if #sides gt 1 or #factors gt 1 then
		    Append(~ta[r]`Refinements,[* ta[r]`Phi,ta[r]`slope *]);
		end if;
		ta[r]`cuttingslope:=-Integers()!side[1];
		ta[r]`Phi:=ta[r+1]`Phi;
		ta[r]`omega:=factor[2];
		Prune(~ta);  
	    else
		vprint montestalk,2:  "Proceeding to higher order";    
		ta[r+1]`omega:=factor[2];
		ta[r+1]`logPi:=Vector(newPi);
		vec:=-ta[r+1]`V *ta[r+1]`logPi;
		vec[r+2]:=1;
		ta[r+1]`logPhi:=Vector(vec); 
		if Basisloop and factor[2] gt 1 then
		    lef:=lengthPQ*ta[r]`e*ta[r]`f;
		    ta[1]`ProdQuots cat:=EnlargePQ[lengthPQ+1..lef];	
		    ta[1]`ProdQuotsVals cat:=EnlargePQVals[lengthPQ+1..lef];
		end if;
            end if; 
// FINAL IF REFINA-AVANÃ‡A
	    Append(~Stack,ta);
        end for;     // FINAL PETIT FOR FACTORS
    end for;         // FINAL GRAN FOR SIDES
    totalindex+:=type[r]`prodf*indexN;
    vprint montestalk, 2: "Added  ",type[r]`prodf*indexN," to the index";
end while;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic MontesloopFactors(level,~Leaves,~totalindex,mahler)
{}
	
Stack:=[[level]];
while #Stack gt 0 and totalindex le mahler do	  
    type:=Stack[#Stack];
    Prune(~Stack);
    r:=#type;
    Phiadic,Quotients:=Taylor(type[1]`Pol,type[r]`Phi,type[r]`omega);
    if Phiadic[1] eq 0 and Phiadic[2] eq 0 then 
	totalindex:=Infinity(); 
	return; 
    end if;
    sides:=[];
    devsEachSide:=[* *];
    Newton(r,~type,~Phiadic,~sides,~devsEachSide);
    lengthN:=type[r]`omega;
    indexN:=-type[r]`cuttingslope*(lengthN*(lengthN-1) div 2); 
    if lengthN eq 1 or Phiadic[1] eq 0 then
	LastLevel(Phiadic,~type,sides[1],0: Lastpsi:=false);
	Append(~Leaves,type);  
    end if;
    if Phiadic[1] eq 0 then
	type[1]`Pol:=Quotients[1];
	indexN+:=Integers()!sides[1,3]-sides[#sides,5];
    end if;
    if lengthN eq 1 then
	sides:=[];
    end if;
    prevh:=0;	
    for i:=#sides to 1 by -1 do  // GRAN FOR  COSTATS
	side:=sides[i];
	type[r]`h:=-Numerator(side[1]);
	type[r]`e:=Denominator(side[1]);
	type[r]`slope:=-side[1];
	type[r]`invh:=InverseMod(type[r]`h,type[r]`e);
	lprime:=(1-type[r]`invh*type[r]`h) div type[r]`e;
	newPi:=Eltseq(type[r]`invh*type[r]`logPhi+lprime*type[r]`logPi);
	Append(~newPi,0);  
	type[r]`logGamma:=type[r]`e*type[r]`logPhi-type[r]`h*type[r]`logPi;
   	Ei:=Integers()!(side[4]-side[2]);
	Hi:=Integers()!(side[3]-side[5]);
	indexN+:=Ei*prevh+((Ei*Hi-Ei-Hi+(Ei div type[r]`e))div 2);
	prevh+:=Hi;
	respol:=0;
	ResidualPolynomial(r,~type,~devsEachSide[i],~respol);
        respol:=respol/LeadingCoefficient(respol);
	factors:=Factorization(respol);
        for factor in factors do       
            ta:=type;  
            ta[r]`psi:=factor[1];
	    ta[r]`f:=Degree(ta[r]`psi);
	    Representative(~ta);
// IF REFINA-AVANÃ‡A
	    if Degree(ta[r]`Phi) eq Degree(ta[r+1]`Phi) then
		if #sides gt 1 or #factors gt 1 then
		    Append(~ta[r]`Refinements,[* ta[r]`Phi,ta[r]`slope *]);
		end if;
		ta[r]`cuttingslope:=-side[1];
		ta[r]`Phi:=ta[r+1]`Phi;
		ta[r]`omega:=factor[2];
		Prune(~ta);  
	    else
		ta[r+1]`omega:=factor[2];
		vec:=-ta[r+1]`V *ta[r+1]`logPi;
		vec[r+2]:=1;
		ta[r+1]`logPhi:=Vector(vec); 
		ta[r+1]`logPi:=Vector(newPi);
            end if; 
// FINAL IF REFINA-AVANÃ‡A
	    Append(~Stack,ta);
        end for;     
    end for; // FINAL GRAN FOR COSTATS
    totalindex+:=type[r]`prodf*indexN;
end while;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Multiplicator(~P,exponents,~mult)
{output mult is congruent to 1 modulo P^a_P and it has Q-value >= a_Q.
The output has a power of p as denominator; thus, if all a_Q>=0, the output is an algebraic integer}

p:=P`IntegerGenerator;
// part of the tree of P
treeP:=0;
TreeInterval(~P,~treeP);
N:=0;
bp:=0;
expsTree:=[exponents[i]+P`exponent*P`Parent`PrimeIdeals[p,i]`e:i in treeP];
MultPiece(~P,treeP,expsTree,~N,~bp);

// part of the rest of the trees
betatree:=0;
beta:=P`Parent!1;
for tree in Exclude(P`Parent`TreesIntervals[p],treeP) do
    exps:=[exponents[t]+(N+P`exponent)*P`Parent`PrimeIdeals[p,t]`e: t in tree];
    CompensateValue(~P`Parent,p,tree,exps,~betatree);
    beta*:=betatree;
end for;
mult:=bp*beta;
MultiplyByInverse(~mult,~P,exponents[P`Position]);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic MultiplyByInverse(~alpha,~P,m)
{alpha is divided by an inverse, called x, so that the output is congruent to 1 modulo P^m}
require m gt 0: "the third argument must be positive";
value,redalpha:=PValuation(alpha,P: RED:=true);
require value eq 0: "the first argument is not invertible modulo the second argument";
xnum:=0;
xden:=0;
LocalLift(~P`Type,redalpha^(-1),~xnum,~xden);
p:=P`IntegerGenerator;
alphaden:=Valuation(Parent(p)!Denominator(alpha),p);
precision:=Max([alphaden,2*P`exponent])+Ceiling(m/P`e);
SFL(~P`Parent,~P,precision*P`e-P`Type[#P`Type]`V);
//Zp:=pAdicRing(p,precision);
//Zpx:=PolynomialRing(Zp);
phi:=P`Type[#P`Type]`Phi mod p^precision;
alphanum:=PolynomialRing(Parent(p))![Parent(p)!i mod p^precision:i in Eltseq(Numerator(alpha))] mod phi;
alphanum,alphaden:=reduce(p,alphanum,alphaden);//:QUO:=false
h:=1;
while h lt m do
    h*:=2;
    lowprecision:=2*P`exponent+Ceiling(h/P`e);
    Inversionloop(p,[*alphanum,alphaden*],~xnum,~xden,phi,lowprecision);
end while;  
alpha*:=Evaluate(PolynomialRing(Parent(p))!xnum,P`Parent.1)/p^xden;

end intrinsic;

//////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic MultPiece(~P,tree,expsTree,~N,~bp)
{output bp has P-value zero and v_Q(bp) >= expsTree[Q]+extraden*e_Q, for all Q\ne P in the tree}

bp:=P`Parent!1;
if #tree eq 1 then    
    return;
end if;
N:=&+[Numerator(x): x in P`CrossedValues];
p:=P`IntegerGenerator;
ExcludeP:=Exclude(tree,P`Position);
j:=P`Position-tree[1]+1;
for t in ExcludeP do
    k:=t-tree[1]+1;
    outPt:=Exclude(ExcludeP,t);
    if #outPt eq 0 then
	wPkAllPhis:=0;
    else
	wPkAllPhis:=&+[Denominator(P`Parent`PrimeIdeals[p,l]`CrossedValues[j])*P`Parent`PrimeIdeals[p,l]`CrossedValues[k]: l in outPt];
    end if;
    e:=P`Parent`PrimeIdeals[p,t]`e;
    ord:=#P`Parent`PrimeIdeals[p,t]`Type;
    V:=P`Parent`PrimeIdeals[p,t]`Type[ord]`V;
    CVPk:=P`Parent`PrimeIdeals[p,t]`CrossedValues;
    den:=Denominator(CVPk[j]);
    wPk:=((expsTree[k]/e)+N-wPkAllPhis)/den;
    SFL(~P`Parent,~P`Parent`PrimeIdeals[p,t],Ceiling(wPk*e)-V);
    M:=Max([1+Floor(Max(CVPk)),Ceiling(wPk)]);
    phi:=P`Parent`PrimeIdeals[p,t]`Type[ord]`Phi mod p^M;
    //bp*:=Evaluate(P`Parent,phi^den);
    bp *:= Evaluate(phi^den, P`Parent.1);
end for;
bp*:=P`Parent!p^(-N);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Newton(i,~type,~phiadic,~sides,~devsEachSide)
{Given a type of order at least i, and the phiadic expansion of a polynomial, compute:
sides=list of sides of the r-th order Newton polygon w.r.t. the type, and 
devsEachSide[k]=list of multiadic phi_1,...,phi_i-1 expansion of the coefficients of the polynomial whose attached point lies on sides[k]}

require i le #type: "the first input is too large";
n:=0;
cloud:=[];
devsEachSide:=[* *];
alldevs:=[* *];
for k in [1..#phiadic] do 
        val:=0;
        dev:=[* *];
        Value(i,~type,phiadic[k],~dev,~val);
        if IsFinite(val) then 
	    Append(~cloud,<k-1,val+n>);  
	    Append(~alldevs,dev);
        end if;
        n+:=type[i]`V;
end for;
V:=NewtonPolygon(cloud);
s:=LowerVertices(V);
sides:=[[LowerSlopes(V)[k],s[k,1],s[k,2],s[k+1,1],s[k+1,2]]: k in [1..#LowerSlopes(V)]];
abscissas:=[x[1] : x in cloud];
for sd in sides do
    height:=Integers()!sd[3];
    dev:=[* *];
    for jj:=Integers()!sd[2] to Integers()!sd[4] by Denominator(sd[1]) do 
	position:=Index(abscissas,jj);
	if position gt 0 and cloud[position,2] eq height then
	    Append(~dev,alldevs[position]);
	else
	    if i eq 1 then
		Append(~dev,0);
	    else
		Append(~dev,[]);
	    end if;
	end if;
	height:=height+Numerator(sd[1]);  
    end for;
    Append(~dev,[Integers()!sd[2],Integers()!sd[3]]);
    Append(~devsEachSide,dev);
end for;
if #sides eq 0 then
      sides:=[[0,s[1,1],s[1,2],s[1,1],s[1,2]]];
      devsEachSide:=[* alldevs[Index(abscissas,Integers()!s[1,1])],[Integers()!s[1,1],Integers()!s[1,2]] *];
end if;
end intrinsic;

/*/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic pDiscriminant(p::RngIntElt, polynomial::RngUPolElt)-> RngIntElt,RngIntElt 
{}
print"noch nicht Ã¼bersetzt";

require IsPrime(p): "First argument must be a prime integer";
require (CoefficientRing(polynomial) eq Integers() and IsMonic(polynomial)): "The polynomial must be monic and integral";

pls,OMReps,totalindex:=pFactors(p,polynomial,0);
if totalindex eq Infinity() then 
    return Infinity(),Infinity(); 
end if;
disc:=0;
difft:=0;
for i:=1 to #OMReps do
    Different(~OMReps[i],~difft);
    disc+:=OMReps[i][#OMReps[i]]`prodf*difft;
end for;
return disc, disc+2*totalindex;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic pFactors(p::RngIntElt,polynomial::RngUPolElt,prec::RngIntElt)->SeqEnum, SeqEnum, RngIntElt
{}
print"noch nicht Ã¼bersetzt";

require IsPrime(p): "First argument must be a prime integer";
require (CoefficientRing(polynomial) eq Integers() and IsMonic(polynomial)): "The polynomial must be monic and integral";

n:=Degree(polynomial);
NormPol:=&+[Abs(x): x in Coefficients(polynomial)];
mahler:=Floor(n*Log(p,n)+(2*n-2)*Log(p,NormPol));
fa:=Factorization(PolynomialRing(GF(p))!polynomial);
totalindex:=0;   
OMReps:=[];
for factor in fa do
    level:=InitialLevel(p,polynomial,factor[1],factor[2]);
    Leaves:=[];
    MontesloopFactors(level,~Leaves,~totalindex,mahler);
    if totalindex gt mahler then 
    return [],[],Infinity();
    end if;
    OMReps cat:=Leaves;  
end for;
if #OMReps eq 1 then
    OMReps[1,#OMReps[1]]`Phi:=polynomial;
    OMReps[1,#OMReps[1]]`slope:=Infinity();
end if;
for i:=1 to #OMReps do
    ord:=#OMReps[i];
    exponent:=OMReps[i,1]`sfl[1];
    slope:=OMReps[i,ord]`prode*(prec+exponent+1)-OMReps[i,ord]`V;
    SFL(~OMReps[i],slope);
end for;
return [t[#t]`Phi: t in OMReps], OMReps, totalindex;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic pHermiteBasis(K::FldFun,p::RngUPolElt)->SeqEnum
{Compute a  p-integral basis of ZK.}

_, _ := Montes(K,p: Basis:=true);
//if not IsDefined(K`pHermiteBasis,p) then
    n:=Degree(K);
    Nums:=[Reverse(Eltseq(Numerator(xx))): xx in K`pBasis[p]];
    Dens:=[Valuation(Parent(p)!Denominator(xx),p): xx in K`pBasis[p]];
    maxexp:=Max(Dens);
//    Zp:=pAdicRing(p,maxexp+1);
    pi:=p;
   	precision:=maxexp+1;
    Nums:=[[(Parent(p)!Nums[i,j] mod p^precision*pi^(maxexp-Dens[i])) mod p^precision: j in [1..n]]: i in [1..n]];
    H:=HermiteForm(Matrix(Nums));
    Dens:=[p^( maxexp-Valuation(H[i,i],p)): i in [1..n]];
    H:=[[H[i,j] div H[i,i]: j in [1..n]]: i in [1..n]];
    K`pHermiteBasis[p]:=Reverse([K!Reverse(H[k])/Dens[k] : k in [1..n]]);
//end if;
return K`pHermiteBasis[p];
end intrinsic;   

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////*/

intrinsic PrescribedValue(~type,value,~Psi,~logpsi)
{if type is attached to the prime ideal P with Okutsu depth r, then logpsi=[a_0,...,a_r] and Psi=phi_1^a_1...phi_r^a_r, with v_P(p^a_0Psi(theta))=value}

Psi:=PolynomialRing(Parent(type[1]`IntegerGenerator))!1;
logpsi:=RSpace(Integers(),#type)!0;
qq,val:=Quotrem(value,type[#type]`prode);
logpsi[1]:=qq;
if val gt 0 then
    body:=val;
    for k:=#type-1 to 1 by -1 do
	jj:=type[k]`invh*body mod type[k]`e;
	logpsi[k+1]:=jj;
	Psi*:=type[k]`Phi^jj;
	res:=(body-jj*type[k]`h) div type[k]`e;
	body:=res-jj*type[k]`V;
    end for;
    logpsi[1]+:=res;
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic pResultant(p::RngIntElt,polynomial::RngUPolElt,polynomial2::RngUPolElt)-> RngIntElt
{}

require IsPrime(p): "First argument must be a prime integer";
require (CoefficientRing(polynomial) eq Integers() and IsMonic(polynomial)): "The first polynomial must be monic and integral";
require (CoefficientRing(polynomial2) eq Integers() and IsMonic(polynomial2)): "The second polynomial must be monic and integral";
//Muss Ã¼bersetzt werden
Pol:=polynomial;
Pol2:=polynomial2;
if Degree(Pol) gt Degree(Pol2) then
    Pol:=polynomial2;
    Pol2:=polynomial;
end if;
Norm:=&+[Abs(x)^2: x in Coefficients(Pol)];
Norm2:=&+[Abs(x)^2: x in Coefficients(Pol2)];
mahler:=Floor((Degree(Pol2)*Log(p,Norm)+Degree(Pol)*Log(p,Norm2))/2);
fa:=Factorization(PolynomialRing(GF(p))!Pol);
totalres:=0;
for factor in fa do
    b:=VValuation(PolynomialRing(GF(p))!Pol2,factor[1]);
    if b eq 0 then 
	continue; 
    end if;
    level:=InitialLevel(p,Pol,factor[1],factor[2]);
    level`alpha:=b;
    Stack:=[[level]];
    while #Stack gt 0 and totalres le mahler do
	type:=Stack[#Stack];
	Prune(~Stack);
	r:=#type;
	Phiadic,Quotients:=Taylor(type[1]`Pol,type[r]`Phi,type[r]`omega);
	Phiadic2,Quotients2:=Taylor(Pol2,type[r]`Phi,type[r]`alpha);
	sides:=[]; 
	sides2:=[];
	devsSides:=[* *]; 
	devsSides2:=[* *];	  
	Newton(r,~type,~Phiadic,~sides,~devsSides);
	Newton(r,~type,~Phiadic2,~sides2,~devsSides2);
	partialres:=-type[r]`cuttingslope*type[r]`omega*type[r]`alpha; 
	if sides[1,2] gt 0 then
	    if sides2[1,2] gt 0 then 
		return Infinity(); 
	    end if;
	    partialres+:=sides[1,2]*(sides2[1,3]-sides2[#sides2,5]);
	    type[1]`Pol:=Quotients[Integers()!sides[1,2]];
	end if;
	if sides2[1,2] gt 0 then
	    Pol2:=Quotients2[Integers()!sides2[1,2]];
	    partialres+:=sides2[1,2]*(sides[1,3]-sides[#sides,5]);
	end if;
	if sides[1,1] eq 0 or sides2[1,1] eq 0 then 
	    sides:=[];
	end if;
	for s:=1 to #sides do 
	    side:=sides[s];
	    lambda:=side[1];
	    type[r]`h:=-Numerator(lambda);
	    type[r]`e:=Denominator(lambda);
	    type[r]`slope:=-lambda;
	    type[r]`invh:=InverseMod(type[r]`h,type[r]`e);
	    lprime:=(1-type[r]`invh*type[r]`h) div type[r]`e;
	    newPi:=ElementToSequence(type[r]`invh*type[r]`logPhi+lprime*type[r]`logPi);
	    Append(~newPi,0);
	    type[r]`logGamma:=type[r]`e*type[r]`logPhi-type[r]`h*type[r]`logPi;
	    acumE:=0;
	    acumH:=0;
	    for side2 in sides2 do
		if lambda gt side2[1] then 
		    acumE+:=Integers()!(side2[4]-side2[2]);
		else
		    acumH+:=Integers()!(side2[3]-side2[5]);
		end if;
	    end for;
	    partialres+:=(side[3]-side[5])*acumE+(side[4]-side[2])*acumH;
	    lloc:=Index([x[1]: x in sides2],lambda);
	    if  lloc eq 0 then 
		continue; 
	    end if;
	    psi:=0;
	    ResidualPolynomial(r,~type,~devsSides[s],~psi);
	    respol:=psi/LeadingCoefficient(psi);
	    ResidualPolynomial(r,~type,~devsSides2[lloc],~psi);
	    respol2:=psi/LeadingCoefficient(psi);
	    factors:=Factorization(respol);
	    for factor in factors do        
		b:=VValuation(respol2,factor[1]);
		if b eq 0 then 
		    continue; 
		end if;
		ta:=type;  
		ta[r]`psi:=factor[1];
		ta[r]`f:=Degree(factor[1]);
		ta[r]`alpha:=b; 
		if ta[r]`omega eq 1 then
		    ta[1]`Phiadic[1]:=Phiadic[1];
		    ta[1]`Phiadic[2]:=Phiadic[2];
		    SFL(~ta,2*ta[r]`h);     
		    ta[r]`cuttingslope:=ta[r]`h;
		else
		    Representative(~ta);
		    r1:=r+1;
		    if factor[2] eq 1 then 
			nur:=&+[ta[j]`slope/ta[j]`prode: j in [1..r]]; 
			ta[1]`sfl[1]:=Floor((ta[r1]`V/ta[r1]`prode)-nur);
		    end if;
		    if Degree(ta[r]`Phi) eq Degree(ta[r1]`Phi) then 
			ta[r]`Phi:=ta[r1]`Phi;
			ta[r]`omega:=factor[2];
			ta[r]`cuttingslope:=ta[r]`h;
			Prune(~ta);
		    else
			ta[r1]`omega:=factor[2];
			ta[r1]`alpha:=b;
			vec:=-ta[r1]`V *ta[r+1]`logPi;
			vec[r+2]:=1; 
			ta[r1]`logPhi:=Vector(vec); 
			ta[r1]`logPi:=Vector(newPi);         
		    end if; 
		end if;
		Append(~Stack,ta);
	    end for;     
	end for; 
	totalres+:=type[r]`prodf*Integers()!partialres;
    end while; 
    if totalres gt mahler then 
	return Infinity(); 
    end if;
end for;
return totalres;
end intrinsic;

////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic PValuation(alpha::FldFunElt, P::Rec: RED:=false)->RngIntElt,FldFinElt
{Compute the P-valuation of alpha at the prime ideal P, which can be given either as PrimeIdealRecord or as an IdealRecord}

F:=P`Parent;
if not alpha in F then
	f:=DefiningPolynomial(F);
	n:=Degree(f);
	Coeff:=Coefficients(f);
	dtemp:=Maximum([Degree(Coeff[i])+(i-1): i in [1..#Coeff]]);
	d:=Ceiling(dtemp/n);
    return PValuation( TransMap(alpha,F),P);
else
	return PValuation(P`Parent!alpha,P);
end if;
end intrinsic;

intrinsic PValuation(alpha::RngUPolElt, P::Rec: RED:=false)->RngIntElt,FldFinElt
{Compute the P-valuation of alpha at the prime ideal P, which can be given either as PrimeIdealRecord or as an IdealRecord}
return PValuation(P`Parent!alpha,P);
end intrinsic;

intrinsic PValuation(alpha::FldFunElt,P::Rec: RED:=false)->RngIntElt,FldFinElt
{Compute the P-valuation of alpha at the prime ideal P, which can be given either as PrimeIdealRecord or as an IdealRecord.
Also the class of alpha in P^value/P^value+1
}
//require IsPrimeIdeal(P): "Second argument should be a prime ideal";

//print"Input", alpha,P;
K:=P`Parent;
if not Parent(alpha) eq K then
	if not assigned K`Cf then
	f:=DefiningPolynomial(K);
	n:=Degree(f);
	Coeff:=Coefficients(f);
	dtemp:=Maximum([Degree(Coeff[i])+(i-1): i in [1..#Coeff]]);
	d:=Ceiling(dtemp/n);
	else
	d:=K`Cf;
	end if;
    alpha:= TransMap(alpha,K);
end if;
require alpha in P`Parent: "Arguments should lie on the same number field";
r:=#P`Type;
p:=P`IntegerGenerator;
Fp:=P`Type[1]`Fq;
Fpy:=P`Type[1]`FqY;
map:=P`Type[1]`Redmap;
reduction:=Fp!0;
if alpha eq 0 then 
    return Infinity(),reduction; 
end if;
den,exp,numPol:=Localize(alpha,P`IntegerGenerator);
cua:=exp*P`e;

pphi:=[map(i):i in Eltseq(P`Type[1]`Phi)];
pnumPol:=[map(i):i in Eltseq(numPol)];
if VValuation(Fpy!pnumPol,Fpy!pphi) eq 0 then 
	if RED then
	ConvertLogs(~P`Type,-cua*P`LogLG,~reduction);
	reduction*:=(map(den))^(-1)*Evaluate(Fpy!pnumPol,P`Type[1]`z);
    end if;
    return cua,reduction; 
end if;
respol:=0;
z:=0;
dev:=[* *];
val:=0;
value:=0;
i:=0;
while value eq 0 do
 	if i lt #P`Type then
	i+:=1;
    else
	SFL(~P`Parent,~P,2*P`Type[#P`Type]`h);
    end if;
    Value(i+1,~P`Type,numPol,~dev,~val);
    ResidualPolynomial(i,~P`Type,~dev,~respol);
    if VValuation(respol,P`Type[i]`psi) eq 0 then
	value:=val*(P`e div (P`Type[i]`e*P`Type[i]`prode));
    end if;
end while;
if RED then
    log:=dev[#dev,1]*P`Type[i]`logPhi+dev[#dev,2]*P`Type[i]`logPi;
    EqualizeLogs(~P`LogLG,~log);
    ConvertLogs(~P`Type,log-(value+cua)*P`LogLG,~reduction);
    Z(~P`Type,i,~z);
    reduction*:=(Fp!den)^(-1)*Evaluate(respol,z);
end if;
return value+cua,reduction;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic reduce(p,poly,den)->RngUPolElt,RngIntElt
{}

if poly eq 0 then
    return poly,0;
end if;
cancel:=Min([den,Min([Valuation(Parent(p)!a,p):a in Eltseq(poly)])]);

num:=poly div p^cancel;
//ChangePrecision(~num,GetPrecision(Zp));
return num,den-cancel;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic 'mod'(alpha:: FldFunElt, P:: Rec)->FldFinElt
{Compute the reduction map ZK--> ZK/P}
// It's a copy of Reduction, with better name
return Reduction(alpha,P);
end intrinsic;

intrinsic Reduction(alpha:: FldFunElt, P:: Rec)->FldFinElt
{Compute the reduction map ZK--> ZK/P}

return Reduction(alpha,P,1)[1];
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Reduction(alpha:: FldFunElt, P:: Rec, m::RngIntElt)->SeqEnum
{reduction map ZK--> ZK/P^m}
print"noch nicht Ã¼bersetzt.";
require m gt 0: "The third argument should be positive";
beta:=alpha;
Simplify(~beta,~P,m);
value,red:=PValuation(beta,P: RED:=true);
require value ge 0: "First argument should be P-integral";
class:=[P`Type[#P`Type]`Fq!0: i in [1..m]];
while value lt m do
    class[value+1]:=red;
    if value eq m-1 then
	value:=m;
    else
	beta-:=LocalLift(red,P)*P`LocalGenerator^value;
	Simplify(~beta,~P,m);
	value,red:=PValuation(beta,P: RED:=true);
    end if;
end while;
return class;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Representative(~type)
{Construction of a representative phi of a type. 
We add phi and V at a new level of type}

s:=#type;
ef:=type[s]`e*type[s]`f;        
u:=ef*type[s]`V+type[s]`f*type[s]`h;                
newphi:=0;
Construct(s,~type,Reductum(type[s]`psi),0,u,~newphi);                   
newphi+:=type[s]`Phi^ef;          
newlevel:=rec<TypeLevel| 
Phi:=newphi, 
V:=type[s]`e*u, 
cuttingslope:=0, 
Refinements:=[* *],
prode:=type[s]`prode*type[s]`e,
prodf:=type[s]`prodf*type[s]`f,
Fq:=ext<type[s]`Fq| type[s]`psi>
>;
newlevel`FqY:=PolynomialRing(newlevel`Fq:Global:=false);
AssignNames(~(newlevel`Fq),["z" cat IntegerToString(s)]);
AssignNames(~(newlevel`FqY),["Y" cat IntegerToString(s)]);
if type[s]`f gt 1 then
    mmm,nnn:=HasAttribute(newlevel`Fq,"PowerPrinting");
    if mmm and nnn then
	AssertAttribute(newlevel`Fq,"PowerPrinting",false); 
    end if;
    newlevel`z:=newlevel`Fq.1;
else
    newlevel`z:=-Coefficient(type[s]`psi,0);                                              
end if;             
Append(~type,newlevel);
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic ResidualPolynomial(i,~type,~devsSide,~psi)
{Internal procedure to compute the i-th residual polynomial psi with respect to
a side S  of slope -type[i]`slope of the Newton polygon of a certain polynomial Pol. 
The coefficients of Pol whose attached  points in N_i(Pol) lie on S have multiadic expansions 
contained in the list devsSide.
}
	
require i le #type: "the first input is too large";
pj:=0;
rescoeffs:=[type[i]`Fq!0 : j in [1..#devsSide-1]];
if i eq 1 then
    height:=devsSide[#devsSide,2];
    for j:=1 to #devsSide-1 do
	dev:=devsSide[j];
	if not dev eq 0 then
	  
	map:=type[1]`Redmap;
		FPP:=Codomain(map);
	    tmp:=PolynomialRing(FPP)![map(ii):ii in Eltseq((dev 	div type[1]`IntegerGenerator^height))];	
	    rescoeffs[j]:=Evaluate(tmp,type[i]`z);
	end if;
    height:=height-type[i]`h;
    end for;
else
    lprime:=(1-type[i-1]`invh*type[i-1]`h) div type[i-1]`e;
    for j:=1 to #devsSide-1 do
	dev:=devsSide[j];
	if not #dev eq 0 then
	    txp:=lprime*dev[#dev,1]-type[i-1]`invh*dev[#dev,2];
	    ResidualPolynomial(i-1,~type,~dev,~pj);
	    rescoeffs[j]:=type[i]`z^txp*Evaluate(pj,type[i]`z);
	end if;
    end for;
end if;
psi:=type[i]`FqY!rescoeffs;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////


intrinsic SFL(~type::SeqEnum,slope::RngIntElt)
{in type[1]`sfl and type[1]`Phiadic we stored relevant data. The aim is type[#type]`slope>=slope}
ord:=#type;
if type[ord]`slope ge slope then
    return;
end if;
//print"Calling SFL for slope",slope;print"\n\n\n\n\n";
tts:=Realtime();
if type[1]`sfl[3] eq 0 then
    SFLInitialize(~type);
end if;

p:=type[1]`IntegerGenerator;
exponent:=type[1]`sfl[1];
nu:=type[1]`sfl[2];
x0prec:=type[1]`sfl[3];
x0num:=type[1]`Phiadic[4];
x0den:=type[1]`sfl[4];
e:=type[ord]`prode;
h:=type[ord]`h-type[ord]`cuttingslope;
lasth:=slope-type[ord]`cuttingslope;
V:=type[ord]`V+type[ord]`cuttingslope;
//Zp:=pAdicRing(p,nu+exponent+Ceiling((V+2*lasth)/e));
precision:=nu+exponent+Ceiling((V+lasth)/e);
piZp:=p;
PolZp:=type[1]`Pol mod p^precision;		
PsinumZp:=type[1]`Phiadic[3] mod p^precision;
//zq:=quo<Zp|piZp^(nu+exponent+Ceiling((V+2*h)/e))>;
//zqt<t>:=PolynomialRing(zq);

path:=PathOfPrecisions(lasth,h);
shortpath:=PathOfPrecisions(h,x0prec);

newprecision:=nu+exponent+Ceiling(h/e);
a1:=type[1]`Phiadic[2] mod p^newprecision;

newprecision:=nu+exponent+Ceiling((V+path[2])/e);
phi:=type[ord]`Phi mod p^newprecision;
Psinum:= PsinumZp mod p^newprecision ;
A0num, A0den := reduce(p,((type[1]`Phiadic[1]mod p^newprecision)*Psinum) mod phi,nu);
A1num, A1den := reduce(p,((a1 mod p^newprecision)*Psinum) mod phi,nu);
for i in [2..#shortpath] do
    lowprecision:=A1den+2*x0den+Ceiling(shortpath[i]/e);
    Inversionloop(p,[* A1num,A1den *],~x0num,~x0den,phi,lowprecision);
end for;  
Anum, Aden := reduce(p,(A0num*(x0num mod p^newprecision)) mod phi, x0den+A0den);
phi:=phi+Anum;

for i in [2..#path-1] do

   // zq:=quo<Zp|piZp^(nu+exponent+Ceiling((V+2*h)/e))>;
    //zqt<t>:=PolynomialRing(zq);
    loopprec:=nu+exponent+Ceiling((V+path[i+1])/e);
    ploop:=p^loopprec;
    phi:=phi mod ploop;
    Psinum:= PsinumZp mod ploop;
    qq,c0:=Quotrem(PolZp mod ploop,phi);
    c1:=qq mod phi;
    C0num,C0den := reduce(p,(c0*Psinum mod ploop) mod phi,nu);
    C1num,C1den := reduce(p,(c1*Psinum mod ploop) mod phi,nu);
    lowprecision:=C1den+2*x0den+Ceiling(path[i]/e);
    Inversionloop(p,[* C1num,C1den *],~x0num,~x0den,phi,lowprecision);
    Cnum,Cden:=reduce(p,(C0num*(x0num)mod ploop) mod phi, x0den+C0den);
    phi:=phi+Cnum;
end for;

type[1]`sfl[3]:=Max([h,path[#path-1]]);
type[ord]`Phi:=phi;
type[1]`Phiadic[4]:=x0num;
type[1]`sfl[4]:=x0den;
//print"EndSFL",Realtime()-tts;
end intrinsic;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

intrinsic SFL(~K::FldFun,~P::Rec,slope::RngIntElt)
{}

if P`Type[#P`Type]`slope ge slope then
    return;
end if;
SFL(~P`Type,slope);
UpdateLastLevel(~P`Type);
K`PrimeIdeals[P`IntegerGenerator,P`Position]`Type[#P`Type]:=P`Type[#P`Type];
K`PrimeIdeals[P`IntegerGenerator,P`Position]`Type[1]:=P`Type[1];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic SFLInitialize(~type)
{}

p:=type[1]`IntegerGenerator;
r:=#type-1;
e:=type[r+1]`prode;
a1:=type[1]`Phiadic[2];
Psinum:=PolynomialRing(Parent(p))!1;
if r eq 0 then
    nu:=Min([Valuation(xx,p): xx in Coefficients(a1)]);
    helpa1:=PolynomialRing(type[1]`Fq)![type[1]`Redmap(i):i in Coefficients(a1 div p^nu)];
    class:=Evaluate(helpa1,type[1]`z);
else
    val:=0;
    dev:=[* *];
    Value(r+1,~type,a1,~dev,~val);
    respol:=0;
    ResidualPolynomial(r,~type,~dev,~respol);
    logpsi:=0;
    qq,s:=Quotrem(-val,e);
    PrescribedValue(~type,s,~Psinum,~logpsi);
    nu:=-logpsi[1]-qq;
    vector:=dev[#dev,1]*type[r]`logPhi+dev[#dev,2]*type[r]`logPi;
    class:=0;
    ConvertLogs(~type,logpsi+vector,~class);
    class*:=Evaluate(respol,type[r+1]`z);
end if;
type[1]`Phiadic[3]:=Psinum;
type[1]`sfl[2]:=nu;
type[1]`sfl[3]:=1;
x0num:=0;
x0den:=0;
LocalLift(~type,class^(-1),~x0num,~x0den);
type[1]`Phiadic[4]:=x0num;
type[1]`sfl[4]:=x0den;
end intrinsic;

///////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Simplify(~beta,~P,m)
{beta is P-integral. The output is congruent to beta mod P^m and it has:
denominator=p^power, deg(numerator) less than n_P, and numerator simplified mod p^power+(m/eP)
}

require m gt 0: "the third argument must be positive";
require beta in P`Parent: "number fields of first and second argument do not coincide";
p:=P`IntegerGenerator;
den,exp,num:=Localize(beta,p);
beta:=P`Parent!0;
precision:=Ceiling(m/P`e)-exp;
if precision gt 0 then
    power:=p^precision;
    SFL(~P`Parent,~P,precision*P`e-P`Type[#P`Type]`V);
    phi:=P`Type[#P`Type]`Phi mod power;
    num:=(InverseMod(den,power)*num mod phi) mod power;
    beta:=Evaluate(num,P`Parent.1)*P`Parent!p^exp;  
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////

intrinsic SIntegralBasis(K::FldFun, primelist::SeqEnum)->SeqEnum
    { Filler intrinsic. }

    print "******** WARNING ********";
    print "Intrinsic SIntegralBasis() for Number Fields is a placeholder.";

    return [];
end intrinsic; // SIntegralBasis
/*/////////////////////////////////////////////////////////////////////////////////////

intrinsic SIntegralBasis(K::FldFun,primelist::SeqEnum)->SeqEnum
{Compute a local integral basis for the given set of primes.}

Numlist:=[];
Denlist:=[];
Fqt:=Parent(primelist[1]);
for p in primelist do
    pHBasis:=pHermiteBasis(K,p);    
    if K`LocalIndex[p] gt 0 then
	Append(~Numlist,[Parent([Fqt.1])!Eltseq(Numerator(xx)): xx in pHBasis]);
	Append(~Denlist,[Fqt!Denominator(xx): xx in pHBasis]);
    end if;
end for;
n:=Degree(K);
nprimes:=#Denlist;
if nprimes eq 0 then
    return [K.1^k: k in [0..n-1]];   
end if;
SBasis:=[K!1];
for i:=2 to n do
    Dens:=[Denlist[k,i] : k in [1..nprimes]];
    coeffs:=[];
    for j:=1 to i-1 do 
	Nums:=[Numlist[k,i,j] : k in [1..nprimes]]; 
	Append(~coeffs,CRT(Nums,Dens));
    end for;
    coeffs cat:=[0: j in [1..n-#coeffs]];
    Append(~SBasis,(K.1^(i-1)+K!coeffs)/&*Dens);
end for;    
return SBasis;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////*/

intrinsic Taylor(pol::RngUPolElt,phi::RngUPolElt,omega::RngIntElt)->SeqEnum
{Compute the first omega+1 coefficients of the phi-expansion of pol}
quot:=pol;
Coeffs:=[];
Quos:=[];
for j:=0 to omega do 
  	quot,rem:=Quotrem(quot,phi);
  	Append(~Coeffs,rem);
	Append(~Quos,quot);
end for;
Prune(~Quos);
return Coeffs,Quos;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic TreeInterval(~P,~tree)
{}

treenumber:=#P`Parent`TreesIntervals[P`IntegerGenerator];
while P`Parent`TreesIntervals[P`IntegerGenerator,treenumber,1] gt P`Position do
    treenumber-:=1;
end while;
tree:=P`Parent`TreesIntervals[P`IntegerGenerator,treenumber];
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Truncate(~log)
{}

require Degree(log) gt 1: "argument too short to be truncated";
log:=Vector(Remove(Eltseq(log),Degree(log)));
end intrinsic;

///////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic UpdateLastLevel(~type)
{}

qq,a0:=Quotrem(type[1]`Pol,type[#type]`Phi);
if a0 eq 0 then 
    type[#type]`slope:=Infinity();
else    
    type[1]`Phiadic[1]:=a0;
    type[1]`Phiadic[2]:=qq mod type[#type]`Phi;
    sides:=[];
    devs:=[* *];
    tmp:=[a0,type[1]`Phiadic[2]];
    Newton(#type,~type,~tmp,~sides,~devs);
    type[#type]`slope:=-sides[1,1];
    type[#type]`h:=-Integers()!sides[1,1];
    psi:=0;
    ResidualPolynomial(#type,~type,~devs[1],~psi);
    type[#type]`psi:=psi/LeadingCoefficient(psi);
    type[#type]`logGamma:=type[#type]`logPhi-type[#type]`h*type[#type]`logPi;
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Value(i,~type,pol,~devs,~val)
{Given a level i, a type and a polynomial pol, the output is:
devs=multiexpansion with respect to phi_1,...,phi_i-1 of the points in S_lambda_i-1(pol)
val=i-th valuation of pol w.r.t. type}

require i le #type+1: "the first input is too large";
val:=Infinity();
if pol eq 0 then
    if i eq 1 then
	  devs:=0;
    else
	  devs:=[];
    end if;
    return;
end if;
if i eq 1 then 
    val:=Min([Valuation(c,type[1]`IntegerGenerator): c in Coefficients(Parent(type[1]`Phi)!pol)]);
    devs:=pol;
else  
    im1:=i-1;
    step:=type[im1]`V+type[im1]`slope;
    minheight:=0;
    Vheight:=0;
    twoe:=2*type[im1]`e;
    quot:=pol;
    k:=0;
    last:=0;
    while quot ne 0 and minheight le val do
	dev:=[* *];
	newval:=0;
	quot,ak:=Quotrem(quot,type[im1]`Phi);
        Value(im1,~type,ak,~dev,~newval);
	candidate:=newval+minheight;
	if candidate le val then
	    if candidate lt val then
		val:=candidate;
		firstabscissa:=k;
		firstordinate:=newval+Vheight;
		devs:=[* dev *];
	    else  
	    for jj:=last+twoe to k by type[im1]`e do;
		if im1 eq 1 then 
		    Append(~devs,0);
		else
		    Append(~devs,[]);
		end if;
	    end for;
	    Append(~devs,dev);
	    end if;
      	last:=k;
	end if;
	minheight+:=step;
	Vheight+:=type[im1]`V;
	k+:=1;
    end while;
    Append(~devs,[firstabscissa,firstordinate]);
    val:=Integers()!(type[im1]`e*val);
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic VValuation(pol:: RngUPolElt,poly:: RngUPolElt)->RngIntElt
{}
ord:=-1;
rem:=0;
pl:=pol;
while rem eq 0 do
    pl,rem:=Quotrem(pl,poly);
    ord+:=1;
end while;
return ord;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Z(~type,i,~z)
{z=z_i belongs to F_(i+1)}

if i eq #type then 
    z:=-Coefficient(type[#type]`psi,0);
else
    z:=type[i+1]`z;
end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//    Functions to  manipulate ideals
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic TwoElement(I:: Rec)->SeqEnum
{Compute a pair of elements generating the ideal I.}
require IsPrimeIdealRecord(I) or IsIdealRecord(I): "Argument should be an ideal record or a prime ideal record"; 
if IsPrimeIdealRecord(I) then
    return [I`Parent!I`IntegerGenerator, I`Generator]; end if;
if IsZero(I) then return [I`Parent!0,I`Parent!0]; end if;
TwoElement(~I);
return [I`Parent!I`IntegerGenerator, I`Generator];
end intrinsic;

intrinsic TwoElement(~I:: Rec)
{Compute a pair of elements generating the ideal.}
require IsPrimeIdealRecord(I) or IsIdealRecord(I): "Argument should be an ideal record or a prime ideal record"; 

if not IsPrimeIdealRecord(I) then 
    // nothing to do if the ideal is prime; the generator has been already computed
    if not assigned I`Generator then 
        K:=I`Parent;
        R:=PolynomialRing(ConstantField(K));
        I`Generator:=K!0;
        list:=Factorization(I);
        TwoGens:=[];
        Mult:=[];
        pos:=1;
        ig:=1;  // integergenerator
        while pos le #list do 
	       p:=list[pos,1];
	       ppart:=[x: x in list | x[1] eq p];
	       Genp:=K!1;
	       Hp:=0;
	       for P in ppart do
	           index:=P[2];
	           exponent:=P[3];
               if not assigned K`PrimeIdeals[p,index]`Generator then
                   Generators(K, p);
               end if;
	           genP:=K`PrimeIdeals[p,index]`Generator;
	           eP:=K`PrimeIdeals[p,index]`e;
	           Genp*:=genP^exponent;
	           if exponent lt 0 then
	               num:=Eltseq(Numerator(K`PrimeIdeals[p,index]`Generator));
                   norm:=R!Resultant(PolynomialRing(R)!num,DefiningPolynomial(K));
                   aa:=Valuation(norm,p);
                   res:=norm div p^aa;
	               Genp*:=res^(Abs(exponent));
	           end if;
	           Hp:=Max(Hp, Ceiling(exponent/eP));
	       end for;
	       first:=p^Hp;
	       ig:=ig*first;
	       Append(~TwoGens,[first,Genp]);
	       Append(~Mult,p);   
	       pos:=pos+#ppart;
        end while;
        I`IntegerGenerator:=ig;
        if #Mult gt 0 then
	       univ:=(&*Mult)*ig;
	       I`Generator:=&+[TwoGens[j,2]*(univ div (PolynomialRing(ConstantField(K))!TwoGens[j,1] * Mult[j])):j in [1..#Mult]];
        end if;
        if not assigned I`Generators then I`Generators:=[K!ig,I`Generator]; end if;
    end if;
end if;    
end intrinsic;

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IsIdealRecord(I::Rec)->BoolElt
{True iff I is a record of type IdealRecord.}
return    Names(I) eq Names(rec<IdealRecord|>);
end intrinsic;

//////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IsPrimeIdealRecord(I::Rec)->BoolElt
{True iff I is a record of type PrimeIdealRecord.}
return    Names(I) eq Names(rec<PrimeIdealRecord|>);
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IsPrimeIdeal(I::Rec)->BoolElt
{True iff I is a record of type IdealRecord or PrimeIdealRecord corresponding to a prime ideal. }
require IsPrimeIdealRecord(I)  or IsIdealRecord(I): "Argument should be an ideal record or a prime ideal record"; 
if IsPrimeIdealRecord(I) then 
    return true;
else
    Factorization(~I);  
    return I`IsPrime ;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic PrimeIdeal(I:: Rec)->Rec
{Transform a  record of type PrimeIdealRecord into a record of type IdealRecord.}
require Names(I) eq Names(rec<PrimeIdealRecord|>) : "Not a PrimeIdealRecord";
return rec<IdealRecord| Parent:=I`Parent, 
                        Factorization:=[[I`IntegerGenerator, I`Position, 1]], 
                        FactorizationString:=Sprintf("P(%o,%o)",I`IntegerGenerator,I`Position),
			Generators:=[I`Parent!I`IntegerGenerator,I`Generator],
			IntegerGenerator:=I`IntegerGenerator,
			Generator:=I`Generator,
                        IsPrime:=true  >;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic PrimeIdeal(K::FldNum, p:: RngIntElt,j:: RngIntElt)->Rec
{Pick up the IdealRecord corresponding to the j-th prime ideal appearing in the factorization of pZK.}
require IsPrime(p): "Not a prime number";
require IsDefined(K`PrimeIdeals,p): "Rational prime not factored yet" ;
require #K`PrimeIdeals[p] ge j: "Rational prime has less than specified factors";
return rec<IdealRecord| Parent:=K, 
                        Factorization:=[[p, j, 1]],
                        FactorizationString:=Sprintf("P(%o,%o)",p,j),
			Generators:=[K!p,K`PrimeIdeals[p,j]`Generator],
			IntegerGenerator:=p,
			Generator:=K`PrimeIdeals[p,j]`Generator,
                        IsPrime:=true  >;
end intrinsic;

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

intrinsic IdealPrime(I:: Rec)->Rec
{Transform a  record of type IdealRecord representing a prime ideal into a record of type PrimeIdealRecord.}
require IsPrimeIdeal(I) : "Not a Prime Ideal";
if IsPrimeIdealRecord(I) then 
    return I;
else
    return rec<PrimeIdealRecord| Parent:=I`Parent, 
                  Pol:=DefiningPolynomial(I`Parent),
		  Prime:=I`Factorization[1,1],
		  Position:=I`Factorization[1,2],
		  e:=I`Factorization[1,3],
		  Type:=(I`Parent)`PrimeIdeals[I`Factorization[1,1],I`Factorization[1,2]]`Type
		  >;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic '*'(I::Rec ,J:: Rec)->Rec
{Compute the product  of the  fractional ideals I,J. They are both factored if their factorization is not yet known.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I) : "First argument is neither an IdealRecord nor a PrimeIdealRecord";
require IsIdealRecord(J) or IsPrimeIdealRecord(J): "Second argument is neither an IdealRecord nor a PrimeIdealRecord";
require I`Parent eq J`Parent: "Ideals do not belong to the same number field";
if IsZero(I) then return I; end if;
if IsZero(J) then return J; end if;
list:= Sort2(Factorization(I) cat Factorization(J));
tot:=#list;
output:=[];
pos:=1;
while pos le tot do    
    i:=pos+1;
    term:=list[pos];
    if (i le tot and list[i,1] eq term[1] and list[i,2] eq term[2]) then 
        term[3]+:=list[i,3];
        i:=i+1;
    end if;
    Append(~output,term);
    pos:=i;
end while;
output:=SequenceToList([x: x in output | x[3] ne 0]);
id:= rec<IdealRecord|  Factorization:= output,
                       FactorizationString:= FactorListToString(output), 
                       Parent:=I`Parent,
                       IsPrime:=(#output eq 1 and output[1,3] eq 1)>;
return id;
end intrinsic;

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

intrinsic '^'(I::Rec, n::RngIntElt)->Rec
{Compute the n-th power of the fractional ideal I. The ideal I is factored if it is not already known its factorization. }
require IsIdealRecord(I) or IsPrimeIdealRecord(I) : "Argument is neither an IdealRecord nor a PrimeIdealRecord";
require not IsZero(I) or n ge 0 : "The zero ideal is not invertible";

if IsZero(I) then return I; end if;
//if n eq 1 then return I; end if;
if n eq 0 then return  rec<IdealRecord|
                            Parent:=I`Parent, 
                            Generators:=[I`Parent!1],
                            Factorization:=[* *],
                            FactorizationString:=""  >; 
end if;

l:=Factorization(I);
for i in [1..#l] do l[i,3]:=n*l[i,3]; end for;
id:= rec<IdealRecord|
                Parent:=I`Parent, 
                Factorization:=l,
                FactorizationString:=FactorListToString(l),
                IsPrime:=(#l eq 1 and l[1,3] eq 1)>;
if assigned id`Generator and n gt 0 then
    TwoElement(~id);
end if;
return id;
end intrinsic;

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

intrinsic '/'(I::Rec ,J:: Rec)->Rec
{Compute the quotient of the fractional ideals I,J. They are both factored if their factorization is not yet knwon.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I) : "First argument is neither an IdealRecord nor a PrimeIdealRecord";
require IsIdealRecord(J) or IsPrimeIdealRecord(J): "Second argument is neither an IdealRecord nor a PrimeIdealRecord";
require I`Parent eq J`Parent: "Ideals do not belong to the same number field";
require not IsZero(J): "Second argument should be a non-zero ideal.";
if IsZero(I) then return I; end if;
return I*(J^-1);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic IsIntegral(I::Rec )-> BoolElt
{True iff I is an integral ideal. The ideal is factored if its factorization is not known yet.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "Argument is neither an IdealRecord record nor a PrimeIdealRecord";
if IsPrimeIdealRecord(I) or IsZero(I) then return true; end if;
ll:=Factorization(I);
return &and[ll[j,3] ge 0: j in [1..#ll]];
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IsZero(I::Rec )-> BoolElt
{True iff I is the zero ideal}
require IsPrimeIdealRecord(I) or IsIdealRecord(I): "Argument should be an ideal record or a prime ideal record"; 
if IsPrimeIdealRecord(I) then return false; end if;
return assigned I`Generators and &and[x eq 0: x in I`Generators];
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic 'eq'(L1::List ,L2:: List)-> BoolElt
{}
if not #L1 eq #L2 then return false;end if;
for i in [1..#L1] do
	for j in [1..3] do
		if not L1[i,j] eq L2[i,j] then return false; end if;
	end for;
end for;
return true;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic 'eq'(I::Rec ,J:: Rec)-> BoolElt
{True iff the fractional ideals I,J are equal. They are both factored if their factorization is not yet kwown.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "First argument is neither an IdealRecord record nor a PrimeIdealRecord";
require IsIdealRecord(J) or IsPrimeIdealRecord(J): "Second argument is neither an IdealRecord record nor a PrimeIdealRecord";

zi1:=IsZero(I);
zi2:=IsZero(J);
if zi1 and zi2 then return true; end if;
if zi1 or zi2 then return false; end if;
return Factorization(I) eq Factorization(J);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic 'subset'(I::Rec ,J:: Rec)-> BoolElt
{True iff the fractional ideal J divides I, i.e., iff I/J is integral. 
Both ideals are factored if their factorization is not yet known.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "First argument is neither an IdealRecord record nor a PrimeIdealRecord";
require IsIdealRecord(J) or IsPrimeIdealRecord(J): "Second argument is neither an IdealRecord record nor a PrimeIdealRecord";

zi1:=IsZero(I);
zi2:=IsZero(J);
if zi1  then return true; end if;
if zi2 then return false; end if;
return IsIntegral(I/J);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Norm(I::Rec)->RngIntElt
{Compute the norm of the ideal I.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "Argument is neither an IdealRecord record nor a PrimeIdealRecord";
require not IsZero(I): "Argument should be a non-zero ideal.";
n:=1;
K:=I`Parent;
for id in Factorization(I) do
 primid:=K`PrimeIdeals[id[1],id[2]];
 n*:=primid`IntegerGenerator^(id[3]*primid`f);
end for;
return n;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic RationalRadical(I::Rec)->SeqEnum
{Compute the rational prime numbers dividing the norm of the ideal I.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "Argument is neither an IdealRecord nor a PrimeIdealRecord";
require not IsZero(I): "Argument must be a non-zero ideal.";

return SetToSequence(Set([x[1]: x in Factorization(I)]));
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
/*intrinsic '+'(I::Rec, J:: Rec)->Rec
{Compute the greatest common divisor of the fractional ideals I,J}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "First argument is neither an IdealRecord nor a PrimeIdealRecord";
require IsIdealRecord(J) or IsPrimeIdealRecord(I): "Second argument is neither an IdealRecord nor a PrimeIdealRecord";
require I`Parent eq J`Parent: "Ideals do not belong to the same number field";

if IsPrimeIdealRecord(I) then a1:=PrimeIdeal(I); else a1:=I;end if;
if IsPrimeIdealRecord(J) then b1:=PrimeIdeal(J); else b1:=J; end if;

if IsZero(a1) then return b1; end if;
if IsZero(b1) then return a1; end if;
GCD:=rec<IdealRecord|   Parent:=a1`Parent>;
if assigned a1`Generators and assigned b1`Generators then
			GCD`Generators:=SetToSequence(Set(a1`Generators) join Set(b1`Generators));
end if;
if not assigned a1`Factorization and assigned b1`Factorization then
    a1,b1:=Explode([b1,a1]);
end if;

if assigned a1`Factorization then
    output:=[];
    primesa1:=[Prune(x): x in a1`Factorization];
    if assigned b1`Factorization then
	primesb1:=[Prune(x): x in b1`Factorization];
        for k in [1..#a1`Factorization] do
	    term:=a1`Factorization[k];
            pos:=Position(primesb1,primesa1[k]);
            if  pos ne 0 then
                exp:=Min(term[3],b1`Factorization[pos,3]);
		              if exp ne 0 then 
		                  term[3]:=exp;
		                  Append(~output,term);
		              end if;
            end if;
        end for;
    else
        // b1 is given by generators
        K:=a1`Parent;
        for x in a1`Factorization do
            exp:=x[3];
            for gen in b1`Generators do
                vp:=PValuation(gen,K`PrimeIdeals[x[1],x[2]]);
                exp:=Min(exp,vp);
            end for;
	        if exp ne 0 then 
		          term:=x;term[3]:=exp;
          	      Append(~output,term);
	        end if;
        end for;
    end if;
    GCD`Factorization:=output ;
    GCD`FactorizationString:=FactorListToString(output);
    GCD`IsPrime:=(#output eq 1 and output[1,3] eq 1);
end if;
return GCD;
end intrinsic;
*/
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ideal(K::FldFun, listgen::SeqEnum[FldFunElt] )->Rec
{Define the fractional ideal generated by the elements of listgen.}
require &and[x in K: x in listgen]: "Elements should lie in the given function field.";
return rec<IdealRecord|  Generators:=listgen, Parent:=K>;
end intrinsic;

intrinsic ideal(K::FldFun, a:: FldFunElt )->Rec
{Define the principal fractional ideal generated by a}
require a in K: "Segon argument should lie in the given function field.";
return rec<IdealRecord|  Generators:=[a], Parent:=K>;
end intrinsic;

intrinsic ideal(K::FldFun, a:: RngUPolElt )->Rec
{Define the principal fractional ideal generated by the integer a}
return rec<IdealRecord|  Generators:=[K!a], Parent:=K>;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Factorization(I::Rec)->SeqEnum
{Compute the decomposition of the fractional ideal I into prime ideals.}
require IsIdealRecord(I) or IsPrimeIdealRecord(I): "Argument is neither an IdealRecord record nor a PrimeIdealRecord";
if IsIdealRecord(I) then 
    Factorization(~I);
    return I`Factorization;
else
    return [*[*I`IntegerGenerator,I`Position,1*]*];
end if; 
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Factorization(~I::Rec)
{Compute the decomposition of the fractional ideal I into prime ideals.}
require IsIdealRecord(I): "Argument should be an IdealRecord record.";
if not assigned I`Factorization then 
    require not IsZero(I): "Argument should be a non-zero ideal.";
    I`Factorization:=[* *];
    K:=I`Parent;
    Rt:=PolynomialRing(ConstantField(K));
    Rxt:=PolynomialRing(Rt);
    normradicals:=[];
    nums:=[];
    dens:=[];
    betas:=[];
    primes:={};
    for g in I`Generators do
        coefs:=Eltseq(g,BaseRing(Parent(g)));
        den:=[Rt!Denominator(x): x in coefs];
        primes:=primes join &join[Set([i[1]:i in Factorization(x)]): x in den];
        num:=Numerator(g); 
       
        gcd:=GCD([Rt!i:i in Eltseq(num)]);
        beta:=num/gcd;
        Append(~betas,beta);
        Append(~normradicals,
            gcd*Resultant(Rxt!Eltseq(beta),Rxt!DefiningPolynomial(K)));
        Append(~dens,LCM(den));
        Append(~nums,gcd);
    end for;

    temp:=GCD([Rt!i:i in normradicals]);
    primes:=Sort(SetToSequence(primes join Set([i[1]:i in Factorization(temp)])));
    for p in primes do
        h1:=[Valuation(x,p): x in nums];
        h2:=[Valuation(x,p): x in dens];
        MontesH(K,p);
        for j in [1..#K`PrimeIdeals[p]] do
            P:=K`PrimeIdeals[p,j];
            h:=[PValuation(x,P): x in betas];
            exp:=Min([(h1[i]-h2[i])*P`e+h[i]: i in [1..#h1]]);
            if exp ne 0 then 
                Append(~I`Factorization,[*p,j,exp*]);
            end if;    
        end for;
    end for;
    I`FactorizationString:=FactorListToString(I`Factorization);
    I`IsPrime:=(#I`Factorization eq 1 and I`Factorization[1,3] eq 1) ;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic FactorListToString(list)->MonStgElt
{Technical function to write down a factorization in pretty form. For internal use only}
if #list eq 0 then return ""; end if;
str:="";
for x in list do
  str:=str cat Sprintf( "*P(%o,%o)", x[1],x[2]);
  if x[3] ne 1 then str:=str cat Sprintf("^%o",x[3]); end if;
end for;
return Substring(str,2,#str);
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ResidueField(P::Rec)->FldFin
{Given a prime ideal P, this function returns the residue field Z_K/P}
require IsPrimeIdealRecord(P): "Argument should be a PrimeIdealRecord representing a prime ideal";
t:=P`Type;
return t[#t]`Fq;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////
////////  ROUTINES ADDRESSED TO THE USER
//////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic Newton(r,type,pol) -> SeqEnum
{Given a type of order at least r, and a polynomial, compute the
list of sides of the r-th order Newton polygon w.r.t. the type
}

phiadic:=Taylor(pol,type[r]`Phi,Floor(Degree(pol)/Degree(type[r]`Phi)));
sides:=[];
devs:=[* *];
Newton(r,~type,~phiadic,~sides,~devs);
return sides;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////

intrinsic Value(r,type,pol) -> RngIntElt
{Given an order r, a type and a polynomial pol, the output is
the r-th valuation of pol w.r.t. the type
}

sides:=Newton(r,type,pol);
PrincipalPart:=[x : x in sides | x[1] lt 0];
k:=#PrincipalPart;
if k gt 0 then
    return Integers()!PrincipalPart[k,5];
else
    return Integers()!PrincipalPart[k+1,3];
end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic ResidualPolynomial(r::RngIntElt, type::SeqEnum, Pol::RngUPolElt)->RngUPolElt 
{r-th residual polynomial of Pol w.r.t. a type
}

phiadic:=Taylor(Pol,type[r]`Phi,Floor(Degree(Pol)/Degree(type[r]`Phi)));
sides:=[];
devs:=[* *];
Newton(r,~type,~phiadic,~sides,~devs);
previous:=[x: x in sides | -x[1] gt type[r]`slope];
k:=#previous;
if k eq #sides then
    dev:=[* devs[k,#devs[k]-1],[Integers()!sides[k,4],Integers()!sides[k,5]] *];
else
    if sides[k+1,1]=-type[r]`slope then
	dev:=devs[k+1];
    else
	dev:=[* devs[k+1,1],[Integers()!sides[k+1,2],Integers()!sides[k+1,3]] *];
    end if;
end if;
psi:=0;
ResidualPolynomial(r,~type,~dev,~psi);
return psi;
end intrinsic;


///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////

intrinsic Construct(r,type,respol,V) -> RngUPolElt
{This routine works out the construction of [HN, Prop. 2.10].
V is a positive integer >= type[r+1]`V. 
respol is a polynomial in type[r]`FqY of degree < type[r]`f.
The output is a polynomial Ppol with integer coefficients such that: 
deg Ppol<m_r+1, v_r+1(Ppol)=V, and y^nuÂ·R_r(Ppol)(y)=respol(y), 
where nu=ord_y(respol)}

s:=type[r]`invh*V mod type[r]`e;
u:=(V-type[r]`h*s) div type[r]`e;
Ppol:=0;
Construct(r, ~type, respol, s,u, ~Ppol);
return Ppol;
end intrinsic

///////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Degree(I::Rec)->RngIntElt
{computes the Degree of a place/prime ideal}

return Integers()!(Degree(I`Type[#I`Type]`Fq)/Degree(ConstantField(I`Parent)));

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PlacesAtInfinity(K::FldFun)->SeqEnum
{Produces the places at infinity}


if not assigned K`PlacesAtInfinity then
	
	if not assigned K`IsomorphicFunctionField then
		K`IsomorphicFunctionField,K`Cf:=InftyField(K);	
	end if;
	
	MontesH(K`IsomorphicFunctionField,PolynomialRing(ConstantField(K)).1);
	K`PlacesAtInfinity:=K`IsomorphicFunctionField`PrimeIdeals[PolynomialRing(ConstantField(K)).1];
	
end if;

return K`PlacesAtInfinity;


end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PlacesAtp(K::FldFun,p::RngUPolElt)->SeqEnum
{Produces the places over p}

	MontesH(K,p);
	
return K`PrimeIdeals[p];


end intrinsic;


//////////////////////////////////////////////////////////////////////
////////////////////Genus Compution///////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IndEx(K::FldFun)->SeqEnum
{Compute the index of the maximal order ZK of K and the discriminant of K.}

if not assigned K`Index then 
	kt<t>:=PolynomialRing(ConstantField(K));

	t1:=Realtime();
 	if not assigned K`FactorizedDiscriminant then
 		
		d:=kt!Discriminant(DefiningPolynomial(K));
		//print"Computation of disc in",Realtime()-t1;
		sq:=SquarefreeFactorization(d);
		if not #sq eq 0 then 
			d:=kt!(d/&*[i[1]:i in sq]);
		end if;	
		//print"disc is now square free",Realtime()-t1;
		fac:=Factorization(d);
		K`FactorizedDiscriminant:=fac;
		//print"initialization took",Realtime()-t1;
	else 	
		fac:=	K`FactorizedDiscriminant;
		
	end if;
	t2:=Realtime();

	primelist:=[];
	for i in fac do
		if i[2] gt 1 then 
			Append(~primelist,i[1]);
		end if;
	end for;
	DegList:=[];
	IndexExpo:=0;
	Indexprimes:=[];

for p in primelist do
    _, _ := Montes(K,p);
	DegList:=DegList cat [Degree(i):i in K`PrimeIdeals[p]];
    IndexExpo:=IndexExpo+K`LocalIndex[p]*Degree(p);
    if K`LocalIndex[p] gt 0 then
    	Append(~Indexprimes,p);
    end if;
end for;
K`Index:=Indexprimes;
KK:=InftyField(K);
KK`Index:=[t];
return IndexExpo,DegList;

else
DegList:=[];
IndexExpo:=0;


for p in K`Index do
	DegList:=DegList cat [Degree(i):i in K`PrimeIdeals[p]];
    IndexExpo:=IndexExpo+K`LocalIndex[p]*Degree(p);
end for;
return IndexExpo,DegList;
end if;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////



intrinsic GENUS(K::FldFun)->SeqEnum
{Compute the genus g of a function field K/k and the index gc=[k_0:k], where k_0 is the full constant field.}
t1:=Realtime();
if assigned K`Genus then return K`Genus;end if;
t:=PolynomialRing(ConstantField(K)).1;
n:=Degree(K);
index,DegList:=IndEx(K);
print"finite Index= =",index;
K_iso:=InftyField(K);
_, _ := Montes(K_iso,t);
DegList:= DegList cat [Degree(i):i in K_iso`PrimeIdeals[t]];
indexlocal:=K_iso`LocalIndex[t];
print"infninite Index= t^-x, x=",indexlocal;
d:=K`Cf;
Append(~DegList,Integers()!(-indexlocal+Integers()!(d*(n-1)*n/2)-index));
Append(~DegList,n);
gc:=GCD(DegList);
gcold:=gc;
newinf:=-n-indexlocal+Integers()!(d*(n-1)*n/2)-index;
tmpp:=1;
print"g(k)=",newinf;
if 1+newinf lt 0 then print"what"; return 0,gc; end if; 
if gc gt 1 then 
	print"k_0 is not equal k";  
	Fp:=GF(Characteristic(ConstantField(K)),Degree(ConstantField(K))*gc);
	Fpt:=RationalFunctionField(Fp);	KxT<x> := PolynomialAlgebra(Fpt);
	print"Factoritation over",Fp;t2:=Realtime();
	tmpp:=Factorization(KxT!DefiningPolynomial(K));
	gc:=#Factorization(KxT!DefiningPolynomial(K));
	print"time needed:",Realtime()-t2;
	print"[k_0:k]=",gc;  

end if;

g:=1+(-n-indexlocal+Integers()!(d*(n-1)*n/2)-index)/gc;
K`Genus:=g;
print"g(k_0)=",g;
return g,gc,tmpp;


end intrinsic;
///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////


/*///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////



intrinsic GENUSTEST(K::FldFun)->SeqEnum
{Compute the genus g of a function field K/k and the index gc=[k_0:k], where k_0 is the full constant field.}
t1:=Realtime();
t:=PolynomialRing(ConstantField(K)).1;
n:=Degree(K);
index,DegList:=IndEx(K);
print"finite Index= =",index;
K_iso:=InftyField(K);
Montes(K_iso,t);
DegList:= DegList cat [Degree(i):i in K_iso`PrimeIdeals[t]];
indexlocal:=K_iso`LocalIndex[t];
print"infninite Index= t^-x, x=",indexlocal;
d:=K`Cf;
Append(~DegList,Integers()!(-indexlocal+Integers()!(d*(n-1)*n/2)-index));
Append(~DegList,n);
gc:=GCD(DegList);
gcold:=gc;
newinf:=-n-indexlocal+Integers()!(d*(n-1)*n/2)-index;
tmpp:=1;
print"g(k)=",newinf;
PossibleGenus:=[];
for i in Divisors(Degree(K)) do

	Append(~PossibleGenus,1+(newinf-1)/i);

end for;
g:=1+(-n-indexlocal+Integers()!(d*(n-1)*n/2)-index)/gc;
K`Genus:=g;
print"g(k_0)=",g;
return g,gc,PossibleGenus;


end intrinsic;
///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////*/


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////Reduction Algorithm ////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic Deg(f::FldFunRatUElt)->RngIntElt
{Let f=g/h with (g,h)=1. Then Degree(f)=Degree(g)-Degree(h)}

return Degree(Numerator(f))-Degree(Denominator(f));

end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic LC(f::FldFunRatUElt)->FldFinElt
{Let f=g/h with (g,h)=1. Then LC(f)=LC(g)/LC(h)}

if f eq 0 then 
	return 0;
else
return LeadingCoefficient(Numerator(f))/LeadingCoefficient(Denominator(f));
end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic ReductionAlgorithm(T::AlgMatElt:InA:=false)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}
NumberRedSteps:=0;
PutInZ(T);
lc:=LCM([Denominator(i):i in Eltseq(T)]);
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n:=Ncols(T);m:=Nrows(T);
T:=Parent(ZeroMatrix(kt,n,n))!(lc*T);

s:=1;

if m eq 1 then return T,Maximum([Deg(j):j in ElementToSequence(T[1])]),0; end if;
VectorNorm:=[Maximum([Degree(j):j in i]):i in RowSequence(T)];
p:=[];
Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);

while s lt m do
	M:=ZeroMatrix(k,m,n);
	for i in [1..m] do
		for j in [1..m] do
			if not T[i,j] eq 0 and Degree(T[i,j]) eq VectorNorm[i] then			
				M[i,j]:=LeadingCoefficient(T[i,j]);				
			end if; 				
		end for;
	end for;
	Mprime,P:=EchelonForm(M);
	s:=Rank(Mprime);
	NumberRedSteps:=NumberRedSteps+m-s;



	if s lt m then
			//Transform P in a shape to read out all relations
		Su:=SubmatrixRange(P,s+1,1,n,n);
		P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
		for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			for i in [1..u-1] do
				if not P[j,i] eq 0 then								
				AddRow(~T,P[j,i]/P[j,u]*t^(VectorNorm[u]-VectorNorm[i]),i,u);
				end if;
			end for;
			VectorNorm[u]:=Maximum([Degree(l):l in ElementToSequence(T[u])]);
		end for;
//			Append(~LLL,T);
		p:=[];
		Sort(~VectorNorm,~p);
		T:=Matrix([T[i]:i in Eltseq(p)]);
	end if;
end while;	
print"Number of RedSteps =",NumberRedSteps;
//PutInZ(LLL);
if InA then 
	return lc,T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;
else
	return (1/K!lc)*T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;
end if;
end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic Norm1(Vec::SeqEnum, Shifts::SeqEnum)->FldRatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}
tmp:=[i : i in [1..#Vec]|not Vec[i] eq 0];

degrees:=[];
for i in [1..#Vec] do

	if not Vec[i] eq 0 then 
		Append(~degrees,Degree(Vec[i])-Shifts[i] );
	end if;
	
end for;


return Maximum(degrees);

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic ReductionAlgorithm2(T::AlgMatElt:InA:=false)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}
NumberRedSteps:=0;
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
n:=Ncols(T);m:=Nrows(T);

Dens:=[];
Nums:=[];
DENNUM:=[];
MM:=Transpose(T);
for i in [1..n] do

	DENNUM:=[[Numerator(j),Denominator(j)]:j in Eltseq(MM[i])];
	Append(~Dens,LCM([j[2]:j in DENNUM]) );
	Append(~Nums,GCD([j[1]:j in DENNUM]) );
end for;
D:=DiagonalMatrix([K!(Dens[i])/K!(Nums[i]):i in [1..n]]);
NormShifts:=[-Degree(Nums[i])+Degree(Dens[i]):i in [1..n]];

//lc:=LCM([Denominator(i):i in Eltseq(T)]);

T:=Parent(ZeroMatrix(kt,n,n))!(T*D);

s:=1;

if m eq 1 then return T,Maximum([Deg(j):j in ElementToSequence(T[1])]),0; end if;


VectorNorm:=[Norm1(Eltseq(T[i]),NormShifts):i in [1..n]];
p:=[];
Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);

while s lt m do
	M:=ZeroMatrix(k,m,n);
	for i in [1..m] do
		for j in [1..m] do
			if not T[i,j] eq 0 and Degree(T[i,j])-NormShifts[j] eq VectorNorm[i] then			
				M[i,j]:=LeadingCoefficient(T[i,j]);				
			end if; 				
		end for;
	end for;
	Mprime,P:=EchelonForm(M);
	s:=Rank(Mprime);
	NumberRedSteps:=NumberRedSteps+m-s;



	if s lt m then
			//Transform P in a shape to read out all relations
		Su:=SubmatrixRange(P,s+1,1,n,n);
		P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
		for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			for i in [1..u-1] do
				if not P[j,i] eq 0 then								
				AddRow(~T,P[j,i]/P[j,u]*t^(VectorNorm[u]-VectorNorm[i]),i,u);
				end if;
			end for;
			tmp:=Eltseq(T[u]);
			VectorNorm[u]:=Norm1(tmp,NormShifts);
//			Maximum([Degree(tmp[l])-NormShifts[l]:l in [1..#tmp]]);
		end for;
//			Append(~LLL,T);
		p:=[];
		Sort(~VectorNorm,~p);
		T:=Matrix([T[i]:i in Eltseq(p)]);
	end if;
end while;	
print"Number of RedSteps =",NumberRedSteps;
//PutInZ(LLL);
if InA then 
	return D,T,NormShifts,[VectorNorm[i]:i in [1..n]],NumberRedSteps;
else
	return T*D^-1,[VectorNorm[i]:i in [1..n]],NumberRedSteps;
end if;
end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Norm(Element::FldFunElt, I::Rec)->FldRatElt
{}
F:=Parent(Element);
Expos:=[0:i in PlacesAtInfinity(F)];
E:=[i`e:i in PlacesAtInfinity(F)];
for i in I`Factorization do 
	Expos[i[2]]:=i[3];
end for;
return -Minimum([(PValuation(Element,PlacesAtInfinity(F)[j])-Expos[j])/E[j]:j in [1..#E]]);

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Norm(Vec::SeqEnum, Values::SeqEnum)->FldRatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}
tmp:=[i : i in [1..#Values]|not Vec[i] eq 0];
return Maximum([Degree(Vec[i])+Values[i]:i in tmp]);

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic ReductionAlgorithm(T::AlgMatElt, Values::SeqEnum)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}


Vals:=SetToSequence(Set(Values));
lc,T,VectorNorm,NumberRedSteps:=ReductionAlgorithm(T:InA:=true);
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);

if #Vals eq 1 then 
	return (1/K!lc)*T,VectorNorm,NumberRedSteps;
end if;

l:=1;
VectorNorm:=[Norm(i,Values):i in RowSequence(T)];
p:=[];Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);
while l le #Vals do
	ColumnIndex:=[ y : y in  [1..#Values] | Values[y] eq Vals[l]];
	RowIndex:=[ y : y in  [1..#VectorNorm] | (VectorNorm[y]-Ceiling(VectorNorm[y])) eq Vals[l]];

	m:=#RowIndex;	n:=#ColumnIndex;
	M:=ZeroMatrix(k,m,n);

	if m gt 1 then
	
		for i in [1..m] do
			for j in [1..n] do
				if not T[RowIndex[i],ColumnIndex[j]] eq 0 and Degree(T[RowIndex[i],ColumnIndex[j]])+Vals[l] eq VectorNorm[RowIndex[i]] then			
					M[i,j]:=LeadingCoefficient(T[RowIndex[i],ColumnIndex[j]]);				
				end if; 				
			end for;
		end for;
		Mprime,P:=EchelonForm(M);
		s:=Rank(Mprime);
		if s eq m then 
			if m lt n and not Vals[l] in [Vals[i]:i in [l+1..#Vals]] then 
				Append(~Vals,Vals[l]);
			end if;	
						
		else
			NumberRedSteps:=NumberRedSteps+m-s;


			Su:=SubmatrixRange(P,s+1,1,m,m);
			P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
			for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			jj:=RowIndex[u];
				for i in [1..u-1] do
					
					if not P[j,i] eq 0 then
						ii:=RowIndex[i];
						AddRow(~T,P[j,i]/P[j,u]*t^(Ceiling(VectorNorm[jj])-Ceiling(VectorNorm[ii])),ii,jj);
					end if;	
				end for;

				VectorNorm[jj]:=Norm(ElementToSequence(T[jj]),Values);
			
				if not VectorNorm[jj]-Ceiling(VectorNorm[jj]) in [Vals[i]:i in [l+1..#Vals]] then 
					Append(~Vals,VectorNorm[jj]-Ceiling(VectorNorm[jj]));
				end if;				

			end for;
			p:=[];
			Sort(~VectorNorm,~p);
			T:=Matrix([T[i]:i in Eltseq(p)]);
		end if;

	end if;
	l:=l+1;
end while;	
print"Number of RedSteps =",NumberRedSteps;
return  (1/K!lc)*T,[i-Degree(lc):i in VectorNorm],NumberRedSteps;

end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic ReductionAlgorithm2(T::AlgMatElt, Values::SeqEnum)->AlgMatElt
{Let the rows of T be a lattice L in K^n, Output: T, whose rows form a reduced basis of L}

print"ALST";
Vals:=SetToSequence(Set(Values));
D,T,NormShifts,VectorNorm,NumberRedSteps:=ReductionAlgorithm2(T:InA:=true);
K:=BaseRing(T);k:=BaseRing(K);kt<t>:=PolynomialRing(k);
ShiftValues:=[Values[j]-NormShifts[j]:j in [1..#Values]];
ShiftValues;
if #Vals eq 1 then 
	return T*D^-1,VectorNorm,NumberRedSteps;
end if;

l:=1;

VectorNorm:=[Norm(i,ShiftValues):i in RowSequence(T)];
Sort(~VectorNorm,~p);
T:=Matrix([T[i]:i in Eltseq(p)]);
while l le #Vals do
	ColumnIndex:=[ y : y in  [1..#Values] | Values[y] eq Vals[l]];
	RowIndex:=[ y : y in  [1..#VectorNorm] | (VectorNorm[y]-Ceiling(VectorNorm[y])) eq Vals[l]];

	m:=#RowIndex;	n:=#ColumnIndex;
	M:=ZeroMatrix(k,m,n);

	if m gt 1 then
	
		for i in [1..m] do
			for j in [1..n] do
				if Degree(T[RowIndex[i],ColumnIndex[j]])+Vals[l]-NormShifts[ColumnIndex[j]] eq VectorNorm[RowIndex[i]] then			
					M[i,j]:=LeadingCoefficient(T[RowIndex[i],ColumnIndex[j]]);				
				end if; 				
			end for;
		end for;
		Mprime,P:=EchelonForm(M);
		s:=Rank(Mprime);
		if s eq m then 
			if m lt n and not Vals[l] in [Vals[i]:i in [l+1..#Vals]] then 
				Append(~Vals,Vals[l]);
			end if;	
						
		else
			NumberRedSteps:=NumberRedSteps+m-s;


			Su:=SubmatrixRange(P,s+1,1,m,m);
			P:=ReverseColumns(EchelonForm(ReverseColumns(Su)));
			for j in [1..m-s] do
			tmp:=exists(u){  y : y in  [m..1 by -1] | not P[j,y] eq 0 }; 
			jj:=RowIndex[u];
				for i in [1..u-1] do
					
					if not P[j,i] eq 0 then
						ii:=RowIndex[i];
						AddRow(~T,P[j,i]/P[j,u]*t^(Ceiling(VectorNorm[jj])-Ceiling(VectorNorm[ii])),ii,jj);
					end if;	
				end for;

				VectorNorm[jj]:=Norm(ElementToSequence(T[jj]),ShiftValues);
			
				if not VectorNorm[jj]-Ceiling(VectorNorm[jj]) in [Vals[i]:i in [l+1..#Vals]] then 
					Append(~Vals,VectorNorm[jj]-Ceiling(VectorNorm[jj]));
				end if;				

			end for;
			p:=[];
			Sort(~VectorNorm,~p);
			T:=Matrix([T[i]:i in Eltseq(p)]);
		end if;

	end if;
	l:=l+1;
end while;	
print"Number of RedSteps =",NumberRedSteps;
return  T*D^-1,[i:i in VectorNorm],NumberRedSteps;

end intrinsic;




/*//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
intrinsic RRSpace(D::Rec:semi:=true)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}
tt1:=Realtime();
Ifin:=(D`FiniteIdeal)^-1;	Iinf:=(D`InfiniteIdeal)^-1;
F:=Ifin`Parent;	  n:=Degree(F);
correctionterm:=0;
if #PlacesAtInfinity(F) eq 1 and #Iinf`Factorization gt 0 then
	correctionterm:=Iinf`Factorization[1,3]/PlacesAtInfinity(F)[1]`e;
	Iinf:=PlacesAtInfinity(F)[1]^0;
end if;
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F)); t:=A.1;

//if DEGREE(D) lt 0 then return [],[F!0],0,[],[0]; end if;

//////////////////////////Producing bases/////////////////////////
Bfin,finitefac:=IdealBaseRR(Ifin);
Montes(F2, t);
if semi eq true then
	Binf,_,_,_,_,infex:=pBasisRR(Iinf,t:Reduced:=false);
	else
	Binf,_,_,_,_,infex:=pBasisRR(Iinf,t:Reduced:=true);	
end if;	

wholefac:=finitefac;	
Bprime:=[TransMap(i,F):i in Binf];
InfPrimes:=PlacesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;

if not semi then
for i in Binf do
	Append(~Values,-Minimum([   ( PValuation(i,InfPrimes[j]) -Expo[j]   )/Es[j]:j in [1..#Es]]));
end for;
end if;
print"Signature=",Values;
M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);	M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);
T:=M1*M2^(-1);
print"Initialisierungen dauerte x sec mit x=",Realtime()-tt1;
tt2:=Realtime();
if not semi then
	RedT,SuccMin:=ReductionAlgorithm(T,Values);
else
	RedT,SuccMin:=ReductionAlgorithm(T);
end if;
SuccMin:=[i+infex+Deg(finitefac)+correctionterm:i in SuccMin];

print"Reduction dauerte x sec mit x=",Realtime()-tt2;
print"\n succmin",SuccMin;
redbasis:=[finitefac* &+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
basis:=[];	dimlist:=[];	templist:=[];	Dim:=0;
for i in [1..n] do 
//	Append(~templist,Floor(-SuccMin[i])+1);
	if Floor(-SuccMin[i]) ge 0 then 
		Append(~dimlist,-Ceiling(SuccMin[i])+1);
	end if;
end for;

if #dimlist eq 0 then
	dim:=0;
else
	dim:=&+dimlist;
end if;
return T,RedT,dim,VectorSpace(ConstantField(F),dim),SuccMin;

end intrinsic;*/

intrinsic Inverse(M::AlgMatElt,d::FldFunRatUElt)->AlgMatElt
{Speeds up inversion of a matrix over the rational field}

K:=BaseRing(M);
R:=PolynomialRing(ConstantField(K));
Mpol:=ChangeRing(d*M,R);
H,R:=HermiteForm(Mpol);
return d*ChangeRing(H,K)^-1*R;
end intrinsic;

 //////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic RRSpace2(D::Rec)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

F:=D`FiniteIdeal`Parent;
if DEGREE(D) lt 0 then return [],[F!0],0,[],[0]; end if;

if Hight(D) lt 3*GENUS(F) then
	print"no reduction, because of small hight of D";
	return RRSpace(D);
end if;
InfPrimes:=PlacesAtInfinity(F); A:=Divisor(&*[i^i`e: i in InfPrimes]);
D0:=D;
D,r,a:=HightReduction(D,A);
count:=0;
for i in Support(D) do

if not i in Support(D0) then count:=count+1; print"count=",count;end if;

end for;
redbasistmp,SuccMin:=RRSpace(D);

redbasis:=[ a* i:i in redbasistmp];
dimlist:=[];
for i in [1..#SuccMin] do 
	temp:=-SuccMin[i]+r;
	if temp ge 0 then 
		Append(~dimlist,-Ceiling(SuccMin[i])+r+1);
	end if;
end for;

if #dimlist eq 0 then
	dim:=0;
else
	dim:=&+dimlist;
end if;
return redbasis,dimlist,dim,VectorSpace(ConstantField(F),dim),[i+r:i in SuccMin];

end intrinsic;

/*//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
intrinsic RRSpaceFast(D::DivFunElt)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

tt1:=Realtime();
Ifin,Iinf:=Ideals(-D);
F:=FunctionField(D);	  n:=Degree(F);
K:=BaseField(F);

if Degree(D) lt 0 then return [],[F!0],0,[],[0]; end if;

//////////////////////////Producing bases/////////////////////////
Bfin:=Basis(Ifin);
GCDDenominator:=BaseField(F)!Denominator(Bfin[n]); r:=Deg(GCDDenominator);
Bfintmp:=[GCDDenominator*i:i in Bfin];

Binf:=Basis(Iinf);
InfPrimes:=Zeros(F!(1/K.1));	 Es:=[RamificationIndex(i):i in InfPrimes];	Values:=[]; Expo:=[];

for jj in InfPrimes do
	Append(~Expo,Valuation(Iinf,Ideal(jj)));
end for;

for i in Binf do
	Append(~Values,-Minimum([   ( Valuation(i,InfPrimes[j]) -Expo[j]   )/Es[j]:j in [1..#Es]]));
end for;
print"Signatura=",Values;
Valli,Posi:=Maximum(Values);
for i in [1..#Values] do

	if Values[i] lt Valli then
		Binf[i]:=Binf[i]+Binf[Posi];		
	end if;

end for;
Values:=[Valli:i in Values];

M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfintmp]);	M2:=Matrix(K,n,&cat [Eltseq(i):i in Binf]);
T:=M1*M2^(-1);
print"Initialisierungen dauerte x sec mit x=",Realtime()-tt1;
tt2:=Realtime();
RedT,SuccMin:=ReductionAlgorithm(T,Values);
SuccMin:=[i-r:i in SuccMin];
print"Reduction dauerte x sec mit x=",Realtime()-tt2;

redbasis:=[1/GCDDenominator* &+[ Binf[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
basis:=[];	dimlist:=[];	templist:=[];	Dim:=0;
for i in [1..n] do 
	Append(~templist,Floor(-SuccMin[i])+1);
	if Floor(-SuccMin[i]) ge 0 then 
		Append(~dimlist,-Ceiling(SuccMin[i])+1);
	end if;
end for;

//Basis determination
for i in [1..#SuccMin] do
	if SuccMin[i] le 0 then
		basis:=basis cat [K.1^j*redbasis[i]:j in [0..-SuccMin[i]]];
		
	end if;

end for;

if #dimlist eq 0 then
	dim:=0;
else
	dim:=&+dimlist;
end if;
return redbasis,basis,SuccMin;

end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic RRSpace2(D::DivFunElt)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

F:=FunctionField(D);
if Degree(D) lt 0 then return [],[F!0],0,[],[0]; end if;

if Degree(PoleDivisor(D))+Degree(ZeroDivisor(D)) lt 3*Genus(F) then
	print"no reduction, because of small hight of D";
	return RRSpace(D);
end if;
A:=ZeroDivisor(PrincipalDivisor(F!(1/BaseField(F).1)));
D,r,a:=HightReduction(D,A);

redbasistmp,_,_,_,SuccMin:=RRSpace(D);

redbasis:=[ a* i:i in redbasistmp];
dimlist:=[];
for i in [1..#SuccMin] do 
	temp:=-SuccMin[i]+r;
	if temp ge 0 then 
		Append(~dimlist,-Ceiling(SuccMin[i])+r+1);
	end if;
end for;

if #dimlist eq 0 then
	dim:=0;
else
	dim:=&+dimlist;
end if;
return redbasis,dimlist,dim,VectorSpace(ConstantField(F),dim),[i+r:i in SuccMin];

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//////////////////Prinicipillity Test/////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic IsPrincipal(D::Rec)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

tt1:=Realtime();
Ifin:=(D`FiniteIdeal)^-1;	Iinf:=(D`InfiniteIdeal)^-1;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;

K:=BaseField(F);	A:=PolynomialRing(ConstantField(F)); t:=A.1;

if not DEGREE(D) eq 0 then return false,0; end if;

//////////////////////////Producing bases/////////////////////////
Bfin:=IdealBasis(Ifin);
GCDDenominator:=BaseField(F)!Denominator(Bfin[n]); r:=Deg(GCDDenominator);
Bfintmp:=[GCDDenominator*i:i in Bfin];

MontesH(F2, t : Basis:=true);
Binf:=pHermiteBasis(Iinf,t);
Bprime:=[TransMap(i,F):i in Binf];

InfPrimes:=PlacesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];

for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;

for i in Binf do
	Append(~Values,-Minimum([   ( PValuation(i,InfPrimes[j]) -Expo[j]   )/Es[j]:j in [1..#Es]]));
end for;

Valli,Posi:=Maximum(Values);
for i in [1..#Values] do

	if Values[i] lt Valli then
		Bprime[i]:=Bprime[i]+Bprime[Posi];		
	end if;

end for;
Values:=[Valli:i in Values];
print"Values",Values;


M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfintmp]);	M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);
T:=M1*M2^(-1);

print"Initialisierungen dauerte x sec mit x=",Realtime()-tt1;
tt2:=Realtime();
Check,ShortVec:=ReductionAlgorithm(T,r);

print"Reduction dauerte x sec mit x=",Realtime()-tt2;

if Check eq false then return false,F!0; end if;

ShortVec:=1/GCDDenominator* &+[ Bprime[j]*ShortVec[j] :j in [1..n]]  ;

return true,ShortVec;

end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////*/


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////
//    New routines concerning the LFRF algorithm
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////

intrinsic calculateBasesVals(tt)-> SeqEnum
    {Calculate all crossed values for the Okutsu basis of the prime ideal determined by the type tt.}

    r := [#t - 1 : t in tt];
    inc:=1;
    PhiVals := [* [] : k in [1..#tt] *];
    BasesVals := [ [] : k in [1..#tt] ];
    for k in [1..#tt] do
        PhiVals[k] := [tt[k,1]`ProdQuotsVals[Degree(tt[k,j]`Phi)+1]: j in [1..r[k]+1]];
        PhiVals[k] := [[* x : jj in [1..#tt] *]: x in PhiVals[k]];
        t1 := tt[k];
        for l in [1..k-1] do
            t2 := tt[l];
	    IndexOfCoincidence(~t1,~t2,~inc);
            Ref1:=Append(t1[inc]`Refinements,[* t1[inc]`Phi,t1[inc]`slope *]);
            Ref2:=Append(t2[inc]`Refinements,[* t2[inc]`Phi,t2[inc]`slope *]);
            minlength:=Min(#Ref1,#Ref2);
            ii:=2;
            while ii le minlength and Ref1[ii,1] eq Ref2[ii,1] do 
                ii+:=1;    
            end while;
            hiddenslope1:=Ref1[ii-1,2];
            hiddenslope2:=Ref2[ii-1,2];
            minslope:=Min([hiddenslope1,hiddenslope2]);
            entry:=(t1[inc]`V+minslope)/t1[inc]`prode;
            if Ref1[ii-1,1] eq t1[inc]`Phi then
                PhiVals[k,inc,l]:=(t1[inc]`V+hiddenslope2)/t1[inc]`prode;
            else
                PhiVals[k,inc,l]:=entry;
            end if;
            if Ref2[ii-1,1] eq t2[inc]`Phi then
                PhiVals[l,inc,k]:=(t1[inc]`V+hiddenslope1)/t1[inc]`prode;
            else
                PhiVals[l,inc,k]:=entry;
            end if;
            entry:=entry/Degree(t1[inc]`Phi);
            for ii:=inc+1 to r[k]+1 do
                PhiVals[k,ii,l]:=Degree(t1[ii]`Phi)*entry;
            end for;    
            for ii:=inc+1 to r[l]+1 do
                PhiVals[l,ii,k]:=Degree(t2[ii]`Phi)*entry;
            end for;    	    
        end for;
    end for;
    for k in [1..#tt] do
        BasesVals[k] := [[* 0: j in [1..#tt] *]: i in [1..Degree(tt[k,1]`Phi)]];        
        for j:=1 to r[k] do
            Enlarged := BasesVals[k];
            for jj:=1 to tt[k,j]`e*tt[k,j]`f-1 do
                Enlarged cat:= [[* jj*PhiVals[k,j,l]+x[l]: l in [1..#tt] *]: x in BasesVals[k]];
            end for;
            BasesVals[k] := Enlarged;
        end for;    
        Append(~BasesVals[k],PhiVals[k,r[k]+1]);
    end for;
    return BasesVals;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
/*

intrinsic calculateBasis(K, p, IExponents)-> List, List, BoolElt
    {Compute the pHermite basis of the fractional ideal I with v_P(I), P|p, given by IExponents}

    vprintf hds,1: "K has %o distinct tree(s) for p = %o.\n", #K`TreesIntervals[p], p;

    allBases := [* *];
    allBasesVals := [* *];
    allBasesIndices := [* *];
    allMinPhiVals := [* *];
    // Process each separate tree of types to combine it into a single integral basis.
    for tree in K`TreesIntervals[p] do
	basisIndices, basisVals, minPhiVals := LFRF(K, p, tree, IExponents[tree]);
//print basisIndices, basisVals, minPhiVals;
        Append(~allBasesVals, basisVals);
        Append(~allBasesIndices, basisIndices);
        Append(~allMinPhiVals, minPhiVals);
    end for;

    maxVal := Max([v[#v-1] : v in allBasesVals]);

    for m in [1..#K`TreesIntervals[p]] do
        vals := allBasesVals[m];
        minPhiVals:=allMinPhiVals[m];
	maxTreeVal:=vals[#vals-1];
	tree:=K`TreesIntervals[p,m];
        for k in tree do
	    j:=k-tree[1]+1;
	    order:=#K`PrimeIdeals[p,k]`Type;
            V:=K`PrimeIdeals[p,k]`Type[order]`V;
	    slope:=K`PrimeIdeals[p,k]`e*(minPhiVals[j]+maxVal-maxTreeVal)-V;
	    SFL(~K,~K`PrimeIdeals[p,k],Ceiling(slope));
	    length:=#K`PrimeIdeals[p,k]`PBasis;
	    K`PrimeIdeals[p,k]`PBasis[length]:=K`PrimeIdeals[p,k]`Type[order]`Phi;
	end for;
        
        basis := calculateBasisFromIndices(K, p, tree, allBasesIndices[m]);
//print basis;
        Append(~allBases, basis);
    end for;

    // If there are multiple disparate trees of types, take each of their combined
    // integral bases and combine those into a single unified integral basis.
    basis, basisVals := combineDisparateBases(allBases, allBasesVals);
    IntVals:=[Floor(x) : x in basisVals];

    //check that the index is correct
    normexponent:=&+[ K`PrimeIdeals[p,i]`f * IExponents[i] : i in [1..#IExponents] ];
    checkindex:=&+IntVals + normexponent eq K`LocalIndex[p];

    vprint hds,4: "p =", p, "exponents:", IExponents;
    n:=#basis;
    dens := [ p^(IntVals[n]-nu) : nu  in IntVals ];
    seq:=&cat[ Reverse([ PolynomialRing(ConstantField(K))!(c*dens[i]): c in Coefficients(basis[i]) ]): i in [n..1 by -1] ];
    HA := UpperTriangularMatrix(seq);
    vprint hds,4: HA;
    HA:= HermiteForm(HA);
    seq:=&cat[[HA[i,j] div HA[i,i]: j in [i..n]]: i in [1..n]];   
    HA := UpperTriangularMatrix(seq);
    vprint hds,4: HA;
    vprint hds,1: "--------------------------------";

    return HA, Reverse(IntVals), checkindex,basis;
end intrinsic; // calculateBasis()


/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


intrinsic calculateIntBasis(K, p, IExponents)-> List, List, BoolElt
    {Compute the pHermite basis of the fractional ideal I with v_P(I), P|p, given by IExponents}

    vprintf hds,1: "K has %o distinct tree(s) for p = %o.\n", #K`TreesIntervals[p], p;

    allBases := [* *];
    allBasesVals := [* *];
    allBasesIndices := [* *];
    allMinPhiVals := [* *];
    // Process each separate tree of types to combine it into a single integral basis.
    for tree in K`TreesIntervals[p] do
	basisIndices, basisVals, minPhiVals := LFRF(K, p, tree, IExponents[tree]);
//print basisIndices, basisVals, minPhiVals;
        Append(~allBasesVals, basisVals);
        Append(~allBasesIndices, basisIndices);
        Append(~allMinPhiVals, minPhiVals);
    end for;

    maxVal := Max([v[#v-1] : v in allBasesVals]);

    for m in [1..#K`TreesIntervals[p]] do
        vals := allBasesVals[m];
        minPhiVals:=allMinPhiVals[m];
	maxTreeVal:=vals[#vals-1];
	tree:=K`TreesIntervals[p,m];
        for k in tree do
	    j:=k-tree[1]+1;
	    order:=#K`PrimeIdeals[p,k]`Type;
            V:=K`PrimeIdeals[p,k]`Type[order]`V;
	    slope:=K`PrimeIdeals[p,k]`e*(minPhiVals[j]+maxVal-maxTreeVal)-V;
	    SFL(~K,~K`PrimeIdeals[p,k],Ceiling(slope));
	    length:=#K`PrimeIdeals[p,k]`PBasis;
	    K`PrimeIdeals[p,k]`PBasis[length]:=K`PrimeIdeals[p,k]`Type[order]`Phi;
	end for;
        
        basis := calculateBasisFromIndices(K, p, tree, allBasesIndices[m]);
//print basis;
        Append(~allBases, basis);
    end for;

    // If there are multiple disparate trees of types, take each of their combined
    // integral bases and combine those into a single unified integral basis.
    basis, basisVals := combineDisparateBases(allBases, allBasesVals);
    IntVals:=[Floor(x) : x in basisVals];
	
	basis:=[Evaluate(i,K.1):i in basis];

    return [basis[i]/BaseField(K).1^IntVals[i]:i in [1..Degree(K)]];
end intrinsic; // calculateBasis()


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic calculateBasisFromIndices(K, p, tree, basisIndices)-> SeqEnum
    {}

    return [ &*[K`PrimeIdeals[p,tree[k]]`PBasis[j[k]] : k in [1..#tree]] : j in basisIndices ];
end intrinsic; // calculateBasisFromIndices()

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////



intrinsic pHermiteBasis(I, p)-> SeqEnum, BoolElt
    {}
MontesH(I`Parent,p: Basis:=true);
    Factorization(~I);
    Iexponents:=[0: i in [1..#I`Parent`PrimeIdeals[p]]];
    for x in I`Factorization do
	if x[1] eq p then 
	    Iexponents[x[2]]:=x[3];
	end if;
    end for;
    basis, vals, checkindex := calculateBasis(I`Parent, p, Iexponents);
    n:=#vals;

    return [ I`Parent![ basis[l,k] : k in [n..1 by -1] ]/BaseField(I`Parent)!p^vals[l] : l in [n..1 by -1] ], checkindex;
end intrinsic; // pHermiteBasis()




/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic pIntegralBasis(I, p)-> SeqEnum, BoolElt
    {}
MontesH(I`Parent,p: Basis:=true);
    Factorization(~I);
    Iexponents:=[0: i in [1..#I`Parent`PrimeIdeals[p]]];
    for x in I`Factorization do
	if x[1] eq p then 
	    Iexponents[x[2]]:=x[3];
	end if;
    end for;

    return calculateIntBasis(I`Parent, p, Iexponents);
end intrinsic; // pHermiteBasis()


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////*/

intrinsic calculatePhiVal(level)-> ExtRe
    {}
    return (level`V + level`slope)/level`prode;
end intrinsic 

/*//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic combineDisparateBases(bases, basesVals)->List, List
    {Combine the bases of n trees, which have already had their bases combined.}

    if #bases eq 1 then
        vprint hds,2: "\nOnly 1 tree, basis complete.";
        
        return Prune(bases[1]), Prune(basesVals[1]);
    end if;
    vprintf hds,2: "\nThere are %o trees, bases must be combined.\n", #bases;
    vprintf hds,2: "[combineDisparateBases]\n";
 
    basis := [ ];
    basisValues := [* *];
 
    vals := basesVals;
    r := [#v : v in vals];
    j := [1 : v in vals];

    for i in [1..&+r-#r] do
        step := [* vals[k,j[k]] : k in [1..#vals] *];   
        minIndex := 1;
        minVal := step[1];
        for k in [2..#step] do
            if step[k] lt minVal then
                minIndex := k;
                minVal := step[k];
            end if;
        end for;

        Append(~basis, &*[bases[k,j[k]] : k in [1..#bases]]);
        Append(~basisValues, minVal);
        j[minIndex] +:= 1;
    end for;

    return basis, basisValues;
end intrinsic; // combineDisparateBases()

/////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////


intrinsic IdealBasis(I::Rec)->SeqEnum
    {Compute a Hermite basis of the ideal I}

    IdealBasis(~I`Parent,~I);
    return I`Basis;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IdealBasis(~K::FldFun, ~I::Rec)
    {Compute a Hermite basis of the ideal I}

//if not assigned I`Basis then
    if not assigned K`FactorizedDiscriminant then
	K`FactorizedDiscriminant:=Factorization( PolynomialRing(ConstantField(K))! Discriminant(DefiningPolynomial(K)));
    end if;
    discfactors:=[x[1]: x in K`FactorizedDiscriminant];
    primes:=SetToSequence(Set(RationalRadical(I) cat discfactors));
    I`Basis, Check:= SIdealBasis(K, I, primes);
    if not Check then print "falla l'index"; end if;
//end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic LFRF(K, p, tree, a)-> List, List, List
    {Combines the bases of the types of a tree using the LFRF algorithm.}

    vals:=[K`PrimeIdeals[p,j]`PBasisVals : j in tree];
    minPhiVals := [ RationalField() | vals[k,#vals[k],k] : k in [1..#tree] ];
    wExps:=[a[j-tree[1]+1]/K`PrimeIdeals[p,j]`e: j in tree];

    if #tree eq 1 then
	vprintf hds,2: "\n[oneTypeTree]\n";

	vals:=vals[1];
	vprint hds,3: vals;
	basisValues := [* v[1]-wExps[1]: v in vals *];
	basisValues[#basisValues] := Infinity();
	basisIndices := [[i] : i in [1..#vals]];
        return basisIndices, basisValues, minPhiVals;
    end if;

    vprintf hds,2: "\n[combineBasesLFRF]\n";

    basisValues := [* *];
    basisIndices := [ ];
    completedPhis := [ ];
    nP := [#v : v in vals];
    j := [1 : t in tree];
    for k in [1..#tree] do
        vals[k,#vals[k],k] := Infinity();
    end for;

    for i in [1..&+nP-#nP] do
        step := [* &+[vals[l,j[l],k] : l in Exclude([1..#tree],k)] : k in [1..#tree] *];
        S := step;
        for k in [1..#tree] do
            S[k] +:= vals[k,j[k],k]-wExps[k];
        end for;   
        minVal, minIndex := Minimum([v : v in S]);
	for k in completedPhis do
	    requiredValue := Floor(minVal) - step[k] + wExps[k];
	    if requiredValue gt minPhiVals[k] then
		minPhiVals[k] := requiredValue;
	    end if;
	end for;
        Append(~basisValues, minVal);
        Append(~basisIndices, j);

        // Increment the minimum index in J and check if we've reached Phi_q.
        j[minIndex] +:= 1;
        if j[minIndex] eq nP[minIndex] then
            Append(~completedPhis, minIndex);
        end if;
    end for;
    Append(~basisValues, Infinity());
    Append(~basisIndices, nP);
    return basisIndices, basisValues, minPhiVals;
end intrinsic; //  LFRF()

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////*/

intrinsic MontesH(K::FldFun,p::RngUPolElt: Basis:=false)
    {Factorize p and eventually compute P-bases for all P|p.}

    require IsPrime(p): "First argument must be a prime integer";

Rt:=Parent(p);
Rxt<x>:=PolynomialRing(Rt);
RXT<T>:=BaseField(K);
Pol:=Rxt!DefiningPolynomial(K);
//    require (CoefficientRing(Pol) eq Integers() and IsMonic(Pol)): "Number Field must be defined by a //monic integral polynomial";

    if not assigned K`FactorizedPrimes then
    K`FactorizedPrimes:=[];
    K`PrimeIdeals:=AssociativeArray();
    K`LocalIndex:=AssociativeArray();
    K`TreesIntervals:=AssociativeArray();

end if; 

    if p in K`FactorizedPrimes then
//print"K`PrimeIdeals[p,1]`PBasis=",K`PrimeIdeals[p,1]`PBasis;    
	if not Basis or assigned K`PrimeIdeals[p,1]`PBasis then
	    return;
	end if;
    end if;
    Fp,map:=ResidueClassField(p);
    Fpy<y>:=PolynomialRing(Fp:Global := false);
    fa:=Factorization(Fpy![map(i): i in Coefficients(Pol)]);
    totalindex:=0;   
    TreesIntervals:=[];
    K`PrimeIdeals[p]:=[];
    right:=0;
    Psi:=0;
    logLG:=0;
    primeid:=rec<IdealRecord|Parent:=K,IsPrime:=true,IsIntegral:=true,IntegerGenerator:=p>;
    for factor in fa do
	vprint montestalk,2: "Analyzing irreducible factor modulo p: ",factor[1];
	level:=InitialLevel(map,p,Pol,factor[1],factor[2]: BAS:=Basis);
	Leaves:=[];
	MontesloopH(level,~Leaves,~totalindex: Basisloop:=Basis);
	Append(~TreesIntervals,[right+1..right+#Leaves]);  
	if Basis then
	    BasesVals:=calculateBasesVals(Leaves);
	end if;
	for k:=1 to #Leaves do
	    primeid`Position:=right+k;
	    primeid`Factorization:=[*[*p,primeid`Position,1*]*];
	    primeid`FactorizationString:=FactorListToString(primeid`Factorization);
	    primeid`Type:=Leaves[k];
	    primeid`e:=primeid`Type[#primeid`Type]`prode;
	    primeid`f:=primeid`Type[#primeid`Type]`prodf; 
	    PrescribedValue(~primeid`Type,1,~Psi,~logLG);
	    primeid`LocalGenerator:=Evaluate(Psi,K.1)*RXT!p^logLG[1];
	    primeid`LogLG:=logLG;
	    primeid`exponent:=primeid`Type[1]`sfl[1];
	    if Basis then
		primeid`PBasis:=primeid`Type[1]`ProdQuots;
		primeid`PBasisVals:=BasesVals[k];
		delete primeid`Type[1]`ProdQuots;
		delete primeid`Type[1]`ProdQuotsVals;
	    end if;
	    Append(~K`PrimeIdeals[p],primeid); 
	end for;
	right+:=#Leaves;
    end for;
    if #K`PrimeIdeals[p] eq 1 then
	K`PrimeIdeals[p,1]`Type[#K`PrimeIdeals[p,1]`Type]`Phi:=Pol;
	K`PrimeIdeals[p,1]`Type[#K`PrimeIdeals[p,1]`Type]`slope:=Infinity();
    end if;
    Append(~K`FactorizedPrimes,p);
    Sort(~K`FactorizedPrimes);
    K`LocalIndex[p]:=totalindex;
    K`TreesIntervals[p]:=TreesIntervals;
    CrossedValues(~K,p);
end intrinsic; // MontesH()

//////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic MontesloopH(level,~Leaves,~totalindex: Basisloop:=false)
{}
	
Stack:=[[level]];
while #Stack gt 0 do	  
    type:=Stack[#Stack];
    Prune(~Stack);
    r:=#type;
    if Basisloop then
	EnlargedBasis:=type[1]`ProdQuots;
	lengthBasis:=#EnlargedBasis;
	efmax:=1;
	powerphi:=type[r]`Phi;
    end if;    
vprint montestalk,2:  "Analyzing type of order ",r;
vprint montestalk,2:  "Phir=",type[r]`Phi;
    Phiadic,Quotients:=Taylor(type[1]`Pol,type[r]`Phi,type[r]`omega);
    sides:=[];
    devsEachSide:=[* *];
    Newton(r,~type,~Phiadic,~sides,~devsEachSide);
    vprint montestalk,3: "Sides of Newton polygon:",sides;
    lengthN:=type[r]`omega;
    indexN:=-type[r]`cuttingslope*(lengthN*(lengthN-1) div 2); 
    if lengthN eq 1 then
	vprint montestalk,2:  "Found a factor of depth  ",r-1;
	LastLevel(Phiadic,~type,sides[1],devsEachSide[1]);
	if Basisloop then
	    Append(~type[1]`ProdQuots,type[r]`Phi);
/*Hier VERMUTLICH FALSCH !!!!!!!
							WAS IST WENN LEVEL'SLOPE GLEUCH UNENDLICH IST?????*/			
	    helpp:=calculatePhiVal(type[r]);
	    if helpp eq Infinity() then
	    print"Could be wrong?";
	    Append(~type[1]`ProdQuotsVals,0);
	    else
	    Append(~type[1]`ProdQuotsVals,helpp);
	    end if;
	end if;
	Append(~Leaves,type);  
	sides:=[];
    end if;
    prevh:=0;	
    for i:=#sides to 1 by -1 do  // GRAN FOR SIDES
	side:=sides[i];
	vprint montestalk,2:  "Analyzing side ",side;        
	type[r]`h:=-Numerator(side[1]);
	type[r]`e:=Denominator(side[1]);
	type[r]`slope:=-side[1];
	type[r]`invh:=InverseMod(type[r]`h,type[r]`e);
	lprime:=(type[r]`invh*type[r]`h-1) div type[r]`e;
	newPi:=Eltseq(type[r]`invh*type[r]`logPhi-lprime*type[r]`logPi);
	Append(~newPi,0);  
	type[r]`logGamma:=type[r]`e*type[r]`logPhi-type[r]`h*type[r]`logPi;
   	Ei:=Integers()!(side[4]-side[2]);
	Hi:=Integers()!(side[3]-side[5]);
	indexN+:=Ei*prevh+((Ei*Hi-Ei-Hi+(Ei div type[r]`e))div 2);
	prevh+:=Hi;
	respol:=0;
	ResidualPolynomial(r,~type,~devsEachSide[i],~respol);
        respol:=respol/LeadingCoefficient(respol);
	factors:=Factorization(respol);
	if Basisloop then
	    vphitheta:=calculatePhiVal(type[r]);
	    addedvalue:=0;
	    fmax:=Max([Degree(x[1]): x in factors]);
	    EnlargedValues:=type[1]`ProdQuotsVals;
	    for jjj:=1 to type[r]`e*fmax-1 do
		addedvalue+:=vphitheta;
		EnlargedValues cat:=[addedvalue+x: x in type[1]`ProdQuotsVals];
	    end for;
	end if;
	vprint montestalk,2: "Monic Residual Polynomial=",respol;
        vprint montestalk,3:  "Factors of R.P.:=",factors;            
// PETIT FOR FACTORS	
        for factor in factors do       
	    vprint montestalk,2: "Analyzing factor of the Res.Pol.",factor[1];
            ta:=type;  
            ta[r]`psi:=factor[1];
	    ta[r]`f:=Degree(ta[r]`psi);
	    ef:=ta[r]`e*ta[r]`f;
	    Representative(~ta);
// IF REFINA-AVANCA
	    if ef eq 1 then
		vprint montestalk,2:  "Refining. Cuttingslope=",-side[1];
		if #sides gt 1 or #factors gt 1 then
		    Append(~ta[r]`Refinements,[* ta[r]`Phi,ta[r]`slope *]);
		end if;
		ta[r]`cuttingslope:=-Integers()!side[1];
		ta[r]`Phi:=ta[r+1]`Phi;
		ta[r]`omega:=factor[2];
		Prune(~ta);  
	    else
		vprint montestalk,2:  "Proceeding to higher order";    
		ta[r+1]`omega:=factor[2];
		ta[r+1]`logPi:=Vector(newPi);
		log:=Eltseq(-(ta[r+1]`V div ta[r]`e)*ta[r]`logPi);
		Append(~log,1);
		ta[r+1]`logPhi:=Vector(log); 
		if Basisloop then
		    if ef gt efmax then
			for exp:=efmax to ef-1 do
			    EnlargedBasis cat:=[powerphi*x: x in ta[1]`ProdQuots];
			    powerphi*:=ta[r]`Phi;
			end for;
			efmax:=ef;
		    end if;
		    lef:=lengthBasis*ef;
		    ta[1]`ProdQuots:=EnlargedBasis[1..lef];	
		    ta[1]`ProdQuotsVals:=EnlargedValues[1..lef];
		end if;
            end if; 
// FINAL IF REFINA-AVANCA
	    Append(~Stack,ta);
        end for;     // FINAL PETIT FOR FACTORS
    end for;         // FINAL GRAN FOR SIDES
    totalindex+:=type[r]`prodf*indexN;
    vprint montestalk, 2: "Added  ",type[r]`prodf*indexN," to the index";
end while;
end intrinsic;



//////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
/*

intrinsic SIdealBasis(K, I::Rec, primelist::SeqEnum)->SeqEnum, BoolElt
    {Compute a local integral basis of I for the given set of primes.}
    Check:=true;
    n:=Degree(I`Parent);
    Numlist:=[];
    Denlist:=[];
    DenlistCRT:=[];
    Factorization(~I);

    for p in primelist do
        MontesH(K, p : Basis:=true);
        // Exponents of the prime ideals
        a := [ 0 : x in K`PrimeIdeals[p] ];
        for P in I`Factorization do
            if P[1] eq p then
                a[P[2]] := P[3];
            end if;
        end for;

        HA, pVals, checkindex := calculateBasis(K, p, a);
	Check:=Check and checkindex;
	nuzero:=pVals[n];
        if nuzero ne 0 or pVals[1] ne 0 then
            Append(~Numlist,HA);
            Append(~Denlist,[BaseField(K)!p^(-v) : v in pVals]);
            Append(~DenlistCRT, [p^(v-nuzero) : v in pVals]);
        end if;
    end for;

    nprimes:=#Denlist;
    if nprimes eq 0 then
        return [K.1^k: k in [0..n-1]], Check;   
    end if;
    Dens:=[&*[Denlist[k,i] : k in [1..nprimes]]: i in [1..n]];
    seq:=[];
    for i := 1 to n-1 do
	multiplier:=PolynomialRing(ConstantField(K))!(Dens[i]/Dens[1]);
	DensCRT:=[DenlistCRT[k,i] : k in [1..nprimes]];
	coeffs := [ multiplier ];
	for j:=i+1 to n do 
	    Nums:=[Numlist[k,i,j] : k in [1..nprimes]]; 
	    Append(~coeffs,multiplier*CRT(Nums,DensCRT));
	end for;
	seq cat:= coeffs;
    end for;
    Append(~seq,PolynomialRing(ConstantField(K))!(Dens[n]/Dens[1]));
    HA := UpperTriangularMatrix(seq);
    H := HermiteForm(HA);
//    if H ne HA then print "no era Hermite!"; end if;
    RowsH:=RowSequence(Dens[1]*H);
    return [ K!Reverse(RowsH[i]): i in [n..1 by -1] ], Check;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic testIdealBasis(I)-> BoolElt
    {}

    correct := true;
    for g in I`Basis do
        for factor in I`Factorization do
            val := PValuation(g, I`Parent`PrimeIdeals[factor[1],factor[2]]);
            correct and:= val ge factor[3];
        end for;
    end for;
    return correct;
end intrinsic; // testIdealBasis()
    
/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
*/
intrinsic Vals(z::FldFunElt,Expo::SeqEnum)->SeqEnum
{}
temp:= PlacesAtInfinity(Parent(z));
return -Minimum([(PValuation(z,temp[j])+Expo[j])/temp[j]`e:j in [1..#temp]]);


end intrinsic;



/////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////Strong-Approximation///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////





intrinsic Red(alpha::FldFunElt,l::RngIntElt,i::RngIntElt)->SeqEnum
{Berechnet pi entwicklung von alpha bis l}
F:=Parent(alpha);
K:=BaseField(F);
R<t>:=PolynomialRing(ConstantField(F));
P:=PlacesAtInfinity(F)[i];
//print"element=",alpha;
LL:=Reduction(TransMap(alpha,InftyField(F)),P,l);
if Degree(P) eq 1 then
	return LL;
else
	return &cat[Eltseq(i):i in LL];
end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////




intrinsic SupportInf(D::Rec)->SeqEnum
{}
F:=D`FiniteIdeal`Parent;
L:=((D`InfiniteIdeal)^1)`Factorization;
PAI:=PlacesAtInfinity(F);
InfinitePrimes:=[];
InfiniteExponents:=[];
for i in L do
	Append(~InfinitePrimes,PAI[i[2]]);
	Append(~InfiniteExponents,i[3]);
end for;

return InfinitePrimes,InfiniteExponents;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



intrinsic Shift(F::FldFun,succ::SeqEnum,i::RngIntElt,ValueMatrix::SeqEnum,PValues::SeqEnum,EE::SeqEnum)->SeqEnum
{Help method for Basis}

r:=0;j:=1;

while i gt r do

	tmp:=r;
	r:=-Ceiling(succ[j])+tmp+1;
	j:=j+1;
end while;

j:=j-1;
if j eq 1 then 
	exp:=i-1;
else
	exp:=i-tmp-1;
end if;
vec:=[];
for i in [1..#PlacesAtInfinity(F)] do
	tt:=(-PlacesAtInfinity(F)[i]`e*exp+PValues[i,j]) mod Abs(EE[i]);

	Append(~vec,[ConstantField(F)!0:i in [1..tt]]   cat   [ValueMatrix[i,j,zz]:zz in [1..#ValueMatrix[i,j]-tt ]]);
end for;


return &cat vec,j,exp;

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/*//////////////////////////////////////////////////////////////////////////
intrinsic Basis(D::Rec,z::FldFunElt)->SeqEnum
{Computes a semi-reduced k[z]-basis of D`FiniteIdeal}
F:=D`FiniteIdeal`Parent;
K:=BaseField(F);
Polz:=InfDiv(z);
d:=DEGREE(Polz);
if  forall{i:i in PlacesAtInfinity(F)|PValuation(z,i) eq 0 } then 
	print"z has no zeros and poles at infinity"; return 0; 
end if;
if d eq 0 then 
print"Degree of (z)_inf is zero"; return 0; 
end if;
_,EE:=SupportInf(Polz);
A,AA:=SupportInf(D);
if #AA lt #PlacesAtInfinity(F) then 
	AAtmp:=[0:i in [1..#PlacesAtInfinity(F)]];

for i in [1..#PlacesAtInfinity(F)] do
	if IsDefined(AA,i) then
		AAtmp[A[i]`Position]:=AA[i];
	end if;	
end for;
AA:=AAtmp;
end if;

if d gt 0 then 
	r:=Ceiling((2*GENUS(F)-1-DEGREE(D))/d)+1;
else
	r:=Floor((2*GENUS(F)-1-DEGREE(D))/d)-1;
end if;

RedBasis,_,_,_,succ:=RRSpace(D+r*Polz);
ValueMatrix:=[];
PValues:=[];
for i in [1..#PlacesAtInfinity(F)] do
	TmpList:=[];
	PTemp:=[];
	for j in [1..Degree(F)] do	
		tmp:=PValuation(RedBasis[j],PlacesAtInfinity(F)[i]);
		Append(~PTemp,tmp);

		shift:=-Floor(tmp/PlacesAtInfinity(F)[i]`e)*PlacesAtInfinity(F)[i]`e+tmp;
		serietmp:=Red(K.1^Floor(tmp/PlacesAtInfinity(F)[i]`e)*RedBasis[j],Abs(EE[i])+  shift ,i );	
		Append(~TmpList,[serietmp[i]:i in [shift+1..#serietmp]]);
	
	end for;

	Append(~ValueMatrix,TmpList);
	Append(~PValues,PTemp);
end for;
Length:=[]; 
for j in [1..#RedBasis] do

	for i in [0..-Ceiling(succ[j])] do
		//Norm der Basiselemente des RR-Raums
		Append(~Length,Ceiling(-Minimum([(PValues[m,j]- i*PlacesAtInfinity(F)[m]`e +AA[m] )/-EE[m]:m in [1..#PlacesAtInfinity(F)]    ])));
	
	end for;
	S:=SetToSequence(Set(Length));
end for;

s:=0;M0:=[];Indices:=[];P0:=[];

for j in [Minimum(S)..Maximum(S)] do

	localindex:=[];

	for m in [1..#Length] do
		if Length[m] eq j then Append(~localindex,m); end if;
	end for;	 
	templist:=[];
	Tranmap:=[];
	for l in localindex do	
		corVec,redindex,expo:=Shift(F,succ,l,ValueMatrix,PValues,EE);
		Append(~templist,corVec);
		Append(~Tranmap,[redindex,expo]);
	end for;
	M:=Transpose(Matrix(M0 cat templist));

	Mprime:=EchelonForm(M);
	Indexnew:=[];
	for l in [s+1..Rank(Mprime)] do
	
		was:=exists(u){  y : y in  [s+1..Ncols(Mprime)] | not Mprime[l,y] eq 0 };	

		Append(~Indices,Tranmap[u-s]);
		Append(~Indexnew,u);
	end for; 


	TMP:=Rows(Transpose(Mprime));
	M0:=M0 cat [ElementToSequence(TMP[i]):i in Indexnew];
	print"M0",M0;
	s:=#M0;
		print"Indices",Indices;
	if s eq Abs(d) then return [BaseField(F).1^i[2]*RedBasis[i[1]]: i in Indices],M0; end if;	
end for;



	return [BaseField(F).1^i[2]*RedBasis[i[1]]: i in Indices],M0;

end intrinsic;*/

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
/*
intrinsic GCD(D1::Rec,D2::Rec)->SeqEnum
{}
L:=[];

a1,b1:=Support(D1);
a2,b2:=Support(D2);
for i in [1..#a1] do
	if a1[i] in a2 then Append(~L,a1[i]); end if;
end for;
return L;

end intrinsic;
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic Intersection(L1::SeqEnum,L2::SeqEnum)->SeqEnum
{blaa}

temp:=[];
temp2:=[];
for i in L1 do

	if i in L2 then Append(~temp,i);
	
	else 
		Append(~temp2,i);
	
	end if;

end for;

return temp,temp2;
end intrinsic;

*/

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////// Computation of	//////////////////////////////////////////////
//////////////////////////////////////////////	integral 		//////////////////////////////////////////////
//////////////////////////////////////////////		Basis		//////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic PhiValuation(F::FldFun,p::RngUPolElt,IndexPhi:: SeqEnum, IndexPrime::RngIntElt)->RngIntElt
{Computes the valuation of Phi at Prime}

P:=IndexPhi[1];
i:=IndexPhi[2];
if i eq 0 then 	
	if Degree(F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi) gt 1 then
		return 0;		
	else
		if F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi eq Parent(F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi).1 then
			return $$(F,p,[P,1],IndexPrime);			
		else	
			tmp:=Minimum([Valuation(Eltseq(F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi)[1],p),F`PrimeIdeals[p,IndexPrime]`Type[1]`slope]);
		//	print"sadasd",tmp,PValuation(F.1,F`PrimeIdeals[p,IndexPrime])/F`PrimeIdeals[p,IndexPrime]`e;
			//Dass kann man auch mit: phi_1=x+a, dann v(theta)=Min(v(a),lambda_1)";	
			return tmp;//PValuation(F.1,F`PrimeIdeals[p,IndexPrime])/F`PrimeIdeals[p,IndexPrime]`e; 
		end if;		
	end if;	

end if;
Q:=IndexPrime;
t1:=F`PrimeIdeals[p,P]`Type;
if P eq Q then
	return (t1[i]`V+Abs(t1[i]`slope))/t1[i]`prode;
end if;
t2:=F`PrimeIdeals[p,Q]`Type;
IndexOfCoincidence(~t1,~t2,~ioc);

if ioc eq 0 then 
	return 0;
else
	Ref1:=Append(t1[ioc]`Refinements,[* t1[ioc]`Phi,t1[ioc]`slope *]);
	Ref2:=Append(t2[ioc]`Refinements,[* t2[ioc]`Phi,t2[ioc]`slope *]);
	minlength:=Min(#Ref1,#Ref2);
	ii:=2;
	while ii le minlength and Ref1[ii,1] eq Ref2[ii,1] do 
	    ii+:=1;    
	end while;
	hiddenslope1:=Ref1[ii-1,2];
	hiddenslope2:=Ref2[ii-1,2];
	minslope:=Min([hiddenslope1,hiddenslope2]);
	entry:=(t1[ioc]`V+minslope)/t1[ioc]`prode;

	if i lt ioc then 
		return (t1[i]`V+Abs(t1[i]`slope))/t1[i]`prode;	
	end if;
	
	if i eq ioc then 	
		if Ref1[ii-1,1] eq t1[ioc]`Phi then 
			return (t1[ioc]`V+hiddenslope2)/t1[ioc]`prode;		
		else
			return entry;	
	
		end if;
	else 
		return entry*Degree(t1[i]`Phi)/Degree(t1[ioc]`Phi);
	end if;	
end if;	


end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Multipliers(F::FldFun,p::RngUPolElt,Expos:: SeqEnum, PhiVals::SeqEnum,BasisVals::SeqEnum,Reduced::BoolElt)->SeqEnum
{Computes computes Multiplier}
//print"Input daten :",BasisVals,PhiVals;
s:=#PhiVals;
FactorIndex:=[Remove([1..s],i):i in [1..s]];
BasisNorm:=[[]:i in [1..s]];

//Berechnung der Norm der Basis Elemente
for l in [1..s] do
	
	for i in [1..s] do 
		if #FactorIndex[l] gt 0 then
		phiadjustment:=&+[PhiVals[j,i,#PhiVals[j,i]]:j in FactorIndex[l]];//- Expos[i]/F`PrimeIdeals[p,i]`e;
		BasisNorm[l,i]:=[BasisVals[l,i,j]- Expos[i]/F`PrimeIdeals[p,i]`e +phiadjustment  :j  in [1..#BasisVals[l,1]]];
		end if;
	end for;
end for;
//print"BasisNorm",BasisNorm;



PrecisionIndex:=[[]:i in [1..s]];

for l in [1..s] do
	
	for i in Remove([1..s],l) do
			phival_i_l:=PhiVals[i,l,#PhiVals[i,l]]; phival_i_i:=PhiVals[i,i,#PhiVals[i,i]];
			ttmmpp:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,i,rr]-phival_i_i):rr in [1..#BasisVals[l,1]]];
			m_0:=Maximum(ttmmpp);
		//	print"phivals",phival_i_l; phival_i_i;
		//	print"m_0",m_0,[ [BasisNorm[l,l,rr]-phival_i_l ,BasisNorm[l,i,rr]-phival_i_i]:rr in [1..#BasisVals[l,1]]];;
			val1:=m_0 ge 0 and i lt l; val2:=m_0 gt 0 and i gt l;
			if Reduced then val2:=m_0 ge 0; end if;
			if val1 or val2 then 
				Append(~PrecisionIndex[l],i);
			else	

				LL:=Remove([1..s],l);
				
				CheckList:=[1];
				for j in Remove(LL,Position(LL,i)) do	// hier berechne ich was doppelt
					ttmmpp2:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,j,rr]-PhiVals[j,i,#PhiVals[j,i]]):rr in [1..#BasisVals[l,1]]];
					m:=Maximum(ttmmpp2);

	
					if  j lt l or Reduced then			
				
						if  m ge 0 then
							
							Append(~CheckList,0);
							
	
						end if;
					else
			
						if  m gt 0 then
							Append(~CheckList,0);						
						
						end if;				
				
						
					end if;
			
			
				end for;	
			
			if &*CheckList eq 1 then
					
				FactorIndex[l]:=Remove(FactorIndex[l],Position(FactorIndex[l],i));
	//									print"i,l",i,l;

	//									print"BasisNorm wow",BasisNorm;

				for z in [1..s] do
					NormAdjusment:=PhiVals[i,z,#PhiVals[i,z]];
//					NormAdjusment:=PhiVals[z,i,#PhiVals[z,i]];
					for y in [1..#BasisNorm[l,1]] do
						
						BasisNorm[l,z,y]:=BasisNorm[l,z,y]-NormAdjusment;
						
					end for;
					
				end for;
			
//								print"BasisNorm after",BasisNorm;

			
			//Alten Werte auch Ã¼berprÃ¼fen
			
			
			
			end if;
			
			end if;

	end for;

end for;
//print"FactorIndex",FactorIndex;
Precision:=[[0:j in [1..#FactorIndex[i]]]:i in [1..s]];
//print"Precision",Precision;


//Berechnung der SFL-Werte
for l in [1..s] do 

	if PrecisionIndex[l] ne [] then

		Adj1:=&+[ PhiVals[j,l,#PhiVals[j,l]] :j in PrecisionIndex[l] ]- Expos[l]/F`PrimeIdeals[p,l]`e;
		LSList:=[BasisVals[l,l,#BasisVals[l,1]]+ Adj1:rr in [1..#BasisVals[l,1]]];
		//print"LS",LS,BasisVals[l,l,#BasisVals[l,1]],Adj1;
		for i in  PrecisionIndex[l] do 
			RSList:=[];
			for mm in [1..#BasisVals[l,1]] do
				iPosition:=Position(PrecisionIndex[l],i);
				phiindices:=Remove(PrecisionIndex[l],iPosition);	

				if #phiindices gt 0 then 
			
					Adj2:=&+[ PhiVals[j,i,#PhiVals[j,i]] :j in phiindices ]- Expos[i]/F`PrimeIdeals[p,i]`e;
				else
					Adj2:=- Expos[i]/F`PrimeIdeals[p,i]`e;
				end if;	
				//print"Adj2",&+[ PhiVals[j,i,#PhiVals[j,i]] :j in PrecisionIndex[l] ], Expos[i]/F`PrimeIdeals[p,i]`e;
				Append(~RSList,BasisVals[l,i,mm]+ Adj2);
				//print"BasisVals,l,i",BasisVals,l,i;
				//print"Data",BasisVals[l,i,#BasisVals[l,1]],Adj2;		
			end for;			
			q:=Maximum([LSList[i]-RSList[i]:i in [1..#LSList]]);		
			
			//print"LS,RS",LS,RS;
			prec:=Ceiling(q*F`PrimeIdeals[p,i]`e);
			//print"prec",prec;
			Boolval:=i lt l;
			if Reduced then Boolval:=true; end if;
			if Boolval and q ge 0 then 
				Precision[l,Position(FactorIndex[l],i)]:=prec + F`PrimeIdeals[p,i]`e;
			
			end if;
			
			if l lt i and q gt 0  then

				Precision[l,Position(FactorIndex[l],i)]:=prec ;				
			
			end if;	
		
		end for; 
	
	end if;
	
end for;

DenExp:=[];
NormVals:=[];
//print"BasisVals",BasisVals;


//Berechnung der Norm der Basiselemente
for l in [1..s] do

	DenExptmp:=[];
	NormValstmp:=[];
	for i in [1..#BasisVals[l,1]] do
	
		
		
		prec:=BasisVals[l,l,i]-Expos[l]/F`PrimeIdeals[p,l]`e;
		
		if FactorIndex[l] ne [] then
		
		Adj:=&+[PhiVals[ jj,l ,#PhiVals[jj,l] ] :jj in FactorIndex[l]];		
				
		Append(~DenExptmp, Floor(prec+Adj));
		Append(~NormValstmp, prec+Adj);
	else
	
		Append(~DenExptmp, Floor(prec));
		Append(~NormValstmp, prec);
		
	end if;
	
	end for;
	
	Append(~DenExp,DenExptmp);
	Append(~NormVals,NormValstmp);
end for;		
//print"DenExpoooos",DenExp;
return FactorIndex,Precision,DenExp,NormVals,BasisNorm;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic MultiplierH(Char::List,Expos:: SeqEnum, PhiVals::SeqEnum,BasisNorm::SeqEnum,FactorIndex::SeqEnum,Reduced::BoolElt)->SeqEnum
{Computes computes Multiplier}
//print"Input daten :",BasisVals,PhiVals;
F:=Char[1];	p:=Char[2];
s:=#PhiVals;
//Berechnung der Norm der Basis Elemente




PrecisionIndex:=[[]:i in [1..s]];

for l in [1..s] do
	
	for i in Remove([1..s],l) do
			phival_i_l:=PhiVals[i,l,#PhiVals[i,l]]; phival_i_i:=PhiVals[i,i,#PhiVals[i,i]];

		//	phival_i_l:=PhiVals[l,i,#PhiVals[l,i]]; phival_i_i:=PhiVals[i,i,#PhiVals[i,i]];
			ttmmpp:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,i,rr]-phival_i_i):rr in [1..#BasisNorm[l,1]]];
			m_0:=Maximum(ttmmpp);
			val1:=m_0 ge 0 and i lt l; val2:=m_0 gt 0 and i gt l;
			if Reduced then val2:=m_0 ge 0; end if;
			if val1 or val2 then 
				Append(~PrecisionIndex[l],i);
				
			else	

				LL:=Remove([1..s],l);
				
				CheckList:=[1];
				for j in Remove(LL,Position(LL,i)) do	// hier berechne ich was doppelt
					ttmmpp2:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,j,rr]-PhiVals[j,i,#PhiVals[j,i]]):rr in [1..#BasisNorm[l,1]]];
					m:=Maximum(ttmmpp2);

	
					if  j lt l or Reduced then			
				
						if  m ge 0 then
							
							Append(~CheckList,0);
							
	
						end if;
					else
			
						if  m gt 0 then
							Append(~CheckList,0);						
						
						end if;				
				
						
					end if;

				end for;	
			
			if &*CheckList eq 1 and i in FactorIndex[l] then
					
				FactorIndex[l]:=Remove(FactorIndex[l],Position(FactorIndex[l],i));
					
				for z in [1..s] do
					NormAdjusment:=PhiVals[i,z,#PhiVals[i,z]];
//					NormAdjusment:=PhiVals[z,i,#PhiVals[z,i]];
					for y in [1..#BasisNorm[l,1]] do
						
						BasisNorm[l,z,y]:=BasisNorm[l,z,y]-NormAdjusment;
						
					end for;
					
				end for;
			
			
			
			//Alten Werte auch Ã¼berprÃ¼fen
			
			
			
			end if;
			
			end if;

	end for;

end for;
//print"FactorIndex",FactorIndex;
Precision:=[[0:j in [1..#FactorIndex[i]]]:i in [1..s]];
//print"Precision",Precision;


return PrecisionIndex,FactorIndex;
end intrinsic;




//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Multipliers2(F::FldFun,p::RngUPolElt,Expos:: SeqEnum, PhiVals::SeqEnum,BasisVals::SeqEnum,Reduced::BoolElt)->SeqEnum
{Computes computes Multiplier}
//print"Input daten :",BasisVals,PhiVals;
s:=#PhiVals;
FactorIndex:=[Remove([1..s],i):i in [1..s]];
BasisNorm:=[[]:i in [1..s]];

//Berechnung der Norm der Basis Elemente
for l in [1..s] do
	
	for i in [1..s] do 
		if #FactorIndex[l] gt 0 then
		phiadjustment:=&+[PhiVals[j,i,#PhiVals[j,i]]:j in FactorIndex[l]];//- Expos[i]/F`PrimeIdeals[p,i]`e;
		BasisNorm[l,i]:=[BasisVals[l,i,j]- Expos[i]/F`PrimeIdeals[p,i]`e +phiadjustment  :j  in [1..#BasisVals[l,1]]];
		end if;
	end for;
end for;
//print"BasisNorm",BasisNorm;



PrecisionIndex:=[[]:i in [1..s]];

for l in [1..s] do
	
	for i in Remove([1..s],l) do
			phival_i_l:=PhiVals[i,l,#PhiVals[i,l]]; phival_i_i:=PhiVals[i,i,#PhiVals[i,i]];
			ttmmpp:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,i,rr]-phival_i_i):rr in [1..#BasisVals[l,1]]];
			m_0:=Maximum(ttmmpp);
			val1:=m_0 ge 0 and i lt l; val2:=m_0 gt 0 and i gt l;
			if Reduced then val2:=m_0 ge 0; end if;
			if val1 or val2 then 
				Append(~PrecisionIndex[l],i);
				
			else	

				LL:=Remove([1..s],l);
				
				CheckList:=[1];
				for j in Remove(LL,Position(LL,i)) do	// hier berechne ich was doppelt
					ttmmpp2:=[Floor( BasisNorm[l,l,rr]-phival_i_l) -Floor(BasisNorm[l,j,rr]-PhiVals[j,i,#PhiVals[j,i]]):rr in [1..#BasisVals[l,1]]];
					m:=Maximum(ttmmpp2);

	
					if  j lt l or Reduced then			
				
						if  m ge 0 then
							
							Append(~CheckList,0);
							
	
						end if;
					else
			
						if  m gt 0 then
							Append(~CheckList,0);						
						
						end if;				
				
						
					end if;
			
			
				end for;	
			
			if &*CheckList eq 1 then
					
				FactorIndex[l]:=Remove(FactorIndex[l],Position(FactorIndex[l],i));
				for z in [1..s] do
					NormAdjusment:=PhiVals[i,z,#PhiVals[i,z]];
//					NormAdjusment:=PhiVals[z,i,#PhiVals[z,i]];
					for y in [1..#BasisNorm[l,1]] do
						
						BasisNorm[l,z,y]:=BasisNorm[l,z,y]-NormAdjusment;
						
					end for;
					
				end for;
			
			
			//Alten Werte auch Ã¼berprÃ¼fen
			
			
			
			end if;
			
			end if;

	end for;

end for;

//Nachbesserungen:
//print"Old Index",FactorIndex;
PrecisionIndex,FactorIndex:=MultiplierH([*F,p*],Expos, PhiVals,BasisNorm,FactorIndex,Reduced);
//print"New Index",FactorIndex;


//print"FactorIndex",FactorIndex;
Precision:=[[0:j in [1..#FactorIndex[i]]]:i in [1..s]];
//print"Precision",Precision;


//Berechnung der SFL-Werte
for l in [1..s] do 

	if FactorIndex[l] ne [] then

		Adj1:=&+[ PhiVals[j,l,#PhiVals[j,l]] :j in FactorIndex[l] ]- Expos[l]/F`PrimeIdeals[p,l]`e;
		LSList:=[BasisVals[l,l,#BasisVals[l,1]]+ Adj1:rr in [1..#BasisVals[l,1]]];
		//print"LS",LS,BasisVals[l,l,#BasisVals[l,1]],Adj1;
		for i in  FactorIndex[l] do 
			RSList:=[];
			for mm in [1..#BasisVals[l,1]] do
				iPosition:=Position(FactorIndex[l],i);
				phiindices:=Remove(FactorIndex[l],iPosition);	

				if #phiindices gt 0 then 
			
					Adj2:=&+[ PhiVals[j,i,#PhiVals[j,i]] :j in phiindices ]- Expos[i]/F`PrimeIdeals[p,i]`e;
				else
					Adj2:=- Expos[i]/F`PrimeIdeals[p,i]`e;
				end if;	
				//print"Adj2",&+[ PhiVals[j,i,#PhiVals[j,i]] :j in PrecisionIndex[l] ], Expos[i]/F`PrimeIdeals[p,i]`e;
				Append(~RSList,BasisVals[l,i,mm]+ Adj2);
				//print"BasisVals,l,i",BasisVals,l,i;
				//print"Data",BasisVals[l,i,#BasisVals[l,1]],Adj2;		
			end for;			
			q:=Maximum([LSList[i]-RSList[i]:i in [1..#LSList]]);		
			
			//print"LS,RS",LS,RS;
			prec:=Ceiling(q*F`PrimeIdeals[p,i]`e);
			//print"prec",prec;
			Boolval:=i lt l;
			if Reduced then Boolval:=true; end if;
			if Boolval and q ge 0 then 
				Precision[l,Position(FactorIndex[l],i)]:=prec + F`PrimeIdeals[p,i]`e;
			
			end if;
			
			if l lt i and q gt 0  then

				Precision[l,Position(FactorIndex[l],i)]:=prec ;				
			
			end if;	
		
		end for; 
	
	end if;
	
end for;

DenExp:=[];
NormVals:=[];
//print"BasisVals",BasisVals;


//Berechnung der Norm der Basiselemente
for l in [1..s] do

	DenExptmp:=[];
	NormValstmp:=[];
	for i in [1..#BasisVals[l,1]] do
	
		
		
		prec:=BasisVals[l,l,i]-Expos[l]/F`PrimeIdeals[p,l]`e;
		
		if FactorIndex[l] ne [] then
		
		Adj:=&+[PhiVals[ jj,l ,#PhiVals[jj,l] ] :jj in FactorIndex[l]];		
				
		Append(~DenExptmp, Floor(prec+Adj));
		Append(~NormValstmp, prec+Adj);
	else
	
		Append(~DenExptmp, Floor(prec));
		Append(~NormValstmp, prec);
		
	end if;
	
	end for;
	
	Append(~DenExp,DenExptmp);
	Append(~NormVals,NormValstmp);
end for;		

//print"DenExpoooos",DenExp;
return FactorIndex,Precision,DenExp,NormVals,BasisNorm,PhiVals;
end intrinsic;




//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

/*intrinsic ComputMultis(F::FldFun,p::RngUPolElt,FacIndex:: SeqEnum, Facprecision::SeqEnum)->SeqEnum
{Determines Multipliers}


print"Input ComputMultis:",FacIndex,Facprecision;
s:=#FacIndex;
kx<x>:=PolynomialRing(PolynomialRing(ConstantField(F)));
Multis:=[[kx!1]:i in [1..s]];
MultiIndex:=[[]:i in [1..s]];

for i in [1..s] do

	SFLList:=[-1:i in [1..s]];
	for j in [1..s] do
	
		if i in FacIndex[j] then
			SFLList[j]:=Facprecision[j,Position(FacIndex[j],i)];
		
		end if;
	
	end for;
	SortSFLList:=Sort(SFLList);
	Bijec:=Sort(SFLList,SortSFLList);
	tmp:=0;
	//	print"\n whatz",SFLList,SortSFLList,Bijec;

	for j in [1..#SortSFLList] do
	
		if SortSFLList[j] gt tmp then //kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
			
			beta:=1;//3/4;//9/16;//5/8;
			Slope:=Maximum([SortSFLList[j]-F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`V,0]);
			//print"Original Slope is                                  ",Slope;
			SFL(~F,~F`PrimeIdeals[p,i],Ceiling(beta*Slope));
			while F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`slope lt Slope do  
				beta:=(beta+1)/2;
				SFL(~F,~F`PrimeIdeals[p,i],Ceiling(beta*Slope));												
			end while;
		//	print"BETA",beta;
		//	print"Slope too large:",F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`slope - Slope;			
			
			

			tmp:=SortSFLList[j]; //hier genauso: \\kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
		end if;
	
		if SortSFLList[j] ge 0 then
			Append(~Multis[Bijec[j]],F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`Phi);
			Append(~MultiIndex[Bijec[j]],i);	
		end if;
	
	end for;
end for;
return [&*i:i in Multis],MultiIndex;
end intrinsic;*/


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic Subsec(List::SeqEnum,p::RngUPolElt,ExtraList::SeqEnum)->SeqEnum
{Splits Liste into sublists of length Lenght[i]}
//=Subsec(ModExpList,p,LengthModExp,modalphas)


Liste:=&cat List;
Liste2:=&cat ExtraList;
Length:=[#i:i in List];
factorList:=ProdList(Liste cat Liste2,p);
exportList:=[factorList[jj]:jj in [#Liste+1..#Liste+#Liste2]];
Liste:=[factorList[jj]:jj in [1..#Liste]];
//print"listen",exportList,Liste2;


useherelist:=[];
for l in [1..#ExtraList] do
	Append(~useherelist,exportList[Position(Liste2,Maximum(ExtraList[l]))]);
end for;


if not #Liste eq &+Length  then print"Liste und Length nicht kompatible"; return 0; end if;
	Out:=[];
	LL:=[];j:=1;
	for i in [1..#Liste] do
	
		Append(~LL,Liste[i]);
		if i eq &+[Length[ll]:ll in [1..j]] then
		
			Append(~Out,LL);
			LL:=[];
			j:=j+1;
		end if;
		
	end for;
	

return Out,useherelist,exportList;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic ModProd(ProdList::SeqEnum,Modterm::RngUPolElt)->SeqEnum
{Multiplies list of polynomials mod modterm}

prod:=1;
for i in [1..#ProdList] do

	prod:=(prod* ProdList[i]) mod Modterm;

end for;

return prod;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ProdList(Expos::SeqEnum,p::RngUPolElt)->SeqEnum
{Produces [p^[Expos[i]]:i in [1..#Expos]] in a intelligent way}

Sort(~Expos,~permutation);
Factors:=[];
prod:=1; j:=0;
for i in [1..#Expos] do
	exp:=Expos[i]-j;
	j:=Expos[i];
	prod:=prod*p^exp;
	Append(~Factors,prod);

end for;

return [Factors[j]:j in Eltseq(permutation^-1)];

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ComputMultis2(F::FldFun,p::RngUPolElt,FacIndex:: SeqEnum, Facprecision::SeqEnum)->SeqEnum
{Determines Multipliers}


print"Input ComputMultis:",FacIndex,Facprecision;
s:=#FacIndex;
kx<x>:=PolynomialRing(PolynomialRing(ConstantField(F)));
Multis:=[[kx!1]:i in [1..s]];
MultiIndex:=[[]:i in [1..s]];

for i in [1..s] do

	SFLList:=[-1:i in [1..s]];
	for j in [1..s] do
	
		if i in FacIndex[j] then
			SFLList[j]:=Facprecision[j,Position(FacIndex[j],i)];
		
		end if;
	
	end for;
	SortSFLList:=Sort(SFLList);
	Bijec:=Sort(SFLList,SortSFLList);
	tmp:=0;
//		print"\n whatz",SFLList,SortSFLList,Bijec;


		Maxi:=Maximum(SortSFLList);
		if Maxi gt tmp then //kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
			
			beta:=1;//3/4;//9/16;//5/8;
			Slope:=Maxi-F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`V;
			//print"Original Slope is",Slope;
			SFL(~F,~F`PrimeIdeals[p,i],Ceiling(beta*Slope));
			while F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`slope lt Slope do  
				beta:=(beta+1)/2;
				SFL(~F,~F`PrimeIdeals[p,i],Ceiling(beta*Slope));												
			end while;
			//print"BETA",beta;
			//print"Slope too large:",F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`slope - Slope;			
			
			

			tmp:=Maxi; //hier genauso: \\kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
		end if;
	for j in [1..#SortSFLList] do	
		if SortSFLList[j] ge 0 then
			Append(~Multis[Bijec[j]],F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`Phi);
			Append(~MultiIndex[Bijec[j]],i);	
		end if;
	
	end for;
end for;
return [&*i:i in Multis],MultiIndex;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ComputMultis(F::FldFun,p::RngUPolElt,FacIndex:: SeqEnum, Facprecision::SeqEnum)->SeqEnum
{Determines Multipliers}
s:=#FacIndex;
ModExponents:=[];
//PutInZ(Facprecision);
for i in [1..s] do

	if Facprecision[i] eq [] then
		Append(~ModExponents,1);
	else
		groesterModExp:=Maximum([Ceiling(Facprecision[i,ll]/F`PrimeIdeals[p,FacIndex[i,ll]]`e)+2:ll in [1..#Facprecision[i]]]);
		Append(~ModExponents,groesterModExp);
	end if;

end for;
//print"TESSSSST",Facprecision,FacIndex,ModExponents;

//print"Input ComputMultis:",FacIndex,Facprecision;
kx<x>:=PolynomialRing(PolynomialRing(ConstantField(F)));
Multis:=[[kx!1]:i in [1..s]];
MultiIndex:=[[]:i in [1..s]];

for i in [1..s] do

	SFLList:=[-1:i in [1..s]];
	for j in [1..s] do
	
		if i in FacIndex[j] then
			SFLList[j]:=Facprecision[j,Position(FacIndex[j],i)];
		
		end if;
	
	end for;
	SortSFLList:=Sort(SFLList);
	Bijec:=Sort(SFLList,SortSFLList);
	tmp:=0;
//		print"\n whatz",SFLList,SortSFLList,Bijec;


		Maxi:=Maximum(SortSFLList);
		if Maxi gt tmp then //kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
			
		//	beta:=1;//3/4;//9/16;//5/8;
			Slope:=Maxi-F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`V;
			//print"Original Slope is",Slope;
			SFL(~F,~F`PrimeIdeals[p,i],Ceiling(Slope));
		/*	while F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`slope lt Slope do  
				beta:=(beta+1)/2;
				SFL(~F,~F`PrimeIdeals[p,i],Ceiling(beta*Slope));	
				print"extra ruuuun\n\n\n";											
			end while;*/
			//
			//print"Slope too large:",F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`slope - Slope;			
			
			

			tmp:=Maxi; //hier genauso: \\kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
		end if;
	for j in [1..#SortSFLList] do	
		if SortSFLList[j] ge 0 then
			Append(~Multis[Bijec[j]],F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`Phi);
			Append(~MultiIndex[Bijec[j]],i);	
		end if;
	
	end for;
end for;
pPowers:=ProdList(ModExponents,p);
//print"Multis",[&*i:i in Multis],[ModProd(Multis[i],p^ModExponents[i]):i in [1..s]],MultiIndex;
//PutInZ([&*i:i in Multis]);PutInZ([ModProd(Multis[i],p^ModExponents[i]):i in [1..s]]);
return [&*i:i in Multis],MultiIndex;
//return [ModProd(Multis[i],pPowers[i]):i in [1..s]],MultiIndex;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ComputMultisShort(F::FldFun,p::RngUPolElt,FacIndex:: SeqEnum, Facprecision::SeqEnum,PhiVals::SeqEnum,modalphas::SeqEnum)->SeqEnum
{Determines Multipliers}

//print"FacIndex",FacIndex,Facprecision;
s:=#FacIndex;
ModExponents:=[];
ModExpList:=[];
for i in [1..s] do

	if Facprecision[i] eq [] then
		Append(~ModExponents,1);
	else
		for l in [1..#FacIndex[i]] do
		phivalues:=[Facprecision[i,l]/F`PrimeIdeals[p,FacIndex[i,l]]`e] cat [PhiVals[l,j,#PhiVals[l,1]]: j in Remove([1..s],l)];
//		print"TESSSSST",phivalues;
		Append(~ModExponents,Ceiling(Maximum([0] cat phivalues))+1);
		end for;
		tmpl:=[];
			
	end if;
	Append(~ModExpList,ModExponents);
	ModExponents:=[];
end for;
LengthModExp:=[#j:j in ModExpList];
factorModList,EndExpos,exportexpos:=Subsec(ModExpList,p,modalphas);//Subsec(ProdList(&cat ModExpList,p),LengthModExp,modalphas);
//print"TESSSSST2",ModExpList;
//print"Input ComputMultis:",FacIndex,Facprecision;
kx<x>:=PolynomialRing(PolynomialRing(ConstantField(F)));
Multis:=[[kx!1]:i in [1..s]];
MultiIndex:=[[]:i in [1..s]];

for i in [1..s] do

	SFLList:=[-1:i in [1..s]];
	for j in [1..s] do
	
		if i in FacIndex[j] then
			SFLList[j]:=Facprecision[j,Position(FacIndex[j],i)];
		
		end if;
	
	end for;
	SortSFLList:=Sort(SFLList);
	Bijec:=Sort(SFLList,SortSFLList);
	tmp:=0;
//		print"\n whatz",SFLList,SortSFLList,Bijec;


		Maxi:=Maximum(SortSFLList);
		if Maxi gt tmp then //kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
			
		//	beta:=1;//3/4;//9/16;//5/8;
			Slope:=Maxi-F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`V;
			//print"Original Slope is",Slope;
			SFL(~F`PrimeIdeals[p,i]`Type,Ceiling(Slope));
            last_lvl := F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type];
            h := last_lvl`h - last_lvl`cuttingslope;
            lasth := Ceiling(Slope) - last_lvl`cuttingslope;
            path:=PathOfPrecisions(lasth,h);
            if #path gt 0 then
                F`SFLCount +:= (#path - 1);
            end if;
		/*	while F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`slope lt Slope do  
				beta:=(beta+1)/2;
				SFL(~F,~F`PrimeIdeals[p,i],Ceiling(beta*Slope));	
				print"extra ruuuun\n\n\n";											
			end while;*/
			//
			//print"Slope too large:",F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`slope - Slope;			
			

			tmp:=Maxi; //hier genauso: \\kann man statt tmp auch v_p(Phi_P) nehmen, wird aber eh in SFL gecheckt
		end if;
	for j in [1..#SortSFLList] do	
		if SortSFLList[j] ge 0 then
			Append(~Multis[Bijec[j]],F`PrimeIdeals[p,i]`Type[#F`PrimeIdeals[p,i]`Type]`Phi);
			Append(~MultiIndex[Bijec[j]],i);	
		end if;
	
	end for;
end for;
//pPowers:=ProdList(ModExponents,p);
//print"Multis",Multis,factorModList;
//PutInZ([&*i:i in Multis]);PutInZ([ModProd(Multis[i],p^ModExponents[i]):i in [1..s]]);
//return [&*i:i in Multis],MultiIndex;
z_kappa:=[];
for ll in [1..#Multis] do
	if #Multis[ll] eq 1 and Multis[ll,1] eq 1 then
		Append(~z_kappa,Multis[ll,1]);
	else		
	Append(~z_kappa,(&*[Multis[ll,mm] mod factorModList[ll,mm-1]:mm in [2..#Multis[ll]]]) mod EndExpos[ll] );//mod EndExpos[mm] 
	end if;
end for;
return z_kappa,MultiIndex,exportexpos;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



intrinsic PhiExpo(m::RngIntElt,DegList::SeqEnum)->SeqEnum
{Compute mi/m_i-1 representation of an integer m}
L:=[];
DegList:=[1] cat DegList;
BoundList:=[Integers()!(DegList[i]/DegList[i-1]):i in [2..#DegList]];
for i in [1..#BoundList] do

	Append(~L,Integers()!(m mod BoundList[i]));
	m:=m div BoundList[i];

end for;


return L;

end intrinsic;
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Deg(z::FldFunElt)->RngIntElt
{}
if z eq 0 then return -Infinity();end if;

L:=Eltseq(z);
tmp:=exists(t){y:y in [Degree(Parent(z))..1 by -1]|not L[y] eq 0 };

return t-1;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic Signature(NormValues::SeqEnum,RamInde::SeqEnum)->SeqEnum
{}
NormelizedValues:=Sort(SetToSequence(Set([0]cat &cat[[j/e:j in [1..e-1]]:e in RamInde])));
PositionList:=[];
for j in NormelizedValues do
	tmp:=[];
	 for i in [1..#NormValues] do 	
		if Denominator(NormValues[i]) eq Denominator(j) 
			and Numerator(NormValues[i]) mod Denominator(NormValues[i]) eq Numerator(j) mod Denominator(j) then
			Append(~tmp,i);	
		end if;
	end for;
	Append(~PositionList,tmp);
end for;

return PositionList;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic pBasisRR(I::Rec,p::RngUPolElt:Reduced:=false)->SeqEnum
{Computes a p-integral basis of the fractional ideal in Hermite Form or if Reduced is set true an p-orthonormal basis of I}

//Initialization
Factorization(~I);
F:=I`Parent;	n:=Degree(F);
Primes:=F`PrimeIdeals[p];
s:=#Primes;
//Ramifications indices
kt:=PolynomialRing(ConstantField(F));	kx<x>:=PolynomialRing(kt); K:=BaseField(F);
_, _ := Montes(F,p);
//SAVEDATA:=F`PrimeIdeals[p];
//tts:=Realtime();

if Reduced eq true and &*[i`e:i in F`PrimeIdeals[p]] eq 1 then
	Reduced:=false;
end if;

if Reduced eq true and forall{i:i in F`PrimeIdeals[p]|i`e  eq 1 } then
	Reduced:=false;
end if;

//Initializing Exponentes of p-part of ideal
Expos:=[0:i in [1..#F`PrimeIdeals[p]]];
for i in I`Factorization do
	if i[1] eq p then 	
		Expos[i[2]]:=i[3];	
	end if;
end for;


//Ziehe groessten p(t)^a*O_F aus I heraus und speicher p(t)^a 
killexpo:=0;
if forall{i:i in [1..s]|Expos[i] gt 0 } then
	killexpo:=Minimum([Floor(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
if forall{i:i in [1..s]|Expos[i] lt 0 } then
	killexpo:=Maximum([Ceiling(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
//Wenn 
if IsDefined(F`LocalIndex,p) and Expos eq [0:i in [1..s]] then
	if F`LocalIndex[p] eq 0 then
		return [F.1^i:i in [0..n-1]],[0:i in [0..n-1]],kt!1,1,p,killexpo ;
	end if;
end if;

if p in F`Index and assigned F`IndexBases and IsDefined(F`IndexBases,p) and Expos eq [0:i in [1..s]] then

	return F`IndexBases[p,1],F`IndexBases[p,2],F`IndexBases[p,3],F`IndexBases[p,4],F`IndexBases[p,5],killexpo;

end if;


/*if Expos eq [0:i in [1..s]] and IsDefined(F`maxorderfinite,p) and Reduced eq false then
	return F`maxorderfinite[p][1],F`maxorderfinite[p][2],F`maxorderfinite[p][3],F`maxorderfinite[p][4],p,killexpo;
end if;*/
//print"Step first in LocalB",Realtime()-tts;tts:=Realtime();

//Determination of Okutsu bases: 
if not IsDefined(F`localbasedata,p) then
	LocalBases:=[];
	VallMatrix:=[];
	PhiValMatrix:=[];
	for i in [1..s] do 
		r:=#Primes[i]`Type;		e_P:=Primes[i]`e;	n_P:=e_P*Primes[i]`f;    a_P:=Expos[i];         
		Phis:= [Primes[i]`Type[j]`Phi:j in [1..r]];
		PhiDeg:=[Degree(j):j in Phis];
		PhiExpos:=[PhiExpo(m,PhiDeg):m in [1..n_P-1]];
		Phis:=[x] cat Phis;
		BasisVals:=[* *];
		PhiVals:=[* *];
		for l in [1..s] do 
			BasisValstmp:=[Rationals()!0:i in [1..n_P]];
			PhiValstmp:=[PhiValuation(F,p,[i,o],l):o in [0..#Primes[i]`Type] ];
			for k in [1..n_P-1] do
				BasisValstmp[k+1]:=&+[PhiExpos[k,ll]*PhiValstmp[ll]:ll in [1..#PhiExpos[k] ]];
			end for;
			Append(~BasisVals,BasisValstmp);
			Append(~PhiVals,PhiValstmp);
		end for;
		Append(~PhiValMatrix,PhiVals);
		Append(~VallMatrix,BasisVals);
		localBasis:=[kx!1] cat [ kx!&*[Phis[j]^PhiExpos[k][j]:j in [1..#Phis-1]]:k in [1..n_P-1]];
		Append(~LocalBases,localBasis);
	end for;

	F`localbasedata[p]:=[*LocalBases,VallMatrix,PhiValMatrix*];
else
	LocalBases:=F`localbasedata[p][1];
	VallMatrix:=F`localbasedata[p][2];
	PhiValMatrix:=F`localbasedata[p][3];
end if;
//print"LocalBases",LocalBases;

//print"Step LocalB",Realtime()-tts;tts:=Realtime();

//

FacIndex,Facprecision,DenExpos,NormValues:=Multipliers2(F,p,Expos,PhiValMatrix,VallMatrix,Reduced);
//print"Step 2 Multi",Realtime()-tts;tts:=Realtime();
//tt:=F`PrimeIdeals[p];
alpha:=Maximum([Ceiling(Expos[j]/Primes[j]`e):j in [1..s]])+1;
//print"alpha",alpha;
//ModExp:=Maximum(&cat [[Integers()!Abs(j):j  in i]:i in DenExpos])+alpha;
//print"ModExp",ModExp;
Base:=[];
//pevModExp2:=p^(ModExp);
groupedNormValues:=NormValues;
NormValues:=&cat NormValues;

_,Possi:=Maximum(NormValues);
constminus:=Minimum([-Expos[j]/Primes[j]`e:j in [1..#Expos]]);
modalphas:=[[Maximum([Ceiling(ll-constminus),0])+1:ll in j]:j in groupedNormValues];
//print"NormValues",modalphas;
Multis,Indices,exportexpos:=ComputMultisShort(F,p,FacIndex,Facprecision,PhiValMatrix,modalphas);
//print"Step 3 Compute Multis",Realtime()-tts;tts:=Realtime();
//print"for p=",p;
//print"\n";
pmodExpos:=ProdList([Maximum([Ceiling(j),0])+1:j in NormValues],p);
pevModExp:=exportexpos[Possi];
_,maxindex:=Maximum(NormValues);
//print"Maximaler Exponent",Maximum(NormValues);
//pevModExp:=pmodExpos[maxindex];
//print"expos...", pevModExp,pmodExpos;
lauf:=1;
for i in [1..#LocalBases] do
	for j in [1..#LocalBases[i]] do
		Append(~Base,Eval(F,(LocalBases[i,j]* Multis[i])) mod exportexpos[lauf]);//pmodExpos[lauf]
		lauf:=lauf+1;	
	end for;
end for;
//print"Step 4 Multiplying to basis",Realtime()-tts;tts:=Realtime();
//Degree(pevModExp),[Degree(i):i in exportexpos];
//Again reduction of Coefficiants
DenExpos:=&cat DenExpos;
modalphasList:=&cat modalphas;
for i in [1..n] do
	TMP:=Parent([p])!Eltseq(Base[i]);
	Base[i]:=F![TMP[j] mod exportexpos[i]: j in [1..#TMP]];
end for;

//////////////Transforming into HNF////////////////////
//print"DenExpos",DenExpos;
denexxo:=Sort(DenExpos);
zeta:=-Maximum(DenExpos);
DenExpos:=[-i-zeta:i in DenExpos];
//print"DenExpos",DenExpos;
//print"Step 7",Realtime()-tts;
PreBase:=Reverse(Sort([p^DenExpos[i]*Base[i]:i in [1..#Base]],func<x, y | Deg(x) - Deg(y)>));
//print"Daten",[p^DenExpos[i]*Base[i]:i in [1..#Base]],DenExpos;
MatList:=[];
//print"Step 7",[Deg(i):i in PreBase];Realtime()-tts;
for j:=1 to #PreBase by  1 do
	Append(~MatList,Reverse(Parent([p])!Eltseq(PreBase[j])));
end for;
//print"Step 5 Gleich HNF",Realtime()-tts;tts:=Realtime();
if Reduced eq false then
		H:=HermiteForm(Matrix(MatList));
//print"Step 9 just HNF",Realtime()-tts;tts:=Realtime();
	MatList:=[Eltseq(H[i]):i in [1..n]];
	Denoms:=[];
	for i in [1..n] do
		exp:=Valuation(MatList[i,i],p);	
		Append(~Denoms,exp);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,i]/pevExp),pevModExp);
		MatList[i,i]:=pevExp;
		for j in [i+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;
	Denoms:=[-(i+zeta):i in Denoms];
	H:=HermiteForm(Matrix(MatList));
//print"Step 10 IN HNF",Realtime()-tts;tts:=Realtime();
	Base:=Reverse([(F!  Parent([p])!Reverse(Eltseq(H[i]))) *K!p^zeta:i in [1..Degree(F)]]);
else
	Posi:=Signature(NormValues,[i`e:i in F`PrimeIdeals[p]]);
// HNF fÃ¼r reduzierte Basis
	for j in [1..#Posi] do
		tmpList:=[MatList[i]: i in Posi[j]];		
		H:=HermiteForm(Matrix(tmpList));
		tmpList:=[Parent([p])!Eltseq(H[i]):i in [1..#tmpList]];
		for i in [1..#tmpList] do
			MatList[Posi[j,i]]:=tmpList[i];			
		end for;
	end for;
// Normalisieren der Basis
	for i in [1..n] do
		nN:=exists(ind){ y : y in [1..n] | not MatList[i,y] eq 0};
		exp:=Valuation(MatList[i,ind],p);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,ind]/pevExp),pevModExp);
		MatList[i,ind]:=pevExp;
		for j in [ind+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;	

//		print"was",Realtime()-tts;tts:=Realtime();

// HNF fÃ¼r reduzierte Basis zum 2.
	for j in [1..#Posi] do

		tmpList:=[MatList[i]: i in Posi[j]];		
		H:=HermiteForm(Matrix(tmpList));
		tmpList:=[Parent([p])!Eltseq(H[i]):i in [1..#tmpList]];
		for i in [1..#tmpList] do
			MatList[Posi[j,i]]:=tmpList[i];			
		end for;		
	end for;
	//					print"drin?",Realtime()-tts;tts:=Realtime();
	Base:=Sort(Reverse([F!  Parent([p])!Reverse(Eltseq(MatList[i])) *K!p^zeta:i in [1..Degree(F)]]),func<x, y | Deg(x) - Deg(y)>);
//	F`PrimeIdeals[p]:=SAVEDATA;// IST NEU
	return Base,[],0,kt!1,p,killexpo;
end if;


if p in F`Index and assigned F`IndexBases and not IsDefined(F`IndexBases,p) and Expos eq [0:i in [1..s]] then
	F`IndexBases[p]:=[*Base,Sort(Denoms),pevModExp,alpha,p,killexpo*];
end if;

/*if Expos eq [0:i in Expos] and not IsDefined(F`maxorderfinite,p) then
	F`maxorderfinite[p]:=[*Base,Sort(Denoms),pevModExp,alpha*];
end if;*/

//F`PrimeIdeals[p]:=SAVEDATA;
//print"Step Raus",Realtime()-tts;tts:=Realtime();
return Base,Sort(Denoms),pevModExp,alpha,p,killexpo;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic pBasisMultipliers(I::Rec,p::RngUPolElt:HNF:=false, exp:=false, random_exponent:=[0, 0])->SeqEnum
{Computes a p-integral basis of the fractional ideal in Hermite Form}

F:=I`Parent;	n:=Degree(F);

if not assigned(F`PrimeIdeals) or not IsDefined(F`PrimeIdeals, p) then
    _, _ := Montes(F, p : Basis:=false);
end if;

// Yes, this is a bit hackish, but it'll do for now.
if Type(exp) ne BoolElt then
    if #F`PrimeIdeals[p] gt #exp then
        exp cat:= [ Random(random_exponent[1], random_exponent[2])
                        : i in [#exp+1..#F`PrimeIdeals[p]] ];
    end if;
    I := &*[ F`PrimeIdeals[p,i]^exp[i] : i in [1..#exp] ];
end if;

exponents_time := Cputime();

//Initialization
Factorization(~I);
Primes:=F`PrimeIdeals[p];
s:=#Primes;
//Ramifications indices
kt:=PolynomialRing(ConstantField(F));	kx<x>:=PolynomialRing(kt); K:=BaseField(F);
//Montes(F,p);
//SAVEDATA:=F`PrimeIdeals[p];
//tts:=Realtime();


//Initializing Exponentes of p-part of ideal
Expos:=[0:i in [1..#F`PrimeIdeals[p]]];
for i in I`Factorization do
	if i[1] eq p then 	
		Expos[i[2]]:=i[3];	
	end if;
end for;

//Ziehe groessten p(t)^a*O_F aus I heraus und speicher p(t)^a 
killexpo:=0;
if forall{i:i in [1..s]|Expos[i] gt 0 } then
	killexpo:=Minimum([Floor(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
if forall{i:i in [1..s]|Expos[i] lt 0 } then
	killexpo:=Maximum([Ceiling(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
//Wenn 
if IsDefined(F`LocalIndex,p) and Expos eq [0:i in [1..s]] then
	if F`LocalIndex[p] eq 0 then
        p_basis := [ F.1^i : i in [0..n-1] ];
        nums := [ kx!Eltseq(c) : c in p_basis ];
        dexp := [ 0 : i in [0..n-1] ];
        return p_basis, nums, dexp, exp;
        // Substituted for the above by Hayden.
		//return [F.1^i:i in [0..n-1]],[0:i in [0..n-1]],kt!1,1,p,killexpo ;
	end if;
end if;

/*if p in F`Index and assigned F`IndexBases and IsDefined(F`IndexBases,p) and Expos eq [0:i in [1..s]] then

	return F`IndexBases[p,1],F`IndexBases[p,2],F`IndexBases[p,3],F`IndexBases[p,4],F`IndexBases[p,5],killexpo;

end if;*/


/*if Expos eq [0:i in [1..s]] and IsDefined(F`maxorderfinite,p) and Reduced eq false then
	return F`maxorderfinite[p][1],F`maxorderfinite[p][2],F`maxorderfinite[p][3],F`maxorderfinite[p][4],p,killexpo;
end if;*/
//print"Step first in LocalB",Realtime()-tts;tts:=Realtime();

okbasis_time := Cputime();

//Construction of Okutsu bases: 
	LocalBases:=[];
	VallMatrix:=[];
	PhiValMatrix:=[];
	for i in [1..s] do 
		r:=#Primes[i]`Type;		e_P:=Primes[i]`e;	n_P:=e_P*Primes[i]`f;    a_P:=Expos[i];         
		Phis:= [Primes[i]`Type[j]`Phi:j in [1..r]];
		PhiDeg:=[Degree(j):j in Phis];
		PhiExpos:=[PhiExpo(m,PhiDeg):m in [1..n_P-1]];
		Phis:=[x] cat Phis;
		BasisVals:=[* *];
		PhiVals:=[* *];
		for l in [1..s] do 
			BasisValstmp:=[Rationals()!0:i in [1..n_P]];
			PhiValstmp:=[PhiValuation(F,p,[i,o],l):o in [0..#Primes[i]`Type] ];
			for k in [1..n_P-1] do
				BasisValstmp[k+1]:=&+[PhiExpos[k,ll]*PhiValstmp[ll]:ll in [1..#PhiExpos[k] ]];
			end for;
			Append(~BasisVals,BasisValstmp);
			Append(~PhiVals,PhiValstmp);
		end for;
		Append(~PhiValMatrix,PhiVals);
		Append(~VallMatrix,BasisVals);
		localBasis:=[kx!1] cat [ kx!&*[Phis[j]^PhiExpos[k][j]:j in [1..#Phis-1]]:k in [1..n_P-1]];
		Append(~LocalBases,localBasis);
	end for;

	F`localbasedata[p]:=[*LocalBases,VallMatrix,PhiValMatrix*];

//print"LocalBases",LocalBases;

//print"Step LocalB",Realtime()-tts;tts:=Realtime();
//

multipliers_time := Cputime();

FacIndex,Facprecision,DenExpos,NormValues:=Multipliers2(F,p,Expos,PhiValMatrix,VallMatrix,false);
//print"Step 2 Multi",Realtime()-tts;tts:=Realtime();
//tt:=F`PrimeIdeals[p];
alpha:=Maximum([Ceiling(Expos[j]/Primes[j]`e):j in [1..s]])+1;
//print"alpha",alpha;
//ModExp:=Maximum(&cat [[Integers()!Abs(j):j  in i]:i in DenExpos])+alpha;
//print"ModExp",ModExp;
Base:=[];
//pevModExp2:=p^(ModExp);
groupedNormValues:=NormValues;
NormValues:=&cat NormValues;
_,Possi:=Maximum(NormValues);
constminus:=Minimum([-Expos[j]/Primes[j]`e:j in [1..#Expos]]);
modalphas:=[[Maximum([Ceiling(ll-constminus),0])+1:ll in j]:j in groupedNormValues];
//print"NormValues",modalphas;
Multis,Indices,exportexpos:=ComputMultisShort(F,p,FacIndex,Facprecision,PhiValMatrix,modalphas);


mult_pol_time:= Cputime();

//print"Step 3 Compute Multis",Realtime()-tts;tts:=Realtime();
//print"Indices",Indices;
//print"\n";

pmodExpos:=ProdList([Maximum([Ceiling(j),0])+1:j in NormValues],p);

pevModExp:=exportexpos[Possi];

_,maxindex:=Maximum(NormValues);
//print"Maximaler Exponent",Maximum(NormValues);
//pevModExp:=pmodExpos[maxindex];
//print"expos...", pevModExp,pmodExpos;
lauf:=1;
for i in [1..#LocalBases] do
	for j in [1..#LocalBases[i]] do
		Append(~Base,Eval(F,(LocalBases[i,j]* Multis[i])) mod exportexpos[lauf]);//pmodExpos[lauf]
		lauf:=lauf+1;	
	end for;
end for;
//print"Step 4 Multiplying to basis",Realtime()-tts;tts:=Realtime();
//Degree(pevModExp),[Degree(i):i in exportexpos];
//Again reduction of Coefficiants

DenExpos:=&cat DenExpos;
modalphasList:=&cat modalphas;
tmps2 := Cputime();
for i in [1..n] do
	TMP:=Parent([p])!Eltseq(Base[i]);
	Base[i]:=F![TMP[j] mod exportexpos[i]: j in [1..#TMP]];
end for;

if HNF eq false then
    nums := Base;
    dexp := DenExpos;

    unsorted_basis := [ [* nums[i], dexp[i] *] : i in [1..#nums] ];
    sorted := Sort(unsorted_basis, func<x, y | Deg(x[1]) - Deg(y[1]) >);
    nums := [ c[1] : c in sorted ];
    dexp := [ c[2] : c in sorted ];
    p_basis := [ nums[i]*K!p^-dexp[i] : i in [1..#nums] ];
    nums := [ kx!Eltseq(c) : c in nums ];

    F`Times cat:= [ okbasis_time - exponents_time,
                    multipliers_time - okbasis_time,
                    mult_pol_time - multipliers_time,
                    Cputime() - mult_pol_time ];

//    unsortedBasis:=[Base[i]*K!p^-DenExpos[i]:i in [1..#Base]];
//    FinalpBasis:=Sort(unsortedBasis,func<x, y | Deg(x) - Deg(y)>);

	return p_basis, nums, dexp, exp;
end if;

//////////////Transforming into HNF////////////////////
//print"DenExpos",DenExpos;
denexxo:=Sort(DenExpos);
zeta:=-Maximum(DenExpos);
DenExpos:=[-i-zeta:i in DenExpos];
//print"DenExpos",DenExpos;
//print"Step 7",Realtime()-tts;
PreBase:=Reverse(Sort([p^DenExpos[i]*Base[i]:i in [1..#Base]],func<x, y | Deg(x) - Deg(y)>));
//print"Daten",[p^DenExpos[i]*Base[i]:i in [1..#Base]],DenExpos;
MatList:=[];
//print"Step 7",[Deg(i):i in PreBase];Realtime()-tts;
for j:=1 to #PreBase by  1 do
	Append(~MatList,Reverse(Parent([p])!Eltseq(PreBase[j])));
end for;
//print"Step 5 Gleich HNF",Realtime()-tts;tts:=Realtime();
		H:=HermiteForm(Matrix(MatList));
//print"Step 9 just HNF",Realtime()-tts;tts:=Realtime();
	MatList:=[Eltseq(H[i]):i in [1..n]];
	Denoms:=[];
	for i in [1..n] do
		exp:=Valuation(MatList[i,i],p);	
		Append(~Denoms,exp);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,i]/pevExp),pevModExp);
		MatList[i,i]:=pevExp;
		for j in [i+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;
	Denoms:=[-(i+zeta):i in Denoms];
	H:=HermiteForm(Matrix(MatList));
    //printf "Post HNF:\n%o\n", H;
//print"Step 10 IN HNF",Realtime()-tts;tts:=Realtime();
	Base:=Reverse([(F!  Parent([p])!Reverse(Eltseq(H[i]))) *K!p^zeta:i in [1..Degree(F)]]);


/*if Expos eq [0:i in Expos] and not IsDefined(F`maxorderfinite,p) then
	F`maxorderfinite[p]:=[*Base,Sort(Denoms),pevModExp,alpha*];
end if;*/

//F`PrimeIdeals[p]:=SAVEDATA;
//print"Step Raus",Realtime()-tts;tts:=Realtime();
return Base,Sort(Denoms),pevModExp,alpha,p,killexpo;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic pBasisRRTEST(I::Rec,p::RngUPolElt:Reduced:=false)->SeqEnum
{Computes a p-integral basis of the fractional ideal in Hermite Form or if Reduced is set true an p-orthonormal basis of I}

//Initialization
Factorization(~I);
F:=I`Parent;	n:=Degree(F);
Primes:=F`PrimeIdeals[p];
s:=#Primes;
//Ramifications indices
kt:=PolynomialRing(ConstantField(F));	kx<x>:=PolynomialRing(kt); K:=BaseField(F);
_, _ := Montes(F,p);
//SAVEDATA:=F`PrimeIdeals[p];
//tts:=Realtime();

if Reduced eq true and &*[i`e:i in F`PrimeIdeals[p]] eq 1 then
	Reduced:=false;
end if;

if Reduced eq true and forall{i:i in F`PrimeIdeals[p]|i`e  eq 1 } then
	Reduced:=false;
end if;

//Initializing Exponentes of p-part of ideal
Expos:=[0:i in [1..#F`PrimeIdeals[p]]];
for i in I`Factorization do
	if i[1] eq p then 	
		Expos[i[2]]:=i[3];	
	end if;
end for;


//Ziehe groessten p(t)^a*O_F aus I heraus und speicher p(t)^a 
killexpo:=0;
if forall{i:i in [1..s]|Expos[i] gt 0 } then
	killexpo:=Minimum([Floor(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
if forall{i:i in [1..s]|Expos[i] lt 0 } then
	killexpo:=Maximum([Ceiling(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
	Expos:=[Expos[ll]-Primes[ll]`e*killexpo:ll in [1..s]];
end if;
//Wenn 
/*if IsDefined(F`LocalIndex,p) and Expos eq [0:i in [1..s]] then
	if F`LocalIndex[p] eq 0 then
		return [F.1^i:i in [0..n-1]],[0:i in [0..n-1]],kt!1,1,p,killexpo,0 ;
	end if;
end if;
*/
//if p in F`Index and assigned F`IndexBases and IsDefined(F`IndexBases,p) and Expos eq [0:i in [1..s]] then

//	return F`IndexBases[p,1],F`IndexBases[p,2],F`IndexBases[p,3],F`IndexBases[p,4],F`IndexBases[p,5],killexpo;

//end if;


/*if Expos eq [0:i in [1..s]] and IsDefined(F`maxorderfinite,p) and Reduced eq false then
	return F`maxorderfinite[p][1],F`maxorderfinite[p][2],F`maxorderfinite[p][3],F`maxorderfinite[p][4],p,killexpo;
end if;*/
//print"Step first in LocalB",Realtime()-tts;tts:=Realtime();

//Determination of Okutsu bases: 
if not IsDefined(F`localbasedata,p) then
	LocalBases:=[];
	VallMatrix:=[];
	PhiValMatrix:=[];
	for i in [1..s] do 
		r:=#Primes[i]`Type;		e_P:=Primes[i]`e;	n_P:=e_P*Primes[i]`f;    a_P:=Expos[i];         
		Phis:= [Primes[i]`Type[j]`Phi:j in [1..r]];
		PhiDeg:=[Degree(j):j in Phis];
		PhiExpos:=[PhiExpo(m,PhiDeg):m in [1..n_P-1]];
		Phis:=[x] cat Phis;
		BasisVals:=[* *];
		PhiVals:=[* *];
		for l in [1..s] do 
			BasisValstmp:=[Rationals()!0:i in [1..n_P]];
			PhiValstmp:=[PhiValuation(F,p,[i,o],l):o in [0..#Primes[i]`Type] ];
			for k in [1..n_P-1] do
				BasisValstmp[k+1]:=&+[PhiExpos[k,ll]*PhiValstmp[ll]:ll in [1..#PhiExpos[k] ]];
			end for;
			Append(~BasisVals,BasisValstmp);
			Append(~PhiVals,PhiValstmp);
		end for;
		Append(~PhiValMatrix,PhiVals);
		Append(~VallMatrix,BasisVals);
		localBasis:=[kx!1] cat [ kx!&*[Phis[j]^PhiExpos[k][j]:j in [1..#Phis-1]]:k in [1..n_P-1]];
		Append(~LocalBases,localBasis);
	end for;

	F`localbasedata[p]:=[*LocalBases,VallMatrix,PhiValMatrix*];
else
	LocalBases:=F`localbasedata[p][1];
	VallMatrix:=F`localbasedata[p][2];
	PhiValMatrix:=F`localbasedata[p][3];
end if;
//print"LocalBases",LocalBases;

//print"Step LocalB",Realtime()-tts;tts:=Realtime();

//

FacIndex,Facprecision,DenExpos,NormValues:=Multipliers2(F,p,Expos,PhiValMatrix,VallMatrix,Reduced);
//print"Step 2 Multi",Realtime()-tts;tts:=Realtime();
//tt:=F`PrimeIdeals[p];
alpha:=Maximum([Ceiling(Expos[j]/Primes[j]`e):j in [1..s]])+1;
//print"alpha",alpha;
//ModExp:=Maximum(&cat [[Integers()!Abs(j):j  in i]:i in DenExpos])+alpha;
//print"ModExp",ModExp;
Base:=[];
//pevModExp2:=p^(ModExp);
groupedNormValues:=NormValues;
NormValues:=&cat NormValues;
//print"NormValues",groupedNormValues,PhiValMatrix,FacIndex;
_,Possi:=Maximum(NormValues);
constminus:=Minimum([-Expos[j]/Primes[j]`e:j in [1..#Expos]]);
modalphas:=[[Maximum([Ceiling(ll-constminus),0])+1:ll in j]:j in groupedNormValues];
//print"NormValues",modalphas;
Multis,Indices,exportexpos:=ComputMultisShort(F,p,FacIndex,Facprecision,PhiValMatrix,modalphas);
//print"Step 3 Compute Multis",Realtime()-tts;tts:=Realtime();
//print"for p=",p;
//print"\n";
pmodExpos:=ProdList([Maximum([Ceiling(j),0])+1:j in NormValues],p);
pevModExp:=exportexpos[Possi];
_,maxindex:=Maximum(NormValues);
//print"Maximaler Exponent",Maximum(NormValues);
//pevModExp:=pmodExpos[maxindex];
//print"expos...", pevModExp,pmodExpos;


lauf:=1;
for i in [1..#LocalBases] do
	for j in [1..#LocalBases[i]] do
		Append(~Base,Eval(F,(LocalBases[i,j]* Multis[i])) mod exportexpos[lauf]);//pmodExpos[lauf]
		lauf:=lauf+1;	
	end for;
end for;
//print"Step 4 Multiplying to basis",Realtime()-tts;tts:=Realtime();
//Degree(pevModExp),[Degree(i):i in exportexpos];
//Again reduction of Coefficiants
DenExpos:=&cat DenExpos;
modalphasList:=&cat modalphas;
for i in [1..n] do
	TMP:=Parent([p])!Eltseq(Base[i]);
	Base[i]:=F![TMP[j] mod exportexpos[i]: j in [1..#TMP]];
end for;
if Reduced eq true then
	Normes:=[];
	for i in [1..s] do
		if not FacIndex[i] eq [] then
			addtmp:=&+[PhiValMatrix[l,i,#PhiValMatrix[l,i]]:l in FacIndex[i]];
		else
			addtmp:=0;
		end if;
		for j in [1..#groupedNormValues[i]] do
	
			Append(~Normes,groupedNormValues[i,j]+addtmp );	
	end for;

	end for;
	
	return [Base[i]/F!p^DenExpos[i]:i in [1..n]],[-i-Ceiling(-i):i in Normes],Multis,Base,p,killexpo,Maximum(DenExpos);

end if;

//////////////Transforming into HNF////////////////////
//print"DenExpos",DenExpos;
denexxo:=Sort(DenExpos);
zeta:=-Maximum(DenExpos);
DenExpos:=[-i-zeta:i in DenExpos];
//print"DenExpos",DenExpos;
//print"Step 7",Realtime()-tts;
PreBase:=Reverse(Sort([p^DenExpos[i]*Base[i]:i in [1..#Base]],func<x, y | Deg(x) - Deg(y)>));
//print"Daten",[p^DenExpos[i]*Base[i]:i in [1..#Base]],DenExpos;
MatList:=[];
//print"Step 7",[Deg(i):i in PreBase];Realtime()-tts;
for j:=1 to #PreBase by  1 do
	Append(~MatList,Reverse(Parent([p])!Eltseq(PreBase[j])));
end for;
//print"Step 5 Gleich HNF",Realtime()-tts;tts:=Realtime();
if Reduced eq false then
		H:=HermiteForm(Matrix(MatList));
//print"Step 9 just HNF",Realtime()-tts;tts:=Realtime();
	MatList:=[Eltseq(H[i]):i in [1..n]];
	Denoms:=[];
	for i in [1..n] do
		exp:=Valuation(MatList[i,i],p);	
		Append(~Denoms,exp);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,i]/pevExp),pevModExp);
		MatList[i,i]:=pevExp;
		for j in [i+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;
	Denoms:=[-(i+zeta):i in Denoms];
	H:=HermiteForm(Matrix(MatList));
//print"Step 10 IN HNF",Realtime()-tts;tts:=Realtime();
	Base:=Reverse([(F!  Parent([p])!Reverse(Eltseq(H[i]))) *K!p^zeta:i in [1..Degree(F)]]);
else
	Posi:=Signature(NormValues,[i`e:i in F`PrimeIdeals[p]]);
// HNF fÃ¼r reduzierte Basis
	for j in [1..#Posi] do
		tmpList:=[MatList[i]: i in Posi[j]];		
		H:=HermiteForm(Matrix(tmpList));
		tmpList:=[Parent([p])!Eltseq(H[i]):i in [1..#tmpList]];
		for i in [1..#tmpList] do
			MatList[Posi[j,i]]:=tmpList[i];			
		end for;
	end for;
// Normalisieren der Basis
	for i in [1..n] do
		nN:=exists(ind){ y : y in [1..n] | not MatList[i,y] eq 0};
		exp:=Valuation(MatList[i,ind],p);
		pevExp:=p^exp;
		inv:=Modinv(Parent(p)!(MatList[i,ind]/pevExp),pevModExp);
		MatList[i,ind]:=pevExp;
		for j in [ind+1..n] do
			MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
		end for;	
	end for;	

//		print"was",Realtime()-tts;tts:=Realtime();

// HNF fÃ¼r reduzierte Basis zum 2.
	for j in [1..#Posi] do

		tmpList:=[MatList[i]: i in Posi[j]];		
		H:=HermiteForm(Matrix(tmpList));
		tmpList:=[Parent([p])!Eltseq(H[i]):i in [1..#tmpList]];
		for i in [1..#tmpList] do
			MatList[Posi[j,i]]:=tmpList[i];			
		end for;		
	end for;
	//					print"drin?",Realtime()-tts;tts:=Realtime();
	Base:=Sort(Reverse([F!  Parent([p])!Reverse(Eltseq(MatList[i])) *K!p^zeta:i in [1..Degree(F)]]),func<x, y | Deg(x) - Deg(y)>);

//	F`PrimeIdeals[p]:=SAVEDATA;// IST NEU
	return Base,[],0,kt!1,p,killexpo;
end if;


if p in F`Index and assigned F`IndexBases and not IsDefined(F`IndexBases,p) and Expos eq [0:i in [1..s]] then
	F`IndexBases[p]:=[*Base,Sort(Denoms),pevModExp,alpha,p,killexpo*];
end if;

/*if Expos eq [0:i in Expos] and not IsDefined(F`maxorderfinite,p) then
	F`maxorderfinite[p]:=[*Base,Sort(Denoms),pevModExp,alpha*];
end if;*/

//F`PrimeIdeals[p]:=SAVEDATA;
//print"Step Raus",Realtime()-tts;tts:=Realtime();
return Base,Sort(Denoms),pevModExp,alpha,p,killexpo;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic PowerMod(base::FldFunElt,Modu::RngUPolElt,exp::RngIntElt)->FldFunElt
{}
if exp eq 0 then return 1; end if;
result:=1;
while exp gt 0 do

	if exp mod 2 eq 1 then 
	
		result:=(result* base) mod Modu;
		
	end if;
	base:=(base^2) mod Modu;
	exp:=Floor(exp/2);

end while;
return result;
end intrinsic;
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic PowerModFast(base::FldFunElt,p::RngUPolElt,exp::RngIntElt,e_P::RngIntElt)->FldFunElt
{}
if exp eq 0 then return 1; end if;
result:=1;Modu:=p;pexpo:=1;
baseexpo:=1;
initialexp:=exp;
resultexpo:=0;
while exp gt 0 do

	if exp mod 2 eq 1 then 
		baseexpo:=baseexpo;
		tmp:=Ceiling((baseexpo+resultexpo)/e_P)+1;
		Modu:=Modu*p^(tmp-pexpo);
		pexpo:=tmp;
		result:=(result* base) mod Modu;
	//	print"mod1",Valuation(Modu,p);
		resultexpo:=baseexpo+resultexpo;
		
	end if;
	if resultexpo eq initialexp then
		break;
	else	
		baseexpo:=2*baseexpo;
		tmp:=Ceiling(baseexpo/e_P)+1;
		Modu:=Modu*p^(tmp-pexpo);
		pexpo:=tmp;
		base:=(base^2) mod Modu;
	//			print"mod2",Valuation(Modu,p);
		exp:=Floor(exp/2);
	end if;
end while;
return result;
end intrinsic;
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic pBasisDirect(I::Rec,p::RngUPolElt)->SeqEnum
{Computes a p-integral basis of the fractional ideal in Hermite Form or if Reduced is set true an p-orthonormal basis of I}

//Initialization
tts:=Realtime();
Factorization(~I);
F:=I`Parent;
n:=Degree(F);
kx<x>:=PolynomialRing(PolynomialRing(ConstantField(F)));
_, _ := Montes(F,p);
tts:=Realtime();
Expos:=[0:i in [1..#F`PrimeIdeals[p]]];

for i in I`Factorization do
	if i[1] eq p then 	
		Expos[i[2]]:=i[3];	
	end if;
end for;

killexpo:=0;
if forall{i:i in [1..#Expos]|Expos[i] gt 0 } then
	killexpo:=Minimum([Floor(Expos[ll]/F`PrimeIdeals[p,ll]`e):ll in [1..#F`PrimeIdeals[p]]]);
	Expos:=[Expos[ll]-F`PrimeIdeals[p,ll]`e*killexpo:ll in [1..#F`PrimeIdeals[p]]];
end if;

if forall{i:i in [1..#Expos]|Expos[i] lt 0 } then
	killexpo:=Maximum([Ceiling(Expos[ll]/F`PrimeIdeals[p,ll]`e):ll in [1..#F`PrimeIdeals[p]]]);
	Expos:=[Expos[ll]-F`PrimeIdeals[p,ll]`e*killexpo:ll in [1..#F`PrimeIdeals[p]]];
end if;

if IsDefined(F`LocalIndex,p) and Expos eq [0:i in Expos] then
	if F`LocalIndex[p] eq 0 then
		return [F.1^i:i in [0..Degree(F)-1]],[0:i in [0..Degree(F)-1]],1,1,p,killexpo ;
	end if;
end if;
	if not F`LocalIndex[p] eq 0 then
		return pBasisRR(I,p) ;
	end if;

beta:=Maximum([Ceiling(-Expos[i]/F`PrimeIdeals[p,i]`e):i in [1..#F`PrimeIdeals[p]]]);

RefreshedExpos:=[Expos[i]+beta*F`PrimeIdeals[p,i]`e:i in [1..#F`PrimeIdeals[p]]];
print"Direct Step 1 ",Realtime()-tts;tts:=Realtime();

Generators(F,p);
print"Direct Step 2 ",Realtime()-tts;tts:=Realtime();
Multipliers_local:=[];

for i in [1..#F`PrimeIdeals[p]] do
	ModExpo:=Ceiling(RefreshedExpos[i]/F`PrimeIdeals[p,i]`e)+1;

	Append(~Multipliers_local,F!PowerModFast(F`PrimeIdeals[p,i]`Generator,p,RefreshedExpos[i],F`PrimeIdeals[p,i]`e));
end for;
alpha:=Maximum([Ceiling(RefreshedExpos[i]/F`PrimeIdeals[p,i]`e):i in [1..#F`PrimeIdeals[p]]] cat [0])+1;
print"Direct Step 3 ",Realtime()-tts;tts:=Realtime();
pevModExp:=p^alpha;
idealfactor:=&*Multipliers_local mod pevModExp;
print"Direct Step 4 ",Realtime()-tts;tts:=Realtime();
//p-int basis of O_F
if F`LocalIndex[p] eq 0 then
		p_intBase:= [F.1^i:i in [0..Degree(F)-1]];
else
	if assigned F`IndexBases then
		p_intBase:=F`IndexBases[Position(F`Index,p)];
	else
		p_intBase:=pBasisRR(F`PrimeIdeals[p,1]^0,p);			
	end if;		
end if;
print"Direct Step 5 ",Realtime()-tts;tts:=Realtime();
Base:=[i*idealfactor mod pevModExp:i in p_intBase];
print"Direct Step 6: Multiply basis ",Realtime()-tts;tts:=Realtime();


//Initialisierung vorbei

// Bis hierhin alles tutti!
//////////////Transforming into HNF////////////////////
//print"DenExpos",DenExpos;

Dens:=[kx!Denominator(i): i in Base];
maxdeg,maxden:=Maximum([Degree(i):i in Dens]);
maxden_p_val:=Integers()!(maxdeg/Degree(p));
PreBase:=Reverse(Sort([maxden*Base[i]:i in [1..#Base]],func<x, y | Deg(x) - Deg(y)>));
MatList:=[];
for j:=1 to #PreBase by  1 do
	Append(~MatList,Reverse(Parent([p])!Eltseq(PreBase[j])));
end for;
print"Direct Before HNF ",Realtime()-tts;tts:=Realtime();
H:=HermiteForm(Matrix(MatList));
MatList:=[Eltseq(H[i]):i in [1..n]];
Denoms:=[];
for i in [1..n] do
	exp:=Valuation(MatList[i,i],p);	
	Append(~Denoms,exp);
	pevExp:=p^exp;
	inv:=Modinv(Parent(p)!(MatList[i,i]/pevExp),pevModExp);
	MatList[i,i]:=pevExp;
	for j in [i+1..n] do
		MatList[i,j]:=(MatList[i,j]*inv) mod pevModExp;
	end for;	
end for;
Denoms:=[-i+maxden_p_val+beta:i in Denoms];
H:=HermiteForm(Matrix(MatList));
print"Direct AFTER HNF ",Realtime()-tts;tts:=Realtime();maxden_p_val,beta;
Base:=Reverse([(F!  Parent([p])!Reverse(Eltseq(H[i]))) *BaseField(F)!p^(maxden_p_val-beta):i in [1..Degree(F)]]);


return Base,Sort(Denoms),pevModExp,alpha,p,killexpo;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
  
intrinsic SIdealBaseRR(I::Rec, primelist::SeqEnum:Maximal:=false)->SeqEnum
    {Compute a local integral basis of I for the given set of primes.}
    K:=I`Parent;
    if primelist eq [] then return [K.1^i:i in [0..Degree(K)-1]]; end if;
    n:=Degree(I`Parent);
    Numlist:=[];    Denlist:=[];    DenlistCRT:=[];    ZetaList:=[];    faclist:=[];
    Factorization(~I);
    Rt:=Parent(primelist[1]);
	R<x>:=PolynomialRing(Rt);
ttt:=Realtime();

for p in primelist do
	//print"\n \n call pBasis for ",p; 	
    _, _ := Montes(I`Parent, p );
        // Exponents of the prime ideals
	pBase, pVals, pmod, alphap,factm,killexp:= pBasisRR(I, p); 
	if Maximal eq true and not IsDefined(K`IndexBases,p) then 
		K`IndexBases[p]:=[*pBase,pVals, pmod, alphap,factm,killexp*]; 	
	end if;    
	if 	#primelist eq 1 then return pBase,BaseField(K)!factm^killexp; end if;
	Append(~faclist,BaseField(K)!factm^killexp);
	pBase:=Reverse(pBase);	pVals:=Reverse(pVals);
	NumListe:=[];			zeta:=-Maximum(pVals);
	Append(~ZetaList,BaseField(K)!p^zeta);	// kann man verbessern
	for i in [1..n] do
  		if pVals[i] le 0 then // sollte nicht lt reichen!
     		CList:=Reverse(Eltseq(pBase[i]*BaseField(K)!p^pVals[i]));
        	Append(~NumListe, [Rt!CList[ll]:ll in [i..n]] );
        else
        	CList:=Reverse(Eltseq(Numerator(pBase[i])) );
        	Append(~NumListe, [Rt!CList[ll]:ll in [i..n]]);
	  	end if;
    end for;
    Append(~Numlist,NumListe);    Append(~Denlist,[BaseField(K)!p^(-v-zeta) : v in pVals]);
    tmpList:=[];
    for i in pVals do
        ex:=Maximum([i+1,0])+Maximum([alphap,0]);
        Append(~tmpList,p^ex);           			
	end for;
    Append(~DenlistCRT, tmpList);
end for;
MatList:=[];  

for i in [1..n] do
    NewCoeff:=[];
   	for m in [1..n-i+1] do
   		CoeffList:=[Numlist[j,i,m]: j in [1..#primelist]];	CRTList:=[DenlistCRT[j,i]: j in [1..#primelist]]; 
        //printf "h_%o,%o = %o = CRT([%o], [%o])\n", i-1, m-1, CRT(CoeffList,CRTList), Join([Sprintf("%o", num) : num in CoeffList], ", "), Join([Sprintf("%o", den) : den in CRTList], ", ");
	    Append(~NewCoeff,CRT(CoeffList,CRTList));		
    end for;
    fac:=Parent(primelist[1])!&*[Denlist[jj,i]:jj in [1..#primelist]];
    Append(~MatList,[l*fac:l in NewCoeff]);	
end for;

H:=HermiteForm(UpperTriangularMatrix(&cat MatList));
ZETA:=&*ZetaList; 
Base:=Reverse([K!Reverse([m :m in Eltseq(H[i])])*ZETA: i in [1..n]]);	
return Base,&*faclist;
end intrinsic;

//////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////
  
intrinsic SIdealBaseDirect(I::Rec, primelist::SeqEnum:Maximal:=false)->SeqEnum
    {Compute a local integral basis of I for the given set of primes.}
    K:=I`Parent;

    if primelist eq [] then return [K.1^i:i in [0..Degree(K)-1]]; end if;
    n:=Degree(I`Parent);
    Numlist:=[];
    Denlist:=[];
    DenlistCRT:=[];
    ZetaList:=[];
    faclist:=[];
    Factorization(~I);
    Rt:=Parent(primelist[1]);
	R<x>:=PolynomialRing(Rt);
	PModExp:=[];
ttt:=Realtime();

  for p in primelist do
 	
        _, _ := Montes(I`Parent, p );
        //print"\n Montes step",Realtime()-ttt;ttt:=Realtime();
        // Exponents of the prime ideals
  tts:=Realtime();
		//print"\n \n call pBasis for ",p;
        pBase, pVals, pmod, alphap,factm,killexp:= pBasisDirect(I, p); 
                //print"\n pBasis computed kklklkl",Realtime()-ttt;ttt:=Realtime();
            if Maximal eq true then Append(~K`IndexBases,pBase); end if;    
       		if 	#primelist eq 1 then return pBase,BaseField(K)!factm^killexp; end if;
        Append(~faclist,BaseField(K)!factm^killexp);
        if not pBase eq [K.1^i:i in [0..Degree(K)-1]] then //Hier Vorsicht!!!!
//print"Steppiii 1=";
			pBase:=Reverse(pBase);	pVals:=Reverse(pVals);
// print"pBasis took s=",Realtime()-tts;    pBase, pVals, pmod, alphap;    
//print"Steppiii 2=";
			NumListe:=[];
			zeta:=-Maximum(pVals);
			
			Append(~ZetaList,BaseField(K)!p^zeta);
			Append(~PModExp,pmod);// kann man verbessern
			//print"Steppiii 3=",Realtime()-tts;
    	    for i in [1..n] do
        		if pVals[i] le 0 then // sollte nicht lt reichen!
        			CList:=Reverse(Eltseq(pBase[i]*BaseField(K)!p^pVals[i]));
        			Append(~NumListe, [Rt!CList[ll]:ll in [i..n]] );

        		else
        			CList:=Reverse(Eltseq(Numerator(pBase[i])) );
        			Append(~NumListe, [Rt!CList[ll]:ll in [i..n]]);
	        	end if;
    	    end for;
                //print"Steppiii 4=",Realtime()-tts;
           Append(~Numlist,NumListe);
           Append(~Denlist,[BaseField(K)!p^(-v-zeta) : v in pVals]);
           tmpList:=[];
           for i in pVals do
           			ex:=Maximum([i+1,0])+Maximum([alphap,0]);
           			Append(~tmpList,p^ex);           			
	       end for;
           Append(~DenlistCRT, tmpList);
                   //print"\n For CRT sorted",Realtime()-ttt;ttt:=Realtime();

        else  
        	primelist:=Remove(primelist,Position(primelist,p));   
 		end if;       
    end for;
MatList:=[];  
        //print"\n BEFORE CRT",Realtime()-ttt;ttt:=Realtime();
// print"CRTData",DenlistCRT;

for i in [1..n] do
    		NewCoeff:=[];
   	for m in [1..n-i+1] do
   		CoeffList:=[Numlist[j,i,m]: j in [1..#primelist]];	CRTList:=[DenlistCRT[j,i]: j in [1..#primelist]]; 
	   if i eq 3 then  
	   end if; 
	           tts:=Realtime();      

	    Append(~NewCoeff,CRT(CoeffList,CRTList));		
    end for;
    fac:=Parent(primelist[1])!&*[Denlist[jj,i]:jj in [1..#primelist]];
    Append(~MatList,[l*fac:l in NewCoeff]);	
end for;

//O<r>:=quo<Parent(primelist[1])|mopFac>;
        //print"\n AFTER CRT",Realtime()-ttt;ttt:=Realtime();
H:=HermiteForm(UpperTriangularMatrix(&cat MatList));
        //print"\n HNF last time",Realtime()-ttt;ttt:=Realtime();

ZETA:=&*ZetaList; 
//	TempBase:=Reverse([K!Reverse(Eltseq(MatList[i]))*ZETA: i in [1..n]]);
//print"H",H,ZETA;

Base:=Reverse([K!Reverse([m :m in Eltseq(H[i])])*ZETA: i in [1..n]]);	
return Base,&*faclist;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic IdealBaseRR(I::Rec:Maximal:=false)->SeqEnum
    {Compute a Hermite basis of the ideal I}

//if not assigned I`Basis then
	F:=I`Parent;	kt:=PolynomialRing(ConstantField(F));
	    tt:=Realtime();
	if #I`Factorization eq 0 then Maximal:=true; end if;
    if not assigned F`FactorizedDiscriminant then
 		d:=kt! Discriminant(DefiningPolynomial(F));   
    	sq:=SquarefreeFactorization(d);
		d:=kt!(d/&*[i[1]:i in sq]);
		print"disc is now square free (IdealBaseRR)",Realtime()-tt;
    	F`FactorizedDiscriminant:=Factorization(d);
    end if;
    if not assigned F`Index then
    	tt:=Realtime();
    	IndEx(F);
    	print"IndEx in IdealBaseRR",Realtime()-tt;
    end if;
   	if Maximal eq true then
   		if not assigned F`IndexBases then
   		F`IndexBases:=[];
	    base:= SIdealBaseRR(I, F`Index:Maximal:=true);
   		return base,1;   	
   		end if;
   	end if; 
    primes:=SetToSequence(Set(RationalRadical(I) cat F`Index));
    if primes eq [] then
    	return [F.1^i:i in [0..Degree(F)-1]],1;
    end if;
    print"Ideal infos",#primes,[Degree(i):i in primes];
    base,fac:= SIdealBaseRR(I, primes);
	return base,fac;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic IdealBaseDirect(I::Rec:Maximal:=false)->SeqEnum
    {Compute a Hermite basis of the ideal I}

//if not assigned I`Basis then
	F:=I`Parent;
	    tt:=Realtime();

    if not assigned F`FactorizedDiscriminant then
	F`FactorizedDiscriminant:=Factorization( PolynomialRing(ConstantField(F))! Discriminant(DefiningPolynomial(F)));
    end if;
    if not assigned F`Index then
    	IndEx(F);
    end if;
   	if Maximal eq true then
   		if not assigned F`IndexBases then
   		F`IndexBases:=[];
	    base:= SIdealBaseRR(I, F`Index:Maximal:=true);
   		return base,1;   	
   		end if;
   	end if; 
    primes:=SetToSequence(Set(RationalRadical(I) cat F`Index));
    if primes eq [] then
    	return [F.1^i:i in [0..Degree(F)-1]];
    end if;
    print"Ideabasis kosten Factori=",Realtime()-tt;
    print"Ideal infos",#primes,[Degree(i):i in primes];
    base,fac:= SIdealBaseDirect(I, primes);
	return base,fac;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


//Basis Computation with just one Application of HNF

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic MaximalOrder(F::FldFun)->SeqEnum
    {Compute basis of maximal order}
tt:=Realtime();
//if not assigned I`Basis then
R:=PolynomialRing(ConstantField(F));
_, _ := Montes(F,R.1);
I:=F`PrimeIdeals[R.1,1]^0;
B:=IdealBaseRR(I:Maximal:=true);	    
print"Basis Computation took",Realtime()-tt;
den:=R!Denominator(B[#B]);
M := Matrix([Parent([R.1])!Eltseq(den*x) : x in B]);
O:=Order(EquationOrderFinite(F),M,den:Check:=false);
SetOrderMaximal(O,true);
return O,B;
end intrinsic;


/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////

intrinsic MaximalOrderInfinitee(F::FldFun)->SeqEnum
    {Compute basis of maximal order}
	tt:=Realtime();
	FF:=InftyField(F);
	R:=PolynomialRing(ConstantField(F));
	T:=BaseField(F).1;
//if not assigned I`Basis then

   		t:=PolynomialRing(ConstantField(F)).1;
  
        _, _ := Montes(FF,t);
    	I:=FF`PrimeIdeals[t,1]^0;
  
		B:=pBasisRR(I,t);	    
  
 

print"Basis Computation took",Realtime()-tt;
EO:=EquationOrderInfinite(F);
print"Step1";
KK:=CoefficientRing(EO);
print"Step2";
B:=[TransMap(i,F):i in B];
M:=Matrix([Eltseq(i):i in B]);
n:=Degree(F);
 D:=DiagonalMatrix([T^(i*F`Cf):i in [0..n-1]]);
 MM:=M*D;
 print"Step3";
den:=KK!(1/MM[n,n]);
 print"Step4";
 Mat:=ChangeRing(den*MM,KK);
  print"Step5";
//Matrix([Parent([R.1])!Eltseq(den*x) : x in B]);
O:=Order(EO,Mat,den:Check:=false);
SetOrderMaximal(O,true);
print"done";
return O,B;
//return B;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Begin IdealsBasis
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic pBasisTriangular(K::FldFun, p::RngUPolElt : exp:=false, store:=false, random_exponent:=[0, 0])-> SeqEnum, SeqEnum, SeqEnum
    { }

    if not assigned(K`PrimeIdeals) or not IsDefined(K`PrimeIdeals, p) then
        _, _ := Montes(K, p : Basis:=false);
    end if;

    // This allows us to only specify up to the highest indexed prime
    // ideal with non-zero exponent.
    if Type(exp) ne BoolElt then
        if #K`PrimeIdeals[p] gt #exp then
            exp cat:= [ Random(random_exponent[1], random_exponent[2])
                            : i in [#exp+1..#K`PrimeIdeals[p]] ];
        end if;
    end if;

    p_basis, nums, dexp := MaxMin(K, p : exponents:=exp);

    if store eq true then
        K`pBasis[p] := p_basis;
    end if;

    return p_basis, nums, dexp, exp;
end intrinsic; // pBasisTriangular

intrinsic HermiteFormBasis(K::FldFun, p::RngUPolElt, nums::SeqEnum, dexp::SeqEnum : algorithm:="triangular", triangular_input:=false, maximal_order:=false)-> SeqEnum
    { }

    if algorithm eq "triangular" then
        HNF_routine := HermiteFormTriangularSimple;
        //hnf_matrix := HermiteFormTriangularSimple(matrix_red);
    elif algorithm eq "magma" then
        HNF_routine := HermiteForm;
        //hnf_matrix := HermiteForm(matrix_red);
    else
        printf "Error: Unknown HNF algorithm %o.\n", algorithm;
        return [];
    end if;

    n := Degree(K);
    maxexp := Maximum(dexp);
    p_max := p^maxexp;
    O := Parent(p);
    KT := BaseField(K);

    if maximal_order eq true then
        Nums := [ [ (O!Coefficient(nums[i], j) * p^(maxexp-dexp[i])) mod p^(maxexp+1)
                    :  j in [n-1..0 by -1] ]
                        : i in [n..1 by -1] ];
    else
        Nums := [ [ O!Coefficient(nums[i], j) * p^(maxexp-dexp[i])
                    :  j in [n-1..0 by -1] ]
                        : i in [n..1 by -1] ];
    end if;

    A := Matrix(Parent(p), Nums);
    H := HNF_routine(A);

    if triangular_input eq false then
        dens := [ (KT!p)^Valuation(H[i,i],p) : i in [1..n] ];

        for i in [1..n] do
            inv := Modinv(O!(H[i,i]/dens[i]), p_max);

            H[i,i] := dens[i];
            for j in [i+1..n] do
                H[i,j] := H[i,j]*inv mod p_max;
            end for;
        end for;

        H := HNF_routine(H);
    end if;

    p_max := K!p_max;
    hnf_basis := Reverse([ K!Reverse(Eltseq(H[i]))/p_max : i in [1..n] ]);

    return hnf_basis; 
end intrinsic; // HermiteFormBasis

intrinsic HermiteFormBasis(K::FldFun, basis::SeqEnum)-> SeqEnum
    { We assume that the (global) basis is triangular. }

    n := #basis;
    kt := PolynomialRing(ConstantField(K));
    dens := [ Denominator(g) : g in Reverse(basis) ];
    maxden := dens[1];

    int_basis := [ g*maxden : g in Reverse(basis) ];
    A := Matrix(kt, [ Reverse(Eltseq(g*maxden, BaseField(K)))
                        : g in Reverse(basis) ]);

    H := HermiteForm(A);

    hnf_basis := [ K!Reverse(Eltseq(H[i]))/maxden : i in [n..1 by -1] ];

    return hnf_basis;
end intrinsic; // HermiteFormBasis


intrinsic pHermiteBasisMaxMin(K::FldFun, p::RngUPolElt : algorithm:="triangle")-> SeqEnum
    { }

    if not assigned(K`pHermiteBasis) or not IsDefined(K`pHermiteBasis, p) then
        if not assigned(K`PrimeIdeals) or not IsDefined(K`PrimeIdeals, p) then
            _, _ := Montes(K, p : Basis:=false);
        end if;

        p_basis, nums, dexp := MaxMin(K, p);

        n := Degree(K);
        Dexp := Reverse(dexp);
        maxexp := Dexp[1];
        Nums := [ [ Coefficient(nums[i], j) * p^(maxexp-dexp[i])
                    :  j in [n-1..0 by -1] ]
                        : i in [n..1 by -1] ];

        if algorithm eq "triangle" then
            matrix_red := Matrix(Nums);
            hnf_matrix := HermiteFormTriangularSimple(matrix_red);
        else
            printf "Error: Unknown HNF algorithm %o.\n", algorithm;
            return [];
        end if;

        hnf_matrix := Matrix([ [hnf_matrix[i,j] / hnf_matrix[i,i]
                                : j in [1..n]]
                                    : i in [1..n] ]);
        K`pHermiteBasis[p] := basisFromMatrix(hnf_matrix, dexp, K, p);
    end if;

    return K`pHermiteBasis[p];
end intrinsic; // pHermiteBasisMaxMin

intrinsic SumTimes(a::SeqEnum, b::SeqEnum)-> SeqEnum
    { }

    if #a gt #b then
        b cat:= [Cputime() - Cputime() : i in [#b+1..#a] ];
    elif #a lt #b then
        a cat:= [Cputime() - Cputime() : i in [#a+1..#b] ];
    end if;

    return [ a[i] + b[i] : i in [1..#a] ];
end intrinsic; // SumTimes

intrinsic SIntegralBasisMaxMin(K::FldFun, primelist::SeqEnum, explist::SeqEnum : noskip:=false)-> SeqEnum
    { Compute a local integral basis for the given set of primes. }

    n := Degree(K);
    kt := Parent(primelist[1]);
    Numlist := [];
    Denlist := [];
    DenCRTlist := [];

    for i in [1..#primelist] do
        p := primelist[i];
        exp := explist[i];

        _, _ := Montes(K, p);
        if #exp lt #K`PrimeIdeals[p] then
            exp cat:= [ 0 : i in [#exp+1..#K`PrimeIdeals[p]] ];
        end if;

        if K`LocalIndex[p] gt 0  or noskip eq true then
            times := K`Times;
            K`Times := [ ];
            sfl_count := K`SFLCount;
            p_basis, nums, dexp := pBasisTriangular(K, p : exp:=exp);
            K`Times := SumTimes(K`Times, times);
            K`SFLCount +:= sfl_count;

            dens := [ BaseField(K)!p^e : e in dexp ];
            alpha := Maximum([ Ceiling(exp[i]/K`PrimeIdeals[p,i]`e)
                                    : i in [1..#exp] ]);
            dens_crt := [ p^(Maximum(alpha, 0)+Maximum(e+1, 0)) : e in dexp ];

            Append(~Numlist, [ Coefficients(g) : g in nums ]);
            Append(~Denlist, dens);
            Append(~DenCRTlist, dens_crt);
        end if;
    end for;

    nprimes := #Denlist;

    if nprimes eq 0 then
        return [K.1^k: k in [0..n-1]];
    end if;

    tmps := Cputime();
    SBasis := [ K | ];

    for i := 1 to n do
        Dens := [ Denlist[k, i] : k in [1..nprimes] ];
        DensCRT := [ DenCRTlist[k,i] : k in [1..nprimes] ];
        coeffs := [];
        for j := 1 to i-1 do
            Nums := [Numlist[k, i, j] : k in [1..nprimes]];
            Append(~coeffs, CRT(Nums, DensCRT));
        end for;
        coeffs cat:= [0: j in [1..n-#coeffs]];
        Append(~SBasis, (K.1^(i-1)+K!coeffs)/&*Dens);
    end for;
    Append(~K`Times, Cputime() - tmps);

    return SBasis;
end intrinsic; // SIntegralBasisMaxMin


intrinsic IntegralBasisMaxMin(K::FldNum)->SeqEnum
    { Compute a basis of the maximal order Z_K of K and the discriminant of K. }

    if not assigned K`IntegralBasis then
        if not assigned K`Discriminant then
            K`Discriminant := Discriminant(DefiningPolynomial(K));
        end if;
        d := K`Discriminant;

        if not assigned K`FactorizedDiscriminant then
            printf "Discriminant is a %o bit number, factorising...\n",
                Ceiling(Log(2, Abs(d)));
            primelist := PrimeDivisors(d);

            d_fac := [ [p, Valuation(d, p)] : p in primelist ];
        else
            primelist := [ factor[1] : factor in K`FactorizedDiscriminant ];
            d_fac := [ [p, Valuation(d, p)] : p in primelist ];
        end if;

        empty_exp := [ [] : p in primelist ];
        K`IntegralBasis := SIntegralBasisMaxMin(K, primelist, empty_exp);

        // FIXME: Do I really need to assign this to anything other than
        //        what I already have in d_fac?
        K`FactorizedDiscriminant := [];
        for p in primelist do
            d := d div p^(2*K`LocalIndex[p]);
            Append(~K`FactorizedDiscriminant, [p, Valuation(d, p)]);
        end for;
    end if;

    return K`IntegralBasis;
end intrinsic; // IntegralBasisMaxMin

intrinsic idealBasis(I::Rec)-> SeqEnum
    { }

    K := I`Parent;
    kt := PolynomialRing(ConstantField(K));

    if not assigned I`Factorization then
        Factorization(~I);
    end if;

    if not assigned K`Discriminant then
        K`Discriminant := kt!Discriminant(DefiningPolynomial(K));
    end if;
    d := K`Discriminant;

    if not assigned K`FactorizedDiscriminant then
        printf "Discriminant is a degree %o polynomial, factoring...\n",
                    Degree(d);

        sqfree_factors := SquareFreeFactorization(d);
        sq_d := kt!(d / &*[ f[1] : f in sqfree_factors ]);
        K`FactorizedDiscriminant := Factorization(sq_d);
    end if;

    primelist := [ p : p in { f[1] : f in I`Factorization }
                            join { f[1] : f in K`FactorizedDiscriminant } ];

    exp := [ [] : p in primelist ];
    for f in I`Factorization do
        p_ind := Index(primelist, f[1]);
        if #exp[p_ind] lt f[2] then
            // Make exp[p] long enough to fit P_f[2].
            exp[p_ind] cat:= [ 0 : i in [#exp[p_ind]+1..f[2]] ];
        end if;
        exp[p_ind,f[2]] := f[3];
    end for;

    basis := SIntegralBasisMaxMin(I`Parent, primelist, exp);

    return basis;
end intrinsic; // idealBasis

intrinsic pIdealBasis(K::FldNum, p::RngUPolElt, exp::SeqEnum)-> SeqEnum
    { Returns a p-basis of a fractional ideal constructed from the product
      of the prime ideals P_i lying over p with exponent e_i. }

    if not assigned(K`PrimeIdeals) or not IsDefined(K`PrimeIdeals, p) then
        _, _ := Montes(K, p : Basis:=false);
    end if;

    // This allows us to only specify up to the highest indexed prime
    // ideal with non-zero exponent.
    if #K`PrimeIdeals[p] gt #exp then
        exp cat:= [ 0 : i in [#exp+1..#K`PrimeIdeals[p]] ];
    end if;

    basis := MaxMin(K, p : exponents:=exp);

    return basis;
end intrinsic; // pIdealBasis


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic MaxMinCore(okbasis_values::SeqEnum, modifiers::SeqEnum)-> SeqEnum, SeqEnum, List, List
    { The core of the MaxMin algorithm.
      Input:
        - The $\Q$-value of every element of each Okutsu $\P$-basis for all
          $\P$, $\Q$ in the input set.
        - 
      Output:
        - Indices of final basis elements as product of input bases elements
        - Denominator exponents of each basis element
        - The $\P$-value of each basis element for all input $\P$
        - The required $\P$-value of each Montes approximation to $F_\P$ }

    indices := [ ];
    den_exp := [ExtendedReals()|];
    values := [* *];

    s := #okbasis_values;
    J := [ 1 : i in [1..s] ];
    nps := [ #okbasis_values[i]-1 : i in [1..s] ];
    n := &+[ np : np in nps ];

    approx_values := [* 0 : i in [1..s] *];
    req_approx_values := [* 0 : i in [1..s] *];

    for m := 0 to n do
        S := [ &+[ okbasis_values[k,J[k],i]
                    : k in [1..s] ] - modifiers[i]
                        : i in [1..s] ];
        v, u := Min([ S[i] + approx_values[i] : i in [1..s] ]);

        Append(~den_exp, S[u]);
        Append(~indices, J);
        Append(~values, S);

        // Store the required phi_P values.
        if m lt n then
            for i in [1..s] do
                if approx_values[i] eq Infinity() then
                    o_val := S[i] - okbasis_values[i,J[i],i];
                    req_approx_values[i] := Max(req_approx_values[i],
                                                v - o_val);
                end if;
            end for;
        end if;

        J[u] +:= 1;
        if J[u] gt nps[u] then
            approx_values[u] := Infinity();
        end if;
    end for;

    return indices, den_exp, values, req_approx_values;
end intrinsic; // MaxMinCore


intrinsic MaxMin(K::FldFun, p::RngUPolElt : exponents:=false)-> SeqEnum, SeqEnum, SeqEnum
    { }

    maxmin_time := Cputime();
    s := #K`PrimeIdeals[p];
    ok_frames := calculateOkutsuFramesValues(K`PrimeIdeals[p]);
    bases_indices := [* *];

    nps := [ type`e*type`f : type in K`PrimeIdeals[p] ];
    rs := [ #type`Type : type in K`PrimeIdeals[p] ];

    for i := 1 to s do
        Append(~bases_indices, calculateBasisIndices(K`PrimeIdeals[p,i]));
    end for;
    bases_values := computeBasesValues(bases_indices, ok_frames);

    if Type(exponents) eq BoolElt and exponents eq false then
        modifiers := [ 0 : i in [1..s] ];
        maximal_order := true;
    else
        modifiers := [ exponents[i]/K`PrimeIdeals[p,i]`e : i in [1..s] ];
        maximal_order := false;
    end if;
            

    // Call MaxMin Core.
    indices, den_exp, values, req_approx_values := MaxMinCore(bases_values,
                                                              modifiers);

    sfl_time := Cputime();

    liftMontesApproximations(~K`PrimeIdeals[p], req_approx_values);
    updateOkutsuFrames(~ok_frames, K`PrimeIdeals[p]);

    polmul_time := Cputime();

    if #ok_frames eq 1 then
        basis := computeOkutsuBasis(ok_frames[1]);
    else
        mod_exponents := reductionExponents(den_exp[1..#den_exp-1], modifiers);
        basis := computeLocalBasis(indices, bases_indices, ok_frames,
                                   p^mod_exponents[#mod_exponents]);
    end if;

    // Remove the degree n element so we have a non-extended basis.
    basis := basis[1..#basis-1];
    den_exp := den_exp[1..#den_exp-1];

    reduce_time := Cputime();
    reducepBasis(~basis, den_exp, modifiers, p);

    den_exp := [ Floor(v) : v in den_exp ];

    p_basis := [ (K![ Coefficient(basis[i], j)
                    : j in [0..#basis-1] ])/K!p^den_exp[i]
                        : i in [#basis..1 by -1] ];

    K`Times cat:= [ sfl_time - maxmin_time,
                    polmul_time - sfl_time,
                    reduce_time - polmul_time,
                    Cputime() - reduce_time ];

    return Reverse(p_basis), basis, den_exp;
end intrinsic; // MaxMin


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic liftMontesApproximations(~types::SeqEnum[Rec], req_phip_vals::List : range:=false)
    { Increase each $\phi_\P$ so that it's $\P$-value is at least that of
      the corresponding entry in `req_phip_vals`. }

    if Type(range) eq BoolElt and range eq false then
        range := [1 ..#types];
    end if;

    for i in [1..#req_phip_vals] do
        ri := range[i];
        V := types[ri]`Type[#types[range[i]]`Type]`V;
        required_slope := (req_phip_vals[i] * types[ri]`e) - V;
        if required_slope ge types[ri]`Type[#types[ri]`Type]`slope then
            last_lvl := types[ri]`Type[#types[ri]`Type];
            h := last_lvl`h - last_lvl`cuttingslope;
            lasth := Ceiling(required_slope) - last_lvl`cuttingslope;
            path := PathOfPrecisions(lasth,h);

            SFL(~types[ri]`Type, Ceiling(required_slope));
            
            if #path gt 0 then
                types[ri]`Parent`SFLCount +:= (#path - 1);
            end if;
        end if;
    end for;

end intrinsic; // liftMontesApproximations


intrinsic calculateOkutsuFramesValues(types)-> List
    { Calculate the primary and secondary values for the phi-polynomials of
      the Okutsu frames for all types. }

    type_levels := [#tt`Type - 1 : tt in types ];

    QQ := RationalField();
    values := [ [ [* -1 : j in [1..#types] *]
                : r in [1..#types[i]`Type] ]
                    : i in [1..#types] ];

    for i := 1 to #types do
        lvlsi := types[i]`Type;

        // Calculate primary values.
        for k := 1 to #lvlsi do
            values[i,k,i] := (lvlsi[k]`V + lvlsi[k]`slope)/lvlsi[k]`prode;
        end for;

        // Calculate cross values.
        for j := 1 to i-1 do
            lvlsj := types[j]`Type;

            indco := IndexOfCoincidence(types[i], types[j]);

            if indco gt 0 then
                refi := Append(lvlsi[indco]`Refinements,
                               [* lvlsi[indco]`Phi, lvlsi[indco]`slope *]);
                refj := Append(lvlsj[indco]`Refinements,
                               [* lvlsj[indco]`Phi, lvlsj[indco]`slope *]);
                length := Min(#refi, #refj);
                k := 2;
                while k le length and refi[k,1] eq refj[k,1] do
                    k +:= 1;
                end while;
                cutting_phi := refi[k-1,1];
                slope_i := refi[k-1,2];
                slope_j := refj[k-1,2];
                min_slope := Min(slope_i, slope_j);

                // Calculate the cross values of each $Phi_{k,\P}$ for
                // $k < $\ell$.
                for k := 1 to indco - 1 do
                    values[i,k,j] := values[i,k,i];
                    values[j,k,i] := values[i,k,i];
                end for;

                // Calculate the cross values of each $Phi_{\ell,\P}$.
                min_val := (lvlsi[indco]`V+min_slope)/lvlsi[indco]`prode;
                if cutting_phi eq lvlsj[indco]`Phi then
                    values[j,indco,i] := (lvlsi[indco]`V + slope_i)/
                                                lvlsi[indco]`prode;
                else
                    values[j,indco,i] := min_val;
                end if;
                if cutting_phi eq lvlsi[indco]`Phi then
                    values[i,indco,j] := (lvlsi[indco]`V + slope_j)/
                                                lvlsi[indco]`prode;
                else
                    values[i,indco,j] := min_val;
                end if;

                min_val /:= Degree(lvlsi[indco]`Phi);
            else
                min_val := 0;
            end if;

            // Calculate the cross values of each $Phi_{k,\P}$ for $k > \ell$.
            for k := indco + 1 to #lvlsi do
                values[i,k,j] := Degree(lvlsi[k]`Phi) * min_val;
            end for;
            for k := indco + 1 to #lvlsj do
                values[j,k,i] := Degree(lvlsj[k]`Phi) * min_val;
            end for;


        end for;
    end for;

    // Include the degree of each element of the Okutsu frame and the index of
    // the phi polinomial along with its values.
    ok_frames := [ [ rec<OkutsuFrameLevel|
                            degree:=Degree(types[i]`Type[k]`Phi),
                            index:=k,
                            values:=values[i,k],
                            polynomial:=types[i]`Type[k]`Phi>
                        : k in [1..#types[i]`Type] ]
                            : i in [1..#types] ];

    // If $\phi_1$ has degree greater than 1, add an extra element for the
    // x required to make okutsu basis elements of degree not congruent with 0
    // mod deg(phi_1).
    x := Parent(types[1]`Type[1]`Phi).1;
    for i in [1..#types] do
        if ok_frames[i,1]`degree gt 1 then
            Insert(~ok_frames[i], 1, rec<OkutsuFrameLevel|
                                            degree:=1,
                                            index:=0,
                                            values:=[* 0 : type in types *],
                                            polynomial:=x>);
        end if;
    end for;

    return ok_frames;
end intrinsic; // calculateOkutsuFramesValues


intrinsic updateOkutsuFrame(~frame::SeqEnum, type::Rec, i::RngIntElt)
    { Update an Okutsu frame after a type has been (single factor) lifted. }

    lvlr := type`Type[#type`Type];
    frame[#frame]`polynomial := lvlr`Phi;
    frame[#frame]`values[i] := (lvlr`V + lvlr`slope)/lvlr`prode;

end intrinsic; // updateOkutsuFrame

intrinsic updateOkutsuFrames(~ok_frames::SeqEnum, types::SeqEnum)
    { }

    for i in [1..#ok_frames] do
        updateOkutsuFrame(~ok_frames[i], types[i], i);
    end for;

end intrinsic; // updateOkutsuFrames

intrinsic computeOkutsuBasis(frame)-> SeqEnum
    { Efficiently computes the Okutsu basis for the given Okutsu frame. This is
      produced by the canonical product of the $\phi$-polynomials from. }

    basis := [ Parent(frame[1]`polynomial)!1 ];
    
    for m := 2 to Degree(frame[#frame]`polynomial)+1 do
        _, ri := Min([ (m-1) mod frame[r]`degree : r in [#frame..1 by -1] ]);
        r := #frame - ri + 1;
        Append(~basis, basis[m - frame[r]`degree] * frame[r]`polynomial);
    end for;

    return basis;
end intrinsic; // computeOkutsuBasis

intrinsic computeBasisValues(t_ind, t_frame)-> SeqEnum
    { Efficiently computes the values of a basis. }

    // Sanity check.
    if #t_frame eq 0 then
        return [ [0] ];
    end if;

    // "Normalise" the degrees so the first is 1.
    for k in [#t_frame..1 by -1]  do
        t_frame[k]`degree := Integers()!(t_frame[k]`degree/t_frame[1]`degree);
    end for;

    if Type(t_frame[1]`values[1]) eq List then
        // This okutsu frame is a composite "terminal" frame.
        values := [ [ [ExtendedReals()| 0 : v in val_group]
                        : val_group in t_frame[1]`values ] ];
        for m := 2 to #t_ind do
            v, u := Max([t_ind[m,i]-t_ind[m-1,i] : i in [1..#t_ind[m]]]);
            prev_vals := [ values[m-t_frame[u]`degree,j]
                                : j in [1..#t_frame[1]`values] ];
            e_vals := [ [ExtendedReals()| prev_vals[j,k]+t_frame[u]`values[j,k]
                            : k in [1..#prev_vals[j]] ]
                                : j in [1..#prev_vals] ];
            Append(~values, e_vals);
        end for;
    else
        // This is a normal Okutsu frame.
        values := [ [ ExtendedReals()| 0 : j in [1..#t_frame[1]`values] ] ];
        for m := 2 to #t_ind do
            v, u := Max([t_ind[m,i]-t_ind[m-1,i] : i in [1..#t_ind[m]]]);
            e_vals := [ExtendedReals()|
                          values[m-t_frame[u]`degree,j] + t_frame[u]`values[j]
                              : j in [1..#t_frame[1]`values] ];
            Append(~values, e_vals);
        end for;
    end if;

    return values;
end intrinsic; // computeBasisValues

intrinsic computeBasesValues(indices, okutsu_frames)-> List
    { Efficiently computes the values of all Oktusu bases. }

    bases_values := [ ];

    for i in [1..#indices] do
        values := computeBasisValues(indices[i], okutsu_frames[i]);
        Append(~bases_values, values);
    end for;

    return bases_values;
end intrinsic; // computeBasesValues

intrinsic calculateBasisIndices(type::Rec: mod_lvl:=0)-> List
    { Calculate the indices that represent basis elements. The 0th indiex is
      the exponent of x (only used if f_0 > 1) then the i-th index is the
      exponent of phi_i,P for the P associated with this type. }

    lvls := type`Type;
    m1 := Degree(type`Type[1]`Phi mod type`IntegerGenerator);
    pools := [ ];

    if mod_lvl eq 0 then
        if m1 gt 1 then
            pools cat:= [ [0..m1-1] ];
        end if;
        mod_lvl := 1;
    end if;
    pools cat:= [ [0..lvls[r]`e * lvls[r]`f - 1] : r in [mod_lvl..#lvls-1] ];
    pools cat:= [ [0] ];

    indices := itertoolsProduct(pools);
    Append(~indices, [ 0 : r in [1..#indices[1]-1] ] cat [1]);

    return indices;
end intrinsic; // calculateBasisIndices


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

intrinsic computeLocalBasis(lb_indices, bases_indices, frames, pprec)-> List
    { Efficiently compute a local basis given the indices of which element
      from each $\P$-basis is used to make up an element of the final basis.

      Note: We don't need to compute the Okutsu basis for each $\P$ to do this,
            just the Okutsu frame. }

    s := #frames;
    local_basis := [* Parent(frames[1,1]`polynomial)!1 *];
    f_bases := [ AssociativeArray() : i in [1..s] ];

    for m := 2 to #lb_indices do
        _, i := Max([lb_indices[m,j]-lb_indices[m-1,j] : j in [1..s]]);
        
//        printf "%3o: %o %o\n", m, lb_indices[m], bases_indices[i,lb_indices[m,i]];
        u_ind := lb_indices[m,i];
        _, u := Max([bases_indices[i,u_ind,j] - bases_indices[i,u_ind-1,j]
                            : j in [1..#bases_indices[i,u_ind]]]);
        ch_index := frames[i,u]`index;
        ch_deg := frames[i,u]`degree;

        if u eq 1 then
            basis_el := local_basis[m-1] * frames[i,1]`polynomial;
        elif ch_index eq 1 then
            basis_el := local_basis[m-ch_deg] * frames[i,u]`polynomial;
        else
            not_i := [1..i-1] cat [i+1..s];
            if &+[ lb_indices[m,j]-lb_indices[m-ch_deg,j] : j in not_i ] eq 0 then
                basis_el := local_basis[m-ch_deg] * frames[i,u]`polynomial;
            else
                basis_el := 1;
                for i in [1..#bases_indices] do
                    computeOkutsuBasisElement(~f_bases[i], frames[i],
                                              bases_indices[i],
                                              lb_indices[m,i]);
                    basis_el *:=  f_bases[i,lb_indices[m,i]];
                end for;
            end if;
        end if;

        // We reduce each element mod p^prec where prec is the maximum
        // precision required by the basis. This keeps the precision reasonably
        // low.
        basis_el := basis_el mod pprec;
        Append(~local_basis, basis_el);
    end for;


    return [g : g in local_basis];
end intrinsic; // computeLocalBasis

intrinsic computeOkutsuBasisElement(~basis, frame, indices, m)
    { }

    // basis := AssociativeArray();

    if IsDefined(basis, m) then
        return;
    end if;

    if m eq 1 then
        // Cheating a bit, but this *must* be true.
        basis[m] := Parent(frame[1]`polynomial)!1;
    else
        _, u := Max([ indices[m,j]-indices[m-1,j] : j in [1..#indices[m]] ]);
        computeOkutsuBasisElement(~basis, frame, indices,
                                  m - frame[u]`degree);
        basis[m] := basis[m - frame[u]`degree] * frame[u]`polynomial;
    end if;

end intrinsic; // computeOkutsuBasisElement


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic basisFromMatrix(matrix::Mtrx, basis_values, K::FldFun, p::RngUPolElt)->SeqEnum
    { Returns a basis comprised of elements from `K`. }

    n := #basis_values;
    
    return [ K![matrix[i,j] : j in [n..1 by -1]]/p^basis_values[n+1-i] : i in [n..1 by -1] ];
end intrinsic; // basisFromMatrix

intrinsic reductionExponents(dexp::SeqEnum, modifiers::SeqEnum)-> SeqEnum
    { Calculate the exponents for reduction modulo p^nu. }

    max_modifier := Maximum(modifiers);
    mod_exponents := [ Maximum(Ceiling(v + max_modifier), 0)+1 : v in dexp ];

    return mod_exponents;
end intrinsic; // reductionExponents

intrinsic reducepBasis(~nums::SeqEnum, dexp::SeqEnum, modifiers::SeqEnum, p::RngUPolElt)
    { Reduce all basis numerators mod their valuation. }

    // We can reduce each basis element g modulo p^(w_I(g + max))
    max_modifier := Maximum(modifiers);
    mod_exponents := [ Maximum(Ceiling(v + max_modifier), 0)+1 : v in dexp ];
//    printf "\n(reducepBasis) mod_exponents: %o\n", mod_exponents;
    mods := [ p^mod_exponents[1] ];
    prime_cache := AssociativeArray();
    for i in [2..#mod_exponents] do
        delta := mod_exponents[i] - mod_exponents[i-1];
        j := Index(mod_exponents, delta);
        if j gt 0 then
            delta_power := mods[j];
        elif IsDefined(prime_cache, j) then
            delta_power := prime_cache[j];
        else
            delta_power := p^j;
            prime_cache[j] := delta_power;
        end if;
        
        Append(~mods, mods[i-1] * delta_power);
    end for;

    tmps := Cputime();
    n := #nums;
    Ox := Parent(nums[1]);
    for i in [1..n] do
        coeffs := Parent([p]) ! Eltseq(nums[i]);
        nums[i] := Ox ! [ coeffs[j] mod mods[i] : j in [1..#coeffs] ];
    end for;

end intrinsic; // reducepBasis


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//      Utility functions
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic HermiteFormTriangularSimple(A::Mtrx)-> Mtrx
    { Compute the Hermite Normal Form of a square triangular matrix. }

    require Nrows(A) eq Ncols(A): "A must be a square matrix.";
    n := Nrows(A);

    rows_times := [];

    for i in [2..n] do
        for j in [i-1..1 by -1] do
            v := A[j,i] div A[i,i];
            AddRow(~A, -v, i, j);
        end for;
    end for;

    return A; 
end intrinsic;


////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


intrinsic itertoolsProduct(pools)-> List
    { The ugly implementation of the product function from python's itertools. }

    result := [* [] *];

    for pool in Reverse(pools) do
        midresult := [* *];
        for x in result do
            midresult cat:= [* [ y ] cat x : y in pool *];
        end for;
        result := midresult;
    end for;

    return result;
end intrinsic;






////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


//////////////////////////Test Polynomials//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Apnk(Fq::FldFin,p::RngUPolElt,n::RngIntElt,k::RngIntElt,r::RngIntElt)->FldFun
{}

Fqt:=Parent(p);

Kx<T> := RationalFunctionField(Fq);

KxT<x> := PolynomialAlgebra(Kx);

f:=(x+&+[p^i:i in [0..r]])^n+p^k;
print"f",f;
return FunctionField(f);

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Ampnk(Fq::FldFin,p::RngUPolElt,n::RngIntElt,k::RngIntElt)->FldFun
{}

Fqt:=Parent(p);

t:=Fqt.1;
Kx<T> := RationalFunctionField(Fq);

KxT<x> := PolynomialAlgebra(Kx);

f:=(&*[(x+t*j)^n +t*p^k: j in Fq])+t*p^(n*k*#Fq);
print"f",f;
return FunctionField(f);

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Bpk(Fq::FldFin,p::RngUPolElt,k::RngIntElt)->FldFun
{}

Fqt:=Parent(p);

t:=Fqt.1;
Kx<T> := RationalFunctionField(Fq);

KxT<x> := PolynomialAlgebra(Kx);

f:=(x^2-2*x+4)^3+p^k;
print"f",f;
return FunctionField(f);

end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Cpk(Fq::FldFin,p::RngUPolElt,k::RngIntElt)->FldFun
{}

Fqt:=Parent(p);

t:=Fqt.1;
Kx<T> := RationalFunctionField(Fq);

KxT<x> := PolynomialAlgebra(Kx);

f:=((x^6+4*p*x^3+3*p^2*x^2+4*p^2)^2+p^6)^3+p^k;
print"f",f;
return FunctionField(f);

end intrinsic;


///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Dlpnk(Fq::FldFin,p::RngUPolElt,n::RngIntElt,l::RngIntElt,k::RngIntElt)->FldFun
{}

Fqt:=Parent(p);

t:=Fqt.1;
Kx<T> := RationalFunctionField(Fq);

KxT<x> := PolynomialAlgebra(Kx);

f:=&+[x^i:i in [0..l-1]]^n+p^k;
print"f",f;
return FunctionField(f);

end intrinsic;



///////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////

intrinsic Epk(p::RngUPolElt,k::RngIntElt)->FldFun
{}

Fqt:=Parent(p);

t:=Fqt.1;
Kx<T> := RationalFunctionField(BaseRing(Fqt));

KxT<x> := PolynomialAlgebra(Kx);


E1:=x^2+t;
E2:=E1^2+(p-1)*p^3*x;
E3:=E2^3+p^11;
E4:=E3^3+p^29*x*E2;
E5:=E4^2+(p-1)*p^42*x*E1*E3^2;
E6:=E5^2+p^88*x*E3*E4;
E7:=E6^3+p^295*E2*E4*E5;
E8:=E7^2+(p-1)*p^632*x*E1*E2^2*E3^3*E6;

L:=[E1,E2,E3,E4,E5,E6,E7,E8];
print"f:=",L[k];
return FunctionField(L[k]);

end intrinsic;
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic DualBasis(B::SeqEnum)->SeqEnum
{Computes the basis Bprime, which is orthornormal wrt the euclidean scalarproduct}

F:=Parent(B[1]);
n:=Degree(F);
K:=BaseField(F);
M:=Matrix([Eltseq(i):i in B]);
solutions:=[];
zero:=[K!0:i in [1..n]];
for i in [1..n] do
temp:=zero;
temp[i]:=1;
ss:=Solution(M,Vector(temp));
Append(~solutions,Eltseq(ss));

end for;


return [F!i:i in solutions];

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic TransPlace(P::PlcFunElt)->SeqEnum
{Uebersetzt Places in Magma setting in mein setting}

F:=FunctionField(P);

p,pi:=TwoGenerators(P);
d:=Deg(BaseField(F)!p);

if d gt 0 then
p:=PolynomialRing(ConstantField(F))!p;
_, _ := Montes(F,p);

for i in F`PrimeIdeals[p] do

	if PValuation(pi,i) gt 0 then
	
		return i;
	
	end if;

end for;

else

for j in PlacesAtInfinity(F) do

	if PValuation(pi,j) gt 0 then
	
		return j;
	
	end if;

end for;
 
end if; 
end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic RandomDivisorOO(F::FldFun,d::RngIntElt,l::RngIntElt,m::RngIntElt,r::RngIntElt)->SeqEnum
{Produziert "zufÃ¤lligen" Divisor, wobei d Stellegroesse ist, l=[k_0:k], m=#Supp, r= Koeffizienten groesse}

inf:=InfinitePlaces(F);

PlacesList:=[RandomPlace(F,Random([l*j:j in [1..d]])):i in [1..m] ]cat inf;
Coeffs:=[Random([-r..r]):i in [1..m+#inf] ];

Dmagma:=[];
Dicke:=[];
for i in [1..m+#inf] do

Append(~Dmagma,Coeffs[i]*PlacesList[i]);
Append(~Dicke,Coeffs[i]*Divisor(TransPlace(PlacesList[i])));
end for;
return &+Dmagma,&+Dicke;

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/*intrinsic RandomDivisorM(F::FldFun,d::RngIntElt,l::RngIntElt,m::RngIntElt,r::RngIntElt)->SeqEnum
{Produziert "zufÃ¤lligen" Divisor, wobei d Stellegroesse ist, l=[k_0:k], m=#Supp, r= Koeffizienten groesse}

inf:=InfinitePlaces(F);

PlacesList:=[RandomPlace(F,Random([l*j:j in [1..d]])):i in [1..m] ]cat inf;
Coeffs:=[Random([-r..r]):i in [1..m+#inf] ];
Heightt:=&+[Degree(PlacesList[i])*Abs(Coeffs[i]): i in[1..m+#inf] ];
Dmagma:=[];
for i in [1..m+#inf] do
MaxDegPlace:=Maximum([Degree(i):i in PlacesList]);
Append(~Dmagma,Coeffs[i]*PlacesList[i]);
end for;
return &+Dmagma,Heightt,MaxDegPlace;

end intrinsic;
*/
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic RandomDivisorM(F::FldFun,d::RngIntElt,l::RngIntElt,m::RngIntElt,r::RngIntElt)->SeqEnum
{Produziert "zufÃ¤lligen" Divisor, wobei d Stellegroesse ist, l=[k_0:k], m=#Supp, r= Koeffizienten groesse}

inf:=InfinitePlaces(F);
K:=BaseField(F);
Fpt:=PolynomialRing(ConstantField(F));
PlacesList:=[];Coeffs:=[];
for i in [1..m] do

	a,b:=Support(PrincipalDivisor(K!RandomPrimePolynomial(Fpt,Random([l*j:j in [1..d]]))));
	Append(~PlacesList,Random(Decomposition(F,a[2])));
	Append(~Coeffs,Random([-r..r]));
end for;
MaxDegPlace:=Maximum([Degree(i):i in PlacesList]);

PlacesList:=PlacesList cat inf;
Coeffs:=Coeffs cat [Random([-r..r]):i in [1..#inf] ];

Heightt:=&+[Degree(PlacesList[i])*Abs(Coeffs[i]): i in[1..m+#inf] ];
Dmagma:=[];
for i in [1..m+#inf] do

Append(~Dmagma,Coeffs[i]*PlacesList[i]);
end for;
return &+Dmagma,Heightt,MaxDegPlace;

end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

intrinsic RandomDivisorBoundM(F::FldFun,d::RngIntElt,l::RngIntElt,m::RngIntElt,r::RngIntElt)->SeqEnum
{Produziert "zufÃ¤lligen" Divisor, wobei d Stellegroesse ist, l=[k_0:k], m=#Supp, r= Koeffizienten groesse}

inf:=[];
tttmmpp:=InfinitePlaces(F);


K:=BaseField(F);
Fpt:=PolynomialRing(ConstantField(F));
PlacesList:=[];Coeffs:=[];

q:=#ConstantField(F);	g:=GENUS(F);
bound:=Maximum([Ceiling(2*Log(q,4*g-2)),Ceiling(2*Log(q,2*g))+1]);


for i in tttmmpp do
	if Degree(i) le bound then
	
	Append(~inf,i);
	end if;

end for;

print"bound",bound;
for i in [1..m] do

	a,b:=Support(PrincipalDivisor(K!RandomPrimePolynomial(Fpt,Random([l*j:j in [1..d]]))));
	rr:=Random([-r..r]);
	if not rr eq 0 then
		P:=Random(Decomposition(F,a[2]));
		if Degree(P) le bound then
			Append(~PlacesList,P);
			Append(~Coeffs,rr);
		end if;	
	end if;	
end for;



if #PlacesList eq 0 then 
return PrincipalDivisor(F!1),0,0;

print"is wohl d zu groÃŸ keule"; end if;



PlacesList:=PlacesList cat inf;
MaxDegPlace:=Maximum([Degree(i):i in PlacesList]);

Coeffs:=Coeffs cat [Random([-r..r]):i in [1..#inf] ];
Heightt:=&+[Degree(PlacesList[i])*Abs(Coeffs[i]): i in [1..#PlacesList] ];
Dmagma:=[];
for i in [1..#PlacesList] do

Append(~Dmagma,Coeffs[i]*PlacesList[i]);
end for;


return &+Dmagma,Heightt,MaxDegPlace;

end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////
//												//
//		Riemann-Roch improvement				//		
//												//	
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////


intrinsic Eq(D1::Rec ,D2:: Rec)-> BoolElt
{}
if  D1`FiniteIdeal eq  D2`FiniteIdeal and D1`InfiniteIdeal eq D2`InfiniteIdeal then
	return true;
else
 return false;
end if;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
intrinsic RRSpace1(D::Rec)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

tt1:=Realtime();
Ifin:=(D`FiniteIdeal)^-1;	Iinf:=(D`InfiniteIdeal)^-1;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F)); t:=A.1;

//if DEGREE(D) lt 0 then return [],[F!0],0,[],[0]; end if;

//////////////////////////Producing bases/////////////////////////
Bfin,finitefac:=IdealBaseRR(Ifin);
_, _ := Montes(F2, t);

	Binf,_,_,_,_,infex:=pBasisRR(Iinf,t:Reduced:=false);
	
wholefac:=finitefac;	
Bprime:=[TransMap(i,F):i in Binf];
InfPrimes:=PlacesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;


M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);	M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);
Mhelp:=M2^(-1);
T:=M1*Mhelp;
print"Initialisierungen dauerte x sec mit x=",Realtime()-tt1;
tt2:=Realtime();

	RedT,SuccMin:=ReductionAlgorithm(T);
print"Reduction dauerte x sec mit x=",Realtime()-tt2;
SuccMin:=[i-infex-Deg(K!finitefac):i in SuccMin];
redbasis:=[ &+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
print"nacher SuccMin",SuccMin;

return RedT,M1,Mhelp,SuccMin,redbasis;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
intrinsic RRSpaceletzteversion(D::Rec:Reduced:=false)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

tt1:=Realtime();
Ifin:=(D`FiniteIdeal)^-1;	Iinf:=(D`InfiniteIdeal)^-1;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F)); t:=A.1;
shift:=0;
//if DEGREE(D) lt 0 then return [],[F!0],0,[],[0]; end if;
print"step1";
//////////////////////////Producing bases/////////////////////////


Bfin,finitefac:=IdealBaseRR(Ifin);
_, _ := Montes(F2,t);
print"step2";
InfPrimes:=PlacesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;
print"step2.2";
if Reduced eq true then
	Binf,_,_,_,_,infex:=pBasisRR(Iinf,t:Reduced:=true);	
	for i in Binf do
		Append(~Values,-Minimum([   ( PValuation(i,PlacesAtInfinity(F)[j]) -Expo[j]   )/Es[j]:j in [1..#Es]])-infex );
	end for;
	print"Signature=",Values;
else
	Binf,_,_,_,_,infex:=pBasisRR(Iinf,t);
end if;
print"step3";
Bprime:=[TransMap(i,F):i in Binf];
print"step33.1";
M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);
	M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);
print"step33.2";ttt:=Realtime();
Mhelp:=M2^(-1);
print"step33.3",Realtime()-ttt;ttt:=Realtime();
T:=M1*Mhelp;print"sads,",Realtime()-ttt;ttt:=Realtime();
print"Initialisierungen dauerte x sec mit x=",Realtime()-tt1;
tt2:=Realtime();
print"step4";
if Reduced eq true then
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T,Values);
else
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T);
end if;	
print"Reduction dauerte x sec mit x=",Realtime()-tt2;
print"succ min=",SuccMin;
tt2:=Realtime();
SuccMin:=[i+infex+Deg(K!finitefac):i in SuccMin];
if NumberOfRedSteps eq 0 then
	redbasis:=Bfin;
else	
	redbasis:=[1/finitefac *&+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
end if;	
print"succmin ende=",[Ceiling(i):i in SuccMin];Realtime()-tt2;
return redbasis,SuccMin,RedT;

end intrinsic;


/////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
 
 //////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
intrinsic RRSpace(D::Rec:Reduced:=false)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

tt1:=Realtime();
Ifin:=(D`FiniteIdeal)^-1;	Iinf:=(D`InfiniteIdeal)^-1;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F)); t:=A.1;
shift:=0;
//if DEGREE(D) lt 0 then return [],[F!0],0,[],[0]; end if;
//////////////////////////Producing bases/////////////////////////


Bfin,finitefac:=IdealBaseRR(Ifin);
_, _ := Montes(F2,t);
InfPrimes:=PlacesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;
if Reduced eq true then
	Binf,Values,_,_,_,infex,Maxep:=pBasisRRTEST(Iinf,t:Reduced:=true);	
	print"Signature=",Values,Maxep;
else
	Binf,_,_,_,_,infex:=pBasisRR(Iinf,t);
end if;
Bprime:=[TransMap(i,F):i in Binf];
M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);
	M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);

if Reduced eq true then
	denmax:=K!Sort([Denominator(i):i in Bprime])[n];
	Mhelp:=Inverse(M2,denmax);
else
	Mhelp:=M2^(-1);
end if;
T:=M1*Mhelp;
print"Initialisierungen dauerte x sec mit x=",Realtime()-tt1;
tt2:=Realtime();
if Reduced eq true then
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T,Values);
else
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm(T);
end if;	
print"Reduction dauerte x sec mit x=",Realtime()-tt2;
print"succ min=",SuccMin;
tt2:=Realtime();
SuccMin:=[i+infex+Deg(K!finitefac):i in SuccMin];
if NumberOfRedSteps eq 0 then
	redbasis:=Bfin;
else	
	redbasis:=[1/finitefac *&+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
end if;	
print"succmin ende=",[Ceiling(i):i in SuccMin];Realtime()-tt2;
return redbasis,SuccMin,RedT;

end intrinsic;


/////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
 
intrinsic RRSpaceAlt(D::Rec:Reduced:=false)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}

tt1:=Realtime();
Ifin:=(D`FiniteIdeal)^-1;	Iinf:=(D`InfiniteIdeal)^-1;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F)); t:=A.1;
shift:=0;
//if DEGREE(D) lt 0 then return [],[F!0],0,[],[0]; end if;

//////////////////////////Producing bases/////////////////////////


Bfin,finitefac:=IdealBaseRR(Ifin);
_, _ := Montes(F2,t);
InfPrimes:=PlacesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;

if Reduced eq true then
	Binf,_,_,_,_,infex:=pBasisRR(Iinf,t:Reduced:=true);	
	for i in Binf do
		Append(~Values,-Minimum([   ( PValuation(i,InfPrimes[j]) -Expo[j]   )/Es[j]:j in [1..#Es]])-infex );
	end for;
	print"Signature=",Values;
else
	Binf,_,_,_,_,infex:=pBasisRR(Iinf,t);
end if;

Bprime:=[TransMap(i,F):i in Binf];

M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfin]);	M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);
Mhelp:=M2^(-1);
T:=M1*Mhelp;
print"Initialisierungen dauerte x sec mit x=",Realtime()-tt1;
tt2:=Realtime();

if Reduced eq true then
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm2(T,Values);
else
	RedT,SuccMin,NumberOfRedSteps:=ReductionAlgorithm2(T);
end if;	
print"Reduction dauerte x sec mit x=",Realtime()-tt2;
print"succ min=",SuccMin;
tt2:=Realtime();
SuccMin:=[i+infex+Deg(K!finitefac):i in SuccMin];
if NumberOfRedSteps eq 0 then
	redbasis:=Bfin;
else	
	redbasis:=[1/finitefac *&+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
end if;	
print"succmin ende=",[Ceiling(i):i in SuccMin];Realtime()-tt2;
return redbasis,SuccMin,RedT;

end intrinsic;



/*//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 
intrinsic RRSpace(D::Rec:semi:=true)->SeqEnum
{The Riemann-Roch-Space of the Divisor I^-1*(P_1^(-Expo[1])*...*P_(#Expo)^(-Expo[#Expo])), where P_i are the places at infinity}
tt1:=Realtime();
Ifin:=(D`FiniteIdeal)^-1;	Iinf:=(D`InfiniteIdeal)^-1;
F:=Ifin`Parent;	  n:=Degree(F);
F2:=Iinf`Parent;
print"Step 1";
K:=BaseField(F);	A:=PolynomialRing(ConstantField(F)); t:=A.1;

if DEGREE(D) lt 0 then return [],[F!0],0,[],[0]; end if;

//////////////////////////Producing bases/////////////////////////
Bfin:=IdealBasis(Ifin);
print"Step 2";
GCDDenominator:=BaseField(F)!Denominator(Bfin[n]); r:=Deg(GCDDenominator);
Bfintmp:=[GCDDenominator*i:i in Bfin];
print"Step 3";
MontesH(F2, t : Basis:=true);
Binf:=pHermiteBasis(Iinf,t);
Bprime:=[TransMap(i,F):i in Binf];
print"Step 4";
InfPrimes:=PlacesAtInfinity(F);	 Es:=[i`e:i in InfPrimes];	Values:=[]; Expo:=[0:i in [1..#InfPrimes]];
for jj in Iinf`Factorization do
	Expo[jj[2]]:=jj[3];
end for;

for i in Binf do
	Append(~Values,-Minimum([   ( PValuation(i,InfPrimes[j]) -Expo[j]   )/Es[j]:j in [1..#Es]]));
end for;
//print"Signature=",Values;
M1:=Matrix(K,n,&cat [Eltseq(i):i in Bfintmp]);	M2:=Matrix(K,n,&cat [Eltseq(i):i in Bprime]);
T:=M1*M2^(-1);
print"Initialisierungen dauerte x sec mit x=",Realtime()-tt1;
tt2:=Realtime();
if not semi then
	RedT,SuccMin:=ReductionAlgorithm(T,Values);
else
	RedT,SuccMin:=ReductionAlgorithm(T);
end if;
SuccMin:=[i-r:i in SuccMin];
/*print"SuccMin",SuccMin,GCDDenominator;
print"\n \n SizeBound:",SuccMin[#SuccMin]-SuccMin[1],Ceiling(SuccMin[#SuccMin])-Ceiling(SuccMin[1]);
print"\n \n";
print"\n \n SuccMin_0:",[jj-SuccMin[1]:jj in SuccMin],&+[jj-SuccMin[1]:jj in SuccMin];
print"\n \n";
print"\n \n SuccMin_0 integer:",[jj-Ceiling(SuccMin[1]):jj in SuccMin],&+[jj-Ceiling(SuccMin[1]):jj in SuccMin];
print"\n \n";
print"Reduction dauerte x sec mit x=",Realtime()-tt2;

redbasis:=[1/GCDDenominator* &+[ Bprime[j]*RedT[i,j] :j in [1..n]]  :i in [1..n]];
basis:=[];	dimlist:=[];	templist:=[];	Dim:=0;
for i in [1..n] do 
//	Append(~templist,Floor(-SuccMin[i])+1);
	if Floor(-SuccMin[i]) ge 0 then 
		Append(~dimlist,-Ceiling(SuccMin[i])+1);
	end if;
end for;

if #dimlist eq 0 then
	dim:=0;
else
	dim:=&+dimlist;
end if;
return redbasis,dimlist,dim,VectorSpace(ConstantField(F),dim),SuccMin;

end intrinsic;*/



 //////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
 //////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



intrinsic RandomPl(F::FldFun,d::RngIntElt)->SeqEnum
{Produziert "zufÃ¤llige" Stelle, Ã¼ber einem Ã¼ber p(t) mit deg p = d }

p:=RandomPrimePolynomial(PolynomialRing(ConstantField(BaseField(F))),d);
_, _ := Montes(F,p);
P:=F`PrimeIdeals[p,Random([1..#F`PrimeIdeals[p]])];
return P;

end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic RandomDivisor(F::FldFun,d::RngIntElt,l::RngIntElt,m::RngIntElt,r::RngIntElt)->SeqEnum
{Produziert "zufÃ¤lligen" Divisor, wobei d Stellegroesse ist, l=[k_0:k], m=#Supp, r= Koeffizienten groesse}

PlacesList:=[RandomPl(F,Random([l*j:j in [1..d]])):i in [1..m] ]cat PlacesAtInfinity(F);
Coeffs:=[Random([-r..r]):i in [1..m+#PlacesAtInfinity(F)] ];
Dicke:=[];
for i in [1..m+#PlacesAtInfinity(F)] do
	if not Coeffs[i] eq 0 then
	Append(~Dicke,Coeffs[i]*Divisor(PlacesList[i]^1));
	end if;	
end for;
return &+Dicke;

end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic RandomDivisorBound(F::FldFun,d::RngIntElt,l::RngIntElt,m::RngIntElt,r::RngIntElt)->SeqEnum
{Produziert "zufÃ¤lligen" Divisor, wobei d Stellegroesse ist, l=[k_0:k], m=#Supp, r= Koeffizienten groesse}

PlacesList:=[RandomPl(F,Random([l*j:j in [1..d]])):i in [1..m] ]cat PlacesAtInfinity(F);
Coeffs:=[Random([-r..r]):i in [1..m+#PlacesAtInfinity(F)] ];
Dicke:=[];

q:=#ConstantField(F);	g:=GENUS(F);
if g eq 0 then 
	bound:=5;
else
	bound:=Maximum([Ceiling(2*Log(q,4*g-2)),Ceiling(2*Log(q,2*g))+1]);
end if;


for i in [1..m+#PlacesAtInfinity(F)] do
	dd:=Degree(PlacesList[i]);
	if not Coeffs[i] eq 0 and dd le bound then
	Append(~Dicke,Coeffs[i]*Divisor(PlacesList[i]^1));
	end if;	
end for;

if #Dicke eq 0 then
	print"d zu groÃŸ"; 
	Dicke:=Divisor(F!1);
	return Dicke,0;
else
	return &+Dicke,1;
end if;

end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Normalization(F::FldFun)->FldFun
{Bekommt FunktionenkÃ¶rper mit definieirenden Polynom f und gibt definierendes Polnynom 
f' aus, wobei f' normiert ist und Koeffizienten in k[t] hat}

f:=DefiningPolynomial(F);
CoeffList:=Eltseq(f);
NewCoeff:=[Parent(CoeffList[1])!1];
alpha:=LCM([Denominator(i):i in CoeffList]);
Nennerfrei:=Reverse([alpha*i :i in CoeffList]);
an:=Nennerfrei[1];
for i in [2..#Nennerfrei] do

	Append(~NewCoeff,an^(i-2)*Nennerfrei[i]);

end for;

return FunctionField(Parent(f)!Reverse(NewCoeff));



end intrinsic;


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Normalization(f::RngUPolElt)->FldFun
{Bekommt definieirendes Polynom f und gibt definierendes Polnynom 
f' aus, wobei f' normiert ist und Koeffizienten in k[t] hat}

CoeffList:=Eltseq(f);
NewCoeff:=[Parent(CoeffList[1])!1];
alpha:=LCM([Denominator(i):i in CoeffList]);
Nennerfrei:=Reverse([alpha*i :i in CoeffList]);
an:=Nennerfrei[1];
for i in [2..#Nennerfrei] do

	Append(~NewCoeff,an^(i-2)*Nennerfrei[i]);

end for;

return Parent(f)!Reverse(NewCoeff);

end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic PoleDiv(a::FldFunElt)->FldFun
{Bestimmt Poldivisor von a}

F:=Parent(a); kt:=PolynomialRing(ConstantField(F));

if a in ConstantField(F) then return Divisor(F!1); end if;
den:=kt!Denominator(a);	num:=Numerator(a);
primes:=Factorization(den);

FintePoles:=[];
for i in primes do

    _, _ := Montes(F,i[1]);
	for j in F`PrimeIdeals[i[1]] do
		tmp:=PValuation(num,j);
		if tmp lt j`e*i[2] then
			Append(~FintePoles,j^(j`e*i[2]-tmp));
		end if;
	end for;

end for;

InfinitePol:=[];

for i in PlacesAtInfinity(F) do

	tmp:=PValuation(num,i);
	if tmp lt -i`e*Degree(den) then
		Append(~InfinitePol,i^(-i`e*Degree(den)-tmp));
	end if;
end for;
if #FintePoles eq 0 or #InfinitePol eq 0 then 
	if #FintePoles eq 0 and #InfinitePol eq 0 then
		return Divisor(F!1);
	end if;
	
	if #FintePoles eq 0 then
		return Divisor(&*InfinitePol);
	else
		return Divisor(&*FintePoles);
	end if;
end if;

return Divisor(&*FintePoles)+Divisor(&*InfinitePol);



end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic ZeroDiv(a::FldFunElt)->FldFun
{Bestimmt Nulldivisor von a}


return PoleDiv(1/a);



end intrinsic;



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic PrincipalDiv(a::FldFunElt)->FldFun
{Bestimmt PrincipalDivisor von a}

F:=Parent(a); kt:=PolynomialRing(ConstantField(F));

if a in ConstantField(F) then return Divisor(F!1); end if;
den:=kt!Denominator(a);	num:=Numerator(a);
primes:=Factorization(den);

FintePoles:=[];
for i in primes do

    _, _ := Montes(F,i[1]);
	for j in F`PrimeIdeals[i[1]] do
		tmp:=PValuation(num,j);
		if not tmp eq j`e*i[2] then
			Append(~FintePoles,j^(tmp-j`e*i[2]));
		end if;
	end for;

end for;

InfinitePoles:=[];

for i in PlacesAtInfinity(F) do

	tmp:=PValuation(num,i);
	if not tmp eq -i`e*Degree(den) then
		Append(~InfinitePoles,i^(tmp+i`e*Degree(den)));
	end if;
end for;

	if not #InfinitePoles eq 0 then
		Dinf:=Divisor(&*InfinitePoles);
	else
		Dinf:= Divisor(F!1);
	end if;

a:=1/a;

den:=kt!Denominator(a);	num:=Numerator(a);
oldprimes:=[i[1]:i in primes];
primes:=Factorization(den);

for i in primes do
	if not i[1] in oldprimes then
        _, _ := Montes(F,i[1]);
		for j in F`PrimeIdeals[i[1]] do
			tmp:=PValuation(num,j);
			if not tmp eq j`e*i[2] then
				Append(~FintePoles,j^(j`e*i[2]-tmp));
			end if;
		end for;
	end if;
end for;

	if not #FintePoles eq 0 then
		Dfin:=Divisor(&*FintePoles);
	else
		Dfin:= Divisor(F!1);
	end if; 

return Dinf+Dfin;



end intrinsic;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


intrinsic Random(F:: FldFun,d:: RngIntElt)->RngUPolElt
{Determines random element in F with voefficiants of degree less or equal d-1}

R:=PolynomialRing(ConstantField(F));
a:=F![Random(R,Random([0..d])):i in [1..Degree(F)]];
b:=F!(Random(R,Random([0..d])));
if a eq 0 then a:=1;end if;
if b eq 0 then b:=b+1;end if;
return a/b; 

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Random(R:: RngUPol,d:: RngIntElt)->RngUPolElt
{Determines random poylinomial in R with degree lesss or equal d-1}

Fp:=BaseRing(R);

return R!Eltseq(Random(VectorSpace(Fp,d))); 

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

/////////////////////SFL/////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



/////////////////////////////////////////////////////////////////////////////////////
/*//////////////////////////////////////////

intrinsic SFL(~type::SeqEnum,slope::RngIntElt)
{in type[1]`sfl and type[1]`Phiadic we stored relevant data. The aim is type[#type]`slope>=slope}

ord:=#type;
if type[ord]`slope ge slope then
    return;
end if;

if type[1]`sfl[3] eq 0 then
    SFLInitialize(~type);
end if;

p:=type[1]`Prime;
exponent:=type[1]`sfl[1];
nu:=type[1]`sfl[2];
x0prec:=type[1]`sfl[3];
x0num:=type[1]`Phiadic[4];
x0den:=type[1]`sfl[4];
e:=type[ord]`prode;
h:=type[ord]`h-type[ord]`cuttingslope;
lasth:=slope-type[ord]`cuttingslope;
V:=type[ord]`V+type[ord]`cuttingslope;

Zp:=pAdicRing(p);
piZp:=UniformizingElement(Zp);
Zp`DefaultPrecision:=nu+exponent+Ceiling((V+lasth)/e);
PolZp:=AdaptPrecision(Zp,type[1]`Phiadic[5],type[1]`ProdQuots);	
PsinumZp:=AdaptPrecision(Zp,type[1]`Phiadic[3],type[1]`ProdQuotsVals);

path:=PathOfPrecisions(lasth,h);
shortpath:=PathOfPrecisions(h,x0prec);

Zp`DefaultPrecision:=nu+exponent+Ceiling(h/e);
a1:=PolynomialRing(Zp)!type[1]`Phiadic[2];

zq:=quo<Zp|piZp^(nu+exponent+Ceiling((V+path[2])/e))>;
zqt<t>:=PolynomialRing(zq);
phi:=zqt!type[ord]`Phi;
Psinum:= zqt!PsinumZp;
A0num, A0den := Cancel((zqt!type[1]`Phiadic[1]*Psinum) mod phi,nu);
A1num, A1den := Cancel((zqt!a1*Psinum) mod phi,nu);

for i in [2..#shortpath] do
    lowprecision:=A1den+2*x0den+Ceiling(shortpath[i]/e);
    Inversionloop([* A1num,A1den *],~x0num,~x0den,phi,lowprecision,Zp);
end for;  

Anum, Aden := Cancel((A0num*zqt!x0num) mod phi, x0den);
phi:=phi+Anum;
//print "primera h", testh(type,phi);

for i in [2..#path-1] do
    zq:=quo<Zp|piZp^(nu+exponent+Ceiling((V+path[i+1])/e))>;
    zqt<t>:=PolynomialRing(zq);
    phi:=zqt!phi;
    Psinum:= zqt!PsinumZp;
    qq,c0:=Quotrem(zqt!PolZp,phi);
    c1:=qq mod phi;
    C0num,C0den := Cancel((c0*Psinum) mod phi,nu);
    C1num,C1den := Cancel((c1*Psinum) mod phi,nu);
    lowprecision:=C1den+2*x0den+Ceiling(path[i]/e);
    Inversionloop([* C1num,C1den *],~x0num,~x0den,phi,lowprecision,Zp);
    Cnum,Cden:=Cancel((C0num*zqt!x0num) mod phi, x0den);
    phi:=phi+Cnum;
//print "nova h", i, testh(type,phi);
end for;

type[1]`sfl[3]:=Max([h,path[#path-1]]);
type[ord]`Phi:=PolynomialRing(Integers())!phi;
type[1]`Phiadic[4]:=x0num;
type[1]`sfl[4]:=x0den;
end intrinsic;

///////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////*/

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

intrinsic PathOfPrecisions(n,h) -> SeqEnum
{}

q:=n;
precs:=[n];
while q gt h do
    q,a:=Quotrem(q,2);
    q+:=a;
    Append(~precs,q);
end while;
return Reverse(precs);
end intrinsic;


