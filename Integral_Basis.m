//////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////
//    Integral_basis Package 
//    Jens-Dietrich Bauch 
//    June 2015
//    (C) 2015 Jens-Dietrich Bauch
//    Distributed under the terms of the GNU General Public License 
//    http://www.gnu.org/licenses/gpl.txt  
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
//    Many routines are translations from the package +Ideals.m
//	  The package is implemented for Magma V2.21-1	
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
// The routine MaximalOrderComp(F) computes for a function field F a basis of the    
//	finite maximal order. For MaximalOrderComp(F:Multiplier:=false) the quotient method is used
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////



declare verbose montestalk, 4;
declare verbose hds, 4;
declare attributes FldFun: 
pBasis, FactorizedDiscriminant, FactorizedPrimes,Index,
LocalIndex, PrimeIdeals, TreesIntervals, BasisExp;
		
		
AddAttribute(FldFun,"Index");

//Records for places and Divisors

PlaceRecord:=recformat<
    FiniteIdeal: Rec, 
    InfiniteIdeal: Rec,
    FactorizationString:  MonStgElt,
    SuccessiveMinima:	SeqEnum,
    ApproximatedSuccessiveMinima:	SeqEnum,
	RedBasis:	SeqEnum,
	SRedBasis:	SeqEnum,
	Basis:	SeqEnum,
	SmallDiv:	Rec,
	r:	RngIntElt,
	a:	FldFunElt,	
	IsPrincipal:	BoolElt
    >;

//Records for montes algorithm
				
PrimeIdealRecord:=recformat<
Type: SeqEnum,
Parent: FldFun,
Pol: RngUPolElt,
PolynomialGenerator: RngUPolElt,
e: Integers(),
f: Integers(),
exponent: RngIntElt,
LocalGenerator: FldFunElt,
LogLG: ModTupRngElt,
Generator: FldFunElt,
CrossedValues: SeqEnum,
OkutsuBasis: SeqEnum,
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
PolynomialGenerator: RngUPolElt,
Generator: FldFunElt,
Basis: SeqEnum,
PBasis: SeqEnum,            /* only for prime ideals */
PBasisVals: SeqEnum,        /* only for prime ideals */
Position: Integers(),       /* only for prime ideals */  
Type: SeqEnum,              /* only for prime ideals */
e: Integers(),              /* only for prime ideals */
f: Integers(),              /* only for prime ideals */
exponent: RngIntElt,       /* only for prime ideals */
LocalGenerator: FldNumElt,  /* only for prime ideals */
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
Fq: Fld,
FqY:RngUPol,
z: FldElt,
omega: Integers(),
cuttingslope: Integers(),
Refinements: List, 
alpha: Integers(),
logPi: ModTupRngElt,
logPhi: ModTupRngElt,
logGamma: ModTupRngElt,
PolynomialGenerator : RngUPolElt,     /* only in level 1 */   // should be Prime!!
Pol : RngUPolElt,       /* only in level 1 */
ProdQuots: SeqEnum,     /* only in level 1 */
ProdQuotsVals: SeqEnum, /* only in level 1 */
Phiadic: SeqEnum,       /* only in level 1 */
sfl: SeqEnum,            /* only in level 1 */
Redmap: Map,
map: Map
>;



OkutsuFrameLevel := recformat<
    degree: RngIntElt,
    index: RngIntElt,
    values: List,
    polynomial: RngUPolElt
>;


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

intrinsic Deg(z::FldFunElt)->RngIntElt
{}
//if z eq 0 then return -Infinity();end if; // ist vielleicht noch mal hilfreich
F := Parent(z);	A<t> := PolynomialRing(ConstantField(F)); Ax := PolynomialRing(A);


return Degree(Ax!Eltseq(Numerator(z)));

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Evaluate(F::FldFun,z::RngUPolElt)->FldFunElt
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

intrinsic Numerator(z:: FldFunElt)->FldFunElt
{Determines the Nominator of a FldFunElt z}

	return Parent(z)!Numerator(z,EquationOrderFinite(Parent(z)));

end intrinsic;




//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



intrinsic Denominator(z:: FldFunElt)->FldFunElt
{Determines the denominator of z}

	return Parent(z)!Denominator(z,EquationOrderFinite(Parent(z)));

end intrinsic;



//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Degree(I::Rec)->RngIntElt
{computes the Degree of a prime ideal record}



	K:=I`Parent;
	if IsFinite(ConstantField(K)) then
		deg:= Integers()!(Degree(I`Type[#I`Type]`Fq)/Degree(ConstantField(K)));
	else
		deg:=Degree(I`Type[#I`Type]`Fq);
	end if;
	return deg;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Montes(K::FldFun,p::RngUPolElt: Basis:=false)
{}
require IsPrime(p): "First argument must be a prime polynomial";
Rt:=Parent(p);
Rxt<x>:=PolynomialRing(Rt);
RXT<T>:=BaseField(K);
Pol:=Rxt!DefiningPolynomial(K);
//require (CoefficientRing(Pol) eq Integers() and IsMonic(Pol)): "Number Field must be defined by a monic integral polynomial";

if not assigned K`FactorizedPrimes then
    K`FactorizedPrimes:=[];
    K`PrimeIdeals:=AssociativeArray();
    K`LocalIndex:=AssociativeArray();
    K`TreesIntervals:=AssociativeArray();
    K`pBasis:=AssociativeArray();
	K`BasisExp:=AssociativeArray();
end if;    
if p in K`FactorizedPrimes and (not Basis or IsDefined(K`pBasis,p)) then
    return;
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
primeid:=rec<PrimeIdealRecord|Parent:=K,Pol:=Pol,PolynomialGenerator:=p>;

for k:=1 to #OMReprs do
    primeid`Position:=k;
    primeid`Type:=OMReprs[k];
    primeid`e:=OMReprs[k][#OMReprs[k]]`prode;
    primeid`f:=OMReprs[k][#OMReprs[k]]`prodf; 
    PrescribedValue(~OMReprs[k],1,~Psi,~logLG);
    primeid`LocalGenerator:=Evaluate(K,Psi)*RXT!p^logLG[1];
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
	
    K`pBasis[p]:=[Evaluate(BasisNums[k],K.1): k in [1..Degree(K)]];
    
     K`BasisExp[p] := [ Floor(x) : x in BasisDens ];
//    return [Evaluate(K,BasisNums[k]): k in [1..Degree(K)]],BasisDexp;
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
logPi:=Vector([1,0]), logPhi:=Vector([0,1]), PolynomialGenerator:=p, Pol:=Pol, Phiadic:=[Ktx!0,Ktx!0,Ktx!0,Ktx!0],
sfl:=[0,0,0,0]>;

level`Fq,level`map:=ResidueClassField(psi);
level`Redmap:=map;

if level`prodf gt 1 then  
 /*   mmm,nnn:=HasAttribute(level`Fq,"PowerPrinting");
    if mmm and nnn then 
	AssertAttribute(level`Fq, "PowerPrinting", false); 
    end if;*/
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

intrinsic PrescribedValue(~type,value,~Psi,~logpsi)
{if type is attached to the prime ideal P with Okutsu depth r, then logpsi=[a_0,...,a_r] 
and Psi=phi_1^a_1...phi_r^a_r, with v_P(p^a_0Psi(theta))=value}

Psi:=PolynomialRing(Parent(type[1]`PolynomialGenerator))!1;
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
	    tmp:=PolynomialRing(FPP)![map(ii):ii in Eltseq((dev 	div type[1]`PolynomialGenerator^height))];	
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

intrinsic Localize(alpha,p)->RngIntElt,RngIntElt,RngUPolElt
{output=den,exp,Pol such that alpha = (1/den)*Pol(theta)*p^exp, and den is coprime to p}

if alpha eq 0 then 
    return 1,0,PolynomialRing(Parent(p))!0;
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

intrinsic ConvertLogs(~type,log,~class)
{log[1] is not used. The product of all Phi_i^log[i] for i>0 should have integer value M.
The output is the class of this product divided by p^M }


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


intrinsic InitialeModRing(R::RngUPol,q::RngUPolElt)->RngUPol
{}
A:=CoefficientRing(R);
quot<tt>:=quo<A|q>;
R<xx>:=PolynomialRing(quot);
return R;
end intrinsic;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////


intrinsic PutModRing(RMod::RngUPol,g::RngUPolElt)->RngUPol
{}

k:=BaseRing(CoefficientRing(Parent(g)));
A:=PolynomialRing(k);
Amod:=CoefficientRing(RMod);
return RMod![Amod!(A!i):i in  Eltseq(g)];


end intrinsic;


///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

intrinsic ChangePrecMod(RMod::RngUPol,g::RngUPolElt)->RngUPol
{}
R:=BaseRing(RMod);
ll:=Eltseq(g);

return RMod![R!Eltseq(i):i in ll];


end intrinsic;

///////////////////////////////////////////////////////////////


intrinsic SFL(~type::SeqEnum,slope::RngIntElt)
{in type[1]`sfl and type[1]`Phiadic we stored relevant data. The aim is type[#type]`slope>=slope}
ord:=#type;
if type[ord]`slope ge slope then
    return;
end if;
tts:=Realtime();
if type[1]`sfl[3] eq 0 then
    SFLInitialize(~type);
end if;
p:=type[1]`PolynomialGenerator;
exponent:=type[1]`sfl[1];
nu:=type[1]`sfl[2];
x0prec:=type[1]`sfl[3];
x0num:=type[1]`Phiadic[4];
x0den:=type[1]`sfl[4];
e:=type[ord]`prode;
h:=type[ord]`h-type[ord]`cuttingslope;
lasth:=slope-type[ord]`cuttingslope;
V:=type[ord]`V+type[ord]`cuttingslope;
precision:=nu+exponent+Ceiling((V+lasth)/e);
piZp:=p;
p_prec:=p^precision;
PolZp_or:=type[1]`Pol;
Ax:=Parent(PolZp_or);
RMod:=InitialeModRing(Ax,p_prec);
PolZp_or:=PutModRing(RMod,PolZp_or);
PsinumZp:=PutModRing(RMod,type[1]`Phiadic[3] );
path:=PathOfPrecisions(lasth,h);
shortpath:=PathOfPrecisions(h,x0prec);
newprecision:=nu+exponent+Ceiling(h/e);

p_prec_new:=p^newprecision;
RMod:=InitialeModRing(Ax,p_prec_new);
a1:=PutModRing(RMod,type[1]`Phiadic[2] );

newprecision:=nu+exponent+Ceiling((V+path[2])/e);
p_prec_new:=p^newprecision;
RMod:=InitialeModRing(Ax,p_prec_new);
phi:=PutModRing(RMod,type[ord]`Phi );

Psinum:=PutModRing(RMod, PsinumZp);
ty_phad1:=PutModRing(RMod,type[1]`Phiadic[1]);
A0num, A0den := reduce(p,(ty_phad1*Psinum) mod phi,nu);
a1:=ChangePrecMod(RMod,a1);
Psinum:=ChangePrecMod(RMod,Psinum);
phi:=ChangePrecMod(RMod,phi);

A1num, A1den := reduce(p,(a1*Psinum) mod phi,nu);

for i in [2..#shortpath] do
    lowprecision:=A1den+2*x0den+Ceiling(shortpath[i]/e);
    Inversionloop(p,[* A1num,A1den *],~x0num,~x0den,phi,lowprecision);
end for;  

x0num:=PutModRing(RMod,x0num);
Anum, Aden := reduce(p,(A0num*x0num ) mod phi, x0den+A0den);
phi:=phi+Anum;

for i in [2..#path-1] do

    loopprec:=nu+exponent+Ceiling((V+path[i+1])/e);
    ploop:=p^loopprec;
    RMod:=InitialeModRing(Ax,ploop);
    phi:=ChangePrecMod(RMod,phi);

    Psinum:= ChangePrecMod(RMod,PsinumZp);
    PolZp:=ChangePrecMod(RMod,PolZp_or);
    qq,c0:=Quotrem(PolZp,phi);

    c1:=qq mod phi;
    C0num,C0den := reduce(p,(c0*Psinum ) mod phi,nu);
    C1num,C1den := reduce(p,(c1*Psinum) mod phi,nu);

    lowprecision:=C1den+2*x0den+Ceiling(path[i]/e);
    Inversionloop(p,[* C1num,C1den *],~x0num,~x0den,phi,lowprecision);
	x0num:=ChangePrecMod(RMod,x0num);
    Cnum,Cden:=reduce(p,(C0num*x0num) mod phi, x0den+C0den);

    phi:=phi+Cnum;

end for;

type[1]`sfl[3]:=Max([h,path[#path-1]]);
type[ord]`Phi:=Ax!phi;
type[1]`Phiadic[4]:=Ax!x0num;
type[1]`sfl[4]:=x0den;

end intrinsic;



//////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

intrinsic SFLInitialize(~type)
{}

p:=type[1]`PolynomialGenerator;
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


intrinsic Value(i,~type,pol,~devs,~val)
{Given a level i, a type and a polynomial pol, the output is:
devs=multiexpansion with respect to phi_1,...,phi_i-1 of the points in S_lambda_i-1(pol)
val=i-th valuation of pol w.r.t. type}

//PutInZ([*i,type,pol,devs,val*]);

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
	p:=type[1]`PolynomialGenerator;
	if p eq Parent(p).1 then 
		vallis:=[];
		for c in Coefficients(Parent(type[1]`Phi)!pol) do
			if not c eq 0 then
				tmp:=Eltseq(c);
				lol:=exists(u){y:y in [1.. #tmp]| not tmp[y] eq 0};
				Append(~vallis,u-1);
			end if;	
		end for;
		val:=Min(vallis);
	else
	    val:=Min([Valuation(c,p): c in Coefficients(Parent(type[1]`Phi)!pol)]);
    end if;
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

intrinsic IndexOfCoincidence(~t1,~t2,~i)
{the types must correspond to different prime ideals}

require t1[1]`PolynomialGenerator eq t2[1]`PolynomialGenerator: "types attached to different prime numbers";
if t1[1]`Phi mod t1[1]`PolynomialGenerator ne t2[1]`Phi mod t1[1]`PolynomialGenerator then 
    i:=0;
else
i:=1;
while t1[i]`Phi eq t2[i]`Phi and t1[i]`slope eq t2[i]`slope and t1[i]`psi eq t2[i]`psi do
    i+:=1;
end while;	
end if;

end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IndexOfCoincidence(t1::Rec, t2::Rec)-> RngIntElt
    { The index of coincidence of types t1 and t2. }

    i := 0;
    IndexOfCoincidence(~t1`Type, ~t2`Type, ~i);

    return i;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic IndexOfCoincidence(t1::SeqEnum, t2::SeqEnum)-> RngIntElt
    { }

    i := 0;
    IndexOfCoincidence(~t1, ~t2, ~i);

    return i;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

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

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////


intrinsic reduce(p,poly,den)->RngUPolElt,RngIntElt
{}

if poly eq 0 then
    return poly,0;
end if;
cancel:=Min([den,Min([Valuation(Parent(p)!a,p):a in Eltseq(poly)])]);
//print"cancel",poly,Parent(poly)!p^cancel;
num:=poly div CoefficientRing(Parent(poly))!p^cancel;

//ChangePrecision(~num,GetPrecision(Zp));
return num,den-cancel;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


intrinsic Inversionloop(p,A,~xnum,~xden,phi,precision)
{}

aden:=A[2];

Ax:=PolynomialRing(Parent(p));
RMod:=InitialeModRing(Ax,p^precision);

Phip:=ChangePrecMod(RMod,phi); 
anum:=ChangePrecMod(RMod,A[1]);
piq:=RMod!(Ax!p);
xnum :=PutModRing(RMod,xnum);
x1num,x1den:=reduce(p,(2*piq^(xden+aden)-((anum )*xnum)) mod Phip,xden+aden); // hier reduce durch reduce 2 ausgetauscht
xnum,xden:=reduce(p,((xnum*x1num)) mod Phip, xden+x1den); // hier reduce durch reduce 2 ausgetauscht
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


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



intrinsic UpdateLastLevel(~type,slope)
{}

ord:=#type;
precision:=Ceiling(	((type[ord]`V+Abs(slope))/type[ord]`prode+1));//ist nicht die richtige präzision
p:=type[1]`PolynomialGenerator;
p_prec:=p^precision;

Ax:=Parent(type[1]`Pol);
RMod:=InitialeModRing(Ax,p_prec);

pol:=PutModRing(RMod,type[1]`Pol);
phi:=PutModRing(RMod,type[#type]`Phi);
qq,a0:=Quotrem(pol,phi);
a0:=Ax!a0;

if a0 eq 0 then 
    type[#type]`slope:=Infinity();
else    
    type[1]`Phiadic[1]:=a0;
    type[1]`Phiadic[2]:=Ax!(qq mod phi);

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
    p:=type[1]`PolynomialGenerator;
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
    v1lift:=Min([Valuation(x,type[1]`PolynomialGenerator): x in Coefficients(lift)]);
    numlift:=lift div type[1]`PolynomialGenerator^v1lift;
    denlift:=expden-v1lift;
end if;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////

intrinsic LocalLift(class,P)->FldFunElt
{class should belong to the residue class field Z_K/P. 

The output is a lift to a P-integral element in K}

numlift:=0;
denlift:=0;
LocalLift(~P`Type,class,~numlift,~denlift);
return  Evaluate(P`Parent,numlift)/P`PolynomialGenerator^denlift;
end intrinsic;

///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////


intrinsic Construct(i,~type,respol,s,u,~Ppol)
{This routine constructs a polynomial Ppol with integer coefficients such that: 
deg Ppol<m_i+1 and y^nu*R_i(Ppol)(y)=respol(y), where nu=ord_y(respol).
The non-negative integers s,u are the coordinates of the left endpoint of a segment of slope -type[i]`slope supporting N_i(Ppol).
}

require i le #type: "the first input is too large";
require Degree(respol) lt type[i]`f: "the Degree of the 3rd argument is too large"; 
require u+s*type[i]`slope ge type[i]`f*(type[i]`e*type[i]`V+type[i]`h): "the point (s,u) is too low";
var:=type[i]`Phi^type[i]`e;
Ppol:=0;
if i eq 1 then
	height:=u-Degree(respol)*type[i]`h;
	p:=type[1]`PolynomialGenerator;
	mappitemp:=type[1]`Redmap;
	Ftemp:=Codomain(mappitemp);
	mappi:=mappitemp^(-1); 
    for a in Reverse(Coefficients(respol)) do
	lift:= PolynomialRing(Parent(p))![mappi(j):j in Eltseq(a,Ftemp)]; 
	Ppol:=Ppol*var+lift*type[1]`PolynomialGenerator^height;
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
	            print"s",s;
      sides:=[[0,s[1,1],s[1,2],s[1,1],s[1,2]]];
      devsEachSide:=[* alldevs[Index(abscissas,Integers()!s[1,1])],[Integers()!s[1,1],Integers()!s[1,2]] *];
end if;
end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

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
	    tmp:=PolynomialRing(FPP)![map(ii):ii in Eltseq((dev 	div type[1]`PolynomialGenerator^height))];	
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
//////////////////////////////////////////////////////////////////////////


intrinsic Index(K::FldFun)->SeqEnum
{Compute the index of the maximal order O_K over the equation order of K and 
factorizes the discriminant of K.}
	t1:=Realtime();
if not assigned K`Index then 
	kt<t>:=PolynomialRing(ConstantField(K));
 	if not assigned K`FactorizedDiscriminant then 		 		
 		d:=kt!Discriminant(DefiningPolynomial(K));
 		if IsFinite(ConstantField(K)) then		
			sq:=SquarefreeFactorization(d);
			if not #sq eq 0 then 
				d:=kt!(d/&*[i[1]:i in sq]);
			end if;				
		else 
			d:=GCD(d,Derivative(d));
		end if;	
		fac:=Factorization(d);
		K`FactorizedDiscriminant:=fac;
	else 	
		fac:=	K`FactorizedDiscriminant;
		
	end if;
	primelist:=[];
	for i in fac do
			Append(~primelist,i[1]);
	end for;
	DegList:=[];
	IndexExpo:=0;
	Indexprimes:=[];
	factor_time := Realtime()-t1;
	for p in primelist do
		tt := Realtime();
		Montes(K,p);
		DegList:=DegList cat [Degree(i):i in K`PrimeIdeals[p]];
	    IndexExpo:=IndexExpo+K`LocalIndex[p]*Degree(p);
	  	  if K`LocalIndex[p] gt 0 then
  		  	Append(~Indexprimes,p);
	  	  else
  	  		factor_time +:=	Realtime() -tt;
  		  end if;
	end for;
	K`Index:=Indexprimes;

return IndexExpo,DegList,factor_time;

else
	DegList:=[];
	IndexExpo:=0;
	for p in K`Index do
		DegList:=DegList cat [Degree(i):i in K`PrimeIdeals[p]];
	    IndexExpo:=IndexExpo+K`LocalIndex[p]*Degree(p);
	end for;
	return IndexExpo,DegList,0;
end if;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic reduceIdeal(I::Rec, p::RngUPolElt)-> Rec, RngIntElt
    { Returns a new ideal J and exponent a such that I = p^a J. }

    Primes := I`Parent`PrimeIdeals[p];
    s := #Primes;

    //Initializing Exponentes of p-part of ideal
    Expos:=[0:i in [1..s]];
    for i in I`Factorization do
        if i[1] eq p then 	
            Expos[i[2]]:=i[3];
        end if;
    end for;

    //Ziehe groessten p(t)^a*O_F aus I heraus und speicher p(t)^a 
    a := 0;
    if forall{i:i in [1..s]|Expos[i] gt 0 } then
        a:=Minimum([Floor(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
        Expos:=[Expos[ll]-Primes[ll]`e*a:ll in [1..s]];
    end if;
    if forall{i:i in [1..s]|Expos[i] lt 0 } then
        a:=Maximum([Ceiling(Expos[ll]/Primes[ll]`e):ll in [1..s]]);
        Expos:=[Expos[ll]-Primes[ll]`e*a:ll in [1..s]];
    end if;

    J := &*[ I`Parent`PrimeIdeals[p,i]^Expos[i] : i in [1..s] ];

    return J, a;
end intrinsic; // reduceIdeal

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

intrinsic Ceil(z::FldRatElt)->RngIntElt
{}

if z in Integers() then
	return Integers()!z+1;
else
	return Ceiling(z);
end if;	

end intrinsic; 

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////



intrinsic LBS(FactorList::SeqEnum, I ::SeqEnum)->SeqEnum
{}

//I :=	Set(&cat FactorList );

if #FactorList eq 0 then 
	return [];
end if;

if #I le 2 then
	
	return Intersection(FactorList,I);
	
else

	for i:=#I-2 to 1 by -1 do	
		L := [I[ll]:ll in [1..i]];
		if forall{j:j in L|j in FactorList } then
			return L;
		end if;
	end for;	
end if;

return [];

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Intersection(S1::SeqEnum, S2 ::SeqEnum)->SeqEnum
{}

L:=[];

for i in S1 do

	if i in S2 then
		Append(~L,i);
	end if;	

end for;

return L;

end intrinsic;
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic RBS(FactorList::SeqEnum, I ::SeqEnum)->SeqEnum
{}

//I :=	Set(&cat FactorList );

if #FactorList eq 0 then 
	return [];
end if;

if #I le 2 then
	
	return Intersection(FactorList,I);
	
else

	for i:=3 to #I  do	
		L := [I[ll]:ll in [i..#I]];
		if forall{j:j in L|j in FactorList } then
			return L;
		end if;
	end for;	
end if;


return [];

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic '-'(S1::SeqEnum,S2::SeqEnum)->SeqEnum
{}

L := [];

for i in S1 do

	if not i in S2 then
		Append(~L,i);
	end if;

end for;

return L;
end intrinsic;
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Common_factors(FactorList::SeqEnum)->SeqEnum
{}


I :=	SetToSequence(Set(&cat FactorList ));	s := #FactorList;
PreCom := [[]: i in [1..s]];

for i:=1 to s do
	tmp := LBS(FactorList[i],I);
	FactorList[i] := FactorList[i] - tmp;
	Append(~PreCom[i], tmp);
	tmp := RBS(FactorList[i],I);
	FactorList[i] := FactorList[i] - tmp;
	Append(~PreCom[i], tmp);
end for;

return PreCom,FactorList;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic Factors(FactorList::SeqEnum)->SeqEnum
{}

s := #FactorList;
PreComp := [];
while #&cat FactorList gt 0 do

	tmp, FactorList := Common_factors(FactorList);
	Append(~PreComp, tmp);
end while;

return PreComp;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic MIN(L::SeqEnum)->RngIntElt
{}

if #L eq 0 then 
	return 0;
else
	return Minimum(L);
end if;		
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic ComputeMultiplier_i(PreComp::SeqEnum,PreFacs::SeqEnum,EndFacs::SeqEnum)->SeqEnum
{}


Check := [];

LPC := [j[1] : j in PreComp];	LPC, perL := Sort(LPC,func<x, y | #x - #y>);	
PerL := Eltseq(perL);

RPC := [j[2] : j in PreComp];	RPC, perR := Sort(RPC,func<x, y | #x - #y>);	
PerR := Eltseq(perR);

tmpL := [];	tmpR := [];
for i in [1..#LPC] do

	if #LPC[i] ge 1 then Append(~tmpL,LPC[i]); end if;
	if #RPC[i] ge 1 then Append(~tmpR,RPC[i]); end if;
	
end for;

l := MIN([#i : i in tmpL]);	r := MIN([#i : i in tmpR]);


for i:= 1 to #LPC do
	if #LPC[i] gt 0 then
		if not LPC[i] in Check then
			if #LPC[i] gt l then
				Append(~PreFacs,[*#PreFacs,LPC[i]*]);
				Append(~Check,LPC[i]);		
			else
				Append(~PreFacs,[*0,LPC[i]*]);
				Append(~Check,LPC[i]);		
			end if;	
			Append(~Check,LPC[i]);
		end if; 
	

		Append(~EndFacs[PerL[i]],#PreFacs);	
	end if;
end for;

Check := [];


for i:= 1 to #RPC do
		if #RPC[i] gt 0 then
			if not RPC[i] in Check then
				if #RPC[i] gt r then
					Append(~PreFacs,[*#PreFacs,RPC[i]*]);
					Append(~Check,LPC[i]);		
				else
					Append(~PreFacs,[*0,RPC[i]*]);
					Append(~Check,RPC[i]);		
				end if;	
				Append(~Check,RPC[i]);	
			end if; 
	
			Append(~EndFacs[PerR[i]],#PreFacs);	
		end if;
end for;


return PreFacs, EndFacs;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic ComputeMultiplierData(PreComp::SeqEnum)->SeqEnum
{}

s := #PreComp[1];	PreFacs := [];	EndFacs := [[] : i in [1..s]];

for i:=1 to #PreComp do
	PreFacs, EndFacs := ComputeMultiplier_i(PreComp[i], PreFacs, EndFacs);
end for;
return PreFacs, EndFacs;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
intrinsic '+'(L1::SeqEnum,L2::SeqEnum)->SeqEnum
{}

if #L1 ge #L2 then
	L := L1;	S:=L2;
else
	L := L2;	S:=L1;
end if;

for i:=1 to #S do
	L[i]+:=S[i];
end for;

return L;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic EffectivePhiMultiplication(fac,Factors,PhiVals,Phis,prec,p)->SeqEnum
{}


Ax := Parent(Phis[1]);	PreFactors := [];	tmp := 1;

if #Factors eq 1 then
	tmp := Phis[Factors[1]];
else
	p_prec := 1;
	old_expo := 0;
	for ll in [1..#Factors] do
		new_exp := Ceil(Max(&+[PhiVals[Factors[j]] : j in [1..ll]]))-old_expo;			
		p_prec := p_prec* p^new_exp;
		old_expo := old_expo+new_exp;
		RMod := InitialeModRing(Ax,p_prec);	
		tmp := ChangePrecMod(RMod,Ax!tmp)*PutModRing(RMod,Phis[Factors[ll]]);			
	end for;
	
end if;
	//print"hier";prec; PhiVals;
end_prec := &+[PhiVals[j] : j in Factors]+prec;
p_prec := p^Ceil(Max(end_prec));
//print"p_prec",p_prec;
RMod := InitialeModRing(Ax,p_prec);	
endi := ChangePrecMod(RMod,Ax!tmp)*PutModRing(RMod,Ax!fac);
return Ax!endi, end_prec;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic ComputeMultiplier(FactorList::SeqEnum,PhiVals::SeqEnum,F::FldFun,p::RngUPolElt)->SeqEnum
{}

PreComp := Factors(FactorList);

PreFactors, EndFactors := ComputeMultiplierData(PreComp);
//print"PreFactors, EndFactors",PreFactors, EndFactors;
tmp := [];	Primes := F`PrimeIdeals[p];	s := #Primes;

for i := 1 to s do
	Append(~tmp,[PhiVals[i,j,#PhiVals[i,j]] : j in [1..s]]);	
end for;
PhiVals := tmp;		Phis := [Primes[i]`Type[#Primes[i]`Type]`Phi: i in [1..s]];

prec_0 :=[0 : i in [1..s]];
PreFacs := []; Prec := [];

for j := 1 to #PreFactors do
	if PreFactors[j,1] eq 0 then
		tmp,prec := EffectivePhiMultiplication(1,PreFactors[j,2],PhiVals,Phis,prec_0,p);
		Append(~PreFacs,tmp);	Append(~Prec,prec);	
	else
		l := PreFactors[j,1];	prec := Prec[l];
		tmp,prec := EffectivePhiMultiplication(PreFacs[l],PreFactors[j,2]-PreFactors[l,2],
   																	 PhiVals,Phis,prec,p);
		Append(~PreFacs,tmp);	Append(~Prec,prec);	   																	 
	end if;		
end for;

multipliers := [];

for i := 1 to #EndFactors do
	pre_fac :=[PreFacs[j] : j in EndFactors[i]];
	pre_fac_vals :=	[Prec[j] : j in EndFactors[i]];
	
	if #pre_fac gt 0 then
		tmp := EffectivePhiMultiplication(1,[1..#pre_fac],pre_fac_vals,pre_fac,prec_0,p);
	else
		tmp := Parent(Phis[1])!1;
	end if;	
	Append(~multipliers,tmp);
end for;

return multipliers;

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic BasisMultiplication(F::FldFun,p::RngUPolElt,Basis_vals::SeqEnum,multiplier::SeqEnum,
															LocalBases::SeqEnum)->SeqEnum
{Computes the resulting basis in an inteligent way}

s := #LocalBases;	n := #Basis_vals;
FastMult_data := [[i,j]:j in [1..#LocalBases[i]],i in [1..s]];
//print"FastMult_data";FastMult_data;

//print"LocalBases";LocalBases;
Sort(~Basis_vals,~per);
FastMult_data := [FastMult_data[Eltseq(per)[i]]:i in [1..#FastMult_data]];
f := DefiningPolynomial(F);
Ax := Parent(LocalBases[1,1]);
p_prec := 1;
old_expo := 0;
basis:=[];


for i in [1..n] do

	mult_ind := FastMult_data[i,1];
	bas_ind :=  FastMult_data[i,2];
	new_exp := Ceil(Basis_vals[i])-old_expo;

	p_prec := p_prec* p^new_exp;
	old_expo := old_expo+new_exp;
	RMod:=InitialeModRing(Ax,p_prec);
	if Degree(LocalBases[mult_ind,bas_ind])+Degree(multiplier[mult_ind]) ge n then	
		RMod_help := quo<RMod|RMod!f>;	
		tmp := RMod_help!PutModRing(RMod,LocalBases[mult_ind,bas_ind])
						*RMod_help!PutModRing(RMod,multiplier[mult_ind]);	
				
	else
		tmp := PutModRing(RMod,LocalBases[mult_ind,bas_ind])*PutModRing(RMod,multiplier[mult_ind]);
	end if;

	Append(~basis,Ax!tmp);		
end for;

return basis, [Floor(i) : i in Basis_vals], [Ceil(i) : i in Basis_vals];

end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic pBasis(F::FldFun,p::RngUPolElt:Reduced:=false,HNF:=true)->SeqEnum
{Computes a p-integral basis of the fractional ideal in Hermite Form or if Reduced is set true an p-orthonormal basis of I}

//Initialization

n := Degree(F);	Montes(F,p);

if F`LocalIndex[p] eq 0 then return [F.1^i:i in [0..n-1]]; end if;

Primes := F`PrimeIdeals[p];		s := #Primes;

L_tmp := [P`e*P`f:P in Primes]; 
Sort(~L_tmp,~per_tmp); Per_tmp := Eltseq(per_tmp);
Primes := Reverse([F`PrimeIdeals[p,i]:i in Per_tmp]);
F`PrimeIdeals[p] := Primes;

kt := PolynomialRing(ConstantField(F));	kx<x> := PolynomialRing(kt); K := BaseField(F);
k :=ConstantField(F);

if Reduced eq true and &*[i`e:i in F`PrimeIdeals[p]] eq 1 then
	Reduced:=false;
end if;

if #F`PrimeIdeals[p] eq 1 then
	HNF := false;
end if;

Expos:=[0:i in [1..#F`PrimeIdeals[p]]];


//Determination of Okutsu bases: §§ Hier Kann ich definitiv etwas rausholen §§
	LocalBases := [];
	VallMatrix := [];
	PhiValMatrix := [];


	for i in [1..s] do 
		
		BasisVals:=[* *];
		PhiVals:=[* *];
		for l in [1..s] do 
			r:=#Primes[l]`Type;		e_P:=Primes[l]`e;	n_P:=e_P*Primes[l]`f;   


			Phis:= [Primes[l]`Type[j]`Phi:j in [1..r]];
			PhiDeg:=[Degree(j):j in Phis];
			PhiExpos:=[PhiExpo(m,PhiDeg):m in [1..n_P-1]];
			Phis:=[x] cat Phis;
			BasisValstmp:=[Rationals()!0:i in [1..n_P]];
			PhiValstmp:=[PhiValuation(F,p,[l,o],i):o in [0..#Primes[l]`Type] ];
			
			for k in [1..n_P-1] do
				BasisValstmp[k+1]:=&+[PhiExpos[k,ll]*PhiValstmp[ll]:ll in [1..#PhiExpos[k] ]];
			end for;
			Append(~BasisVals,BasisValstmp);
			Append(~PhiVals,PhiValstmp);
		end for;
		Append(~PhiValMatrix,PhiVals);
		Append(~VallMatrix,BasisVals);
		r:=#Primes[i]`Type;		e_P:=Primes[i]`e;	n_P:=e_P*Primes[i]`f; 
			Phis:= [Primes[i]`Type[j]`Phi:j in [1..r]];
			PhiDeg:=[Degree(j):j in Phis];
			PhiExpos:=[PhiExpo(m,PhiDeg):m in [1..n_P-1]];
			Phis:=[x] cat Phis;
		localBasis:=[kx!1] cat [ kx!&*[Phis[j]^PhiExpos[k][j]:j in 
														[1..#Phis-1]]:k in [1..n_P-1]];
		Append(~LocalBases,localBasis);
	end for;

if s gt 1 then 
	FacIndex,Facprecision:=Multipliers(F,p,PhiValMatrix,VallMatrix,Reduced);

L_check := Sort([#i:i in FacIndex]);
if L_check eq [0..s-1] then HNF := false; end if;
	for j in [1..s] do
		type := Primes[j]`Type;	slope:= Facprecision[j]*Primes[j]`e-type[#type]`V;
		new_prec := (type[#type]`V+slope)/Primes[j]`e;
		if new_prec gt PhiValMatrix[j,j,#PhiValMatrix[j,j]] then		
			SFL(~type,slope);	F`PrimeIdeals[p,j]`Type := type;
			PhiValMatrix[j,j,#PhiValMatrix[j,j]] := (type[#type]`V+slope)/Primes[j]`e;	
		end if;
	end for;

	multiplier := ComputeMultiplier(FacIndex,PhiValMatrix,F,p);
	Basis_vals := [];	Basis_vals_mod := [];

	for j in [1..s] do
		mult_vals_j := [sum([PhiValMatrix[jj,m,#PhiValMatrix[jj,m]]:m in FacIndex[j]]):jj in [1..s]];
		for i in [1..#VallMatrix[j,j]] do
			w_l_values := [];		

				tmp:=Min([VallMatrix[l,j,i]+mult_vals_j[l] : l in [1..s]]);
				
				Append(~Basis_vals,tmp);			
		end for;
	end for;
	basis, Den_expos, basis_vals := BasisMultiplication(F,p,Basis_vals,multiplier,LocalBases);
	Sort(~basis,~per);	Per := Eltseq(per);

	base := [Evaluate(F,basis[i]):i in [1..n]];
	basis := [base[i]/p^Den_expos[Per[i]]:i in [1..n]];
else
	base := [Evaluate(F,localBasis[i]):i in [1..n]];
	basis := [base[j]/p^Floor(BasisValstmp[j]) : j in [1..n]];
	Den_expos := [Floor(i): i in BasisValstmp];
	basis_vals := [Ceil(i): i in BasisValstmp];
		
end if;

if not HNF 
	then return basis;
end if;


//////////////Transforming into triangular form////////////////////
zeta:=Maximum(Den_expos);
Den_expos:=[zeta-i:i in Den_expos];

PreBase:=Reverse([p^Den_expos[i]*base[i]:i in [1..n]]);

MatList:=[];

pevModExp := p^(Maximum(basis_vals)+1);
kt_mod := quo<kt|pevModExp>;
for j:=1 to #PreBase by  1 do
	Append(~MatList,Reverse(Parent([kt_mod!p])!Eltseq(PreBase[j])));
end for;
	MM := Matrix(MatList);
	if not IsFinite(k) then
		MM := ChangeRing(MM,kt);
	end if;
	H:=HermiteForm(MM);
	MatList:=[Eltseq(H[i]):i in [1..n]];
	Denoms:=[];
	for i in [1..n] do
		exp:=Valuation(kt!MatList[i,i],p);	
		Append(~Denoms,exp);
		pevExp:=p^exp;			
		inv:=Modinv(kt!(kt!MatList[i,i]/pevExp),pevModExp);
		MatList[i,i]:=kt_mod!pevExp;
		for j in [i+1..n] do
			if 	not MatList[i,j] eq 0 then
				tmp := kt_mod!MatList[i,j]*kt_mod!inv;
				MatList[i,j]:=tmp;
			end if;
		end for;	
	end for;
	H := Matrix(MatList);
	if not IsFinite(k) then
		H := ChangeRing(H,kt_mod);
	end if;
	Denoms:=Sort([i-zeta:i in Denoms]);
	Base:=Reverse([(F!  Parent([p])!Reverse(Eltseq(H[i]))) *K!p^-zeta:i in [1..n]]);

return Base;

end intrinsic;


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic sum(L::SeqEnum)->RngIntElt
{Help}

if #L gt 0 then
	return &+L;
else
	return 0;
end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


intrinsic Multipliers(F::FldFun,p::RngUPolElt, PhiVals::SeqEnum,BasisVals::SeqEnum,	
																Reduced::BoolElt)->SeqEnum
{Computes Multiplier}

s:=#PhiVals;

if s eq 1 then return [[]],[[0]]; end if;

omega_Plus := [[]:i in [1..s]];	omega_Minus := [[]:i in [1..s]];

//Computing the omega values
for i in [1..s] do	
	for j in [1..s] do 		
		omega_Plus[i,j] := BasisVals[j,i,#BasisVals[j,i]];
		omega_Minus[i,j] := BasisVals[j,i,1];
	end for;
end for;

SFL_List := [[0]:i in [1..s]];	Factor_List := [];	Right_Indices := [1..s];
Left_Indices := [];	

relations := Matrix(Integers(),2*s-1,1,[1:i in [1..s-1]] cat [1] cat [-1:i in [1..s-1]]); 

for r in [1..s] do
	
	if Reduced then
		_,min_index := Min([Floor(  sum([PhiVals[l_i,l,#PhiVals[l_i,l]]
																 : l_i in Left_Indices ])
											 + omega_Plus[l,l]    ): l in  Right_Indices]);
	else
		_,min_index := Min([sum([PhiVals[l_i,l,#PhiVals[l_i,l]] : l_i in Left_Indices ])
												 + omega_Plus[l,l] : l in  Right_Indices]);	
	end if;										 
	i := Right_Indices[min_index];
	Remove(~Right_Indices,Position(Right_Indices,i));
	Append(~Left_Indices,i);	
	C_List := [0:i in [1..s]];		lhs_vals := [];
	for j in Remove([1..s],i) do
		gamma := Lcm(F`PrimeIdeals[p,i]`e,F`PrimeIdeals[p,j]`e);		lhs_tmp := [];
		C_List[j] := gamma*(omega_Plus[i,i]-omega_Minus[j,i]-1)+1;
	
		if j in Left_Indices or Reduced then
			C_List[j] := C_List[j]+1;
		end if;
		run := 1;	
		for k in Remove([1..s],i) do
			if k eq j then
				k_j_ind := run;
				tmp := 0;
			else
				tmp := gamma*(PhiVals[j,k,#PhiVals[j,k]]-PhiVals[i,k,#PhiVals[i,k]]);	
				run := run+1;
			end if;	
			Append(~lhs_tmp,tmp);
		end for;
		lhs_tmp[k_j_ind] := C_List[j]-sum(lhs_tmp);
		Append(~lhs_vals,lhs_tmp );	
	end for;

	Append(~lhs_vals,[1:ii in [1..s-1]]);							

	RHS := Matrix(Integers(),2*s-1,1, Remove(C_List,i) cat [r-1] cat [1:ii in [1..s-1]]);
	LHS :=  VerticalJoin(Matrix(Integers(),s,s-1,lhs_vals),IdentityMatrix(Integers(),s-1));
	obj := Matrix(Integers(),1,s-1,[1:i in [1..s-1]]);	

	L	:= MinimalSolution(LHS,relations,RHS,obj);
	L:=Insert(Eltseq(L),i,0);
	Factor_tmp	:=	[];
	for m in [1..s] do
		if not L[m] eq 0 then
			Append(~Factor_tmp,m);
		end if;
	end for;
	Factor_List[i] := Factor_tmp;
	// Computing precision of the Okutsu appr.	
	for j in Factor_List[i] do
		pos := Position(Factor_List[i],j);
		e := F`PrimeIdeals[p,j]`e;
		lhs := sum([PhiVals[ll,i,#PhiVals[ll,i]] : ll in Factor_List[i] ])+omega_Plus[i,i];
		lambda := sum([PhiVals[ll,j,#PhiVals[ll,j]] : ll in Remove(Factor_List[i], pos) ])
																		-omega_Minus[j,i];	

		gamma := Lcm(e,F`PrimeIdeals[p,i]`e);	
		tmp := lhs - lambda -1+1/gamma;
	
		if j in Left_Indices or Reduced then
			tmp := tmp+1;
		end if;	
		tmp := Ceiling(tmp);
		Append(~SFL_List[j],tmp);
	end for;

end for;
SFL_List := [Max(i): i in SFL_List];

return Factor_List, SFL_List;

end intrinsic;	

//////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////


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
			tmp:=Minimum([Valuation(Eltseq(F`PrimeIdeals[p,IndexPrime]`Type[1]`Phi)[1],p),
											F`PrimeIdeals[p,IndexPrime]`Type[1]`slope]);
			return tmp;
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

intrinsic Truncate(~log)
{}

require Degree(log) gt 1: "argument too short to be truncated";
log:=Vector(Remove(Eltseq(log),Degree(log)));
end intrinsic;

/////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////


intrinsic MaximalOrderComp(F::FldFun:Multiplier:=true)-> SeqEnum
    { Compute maximal order of a function field. }

t1 := Realtime();
n := Degree(F);
if not assigned F`Index then
   	Index(F);	
end if;   	
 index_time := Realtime()-t1;
 print"Index Berechnung dauerte in Sekunden:",   index_time;	
   	primelist := F`Index; 

	if #primelist eq 0 then return [F.1^i:i in [0..n-1]],index_time; end if;
	if #primelist eq 1 then return pBasis(F, primelist[1]),index_time; end if;
    Numlist := [];
    Denlist := [];
    DenCRTlist := [];
	A := Parent(primelist[1]);	Ax := PolynomialRing(A);
	
    for i in [1..#primelist] do
        p := primelist[i];

		Montes(F, p);

        if F`LocalIndex[p] gt 0 then
        	if Multiplier then
	            B := pBasis(F, p);
	        else   
	        	B := pBasisQutients(F, p);
	        end if;	
            nums := [Ax!Eltseq(Numerator(b)): b in B];
            dens := [A! Denominator(b) : b in B];
            dens_crt := [ p*j : j in dens ];

            Append(~Numlist, [ Coefficients(g) : g in nums ]);
            Append(~Denlist, dens);
            Append(~DenCRTlist, dens_crt);
        end if;
    end for;
    nprimes := #Denlist;
    if nprimes eq 0 then
        return [F.1^k: k in [0..n-1]],index_time;
    end if;
    tmps := Cputime();
    SBasis := [ F | ];

    for i := 1 to n do
        Dens := [ Denlist[k, i] : k in [1..nprimes] ];
        DensCRT := [ DenCRTlist[k,i] : k in [1..nprimes] ];
        coeffs := [];
        for j := 1 to i-1 do
            Nums := [Numlist[k, i, j] : k in [1..nprimes]];
            Append(~coeffs, CRT(Nums, DensCRT));
        end for;
        coeffs cat:= [0: j in [1..n-#coeffs]];
        Append(~SBasis, (F.1^(i-1)+F!coeffs)/&*Dens);
    end for;

    return SBasis,index_time;
end intrinsic; // SIdealBasis


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

intrinsic pBasisQutients(F::FldFun,p ::RngUPolElt)-> SeqEnum
{}

n := Degree(F);
kt := PolynomialRing(ConstantField(F));	K:=BaseField(F); k:= ConstantField(F);
Montes(F,p:Basis := true);
base := F`pBasis[p]; Den_expos := F`BasisExp[p];
//////////////Transforming into HNF////////////////////
zeta:=Maximum(Den_expos);

den_vals :=[zeta-i:i in Den_expos]; 

PreBase:=Reverse([p^den_vals[i]*base[i]:i in [1..n]]);

MatList:=[];

pevModExp := p^(Maximum(Den_expos)+2);
kt_mod := quo<kt|pevModExp>;
for j:=1 to #PreBase by  1 do

	Append(~MatList,Reverse(Parent([kt_mod!p])!Eltseq(PreBase[j])));
end for;
	MM := Matrix(MatList);
	if not IsFinite(k) then
		MM := ChangeRing(MM,kt);
	end if;
	H:=HermiteForm(MM);
	MatList:=[Eltseq(H[i]):i in [1..n]];
	Denoms:=[];
	for i in [1..n] do
		exp:=Valuation(kt!MatList[i,i],p);	
		Append(~Denoms,exp);
		pevExp:=p^exp;			
		inv:=Modinv(kt!(kt!MatList[i,i]/pevExp),pevModExp);
		MatList[i,i]:=kt_mod!pevExp;
		for j in [i+1..n] do
			if 	not MatList[i,j] eq 0 then
				tmp := kt_mod!MatList[i,j]*kt_mod!inv;
				MatList[i,j]:=tmp;
			end if;
		end for;	
	end for;

	Denoms:=Sort([i-zeta:i in Denoms]);

	H := Matrix(MatList);
	if not IsFinite(k) then
		H := ChangeRing(MM,kt_mod);
	end if;

	Base:=Reverse([(F!  Parent([p])!Reverse(Eltseq(H[i]))) *K!p^-zeta:i in [1..n]]);

return Base;


end intrinsic; 
