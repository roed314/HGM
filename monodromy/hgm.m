intrinsic HypergeometricLabel(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt]) -> MonStgElt
{ LMFDB label of the hypergeometric family associated to the hypergeometric data A,B. }
    require #A gt 0 and #B gt 0 and &+[EulerPhi(a):a in A] eq &+[EulerPhi(b):b in B]: "A,B must specify valid hypergeometric (cyclotomic) data.";
    return "A" cat Join([IntegerToString(a):a in A],".") cat "_B" cat Join([IntegerToString(b):b in B],".");
end intrinsic;

intrinsic pParts(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt],p::RngIntElt) -> SeqEnum[RngIntElt], SeqEnum[RngIntElt], SeqEnum[RngIntElt]
{ Computes (reduced) p-parts of hypergeometric data A,B and common p-part. }
    require #A gt 0 and #B gt 0 and &+[EulerPhi(a):a in A] eq &+[EulerPhi(b):b in B]: "A,B must specify valid hypergeometric (cyclotomic) data.";
    require IsPrime(p):"p must be prime.";
    psplit := func<v,p|&cat[[q:i in [1..EulerPhi(a div q)]] where q:=p^Valuation(a,p) : a in v]>;
    Ap:= psplit(A,p);  Bp := psplit(B,p);
    Cp := Reverse(Sort([a:a in Multiset(Ap) meet Multiset(Bp)]));
    Ap := Reverse(Sort([a:a in Multiset(Ap) diff Multiset(Cp)]));
    Bp := Reverse(Sort([a:a in Multiset(Bp) diff Multiset(Cp)]));
    return Ap,Bp,Cp;
end intrinsic;

intrinsic upParts(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt],p::RngIntElt) -> SeqEnum[RngIntElt], SeqEnum[RngIntElt], SeqEnum[RngIntElt]
{ Computes (reduced) prime-to-p-parts of hypergeometric data A,B and common prime-to-p-part. }
    require #A gt 0 and #B gt 0 and &+[EulerPhi(a):a in A] eq &+[EulerPhi(b):b in B]: "A,B must specify valid hypergeometric (cyclotomic) data.";
    require IsPrime(p):"p must be prime.";
    upsplit := func<v,p|&cat[[a div q:i in [1..EulerPhi(q)]] where q:=p^Valuation(a,p) : a in v]>;
    Aup := upsplit(A,p); Bup := upsplit(B,p);
    Cup := Reverse(Sort([a:a in Multiset(Aup) meet Multiset(Bup)]));
    Aup := Reverse(Sort([a:a in Multiset(Aup) diff Multiset(Cup)]));
    Bup := Reverse(Sort([a:a in Multiset(Bup) diff Multiset(Cup)]));
    return Aup,Bup,Cup;
end intrinsic;

intrinsic Degree(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt]) -> RngIntElt
{ The degree of the hypergeometric data A,B. }
    return Degree(HypergeometricData(A,B));
end intrinsic

intrinsic Weight(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt]) -> RngIntElt
{ The weight of the hypergeometric data A,B (width of the Hodge vector). }
    return Weight(HypergeometricData(A,B));
end intrinsic;

intrinsic HodgeVector(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt]) -> RngIntElt
{ The Hodge vector associated to the hypergeometric data A,B. }
    H := HypergeometricData(A,B);
    // Hack to handle even weight (this should be reexamined at some point)
    w := Weight(A,B);
    S := IsOdd(w) select HodgeStructure(H) else HodgeStructure(LSeries(H,17:Identify:=false,BadPrimes:=[<2,0,1>,<3,0,1>,<5,0,1>,<7,0,1>]));
    S := {*u[1]:u in S*};
    return [Multiplicity(S,j):j in [0..w]];
end intrinsic;

intrinsic BezoutMatrix(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt]) -> AlgMatElt[RngInt]
{ The Bezout matrix associated to hypergeometric data A,B. }
    require #A gt 0 and #B gt 0 and &+[EulerPhi(a):a in A] eq &+[EulerPhi(b):b in B]: "A,B must specify valid hypergeometric (cyclotomic) data.";
    d := Degree(A,B);
    R<y,z> := PolynomialRing(Integers(),2);
    bezpoly := func<f,g|(Evaluate(f,y)*Evaluate(g,z)-Evaluate(f,z)*Evaluate(g,y)) div (y-z)>;
    poly := func<v|&*[CyclotomicPolynomial(n): n in v]>;
    bp := bezpoly(poly(A),poly(B));
    return Matrix(Integers(),d,d,[Coefficient(Coefficient(bp,1,j),2,i): i in [0..d-1],j in [d-1..0 by -1]]);
end intrinsic;

intrinsic BezoutForm(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt],ell::RngIntElt) -> AlgMatElt[RngInt]
{ The quadratic form associated the Bezout matrix of the hypergeometric data A,B of even weight. }
    require IsEven(Weight(A,B)): "The weight of the hypergoemetric data A,B must be even.";
    require IsPrime(ell): "The integer ell must be a prime.";
    return ChangeRing(ExactQuotient(QuadraticForm(BezoutMatrix(A,B)),ell eq 2 select 2 else 1),GF(ell));
end intrinsic;

intrinsic PolarSpace(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt],ell::RngIntElt:ReScale:=false) -> ModTupRng[FldFin]
{ The polar space over F_ell defined by the Bezout matrix of the hypergeometric data A,B. }
    // The rescale parameter is used to deal with a Magma bug, remove once bug is fixed
    c := ReScale select PrimitiveRoot(ell) else 1;
    M := c*BezoutMatrix(A,B);
    F := GF(ell);
    if IsEven(Weight(A,B)) then
        return QuadraticSpace(ChangeRing(ExactQuotient(QuadraticForm(M),ell eq 2 select 2 else 1),F));
    else
        return SymplecticSpace(ChangeRing(M,F));
    end if;
end intrinsic;

intrinsic LeftIsometryGroup(V::ModTupFld) -> GrpMat
{ The isometry group of V (acting on the left). }
    G := IsometryGroup(V);
    return sub<GL(Degree(G),BaseRing(G))|[Transpose(g):g in Generators(G)]>;
end intrinsic;

intrinsic AmbientIsometryGroup(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt],ell::RngIntElt) -> GrpMat[FldFin], ModTupRng[FldFin]
{ The (left) isometry group of the polar space over F_ell determined by the Bezout matrix of the hypergeometric data A,B. }
    // hack to deal with magma bug, undo once bug is fixed
    try
        V := PolarSpace(A,B,ell);
        return LeftIsometryGroup(V),V;
    catch e
        V := PolarSpace(A,B,ell:ReScale);
        return LeftIsometryGroup(V),V;
    end try;
end intrinsic;

intrinsic MonodromyGroup(A::SeqEnum[RngIntElt],B::SeqEnum[RngIntElt],ell::RngIntElt) -> GrpMat[FldFin]
{ The mod-ell monodromy group of the hypergeometric data A,B (a subgroup of the AmbientIsometryGroup). }
    poly := func<v|&*[CyclotomicPolynomial(n): n in v]>;
    return MatrixGroup<Degree(A,B),GF(ell)|CompanionMatrix(poly(A)),CompanionMatrix(poly(B))>;
end intrinsic;
