Attach("hgm.m");

// handy utility functions
strip := func<s|Join(Split(Join(Split(s," "),""),"\n"),"")>;
atoi := func<s|#s gt 0 select StringToInteger(s) else 0>;
atoii := func<s|t eq "[]" select [Integers()|] else [Integers()|StringToInteger(n):n in Split(t[2..#t-1],",")] where t:=strip(s)>;

// Do not use SubstituteString here, it is horrendously slow
function bracket(s)
    t := Join(Split(Join(Split(s,"<":IncludeEmpty),"["),">":IncludeEmpty),"]");
    // Split omits the last field if it is empty even when IncludeEmpty is set (which makes no sense!), so we work around this by padding if needed
    if #t lt #s and s[#s] eq ">" then t cat:="]";  end if;  // don't check for trailing <, this shouldn't happen, and if it does assert below will fail
    assert #s eq #t;
    return t;
end function;

function curly(s) 
    // Split omits the last field if it is empty even when IncludeEmpty is set (which makes no sense!), so we work around this by padding if needed
    t := Join(Split(Join(Split(s,"[":IncludeEmpty),"{"),"]":IncludeEmpty),"}");
    if #t lt #s and s[#s] eq "]" then t cat:="}";  end if; // don't check for trailing [, this shouldn't happen, and if it does assert below will fail
    assert #s eq #t;
    return t;
end function;

function uncurly(s) 
    // Split omits the last field if it is empty even when IncludeEmpty is set (which makes no sense!), so we work around this by padding if needed
    t := Join(Split(Join(Split(s,"{":IncludeEmpty),"["),"}":IncludeEmpty),"]");
    if #t lt #s and s[#s] eq "}" then t cat:="]";  end if; // don't check for trailing [, this shouldn't happen, and if it does assert below will fail
    assert #s eq #t;
    return t;
end function;

function small_group_order(n)
    return n lt 2047 and not n in [512,1024,1152,1536,1920,2048];
end function;

hgm_monodromy_columns := [
    ["A","integer[]"],
    ["B","integer[]"],
    ["family","text"],
    ["ell","integer"],
    ["Au","integer[]"],
    ["Bu","integer[]"],
    ["Cu","integer[]"],
    ["degree","integer"],
    ["weight","integer"],
    ["type","integer"],
    ["bezout_det","integer"],
    ["radical_dim","integer"],
    ["isotropic_dim","integer"],
    ["witt_index","integer"],
    ["ambient_order","numeric"],
    ["ambient_factored_order","integer[]"],
    ["monodromy_order","numeric"],
    ["monodromy_factored_order","integer[]"],
    ["monodromy_index","numeric"],
    ["monodromy_factored_index","integer[]"],
    ["ambient_gens","integer[]"],
    ["monodromy_gens","integer[]"],
    ["ambient_name","text"],
    ["ambient_matrix_group_label","text"],
    ["ambient_group_label","text"],
    ["monodromy_matrix_group_label","text"],
    ["monodromy_group_label","text"]
];

function ambient_name(deg,wt,rad,iso,witt,ell)
    type := wt mod 2 eq 1 select "Sp" else "O";
    if ell eq 2 then
        sign := Sprintf("{%o,%o}",iso mod 2, witt mod 2);
    else
        sign := Sprintf("%o",witt mod 2);
    end if;
    return Sprintf("$%o_%o(\\mathbb{F}_%o)_%o^%o$",type,deg,ell,rad,sign);
end function;

function monodromy_record(A,B,ell:ambient_order:=0,monodromy_order:=0)
    str := func<x|curly(bracket(strip(Sprintf("%o",x))))>;
    itoa := func<n|IntegerToString(n)>;
    rec := AssociativeArray();
    rec["family"] := HypergeometricLabel(A,B);
    Au,Bu,Cu := upParts(A,B,ell);
    deg := Degree(A,B); wt := Weight(A,B);
    rec["A"] := str(A);
    rec["B"] := str(B);
    rec["ell"] := str(ell);
    rec["Au"] := str(Au); rec["Bu"] := str(Bu); rec["Cu"] := str(Cu);
    rec["degree"] := itoa(deg);
    rec["weight"] := itoa(wt);
    rec["type"] := itoa(wt mod 2);
    rec["bezout_det"] := itoa(Determinant(BezoutMatrix(A,B)) mod ell);
    ambi,V := AmbientIsometryGroup(A,B,ell);
    rad := Dimension(Radical(V));
    iso := Dimension(MaximalTotallyIsotropicSubspace(OrthogonalComplement(V,Radical(V))));
    witt := WittIndex(V);
    rec["radical_dim"] := itoa(rad);
    rec["isotropic_dim"] := itoa(iso);
    rec["witt_index"] := itoa(witt);
    rec["ambient_name"] := ambient_name(deg,wt,rad,iso,witt,ell);
    mono := MonodromyGroup(A,B,ell);
    rec["ambient_gens"] := str([[Eltseq(r):r in Rows(g)]:g in Generators(ambi)]);
    rec["monodromy_gens"] := str([[Eltseq(r):r in Rows(g)]:g in Generators(mono)]);
    if ambient_order eq 0 then ambient_order := #ambi; end if; // this could take a while
    if monodromy_order eq 0 then monodromy_order := #mono; end if; // this could take a while
    rec["ambient_order"] := str(ambient_order);
    rec["ambient_factored_order"] := str(Factorization(ambient_order));
    rec["monodromy_order"] := str(monodromy_order);
    rec["monodromy_factored_order"] := str(Factorization(monodromy_order));
    rec["monodromy_index"] := str(ExactQuotient(ambient_order,monodromy_order));
    rec["monodromy_factored_index"] := str(Factorization(ExactQuotient(ambient_order,monodromy_order)));
    rec["ambient_matrix_group_label"] := "\\N";
    rec["ambient_group_label"] := small_group_order(ambient_order) select Sprintf("%o.%o",gid[1],gid[2]) where gid := IdentifyGroup(ambi) else "\\N";
    rec["monodromy_matrix_group_label"] := "\\N";
    rec["monodromy_group_label"] := small_group_order(monodromy_order) select Sprintf("%o.%o",gid[1],gid[2]) where gid := IdentifyGroup(mono) else "\\N";
    out := [rec[c[1]]:c in hgm_monodromy_columns];
    return strip(Join(out,":"));
end function;

function monodromy_header_names()
    return Join([c[1]:c in hgm_monodromy_columns],":");
end function;

function monodromy_header_types()
    return Join([c[2]:c in hgm_monodromy_columns],":");
end function;

if assigned A and assigned B and assigned ell then
    print monodromy_record(atoii(A),atoii(B),atoi(ell));
    exit;
end if;
