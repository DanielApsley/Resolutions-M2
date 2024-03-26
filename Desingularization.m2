newPackage(
    "Desingularization",
    Version => "0.01",
    Date => "October 41, 2029",
    Authors => {
	{Name => "Daniel Apsley", Email => "apsley@math.utah.edu", HomePage => "https://www.math.utah.edu/~apsley/"}, 
    {Name => "Emelie Arvidsson", Email => "arvidsson@utah.edu", HomePage => "https://www.emeliearvidsson.com/"},
    {Name => "Joseph Sullivan", Email => "jsullivan@math.utah.edu", HomePage => "https://partiallyordered.com/"}},
    Headline => "Resolving Singularities in Macaulay2",
    Keywords => {"Algebraic Geometry"},
    PackageImports => { "ReesAlgebra", "Divisor", "PrimaryDecomposition", "IntegralClosure" },
    DebuggingMode => true,
    Reload=>true
    );

export {
-- Methods
"variableChange", 
"inverseMap", 
"baseChangeRingMap",
"blowupCharts",
"totalTransform",
"strictTransform",
"desingStep",
"nonSNCLocus",
"singularIndices",
"curveResolution",
"restrictDivisor",
"nonSNCLocusAlongIdeal",
"normalizeStep",
"projDesingStep",
-- Options
"Exceptional",
"Divisorial",
"AuxiliaryData",
-- Types and Terms
"DesingularizationStep",
"Charts",
"CheckLoci",
"StepNumber",
"IntersectionMatrix",
"Exceptionals",
"Boundary"
};

-- Change the above as needed! We will probably take out a good chunk of these before submission. 

DesingularizationStep = new Type of MutableHashTable;
desingStep = method();

desingStep(Ring) := R -> (
	new DesingularizationStep from {Charts => {map(R, R, flatten entries vars R)}, CheckLoci => {ideal(sub(0,R))}, IntersectionMatrix => matrix(0), StepNumber => 0, Exceptionals => {{}}, Boundary => {divisor(sub(1, R))}}
);

desingStep(WeilDivisor) := D -> (
    R := ring(D);
    new DesingularizationStep from {Charts => {map(R, R, flatten entries vars R)}, CheckLoci => {ideal(sub(0,R))}, IntersectionMatrix => matrix(0), StepNumber => 0, Exceptionals => {{}}, Boundary => {D}}
);

-- AuxiliaryData outputs the dehomogenization maps as charts. Intended for strictly internal use. 

projDesingStep =  method(Options => {AuxiliaryData => false});
projDesingStep(Ring) := opts -> R -> (
    -- if isHomogeneous(R) == false then (
    --     error "expected homogeneous ring"
    -- );
    L := flatten entries vars R;
    n := #L;
    k := coefficientRing(R);
    S := k[L];
    I := ideal R;
    deg := degree I;
    affCharts := {};
    checkLoci := {};
    mappingVars := {};
    newChart := map(R,R, flatten entries vars R);
    for i from 0 to (n - 1) do (
        affineVars := delete(L#i, L);
        affineRing := k[affineVars];
        for i from 0 to (n - 2) do (
            affineVars = replace(i, sub(affineVars#i, affineRing), affineVars);
        );
        mappingVars = insert(i, sub(1, affineRing), affineVars);
        phi := map(affineRing, S, mappingVars);
        affineIdeal := phi(sub(I, S));
        affR := affineRing/affineIdeal;
        -- the locus where we should check for singularities
        -- if charts are U0, U1, U2, ..., Un
        -- want to only look for singualarities (to avoid redundancy) by looking in
        -- U0, U1\U0, U2\(U0 cup U1), ..., Un\(U0 cup U1 cup ... cup Un)
        checkLocus := sub(ideal(apply(L_{0..(i-1)}, x->sub(x,affR))), affR);
        checkLoci = append(checkLoci, checkLocus);
        if opts#AuxiliaryData === false then (
            newChart = map(affR, affR, flatten entries vars affR);
            affCharts = append(affCharts, newChart);
        );
        if opts#AuxiliaryData === true then (
            for i from 0 to (#mappingVars - 1) do (
                mappingVars = replace(i, sub(mappingVars#i, affR), mappingVars);
            );
            newChart = map(affR, R, mappingVars);
            affCharts = append(affCharts, newChart); 
        );
    );

    newBoundary := {};
    for C in affCharts do (
        newBoundary = append(newBoundary, divisor(sub(1, target C)));
    );
    
    return new DesingularizationStep from {Charts => affCharts, CheckLoci => checkLoci, IntersectionMatrix => matrix(deg^2), StepNumber => 0, Exceptionals => apply(affCharts, chart->{}), Boundary => newBoundary}
);

variableChange = method();
variableChange(PolynomialRing, Symbol) := (R, t) -> (
	oldVars := flatten entries vars R;
	n := #(oldVars);
	coeffRing := coefficientRing(R);
	freshRing := coeffRing[t_1..t_n];
	phi := map(freshRing, R, vars freshRing);
	phi
);

variableChange(QuotientRing, Symbol) := (R, t) -> (
	oldVars := flatten entries vars R;
	n := #oldVars;
	coeffRing := coefficientRing(R);
	freshPolyRing := coeffRing[t_1..t_n];
	psi := map(R, freshPolyRing, oldVars);
	freshIdeal := ker psi;
	freshRing := freshPolyRing/freshIdeal;
	phi := map(freshRing, R, vars freshRing);
	phi
);

variableChange(RingMap, Symbol) := (phi, t) -> (
    return variableChange(target phi, t) * phi
)


variableChange(Ideal, Symbol) := (I, t) -> (
	R := ring(I);
	phi := variableChange(R, t);
	phi(I)
);

-- Perhaps the function finding the 'pruning map' exists already. I couldn't find it so I made some. Excuse the bit of space.

preImage = method();
preImage(RingMap, Ideal) := (phi, I) -> (
    projection := map(target(phi)/I, target(phi));
    kernel (projection*phi) 
);


inverseMap = method();
inverseMap(RingMap) := phi -> (
    if kernel phi != ideal(substitute(0, source phi)) then (
        error "The map is not invertible."
    );
    flatRing := (flattenRing(target phi))#0;
    varlist := flatten entries vars flatRing;
    images := {};
    for x in varlist do (
        J := preImage(phi, ideal(substitute(x, target phi)));
        gensJ := flatten entries gens J;
        images = append(images, gensJ#0);
    );
    map(source phi, target phi, images)
);

--TODO: add an error for when J is not principal. 

prunedringMapInv = method();
prunedringMapInv(Ring) := R -> (
    prunedRing := prune R; 
    badvars := flatten entries vars prunedRing;
    goodvars := {};
    for x in badvars do (
        goodvars = append(goodvars, substitute(x, R))
    );
    phi := map(R, prunedRing, goodvars);
    phi
);

prunedringMap = method();
prunedringMap(Ring) := R -> (
    prunedRing := prune R; 
    badvars := flatten entries vars prunedRing;
    goodvars := {};
    for x in badvars do (
        goodvars = append(goodvars, substitute(x, R))
    );
    phi := map(R, prunedRing, goodvars);
    inverseMap(phi)
);

-- convenience method which "prunes" a ring homomorphism

prunedMapOfRings = method();
prunedMapOfRings(RingMap) := (F) -> (
    R := F.source;
    S := F.target;

    PRtoR := prunedringMapInv(R);
    StoPS := prunedringMap(S);
    PR := PRtoR.source;
    PS := StoPS.target;
    PF := StoPS * F * PRtoR;

    return PF;
);

-- base changes map of K-algebras to map of L-algebras

baseChangeRingMap = method();
baseChangeRingMap(RingMap, Ring) := (F, L) -> (
    PF := F; -- prunedMapOfRings(F);
    PR := PF.source;
    PS := PF.target;

    -- step 2: make the corresponding polynomial rings over which to define LR, LS
    LpolyR := L[PR.gens];
    LpolyS := L[PS.gens];

    -- step 3: base change the defining ideals
    LpolyR;
    LRideal := ideal(sub(0, LpolyR));
    if isQuotientRing(PR) then (
        LRideal = sub(PR.ideal,LpolyR);
    );
    LpolyS;
    LSideal := ideal(sub(0, LpolyS));
    if isQuotientRing(PS) then (
        LSideal = sub(PS.ideal,LpolyS);
    );

    -- step 4: write the quotients
    LR := LpolyR/LRideal;
    LS := LpolyS/LSideal;

    originalEntries := flatten(entries(PF.matrix));
    Lentries := {};
    for i from 0 to #(originalEntries)-1 do (
        Lentries = append(Lentries, sub((originalEntries#i), LS));
    );

    LF := map(LS,LR,Lentries);

    return LF;
);


blowupCharts = method(Options => {AuxiliaryData => false});

blowupCharts(Ideal, Symbol) := opts -> (J,s) -> (
    a := reesIdeal(J); -- Ideal of rees algebra in affine space over A.
	A := ring(J);
    B := ring(a);
    
    rees := B/a; -- Rees algebra of J
    structureB := map(rees, A, {});

    D := projDesingStep(rees, AuxiliaryData => true);
    precharts := D#Charts;

    newCharts := {};
    newExceptionals := {};
    newCheckLoci := {};
    for i from 0 to #precharts - 1 do (
        phi := precharts#i;
        varChangeMap := variableChange(target phi, s);
        psi := varChangeMap*phi*structureB;
        newCharts = append(newCharts, psi);
        newExceptionals = append(newExceptionals, psi(J));
        newCheckLoci = append(newCheckLoci, varChangeMap(D#CheckLoci#i));
    );
    if opts#AuxiliaryData === true then (
        return (newCharts, newExceptionals, newCheckLoci);
    );
    if opts#AuxiliaryData === false then (
        return newCharts;
    );
);

blowupCharts(DesingularizationStep, Ideal) := opts -> (S, J) -> (
    newStepNumber := S#StepNumber + 1;
    oldExceptionals := S#Exceptionals;
    oldCharts := S#Charts;
    oldCheckLoci := S#CheckLoci;
    oldTargets := {};
    for f in oldCharts do (
        oldTargets = append(oldTargets, target(f))
    );
    Jrings := 0;
    Jringindex := -1;
    oldBoundary := S#Boundary;

    -- checking the ideal we're blowing up is an ideal of one of the charts, and finding which chart it lives in.

    for R in oldTargets do (
        Jringindex = Jringindex + 1;
        if ring(J) === R then (
            Jrings = Jrings + 1;
            break;
        );
    );
    if Jrings != 1 then (
        error "expected ideal of some chart"
    );
    
    prenewvariable := concatenate{"T", toString(newStepNumber)};
    newvariable := getSymbol prenewvariable;
    (newblowupcharts, newexceptionals, newcheckloci) := blowupCharts(J, newvariable, AuxiliaryData => true);
    oldseq := (oldExceptionals)#Jringindex;
    if #oldBoundary != 0 then (
        oldDIdeal := ideal oldBoundary#Jringindex;
    );
    
    chartstoappend := {};
    exceptionalstoappend := {};
    boundarytoappend := {};
    checklocitoappend := {};

    for i from 0 to (#newblowupcharts - 1) do (
        C := (newblowupcharts#i, newexceptionals#i, newcheckloci#i);
        pref := C#0;
        g := oldCharts#Jringindex;
        fvars := flatten entries matrix pref;
        f := map(target pref, target g, fvars);
        localExcideal := C#1;
        freshseq := {};
        R := target(f);
        for exIdeal in oldseq do (
            unsaturatedExc := (f(sub(exIdeal, source f)));
            transformedExc := saturate(unsaturatedExc, localExcideal);
            freshseq = append(freshseq, transformedExc);
        );
        freshseq = append(freshseq, C#1);
        chartstoappend = append(chartstoappend, f*g);
        exceptionalstoappend = append(exceptionalstoappend, freshseq);
        if #oldBoundary != 0 then(
                boundarytoappend = append(boundarytoappend, divisor(f(sub(oldDIdeal, source f))));
        );

        -- intersect each of the newcheckloci with the pullback of oldCheckLoci#Jringindex
        newcheckloci = replace(i, newcheckloci#i + f(oldCheckLoci#Jringindex), newcheckloci);
    );

    -- Adding an empty exceptional divisor in each irrelevant chart. 
    if newStepNumber > 1 then (
        numolds := #(oldExceptionals);
        for i from 0 to numolds - 1 do (
            chartRing := ring((oldExceptionals#i)#0);
            oldExceptionals = replace(i, {append(oldExceptionals#i, sub(1, chartRing))}, oldExceptionals)
        );
    );

    newCharts := flatten replace(Jringindex, chartstoappend, oldCharts);
    newExceptionals := flatten replace(Jringindex, exceptionalstoappend, oldExceptionals);
    newBoundary := flatten replace(Jringindex, boundarytoappend, oldBoundary);
    newCheckLoci := flatten replace(Jringindex, newcheckloci, oldCheckLoci);
    new DesingularizationStep from {Charts => newCharts, IntersectionMatrix => matrix(0), StepNumber => newStepNumber, Exceptionals => newExceptionals, CheckLoci => newCheckLoci, Boundary => newBoundary}
);

-- takes in and outputs desingularization step
-- performs integral closure of each chart, and composes with all the blow ups
-- pull back the divisors
normalizeStep = method();

normalizeStep(DesingularizationStep) := S -> (
    newStepNumber := S#StepNumber + 1;
    newCharts := {};
    newExceptionals := {};
    newBoundary := {};
    Cindex := 0;
    for oldChart in S#Charts do (
        icMapForChart := icMap(target(oldChart));
        newChart := icMapForChart * oldChart;
        newCharts = append(newCharts, newChart);
        
        newExceptionalsForChart := {};
        for exceptional in (S#Exceptionals)#Cindex do (
            newExceptional := icMapForChart(exceptional);
            newExceptionalsForChart = append(newExceptionalsForChart, newExceptional);
        );
        newExceptionals = append(newExceptionals, newExceptionalsForChart);

        newBoundaryForChart := divisor icMapForChart(ideal((S#Boundary)#Cindex));
        newBoundary = append(newBoundary, newBoundaryForChart);

        Cindex = Cindex + 1;
    );
    new DesingularizationStep from {Charts => newCharts, IntersectionMatrix => matrix(0), StepNumber => newStepNumber, Exceptionals => newExceptionals, Boundary => newBoundary}
)

totalTransform = method(Options => {Divisorial => false});

totalTransform(DesingularizationStep, Ideal) := opts -> (S, I) -> (
    listofCharts := S#Charts;
    outputList := {};
    if opts#Divisorial === false then (
        for phi in listofCharts do (
            outputList = append(outputList, phi(I))
        );
    );
    if opts#Divisorial === true then (
        for phi in listofCharts do (
            outputList = append(outputList, divisor(phi(I)))
        );
    );
    outputList
);

totalTransform(Ideal, Ideal) := opts -> (I, J) -> (
    S := blowupCharts(desingStep(ring(J)), J);
    totalTransform(S, I)
);

strictTransform = method(Options => {Divisorial => false});

strictTransform(DesingularizationStep, Ideal) := opts -> (S, I) -> (
    listofCharts := S#Charts;
    exceptionalDivisors := S#Exceptionals;
    numofCharts := #listofCharts;
    preoutputList := {};
    for i from 0 to (numofCharts - 1) do (
        exceptionalLoci := exceptionalDivisors#i;
        phi := listofCharts#i;
        R := target phi;
        outputIdeal := (totalTransform(S, I))#i;	
        for E in exceptionalLoci do (
		outputIdeal = saturate(outputIdeal, E)
        );
        preoutputList = append(preoutputList, outputIdeal);
    );
    outputList := {};
    if opts#Divisorial === true then (
        for J in preoutputList do (
            outputList = append(outputList, divisor(J));
        );
    );
    if opts#Divisorial === false then (
        outputList = preoutputList
    );
    outputList
);

strictTransform(Ideal, Ideal) := opts -> (I, J) -> (
    S := blowupCharts(desingStep(ring(J)), J);
    strictTransform(S, I, opts)
);

--Auxiliary methods for nonSNCLocus.

-- The method below finds all sublists of L of length k.

subLists = method();

subLists(ZZ, List) := (k, L) -> (
    -- Base cases for recursive definition.
    if k == 1 then (
        outputlist := {};
        for x in L do (
            outputlist = append(outputlist, {x})
        );
        return outputlist
    );
    if #L == k then (
        return {L}
    );
    -- Recursive step: We start with all the k-length sublists starting with x by recursively calling the function to find the k-1-length sublists of the list without x. Then we add the rest by recursively finding the k-length sublists of this punctured list. 
    if (k > 1 and #L != k) then (
        x := L#0;
        puncturedList := delete(x, L);
        TBA := {subLists(k, puncturedList), subLists(k - 1, puncturedList)};
        tobeadded1 := TBA#1;
        tobeadded2 := TBA#0;
        indexnum := #(tobeadded1) - 1;
        for i from 0 to indexnum do (
            tobeadded1 = replace(i, insert(0, x, tobeadded1#i), tobeadded1)
        );
        outputList := flatten {tobeadded1, tobeadded2};
        return outputList
    );
); 

subLists(ZZ, ZZ) := (l, k) -> (
    subLists(l, toList(1..k))
);


highcoeffComps = method();


highcoeffComps(WeilDivisor) := D -> (
    R := ring(D);
    idealList := primes D;
    redIdeal := ideal(sub(1, R)); 
    for a in idealList do (
        redIdeal = a * redIdeal;
    );
    redD := divisor(redIdeal);
    primes(D - redD)
);
--TBC add checks or make this work for divisors which are not necessarily effective. 

nonSNCLocus = method();

nonSNCLocus(Ideal) := inputIdeal -> (
    R := ring(inputIdeal);
    n := dim(R);
    outputIdeal := sub(ideal singularLocus R, R); 
    -- Base case for recursion: singular dimension 0 points. Note the divisor is irrelevant here. This is why we initially define with an ideal.
    if dim R == 0 then (
        return outputIdeal;
    );
    D := divisor(inputIdeal);
    comps := primes(D);
    -- STEP 1: Multiplying the output by the components with coefficients higher than 1. Note divisor(J) is effective.
    for J in highcoeffComps(D) do (
        outputIdeal = J * outputIdeal
    );
    -- STEP 2: Multiplying the output by the ideals of intersections of too many divisors. 
    if #comps > n then (
        for L in subLists(n + 1, comps) do (
            J := ideal(sub(0, R));
            for a in L do (
                J = J + a;
            );
            outputIdeal = J*outputIdeal
        );
    );
    -- STEP 3: Recursive step: We run the above on every component of D, and then bring the ideals back to R.
    indexnum := #comps - 1;
    for i from 0 to indexnum do (
        S := R/comps#i;
        p := map(S, R, {});
        satInput := saturate(inputIdeal, comps#i);
        restrictedIdeal := p(satInput);
        recursiveIdeal := nonSNCLocus(restrictedIdeal);
        outputIdeal = preImage(p, recursiveIdeal) * outputIdeal
    );
    -- voila 
    return outputIdeal;
);

nonSNCLocus(WeilDivisor) := D -> (
    nonSNCLocus(ideal D)
);

nonSNCLocusAlongIdeal = method();

nonSNCLocusAlongIdeal(WeilDivisor, Ideal) := (D,I) -> (
    -- check along I
    R := ring(I);
    (E,p) := restrictDivisor(D,I);
    J := nonSNCLocus(E);
    preImage(p, J)
);

nonSNCLocus(DesingularizationStep) := S -> (
    output := {};
    numCharts := #(S#Charts);
    for i from 0 to (numCharts - 1) do (
        D := (S#Boundary)#i;
        checkIdeal := (S#CheckLoci)#i;
        output = append(output, nonSNCLocusAlongIdeal(D, checkIdeal));
    );
    return output
);

-- This is not working, we need to fix nonSNCLocusAlongIdeal. 

restrictDivisor = method();

restrictDivisor(WeilDivisor, Ideal) := (D,I) -> (
    R := ring(I);
    S := R/I;
    p := map(S,R, {});

    J := ideal(D);
    if isSubset(I,J) then (
        return (divisor(p(J)), p);
    );
    Jsat := saturate(J, I);

    return (divisor(p(Jsat)), p)
)

singularIndices = method();

singularIndices(DesingularizationStep, Ideal) := (S, I) -> (
    output := {};
    L := totalTransform(S, I);
    for i from 0 to (#L) - 1 do (
        if sub(nonSNCLocus(radical L#i), ring(L#i)) != ideal(sub(1, ring(L#i))) then (
            output = append(output, i);
        );
    );
    return output
);

singularIndices(DesingularizationStep, WeilDivisor) := (S, D) -> (
    singularIndices(S, ideal(D));
);

curveResolution = method();

curveResolution(Ideal) := I -> (
    -- Checking that I defines a curve in a surface.
    R := ring(I);
    if dim R != 2 or (ideal singularLocus R != ideal(sub(1, R))) then (
        error "input is not in a smooth surface"
    );

    if I != ideal(divisor(I)) then (
        error "input does not define a curve"
    );

    -- Running the algorithm. 
    movingStep := desingStep(ring I);
    while singularIndices(movingStep, I) != {} do (
        L := totalTransform(movingStep, I);
        i := (singularIndices(movingStep, I))#0;
        singularIdeal := trim radical nonSNCLocus(radical L#i);
        idealList := primaryDecomposition(singularIdeal);
        m := idealList#0;
        movingStep = blowupCharts(movingStep, m);
    );
    movingStep
);

curveResolution(WeilDivisor) := D -> (
    curveResolution(ideal D)
);


beginDocumentation()

doc ///
    Key 
        variableChange
        (variableChange, Ideal, Symbol)
        (variableChange, PolynomialRing, Symbol)
        (variableChange, QuotientRing, Symbol)
    Headline
        Changes the variables of your ring.   
    Usage
        variableChange(I, s)
        variableChange(R, s)
        variableChange(Q, s)
    Inputs
        I: Ideal
        R: PolynomialRing
        Q: QuotientRing
        s: Symbol
    Outputs
        : Ideal
        : PolynomialRing
        : QuotientRing
    Description
        Text
         Depending on the input, this changes the variables and outputs the same object, but with enumerated variables s.  
    SeeAlso

///

doc ///
    Key 
        desingStep
        (desingStep, Ring)
    Headline
        Desingularization step from a ring.  
    Usage
        desingStep(R)
    Inputs
        R: Ring
    Outputs
        : DesingularizationStep
    Description
        Text
         Outputs the desingularization step consisting of a single chart (the identity) and no exceptional divisors.   
    SeeAlso
        DesingularizationStep

///

doc ///
    Key 
        DesingularizationStep
    Headline
        Data type for resolving singularities. 
    Description
        Text
         This is a mutable hash table, consisting of a collection of charts, exceptional divisors, an intersection matrix, and the stepn umber.   
    SeeAlso
        desingStep
        StepNumber
        Charts
        Exceptionals

///

doc ///
    Key 
        StepNumber
    Headline
        Step number in DesingularizationStep
    Description
        Text
         This keeps track of which step of the resolution we are at. 
    SeeAlso
        DesingularizationStep

///

doc ///
    Key 
        Exceptionals
    Headline
        List of exceptional divisors in DesingularizationStep
    Description
        Text
         For each chart, this gives a list of exceptional divisors intersecting that chart. 
    SeeAlso
        DesingularizationStep

///

doc ///
    Key 
        Charts
    Headline
        List of charts in DesingularizationStep
    Description
        Text
         This collects the charts in a resolution step. 
    SeeAlso
        DesingularizationStep

///

doc ///
    Key 
        IntersectionMatrix
    Headline
        Interseciton data of a resolution step. 
    Description
        Text
         This collects the intersection numbers of all the exceptional divisors in the blowup in the form of a matrix, as part of the data included in a DesingularizationStep. (Not implemented yet.)
    SeeAlso
        DesingularizationStep

///
doc ///
    Key 
        prunedringMap
        (prunedringMap, Ring)
    Headline
        the pruning isomorphism. 
    Usage
        prunedringMap(R)
    Inputs
        R: Ring
    Outputs
        : RingMap
    Description
        Text
         Outputs the isomorphism between a quotient ring and its pruning.  
    SeeAlso

///

doc ///
    Key 
        baseChangeRingMap
        (baseChangeRingMap, RingMap, Ring)
    Headline
        Base changing a ring map.
    Usage
        baseChangeRingMap(f, R)
    Inputs
        f: RingMap
        R: Ring
    Outputs
        : RingMap
    Description
        Text
         Outputs the map obtained by base changing the ring map to R, whenever possible.  
    SeeAlso

///

doc ///
    Key 
        inverseMap
        (inverseMap, RingMap)
    Headline
        Inverting ring maps
    Usage
        inverseMap(f)
    Inputs
        f: RingMap
    Outputs
        : RingMap
    Description
        Text
         Finds the inverse map of a given isomorphism of rings.   
    SeeAlso

///
doc ///
    Key 
        blowupCharts
        (blowupCharts, Ideal, Symbol)
        (blowupCharts, DesingularizationStep, Ideal)
    Headline
        Blowing up ideals of affine varieties and charts.  
    Usage
        blowupCharts(J, n, Exceptional => b)
        blowupCharts(J, Exceptional => b)
        blowupCharts(I, s, Exceptional => b)
        blowupCharts(I, n, s, Exceptional => b)
        blowupCharts(S, J)
    Inputs
        J: Ideal
        n: ZZ
        s: Symbol
        b: Boolean
        S: DesingularizationStep
    Outputs
        : List
        : List
        : List
        : List
        : DesingularizationStep
    Description
        Text
         Finds the charts and exceptional divisors of the blowup of an affine scheme along an ideal. Outputs the n'th chart of the blowup of ring(J) along J. It will output a list of ring maps, together with ideals of the target which define the exceptional locus. The optional symbol input allows you to choose which variables are introduced in the blowup. (the default is "u".) The option determines if the exceptional divisors are included in the output. Alternatively, this will replace a disingularization step by one obtained by blowing up the ideal J of one of the charts. 
    SeeAlso
        Exceptional

///

doc ///
    Key 
        Exceptional
    Headline
        Exceptional option for blowupCharts. 
    Description
        Text
         This option decides if the blowupCharts method output includes exceptional divisors. 
    SeeAlso
        blowupCharts

///

doc ///
    Key 
        totalTransform
        (totalTransform, Ideal, Ideal)
        (totalTransform, DesingularizationStep, Ideal)
        [totalTransform, Divisorial]
    Headline
        Transporting ideals along blowups.
    Usage
        totalTransform(I, J, Divisorial => b)
        totalTransform(S, I)
    Inputs
        I: Ideal
        J: Ideal
        b: Boolean
        S: DesingularizationStep
    Outputs
        : List
        : List
    Description
        Text
         Computes the total transform of I in the blowup along J. If X' -> X is the blowup and a is the ideal, this computes the local description of a*O_X'. If Divisiorial is set to true, this outputs the associated divisor (resp. list of divisors). If inputting a desingularization step, it will output the transform in each chart. 
    SeeAlso
        Divisorial

///

doc ///
    Key 
        strictTransform
        (strictTransform, Ideal, Ideal)
        (strictTransform, DesingularizationStep, Ideal)
        [strictTransform, Divisorial]
    Headline
        The non-exceptional part of the total transform. 
    Usage
        strictTransform(I, J, Divisorial => b)
        strictTransform(S, I)
    Inputs
        I: Ideal
        J: Ideal
        n: ZZ
        b: Boolean
    Outputs
        : Ideal
        : List
    Description
        Text
         Computes the strict transform of I in the blowup along J. That is, it factors the exceptional part out of the total transform. The option determines whether to output an ideal or the associated divisor. Similarly if putting in a desingularization step and an ideal of the base, it transforms the ideal in each of the charts. 
    SeeAlso
        Divisorial
///

doc ///
    Key 
        Divisorial
    Headline
        Option for outputting divisors. 
    Description
        Text
         This option controls whether the output of strictTransform or totalTransform is a divisor or an ideal. 
    SeeAlso
        strictTransform
        totalTransform

///

doc ///
    Key 
        nonSNCLocus
        (nonSNCLocus, Ideal)
        (nonSNCLocus, WeilDivisor)
    Headline
        Finds the locus where an effective divisor isn't SNC
    Usage
        nonSNCLocus(I)
        nonSNCLocus(D)
    Inputs
        I: Ideal
        D: WeilDivisor
    Outputs
        : Ideal
    Description
        Text
         This method finds the closed subset where an effective divisor is not SNC, given by the ideal of this closed subset, possibly with mulitplicities. Note that this is the non-SNC locus, meaning that components with coefficients >1 will contribute to this locus. This will also include the singular locus of the ambient ring. 
    SeeAlso
        totalTransform
///

doc ///
    Key 
        singularIndices
        (singularIndices, DesingularizationStep, Ideal)
        (singularIndices, DesingularizationStep, WeilDivisor)
    Headline
        Finds the charts where the total transform is not SNC. 
    Usage
        singularIndices(S, I)
        singularIndices(S, D)
    Inputs
        S: DesingularizationStep
        I: Ideal
        D: WeilDivisor
    Outputs
        : List
    Description
        Text
         This method finds the charts in S where the total transform of I is not SNC. 
    SeeAlso
        totalTransform
///

doc ///
    Key 
        curveResolution
        (curveResolution, Ideal)
        (curveResolution, WeilDivisor)
    Headline
        Finds an embedded resolution of a curve (effective weil divisor) in a smooth surface.
    Usage
        curveResolution(I)
        curveREsolution(D)
    Inputs
        I: Ideal
        D: WeilDivisor
    Outputs
        : DesingularizationStep
    Description
        Text
         This repeatedly blows up non-SNC points until the total transform of D has SNC support. 
    SeeAlso
        totalTransform
///

TEST /// --check #0 (variableChange, Ring, Symbol) checking that it outputs an isomorphism.  
R = QQ[x,y,z];
phi = variableChange(R, L9);
phinverse = inverseMap(phi); 
assert(ker phi == ideal(sub(0,source phi)));
assert(ker phinverse == ideal(sub(0,source phinverse)))
///

TEST /// --check #1 (totalTransform, Ideal) checking that simple node is resolved. 
needsPackage "Divisor";
k = GF(5);
R = k[x,y];
m = ideal(x,y);
I = ideal(y^3 - (x + y)*(x - y));
L = totalTransform(I, m);

singcharts = 0;

for a in L do (
    if isSNC(divisor(a)) != true then (
        singcharts = singcharts + 1;
    );
);

assert(singcharts == 0);
///

TEST /// --check #2 (blowupCharts, Ideal) blowing up trivial ideals.
R = QQ[x,y,z]/ideal(x^2 + y^2 - z);
--t1 = ideal(sub(0, R)); TBC: What is going on here? Make an error or something to fix this. 
t2 = ideal(sub(1, R));
t3 = ideal(x); 

-- phi1 = inverseMap(((blowupCharts(t1)#0))#0);
phi2 = inverseMap(((blowupCharts(t2))#0)#0);
phi3 = inverseMap(((blowupCharts(t3))#0)#0);

--assert(ker phi1 == ideal(sub(0,source phi1)));
assert(ker phi2 == ideal(sub(0,source phi2)));
assert(ker phi3 == ideal(sub(0,source phi3)));
///

TEST /// --check #3 (strictTransform, DesingularizationStep, Ideal) resolving the Whitney umbrella
R = QQ[x,y,z];
J = ideal(x,y); -- center of blowup
I = ideal(x^2*z - y^2); -- whitney umbrella

S = desingStep(R);
T = blowupCharts(S, J);

L = strictTransform(T, I);

for a in L do (
    assert(ideal singularLocus a == ideal(sub(1, ring a)));
);
///

TEST /// --check #4 (nonSNCLocusAlongIdeal, WeilDivisor, Ideal) 
needsPackage "Divisor";
R = QQ[x,y];
I1 = ideal(y-x^2);
J1 = ideal(y);
D1 = divisor(I1*J1);
a1 = nonSNCLocusAlongIdeal(D1,J1); -- expect (x,y)

I2 = ideal(y-x^2*(x-1));
J2 = ideal(y);
D2 = divisor(I2*J2);
a2 = nonSNCLocusAlongIdeal(D2,J2); -- expect (x,y)

I3 = ideal((y-2*x)*(y-3*x));
J3 = ideal(y-x);
D3 = divisor(I3*J3);
a3 = nonSNCLocusAlongIdeal(D3,J3); -- expect (x,y)

assert(a1 == ideal(x,y));
assert(a2 == ideal(x,y));
assert(a3 == ideal(x,y));
///

TEST /// --check #5 (normalizeStep, DesingularizationStep) 
R = QQ[x,y,z]/(x^2*z-y^3);
I = ideal(z-1);

S = desingStep(R);
S#Exceptionals = {{I}};

normalizeStep(S);
///

end



