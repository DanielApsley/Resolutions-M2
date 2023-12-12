needsPackage("Desingularization");
needsPackage("Divisor")
R = QQ[x,y];
--m = ideal(x,y);

S = desingStep(R);
--T = blowupCharts(S, m);

isTerminal = method();
isTerminal(DesingularizationStep, Ideal) := (S, I) -> (
    singularindices := {};
    L := strictTransform(S, I);
    for i from 0 to (#L) - 1 do (
        if sub(ideal(singularLocus(L#i)), ring(L#i)) != ideal(sub(1, ring(L#i))) then (
            singularindices = append(singularindices, i);
        );
    );
    if singularindices == {} then (
        return true;
    );
    if singularindices != {} then (
        return singularindices;
    );
);

-- Checks if the strict transform is smooth in each chart of a Step. 

planecurveResolution = method();
planecurveResolution(Ideal) := I -> (
    movingStep := desingStep(ring I);
    while (isTerminal(movingStep, I) === true) == false do (
        L := strictTransform(movingStep, I);
        singularIndices = isTerminal(movingStep, I);
        i := singularIndices#0;
        singularIdeal := trim ideal(singularLocus(L#i));
        idealList := primaryDecomposition(singularIdeal);
        m := radical(idealList#0);
        movingStep = blowupCharts(movingStep, m);
    );
    movingStep
);

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

nonSNCLocus = method();

nonSNCLocus(Ideal) := I -> (
    R := ring(I);
    -- check if R defines a smooth surface
    if (dim(R) != 2) or (ideal(singularLocus(R)) != ideal(sub(1, R))) then (
        error "expected divisor on smooth surface"
    );
    -- TBC possibly restricting to I being a divisor.
    -- find the singular locus of each component
    components := primaryDecomposition(I);
    outputideal := ideal(sub(1, R));
    for J in components do (
        outputideal = outputideal * (ideal singularLocus J);
    );
    -- find the singular locus of each intersection
    -- find the triple intersection locus

);

-- Should find the closed subset where the divisor does not have SNC support, given by some ideal of this closed subset, possibly with mulitplicities. It is initially defined with an ideal in order to make sense of the dim R = 0 base case, since divisors dont make sense in dim = 0. 

nonSNCLocus(Ideal) := inputIdeal -> (
    R := ring(inputIdeal);
    n := dim(R);
    outputideal := ideal singularLocus R; 
    -- Base case for recursion: singular dimension 0 points. Note the divisor is irrelevant here.
    if dim R == 0 then (
        return outputideal;
    );
    D := divisor(inputIdeal);
    comps := primes(D);
    indexnum := #comps - 1;
    -- Multiplying the output by the ideals of intersections of too many divisors. 
    if #comps > n then (
        for L in subLists(n + 1, comps) do (
            J := ideal(sub(0, R));
            for a in L do (
                J = J + a;
            );
            outputideal = J*outputideal
        );
    );
    -- Recursive step: We run the above on every component of D.
    for i from 1 to indexnum do (
        S := R/comps#i;
        SComps := {};
        for I in delete(comps#i, comps) do (
            SComps = append(SComps, sub(I, S))
        );
        F := divisor(SComps#0);
        for i from 1 to #comps - 2 do (
            F = F + divisor(SComps#i);
        );
        -- F is the divisor obtained by restricting all the components of D but comps#i to comps#i. 
        recursiveIdeal := sub(nonSNCLocus(ideal F), S);
        p := map(S, R, {});
        outputideal = preImage(p, recursiveIdeal) * outputideal;
    );
    return outputideal
);

nonSNCLocus(WeilDivisor) := D -> (
    nonSNCLocus(ideal D)
);

D1 = divisor(ideal(y*(y - x^2)));
D2 = divisor(ideal(y*x*(x + y)));

-- TBC Make the above work for D1. The recursive step misses multiplicities by taking divisors. 

