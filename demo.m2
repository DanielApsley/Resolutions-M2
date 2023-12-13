needsPackage("Desingularization");
needsPackage("Divisor")
--R = QQ[x,y];
--m = ideal(x,y);

--S = desingStep(R);
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

testRing = QQ[x,y];
D1 = divisor(ideal(y*(y - x^2)));
D2 = divisor(ideal(y*x*(x + y)));
D3 = divisor(x^3*y^4);

-- nonSNCLocus(D1);

-- TBC Make the above work for D1. The recursive step misses multiplicities by taking divisors. 

