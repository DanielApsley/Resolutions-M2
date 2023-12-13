needsPackage("Desingularization");
needsPackage("Divisor")
--R = QQ[x,y];
--m = ideal(x,y);

--S = desingStep(R);
--T = blowupCharts(S, m);

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

-- Checks if the strict transform is smooth in each chart of a Step. 

planecurveResolution = method();
planecurveResolution(Ideal) := I -> (
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

testRing = QQ[x,y];
D1 = divisor(ideal(y*(y - x^2)));
D2 = divisor(ideal(y*x*(x + y)));
D3 = divisor(x^3*y^4);

-- nonSNCLocus(D1);

cusp = ideal(y^2 - x^3);
cuspresolution = planecurveResolution(cusp);

-- TBC Make the above work for D1. The recursive step misses multiplicities by taking divisors. 

