needsPackage("Desingularization");
R = QQ[x,y];
--m = ideal(x,y);

S = desingStep(R);
--T = blowupCharts(S, m);

isTerminal = method();
isTerminal(DesingularizationStep, Ideal) := (S, I) -> (
    singularindices := {};
    L := strictTransform(S, I);
    for i from 0 to (#L) - 1 do (
        if ideal(singularLocus(L#i)) != ideal(sub(1, ring(L#i))) then (
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

highernodeResolution = method();
highernodeResolution(ZZ) := r -> (
    I := ideal(y^2 - x^r);
    movingStep := S; 
    while (isTerminal(movingStep, I) === true) == false do (
        L := strictTransform(movingStep, I);
        singularIndices = isTerminal(movingStep, I);
        i := singularIndices#0;
        singularIdeal := ideal(singularLocus(L#i));
        idealList := primaryDecomposition(singularIdeal);
        m := radical(idealList#0);
        movingStep = blowupCharts(movingStep, m);
    );
    movingStep
);
