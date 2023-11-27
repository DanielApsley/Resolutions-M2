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

-- Checks if the strict transform is smooth in each chart of a Step. 

highernodeResolution = method();
highernodeResolution(ZZ) := r -> (
    I := ideal(y^2 - x^r);
    movingStep := S; 
    while (isTerminal(movingStep, I) === true) == false do (
        L := strictTransform(movingStep, I);
        singularIndices = isTerminal(movingStep, I);
        i := singularIndices#0;
        singularIdeal := trim ideal(singularLocus(L#i));
        idealList := primaryDecomposition(singularIdeal);
        m := radical(idealList#0);
        movingStep = blowupCharts(movingStep, m);
        if movingStep#StepNumber > r - 1 then (
            error "this should be done by now. What is happening??"
        )
    );
    movingStep
);

-- Running this for r = 6 gives an endless loop, and this is very slow.  
