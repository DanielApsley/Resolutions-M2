# Resolutions-M2
Some stuff to compute resolutions of singularities in Macaulay2. As is it roughly computes the charts of an embedded resolution of a curve in a smooth surface. Desingularization.m2 is the main package, and demo.m2 contains the methods which can compute embedded resolutions. b-sides.m2 is for methods which aren't yet used in the package. 

So far there are some inefficiencies and issues we'd like to improve. For example, we check the singular locus in each chart which is quite redundant. We also don't yet expand the base field, so there's no guarantee the exceptional divisors are geometrically irreducible. 

Next, we would like to track more of the data of this embedded resolution. In particular, we would like to track the intersection data to find multiplier ideals, dual graphs, etc. 

Once this is done, we will try and implement more general resolutions starting with curves in singular surfaces. 

Throughout, the documentation and testing will be updated to reflect the state of the package. 
