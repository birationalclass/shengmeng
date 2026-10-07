# Milestone 37: actual reduction of a formal coordinate thickening

For a domain coefficient ring R and J = (z_i) in R[[z]], the sandwich J^e <= I <= J with e > 0 proves radical(I)=J. The actual constant-coefficient map constructs a surjective R-algebra map R[[z]]/I -> R. Its kernel is proved to equal the nilradical by the library radical-of-surjective-quotient formula. No reduction isomorphism or kernel identification is assumed.

This applies to the manuscript coefficient ring C[[s]]. It does not prove the geometric sandwich or finite flatness. The finite-module result in milestone 36 is independent; formal regularity and global lifting remain unfinished.

Discovery: official pinned mathlib Ideal/Operations.lean inspected online, and Ideal/Maps.lean plus Quotient/Operations.lean locally. Reuses radical_pow, radical_mono, kernel primeness, ker_quotient_lift and map_radical_of_surjective. No new axiom and no global theorem completion claim.
