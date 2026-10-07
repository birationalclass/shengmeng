# Milestone 68: simultaneous good chart point and its actual local parameter pullback

The exact Linearity Theorem remains unproved.

The actual rational chart map is proved injective. A nonempty principal open can be chosen simultaneously smooth over the base field and formally unramified for this actual map. A rational point is then constructed which is smooth in the source, has smooth image, and lies in the unramified locus. The last assertion is derived for the same point, using injectivity and a nonzero product avoiding both excluded closed sets.

The genuine local ring map at that point and its image is constructed by mathlib localization. It is essentially of finite type and formally unramified. Every supplied generating family of the target maximal ideal pulls back to a generating family of the source maximal ideal. Instantiating this with the original homogeneous endomorphism and totally invariant integral variety discharges these local map properties; it does not construct a whole general fiber or a particular parameter family.

Remaining obligations include the comparison to the ambient rational polynomial local quotient maps used in the relative Jacobian application, choosing a complete general projective fiber in the good locus, its cardinality/degree and dimension comparisons, uniform global duality lifting, and actual geometric Bezout. There is no claim that one good point proves any of these whole-fiber statements.

Seven new public modules were privately compiled with exact source hashes and only propext, Classical.choice and Quot.sound. The full project build and axiom audit determine the checkpoint's final recorded status.
