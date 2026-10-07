# Milestone 26: local-to-global socles and affine point relation

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

The annihilator of a finitely generated ideal is proved to commute with actual localization. The proof first clears denominators for a principal ideal, then uses finite intersection preservation for a finite generating set. Localization of the nilradical is identified using the actual radical comparison theorem. Maximal-localization equality glues local socle generation to global generation.

`affine_polynomial_weighted_point_relation` constructs actual maximal residue maps and nonzero weights, whose weighted evaluations vanish whenever `degree(Theta)+degree(f)<sum(deg(P_i)-1)`. Its explicit inputs are positive degrees, regular highest homogeneous parts, their origin-only zero locus, and local nilradical-annihilator generation by the image of the chosen polynomial `Theta` at every maximal localization. Neither the weights nor the vanishing relation are inputs.

This route uses the constructed algebraic perfect pairing, so a separate identification with geometric Grothendieck residues is no longer necessary to obtain the required relation. The outstanding geometric obligations include highest-part regularity, source and target smooth charts, completion-to-local-fiber comparison and transport of the proved relative Jacobian result to the actual local fiber. They have not been replaced by assumptions in the final Linearity Theorem.

Primary reused APIs: actual pinned `IsLocalization.map_inf`, `IsLocalization.map_radical`, `IsLocalization.map_eq_zero_iff`, `Ideal.eq_of_localization_maximal`. Their full types and the official `LocalProperties/Basic` and `LocalProperties/Submodule` documentation were inspected before the new bridge.
