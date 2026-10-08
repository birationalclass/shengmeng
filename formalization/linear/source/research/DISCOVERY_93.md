# Actual common Jacobian through the rational chart

Primary online discovery searched mathlib's MvPowerSeries substitution and
evaluation code, and original mathlib repositories. The generated substitution
documentation and exact pinned raw-source URL could not be fetched by the web
tool; this is a discovery limitation, not proof of absence of code.

- https://github.com/leanprover-community/mathlib4
- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/RingTheory/MvPowerSeries/Evaluation.lean
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPowerSeries/Substitution.html

Read the full pinned declaration MvPowerSeries.substAlgHom_coe in
Mathlib/RingTheory/MvPowerSeries/Substitution.lean at pinned revision
2a885768dae569d938bb9ff3474da6a8753bb90a. Reuse it to compare the actual polynomial
rational pullback and formal substitution. Reuse local verified
RationalUnramifiedParameters, RationalSmoothRadical, PolynomialLocalParameters,
LocalQuotientMaximalIdeal, FirstJetNormalForm, SmoothProjectiveFormalSocle and
SmoothPolynomialFiber; do not replace their actual maps with independent ones.

The new bridge derives the formal radical and parameter-generation hypotheses
from actual source/target local equations, normalized target polynomial first
jets, the actual ideal-power sandwich and genuine rational local
unramification. Essential finite type is constructed automatically. It proves
the SAME common polynomial Theta=det(d p_normal/d z_normal), rather than the
Jacobian of a separately chosen local equation family, generates the formal
and actual Artinian localized polynomial-fiber annihilator and is nonzero.

This remains a CONDITIONAL geometric bridge: the original whole-fiber
coordinate transformations and ideal-power inequalities still have to be
assembled into these inputs. It is not the completed original relation.
The homogeneous extension, Bertini d-fiber union, Section 4 and the actual
intersection inequality remain open. The full theorem remains UNPROVED.
