# Milestone 36: actual finite thickened power-series quotients

From coordinate powers in an actual ideal I in R[[z]], every quotient class is the image of a polynomial, proved by actual finite-box truncation. The coordinate images satisfy monic power equations. The pinned mathlib `fg_adjoin_of_finite` theorem and the surjective polynomial evaluation prove Module.Finite R (R[[z]]/I).

The theorem applies to arbitrary commutative coefficient rings and finite nonempty coordinate sets; neither field coefficients nor flatness is assumed. The geometric source provides a power of the coordinate ideal contained in I, to which the final theorem applies. Flatness and geometric derivation of that containment remain separate obligations.

Discovery: inspected the official pinned 2a885768 mathlib IntegralClosure/IsIntegral/Basic.lean online and locally. Reused fg_adjoin_of_finite and actual algebra-adjoin/evaluation and module-finiteness interfaces; no arbitrary downloaded code was run. No claim of global Linearity Theorem completion.
