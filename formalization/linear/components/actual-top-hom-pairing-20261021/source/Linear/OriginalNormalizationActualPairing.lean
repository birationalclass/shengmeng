module
public import Linear.OriginalNormalizationActualTopDuality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
/-- The additive functional of the SAME actual top-H dual comparison for
ORIGINAL V. Evaluate it on a homogeneous Hom coefficient to get the pairing.
Canonical-dualizing identification and normalized trace compatibility OPEN. -/
def originalNormalizationActualTopHomPairing {n : ℕ}
    (V : IntegralProjectiveEquations n) (q : ℕ)
    (L : Fin (q+2) → CoordinateRing n) (hL : ∀ i,(L i).IsHomogeneous 1)
    (hfinite : (projectiveLinearNormalizationMap V L).Finite) (k : ℤ) :=
  (originalNormalization_actualTopHomDualIso V q L hL hfinite k).hom.hom
end LinearStudy
