module
public import Linear.NativeIntegerTwistInternalExtVanishing
public import Linear.SchemeModuleBiproductInternalExt
public import Linear.SchemeModuleFiniteFreeFrameInternalExt
public import Linear.NativeProjectiveKoszulComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local irreducible] nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf
  integerShiftedFreePiece nativeProjectiveRingIntegerPiece

/-- ALL ACTUAL original global Koszul source terms have vanishing positive
INTERNAL SHEAF Ext for ANY coefficient and EVERY integer twist. Use SAME
proved original term/biproduct iso and actual native rank-one chart frames. -/
theorem nativeProjectiveKoszulTermInternalExt_succ {ι : Type} (a : ι → S)
    (ha : ∀ i, a i ∈ 𝓑 1) (hgen : Algebra.adjoin K (Set.range a) = ⊤)
    (r d p : ℕ) (k : ℤ) (N : (AlgebraicGeometry.Proj 𝓑).Modules) (q : ℕ) :
    IsZero (schemeModuleInternalExt (nativeProjectiveKoszulTerm 𝓑 r d p k) N (q+1)) := by
  let e := nativeProjectiveKoszulTermTwistIso 𝓑 r d p k
  have hz : IsZero (schemeModuleInternalExt
      (biproduct (fun _ : Set.powersetCard (Fin r) p =>
        nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
          (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(p:ℤ)*(d:ℤ)))) N (q+1)) :=
    schemeModuleBiproductInternalExt_isZero N _ (q+1)
      (fun _ => nativeIntegerTwistInternalExt_succ 𝓑 a ha hgen _ N q)
  exact IsZero.of_iso hz (schemeModuleInternalExtSourceIso e N (q+1))

end LinearStudy
