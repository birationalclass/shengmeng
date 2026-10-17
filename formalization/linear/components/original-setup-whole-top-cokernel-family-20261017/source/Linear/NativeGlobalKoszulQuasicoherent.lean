module
public import Linear.NativeIntegerFreeTwistRegrading
public import Linear.NativeProjectiveFiniteGradedQuasicoherent
public import Linear.NativeProjectiveKoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑] [IsNoetherianRing S]

/-- Quasicoherence of the SAME ORIGINAL finite shifted-free associated
sheaf at EVERY integer twist,derived by original identity regrading.
No quasicoherence or affine comparison certificate is assumed. -/
theorem nativeIntegerShiftedFree_isQuasicoherent
    {I J : Type} [Fintype I] [DecidableEq I] (w : I → ℤ)
    (a : J → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range a) = ⊤) (k : ℤ) :
    (nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k).IsQuasicoherent := by
  letI := integerShiftedFreeDecomposition 𝓑 (fun i => w i-k)
  have hz := nativeFiniteGraded_isQuasicoherent 𝓑
    (integerShiftedFreePiece 𝓑 (fun i => w i-k))
    (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun i => w i-k)) a ha hgen
  exact (SheafOfModules.isQuasicoherent (Proj 𝓑).ringCatSheaf).prop_of_iso
    (nativeIntegerFreeTwistRegradingIso 𝓑 w k) hz

/-- Every actual ORIGINAL global Koszul term is quasicoherent for ALL
integer twists. This is a property of the source,not an assumption on N. -/
theorem nativeProjectiveKoszulTerm_isQuasicoherent {J : Type}
    (a : J → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range a) = ⊤) (r q p : ℕ) (k : ℤ) :
    (nativeProjectiveKoszulTerm 𝓑 r q p k).IsQuasicoherent := by
  exact nativeIntegerShiftedFree_isQuasicoherent 𝓑
    (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)) a ha hgen k

/-- Actual restriction of the SAME ORIGINAL global Koszul term to ANY
original open immersion is quasicoherent,by native restriction preservation. -/
theorem nativeProjectiveKoszulTerm_restrict_isQuasicoherent {J : Type}
    (a : J → S) (ha : ∀ i, a i ∈ 𝓑 1)
    (hgen : Algebra.adjoin K (Set.range a) = ⊤) (r q p : ℕ) (k : ℤ)
    {Y : Scheme} (f : Y ⟶ Proj 𝓑) [IsOpenImmersion f] :
    ((Scheme.Modules.restrictFunctor f).obj
      (nativeProjectiveKoszulTerm 𝓑 r q p k)).IsQuasicoherent := by
  letI := nativeProjectiveKoszulTerm_isQuasicoherent 𝓑 a ha hgen r q p k
  infer_instance

end LinearStudy
