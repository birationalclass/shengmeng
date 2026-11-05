module
public import Linear.NativeProjectiveTwistFraction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (a : S) (ha : a ∈ 𝓑 1) (m : ℕ)
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- Actual positive twist trivialization on EVERY original open set
where a is nonvanishing. Both directions use actual module fractions
and actual native structure-ring actions. -/
def nativeProjectiveTwistSectionEquiv (k : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal) :
    nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k U ≃ₗ[
        (ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U]
      nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (k+(m : ℤ)) U where
  toFun f := ⟨fun p => nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m (f.1 p),
    nativeProjectiveTwistLocalFraction_forward 𝓑 a ha m k hp f.property⟩
  invFun f := ⟨fun p => (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm (f.1 p),
    nativeProjectiveTwistLocalFraction_backward 𝓑 a ha m k hp f.property⟩
  left_inv f := by
    apply Subtype.ext
    funext p
    exact (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m).symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    funext p
    exact (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m).apply_symm_apply _
  map_add' f g := by
    apply Subtype.ext
    funext p
    exact (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m).map_add _ _
  map_smul' r f := by
    apply Subtype.ext
    funext p
    exact (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a (hp p) m).map_smul (r.1 p) (f.1 p)

/-- The actual twist trivializations commute with every original open
restriction inside the degree-one chart, including their native ring maps. -/
theorem nativeProjectiveTwistSectionEquiv_restrict (k : ℤ)
    {U V : (Opens (ProjectiveSpectrum.top 𝓑))ᵒᵖ} (i : U ⟶ V)
    (hp : ∀ p : U.unop, a ∉ p.1.asHomogeneousIdeal)
    (f : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k U) :
    (nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k+(m : ℤ))).map i
        (nativeProjectiveTwistSectionEquiv 𝓑 a ha m k U hp f) =
      nativeProjectiveTwistSectionEquiv 𝓑 a ha m k V (fun p => hp (i.unop p))
        ((nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
          (nativeProjectiveRingIntegerPiece_graded 𝓑) k).map i f) := by
  apply Subtype.ext
  funext p
  rfl

end LinearStudy
