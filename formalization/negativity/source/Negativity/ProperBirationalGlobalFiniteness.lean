module

public import Negativity.ProperBirationalFunctions
public import Negativity.FiniteNormalizationAlgebra
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: actual global functions on a proper birational source
are a finite module over any affine finite-type integral base over a
perfect field. The base need not be normal and the source need not be
affine. Properness makes every actual section integral; the actual
birational function-field map embeds them into the proved finite
normalization, where Noetherianity supplies module finiteness. -/
theorem actual_proper_birational_global_functions_finite
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsAffine Y]
    (k : Type u) [Field k] [PerfectField k]
    [Algebra k Γ(Y, ⊤)] [Algebra.FiniteType k Γ(Y, ⊤)]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) :
    letI : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := by
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : Nonempty (f ⁻¹ᵁ (⊤ : Y.Opens)) := ⟨⟨genericPoint X, trivial⟩⟩
  let R := Γ(Y, ⊤)
  let S := Γ(X, ⊤)
  let : Algebra R S := f.appTop.hom.toAlgebra
  let : IsDominant f := birationalMorphism_dominant f hf
  have : IsFractionRing R Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y ⊤ (isAffineOpen_top Y)
  have : Module.Finite R (integralClosure R Y.functionField) :=
    finiteType_perfectField_integralClosure_finite k R Y.functionField Y.functionField
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let e : Y.functionField ≃+* X.functionField := RingEquiv.ofBijective
    (dominantFunctionFieldMap f) (birational_functionField_pullback_bijective f hf)
  let j : S →ₐ[R] Y.functionField := {
    __ := e.symm.toRingHom.comp (X.germToFunctionField ⊤).hom
    commutes' := by
      intro r
      apply e.injective
      change e (e.symm (X.germToFunctionField ⊤ (f.appTop r))) =
        e (algebraMap R Y.functionField r)
      rw [RingEquiv.apply_symm_apply]
      exact (dominantFunctionFieldMap_germ f ⊤ r).symm }
  have hj : Function.Injective j :=
    e.symm.injective.comp (X.germToFunctionField_injective ⊤)
  have : Algebra.IsIntegral R S :=
    algebraMap_isIntegral_iff.mp (isIntegral_appTop_of_universallyClosed f)
  let jc : S →ₐ[R] integralClosure R Y.functionField := {
    toFun s := ⟨j s, (Algebra.IsIntegral.isIntegral s).map j⟩
    map_zero' := Subtype.ext (map_zero j)
    map_one' := Subtype.ext (map_one j)
    map_add' s t := Subtype.ext (map_add j s t)
    map_mul' s t := Subtype.ext (map_mul j s t)
    commutes' r := Subtype.ext (j.commutes r) }
  apply Module.Finite.of_injective jc.toLinearMap
  intro s t hst
  exact hj (congrArg Subtype.val hst)

end
end Negativity
