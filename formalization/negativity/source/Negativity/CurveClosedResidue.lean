module

public import Negativity.CurveFiberPrimes
public import Negativity.DivisorPullback
public import Negativity.CurveFunctionField
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory IsDedekindDomain
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.Opens) (hU : IsAffineOpen U) (k : Type u) [Field k]
    (b : Y ⟶ Spec (.of k))

local instance : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
theorem curve_chart_base_scalar_tower :
    letI : Algebra k Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ b)).hom.toAlgebra
    letI : Algebra k Γ(X, f ⁻¹ᵁ U) :=
      (Spec.preimage ((hU.preimage f).fromSpec ≫ f ≫ b)).hom.toAlgebra
    IsScalarTower k Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let : Algebra k Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ b)).hom.toAlgebra
  let : Algebra k Γ(X, f ⁻¹ᵁ U) :=
    (Spec.preimage ((hU.preimage f).fromSpec ≫ f ≫ b)).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  symm
  change Spec.map (Spec.preimage (hU.fromSpec ≫ b) ≫ f.app U) = _
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
  have hs := hU.SpecMap_appLE_fromSpec f (hU.preimage f) le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at hs
  rw [← Category.assoc, hs, Category.assoc]

theorem curve_chart_base_finiteType [LocallyOfFiniteType b] :
    letI : Algebra k Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ b)).hom.toAlgebra
    Algebra.FiniteType k Γ(Y, U) := by
  let : Algebra k Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ b)).hom.toAlgebra
  have hc : (Spec.preimage (hU.fromSpec ≫ b)).hom.FiniteType := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [Spec.map_preimage]
    infer_instance
  exact hc

include hU
omit [IsAffineHom f] in
/-- Final theorem: for an actual finite dominant map of normal curves over
an algebraically closed field, every actual fiber prime has relative
residue degree one. Actual base algebras and compatibility come from the
Scheme section-map square and Zariski's lemma. No separability is required. -/
theorem finite_normal_curve_relative_residueDegree_one
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite f] [IsDominant f] [IsAlgClosed k] [LocallyOfFiniteType b]
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    (hnX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hdX : Order.krullDim X ≤ 1) (hdY : Order.krullDim Y ≤ 1) :
    letI : Algebra k Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ b)).hom.toAlgebra
    letI : Algebra k Γ(X, f ⁻¹ᵁ U) :=
      (Spec.preimage ((hU.preimage f).fromSpec ≫ f ≫ b)).hom.toAlgebra
    letI := normal_curve_affine_dedekind Y hnY hdY U hU
    letI := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
    ∀ (p : HeightOneSpectrum Γ(Y, U)) (q : p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ U)),
      q.1.inertiaDeg Γ(Y, U) = 1 := by
  let : Algebra k Γ(Y, U) := (Spec.preimage (hU.fromSpec ≫ b)).hom.toAlgebra
  let : Algebra k Γ(X, f ⁻¹ᵁ U) :=
    (Spec.preimage ((hU.preimage f).fromSpec ≫ f ≫ b)).hom.toAlgebra
  have := normal_curve_affine_dedekind Y hnY hdY U hU
  have := normal_curve_affine_dedekind X hnX hdX (f ⁻¹ᵁ U) (hU.preimage f)
  have := dominant_curve_chart_torsionFree f U
  have := curve_chart_base_scalar_tower f U hU k b
  have := curve_chart_base_finiteType U hU k b
  have : LocallyOfFiniteType (f ≫ b) := inferInstance
  have := curve_chart_base_finiteType (f ⁻¹ᵁ U) (hU.preimage f) k (f ≫ b)
  intro p q
  have he := Ideal.inertiaDeg_tower (R := k) p.asIdeal q.1
  have hp := closedPoint_residueDegree_one k Γ(Y, U) p
  have hq := closedPoint_residueDegree_one k Γ(X, f ⁻¹ᵁ U) (heightOnePrimeAbove p q)
  change q.1.inertiaDeg k = 1 at hq
  simpa only [hp, hq, one_mul] using he.symm

end
end Negativity
