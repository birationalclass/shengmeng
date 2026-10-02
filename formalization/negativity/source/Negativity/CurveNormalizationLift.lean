module

public import Negativity.NormalizationLift
public import Negativity.CurveNormalization
public import Negativity.FunctionFieldFunctoriality
public import Negativity.ProperCurveFinite
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem birational_functionFieldMap_bijective
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (f : C ⟶ X) [IsDominant f] (hf : BirationalMorphism f) :
    Function.Bijective (dominantFunctionFieldMap f) := by
  have := birationalMorphism_generic_stalk_isIso f hf
  let φ : X.functionField ⟶ C.functionField :=
    (X.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
      f.stalkMap (genericPoint C)
  have : IsIso φ := by dsimp only [φ]; infer_instance
  exact ConcreteCategory.bijective_of_isIso φ

/-- Final theorem: a proper dominant map of any complete integral curves
lifts to an actual finite dominant map of their actual normalizations.
The square commutes and the full function-field degree is unchanged.
Neither original curve is assumed normal or smooth; inseparable maps
are included over an algebraically closed field of arbitrary characteristic. -/
theorem complete_integral_curves_normalization_lift_degree
    {C X : Scheme.{u}} [IsIntegral C] [IsIntegral X]
    (hdC : Order.krullDim C = 1) (hdX : Order.krullDim X = 1)
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : X ⟶ Spec (.of k)) [IsProper b]
    (f : C ⟶ X) [IsProper f] [IsDominant f] :
    let nC := C.fromSpecStalk (genericPoint C)
    let nX := X.fromSpecStalk (genericPoint X)
    letI : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
    ∃ l : nC.normalization ⟶ nX.normalization,
      l ≫ nX.fromNormalization = nC.fromNormalization ≫ f ∧
      IsFinite l ∧ ∃ hl : IsDominant l,
        letI := hl
        letI : Algebra nX.normalization.functionField nC.normalization.functionField :=
          (dominantFunctionFieldMap l).toAlgebra
        Module.finrank nX.normalization.functionField nC.normalization.functionField =
          Module.finrank X.functionField C.functionField := by
  let nC := C.fromSpecStalk (genericPoint C)
  let nX := X.fromSpecStalk (genericPoint X)
  let : Algebra X.functionField C.functionField := (dominantFunctionFieldMap f).toAlgebra
  have hC := complete_integral_curve_normalization_properties C hdC k (f ≫ b)
  have hX := complete_integral_curve_normalization_properties X hdX k b
  have : IsFinite nC.fromNormalization := hC.1
  have : IsLocallyNoetherian nC.normalization := hC.2.2.2.2.2.1
  have : IsProper (nC.fromNormalization ≫ (f ≫ b)) := hC.2.2.2.2.2.2
  let : CompactSpace nC.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (nC.fromNormalization ≫ (f ≫ b))
  have : IsNoetherian nC.normalization := ⟨⟩
  have : IsDominant nC.fromNormalization := birationalMorphism_dominant _ hC.2.1
  have : IsDominant nX.fromNormalization := birationalMorphism_dominant _ hX.2.1
  have : IsFinite (nC.fromNormalization ≫ f) :=
    proper_dominant_integral_curve_isFinite _ hC.2.2.2.2.1 hdX
  obtain ⟨l, hl, hlf, hld⟩ := exists_finite_dominant_normalization_lift
    (nC.fromNormalization ≫ f) (generic_normalization_stalks_normal C) k b
  have : IsFinite l := hlf
  have : IsDominant l := hld
  let : Algebra nX.normalization.functionField nC.normalization.functionField :=
    (dominantFunctionFieldMap l).toAlgebra
  let eC : C.functionField ≃+* nC.normalization.functionField :=
    RingEquiv.ofBijective (dominantFunctionFieldMap nC.fromNormalization)
      (birational_functionFieldMap_bijective _ hC.2.1)
  let eX : X.functionField ≃+* nX.normalization.functionField :=
    RingEquiv.ofBijective (dominantFunctionFieldMap nX.fromNormalization)
      (birational_functionFieldMap_bijective _ hX.2.1)
  have hcomm : (dominantFunctionFieldMap nC.fromNormalization).comp (dominantFunctionFieldMap f) =
      (dominantFunctionFieldMap l).comp (dominantFunctionFieldMap nX.fromNormalization) := by
    rw [← dominantFunctionFieldMap_comp nC.fromNormalization f,
      ← dominantFunctionFieldMap_comp l nX.fromNormalization]
    congr 1
    exact hl.symm
  refine ⟨l, hl, hlf, hld, ?_⟩
  symm
  apply Algebra.finrank_eq_of_equiv_equiv eX eC
  exact hcomm.symm

end
end Negativity
