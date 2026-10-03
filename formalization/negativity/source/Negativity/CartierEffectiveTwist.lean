module

public import Negativity.FiniteNormalGeometry
public import Negativity.CartierCurveMoving
public import Mathlib.RingTheory.Localization.Integer
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- On a quasi-compact integral scheme birational over an affine integral
base, every actual Cartier atlas has an effective principal twist. The
twisting function is constructed by clearing a finite family of denominators
in the actual coordinate ring of the base. No section-existence hypothesis
or desired effectivity conclusion is supplied. -/
theorem exists_effective_cartier_rational_twist
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [CompactSpace X]
    [IsAffine Y] (f : X ⟶ Y) (hf : BirationalMorphism f)
    {ι : Type*} (A : CartierAtlas X ι) :
    ∃ a : X.functionFieldˣ, (A.rationalTwist a).Effective := by
  classical
  have := birationalMorphism_dominant f hf
  have := birationalMorphism_generic_stalk_isIso f hf
  have : Nonempty (⊤ : Y.Opens) := ⟨genericPoint Y, trivial⟩
  let R := Γ(Y, ⊤)
  have : IsFractionRing R Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y ⊤ (isAffineOpen_top Y)
  let g : Y.functionField ⟶ X.functionField :=
    (Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
      f.stalkMap (genericPoint X)
  let e : Y.functionField ≃+* X.functionField :=
    RingEquiv.ofBijective g.hom (ConcreteCategory.bijective_of_isIso g)
  have hc : (Set.univ : Set X) ⊆ ⋃ i, (A.chart i : Set X) := by
    intro x _
    obtain ⟨i, hi⟩ := A.covers x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (A.chart i : Set X)) (fun i => (A.chart i).isOpen) hc
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors R) t (fun i => e.symm (A.equation i : X.functionField))
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hsK : algebraMap R Y.functionField (s : R) ≠ 0 := by
    intro hz
    exact hs0 (IsFractionRing.injective R Y.functionField
      (hz.trans (map_zero _).symm))
  let a : X.functionFieldˣ := Units.mk0 (e (algebraMap R Y.functionField (s : R)))
    (fun hz => hsK (e.injective (hz.trans e.map_zero.symm)))
  have hreg : ∀ i ∈ t, ∀ x : X, ∃ r : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField r =
        ((A.rationalTwist a).equation i : X.functionField) := by
    intro i hi x
    obtain ⟨r, hr⟩ := hs i hi
    have heq : e (Y.germToFunctionField ⊤ r) =
        (a : X.functionField) * (A.equation i : X.functionField) := by
      change e (algebraMap R Y.functionField r) = _
      rw [hr, Algebra.smul_def, map_mul, RingEquiv.apply_symm_apply]
      rfl
    refine ⟨(f.stalkMap x).hom (Y.presheaf.germ ⊤ (f x) trivial r), ?_⟩
    rw [← dominantFunctionFieldMap_stalk f x,
      Scheme.algebraMap_germ_eq_germToFunctionField Y
        (U := ⊤) (x := f x) trivial r]
    exact heq
  refine ⟨a, ?_⟩
  intro j x hxj
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  obtain ⟨r, hr⟩ := hreg i hi x
  obtain ⟨v, hv⟩ := (A.rationalTwist a).transition i j x hxi hxj
  refine ⟨(v : X.presheaf.stalk x) * r, ?_⟩
  rw [map_mul, hr]
  exact congrArg Units.val hv

end
end Negativity
