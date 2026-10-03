module

public import Negativity.CodimensionOne
public import Negativity.FiniteNormalGeometry
public import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Spread the actual generic inverse of a separated finite-type map;
its dense section becomes an actual isomorphism on a nonempty open. -/
theorem birational_of_actual_generic_stalk_isIso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f]
    [IsIso (f.stalkMap (genericPoint X))] : BirationalMorphism f := by
  let x := genericPoint X
  let s₀ : Spec (Y.presheaf.stalk (f x)) ⟶ X :=
    inv (Spec.map (f.stalkMap x)) ≫ X.fromSpecStalk x
  have hs₀ : s₀ ≫ f = Y.fromSpecStalk (f x) := by
    dsimp [s₀]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      IsIso.inv_hom_id_assoc]
  obtain ⟨U, hyU, s, hspread, hs⟩ := spread_out_of_isGermInjective'
    (𝟙 Y) f s₀ (by simpa using hs₀)
  have : IsDominant (X.fromSpecStalk (genericPoint X)) := generic_stalk_dominant X
  have : IsDominant s₀ := by dsimp [s₀, x]; infer_instance
  have : IsDominant (U.fromSpecStalkOfMem (f x) hyU ≫ s) := by
    rw [← hspread]; infer_instance
  have : IsDominant s := IsDominant.of_comp (U.fromSpecStalkOfMem (f x) hyU) s
  let s' : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι s (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change f (s y) ∈ U
    rw [← Scheme.Hom.comp_apply, hs]
    exact y.2)
  have hs' : s' ≫ (f ⁻¹ᵁ U).ι = s := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant (s' ≫ (f ⁻¹ᵁ U).ι) := by rw [hs']; infer_instance
  have : IsDominant s' := IsDominant.of_comp_of_isOpenImmersion s' (f ⁻¹ᵁ U).ι
  refine ⟨U, ⟨⟨f x, hyU⟩⟩, separated_dominant_section_isIso (f ∣_ U) s' ?_⟩
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, hs', hs]
  simp

/-- Final theorem: the composition of actual separated finite-type
birational morphisms of integral schemes is birational in the geometric
nonempty-isomorphism-open sense. The required actual open is constructed
by spreading the composed generic inverse; it is not an extra input. -/
theorem actual_birational_morphism_comp
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsSeparated f]
    (g : Y ⟶ Z) [LocallyOfFiniteType g] [IsSeparated g]
    (hf : BirationalMorphism f) (hg : BirationalMorphism g) :
    BirationalMorphism (f ≫ g) := by
  have : IsDominant f := birationalMorphism_dominant f hf
  have : IsIso (f.stalkMap (genericPoint X)) := birationalMorphism_generic_stalk_isIso f hf
  have : IsIso (g.stalkMap (f (genericPoint X))) := by
    rw [dominant_genericPoint_eq f]
    exact birationalMorphism_generic_stalk_isIso g hg
  have : IsIso ((f ≫ g).stalkMap (genericPoint X)) := by
    rw [Scheme.Hom.stalkMap_comp]
    infer_instance
  exact birational_of_actual_generic_stalk_isIso (f ≫ g)

end
end Negativity
