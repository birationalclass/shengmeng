module

public import Negativity.NormalBirational
public import Negativity.NormalSections
public import Negativity.CartierPullback
public import Negativity.CodimensionOne
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- Birationality of the given map supplies dominance, rather than taking
dominance as a second geometric hypothesis. -/
theorem birationalMorphism_dominant {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : BirationalMorphism f) : IsDominant f := by
  obtain ⟨U, hU, hIso⟩ := hf
  have : IsIso (f ∣_ U) := hIso
  constructor
  apply Dense.mono (s₁ := (U : Set Y))
  · intro y hy
    let z := inv (f ∣_ U) ⟨y, hy⟩
    have hz : (f ∣_ U) z = ⟨y, hy⟩ := by
      dsimp [z]
      change ((inv (f ∣_ U) ≫ (f ∣_ U)) ⟨y, hy⟩) = _
      simp
    refine ⟨(f ⁻¹ᵁ U).ι z, ?_⟩
    change (((f ⁻¹ᵁ U).ι ≫ f) z) = y
    rw [← morphismRestrict_ι, Scheme.Hom.comp_apply, hz]
    rfl
  · exact U.isOpen.dense (by simpa using hU)

/-- The actual generic stalk map is an isomorphism for a birational map. -/
theorem birationalMorphism_generic_stalk_isIso {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : BirationalMorphism f) :
    IsIso (f.stalkMap (genericPoint X)) := by
  have := birationalMorphism_dominant f hf
  obtain ⟨U, hU, hIso⟩ := hf
  have : IsIso (f ∣_ U) := hIso
  apply stalkMap_isIso_over_isomorphism_open f U (genericPoint X)
  rw [dominant_genericPoint_eq f]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- Pullback of actual affine sections commutes with the constructed map
on function fields. -/
theorem dominantFunctionFieldMap_germ {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] (r : Γ(Y, U)) :
    dominantFunctionFieldMap f (Y.germToFunctionField U r) =
      X.germToFunctionField (f ⁻¹ᵁ U) (f.app U r) := by
  have hη : f (genericPoint X) ∈ U := by
    rw [dominant_genericPoint_eq f]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField Y hη r,
    dominantFunctionFieldMap_stalk f (genericPoint X), f.germ_stalkMap_apply]
  exact Scheme.algebraMap_germ_eq_germToFunctionField X hη _

/-- Every affine coordinate-ring map of a finite birational morphism to a
normal integral scheme is bijective. The embedding into the base function
field is constructed from generic stalks, not supplied as an extra input. -/
theorem finite_normal_birational_affine_bijective {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f]
    (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Function.Bijective (f.app U) := by
  have := birationalMorphism_dominant f hf
  have := birationalMorphism_generic_stalk_isIso f hf
  have hη : f (genericPoint X) ∈ U := by
    rw [dominant_genericPoint_eq f]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have : Nonempty (f ⁻¹ᵁ U) := ⟨genericPoint X, hη⟩
  let R := Γ(Y, U)
  let S := Γ(X, f ⁻¹ᵁ U)
  let : Algebra R S := (f.app U).hom.toAlgebra
  have : Module.Finite R S := f.finite_app U hU
  have : IsIntegrallyClosed R := normal_affine_sections Y hn U hU
  have : IsFractionRing R Y.functionField := functionField_isFractionRing_of_isAffineOpen Y U hU
  let g : Y.functionField ⟶ X.functionField :=
    (Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
      f.stalkMap (genericPoint X)
  let e : Y.functionField ≃+* X.functionField :=
    RingEquiv.ofBijective g.hom (ConcreteCategory.bijective_of_isIso g)
  let j : S →ₐ[R] Y.functionField := {
    __ := e.symm.toRingHom.comp (X.germToFunctionField (f ⁻¹ᵁ U)).hom
    commutes' := by
      intro r
      apply e.injective
      change e (e.symm (X.germToFunctionField (f ⁻¹ᵁ U) (f.app U r))) =
        e (algebraMap R Y.functionField r)
      rw [RingEquiv.apply_symm_apply]
      exact (dominantFunctionFieldMap_germ f U r).symm }
  have hj : Function.Injective j :=
    e.symm.injective.comp (X.germToFunctionField_injective (f ⁻¹ᵁ U))
  exact finite_birational_algebraMap_bijective R S Y.functionField j hj

/-- A finite birational map of integral schemes to a normal base is an
actual Scheme isomorphism, obtained by gluing the proved affine inverses. -/
theorem finite_normal_birational_isIso {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f]
    (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) : IsIso f := by
  classical
  have hlocal (U : Y.Opens) (hU : IsAffineOpen U) : IsIso (f ∣_ U) := by
    by_cases hne : Nonempty U
    · have : Nonempty U := hne
      have hb := finite_normal_birational_affine_bijective f hf hn U hU
      have : IsIso (f.app U) := (ConcreteCategory.isIso_iff_bijective _).mpr hb
      exact (isIso_morphismRestrict_iff_isIso_app f hU).mpr inferInstance
    · have : IsEmpty U := not_nonempty_iff.mp hne
      infer_instance
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) (f := f)
    (fun U : Y.affineOpens => (U : Y.Opens)) (iSup_affineOpens_eq_top Y)).mpr
  intro U
  exact hlocal U.1 U.2

/-- Normality of actual stalks is preserved on open subschemes. -/
theorem normalStalks_restrict (Y : Scheme.{u}) (U : Y.Opens)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∀ y : U.toScheme, IsIntegrallyClosed (U.toScheme.presheaf.stalk y) := by
  intro y
  have := hn y.1
  let e := RingEquiv.ofBijective (U.stalkIso y).hom.hom
    (ConcreteCategory.bijective_of_isIso (U.stalkIso y).hom)
  exact IsIntegrallyClosed.of_equiv e.symm

/-- A birational map remains birational after restricting to any nonempty
open in its integral target. -/
theorem birationalMorphism_restrict {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : BirationalMorphism f) (U : Y.Opens) [Nonempty U] :
    BirationalMorphism (f ∣_ U) := by
  obtain ⟨V, hV, hIso⟩ := hf
  have : IsIso (f ∣_ V) := hIso
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hUV : ((U ⊓ V : Y.Opens) : Set Y).Nonempty :=
    nonempty_preirreducible_inter U.isOpen V.isOpen
      (by simpa using ‹Nonempty U›) (by simpa using hV)
  have hW : Nonempty W := by
    obtain ⟨y, hyU, hyV⟩ := hUV
    exact ⟨⟨⟨y, hyU⟩, hyV⟩⟩
  have hiUV : IsIso (f ∣_ (U ⊓ V)) := by
    have hi : IsIso ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ U)) := inferInstance
    have himage : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U ⊓ V := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
    have he := (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp hi
    rwa [himage] at he
  refine ⟨W, hW, ?_⟩
  have himage : U.ι ''ᵁ W = U ⊓ V := by
    dsimp [W]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  apply (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
    (morphismRestrictRestrict f U W)).mpr
  rwa [himage]

/-- The actual Zariski-main application: a finite fiber of a proper
birational map to a normal integral base has an isomorphism neighborhood. -/
theorem proper_normal_birational_isIso_near_finite_fiber {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsProper f]
    (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (y : Y) (hfinite : (f ⁻¹' {y}).Finite) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  obtain ⟨U, hy, hfin⟩ := proper_finite_fiber_neighborhood f y hfinite
  have : Nonempty U := ⟨y, hy⟩
  have : IsFinite (f ∣_ U) := hfin
  have := birationalMorphism_dominant f hf
  have hη : f (genericPoint X) ∈ U := by
    rw [dominant_genericPoint_eq f]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have : Nonempty (f ⁻¹ᵁ U) := ⟨genericPoint X, hη⟩
  exact ⟨U, hy, finite_normal_birational_isIso (f ∣_ U)
    (birationalMorphism_restrict f hf U) (normalStalks_restrict Y U hn)⟩

/-- An actual birational map embeds sections of each nonempty inverse-image
open into the target function field, as an algebra over target sections. -/
theorem birational_affine_functionField_embedding {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : BirationalMorphism f)
    (U : Y.Opens) [Nonempty U] :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    ∃ j : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.functionField, Function.Injective j := by
  have := birationalMorphism_dominant f hf
  have := birationalMorphism_generic_stalk_isIso f hf
  have hη : f (genericPoint X) ∈ U := by
    rw [dominant_genericPoint_eq f]
    exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have : Nonempty (f ⁻¹ᵁ U) := ⟨genericPoint X, hη⟩
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let g : Y.functionField ⟶ X.functionField :=
    (Y.presheaf.stalkCongr (.of_eq (dominant_genericPoint_eq f))).inv ≫
      f.stalkMap (genericPoint X)
  let e : Y.functionField ≃+* X.functionField :=
    RingEquiv.ofBijective g.hom (ConcreteCategory.bijective_of_isIso g)
  let j : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Y.functionField := {
    __ := e.symm.toRingHom.comp (X.germToFunctionField (f ⁻¹ᵁ U)).hom
    commutes' := by
      intro r
      apply e.injective
      change e (e.symm (X.germToFunctionField (f ⁻¹ᵁ U) (f.app U r))) =
        e (algebraMap Γ(Y, U) Y.functionField r)
      rw [RingEquiv.apply_symm_apply]
      exact (dominantFunctionFieldMap_germ f U r).symm }
  exact ⟨j, e.symm.injective.comp (X.germToFunctionField_injective (f ⁻¹ᵁ U))⟩

/-- Relative normalization adds no sections to a normal target for an
actual birational map. No finiteness of the normalization is assumed. -/
theorem birational_relative_integralClosure_bijective {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Function.Bijective (algebraMap Γ(Y, U)
      (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) := by
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  obtain ⟨j, hj⟩ := birational_affine_functionField_embedding f hf U
  have : IsIntegrallyClosed Γ(Y, U) := normal_affine_sections Y hn U hU
  have : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  exact integral_birational_algebraMap_bijective _ _ _
    (j.comp (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)).val)
    (hj.comp Subtype.val_injective)

/-- Zariski-main's relative normalization of a birational map to a normal
integral target is the target itself, proved using the actual affine charts. -/
theorem normal_birational_fromNormalization_isIso {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    IsIso f.fromNormalization := by
  have hlocal (U : Y.Opens) (hU : IsAffineOpen U) : IsIso (f.fromNormalization ∣_ U) := by
    by_cases hne : Nonempty U
    · have : Nonempty U := hne
      have hb := birational_relative_integralClosure_bijective f hf hn U hU
      let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
      have : IsIso (CommRingCat.ofHom (algebraMap Γ(Y, U)
          (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)))) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr hb
      have : IsIso (f.fromNormalization.app U) := by
        rw [f.fromNormalization_app hU]
        infer_instance
      exact (isIso_morphismRestrict_iff_isIso_app f.fromNormalization hU).mpr inferInstance
    · have : IsEmpty U := not_nonempty_iff.mp hne
      infer_instance
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _)
    (f := f.fromNormalization) (fun U : Y.affineOpens => (U : Y.Opens))
    (iSup_affineOpens_eq_top Y)).mpr
  intro U
  exact hlocal U.1 U.2

/-- The pointwise Zariski-main criterion needed by exceptional curve
coverage: one quasi-finite point gives a target isomorphism neighborhood. -/
theorem proper_normal_birational_isIso_near_quasiFiniteAt {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsProper f]
    (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) (hx : f.QuasiFiniteAt x) :
    ∃ U : Y.Opens, f x ∈ U ∧ IsIso (f ∣_ U) := by
  have := normal_birational_fromNormalization_isIso f hf hn
  obtain ⟨V, hxV, hIso⟩ := f.exists_mem_and_isIso_morphismRestrict_toNormalization x hx
  have : IsIso (f.toNormalization ∣_ V) := hIso
  let U := f.fromNormalization ''ᵁ V
  have hpre : f.fromNormalization ⁻¹ᵁ U = V := by
    ext z
    change (∃ v, v ∈ V ∧ f.fromNormalization v = f.fromNormalization z) ↔ z ∈ V
    constructor
    · rintro ⟨v, hv, he⟩
      exact f.fromNormalization.isOpenEmbedding.injective he ▸ hv
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hmem : f x ∈ U := by
    refine ⟨f.toNormalization x, hxV, ?_⟩
    change ((f.toNormalization ≫ f.fromNormalization) x) = f x
    rw [f.toNormalization_fromNormalization]
  have hi : IsIso ((f.toNormalization ≫ f.fromNormalization) ∣_ U) := by
    rw [morphismRestrict_comp]
    have : IsIso (f.toNormalization ∣_ (f.fromNormalization ⁻¹ᵁ U)) := by rwa [hpre]
    infer_instance
  rw [f.toNormalization_fromNormalization] at hi
  exact ⟨U, hmem, hi⟩

/-- Exceptional points cannot be quasi-finite. The exceptional condition
means that their image has no open over which the original map is an iso. -/
theorem exceptional_point_not_quasiFiniteAt {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsProper f]
    (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) (hcenter : ∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U)) :
    ¬ f.QuasiFiniteAt x := by
  intro hx
  obtain ⟨U, hxU, hU⟩ := proper_normal_birational_isIso_near_quasiFiniteAt f hf hn x hx
  exact hcenter U hxU hU

/-- Each actual fiber point over the exceptional center is nonisolated,
not merely one point somewhere in that fiber. -/
theorem exceptional_fiber_point_not_isOpen_singleton {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsProper f]
    (hf : BirationalMorphism f)
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (x : X) (hcenter : ∀ U : Y.Opens, f x ∈ U → ¬ IsIso (f ∣_ U)) :
    ¬ IsOpen {f.asFiber x} := by
  rw [← Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  exact exceptional_point_not_quasiFiniteAt f hf hn x hcenter

end Negativity
