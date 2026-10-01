module

public import Negativity.LocalGeometry
public import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false

/-- A birational morphism here means that the given morphism, not merely its
source and target, is an isomorphism over a nonempty open of the integral target. -/
def BirationalMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ U : Y.Opens, Nonempty U ∧ IsIso (f ∣_ U)

/-- The canonical map from the generic local ring has dense image. -/
theorem generic_stalk_dominant (Y : Scheme.{u}) [IsIntegral Y] :
    IsDominant (Y.fromSpecStalk (genericPoint Y)) := by
  constructor
  apply Dense.mono (s₁ := {genericPoint Y})
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨IsLocalRing.closedPoint _, Y.fromSpecStalk_closedPoint⟩
  · rw [dense_iff_closure_eq]
    exact (genericPoint_spec Y).def

/-- The codimension-one hypothesis is the geometric coheight, not a separately
assumed equality for the dimension of the stalk. -/
theorem normal_codimensionOne_stalk_isDVR (Y : Scheme.{u}) [IsIntegral Y]
    [IsLocallyNoetherian Y] (y : Y)
    [IsIntegrallyClosed (Y.presheaf.stalk y)] (hy : Order.coheight y = 1) :
    IsDiscreteValuationRing (Y.presheaf.stalk y) := by
  apply scheme_normal_one_dimensional_stalk_isDVR Y y
  rw [ringKrullDim_stalk_eq_coheight, hy]
  rfl

/-- A section with dense image of a separated morphism onto a reduced source
is an inverse. No local-isomorphism hypothesis is assumed. -/
theorem separated_dominant_section_isIso {X Y : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Y) [IsSeparated f] (s : Y ⟶ X) [IsDominant s]
    (hs : s ≫ f = 𝟙 Y) : IsIso f := by
  have : IsClosedImmersion (s ≫ f) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  have : Surjective s := surjective_of_isDominant_of_isClosed_range s
    s.isClosedEmbedding.isClosed_range
  have : IsIso s := isIso_of_isClosedImmersion_of_surjective s
  have : IsIso (s ≫ f) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s f

set_option backward.isDefEq.respectTransparency false in
/-- Proper birational maps between integral schemes are isomorphisms near
every point of the target whose local ring is a DVR. The proof constructs the
valuative square, spreads its lift to a section, and proves it is an inverse. -/
theorem proper_birational_isIso_near_DVR {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsProper f]
    (hf : BirationalMorphism f) (y : Y)
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] :
    ∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V) := by
  classical
  obtain ⟨U, hU, hIso⟩ := hf
  have : Nonempty U := hU
  have : IsIso (f ∣_ U) := hIso
  let η := genericPoint Y
  have hη : η ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using hU)
  let a : Spec Y.functionField ⟶ U := U.fromSpecStalkOfMem η hη
  have : IsDominant (a ≫ U.ι) := by
    simpa [a, η] using generic_stalk_dominant Y
  have : IsDominant a := IsDominant.of_comp_of_isOpenImmersion a U.ι
  let top : Spec Y.functionField ⟶ X := a ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hpre : Nonempty (f ⁻¹ᵁ U) := ⟨inv (f ∣_ U) ⟨η, hη⟩⟩
  have : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι
    ((f ⁻¹ᵁ U).isOpen.dense (by simpa using hpre))
  have : IsDominant top := by dsimp [top]; infer_instance
  let R : Type u := Y.presheaf.stalk y
  have : IsDomain R := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
  have : IsDiscreteValuationRing R :=
    inferInstanceAs (IsDiscreteValuationRing (Y.presheaf.stalk y))
  have : IsFractionRing R Y.functionField :=
    inferInstanceAs (IsFractionRing (Y.presheaf.stalk y) Y.functionField)
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫
      Y.fromSpecStalk y = Y.fromSpecStalk η := by
    exact Y.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y).specializes trivial)
  have hw : top ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫
      Y.fromSpecStalk y := by
    rw [hspec]
    dsimp [top]
    simp only [Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    exact U.fromSpecStalkOfMem_ι η hη
  obtain ⟨lift, hl, hr⟩ := proper_dvr_lift f R Y.functionField top (Y.fromSpecStalk y) hw
  obtain ⟨V, hyV, s, hspread, hs⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f lift (by simpa using hr)
  have hsf : s ≫ f = V.ι := by simpa using hs
  have hVs : Set.range s ⊆ Set.range (f ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change f (s x) ∈ V
    rw [← Scheme.Hom.comp_apply, hsf]
    exact x.2
  let s' : V.toScheme ⟶ (f ⁻¹ᵁ V) := IsOpenImmersion.lift (f ⁻¹ᵁ V).ι s hVs
  have hs'ι : s' ≫ (f ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ hVs
  have : IsDominant s := by
    have : IsDominant
        ((Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫
          V.fromSpecStalkOfMem y hyV) ≫ s) := by
      rw [Category.assoc, ← hspread, hl]
      infer_instance
    exact IsDominant.of_comp
      (Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫
        V.fromSpecStalkOfMem y hyV) s
  have : IsDominant s' := by
    have : IsDominant (s' ≫ (f ⁻¹ᵁ V).ι) := by rw [hs'ι]; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion s' (f ⁻¹ᵁ V).ι
  have : Nonempty (f ⁻¹ᵁ V) := ⟨s' ⟨y, hyV⟩⟩
  have : IsIntegral (f ⁻¹ᵁ V).toScheme := inferInstance
  refine ⟨V, hyV, separated_dominant_section_isIso (f ∣_ V) s' ?_⟩
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, hs'ι, hsf, Category.id_comp]

/-- The full geometric codimension-one neighborhood theorem. Normality is
expressed by the actual local ring being integrally closed, as mathlib does not
yet package a global `IsNormal` scheme class. -/
theorem proper_birational_isIso_near_codimensionOne {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) (y : Y)
    [IsIntegrallyClosed (Y.presheaf.stalk y)] (hy : Order.coheight y = 1) :
    ∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V) := by
  have := normal_codimensionOne_stalk_isDVR Y y hy
  exact proper_birational_isIso_near_DVR f hf y

/-- All codimension-one points lie in a single open over which f is an
isomorphism. The opens are constructed above and glued using Zariski locality. -/
theorem proper_birational_isIso_on_codimensionOne_open {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnormal : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∃ U : Y.Opens, (∀ y : Y, Order.coheight y = 1 → y ∈ U) ∧ IsIso (f ∣_ U) := by
  classical
  have (y : Y) : IsIntegrallyClosed (Y.presheaf.stalk y) := hnormal y
  choose V hy hIso using fun y : {y : Y // Order.coheight y = 1} ↦
    proper_birational_isIso_near_codimensionOne f hf y.1 y.2
  have hiso : IsIso (f ∣_ ⨆ y, V y) := by
    let 𝒰 := Scheme.Opens.iSupOpenCover V
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun y ↦ ?_
    refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
      ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
    have : Scheme.Opens.ι _ ''ᵁ (𝒰.f y).opensRange = V y := by
      simp only [Scheme.Opens.iSupOpenCover, 𝒰, ← Scheme.Hom.opensRange_comp,
        Scheme.homOfLE_ι, Scheme.Opens.opensRange_ι]
    rw [this]
    exact hIso y
  exact ⟨⨆ y, V y, fun y hy' ↦ Opens.mem_iSup.mpr ⟨⟨y, hy'⟩, hy ⟨y, hy'⟩⟩, hiso⟩

/-- An isomorphism over an open gives actual isomorphisms of the stalk maps
of the original morphism at every point over that open. -/
theorem stalkMap_isIso_over_isomorphism_open {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)] (x : X) (hx : f x ∈ U) :
    IsIso (f.stalkMap x) := by
  let z : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have : IsIso (((f ⁻¹ᵁ U).ι ≫ f).stalkMap z) := by
    rw [← morphismRestrict_ι, Scheme.Hom.stalkMap_comp]
    infer_instance
  rw [Scheme.Hom.stalkMap_comp] at this
  have : IsIso (f.stalkMap x ≫ (f ⁻¹ᵁ U).ι.stalkMap z) := by
    simpa only [Scheme.Opens.ι_apply] using this
  exact IsIso.of_isIso_comp_right (f.stalkMap x) ((f ⁻¹ᵁ U).ι.stalkMap z)

/-- Every codimension-one target point has a unique preimage, and the actual
stalk map there is an isomorphism. This supplies the local strict-transform input. -/
theorem proper_birational_codimensionOne_unique_preimage {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) (y : Y)
    [IsIntegrallyClosed (Y.presheaf.stalk y)] (hy : Order.coheight y = 1) :
    ∃ x : X, f x = y ∧ IsIso (f.stalkMap x) ∧ Order.coheight x = 1 ∧
      ∀ x' : X, f x' = y → x' = x := by
  obtain ⟨U, hyU, hIso⟩ := proper_birational_isIso_near_codimensionOne f hf y hy
  have : IsIso (f ∣_ U) := hIso
  obtain ⟨z, hz⟩ := (f ∣_ U).surjective ⟨y, hyU⟩
  have hz' : f z.1 = y :=
    (morphismRestrict_base_coe f U z).symm.trans (congrArg Subtype.val hz)
  refine ⟨z.1, hz', stalkMap_isIso_over_isomorphism_open f U z.1 z.2, ?_, ?_⟩
  · calc
      Order.coheight z.1 = Order.coheight z :=
        coheight_eq_of_isOpenImmersion (f := (f ⁻¹ᵁ U).ι)
      _ = Order.coheight ((f ∣_ U) z) :=
        (coheight_eq_of_isOpenImmersion (f := f ∣_ U)).symm
      _ = Order.coheight (U.ι ((f ∣_ U) z)) :=
        (coheight_eq_of_isOpenImmersion (f := U.ι)).symm
      _ = 1 := by rw [hz]; exact hy
  · intro x' hx'
    have hxU : f x' ∈ U := hx' ▸ hyU
    have he : (f ∣_ U) ⟨x', hxU⟩ = (f ∣_ U) z := by
      apply Subtype.ext
      rw [morphismRestrict_base_coe, morphismRestrict_base_coe]
      exact hx'.trans hz'.symm
    exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective he)

/-- Proper birational modifications are surjective. This is an actual scheme
fact needed in Chow descent, not an extra set-theoretic input. -/
theorem proper_birational_surjective {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f) : Surjective f := by
  obtain ⟨U, hU, hIso⟩ := hf
  have : IsIso (f ∣_ U) := hIso
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense (by simpa using hU))
  have : IsDominant ((f ∣_ U) ≫ U.ι) := inferInstance
  have : IsDominant ((f ⁻¹ᵁ U).ι ≫ f) := by rwa [morphismRestrict_ι] at this
  have : IsDominant f := IsDominant.of_comp (f ⁻¹ᵁ U).ι f
  exact surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range

end Negativity
