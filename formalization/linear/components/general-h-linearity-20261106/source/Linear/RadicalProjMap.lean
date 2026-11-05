/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Proj maps under the radical no-base-locus condition

Adapted from the pinned mathlib Functor.lean, keeping its local rings,
structure sheaf, actual Scheme morphism and original chart square.
The only mathematical hypothesis change is replacing ideal containment
by radical containment; homogeneous prime ideals are radical.
Original upstream authors and license above are retained.
-/

@[expose] public section

set_option maxHeartbeats 1800000
universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace LinearStudy

section universe_polymorphic

variable {A B C σ τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : (irrelevant ℬ).toIdeal ≤ (Ideal.map f.toRingHom (irrelevant 𝒜).toIdeal).radical)


/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
@[simps] def radicalProjectiveComapFun (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| by
    change (irrelevant ℬ).toIdeal ≤ p.1.toIdeal
    apply hf.trans
    apply (p.2.isRadical.radical_le_iff).mpr
    exact Ideal.map_le_of_le_comap le

/-- The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
def radicalProjectiveComap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := radicalProjectiveComapFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩



open ProjectiveSpectrum.StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ radicalProjectiveComap f hf ⁻¹' U.1)

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def radicalProjStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨radicalProjectiveComap f hf y.1, hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
lemma radicalProjStructureSheafFun_isLocallyFraction
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (radicalProjStructureSheafFun f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨radicalProjectiveComap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (radicalProjectiveComap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [radicalProjStructureSheafFun]

set_option backward.isDefEq.respectTransparency false in
/-- The underlying ring hom of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def radicalProjStructureSheaf :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨radicalProjStructureSheafFun _ _ _ _ hUV s.1,
      radicalProjStructureSheafFun_isLocallyFraction _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [radicalProjStructureSheafFun]
  map_zero' := by ext; simp [radicalProjStructureSheafFun]
  map_add' x y := by ext; simp [radicalProjStructureSheafFun]
  map_mul' x y := by ext; simp [radicalProjStructureSheafFun]


end universe_polymorphic

section universe_monomorphic


variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : (irrelevant ℬ).toIdeal ≤ (Ideal.map f.toRingHom (irrelevant 𝒜).toIdeal).radical) (hg : (irrelevant 𝒞).toIdeal ≤ (Ideal.map g.toRingHom (irrelevant ℬ).toIdeal).radical)

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces. -/
@[simps! (isSimp := false)] noncomputable def radicalProjSheafedSpaceMap :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| radicalProjectiveComap f hf
      c := { app U := CommRingCat.ofHom <| radicalProjStructureSheaf f hf _ _ Set.Subset.rfl } }

lemma radicalProjGerm_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (radicalProjectiveComap f hf p).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (radicalProjSheafedSpaceMap f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((radicalProjSheafedSpaceMap f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp] lemma radicalProjSectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜)
    (c : NumDenSameDeg 𝒜 p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    ((sectionInBasicOpen 𝒜 p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise] theorem radicalProj_localRingHom_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (radicalProjectiveComap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (radicalProjSheafedSpaceMap f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [radicalProjGerm_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of `Proj`. -/
noncomputable def radicalProjMap : Proj ℬ ⟶ Proj 𝒜 where
  __ := (radicalProjSheafedSpaceMap f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← radicalProj_localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜 (radicalProjectiveComap f hf p)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem radicalProjMap_preimage_basicOpen (s : A) :
    radicalProjMap f hf ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 s = AlgebraicGeometry.Proj.basicOpen ℬ (f s) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem radicalProjChart_ι_comp_map (s : A) : (AlgebraicGeometry.Proj.basicOpen ℬ (f s)).ι ≫ radicalProjMap f hf =
    (radicalProjMap f hf).resLE _ _ le_rfl ≫ (AlgebraicGeometry.Proj.basicOpen 𝒜 s).ι := by simp

@[reassoc] lemma radicalProjMap_awayToSection_appLE {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) :
    AlgebraicGeometry.Proj.awayToSection 𝒜 s ≫
      Scheme.Hom.appLE (radicalProjMap f hf) (AlgebraicGeometry.Proj.basicOpen 𝒜 s) (AlgebraicGeometry.Proj.basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) ≫
      AlgebraicGeometry.Proj.awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The following square commutes:
```
Proj ℬ         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
@[reassoc] theorem radicalProjMap_awayι_comp {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    awayι ℬ (f s) (f.2 hs) hi ≫ radicalProjMap f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi := by
  rw [awayι, awayι, Category.assoc, radicalProjChart_ι_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (AlgebraicGeometry.Proj.basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, radicalProjMap_awayToSection_appLE _ _ hs]


end universe_monomorphic
end LinearStudy
