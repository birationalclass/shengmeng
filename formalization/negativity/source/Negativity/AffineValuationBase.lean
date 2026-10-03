module

public import Negativity.RelativeKernelValuative
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualAffineRingBase (Y : Scheme.{u}) [IsAffine Y]
    {V : Type u} [CommRing V] (g : Γ(Y, ⊤) →+* V) : Spec (.of V) ⟶ Y :=
  Spec.map (CommRingCat.ofHom g) ≫ Y.isoSpec.inv

theorem actual_affine_ring_base_sections (Y : Scheme.{u}) [IsAffine Y]
    {V : Type u} [CommRing V] (g : Γ(Y, ⊤) →+* V) :
    (actualAffineRingBase Y g).appTop ≫ (Scheme.ΓSpecIso (.of V)).hom =
      CommRingCat.ofHom g := by
  rw [actualAffineRingBase, Scheme.Hom.comp_appTop, Category.assoc]
  have hn := Scheme.SpecΓIdentity.hom.naturality (CommRingCat.ofHom g)
  change (Spec.map (CommRingCat.ofHom g)).appTop ≫ (Scheme.ΓSpecIso (.of V)).hom =
    (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ CommRingCat.ofHom g at hn
  rw [hn]
  have hh : Y.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop]
    change Y.isoSpec.inv.appTop ≫ Y.isoSpec.hom.appTop = _
    rw [← Scheme.Hom.comp_appTop, Y.isoSpec.hom_inv_id]
    simp
  rw [← Category.assoc, hh, Category.id_comp]

theorem actual_affine_ring_base_dominant (Y : Scheme.{u}) [IsAffine Y]
    {V : Type u} [CommRing V] (g : Γ(Y, ⊤) →+* V)
    (hg : Function.Injective g) : IsDominant (actualAffineRingBase Y g) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom g)) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g).mpr
    intro r hr
    have hr0 : g r = 0 := hr
    have : r = 0 := hg (hr0.trans (map_zero g).symm)
    simpa [this] using (Ideal.zero_mem (nilradical Γ(Y, ⊤)))
  dsimp [actualAffineRingBase]
  infer_instance

/-- Final theorem: the constructed affine base map has a dominant
generic map for every injective map into a valuation ring. No Scheme
map or generic dominance is supplied separately from the ring embedding. -/
theorem actual_affine_valuation_generic_dominant
    (Y : Scheme.{u}) [IsAffine Y]
    (V K : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (g : Γ(Y, ⊤) →+* V) (hg : Function.Injective g) :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫
      actualAffineRingBase Y g) := by
  have : IsDominant (actualAffineRingBase Y g) :=
    actual_affine_ring_base_dominant Y g hg
  have : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap V K))) := by
    constructor
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
      (algebraMap V K)).mpr
    intro r hr
    have hr0 : algebraMap V K r = 0 := hr
    have : r = 0 := (IsFractionRing.injective V K)
      (hr0.trans (map_zero (algebraMap V K)).symm)
    simpa [this] using (Ideal.zero_mem (nilradical V))
  infer_instance

end
end Negativity
