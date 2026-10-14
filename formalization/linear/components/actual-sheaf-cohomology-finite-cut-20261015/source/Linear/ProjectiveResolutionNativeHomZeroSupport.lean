module
public import Linear.ProjectiveResolutionNativeHomCocycles
public import Mathlib.RingTheory.Ideal.Maps
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {X : ModuleCat.{u} R}

/-- SAME original source annihilator kills ACTUAL native degree-zero
Hom cycles. Factor the ORIGINAL cocycle through ORIGINAL resolution
augmentation using its native PROVED cokernel universal property. -/
theorem projectiveResolutionNativeHomZeroCycle_annihilator
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) :
    Module.annihilator R X ≤ Module.annihilator R
      (LinearMap.ker ((P.complex.linearYonedaObj R N).d 0 1).hom) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  intro z
  let g : X ⟶ N := P.isColimitCokernelCofork.desc
    (CokernelCofork.ofπ z.val (projectiveResolutionNativeHomCycle_isCocycle P N 0 z))
  have hg : P.π.f 0 ≫ g = z.val := Cofork.IsColimit.π_desc P.isColimitCokernelCofork
  have hgz : a • g = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change a • g.hom x = 0
    rw [← map_smul,Module.mem_annihilator.mp ha x,map_zero]
  apply Subtype.ext
  change a • z.val = 0
  rw [← hg,← Linear.comp_smul,hgz,comp_zero]

/-- SAME source annihilator kills ACTUAL original native degree-zero
COHOMOLOGY. Reuse native zero-degree homology/cycles identification,
not an assumed Ext comparison or substitute coefficient model. -/
theorem projectiveResolutionNativeHomZeroCohomology_annihilator
    (P : ProjectiveResolution X) (N : ModuleCat.{u} R) :
    Module.annihilator R X ≤ Module.annihilator R
      ((P.complex.linearYonedaObj R N).homology 0) := by
  let e : (P.complex.linearYonedaObj R N).homology 0 ≃ₗ[R]
      LinearMap.ker ((P.complex.linearYonedaObj R N).d 0 1).hom :=
    ((P.complex.linearYonedaObj R N).isoHomologyπ₀.symm ≪≫
      (P.complex.linearYonedaObj R N).cyclesIsoSc' 0 0 1
        ((ComplexShape.up ℕ).prev_eq_self' 0 (by intro i hi;change i+1=0 at hi;omega))
        ((ComplexShape.up ℕ).next_eq' (by rfl)) ≪≫
      ((P.complex.linearYonedaObj R N).sc' 0 0 1).moduleCatCyclesIso).toLinearEquiv
  intro a ha
  apply Module.mem_annihilator.mpr
  intro x
  apply e.injective
  rw [map_smul,map_zero]
  exact (Module.mem_annihilator.mp
    ((projectiveResolutionNativeHomZeroCycle_annihilator P N) ha)) (e x)

end LinearStudy
