module
public import Linear.NativeStructureModuleSections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- The actual degree-zero associated ring-module presheaf is the native
Proj structure-ring unit presheaf. The section isomorphisms commute with
the ORIGINAL restriction maps, rather than with a supplied model. -/
def nativeStructureRingZeroModulePresheafIso :
    PresheafOfModules.unit (AlgebraicGeometry.Proj 𝓑).ringCatSheaf.obj ≅
      nativeProjectiveModulePresheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) 0 :=
  PresheafOfModules.isoMk (fun U => by
    letI := nativeProjectiveModuleSectionGroup 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) 0 U
    letI := nativeProjectiveModuleSectionModule 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) 0 U
    exact (nativeStructureRingZeroModuleSectionEquiv 𝓑 U).toModuleIso)
    (by intros; apply ModuleCat.hom_ext; rfl)

/-- The degree-zero associated ring-module SHEAF is the ACTUAL native
Proj structure sheaf as a module. This is a constructed global comparison;
it does not identify the normalization dual with the canonical sheaf. -/
def nativeStructureRingZeroModuleSheafIso :
    SheafOfModules.unit (AlgebraicGeometry.Proj 𝓑).ringCatSheaf ≅
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) 0 where
  hom := ⟨(nativeStructureRingZeroModulePresheafIso 𝓑).hom⟩
  inv := ⟨(nativeStructureRingZeroModulePresheafIso 𝓑).inv⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    exact (nativeStructureRingZeroModulePresheafIso 𝓑).hom_inv_id
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    exact (nativeStructureRingZeroModulePresheafIso 𝓑).inv_hom_id

end LinearStudy
