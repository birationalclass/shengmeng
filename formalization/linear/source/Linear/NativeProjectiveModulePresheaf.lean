module
public import Linear.NativeProjectiveModuleSections
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S D : Type u} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)
variable (hgrade : ∀ n : ℕ, ∀ d : ℤ, ∀ b : S, b ∈ 𝓑 n →
  ∀ ell : D, ell ∈ 𝒟 d → b • ell ∈ 𝒟 ((n : ℤ)+d))

/-- Actual homogeneous local-fraction sections with ACTUAL native
Proj structure-ring actions and natural restriction maps, bundled
as a presheaf of modules on the ORIGINAL Proj scheme. -/
def nativeProjectiveModulePresheaf (k : ℤ) :
    (AlgebraicGeometry.Proj 𝓑).PresheafOfModules where
  obj U := by
    change ModuleCat ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj U)
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hgrade k U
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hgrade k U
    exact ModuleCat.of _ ((nativeProjectiveModuleSheafInType 𝓑 𝒟 k).1.obj U)
  map {U V} i := by
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hgrade k U
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hgrade k U
    letI := nativeProjectiveModuleSectionGroup 𝓑 𝒟 hgrade k V
    letI := nativeProjectiveModuleSectionModule 𝓑 𝒟 hgrade k V
    exact ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars ((AlgebraicGeometry.Proj 𝓑).ringCatSheaf.obj.map i).hom).obj
        (ModuleCat.of ((ProjectiveSpectrum.Proj.structureSheaf 𝓑).1.obj V)
          ((nativeProjectiveModuleSheafInType 𝓑 𝒟 k).1.obj V))) {
      toFun := (nativeProjectiveModuleSheafInType 𝓑 𝒟 k).1.map i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id U := by
    apply ModuleCat.hom_ext
    rfl
  map_comp i j := by
    apply ModuleCat.hom_ext
    rfl

/-- The underlying Type-valued presheaf agrees with the actual
local-fraction sheaf, including its original restriction maps. -/
def nativeProjectiveModulePresheafForgetIso (k : ℤ) :
    (nativeProjectiveModulePresheaf 𝓑 𝒟 hgrade k).presheaf ⋙ forget AddCommGrpCat ≅
      (nativeProjectiveModuleSheafInType 𝓑 𝒟 k).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

end LinearStudy
