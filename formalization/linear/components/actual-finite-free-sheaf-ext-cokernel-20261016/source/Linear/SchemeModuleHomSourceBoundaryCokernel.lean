module
public import Linear.SchemeModuleInternalExtZeroSource
public import Linear.SchemeModuleInternalExtSourceBoundaryCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- ACTUAL SHEAF Ext^1 is the cokernel of SAME ACTUAL Hom precomposition,
using PROVED source compatibility of zero SHEAF Ext~=Hom. -/
def schemeModuleHomSourceBoundaryCokernelIso
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N)
    (hB : IsZero (schemeModuleInternalExt S.X₂ N 1)) :
    cokernel (schemeModuleHomPrecompose (N := N) S.f) ≅
      schemeModuleInternalExt S.X₃ N 1 :=
  cokernel.mapIso (schemeModuleHomPrecompose (N := N) S.f)
      (schemeModuleInternalExtSourceMap S.f N 0)
      ((schemeModuleInternalExtZeroIso S.X₂).app N).symm
      ((schemeModuleInternalExtZeroIso S.X₁).app N).symm
      (schemeModuleInternalExtZeroIso_source_inv S.f N) ≪≫
    schemeModuleInternalExtSourceBoundaryCokernelIso S hS N I 0 hB

/-- The cokernel projection is SAME actual connecting map,normalized
by canonical ACTUAL Hom~=Ext^0 comparison. -/
theorem schemeModuleHomSourceBoundaryCokernelIso_hom
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N)
    (hB : IsZero (schemeModuleInternalExt S.X₂ N 1)) :
    cokernel.π (schemeModuleHomPrecompose (N := N) S.f) ≫
        (schemeModuleHomSourceBoundaryCokernelIso S hS N I hB).hom =
      ((schemeModuleInternalExtZeroIso S.X₁).app N).inv ≫
        schemeModuleInternalExtSourceBoundaryViaResolution S hS N I 0 := by
  dsimp only [schemeModuleHomSourceBoundaryCokernelIso,Iso.trans_hom]
  erw [cokernel.mapIso_hom]
  rw [← Category.assoc,cokernel.π_desc,Category.assoc,
    schemeModuleInternalExtSourceBoundaryCokernelIso_hom]
  rfl

/-- The actual Hom-cokernel comparison is independent of ANY actual I. -/
theorem schemeModuleHomSourceBoundaryCokernelIso_independent
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I J : InjectiveResolution N)
    (hB : IsZero (schemeModuleInternalExt S.X₂ N 1)) :
    schemeModuleHomSourceBoundaryCokernelIso S hS N I hB =
      schemeModuleHomSourceBoundaryCokernelIso S hS N J hB := by
  unfold schemeModuleHomSourceBoundaryCokernelIso
  rw [schemeModuleInternalExtSourceBoundaryCokernelIso_independent S hS N I J 0 hB]

/-- A GENUINE finite-free middle frame derives the needed SHEAF Ext^1
vanishing,so this Hom-cokernel comparison has no vanishing premise. -/
def schemeModuleFiniteFreeHomSourceCokernelIso
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (ι : Type u) [Finite ι]
    (e : S.X₂ ≅ SheafOfModules.free (R := X.ringCatSheaf) ι) :
    cokernel (schemeModuleHomPrecompose (N := N) S.f) ≅
      schemeModuleInternalExt S.X₃ N 1 :=
  schemeModuleHomSourceBoundaryCokernelIso S hS N I
    (schemeModuleFiniteFreeFrameInternalExt_succ N ι e 0)

/-- The finite-free case retains SAME actual normalized boundary. -/
theorem schemeModuleFiniteFreeHomSourceCokernelIso_hom
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (N : X.Modules)
    (I : InjectiveResolution N) (ι : Type u) [Finite ι]
    (e : S.X₂ ≅ SheafOfModules.free (R := X.ringCatSheaf) ι) :
    cokernel.π (schemeModuleHomPrecompose (N := N) S.f) ≫
        (schemeModuleFiniteFreeHomSourceCokernelIso S hS N I ι e).hom =
      ((schemeModuleInternalExtZeroIso S.X₁).app N).inv ≫
        schemeModuleInternalExtSourceBoundaryViaResolution S hS N I 0 :=
  schemeModuleHomSourceBoundaryCokernelIso_hom S hS N I
    (schemeModuleFiniteFreeFrameInternalExt_succ N ι e 0)

end LinearStudy
