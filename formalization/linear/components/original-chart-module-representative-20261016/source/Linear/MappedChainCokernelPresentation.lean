module
public import Linear.ChainFirstCokernelIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]

/-- Compose cokernel preservation,whole-chain transport and the original
quotient presentation while C,D and the quotient are VARIABLES. The whole
complex iso and the colimit property are EXPLICIT generic inputs;the
original Koszul application must construct them. -/
def mappedChainFirstCokernelPresentationIso (F : A ⥤ B) [F.Additive]
    [F.PreservesHomology] (C : ChainComplex A ℕ) (D : ChainComplex B ℕ)
    (e : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (hQ : IsColimit Q) :
    F.obj (cokernel (C.d 1 0)) ≅ Q.pt := by
  letI : PreservesColimit (parallelPair (C.d 1 0) 0) F :=
    Functor.PreservesHomology.preservesCokernel F (C.d 1 0)
  exact PreservesCokernel.iso F (C.d 1 0) ≪≫
    originalChainFirstCokernelIso _ D e ≪≫
    (cokernelIsCokernel (D.d 1 0)).coconePointUniqueUpToIso hQ

/-- The generic comparison keeps the original cokernel projection and
the actual quotient presentation map. -/
theorem mappedChainFirstCokernelPresentationIso_projection (F : A ⥤ B) [F.Additive]
    [F.PreservesHomology] (C : ChainComplex A ℕ) (D : ChainComplex B ℕ)
    (e : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (hQ : IsColimit Q) :
    F.map (cokernel.π (C.d 1 0)) ≫
      (mappedChainFirstCokernelPresentationIso F C D e Q hQ).hom =
      e.hom.f 0 ≫ Q.π := by
  letI : PreservesColimit (parallelPair (C.d 1 0) 0) F :=
    Functor.PreservesHomology.preservesCokernel F (C.d 1 0)
  dsimp only [mappedChainFirstCokernelPresentationIso,Iso.trans_hom]
  simp only [← Category.assoc,PreservesCokernel.π_iso_hom]
  have hp := originalChainFirstCokernelIso_projection
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) D e
  change cokernel.π (F.map (C.d 1 0)) ≫ _ = _ at hp
  rw [hp,Category.assoc]
  exact congrArg (fun t => e.hom.f 0 ≫ t)
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (D.d 1 0)) hQ WalkingParallelPair.one)

end LinearStudy