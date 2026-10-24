module
public import Linear.ChainActualCokernelAugmentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {A : Type*} [Category* A] [Abelian A]

/-- A PROVIDED whole original chain-complex iso induces the actual
cokernel iso of its ORIGINAL d1. The complex iso is an explicit premise. -/
def originalChainFirstCokernelIso (C D : ChainComplex A ℕ) (e : C ≅ D) :
    cokernel (C.d 1 0) ≅ cokernel (D.d 1 0) :=
  cokernel.mapIso (C.d 1 0) (D.d 1 0)
    ((HomologicalComplex.eval A (ComplexShape.down ℕ) 1).mapIso e)
    ((HomologicalComplex.eval A (ComplexShape.down ℕ) 0).mapIso e)
    (e.hom.comm 1 0).symm

/-- It preserves the original degree-zero map to the actual cokernel. -/
theorem originalChainFirstCokernelIso_projection (C D : ChainComplex A ℕ) (e : C ≅ D) :
    cokernel.π (C.d 1 0) ≫ (originalChainFirstCokernelIso C D e).hom =
      e.hom.f 0 ≫ cokernel.π (D.d 1 0) := by
  simp [originalChainFirstCokernelIso,cokernel.mapIso,cokernel.map]

end LinearStudy