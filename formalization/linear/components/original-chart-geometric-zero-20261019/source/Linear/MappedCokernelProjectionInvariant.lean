module
public import Linear.MappedChainCokernelPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]

/-- A named ACTUAL projection identity,with every map explicit.
This definition alone is a statement,NOT a proof. Keeping its body at
the generic boundary avoids expanding concrete Koszul objects during
application. The next theorem proves it for the constructed comparison. -/
def chainCokernelProjectionInvariant (F : A ⥤ B) [F.PreservesZeroMorphisms]
    (C : ChainComplex A ℕ) (D : ChainComplex B ℕ)
    (e : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (E : F.obj (cokernel (C.d 1 0)) ≅ Q.pt) : Prop :=
  F.map (cokernel.π (C.d 1 0)) ≫ E.hom = e.hom.f 0 ≫ Q.π

/-- PROVE the actual projection invariant for the SAME constructed
mapped-cokernel comparison,without assuming the desired map equality. -/
theorem mappedChainFirstCokernelPresentationIso_projectionInvariant
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (C : ChainComplex A ℕ) (D : ChainComplex B ℕ)
    (e : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D)
    (Q : CokernelCofork (D.d 1 0)) (hQ : IsColimit Q) :
    chainCokernelProjectionInvariant F C D e Q
      (mappedChainFirstCokernelPresentationIso F C D e Q hQ) :=
  mappedChainFirstCokernelPresentationIso_projection F C D e Q hQ

end LinearStudy
