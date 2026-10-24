module
public import Linear.MappedCokernelProjectionInvariant
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]

/-- ACTUAL complex/chart/cofork data only;no desired projection equality
or comparison is supplied. The native application constructs every field. -/
def mappedChainPresentationData (F : A ⥤ B) [F.PreservesZeroMorphisms] : Type _ :=
  Σ C : ChainComplex A ℕ,Σ D : ChainComplex B ℕ,
    Σ _e : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj C) ≅ D,
      Σ Q : CokernelCofork (D.d 1 0),IsColimit Q

/-- The same generic cokernel comparison,constructed from actual data. -/
def mappedChainPresentationDataIso (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (d : mappedChainPresentationData F) :
    F.obj (cokernel (d.1.d 1 0)) ≅ d.2.2.2.1.pt :=
  mappedChainFirstCokernelPresentationIso F d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

/-- PROVE the actual projection equality from the data,never assuming it. -/
theorem mappedChainPresentationData_projection
    (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (d : mappedChainPresentationData F) :
    chainCokernelProjectionInvariant F d.1 d.2.1 d.2.2.1 d.2.2.2.1
      (mappedChainPresentationDataIso F d) :=
  mappedChainFirstCokernelPresentationIso_projectionInvariant
    F d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

end LinearStudy
