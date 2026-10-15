module
public import Linear.SchemeModuleOpenRestrictionExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v

/-- Native homology transport for an ACTUAL original complex C and a
PROVIDED whole restricted-complex isomorphism e. This generic lemma has
that explicit isomorphism premise;the Koszul application constructs e. -/
def schemeModuleRestrictionComplexHomologyIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] {ι : Type v} (c : ComplexShape ι)
    (C : HomologicalComplex Y.Modules c) (D : HomologicalComplex X.Modules c) :
    letI := schemeModuleOpenRestriction_additive j
    (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex c).obj C ≅ D) →
    (i : ι) → (Scheme.Modules.restrictFunctor j).obj (C.homology i) ≅ D.homology i := by
  letI := schemeModuleOpenRestriction_additive j
  intro e i
  exact (schemeModuleOpenRestriction_homologyIso j c C i).symm ≪≫
    (HomologicalComplex.homologyFunctor X.Modules c i).mapIso e

end LinearStudy