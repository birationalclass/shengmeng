module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u

/-- Actual global sections carry an epimorphism of quasi-coherent sheaves
on an actual affine scheme to a surjective module map. This uses mathlib's
proved affine equivalence, rather than assuming sectionwise surjectivity.
It is the exactness input for the native finite graded chart presentation. -/
theorem affineQuasicoherent_globalSections_surjective (R : CommRingCat.{u})
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] :
    Function.Surjective ((moduleSpecΓFunctor (R := R)).map f) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let M' : P.FullSubcategory := ⟨M,inferInstance⟩
  let N' : P.FullSubcategory := ⟨N,inferInstance⟩
  let f' : M' ⟶ N' := ObjectProperty.homMk f
  haveI : Epi ((ObjectProperty.ι P).map f') := ‹Epi f›
  haveI : Epi f' := (ObjectProperty.ι P).epi_of_epi_map (f := f') inferInstance
  haveI : Epi ((tildeEquiv (R := R)).inverse.map f') := inferInstance
  have h : Epi ((tildeEquiv (R := R)).inverse.map f') := inferInstance
  change Epi ((moduleSpecΓFunctor (R := R)).map f) at h
  exact (ModuleCat.epi_iff_surjective _).mp h

end LinearStudy
