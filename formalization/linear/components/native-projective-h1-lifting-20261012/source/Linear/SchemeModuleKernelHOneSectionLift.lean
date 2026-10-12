module
public import Linear.SchemeModuleHOneSectionLift
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u w

/-- Let f be an actual epimorphism of O_X-module sheaves.
Then H1(ker f)=0 gives surjectivity on actual global sections.
The actual kernel short exact sequence is constructed here; no exactness
certificate or section-lifting hypothesis is assumed. -/
theorem schemeModuleEpi_sections_surjective_of_kernel_H1_vanish
    {X : Scheme.{u}} [HasExt.{w} (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    {M N : X.Modules} (f : M ⟶ N) [Epi f]
    [Subsingleton (CategoryTheory.Sheaf.H.{w}
      ((schemeModuleToAdditiveSheaf X).obj (kernel f)) 1)] :
    Function.Surjective (f.app ⊤) := by
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk (S.exact_of_f_is_kernel (kernelIsKernel f))
  exact schemeModuleShortExact_sections_surjective_of_H1_vanish S hS
end LinearStudy
