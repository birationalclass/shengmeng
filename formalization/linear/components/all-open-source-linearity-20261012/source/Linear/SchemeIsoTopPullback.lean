module
public import Linear.StructureModuleCompositeChartValue
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
theorem schemeIsoAppIsoTopHom {X Y : Scheme.{u}} (e : X ≅ Y) :
    (e.hom.appIso ⊤).hom =
    Y.presheaf.map (eqToHom (show ⊤ = e.hom ''ᵁ ⊤ by
      simp [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso])).op ≫ e.hom.appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE]
  have ht : ⊤ = e.hom ''ᵁ ⊤ := by simp [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hn := e.hom.naturality (eqToHom ht).op
  refine Eq.trans ?_ hn.symm
  congr 1

end LinearStudy
