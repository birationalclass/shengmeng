module
public import Linear.SchemeModuleInternalHomSourceShortExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
/-- A morphism of ACTUAL source short complexes induces the reversed ACTUAL internal-Hom complex morphism. -/
def schemeModuleHomShortComplexSourceMap {S T : ShortComplex X.Modules}
    (phi : S ⟶ T) (K : CochainComplex X.Modules ℕ) :
    schemeModuleHomSourceShortComplex T K ⟶ schemeModuleHomSourceShortComplex S K where
  τ₁ := schemeModuleHomCoefficientComplexMap phi.τ₃ K
  τ₂ := schemeModuleHomCoefficientComplexMap phi.τ₂ K
  τ₃ := schemeModuleHomCoefficientComplexMap phi.τ₁ K
  comm₁₂ := by
    ext q : 1
    change schemeModuleHomPrecompose (N := K.X q) phi.τ₃ ≫ schemeModuleHomPrecompose (N := K.X q) S.g =
      schemeModuleHomPrecompose (N := K.X q) T.g ≫ schemeModuleHomPrecompose (N := K.X q) phi.τ₂
    simpa only [schemeModuleHomPrecompose_comp] using
      (congrArg (fun z : S.X₂ ⟶ T.X₃ => schemeModuleHomPrecompose (N := K.X q) z) phi.comm₂₃).symm
  comm₂₃ := by
    ext q : 1
    change schemeModuleHomPrecompose (N := K.X q) phi.τ₂ ≫ schemeModuleHomPrecompose (N := K.X q) S.f =
      schemeModuleHomPrecompose (N := K.X q) T.f ≫ schemeModuleHomPrecompose (N := K.X q) phi.τ₁
    simpa only [schemeModuleHomPrecompose_comp] using
      (congrArg (fun z : S.X₁ ⟶ T.X₂ => schemeModuleHomPrecompose (N := K.X q) z) phi.comm₁₂).symm
end LinearStudy
