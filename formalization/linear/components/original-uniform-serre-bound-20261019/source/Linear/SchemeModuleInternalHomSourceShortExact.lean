module
public import Linear.SchemeModuleInjectiveHomExact
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- The actual coefficient complex used to compute actual derived SHEAF Ext. -/
def schemeModuleHomCoefficientComplex (P : X.Modules) (K : CochainComplex X.Modules ℕ) :
    CochainComplex X.Modules ℕ :=
  ((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K

/-- Source precomposition on the SAME actual coefficient complex. -/
def schemeModuleHomCoefficientComplexMap {A B : X.Modules} (f : A ⟶ B)
    (K : CochainComplex X.Modules ℕ) :
    schemeModuleHomCoefficientComplex B K ⟶ schemeModuleHomCoefficientComplex A K :=
  (NatTrans.mapHomologicalComplex (schemeModuleInternalHomSourceNatTrans f)
    (ComplexShape.up ℕ)).app K

/-- The SAME precomposition map preserves the zero source morphism. -/
theorem schemeModuleHomPrecompose_zero (A B N : X.Modules) :
    schemeModuleHomPrecompose (N := N) (0 : A ⟶ B) = 0 := by
  apply SheafOfModules.hom_ext
  ext U f
  apply Subtype.ext
  change (_ : (Over.forget U.unop).op ⋙ A.presheaf ⟶
    (Over.forget U.unop).op ⋙ N.presheaf) = _
  ext W x
  change f.val.app W 0 = 0
  exact map_zero (f.val.app W).hom

/-- A SAME original source short complex gives the actual reversed Hom complexes. -/
def schemeModuleHomSourceShortComplex (S : ShortComplex X.Modules)
    (K : CochainComplex X.Modules ℕ) : ShortComplex (CochainComplex X.Modules ℕ) :=
  ShortComplex.mk (schemeModuleHomCoefficientComplexMap S.g K)
    (schemeModuleHomCoefficientComplexMap S.f K) (by
      ext j : 1
      change schemeModuleHomPrecompose S.g ≫ schemeModuleHomPrecompose S.f = 0
      rw [← schemeModuleHomPrecompose_comp, S.zero]
      exact schemeModuleHomPrecompose_zero S.X₁ S.X₃ (K.X j))

/-- Exactness for ACTUAL injective coefficients,proved degreewise.
No desired short exactness of the Hom complexes is an input premise. -/
theorem schemeModuleHomSourceShortComplex_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (K : CochainComplex X.Modules ℕ) [∀ j, Injective (K.X j)] :
    (schemeModuleHomSourceShortComplex S K).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  letI := schemeModuleInternalHomFunctor_preservesFiniteLimits X (K.X j)
  letI := schemeModuleInjectiveInternalHom_preservesFiniteColimits X (K.X j)
  change (S.op.map (schemeModuleInternalHomFunctor X (K.X j))).ShortExact
  exact hS.op.map_of_exact _

/-- Every actual differential-degree map retains the SAME original source map. -/
theorem schemeModuleHomCoefficientComplexMap_f {A B : X.Modules} (f : A ⟶ B)
    (K : CochainComplex X.Modules ℕ) (j : ℕ) :
    (schemeModuleHomCoefficientComplexMap f K).f j =
      schemeModuleHomPrecompose (N := K.X j) f := rfl

end LinearStudy
