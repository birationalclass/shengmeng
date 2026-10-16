module
public import Linear.SchemeModuleInternalHomBifunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Actual coefficient map on SAME source-chain internal Hom complex.
Its differential square is the PROVED actual Hom bifunctor square. -/
def schemeModuleSourceHomCoefficientComplexMap (K : ChainComplex X.Modules ℕ)
    {N M : X.Modules} (c : N ⟶ M) :
    schemeModuleInternalHomCochainComplex N K ⟶ schemeModuleInternalHomCochainComplex M K where
  f p := schemeModuleHomPostcompose (P := K.X p) c
  comm' i j _ := ((schemeModuleInternalHomSourceNatTrans (K.d j i)).naturality c).symm

/-- Actual coefficient identity remains identity on SAME source-Hom complex. -/
theorem schemeModuleSourceHomCoefficientComplexMap_id (K : ChainComplex X.Modules ℕ)
    (N : X.Modules) : schemeModuleSourceHomCoefficientComplexMap K (𝟙 N) = 𝟙 _ := by
  ext p : 1
  exact schemeModuleHomPostcompose_id

/-- Actual coefficient composition remains composition on SAME source-Hom complex. -/
theorem schemeModuleSourceHomCoefficientComplexMap_comp (K : ChainComplex X.Modules ℕ)
    {N M P : X.Modules} (c : N ⟶ M) (d : M ⟶ P) :
    schemeModuleSourceHomCoefficientComplexMap K (c ≫ d) =
      schemeModuleSourceHomCoefficientComplexMap K c ≫ schemeModuleSourceHomCoefficientComplexMap K d := by
  ext p : 1
  exact schemeModuleHomPostcompose_comp c d

/-- Actual internal Hom of SAME source chain is a coefficient functor. -/
def schemeModuleSourceHomCoefficientComplexFunctor (K : ChainComplex X.Modules ℕ) :
    X.Modules ⥤ CochainComplex X.Modules ℕ where
  obj N := schemeModuleInternalHomCochainComplex N K
  map c := schemeModuleSourceHomCoefficientComplexMap K c
  map_id N := schemeModuleSourceHomCoefficientComplexMap_id K N
  map_comp c d := schemeModuleSourceHomCoefficientComplexMap_comp K c d

/-- Native cohomology of SAME Hom complex is an actual coefficient functor.
This constructs the TARGET functor for comparison naturality,not that naturality proof. -/
def schemeModuleSourceHomCohomologyFunctor (K : ChainComplex X.Modules ℕ) (q : ℕ) :
    X.Modules ⥤ X.Modules :=
  schemeModuleSourceHomCoefficientComplexFunctor K ⋙
    HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℕ) q

/-- Coefficient action is native homologyMap of SAME actual complex map. -/
theorem schemeModuleSourceHomCohomologyFunctor_map (K : ChainComplex X.Modules ℕ)
    (q : ℕ) {N M : X.Modules} (c : N ⟶ M) :
    (schemeModuleSourceHomCohomologyFunctor K q).map c =
      HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) q := rfl

end LinearStudy
