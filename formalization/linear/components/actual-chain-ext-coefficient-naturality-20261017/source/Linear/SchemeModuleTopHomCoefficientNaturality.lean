module
public import Linear.SchemeModuleChainTopOpcycleIso
public import Linear.SchemeModuleChainTopHomology
public import Linear.SchemeModuleHomCokernelCoefficientNaturality
public import Linear.SchemeModuleSourceHomCoefficientComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- Actual coefficient map on the cokernel of SAME original Hom differential. -/
def schemeModuleChainDifferentialHomCokernelCoefficientMap (K : ChainComplex X.Modules ℕ)
    (p : ℕ) {N M : X.Modules} (c : N ⟶ M) :
    cokernel (schemeModuleHomPrecompose (N := N) (K.d (p+1) p)) ⟶
      cokernel (schemeModuleHomPrecompose (N := M) (K.d (p+1) p)) :=
  cokernel.map _ _ (schemeModuleHomPostcompose (P := K.X p) c)
    (schemeModuleHomPostcompose (P := K.X (p+1)) c)
    ((schemeModuleInternalHomSourceNatTrans (K.d (p+1) p)).naturality c).symm

/-- SAME differential-Hom cokernel projection retains coefficient action. -/
theorem schemeModuleChainDifferentialHomCokernelCoefficientMap_projection
    (K : ChainComplex X.Modules ℕ) (p : ℕ) {N M : X.Modules} (c : N ⟶ M) :
    cokernel.π (schemeModuleHomPrecompose (N := N) (K.d (p+1) p)) ≫
        schemeModuleChainDifferentialHomCokernelCoefficientMap K p c =
      schemeModuleHomPostcompose (P := K.X (p+1)) c ≫
        cokernel.π (schemeModuleHomPrecompose (N := M) (K.d (p+1) p)) :=
  cokernel.π_desc _ _ _

/-- SAME actual top-opcycle quotient transport commutes with coefficients. -/
theorem schemeModuleChainTopHomCokernelIso_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (p : ℕ) (hAbove : IsZero (K.X (p+2)))
    {N M : X.Modules} (c : N ⟶ M) :
    schemeModuleHomSourceCokernelCoefficientMap (schemeModuleChainOpcycleSequence K p) c ≫
        (schemeModuleChainTopHomCokernelIso K M p hAbove).hom =
      (schemeModuleChainTopHomCokernelIso K N p hAbove).hom ≫
        schemeModuleChainDifferentialHomCokernelCoefficientMap K p c := by
  apply (cancel_epi (cokernel.π
    (schemeModuleHomPrecompose (N := N) (K.fromOpcycles (p+1) p)))).1
  erw [← Category.assoc,schemeModuleHomSourceCokernelCoefficientMap_projection (schemeModuleChainOpcycleSequence K p) c,
    Category.assoc,schemeModuleChainTopHomCokernelIso_hom K M p hAbove]
  erw [← Category.assoc,(schemeModuleInternalHomSourceNatTrans (K.pOpcycles (p+1))).naturality c,
    Category.assoc,← schemeModuleChainDifferentialHomCokernelCoefficientMap_projection K p c,
    ← Category.assoc,← schemeModuleChainTopHomCokernelIso_hom K N p hAbove,Category.assoc]

/-- Native SAME Hom-complex homology commutes with its specified-index short complex.
This is derived from mathlib's ACTUAL natIsoSc',not an assumed comparison square. -/
theorem schemeModuleSourceHomHomologyIsoSc_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (p : ℕ) {N M : X.Modules} (c : N ⟶ M) :
    HomologicalComplex.homologyMap (schemeModuleSourceHomCoefficientComplexMap K c) (p+1) ≫
        ((schemeModuleInternalHomCochainComplex M K).homologyIsoSc'
          p (p+1) (p+2) (by simp) (by simp)).hom =
      ((schemeModuleInternalHomCochainComplex N K).homologyIsoSc'
          p (p+1) (p+2) (by simp) (by simp)).hom ≫
        ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' X.Modules
          (ComplexShape.up ℕ) p (p+1) (p+2)).map (schemeModuleSourceHomCoefficientComplexMap K c)) := by
  have h := congrArg (fun f => ShortComplex.homologyMap f)
    ((HomologicalComplex.natIsoSc' X.Modules (ComplexShape.up ℕ)
      p (p+1) (p+2) (by simp) (by simp)).hom.naturality
        (schemeModuleSourceHomCoefficientComplexMap K c))
  dsimp only [HomologicalComplex.homologyMap,HomologicalComplex.homologyIsoSc',
    ShortComplex.homologyMapIso,HomologicalComplex.isoSc',Iso.app,HomologicalComplex.homology]
  simpa only [ShortComplex.homologyMap_comp] using h

end LinearStudy
