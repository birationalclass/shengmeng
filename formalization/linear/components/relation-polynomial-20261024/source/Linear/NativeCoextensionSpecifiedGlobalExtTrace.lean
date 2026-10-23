module
public import Linear.NativeCoextensionSpecifiedEvaluationTrace
public import Linear.SchemeModuleActualTraceCalibration
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K S : Type} [Field K] {σ : Type} [Fintype σ] [LinearOrder σ]
variable [CommRing S] [Algebra K S] [Algebra (MvPolynomial σ K) S]
variable [IsScalarTower K (MvPolynomial σ K) S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule σ K) B]
variable [IsDomain S] [IsNoetherianRing S] [Algebra.FiniteType K S]
variable [Module.Finite (MvPolynomial σ K) S]
attribute [local instance] coextensionGradedBaseModule nativeCoextensionNormalizationBaseModule
  coextensionGradedDecomposition coextensionOriginalBaseScalarTower
attribute [local instance] coextensionTraceBaseSourceTower coextensionTraceFieldSourceTower
  coextensionTraceFiniteBase coextensionTraceFiniteSource coextensionTraceTorsionFree
  schemeModuleActualCohomologyAddCommGroup
attribute [local irreducible] nativeCoextensionSpecifiedTopEvaluationTrace nativeProjectiveModuleSheaf
/-- The ACTUAL global unit-Ext trace supplied by the CONSTRUCTED model
trace and SAME canonical Ext/H comparison. It is not an arbitrary trace
certificate or normalized geometric trace identification. -/
def nativeCoextensionSpecifiedTopGlobalExtTrace
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2) :
    Ext.{0} (SheafOfModules.unit (Proj B).ringCatSheaf)
      (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
        (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))) (q+1) →+ K :=
  schemeModuleActualHToGlobalExtTrace
    (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard)
/-- Exact underlying value through the SAME canonical original Ext/H map. -/
theorem nativeCoextensionSpecifiedTopGlobalExtTrace_apply
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    (z : Ext.{0} (SheafOfModules.unit (Proj B).ringCatSheaf)
      (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
        (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))) (q+1)) :
    nativeCoextensionSpecifiedTopGlobalExtTrace B c hc hgenC q hcard z =
      nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
        (schemeModuleGlobalExtActualHAddEquiv (Proj B)
          (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
            (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))) (q+1) z) := by
  rfl
/-- For EVERY ACTUAL source sheaf and coefficient morphism,the ORIGINAL
Ext pairing is actual H.map followed by the CONSTRUCTED model trace.
No coefficient naturality or trace-compatibility certificate is an input. -/
theorem nativeCoextensionSpecifiedTopGlobalExtTrace_actualPairing
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    {F : (Proj B).Modules}
    (a : F ⟶ nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
      (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ)))
    (x : schemeModuleActualCohomology (Proj B) F (q+1)) :
    schemeModuleActualHTracePairing
      (nativeCoextensionSpecifiedTopGlobalExtTrace B c hc hgenC q hcard) a x =
    nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
      (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map a) (q+1) x) := by
  exact schemeModuleActualHToGlobalExtTrace_pairing
    (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard) a x
/-- Specialize the SAME ORIGINAL chain/Koszul roof formula to the
CONSTRUCTED coextension model trace. The actual-H trace parameter is
DISCHARGED. The actual chain,augmentation,top identification,small Ext
class and actual original boundary are unchanged. Canonical/geometric
trace identification and the original right nondegeneracy remain separate. -/
theorem nativeCoextensionSpecifiedTopGlobalExtTrace_originalBoundary
    {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
    (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
    (q : ℕ) (hcard : Fintype.card σ=q+2)
    {G F : (Proj B).Modules} (CC : ChainComplex (Proj B).Modules ℕ)
    (alpha : CC ⟶ (ChainComplex.single₀ (Proj B).Modules).obj G) (hAlpha : QuasiIso alpha)
    (hAbove : CategoryTheory.Limits.IsZero (CC.X ((q+1)+1))) (phi : CC.X (q+1) ≅ F)
    (a : F ⟶ nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
      (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ)))
    (s : Γ(G,⊤)) :
    nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard
      (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map a) (q+1)
        (schemeModuleOriginalActualSectionBoundary CC (q+1) alpha hAlpha hAbove phi s)) =
    schemeModuleExtSectionTracePairing
      (nativeCoextensionSpecifiedTopGlobalExtTrace B c hc hgenC q hcard)
      (schemeModuleExtClassCoefficientPushforwardAddHom
        (schemeModuleOriginalChainTopExtClassSmall CC (q+1) alpha hAlpha phi.hom
          (hAbove.eq_of_src _ _)) a) s := by
  exact schemeModuleOriginalActualSectionBoundary_actualH_trace_transpose
    CC (q+1) alpha hAlpha hAbove phi a
      (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard) s
end LinearStudy
