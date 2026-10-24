module
public import Linear.NativeCoextensionSpecifiedEvaluationTrace
public import Linear.NativeCoextensionSpecifiedTraceInjective
public import Linear.NativeCoextensionSpecifiedTraceProperties
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
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
attribute [local irreducible] nativeFiniteNormalization_specifiedActualTopHomDualIso
variable [IsAlgClosed K] [FaithfulSMul (MvPolynomial σ K) S]
variable {κ : Type} (c : κ → S) (hc : ∀ i,c i ∈ B 1)
variable (hgenC : Algebra.adjoin K (Set.range c) = ⊤)
variable (q : ℕ) (hcard : Fintype.card σ=q+2)
/-- The SAME trace is linear for the ORIGINAL coefficient action on
actual H. Reuse the already proved original scalar comparison;no scalar
action is transported through a chosen equivalence. -/
theorem nativeCoextensionSpecifiedTopEvaluationTrace_originalScalar
    (a : K) (x : schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))) (q+1)) :
    nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map (originalGlobalModuleScalar ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))))) (q+1) x) = a * nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x := by
  let V := integerGradedHomPiece (MvPolynomial.homogeneousSubmodule σ K)
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
    (-(Fintype.card σ:ℤ)-(-(Fintype.card σ:ℤ)))
  have hs := nativeFiniteNormalization_specifiedActualTopHomDualIso_originalScalar B
    (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionNormalizationBaseGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B)
    c hc hgenC q hcard (-(Fintype.card σ:ℤ)) a x
  exact congrArg (fun f : Module.Dual K V => f (nativeCoextensionSpecifiedTopEvaluationHom B)) hs
/-- The SAME trace takes EVERY original field value on actual H;unit
normalization and original scalar linearity are proved,not supplied. -/
theorem nativeCoextensionSpecifiedTopEvaluationTrace_surjective :
    Function.Surjective (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard) := by
  obtain ⟨x,hx⟩ := nativeCoextensionSpecifiedTopEvaluationTrace_exists_one B c hc hgenC q hcard
  intro a
  refine ⟨CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map (originalGlobalModuleScalar ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))))) (q+1) x,?_⟩
  rw [nativeCoextensionSpecifiedTopEvaluationTrace_originalScalar B c hc hgenC q hcard,hx,mul_one]
/-- The ORIGINAL actual top-H model trace is bijective. In particular
its trace space is one dimensional over the original coefficient field;
this does not identify a geometric proper trace or canonical coefficient. -/
theorem nativeCoextensionSpecifiedTopEvaluationTrace_bijective :
    Function.Bijective (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard) :=
  ⟨nativeCoextensionSpecifiedTopEvaluationTrace_injective B c hc hgenC q hcard,
    nativeCoextensionSpecifiedTopEvaluationTrace_surjective B c hc hgenC q hcard⟩
/-- EVERY nonzero functional on the SAME actual H,linear for ORIGINAL
coefficient multiplication,is a NONZERO scalar multiple of the SAME
model trace. Application to a geometric proper trace still requires its
actual coefficient identification and original scalar compatibility. -/
theorem nativeCoextensionSpecifiedTopEvaluationTrace_nonzero_scalar_transfer
    (ell : (schemeModuleActualCohomology (Proj B) (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))) (q+1)) →+ K)
    (hlinear : ∀ a : K,∀ x,ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map (originalGlobalModuleScalar ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a)) (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))))) (q+1) x)=a * ell x)
    (hne : ell ≠ 0) :
    ∃ a : K,a ≠ 0 ∧ ∀ x,ell x=a * nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x := by
  obtain ⟨x0,hx0⟩ := nativeCoextensionSpecifiedTopEvaluationTrace_exists_one B c hc hgenC q hcard
  have form (x) : ell x=ell x0 * nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x := by
    have hx : x=CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map (originalGlobalModuleScalar ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x))) (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))))) (q+1) x0 := by
      apply nativeCoextensionSpecifiedTopEvaluationTrace_injective B c hc hgenC q hcard
      rw [nativeCoextensionSpecifiedTopEvaluationTrace_originalScalar B c hc hgenC q hcard,hx0,mul_one]
    calc
      ell x=ell (CategoryTheory.Sheaf.H.map ((schemeModuleToActualAbelianSheaf (Proj B)).map (originalGlobalModuleScalar ((Proj.toSpecZero B ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B 0)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv (nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x))) (nativeProjectiveModuleSheaf B (coextensionGradedPiece (MvPolynomial.homogeneousSubmodule σ K) B) (coextensionProjectiveGradeCompatibility (MvPolynomial.homogeneousSubmodule σ K) B) (-(Fintype.card σ:ℤ))))) (q+1) x0) := congrArg ell hx
      _=nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x * ell x0 := hlinear _ _
      _=ell x0 * nativeCoextensionSpecifiedTopEvaluationTrace B c hc hgenC q hcard x := mul_comm _ _
  refine ⟨ell x0,?_,form⟩
  intro hz
  apply hne
  ext x
  rw [form,hz,zero_mul]
  rfl
end LinearStudy
