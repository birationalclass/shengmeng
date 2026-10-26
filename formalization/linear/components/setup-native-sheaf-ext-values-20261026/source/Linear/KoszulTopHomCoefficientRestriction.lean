module
public import Linear.KoszulTopComplementFunctional
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Ideal.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
open scoped BigOperators Pointwise
namespace LinearStudy
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N] (n : ℕ)

/-- ORIGINAL top Hom into ANY ORIGINAL coefficient module N is identified
with its SAME ORIGINAL ordered top-generator value;N need not be free. -/
def koszulTopHomCoefficientEquiv :
    ((⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) ≃ₗ[R] N where
  toFun L := L (topKoszulGenerator (n+1))
  invFun a := (topKoszulCoordinate (n+1)).smulRight a
  left_inv L := by
    apply LinearMap.ext
    intro x
    change topKoszulCoordinate (n+1) x • L (topKoszulGenerator (n+1)) = L x
    exact (map_smul L _ _).symm.trans (congrArg L (topKoszulCoordinate_reconstruct (n+1) x))
  right_inv a := by simp only [LinearMap.smulRight_apply,topKoszulCoordinate_generator,one_smul]
  map_add' L F := rfl
  map_smul' c L := rfl

/-- Evaluate ACTUAL original Koszul precomposition in ANY original N
at the SAME original ordered top generator. -/
def koszulTopHomDifferentialCoordinate (H : Fin (n+1) → R) :
    ((⋀[R]^n (Fin (n+1) → R)) →ₗ[R] N) →ₗ[R] N :=
  (koszulTopHomCoefficientEquiv n).toLinearMap.comp
    (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n))

/-- ACTUAL top precomposition has image EXACTLY I N in the ORIGINAL N,
with I=(ORIGINAL H). No FP/free/invertible/flat/CM conditions on N. -/
theorem koszulTopHomDifferentialCoordinate_range (H : Fin (n+1) → R) :
    LinearMap.range (koszulTopHomDifferentialCoordinate (N := N) n H) =
      Ideal.span (Set.range H) • (⊤ : Submodule R N) := by
  apply le_antisymm
  · rintro y ⟨L,rfl⟩
    change L (koszulComplex.d (Fintype.linearCombination R H) n
      (topKoszulGenerator (n+1))) ∈ _
    classical
    rw [topKoszulGenerator,koszulComplex.d,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      koszulComplex.dAlternating_apply,map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    simp only [Pi.basisFun_apply,Fintype.linearCombination_apply_single,one_smul]
    exact Submodule.smul_mem_smul
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))) Submodule.mem_top
  · rw [← Submodule.coe_set_smul,Submodule.coe_span_smul]
    apply Submodule.set_smul_le
    rintro r a ⟨i,rfl⟩ ha
    refine ⟨(LinearMap.toSpanSingleton R N a).comp (koszulTopComplementFunctional n i),?_⟩
    change (LinearMap.toSpanSingleton R N a)
      (koszulTopComplementFunctional n i
        (koszulComplex.d (Fintype.linearCombination R H) n
          (topKoszulGenerator (n+1)))) = H i • a
    rw [koszulTopComplementFunctional_differential]
    rfl

/-- SAME original top functional restricted to SAME original coefficient
quotient N/I N. No freeness/regularity comparison assumption. -/
def koszulTopHomCoefficientRestriction (H : Fin (n+1) → R) :
    ((⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) →ₗ[R]
      N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)) :=
  (Ideal.span (Set.range H) • (⊤ : Submodule R N)).mkQ.comp
    (koszulTopHomCoefficientEquiv n).toLinearMap

/-- Kernel of ORIGINAL N-coefficient restriction is EXACTLY image of
ACTUAL original precomposition by the SAME original Koszul d. -/
theorem koszulTopHomCoefficientRestriction_kernel (H : Fin (n+1) → R) :
    LinearMap.ker (koszulTopHomCoefficientRestriction (N := N) n H) =
      LinearMap.range (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n)) := by
  apply le_antisymm
  · intro L hL
    have hm : L (topKoszulGenerator (n+1)) ∈
        Ideal.span (Set.range H) • (⊤ : Submodule R N) := (Submodule.Quotient.mk_eq_zero _).mp hL
    rw [← koszulTopHomDifferentialCoordinate_range n H] at hm
    obtain ⟨F,hF⟩ := hm
    refine ⟨F,?_⟩
    apply (koszulTopHomCoefficientEquiv n).injective
    exact hF
  · rintro L ⟨F,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact LinearMap.mem_range_self (koszulTopHomDifferentialCoordinate (N := N) n H) F
      |> (koszulTopHomDifferentialCoordinate_range n H).le

/-- ORIGINAL coefficient restriction is onto N/I N for ANY original N. -/
theorem koszulTopHomCoefficientRestriction_surjective (H : Fin (n+1) → R) :
    Function.Surjective (koszulTopHomCoefficientRestriction (N := N) n H) := by
  intro v
  obtain ⟨a,rfl⟩ := Submodule.mkQ_surjective _ v
  refine ⟨(koszulTopHomCoefficientEquiv n).symm a,?_⟩
  change Submodule.Quotient.mk ((koszulTopHomCoefficientEquiv n)
    ((koszulTopHomCoefficientEquiv n).symm a)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- The actual ORIGINAL Hom-Koszul top cokernel into ANY original N is
CONSTRUCTED isomorphic to ORIGINAL N/I N. -/
def koszulTopHomCokernelCoefficientEquiv (H : Fin (n+1) → R) :
    (((⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) ⧸
      LinearMap.range (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n))) ≃ₗ[R]
      N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)) :=
  (Submodule.quotEquivOfEq _ _ (koszulTopHomCoefficientRestriction_kernel n H).symm).trans
    ((koszulTopHomCoefficientRestriction n H).quotKerEquivOfSurjective
      (koszulTopHomCoefficientRestriction_surjective n H))

/-- ORIGINAL class [L] goes to SAME ORIGINAL L(v_r) modulo ORIGINAL I N. -/
theorem koszulTopHomCokernelCoefficientEquiv_class (H : Fin (n+1) → R)
    (L : (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) :
    koszulTopHomCokernelCoefficientEquiv n H (Submodule.Quotient.mk L) =
      Submodule.Quotient.mk (L (topKoszulGenerator (n+1))) := by
  rw [koszulTopHomCokernelCoefficientEquiv,LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end LinearStudy