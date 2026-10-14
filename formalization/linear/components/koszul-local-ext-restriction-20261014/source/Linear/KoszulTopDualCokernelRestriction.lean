module
public import Linear.KoszulTopComplementFunctional
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
variable {R : Type*} [CommRing R] (n : ℕ)

/-- Evaluate the ACTUAL original dual top differential on the ORIGINAL
ordered top generator. -/
def koszulTopDualDifferentialCoordinate (H : Fin (n+1) → R) :
    Module.Dual R (⋀[R]^n (Fin (n+1) → R)) →ₗ[R] R where
  toFun L := L (koszulComplex.d (Fintype.linearCombination R H) n (topKoszulGenerator (n+1)))
  map_add' L F := rfl
  map_smul' c L := rfl

/-- The image of the ACTUAL original dual top differential coordinates
is EXACTLY the ORIGINAL equation ideal,for every commutative ring and
original list. No regularity or already-known quotient is assumed. -/
theorem koszulTopDualDifferentialCoordinate_range (H : Fin (n+1) → R) :
    LinearMap.range (koszulTopDualDifferentialCoordinate n H)=Ideal.span (Set.range H) := by
  apply le_antisymm
  · rintro y ⟨L,rfl⟩
    exact koszul_top_differential_functional_mem n H L
  · change Submodule.span R (Set.range H) ≤ LinearMap.range (koszulTopDualDifferentialCoordinate n H)
    apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    exact ⟨koszulTopComplementFunctional n i,koszulTopComplementFunctional_differential n H i⟩

/-- The actual top dual functional is identified with its ORIGINAL
coefficient at the ORIGINAL ordered top generator. -/
def koszulTopFunctionalEquiv :
    Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R)) ≃ₗ[R] R where
  toFun L := L (topKoszulGenerator (n+1))
  invFun r := r • topKoszulCoordinate (n+1)
  left_inv L := by
    apply LinearMap.ext
    intro x
    have hx : L x=topKoszulCoordinate (n+1) x * L (topKoszulGenerator (n+1)) := by
      calc
        L x=L (topKoszulCoordinate (n+1) x • topKoszulGenerator (n+1)) :=
          congrArg L (topKoszulCoordinate_reconstruct (n+1) x).symm
        _ = _ := by rw [map_smul]; rfl
    change L (topKoszulGenerator (n+1))*topKoszulCoordinate (n+1) x=L x
    exact (mul_comm _ _).trans hx.symm
  right_inv r := by simp [topKoszulCoordinate_generator]
  map_add' L F := rfl
  map_smul' c L := rfl

/-- Actual original top-coefficient restriction to the original cut R/(H).
This is independent of any derived Ext comparison. -/
def koszulTopFunctionalRestriction (H : Fin (n+1) → R) :
    Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] R ⧸ Ideal.span (Set.range H) :=
  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range H))).toLinearMap.comp
    (koszulTopFunctionalEquiv n).toLinearMap

/-- Kernel of ORIGINAL coefficient restriction is the image of the
ACTUAL ORIGINAL dual top differential. -/
theorem koszulTopFunctionalRestriction_kernel (H : Fin (n+1) → R) :
    LinearMap.ker (koszulTopFunctionalRestriction n H)=
      LinearMap.range (koszulComplex.d (Fintype.linearCombination R H) n).dualMap := by
  apply le_antisymm
  · intro L hL
    have hm : L (topKoszulGenerator (n+1)) ∈ Ideal.span (Set.range H) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hL
    rw [← koszulTopDualDifferentialCoordinate_range n H] at hm
    obtain ⟨F,hF⟩ := hm
    refine ⟨F,?_⟩
    apply (koszulTopFunctionalEquiv n).injective
    exact hF
  · rintro L ⟨F,rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (koszul_top_differential_functional_mem n H F)

/-- The original coefficient restriction is onto the ORIGINAL cut ring. -/
theorem koszulTopFunctionalRestriction_surjective (H : Fin (n+1) → R) :
    Function.Surjective (koszulTopFunctionalRestriction n H) := by
  intro v
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective v
  refine ⟨(koszulTopFunctionalEquiv n).symm r,?_⟩
  change Ideal.Quotient.mk _ ((koszulTopFunctionalEquiv n) ((koszulTopFunctionalEquiv n).symm r)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- ACTUAL original dual-Koszul top cokernel is the ORIGINAL cut ring.
This computes the local restriction piece,not global derived Ext. -/
def koszulTopDualCokernelEquiv (H : Fin (n+1) → R) :
    (Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R)) ⧸
      LinearMap.range (koszulComplex.d (Fintype.linearCombination R H) n).dualMap) ≃ₗ[R]
      R ⧸ Ideal.span (Set.range H) :=
  (Submodule.quotEquivOfEq _ _ (koszulTopFunctionalRestriction_kernel n H).symm).trans
    ((koszulTopFunctionalRestriction n H).quotKerEquivOfSurjective
      (koszulTopFunctionalRestriction_surjective n H))

/-- The ORIGINAL top functional class is sent to its ORIGINAL coefficient
modulo (H). In a fixed local frame,this is EXACTLY a restricted to S;
the global extension-class and sheaf/derived identifications remain separate. -/
theorem koszulTopDualCokernelEquiv_class (H : Fin (n+1) → R)
    (L : Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R))) :
    koszulTopDualCokernelEquiv n H (Submodule.Quotient.mk L)=
      Ideal.Quotient.mk (Ideal.span (Set.range H)) (L (topKoszulGenerator (n+1))) := by
  rw [koszulTopDualCokernelEquiv,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end LinearStudy
