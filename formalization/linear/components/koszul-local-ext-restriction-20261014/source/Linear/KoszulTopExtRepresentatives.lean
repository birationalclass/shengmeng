module
public import Linear.KoszulTopDualCokernelRestriction
public import Linear.KoszulFunctionResolution
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian RingTheory.Sequence
universe u
variable {R : Type u} [CommRing R] (n : ℕ)
variable (H : Fin (n+1) → R) (hreg : IsRegular R (List.ofFn H))

/-- The ACTUAL original top functional is a cocycle for the ACTUAL
original regular-list Koszul projective resolution;the next term is zero. -/
theorem koszulTopFunctional_isCocycle
    (L : Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R))) :
    (functionKoszulResolution H hreg).complex.d (n+2) (n+1) ≫ ModuleCat.ofHom L=0 := by
  have hz : IsZero ((koszulComplex (Fintype.linearCombination R H)).X (n+2)) :=
    koszulComplex.isZero_X_of_card_generators_lt _ (Pi.basisFun R (Fin (n+1)))
      (Pi.basisFun R (Fin (n+1))).span_eq (n+2) (by simp)
  exact hz.eq_of_src _ _

/-- Construct the ACTUAL derived Ext representative from the ORIGINAL
regular Koszul resolution using existing mathlib ProjectiveResolution.extMk.
No Ext/comparison isomorphism is a premise. -/
def koszulTopExtRepresentative
    (L : Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R))) :
    Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) (ModuleCat.of R R) (n+1) :=
  (functionKoszulResolution H hreg).extMk (ModuleCat.ofHom L) (n+2) rfl
    (koszulTopFunctional_isCocycle n H hreg L)

/-- The ACTUAL original derived Ext representative is zero exactly when
its ORIGINAL top coefficient belongs to the ORIGINAL equation ideal. -/
theorem koszulTopExtRepresentative_eq_zero_iff
    (L : Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R))) :
    koszulTopExtRepresentative n H hreg L=0 ↔
      L (topKoszulGenerator (n+1)) ∈ Ideal.span (Set.range H) := by
  refine ((functionKoszulResolution H hreg).extMk_eq_zero_iff
    (ModuleCat.ofHom L) (n+2) rfl (koszulTopFunctional_isCocycle n H hreg L) n rfl).trans ?_
  constructor
  · rintro ⟨F,hF⟩
    change (koszulComplex (Fintype.linearCombination R H)).d (n+1) n ≫ F=ModuleCat.ofHom L at hF
    rw [koszulComplex.d_eq_d] at hF
    have hv := congrArg (fun f => f.hom (topKoszulGenerator (n+1))) hF
    change F.hom (koszulComplex.d (Fintype.linearCombination R H) n
      (topKoszulGenerator (n+1)))=L (topKoszulGenerator (n+1)) at hv
    rw [← hv]
    exact koszul_top_differential_functional_mem n H F.hom
  · intro hm
    rw [← koszulTopDualDifferentialCoordinate_range n H] at hm
    obtain ⟨F,hF⟩ := hm
    have hd : (koszulComplex.d (Fintype.linearCombination R H) n).dualMap F=L := by
      apply (koszulTopFunctionalEquiv n).injective
      exact hF
    refine ⟨ModuleCat.ofHom F,?_⟩
    change (koszulComplex (Fintype.linearCombination R H)).d (n+1) n ≫ ModuleCat.ofHom F=ModuleCat.ofHom L
    rw [koszulComplex.d_eq_d]
    exact ModuleCat.hom_ext hd

/-- EVERY ACTUAL original derived Ext class has an ORIGINAL Koszul top
functional representative,using the existing projective-resolution API. -/
theorem koszulTopExtRepresentative_surjective :
    Function.Surjective (koszulTopExtRepresentative n H hreg) := by
  intro a
  obtain ⟨f,hf,h⟩ := (functionKoszulResolution H hreg).extMk_surjective a (n+2) rfl
  exact ⟨f.hom,h⟩

/-- Push the ACTUAL original Ext representative along an ORIGINAL
R-linear a:R->R. Existing mathlib extMk_comp_mk0 preserves the actual
original functional representative,not merely an abstract Ext class. -/
theorem koszulTopExtRepresentative_push
    (L : Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R))) (a : R →ₗ[R] R) :
    (koszulTopExtRepresentative n H hreg L).comp (Ext.mk₀ (ModuleCat.ofHom a)) (add_zero _) =
      koszulTopExtRepresentative n H hreg (a.comp L) :=
  (functionKoszulResolution H hreg).extMk_comp_mk₀ (ModuleCat.ofHom L) (n+2) rfl
    (koszulTopFunctional_isCocycle n H hreg L) (ModuleCat.ofHom a)

end LinearStudy
