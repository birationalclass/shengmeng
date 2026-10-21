module
public import Linear.NoetherianInjectiveArtinRees
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
universe u
open scoped BigOperators Pointwise
/-- Pairwise compatible numerators kill every relation after multiplication by the denominator ideal. -/
theorem finiteCompatibleFamily_ideal_kills_relations
    {R I ι : Type u} [CommRing R] [AddCommGroup I] [Module R I] [Fintype ι]
    (b : ι → R) (a : ι → I) (hab : ∀ i j, b j • a i = b i • a j) :
    (Ideal.span (Set.range b)) • LinearMap.ker (Fintype.linearCombination R b) ≤
      LinearMap.ker (Fintype.linearCombination R a) := by
  have hcomp (v : ι → R) (j : ι) :
      b j • Fintype.linearCombination R a v =
        Fintype.linearCombination R b v • a j := by
    simp only [Fintype.linearCombination_apply, Finset.smul_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_comm (b j), hab i j, smul_smul]
    rfl
  apply Submodule.smul_le.mpr
  intro r hr v hv
  change Fintype.linearCombination R a (r • v) = 0
  rw [map_smul]
  let A := LinearMap.ker (LinearMap.toSpanSingleton R I (Fintype.linearCombination R a v))
  have hA : Ideal.span (Set.range b) ≤ A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change b i • Fintype.linearCombination R a v = 0
    rw [hcomp v i, show Fintype.linearCombination R b v = 0 from hv, zero_smul]
  exact hA hr

/-- Over a Noetherian ring, a finite pairwise compatible fraction family in an injective module
has ONE global numerator after a common denominator power. Artin--Rees constructs the missing
relation bound; injectivity supplies the actual global element. -/
theorem noetherian_injective_compatible_family_lift
    {R I ι : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup I] [Module R I] [Module.Injective R I] [Fintype ι]
    (b : ι → R) (a : ι → I) (hab : ∀ i j, b j • a i = b i • a j) :
    ∃ n : ℕ, ∃ x : I, ∀ i, b i ^ (n+1) • x = b i ^ n • a i := by
  classical
  let J : Ideal R := Ideal.span (Set.range b)
  let f : (ι → R) →ₗ[R] R := Fintype.linearCombination R b
  let g : (ι → R) →ₗ[R] I := Fintype.linearCombination R a
  obtain ⟨n,hn,hrel⟩ := noetherian_artinRees_kernel_restriction J f g
    (finiteCompatibleFamily_ideal_kills_relations b a hab)
  let C : Submodule R (ι → R) := J ^ n • ⊤
  obtain ⟨h,hh⟩ := injective_linearMap_extend_of_ker_le (f.comp C.subtype)
    (g.comp C.subtype) (by
      intro v hv
      exact hrel v.val v.property hv)
  refine ⟨n,h 1,?_⟩
  intro i
  have hbi : b i ∈ J := Ideal.subset_span ⟨i,rfl⟩
  have hp : b i ^ n • Pi.single i (1 : R) ∈ C :=
    Submodule.smul_mem_smul (Ideal.pow_mem_pow hbi n)
      (Submodule.mem_top)
  let p : C := ⟨b i ^ n • Pi.single i (1 : R),hp⟩
  have hv := congrArg (fun l => l p) hh
  change h (f p.val) = g p.val at hv
  have hf : f p.val = b i ^ (n+1) := by
    simp [f,p,Fintype.linearCombination_apply_single,pow_succ]
  have hg : g p.val = b i ^ n • a i := by
    simp [g,p,Fintype.linearCombination_apply_single]
  rw [hf,hg] at hv
  rw [← h.map_smul, smul_eq_mul, mul_one]
  exact hv
end LinearStudy