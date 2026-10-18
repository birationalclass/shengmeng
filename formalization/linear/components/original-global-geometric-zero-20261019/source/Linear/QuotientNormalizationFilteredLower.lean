module
public import Linear.PolynomialFilteredImage
public import Linear.PolynomialRectangleDimension
public import Linear.ProjectiveFilteredPullback
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace LinearStudy

/-- Construct a uniform ACTUAL degree bound on the images of a finite
polynomial generating family in the ORIGINAL coordinate quotient. -/
theorem polynomial_to_quotient_exists_filtration_bound
    {k σ τ : Type*} [Field k] [Finite τ]
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I)) :
    ∃ c : ℕ, 0 < c ∧ ∀ p : MvPolynomial τ k,
      g p ∈ homogeneousQuotientFiltration I (c * p.totalDegree) := by
  classical
  letI : Fintype τ := Fintype.ofFinite τ
  choose H hH using fun i : τ => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let c := 1 + Finset.univ.sup (fun i : τ => (H i).totalDegree)
  have hXi : ∀ i : τ, g (MvPolynomial.X i) ∈ homogeneousQuotientFiltration I c := by
    intro i
    apply (homogeneousQuotientFiltration_mem_iff I c _).mpr
    refine ⟨H i, ?_, hH i⟩
    exact (Finset.le_sup (f := fun i : τ => (H i).totalDegree) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ _)
  have h1 : (1 : MvPolynomial σ k ⧸ I) ∈ homogeneousQuotientFiltration I 0 :=
    (homogeneousQuotientFiltration_mem_iff I 0 _).mpr ⟨1, by simp, map_one _⟩
  refine ⟨c, by simp [c], ?_⟩
  intro p
  have hp := polynomial_image_mem_filtration g (homogeneousQuotientFiltration I)
    (fun _ _ h => homogeneousQuotientFiltration_mono I h) c 0 h1
    (fun N a ha i => homogeneousQuotientFiltration_mul_mem I N c a _ ha (hXi i)) p
  simpa only [Nat.add_zero] using hp

/-- An actual injective normalization supplies a LOWER dimension bound on
the original polynomial filtration; neither its growth nor dimension is assumed. -/
theorem quotient_normalization_filtration_lower
    {k σ τ : Type*} [Field k] [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) :
    ∃ c : ℕ, 0 < c ∧ ∀ N : ℕ,
      (N + 1) ^ Nat.card τ ≤
        Module.finrank k (homogeneousQuotientFiltration I (c * (Nat.card τ * N))) := by
  obtain ⟨c, hc, hbound⟩ := polynomial_to_quotient_exists_filtration_bound I g
  refine ⟨c, hc, ?_⟩
  intro N
  let L := g.toLinearMap.domRestrict (MvPolynomial.restrictDegree τ k N)
  have hmem : ∀ p : MvPolynomial.restrictDegree τ k N,
      L p ∈ homogeneousQuotientFiltration I (c * (Nat.card τ * N)) := by
    intro p
    apply homogeneousQuotientFiltration_mono I _ (hbound p)
    exact Nat.mul_le_mul_left c ((MvPolynomial.mem_restrictTotalDegree τ _ _).mp
      (polynomial_restrictDegree_le_totalDegree k τ N p.property))
  let T := L.codRestrict (homogeneousQuotientFiltration I (c * (Nat.card τ * N))) hmem
  have hT : Function.Injective T := by
    intro p q heq
    apply Subtype.ext
    exact hg (congrArg Subtype.val heq)
  letI := homogeneousQuotientFiltration_finite I (c * (Nat.card τ * N))
  have h := LinearMap.finrank_le_finrank_of_injective hT
  simpa [polynomial_restrictDegree_finrank k τ N] using h

end LinearStudy
