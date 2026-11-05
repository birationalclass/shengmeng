module
public import Linear.ProjectiveLaurentNatExponent
public import Linear.ProjectiveCechLaurentSections
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
universe u
variable {σ : Type} [Fintype σ]
local instance nativeMonomialLaurentDecidableEq : DecidableEq σ := Classical.decEq σ

/-- Dehomogenizing a monomial deletes exactly its anchor exponent. -/
theorem dehomogenizeAux_monomial_chart {R : Type u} [CommRing R]
    (i : σ) (α : σ →₀ ℕ) (c : R) :
    dehomogenizeAux R i (monomial α c) =
      monomial (α.subtypeDomain (fun j => j ≠ i)) c := by
  rw [dehomogenizeAux,eval₂Hom_monomial,monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  let f : σ → MvPolynomial {j : σ // j ≠ i} R :=
    fun j => (if h : j = i then 1 else X ⟨j,h⟩) ^ α j
  change (∏ j, f j) = ∏ j : {j : σ // j ≠ i}, X j ^ α j.1
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : σ => j ≠ i) f]
  have hn : (∏ j : {j : σ // ¬j ≠ i}, f j.1) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    have hji : j.1 = i := not_ne_iff.mp j.2
    simp [f,hji]
  rw [hn,mul_one]
  apply Finset.prod_congr rfl
  intro j _
  simp only [f,dif_neg j.2]

/-- Every nonnegative homogeneous weight is allowed on every original
coordinate intersection. -/
theorem HomogeneousLaurentExponent.isAllowedOn_of_nonnegative {d : ℤ}
    (e : HomogeneousLaurentExponent σ d) (he : ∀ i, 0 ≤ e.1 i)
    {n : ℕ} (a : Fin (n+1) → σ) : e.IsAllowedOn a := by
  intro i hi
  exact (not_lt_of_ge (he i) hi).elim

/-- The Laurent reindexing of the natural chart monomial recovers its
original homogeneous weight, including the reconstructed anchor degree. -/
theorem coordinateLaurentExponentEquiv_natChart {n : ℕ}
    (a : Fin (n+1) → σ) (m : ℕ)
    (e : HomogeneousLaurentExponent σ (m : ℤ)) (he : ∀ i, 0 ≤ e.1 i) :
    coordinateLaurentExponentEquiv a (m : ℤ)
      (laurentExponentAwayMap (coordinateTailExponent a)
        (e.natExponent.subtypeDomain (fun j => j ≠ a 0))) =
      ⟨e,e.isAllowedOn_of_nonnegative he a⟩ := by
  let out := coordinateLaurentExponentEquiv a (m : ℤ)
    (laurentExponentAwayMap (coordinateTailExponent a)
      (e.natExponent.subtypeDomain (fun j => j ≠ a 0)))
  have hne (i : σ) (hi : i ≠ a 0) : out.1.1 i = e.1 i := by
    dsimp only [out]
    rw [coordinateLaurentExponentEquiv_apply_of_ne a (m : ℤ) _ i hi,
      laurentExponentAwayMap_apply]
    exact e.natExponent_cast_apply he i
  have herase : Finsupp.erase (a 0) out.1.1 = Finsupp.erase (a 0) e.1 := by
    ext i
    by_cases hi : i = a 0
    · subst i
      simp
    · rw [Finsupp.erase_ne hi,Finsupp.erase_ne hi,hne i hi]
  have hanchor : out.1.1 (a 0) = e.1 (a 0) := by
    have ho := congrArg Finsupp.degree (Finsupp.single_add_erase (a 0) out.1.1)
    have he' := congrArg Finsupp.degree (Finsupp.single_add_erase (a 0) e.1)
    rw [map_add,Finsupp.degree_single,herase,out.1.property] at ho
    rw [map_add,Finsupp.degree_single,e.property] at he'
    omega
  apply Subtype.ext
  apply Subtype.ext
  ext i
  by_cases hi : i = a 0
  · subst i
    exact hanchor
  · exact hne i hi
end MvPolynomial
