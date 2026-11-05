module
public import Linear.ProjectiveNegativeWeightComplement
public import Linear.ProjectiveLaurentGeneralTopBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {σ : Type} [CommRing R] [Fintype σ] [LinearOrder σ]

/-- All the top negative-weight coefficients, in the actual coordinate complex. -/
def coordinateGeneralResidue (m n : ℕ) (hc : Fintype.card σ = n+1) :
    coordinateHomogeneousLaurentOrderedCechObject
      (R := R) (σ := σ) (-(m : ℤ)-Fintype.card σ) n →ₗ[coordinateCanonicalBaseRing R]
      (ProjectiveNegativeWeight σ m → coordinateCanonicalBaseRing R) where
  toFun s e := (coordinateHomogeneousLaurentWeightComponent (R := R)
    (-(m : ℤ)-Fintype.card σ) e.1 n s).1
      (LinearStudy.orderedCechFullIndex n (by simpa using hc))
  map_add' s t := by ext e; simp
  map_smul' r s := by ext e; simp

theorem projectiveNegativeWeight_liftedSupport (m : ℕ) (e : ProjectiveNegativeWeight σ m) :
    (e.1.liftedNegativeSupport : Set (ULift.{u} σ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro i
  exact e.2 i.down

/-- The kernel of all residue coordinates is exactly the actual boundary
space for every complementary degree -m-card(sigma). -/
theorem coordinateGeneralResidue_ker_eq_range (m n : ℕ) (hc : Fintype.card σ = n+2) :
    LinearMap.ker (coordinateGeneralResidue (R := R) m (n+1) hc) =
      LinearMap.range (coordinateHomogeneousLaurentOrderedCechDifferential
        (R := R) (σ := σ) (-(m : ℤ)-Fintype.card σ) n).hom := by
  ext s
  constructor
  · intro hs
    apply exists_preimage_coordinateLaurent_top_of_full_support_zero _ n hc s
    intro e he
    have hn : ∀ i, e.1 i < 0 := by
      intro i
      have hi : (ULift.up i : ULift.{u} σ) ∈ e.liftedNegativeSupport := by
        rw [he]; trivial
      exact hi
    have hz := congrFun hs (⟨e,hn⟩ : ProjectiveNegativeWeight σ m)
    apply (LinearStudy.orderedCechSupport_top_eval_eq_zero_iff
      (coordinateCanonicalBaseRing R) _ (n+1) (by simpa using hc) _).mp
    exact hz
  · rintro ⟨t,rfl⟩
    apply LinearMap.mem_ker.mpr
    funext e
    change (coordinateHomogeneousLaurentWeightComponent (R := R) _ e.1 (n+1)
      ((coordinateHomogeneousLaurentOrderedCechDifferential (R := R) _ n).hom t)).1 _ = 0
    rw [coordinateLaurent_boundary_full_support_eq_zero _ n hc t e.1
      (projectiveNegativeWeight_liftedSupport m e)]
    rfl
end MvPolynomial
