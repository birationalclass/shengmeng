module
public import Linear.ProjectiveCanonicalResidue
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} {σ : Type} [CommRing R] [Fintype σ] [LinearOrder σ]

/-- Actual homogeneous Laurent Cech cochains vanish above the size of the
coordinate cover, because there are no increasing tuples of that length. -/
theorem coordinateHomogeneousLaurentOrderedCech_eq_zero_of_card_le
    (d : ℤ) (n : ℕ) (hn : Fintype.card σ ≤ n)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n) :
    s = 0 := by
  letI : IsEmpty (Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n) :=
    Scheme.Modules.isEmpty_orderedCechIndex_of_card_le _ n (by simpa using hn)
  apply Concrete.limit_ext (Discrete.functor fun
    a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      ModuleCat.of (coordinateCanonicalBaseRing R)
        (AddMonoidAlgebra (coordinateCanonicalBaseRing R)
          {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun k => (a.1 k).down)}))
  intro a
  rcases a with ⟨a⟩
  exact isEmptyElim a

/-- Every actual top cochain is a cocycle. This removes an extra cycle
hypothesis when computing the top residue quotient. -/
theorem coordinateHomogeneousLaurent_top_is_cycle (d : ℤ) (n : ℕ)
    (hc : Fintype.card σ = n+1)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n) :
    (coordinateHomogeneousLaurentOrderedCechDifferential
      (R := R) (σ := σ) d n).hom s = 0 :=
  coordinateHomogeneousLaurentOrderedCech_eq_zero_of_card_le d (n+1)
    (by omega) _
end MvPolynomial
