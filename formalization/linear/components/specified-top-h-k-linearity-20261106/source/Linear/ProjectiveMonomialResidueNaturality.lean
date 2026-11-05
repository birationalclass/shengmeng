module
public import Linear.ProjectiveComplementaryCechShift
public import Linear.ProjectiveMonomialDualTranspose
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- The actual top coordinate intersection contains every Laurent weight. -/
theorem homogeneousLaurentWeight_allowed_full {d : ℤ}
    (e : HomogeneousLaurentExponent σ d) (n : ℕ) (hc : Fintype.card σ = n+1) :
    e.IsAllowedOn (fun j => ((LinearStudy.orderedCechFullIndex n
      (by simpa using hc) : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n).1 j).down) := by
  apply (e.isAllowedOn_iff_liftedNegativeSupport_subset _).mpr
  rw [LinearStudy.orderedCechFullIndex_range]
  exact Set.subset_univ _

/-- For actual top cochains, multiplication by X^b extracts the source
coefficient complementary to b+c. The map is the previously constructed
Laurent multiplication, followed only by integer-degree equality transport. -/
theorem coordinateGeneralResidue_monomial_shift (l m n : ℕ)
    (hc : Fintype.card σ = n+1) (b : ProjectiveMonomialIndex σ l)
    (s : coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ)
      (-((l+m:ℕ):ℤ)-Fintype.card σ) n) (e : ProjectiveNegativeWeight σ m) :
    coordinateGeneralResidue (R := R) m n hc
      (coordinateComplementaryMonomialCechShift l m b n s) e =
    coordinateGeneralResidue (R := R) (l+m) n hc s
      (projectiveMonomialNegativeWeight (l+m)
        (projectiveMonomialIndexAdd l m b (projectiveNegativeWeightEquivMonomial m e))) := by
  let a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n :=
    LinearStudy.orderedCechFullIndex n (by simpa using hc)
  let c := projectiveNegativeWeightEquivMonomial m e
  let es := (projectiveMonomialNegativeWeight (l+m) (projectiveMonomialIndexAdd l m b c)).1
  have hs : es.IsAllowedOn (fun j => (a.1 j).down) :=
    homogeneousLaurentWeight_allowed_full es n hc
  have he : projectiveMonomialNegativeWeight m c = e :=
    (projectiveNegativeWeightEquivMonomial m).symm_apply_apply e
  have ht := projectiveComplementaryShiftWeight l m b c (fun j => (a.1 j).down) hs
  rw [he] at ht
  change (coordinateHomogeneousLaurentWeightComponent (R := R) _ e.1 n
      (coordinateLaurentCechDegreeCast (R := R) (projectiveComplementaryShiftDegree (σ := σ) l m) n
        ((coordinateLaurentCechShift (R := R) (d := -((l+m:ℕ):ℤ)-Fintype.card σ)
          (projectiveMonomialPositiveWeight l b)
          (projectiveMonomialPositiveWeight_nonnegative l b) n).hom s))).1 a =
    (coordinateHomogeneousLaurentWeightComponent (R := R) _ es n s).1 a
  rw [← ht, coordinateLaurentCechDegreeCast_weightComponent]
  exact coordinateLaurentCechShift_weightComponent a (projectiveMonomialPositiveWeight l b)
    (projectiveMonomialPositiveWeight_nonnegative l b) ⟨es,hs⟩ s

end MvPolynomial
