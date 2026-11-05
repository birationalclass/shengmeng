module
public import Linear.ProjectiveHomogeneousMultiplication
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace MvPolynomial
variable {R : Type} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

/-- The basis used by the actual residue-duality interface consists of
the original polynomial monomials with coefficient1. -/
theorem projectiveHomogeneousMonomialBasis_coe (m : ℕ) (a : ProjectiveMonomialIndex σ m) :
    (projectiveHomogeneousMonomialBasis (R := R) m a).1 = monomial a.1 1 := by
  change ((basisRestrictSupport R {a : σ →₀ ℕ | a.degree=m}) a).1 = _
  change ((AddMonoidAlgebra.supportedEquivFinsupp {a : σ →₀ ℕ | a.degree=m}).symm
    (Finsupp.single a 1)).1 = _
  simp [AddMonoidAlgebra.supportedEquivFinsupp]
  rfl

def projectiveMonomialIndexAdd (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) (c : ProjectiveMonomialIndex σ m) :
    ProjectiveMonomialIndex σ (l+m) := ⟨b.1+c.1, by rw [map_add,b.property,c.property]⟩

/-- The actual homogeneous polynomial multiplication map multiplies its
monomial basis vectors by adding the original natural exponents. -/
theorem projectiveHomogeneousMultiply_basis (l m : ℕ)
    (b : ProjectiveMonomialIndex σ l) (c : ProjectiveMonomialIndex σ m) :
    projectiveHomogeneousMultiply l m (projectiveHomogeneousMonomialBasis (R := R) l b)
      (projectiveHomogeneousMonomialBasis (R := R) m c) =
    projectiveHomogeneousMonomialBasis (R := R) (l+m) (projectiveMonomialIndexAdd l m b c) := by
  apply Subtype.ext
  rw [projectiveHomogeneousMultiply_coe, projectiveHomogeneousMonomialBasis_coe,
    projectiveHomogeneousMonomialBasis_coe, projectiveHomogeneousMonomialBasis_coe]
  simp [projectiveMonomialIndexAdd]
end MvPolynomial
