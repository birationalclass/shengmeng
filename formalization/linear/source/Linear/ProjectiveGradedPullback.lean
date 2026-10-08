module
public import Linear.HomogeneousCoordinatePieces
public import Linear.ProjectiveConeFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The ORIGINAL coordinate-domain pullback carries its actual degree-m
piece into the actual degree-q*m piece. -/
theorem projectiveCoordinateDomainMap_piece_mem
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (m : ℕ) (a : CoordinateRing n ⧸ V.ideal.toIdeal)
    (ha : a ∈ homogeneousQuotientPiece V.ideal.toIdeal m) :
    projectiveCoordinateDomainMap f V hq hf hV a ∈
      homogeneousQuotientPiece V.ideal.toIdeal (f.degree * m) := by
  obtain ⟨H, hH, rfl⟩ := (homogeneousQuotientPiece_mem_iff V.ideal.toIdeal m a).mp ha
  apply (homogeneousQuotientPiece_mem_iff V.ideal.toIdeal (f.degree*m) _).mpr
  exact ⟨MvPolynomial.aeval f.forms H, hH.aeval f.forms f.homogeneous,
    (projectiveCoordinateDomainMap_mk f V hq hf hV H).symm⟩

/-- The actual finite-piece linear map; no Hilbert polynomial is input. -/
def projectiveCoordinatePiecePullback
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (m : ℕ) :
    homogeneousQuotientPiece V.ideal.toIdeal m →ₗ[ℂ]
      homogeneousQuotientPiece V.ideal.toIdeal (f.degree * m) :=
  ((projectiveCoordinateDomainMap f V hq hf hV).toLinearMap.domRestrict
    (homogeneousQuotientPiece V.ideal.toIdeal m)).codRestrict
      (homogeneousQuotientPiece V.ideal.toIdeal (f.degree * m))
      (fun a => projectiveCoordinateDomainMap_piece_mem f V hq hf hV m a a.property)

theorem projectiveCoordinatePiecePullback_injective
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (m : ℕ) :
    Function.Injective (projectiveCoordinatePiecePullback f V hq hf hV m) := by
  intro a b hab
  apply Subtype.ext
  apply projectiveCoordinateDomainMap_injective f V hq hf hV
  exact congrArg Subtype.val hab

theorem projectiveCoordinateDomainMap_component
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (m : ℕ) (a : CoordinateRing n ⧸ V.ideal.toIdeal) :
    homogeneousQuotientComponent V.ideal.toIdeal V.ideal.isHomogeneous (f.degree * m)
      (projectiveCoordinateDomainMap f V hq hf hV a) =
    projectiveCoordinateDomainMap f V hq hf hV
      (homogeneousQuotientComponent V.ideal.toIdeal V.ideal.isHomogeneous m a) := by
  obtain ⟨H, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [projectiveCoordinateDomainMap_mk, homogeneousQuotientComponent_mk,
    homogeneousComponent_aeval_common_positive_degree f.forms f.degree hq f.homogeneous]

/-- A first dimension comparison for the ORIGINAL graded coordinate ring.
This is not the unproved function-field degree formula q^dim(V). -/
theorem projectiveCoordinateHilbert_pullback_le
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (m : ℕ) :
    homogeneousQuotientHilbert V.ideal.toIdeal m ≤
      homogeneousQuotientHilbert V.ideal.toIdeal (f.degree * m) := by
  letI := homogeneousQuotientPiece_finite V.ideal.toIdeal (f.degree * m)
  exact LinearMap.finrank_le_finrank_of_injective
    (projectiveCoordinatePiecePullback_injective f V hq hf hV m)

end LinearStudy
