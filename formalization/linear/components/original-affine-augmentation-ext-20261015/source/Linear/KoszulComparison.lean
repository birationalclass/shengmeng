module

public import Linear.KoszulTop
public import Linear.KoszulResolution

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open CategoryTheory
namespace LinearStudy
variable {R : Type*} [CommRing R] {n : ℕ}

theorem coefficientMatrix_koszul_compatibility (H x : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (h : M.mulVec x = H) :
    (Fintype.linearCombination R x).comp (Matrix.toLin' M.transpose) =
      Fintype.linearCombination R H := by
  classical
  apply (Pi.basisFun R (Fin n)).ext
  intro i
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply, Pi.basisFun_apply]
  change (Fintype.linearCombination R x) (M.transpose.mulVec (Pi.single i 1)) = _
  rw [Matrix.mulVec_single]
  rw [Fintype.linearCombination_apply_single]
  simp only [Fintype.linearCombination_apply,
    smul_eq_mul]
  simpa [Matrix.mulVec, dotProduct] using congrFun h i

def coefficientKoszulComparison (H x : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (h : M.mulVec x = H) :
    koszulComplex (Fintype.linearCombination R H) ⟶
      koszulComplex (Fintype.linearCombination R x) :=
  koszulComplex.map _ (Matrix.toLin' M.transpose) _
    (coefficientMatrix_koszul_compatibility H x M h)

theorem coefficientKoszulComparison_top (H x : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (h : M.mulVec x = H)
    (v : ⋀[R]^n (Fin n → R)) :
    ((coefficientKoszulComparison H x M h).f n).hom v = M.det • v := by
  change exteriorPower.map n (Matrix.toLin' M.transpose) v = M.det • v
  rw [topKoszul_map, LinearMap.det_toLin', Matrix.det_transpose]

end LinearStudy
