module

public import Linear.Vendor.KoszulComplex
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section
noncomputable section
open scoped BigOperators
namespace LinearStudy
variable {R : Type*} [CommRing R] (n : ℕ)

def topKoszulGenerator : ⋀[R]^n (Fin n → R) :=
  exteriorPower.ιMulti R n (Pi.basisFun R (Fin n))

theorem topExterior_alternating_map :
    exteriorPower.ιMulti R n =
      (Pi.basisFun R (Fin n)).det.smulRight (topKoszulGenerator n) := by
  classical
  apply (Pi.basisFun R (Fin n)).ext_alternating
  intro v hv
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective v (Finite.injective_iff_bijective.mp hv)
  change exteriorPower.ιMulti R n ((Pi.basisFun R (Fin n)) ∘ σ) = _
  rw [AlternatingMap.map_perm]
  change Equiv.Perm.sign σ • topKoszulGenerator (R := R) n =
    (Pi.basisFun R (Fin n)).det ((Pi.basisFun R (Fin n)) ∘ σ) • topKoszulGenerator (R := R) n
  rw [AlternatingMap.map_perm, Module.Basis.det_self]
  simp

def topKoszulCoordinate : (⋀[R]^n (Fin n → R)) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv (Pi.basisFun R (Fin n)).det

theorem topKoszulCoordinate_generator :
    topKoszulCoordinate n (topKoszulGenerator (R := R) n) = 1 := by
  change exteriorPower.alternatingMapLinearEquiv (Pi.basisFun R (Fin n)).det
    (exteriorPower.ιMulti R n (Pi.basisFun R (Fin n))) = 1
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self]

theorem topKoszulCoordinate_reconstruct (x : ⋀[R]^n (Fin n → R)) :
    topKoszulCoordinate n x • topKoszulGenerator n = x := by
  have he : (LinearMap.id.smulRight (topKoszulGenerator (R := R) n)).comp
      (topKoszulCoordinate n) = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simpa [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      topKoszulCoordinate] using
      (DFunLike.congr_fun (topExterior_alternating_map (R := R) n) v).symm
  exact LinearMap.congr_fun he x

def topKoszulEquiv : (⋀[R]^n (Fin n → R)) ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (topKoszulCoordinate n)
    (LinearMap.id.smulRight (topKoszulGenerator n))
    (by apply LinearMap.ext; intro r; simp [topKoszulCoordinate_generator])
    (by apply LinearMap.ext; intro x; exact topKoszulCoordinate_reconstruct n x)

theorem topKoszulCoordinate_map_generator (f : (Fin n → R) →ₗ[R] (Fin n → R)) :
    topKoszulCoordinate n (exteriorPower.map n f (topKoszulGenerator n)) = f.det := by
  classical
  rw [topKoszulGenerator, exteriorPower.map_apply_ιMulti]
  rw [topKoszulCoordinate, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change (Pi.basisFun R (Fin n)).det (f ∘ (Pi.basisFun R (Fin n))) = f.det
  rw [Module.Basis.det_apply]
  have hm : (Pi.basisFun R (Fin n)).toMatrix (f ∘ (Pi.basisFun R (Fin n))) =
      LinearMap.toMatrix (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n)) f := by
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [hm]
  exact LinearMap.det_toMatrix _ _

theorem topKoszul_map (f : (Fin n → R) →ₗ[R] (Fin n → R))
    (x : ⋀[R]^n (Fin n → R)) : exteriorPower.map n f x = f.det • x := by
  rw [← topKoszulCoordinate_reconstruct n x, map_smul]
  have hg : exteriorPower.map n f (topKoszulGenerator n) =
      f.det • topKoszulGenerator n := by
    rw [← topKoszulCoordinate_map_generator n f]
    exact (topKoszulCoordinate_reconstruct n _).symm
  rw [hg, smul_smul, mul_comm, ← smul_smul]

end LinearStudy
