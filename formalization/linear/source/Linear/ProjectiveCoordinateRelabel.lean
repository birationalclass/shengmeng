module
public import Linear.ProjectiveIdealInvariance
public import Mathlib.Algebra.MvPolynomial.Rename
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomial_relabel_pullback {K σ τ : Type*} [CommSemiring K]
    (e : σ ≃ τ) (F : σ → MvPolynomial σ K) :
    (MvPolynomial.renameEquiv K e).toAlgHom.comp (MvPolynomial.aeval F) =
      (MvPolynomial.aeval (fun j => MvPolynomial.renameEquiv K e (F (e.symm j)))).comp
        (MvPolynomial.renameEquiv K e).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [MvPolynomial.renameEquiv_apply]

theorem projective_total_invariance_relabel_radical {n : ℕ} {σ : Type*}
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hf : f.degree ≠ 0) (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet)
    (e : Fin (n + 1) ≃ σ) :
    let E := MvPolynomial.renameEquiv ℂ e
    let I := V.ideal.toIdeal.map E.toRingHom
    let F := fun j => E (f.forms (e.symm j))
    (I.map (MvPolynomial.aeval F).toRingHom).radical = I := by
  let E := MvPolynomial.renameEquiv ℂ e
  let F := fun j => E (f.forms (e.symm j))
  have hcomm := congrArg AlgHom.toRingHom (polynomial_relabel_pullback e f.forms)
  have hmap : (V.ideal.toIdeal.map E.toRingHom).map (MvPolynomial.aeval F).toRingHom =
      (V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom).map E.toRingHom := by
    rw [Ideal.map_map, Ideal.map_map]
    exact congrArg (fun φ => V.ideal.toIdeal.map φ) hcomm.symm
  change ((V.ideal.toIdeal.map E.toRingHom).map (MvPolynomial.aeval F).toRingHom).radical = _
  have hradmap := Ideal.map_radical_of_surjective (f := E.toRingHom)
    (I := V.ideal.toIdeal.map (MvPolynomial.aeval f.forms).toRingHom)
    E.surjective (by
      intro p hp
      change E p = 0 at hp
      have hz : p = 0 := E.injective (hp.trans (map_zero E).symm)
      rw [hz]
      exact Ideal.zero_mem _)
  rw [hmap, ← hradmap, projective_total_invariance_pullback_radical f V hf hV]

end LinearStudy
