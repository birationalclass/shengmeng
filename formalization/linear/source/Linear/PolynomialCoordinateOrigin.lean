module
public import Linear.PolynomialCoordinatePoints
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

/-- Actual coordinate equivalences fixing the origin preserve the origin-only
zero locus of an ideal. Neither point surjectivity nor radical equality is input. -/
theorem polynomial_coordinate_origin_zeroLocus
    {K σ τ : Type*} [Field K]
    (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (h0 : ∀ j, MvPolynomial.eval (0 : σ → K) (E.symm (MvPolynomial.X j)) = 0)
    (I : Ideal (MvPolynomial σ K))
    (hz : MvPolynomial.zeroLocus K I = {0}) :
    MvPolynomial.zeroLocus K (I.map E.toRingHom) = {0} := by
  classical
  ext v
  constructor
  · intro hv
    let x := fun i => MvPolynomial.eval v (E (MvPolynomial.X i))
    have hcomp := polynomial_coordinate_point_evaluation E.symm v
    have he (F : MvPolynomial σ K) : MvPolynomial.eval x F = MvPolynomial.eval v (E F) := by
      have h := AlgHom.congr_fun hcomp (E F)
      change MvPolynomial.eval x (E.symm (E F)) = MvPolynomial.eval v (E F) at h
      rw [E.symm_apply_apply] at h
      exact h
    have hx : x ∈ MvPolynomial.zeroLocus K I := by
      intro F hF
      change MvPolynomial.eval x F = 0
      rw [he]
      exact hv (E F) (Ideal.mem_map_of_mem E.toRingHom hF)
    have hx0 : x = 0 := by simpa only [hz,Set.mem_singleton_iff] using hx
    apply Set.mem_singleton_iff.mpr
    funext j
    have h := AlgHom.congr_fun hcomp (MvPolynomial.X j)
    change MvPolynomial.eval x (E.symm (MvPolynomial.X j)) = MvPolynomial.eval v (MvPolynomial.X j) at h
    rw [hx0,h0,MvPolynomial.eval_X] at h
    exact h.symm
  · intro hv
    have hv0 := Set.mem_singleton_iff.mp hv
    subst v
    have hx : (0 : σ → K) ∈ MvPolynomial.zeroLocus K I := by rw [hz]; exact Set.mem_singleton 0
    intro F hF
    obtain ⟨G,hG,rfl⟩ := (Ideal.mem_map_iff_of_surjective E.toRingHom E.surjective).mp hF
    have hcomp := polynomial_coordinate_point_evaluation E (0 : σ → K)
    have h := AlgHom.congr_fun hcomp G
    have hpoint : (fun j => MvPolynomial.eval (0 : σ → K) (E.symm (MvPolynomial.X j))) = 0 :=
      funext h0
    change MvPolynomial.eval (fun j => MvPolynomial.eval (0 : σ → K)
      (E.symm (MvPolynomial.X j))) (E G) = MvPolynomial.eval (0 : σ → K) G at h
    rw [hpoint] at h
    exact h.trans (hx G hG)

end LinearStudy
