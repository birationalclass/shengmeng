module
public import Linear.SmoothFormalCoordinates
public import Linear.CompleteIntersectionChange
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
variable {K : Type*} [Field K] (r c : ℕ) [Nonempty (Fin c)]

def normalVariableQuotientEquiv :
    (MvPowerSeries (Fin r ⊕ Fin c) K ⧸
      Ideal.span (Set.range (fun j : Fin c => MvPowerSeries.X (R := K) (Sum.inr j)))) ≃+*
        MvPowerSeries (Fin r) K := by
  let E := powerSeriesCoordinateChart K r c
  let I : Ideal (MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K)) :=
    Ideal.span (Set.range MvPowerSeries.X)
  let J : Ideal (MvPowerSeries (Fin r ⊕ Fin c) K) :=
    Ideal.span (Set.range (fun j : Fin c => MvPowerSeries.X (Sum.inr j)))
  have hmap : J = I.map E.toRingHom := by
    rw [Ideal.map_span, ← Set.range_comp]
    have hf : (E.toRingHom ∘ MvPowerSeries.X) =
        (fun j : Fin c => MvPowerSeries.X (R := K) (Sum.inr j)) := by
      funext j
      exact powerSeriesCoordinateChart_X K r c j
    rw [hf]
  let Q := Ideal.quotientEquiv I J E hmap
  let cc : MvPowerSeries (Fin c) (MvPowerSeries (Fin r) K) →+* MvPowerSeries (Fin r) K :=
    MvPowerSeries.constantCoeff
  have hker : I = RingHom.ker cc := powerSeries_constantCoeff_kernel.symm
  exact Q.symm.trans ((Ideal.quotEquivOfEq hker).trans
    (cc.quotientKerEquivOfSurjective (fun f => ⟨MvPowerSeries.C f, by simp [cc]⟩)))

theorem normalVariableQuotientEquiv_mk
    (f : MvPowerSeries (Fin r ⊕ Fin c) K) :
    normalVariableQuotientEquiv r c (Ideal.Quotient.mk _ f) =
      (powerSeriesCoordinateChart K r c |>.symm f).constantCoeff := by
  unfold normalVariableQuotientEquiv
  simp [Ideal.quotientEquiv, RingHom.quotientKerEquivOfSurjective_apply_mk]

def smoothFormalQuotientEquiv
    (G : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hG : ∀ j, (G j).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff))) :
    (MvPowerSeries (Fin r ⊕ Fin c) K ⧸ Ideal.span (Set.range G)) ≃+*
      MvPowerSeries (Fin r) K := by
  let E := smoothFormalCoordinateEquiv G hG hJ
  let I : Ideal (MvPowerSeries (Fin r ⊕ Fin c) K) := Ideal.span (Set.range G)
  let J : Ideal (MvPowerSeries (Fin r ⊕ Fin c) K) :=
    Ideal.span (Set.range (fun j : Fin c => MvPowerSeries.X (Sum.inr j)))
  have hmap : J = I.map E.symm.toRingEquiv.toRingHom := by
    rw [Ideal.map_span, ← Set.range_comp]
    have hf : (E.symm ∘ G) = fun j => MvPowerSeries.X (Sum.inr j) := by
      funext j
      rw [Function.comp_apply, ← smoothFormalCoordinateEquiv_normal G hG hJ j]
      exact E.symm_apply_apply _
    change J = Ideal.span (Set.range (E.symm ∘ G))
    rw [hf]
  exact (Ideal.quotientEquiv I J E.symm.toRingEquiv hmap).trans
    (normalVariableQuotientEquiv r c)

theorem smoothFormalQuotientEquiv_mk
    (G : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hG : ∀ j, (G j).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff)))
    (f : MvPowerSeries (Fin r ⊕ Fin c) K) :
    smoothFormalQuotientEquiv r c G hG hJ (Ideal.Quotient.mk _ f) =
      (powerSeriesCoordinateChart K r c |>.symm
        ((smoothFormalCoordinateEquiv G hG hJ).symm f)).constantCoeff := by
  unfold smoothFormalQuotientEquiv
  rw [RingEquiv.trans_apply, Ideal.quotientEquiv_mk, normalVariableQuotientEquiv_mk]
  rfl

theorem smoothFormalQuotientEquiv_parameter_series
    (G : Fin c → MvPowerSeries (Fin r ⊕ Fin c) K)
    (hG : ∀ j, (G j).constantCoeff = 0)
    (hJ : IsUnit (Matrix.det (fun i j =>
      (MvPowerSeries.pderiv (Sum.inr j) (G i)).constantCoeff)))
    (b : MvPowerSeries (Fin r) K) :
    smoothFormalQuotientEquiv r c G hG hJ
      (Ideal.Quotient.mk _ (MvPowerSeries.rename Sum.inl b)) = b := by
  rw [smoothFormalQuotientEquiv_mk]
  have hh : (smoothFormalCoordinateEquiv G hG hJ).symm (MvPowerSeries.rename Sum.inl b) =
      MvPowerSeries.rename Sum.inl b := by
    apply (smoothFormalCoordinateEquiv G hG hJ).injective
    rw [AlgEquiv.apply_symm_apply, smoothFormalCoordinateEquiv_parameter_series]
  rw [hh, ← powerSeriesCoordinateChart_C K r c b, RingEquiv.symm_apply_apply]
  simp

end LinearStudy
