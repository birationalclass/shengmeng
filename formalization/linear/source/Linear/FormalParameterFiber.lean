module
public import Linear.ThickeningFromRadical
public import Linear.CompletionQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace LinearStudy

def equationParameterQuotientEquiv {R ι : Type*} [CommRing R]
    (I : Ideal R) (τ : ι → R) :
    ((R ⧸ I) ⧸ Ideal.span (Set.range (fun i => Ideal.Quotient.mk I (τ i)))) ≃+*
      (R ⧸ I ⊔ Ideal.span (Set.range τ)) := by
  have h : Ideal.span (Set.range (fun i => Ideal.Quotient.mk I (τ i))) =
      (Ideal.span (Set.range τ)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  exact (Ideal.quotEquivOfEq h).trans (DoubleQuot.quotQuotEquivQuotSup _ _)

theorem equationParameterQuotientEquiv_mk {R ι : Type*} [CommRing R]
    (I : Ideal R) (τ : ι → R) (a : R) :
    equationParameterQuotientEquiv I τ
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I ⊔ Ideal.span (Set.range τ)) a := by
  dsimp only [equationParameterQuotientEquiv]
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

def parameterFiberSocle {R ι : Type*} [CommRing R]
    (I : Ideal R) (τ : ι → R) (δ : R) : Prop :=
  IsArtinianRing (R ⧸ I ⊔ Ideal.span (Set.range τ)) ∧
    (nilradical (R ⧸ I ⊔ Ideal.span (Set.range τ))).annihilator =
      Ideal.span {Ideal.Quotient.mk (I ⊔ Ideal.span (Set.range τ)) δ} ∧
    Ideal.Quotient.mk (I ⊔ Ideal.span (Set.range τ)) δ ≠ 0

theorem parameterFiberSocle_of_doubleQuotient {R ι : Type*} [CommRing R]
    (I : Ideal R) (τ : ι → R) (δ : R)
    (hArt : IsArtinianRing ((R ⧸ I) ⧸
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk I (τ i)))))
    (hgen : (nilradical ((R ⧸ I) ⧸
      Ideal.span (Set.range (fun i => Ideal.Quotient.mk I (τ i))))).annihilator =
        Ideal.span {Ideal.Quotient.mk _ (Ideal.Quotient.mk I δ)})
    (hne : Ideal.Quotient.mk (Ideal.span (Set.range (fun i => Ideal.Quotient.mk I (τ i))))
      (Ideal.Quotient.mk I δ) ≠ 0) : parameterFiberSocle I τ δ := by
  let : IsArtinianRing ((R ⧸ I) ⧸ Ideal.span (Set.range (fun i => Ideal.Quotient.mk I (τ i)))) := hArt
  let E := equationParameterQuotientEquiv I τ
  have hg := ringEquiv_nilradical_annihilator_generator E _ hgen
  rw [equationParameterQuotientEquiv_mk] at hg
  refine ⟨E.isArtinianRing, hg, ?_⟩
  rw [← equationParameterQuotientEquiv_mk I τ δ]
  intro hz
  exact hne (E.injective (hz.trans E.map_zero.symm))

theorem formal_parameter_fiber_jacobian_socle
    {r c : ℕ} (H : Fin c → AmbientRing r c) (hr : 0 < r) (hc : 0 < c)
    (hrad : (equationIdeal H).radical =
      Ideal.span (Set.range (MvPowerSeries.X (σ := Fin c) (R := ParameterRing r))))
    (τ : Fin r → AmbientRing r c)
    (hτ : Ideal.span (Set.range (fun i => (τ i).constantCoeff)) =
      IsLocalRing.maximalIdeal (ParameterRing r)) :
    parameterFiberSocle (equationIdeal H) τ
      (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) := by
  let q := coordinateThickeningReductionFromRadical H hc hrad
  let t := fun i => Ideal.Quotient.mk (equationIdeal H) (τ i)
  let J := Ideal.span (Set.range t)
  have ht : Ideal.span (Set.range (fun i => q (t i))) =
      IsLocalRing.maximalIdeal (ParameterRing r) := hτ
  obtain ⟨hArt, hMax, hgen, hne⟩ :=
    (formalThickening_relativeJacobian_socle H hr hc hrad).2 t ht
  let : IsArtinianRing (CompleteIntersection H ⧸ J) := hArt
  have hJ : J.map q.toRingHom = IsLocalRing.maximalIdeal (ParameterRing r) := by
    rw [Ideal.map_span, ← Set.range_comp]
    exact ht
  have hnil := parameterQuotient_nilradical_eq q
    (coordinateThickeningReductionFromRadical_kernel H hc hrad) J hJ
  rw [← hnil] at hgen
  exact parameterFiberSocle_of_doubleQuotient (equationIdeal H) τ _ hArt hgen hne

end LinearStudy
