module

public import Linear.PowerSeriesAugmentation
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
# Actual parameter specialization of power-series quotients

Specializing the parameter-ring coefficients to their constant terms is
surjective, with kernel exactly the extended parameter ideal. The actual
quotient by equations followed by the parameter ideal is ring-isomorphic
to the quotient by specialized equations. Formal partial derivatives and
Jacobian determinants are compatible with this explicit isomorphism.
Regularity of the specialized equations is a separate obligation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ}

def parameterSpecialization :
    MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) →+*
      MvPowerSeries (Fin c) K :=
  MvPowerSeries.map MvPowerSeries.constantCoeff

theorem parameterSpecialization_surjective :
    Function.Surjective (parameterSpecialization (K := K) (r := r) (c := c)) := by
  intro f
  refine ⟨MvPowerSeries.map (MvPowerSeries.C (σ := Fin (r + 1))) f, ?_⟩
  change MvPowerSeries.map MvPowerSeries.constantCoeff (MvPowerSeries.map MvPowerSeries.C f) = f
  rw [MvPowerSeries.map_map, MvPowerSeries.constantCoeff_comp_C, MvPowerSeries.map_id]
  rfl

theorem parameterSpecialization_kernel :
    RingHom.ker (parameterSpecialization (K := K) (r := r) (c := c)) =
      Ideal.span (Set.range (fun i : Fin (r + 1) =>
        MvPowerSeries.C (σ := Fin c) (MvPowerSeries.X (R := K) i))) := by
  have hf : (RingHom.ker
      (MvPowerSeries.constantCoeff (σ := Fin (r + 1)) (R := K))).FG := by
    rw [powerSeries_constantCoeff_kernel]
    exact Submodule.fg_span (Set.finite_range _)
  change RingHom.ker (MvPowerSeries.map MvPowerSeries.constantCoeff) = _
  rw [MvPowerSeries.ker_map_of_fg _ hf, powerSeries_constantCoeff_kernel,
    Ideal.map_span, ← Set.range_comp]
  rfl

def parameterSpecializationQuotientEquiv :
    (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸
      Ideal.span (Set.range (fun i : Fin (r + 1) =>
        MvPowerSeries.C (σ := Fin c) (MvPowerSeries.X (R := K) i)))) ≃+*
      MvPowerSeries (Fin c) K :=
  (Ideal.quotEquivOfEq parameterSpecialization_kernel.symm).trans
    (RingHom.quotientKerEquivOfSurjective parameterSpecialization_surjective)

section Quotient
variable {R S : Type*} [CommRing R] [CommRing S]

def quotientSpecialization (f : R →+* S) (I : Ideal R) :
    R ⧸ I →+* S ⧸ I.map f :=
  Ideal.quotientMap (I.map f) f Ideal.le_comap_map

theorem quotientSpecialization_kernel (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) :
    RingHom.ker (quotientSpecialization f I) =
      (RingHom.ker f).map (Ideal.Quotient.mk I) := by
  rw [quotientSpecialization, Ideal.quotientMap, Ideal.ker_quotient_lift,
    ← RingHom.comap_ker, Ideal.mk_ker,
    Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
    Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]

theorem quotientSpecialization_surjective (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) : Function.Surjective (quotientSpecialization f I) := by
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨Ideal.Quotient.mk I r, rfl⟩

def quotientSpecializationEquiv (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) :
    ((R ⧸ I) ⧸ (RingHom.ker f).map (Ideal.Quotient.mk I)) ≃+* S ⧸ I.map f :=
  (Ideal.quotEquivOfEq (quotientSpecialization_kernel f hf I).symm).trans
    (RingHom.quotientKerEquivOfSurjective (quotientSpecialization_surjective f hf I))

end Quotient

def powerSeriesClosedQuotientEquiv
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K)) :
    ((MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K) ⧸
      Ideal.span (Set.range H)) ⧸
      (Ideal.span (Set.range (fun i : Fin (r + 1) =>
        MvPowerSeries.C (σ := Fin c) (MvPowerSeries.X (R := K) i)))).map
        (Ideal.Quotient.mk (Ideal.span (Set.range H)))) ≃+*
      (MvPowerSeries (Fin c) K ⧸ Ideal.span
        (Set.range (fun i => parameterSpecialization (H i)))) := by
  let I := Ideal.span (Set.range H)
  let f := parameterSpecialization (K := K) (r := r) (c := c)
  have hp := congrArg (fun J => J.map (Ideal.Quotient.mk I))
    (parameterSpecialization_kernel (K := K) (r := r) (c := c))
  have hH : I.map f = Ideal.span (Set.range (fun i => f (H i))) := by
    dsimp [I]
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  exact (Ideal.quotEquivOfEq hp.symm).trans
    ((quotientSpecializationEquiv f parameterSpecialization_surjective I).trans
      (Ideal.quotEquivOfEq hH))

theorem powerSeriesClosedQuotientEquiv_mk
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K))
    (z : MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K)) :
    powerSeriesClosedQuotientEquiv H
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ z)) =
      Ideal.Quotient.mk _ (parameterSpecialization z) := by
  rfl

theorem powerSeries_map_pderiv {R S σ : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i : σ) (H : MvPowerSeries σ R) :
    MvPowerSeries.map f (MvPowerSeries.pderiv i H) =
      MvPowerSeries.pderiv i (MvPowerSeries.map f H) := by
  ext a
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv]

theorem parameterSpecialization_jacobian
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K)) :
    parameterSpecialization (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))) =
      Matrix.det (fun i j => MvPowerSeries.pderiv j (parameterSpecialization (H i))) := by
  rw [RingHom.map_det]
  congr 1
  funext i j
  exact powerSeries_map_pderiv
    (MvPowerSeries.constantCoeff (σ := Fin (r + 1)) (R := K)) j (H i)

theorem powerSeriesClosedQuotientEquiv_jacobian
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) K)) :
    powerSeriesClosedQuotientEquiv H
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk _
        (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i))))) =
      Ideal.Quotient.mk _
        (Matrix.det (fun i j => MvPowerSeries.pderiv j (parameterSpecialization (H i)))) := by
  rw [powerSeriesClosedQuotientEquiv_mk, parameterSpecialization_jacobian]

end LinearStudy
