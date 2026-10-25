module
public import Linear.LocalPullbackGenerators
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace LinearStudy
variable {K : Type*} [Field K] {r c : ℕ} [Nonempty (Fin c)]

def polynomialSmoothReducedMap (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    MvPolynomial (Fin r ⊕ Fin c) K →+* MvPowerSeries (Fin r) K :=
  MvPowerSeries.constantCoeff.comp (polynomialSmoothFormalMap x G hG hJ)

theorem polynomialSmoothReducedMap_isUnit_iff (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (P : MvPolynomial (Fin r ⊕ Fin c) K) :
    IsUnit (polynomialSmoothReducedMap x G hG hJ P) ↔ MvPolynomial.eval x P ≠ 0 := by
  change IsUnit ((polynomialSmoothFormalMap x G hG hJ P).constantCoeff) ↔ _
  rw [← MvPowerSeries.isUnit_iff_constantCoeff (φ := polynomialSmoothFormalMap x G hG hJ P)]
  exact polynomialSmoothFormalMap_isUnit_iff x G hG hJ P

theorem polynomialSmoothReducedMap_parameter (x : Fin r ⊕ Fin c → K)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (i : Fin r) :
    polynomialSmoothReducedMap x G hG hJ
      (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (x (Sum.inl i))) = MvPowerSeries.X i := by
  change (polynomialSmoothFormalMap x G hG hJ _).constantCoeff = _
  rw [polynomialSmoothFormalMap_parameter, MvPowerSeries.constantCoeff_C]

theorem polynomialSmoothReducedMap_pointIdeal (P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K))
    [Nonempty (Fin r)]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    P.map (polynomialSmoothReducedMap x G hG hJ) = IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change ¬ IsUnit (polynomialSmoothReducedMap x G hG hJ p)
    rw [polynomialSmoothReducedMap_isUnit_iff]
    rw [hP, RingHom.mem_ker] at hp
    change MvPolynomial.eval x p = 0 at hp
    intro hn
    exact hn hp
  · rw [← powerSeries_coordinateIdeal_eq_maximalIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← polynomialSmoothReducedMap_parameter x G hG hJ i]
    apply Ideal.mem_map_of_mem
    rw [hP, RingHom.mem_ker]
    simp

def polynomialSmoothPointLocalReduction (P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    Localization.AtPrime P →+* MvPowerSeries (Fin r) K :=
  IsLocalization.lift (S := Localization.AtPrime P) (g := polynomialSmoothReducedMap x G hG hJ)
    (fun s : P.primeCompl => (polynomialSmoothReducedMap_isUnit_iff x G hG hJ s).mpr (by
    intro hz
    apply s.property
    exact (congrArg (fun J : Ideal (MvPolynomial (Fin r ⊕ Fin c) K) =>
      (s : MvPolynomial (Fin r ⊕ Fin c) K) ∈ J) hP).mpr hz))

theorem polynomialSmoothPointLocalReduction_polynomial
    (P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (p : MvPolynomial (Fin r ⊕ Fin c) K) :
    polynomialSmoothPointLocalReduction P x hP G hG hJ (algebraMap _ (Localization.AtPrime P) p) =
      polynomialSmoothReducedMap x G hG hJ p := by
  unfold polynomialSmoothPointLocalReduction
  exact IsLocalization.lift_eq _ p

theorem polynomialSmoothPointLocalReduction_maximalIdeal
    [Nonempty (Fin r)]
    (P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i))))) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (polynomialSmoothPointLocalReduction P x hP G hG hJ) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin r) K) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
  have hcomp : (polynomialSmoothPointLocalReduction P x hP G hG hJ).comp
      (algebraMap _ (Localization.AtPrime P)) = polynomialSmoothReducedMap x G hG hJ := by
    apply RingHom.ext
    intro p
    exact polynomialSmoothPointLocalReduction_polynomial P x hP G hG hJ p
  rw [hcomp]
  exact polynomialSmoothReducedMap_pointIdeal P x hP G hG hJ

theorem polynomialSmoothPointLocalReduction_ideal_kernel
    (I P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    I.map (algebraMap _ (Localization.AtPrime P)) ≤
      RingHom.ker (polynomialSmoothPointLocalReduction P x hP G hG hJ) := by
  rw [hlocal]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change polynomialSmoothPointLocalReduction P x hP G hG hJ
    (algebraMap _ (Localization.AtPrime P) (G i)) = 0
  rw [polynomialSmoothPointLocalReduction_polynomial]
  change (polynomialSmoothFormalMap x G hG hJ (G i)).constantCoeff = 0
  rw [polynomialSmoothFormalMap_equation, MvPowerSeries.constantCoeff_X]

def polynomialSmoothLocalQuotientReduction
    (I P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) →+*
      MvPowerSeries (Fin r) K :=
  Ideal.Quotient.lift _ (polynomialSmoothPointLocalReduction P x hP G hG hJ)
    (polynomialSmoothPointLocalReduction_ideal_kernel I P x hP G hG hJ hlocal)

theorem polynomialSmoothLocalQuotientReduction_mk
    (I P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (a : Localization.AtPrime P) :
    polynomialSmoothLocalQuotientReduction I P x hP G hG hJ hlocal (Ideal.Quotient.mk _ a) =
      polynomialSmoothPointLocalReduction P x hP G hG hJ a := rfl

theorem polynomialSmoothLocalQuotient_isLocalRing
    (I P : Ideal (MvPolynomial (Fin r ⊕ Fin c) K)) [P.IsPrime]
    (x : Fin r ⊕ Fin c → K)
    (hP : P = RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    (G : Fin c → MvPolynomial (Fin r ⊕ Fin c) K)
    (hG : ∀ i, MvPolynomial.eval x (G i) = 0)
    (hJ : IsUnit (Matrix.det (fun i j => MvPolynomial.eval x (MvPolynomial.pderiv (Sum.inr j) (G i)))))
    (hlocal : I.map (algebraMap _ (Localization.AtPrime P)) =
      Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i)))) :
    IsLocalRing (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) := by
  let φ := polynomialSmoothLocalQuotientReduction I P x hP G hG hJ hlocal
  let : Nontrivial (Localization.AtPrime P ⧸ I.map (algebraMap _ (Localization.AtPrime P))) :=
    φ.domain_nontrivial
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem local_quotient_reduction_maximalIdeal {R S : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (J : Ideal R) [IsLocalRing (R ⧸ J)] (χ : R →+* S) (hker : J ≤ RingHom.ker χ)
    (hχ : (IsLocalRing.maximalIdeal R).map χ = IsLocalRing.maximalIdeal S) :
    (IsLocalRing.maximalIdeal (R ⧸ J)).map (Ideal.Quotient.lift J χ hker) =
      IsLocalRing.maximalIdeal S := by
  have hπ := IsLocalRing.map_maximalIdeal_of_surjective (R := R) (S := R ⧸ J)
    (Ideal.Quotient.mk J) (Ideal.Quotient.mk_surjective (I := J))
  rw [← hπ, Ideal.map_map]
  have hcomp : (Ideal.Quotient.lift J χ hker).comp (Ideal.Quotient.mk J) = χ := by
    apply RingHom.ext
    intro a
    rfl
  rw [hcomp]
  exact hχ

end LinearStudy
