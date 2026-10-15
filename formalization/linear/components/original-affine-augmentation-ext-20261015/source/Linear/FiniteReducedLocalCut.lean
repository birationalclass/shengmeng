module
public import Linear.LocalFiber
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy

/-- In a finite reduced cut, localizing the original defining ideal at
an actual prime of the cut gives the ambient maximal ideal. The original
ideal is preserved, and neither a radical replacement nor an assumed
pointwise multiplicity is used. -/
theorem artinian_reduced_cut_local_ideal_eq_maximalIdeal
    {R : Type*} [CommRing R] (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] [IsReduced (R ⧸ I)]
    (p : Ideal (R ⧸ I)) [p.IsPrime] :
    I.map (algebraMap R (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (p.comap (Ideal.Quotient.mk I))) := by
  let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
  let J := I.map (algebraMap R A)
  let e := localizationQuotientEquiv I p
  letI : IsReduced (A ⧸ J) := isReduced_of_injective e.toRingHom e.injective
  letI : IsArtinianRing (A ⧸ J) := e.symm.toRingEquiv.isArtinianRing
  letI : IsLocalRing (A ⧸ J) := e.symm.toRingEquiv.isLocalRing
  apply IsLocalRing.eq_maximalIdeal
  apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing (A ⧸ J)

theorem artinian_reduced_cut_local_ideal_eq_maximalIdeal_of_le
    {R : Type*} [CommRing R] (I P : Ideal R) [P.IsPrime]
    [IsArtinianRing (R ⧸ I)] [IsReduced (R ⧸ I)] (hIP : I ≤ P) :
    I.map (algebraMap R (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  let p := P.map (Ideal.Quotient.mk I)
  letI : p.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hIP)
  have hcomap : p.comap (Ideal.Quotient.mk I)=P := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot,Ideal.mk_ker]
    exact sup_eq_left.mpr hIP
  have h := artinian_reduced_cut_local_ideal_eq_maximalIdeal I p
  let Q : PrimeSpectrum R := ⟨P,inferInstance⟩
  let Q' : PrimeSpectrum R := ⟨p.comap (Ideal.Quotient.mk I),inferInstance⟩
  have he : Q'=Q := PrimeSpectrum.ext hcomap
  let E : PrimeSpectrum R → Prop := fun z =>
    I.map (algebraMap R (Localization.AtPrime z.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime z.asIdeal)
  have hE : E Q' := h
  have hQ : E Q := Eq.mp (congrArg E he) hE
  exact hQ

end LinearStudy
