module
public import Linear.HomogeneousNoBasePointFinite
public import Linear.HomogeneousRationalPullback
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
namespace LinearStudy
/-- A finite ACTUAL cone map descends to the ACTUAL original affine
source chart when its first coordinate becomes1 on that chart. No
weighted chart or generic-open finiteness certificate is substituted. -/
theorem homogeneous_cone_finite_implies_actual_affine_map_finite
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (P : Fin (r+1) → MvPolynomial (Fin (n+1)) K)
    (hfin : (((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval P) :
      MvPolynomial (Fin (r+1)) K →ₐ[K] MvPolynomial (Fin (n+1)) K ⧸ I).toRingHom).Finite)
    (hfirst : affineChartPolynomialMap (K:=K) (P 0)=1) :
    (((Ideal.Quotient.mkₐ K (I.map (affineChartPolynomialMap (K:=K)).toRingHom)).comp
      (MvPolynomial.aeval (fun i : Fin r => affineChartPolynomialMap (K:=K) (P i.succ))) :
      MvPolynomial (Fin r) K →ₐ[K]
        MvPolynomial (Fin n) K ⧸ I.map (affineChartPolynomialMap (K:=K)).toRingHom).toRingHom).Finite := by
  let delta := affineChartPolynomialMap (K:=K) (n:=n)
  let J := I.map delta.toRingHom
  let cone := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval P)
  let affine := (Ideal.Quotient.mkₐ K J).comp
    (MvPolynomial.aeval (fun i : Fin r => delta (P i.succ)))
  let deltaBar := Ideal.quotientMapₐ J delta Ideal.le_comap_map
  have hdelta : Function.Surjective delta := by
    intro a
    refine ⟨MvPolynomial.rename Fin.succ a,?_⟩
    have hh : delta.comp (MvPolynomial.rename Fin.succ)=AlgHom.id K (MvPolynomial (Fin n) K) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [delta,affineChartPolynomialMap,AlgHom.comp_apply]
    exact AlgHom.congr_fun hh a
  have hbar : Function.Surjective deltaBar :=
    Ideal.quotientMap_surjective (H:=Ideal.le_comap_map) hdelta
  have hh : deltaBar.comp cone=affine.comp (affineChartPolynomialMap (K:=K) (n:=r)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,cone,MvPolynomial.aeval_X]
    cases i using Fin.cases with
    | zero =>
      change Ideal.Quotient.mk J (delta (P 0))=
        affine (affineChartPolynomialMap (K:=K) (MvPolynomial.X 0))
      rw [show delta (P 0)=1 from hfirst]
      simp [affineChartPolynomialMap]
    | succ i =>
      change Ideal.Quotient.mk J (delta (P i.succ))=
        affine (affineChartPolynomialMap (K:=K) (MvPolynomial.X i.succ))
      simp [affine,affineChartPolynomialMap,AlgHom.comp_apply]
  have ht : (deltaBar.comp cone).Finite :=
    (AlgHom.Finite.of_surjective deltaBar hbar).comp hfin
  rw [hh] at ht
  exact AlgHom.Finite.of_comp_finite ht
end LinearStudy
