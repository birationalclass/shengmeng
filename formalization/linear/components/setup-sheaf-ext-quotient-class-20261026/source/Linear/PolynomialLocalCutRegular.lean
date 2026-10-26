module
public import Linear.CutLocalRegularSequence
public import Linear.FiniteReducedLocalCut
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
open RingTheory.Sequence
variable {K : Type*} [Field K] {n r c : ℕ}

theorem polynomial_rationalPoint_height (x : Fin n → K) :
    (RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom).height=n := by
  let rs := List.ofFn (fun i : Fin n => MvPolynomial.X i-MvPolynomial.C (x i))
  have hs : Ideal.ofList rs=RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom := by
    rw [show Ideal.ofList rs=Ideal.span (Set.range
      (fun i : Fin n => MvPolynomial.X i-MvPolynomial.C (x i))) by
        simp [rs,Ideal.ofList,List.mem_ofFn,Set.range]]
    exact (polynomial_point_kernel_eq_span_centered_coordinates x).symm
  have hh := Ideal.ofList_height_eq_length_of_isWeaklyRegular rs
    (polynomial_centered_variables_regular n x).1
    (by rw [hs];exact (RingHom.ker_isPrime (MvPolynomial.aeval (R := K) x).toRingHom).ne_top)
  rw [hs] at hh
  simpa only [rs,List.length_ofFn,Fintype.card_fin] using hh

/-- The original r cut polynomials are regular in the original variety's
local quotient when c normal equations generate its actual local ideal,
c+r=n and the joint actual cut is finite and reduced. No global CM property
of the variety is assumed. -/
theorem polynomial_local_cut_equations_regular
    (x : Fin n → K) (I : Ideal (MvPolynomial (Fin n) K))
    (G : Fin c → MvPolynomial (Fin n) K) (H : Fin r → MvPolynomial (Fin n) K)
    (hdim : c+r=n)
    (hlocal : let P := RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom
      letI : P.IsPrime := RingHom.ker_isPrime _
      I.map (algebraMap _ (Localization.AtPrime P)) =
        Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime P) (G i))))
    (hpoint : I ⊔ Ideal.span (Set.range H) ≤
      RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom)
    [IsArtinianRing (MvPolynomial (Fin n) K ⧸ (I ⊔ Ideal.span (Set.range H)))]
    [IsReduced (MvPolynomial (Fin n) K ⧸ (I ⊔ Ideal.span (Set.range H)))] :
    let P := RingHom.ker (MvPolynomial.aeval (R := K) x).toRingHom
    letI : P.IsPrime := RingHom.ker_isPrime _
    let A := Localization.AtPrime P
    IsRegular (A ⧸ I.map (algebraMap _ A))
      (List.ofFn (fun i => Ideal.Quotient.mk (I.map (algebraMap _ A)) (algebraMap _ A (H i)))) := by
  intro P
  letI : P.IsPrime := RingHom.ker_isPrime _
  intro A
  letI : IsCohenMacaulayRing K := field_isCohenMacaulay
  letI : IsCohenMacaulayRing (MvPolynomial (Fin n) K) := MvPolynomial.isCM_of_isCM_of_finite K (Fin n)
  letI : IsCohenMacaulayLocalRing A :=
    (isCohenMacaulayRing_def (MvPolynomial (Fin n) K)).mp inferInstance P inferInstance
  let normal := List.ofFn (fun i => algebraMap _ A (G i))
  let cut := List.ofFn (fun i => algebraMap _ A (H i))
  have hn : Ideal.ofList normal=I.map (algebraMap _ A) := by
    rw [show Ideal.ofList normal=Ideal.span (Set.range (fun i => algebraMap _ A (G i))) by
      simp [normal,Ideal.ofList,List.mem_ofFn,Set.range]]
    exact hlocal.symm
  have hgen : Ideal.ofList (normal++cut)=IsLocalRing.maximalIdeal A := by
    rw [Ideal.ofList_append,hn]
    have hcut : Ideal.ofList cut=(Ideal.span (Set.range H)).map (algebraMap _ A) := by
      rw [Ideal.map_span,← Set.range_comp']
      simp [cut,Ideal.ofList,List.mem_ofFn,Set.range,Function.comp_def]
    rw [hcut,← Ideal.map_sup]
    exact artinian_reduced_cut_local_ideal_eq_maximalIdeal_of_le _ P hpoint
  have hlen : (normal++cut).length=ringKrullDim A := by
    rw [List.length_append,List.length_ofFn,List.length_ofFn,
      IsLocalization.AtPrime.ringKrullDim_eq_height P A,polynomial_rationalPoint_height x,hdim]
    rfl
  have hreg := local_cut_regular_of_ambient_parameters normal cut hgen hlen
  rw [hn,List.map_ofFn] at hreg
  exact hreg

end LinearStudy
