module
public import Linear.HomogeneousCoordinateGrading
public import Linear.HomogeneousRationalPullback
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] {n : ℕ}

/-- A homogeneous fraction in the native first chart of ANY homogeneous
polynomial quotient. No primality, radicality or reducedness is assumed. -/
def homogeneousQuotientNativeChartElement
    (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K))
    (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m) :
    letI := homogeneousQuotientGrading I hI
    HomogeneousLocalization.Away (homogeneousQuotientPiece I)
      (Ideal.Quotient.mk I (MvPolynomial.X 0)) := by
  letI := homogeneousQuotientGrading I hI
  exact HomogeneousLocalization.Away.mk (homogeneousQuotientPiece I)
    (show Ideal.Quotient.mk I (MvPolynomial.X 0) ∈ homogeneousQuotientPiece I 1 from
      ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X K 0,rfl⟩) m
    (Ideal.Quotient.mk I H)
    (by simpa only [smul_eq_mul,mul_one] using
      (show Ideal.Quotient.mk I H ∈ homogeneousQuotientPiece I m from ⟨H,hH,rfl⟩))

/-- The actual native first chart is the actual dehomogenized quotient,
even for a nonintegral or nonreduced homogeneous ideal. The isomorphism
retains the original equations and is compatible with homogeneous fractions. -/
theorem homogeneousQuotient_nativeChart_ringEquiv
    (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule _ K)) :
    letI := homogeneousQuotientGrading I hI
    ∃ e : (MvPolynomial (Fin n) K ⧸ I.map (affineChartPolynomialMap (K := K)).toRingHom) ≃+*
      HomogeneousLocalization.Away (homogeneousQuotientPiece I)
        (Ideal.Quotient.mk I (MvPolynomial.X 0)),
      ∀ (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m),
        e (Ideal.Quotient.mk _ (affineChartPolynomialMap H)) =
          homogeneousQuotientNativeChartElement I hI m H hH := by
  classical
  letI := homogeneousQuotientGrading I hI
  let A := MvPolynomial (Fin (n+1)) K ⧸ I
  let a₀ : A := Ideal.Quotient.mk I (MvPolynomial.X 0)
  let 𝒜 := homogeneousQuotientPiece I
  let T := HomogeneousLocalization.Away 𝒜 a₀
  let B := Localization.Away a₀
  let J := I.map (affineChartPolynomialMap (K := K)).toRingHom
  let C := MvPolynomial (Fin n) K ⧸ J
  have hgrade : a₀ ∈ 𝒜 1 :=
    ⟨MvPolynomial.X 0,MvPolynomial.isHomogeneous_X K 0,rfl⟩
  let k₀ : K →+* 𝒜 0 :=
    { toFun := fun c => ⟨algebraMap K A c,⟨MvPolynomial.C c,MvPolynomial.isHomogeneous_C _ c,rfl⟩⟩
      map_one' := Subtype.ext (map_one (algebraMap K A))
      map_zero' := Subtype.ext (map_zero (algebraMap K A))
      map_mul' := fun c d => Subtype.ext (map_mul (algebraMap K A) c d)
      map_add' := fun c d => Subtype.ext (map_add (algebraMap K A) c d) }
  let coeff : K →+* T := (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers a₀)).comp k₀
  have hcoeff (c : K) : (coeff c).val = algebraMap K B c := by
    change Localization.mk (algebraMap K A c) (1 : Submonoid.powers a₀)=algebraMap K B c
    exact Localization.mk_algebraMap c
  let β : T →+* B := algebraMap T B
  let z : Fin (n+1) → B := fun i => algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))
  let inv : B := IsLocalization.Away.invSelf a₀
  let v : Fin n → T := fun i => homogeneousQuotientNativeChartElement I hI 1
    (MvPolynomial.X i.succ) (MvPolynomial.isHomogeneous_X K i.succ)
  let φ : MvPolynomial (Fin n) K →+* T := MvPolynomial.eval₂Hom coeff v
  have hz0 : z 0 * inv=1 := IsLocalization.Away.mul_invSelf a₀
  have hvval (i : Fin n) : β (v i)=z i.succ*inv := by
    change (v i).val=z i.succ*inv
    dsimp only [v,homogeneousQuotientNativeChartElement]
    rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    simp only [pow_one]
    rfl
  have hφval : β.comp φ=(MvPolynomial.aeval (fun i => z i.succ*inv)).toRingHom := by
    have hc : β.comp coeff=algebraMap K B := by
      apply RingHom.ext
      intro c
      exact hcoeff c
    dsimp only [φ]
    rw [MvPolynomial.comp_eval₂Hom,hc]
    change MvPolynomial.eval₂Hom (algebraMap K B) (fun i => β (v i))=
      MvPolynomial.eval₂Hom (algebraMap K B) (fun i => z i.succ*inv)
    congr 1
    funext i
    exact hvval i
  have hz : MvPolynomial.aeval z=(IsScalarTower.toAlgHom K A B).comp (Ideal.Quotient.mkₐ K I) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [MvPolynomial.aeval_X]
    rfl
  have hhom (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m) :
      φ (affineChartPolynomialMap H)=homogeneousQuotientNativeChartElement I hI m H hH := by
    apply HomogeneousLocalization.val_injective (Submonoid.powers a₀)
    change β (φ (affineChartPolynomialMap H)) = _
    rw [← RingHom.comp_apply,hφval]
    change MvPolynomial.aeval _ (affineChartPolynomialMap H)=_
    rw [← AlgHom.comp_apply,affineChartPolynomialMap_comp_aeval]
    have hv' : Fin.cases 1 (fun i => z i.succ*inv)=(fun i : Fin (n+1) => inv*z i) := by
      funext i
      cases i using Fin.cases with
      | zero => exact hz0.symm.trans (mul_comm (z 0) inv)
      | succ i => exact mul_comm (z i.succ) inv
    rw [hv',homogeneous_aeval_smul hH,hz,AlgHom.comp_apply]
    change inv^m*algebraMap A B (Ideal.Quotient.mk I H) = _
    dsimp only [homogeneousQuotientNativeChartElement]
    rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',
      IsLocalization.mk'_eq_mul_mk'_one]
    have hfrac : IsLocalization.mk' B 1
        (⟨a₀,Submonoid.mem_powers a₀⟩ ^ m)=inv^m := by
      change IsLocalization.mk' B 1 (⟨a₀,Submonoid.mem_powers a₀⟩ ^ m)=
        (IsLocalization.mk' B (1 : A) ⟨a₀,Submonoid.mem_powers a₀⟩)^m
      simpa only [one_pow] using (IsLocalization.mk'_pow (S := B) (1 : A)
        (⟨a₀,Submonoid.mem_powers a₀⟩) m)
    change inv^m*algebraMap A B (Ideal.Quotient.mk I H)=
      algebraMap A B (Ideal.Quotient.mk I H)*
        IsLocalization.mk' B 1 (⟨a₀,Submonoid.mem_powers a₀⟩ ^ m)
    rw [hfrac]
    exact mul_comm _ _
  have hker : J ≤ RingHom.ker φ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro P hP
    change φ (affineChartPolynomialMap P)=0
    rw [← MvPolynomial.sum_homogeneousComponent P]
    simp only [map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    rw [hhom m _ (MvPolynomial.homogeneousComponent_isHomogeneous m P)]
    have hmem := MvPolynomial.homogeneousComponent_mem_of_mem hI hP m
    apply HomogeneousLocalization.val_injective (Submonoid.powers a₀)
    simp only [homogeneousQuotientNativeChartElement,HomogeneousLocalization.Away.val_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem,Localization.mk_zero,HomogeneousLocalization.val_zero]
  let φq : C →+* T := Ideal.Quotient.lift J φ hker
  let deh : A →+* C := Ideal.Quotient.lift I
    ((Ideal.Quotient.mk J).comp (affineChartPolynomialMap (K := K)).toRingHom)
    (by
      intro P hP
      change Ideal.Quotient.mk J (affineChartPolynomialMap P)=0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hP))
  have hdeh0 : deh a₀=1 := by
    change Ideal.Quotient.mk J (affineChartPolynomialMap (MvPolynomial.X 0))=1
    simp [affineChartPolynomialMap]
  let ψB : B →+* C := IsLocalization.Away.lift a₀ (hdeh0 ▸ isUnit_one)
  let ψ : T →+* C := ψB.comp (algebraMap T B)
  have hψhom (m : ℕ) (H : MvPolynomial (Fin (n+1)) K) (hH : H.IsHomogeneous m) :
      ψ (homogeneousQuotientNativeChartElement I hI m H hH)=
        Ideal.Quotient.mk J (affineChartPolynomialMap H) := by
    have hspec : algebraMap A B (a₀^m)*
        (homogeneousQuotientNativeChartElement I hI m H hH).val =
          algebraMap A B (Ideal.Quotient.mk I H) := by
      dsimp only [homogeneousQuotientNativeChartElement]
      rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
      exact IsLocalization.mk'_spec' B _ _
    have hh := congrArg ψB hspec
    simp only [map_mul,ψB,IsLocalization.Away.lift_eq,map_pow,hdeh0,one_pow,one_mul] at hh
    exact hh
  have hinj : Function.Injective φq := by
    have hleft : ∀ a : C, ψ (φq a)=a := by
      intro a
      obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
      change ψ (φ P)=Ideal.Quotient.mk J P
      have he : ψ.comp φ=Ideal.Quotient.mk J := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp only [RingHom.comp_apply,φ,MvPolynomial.eval₂Hom_C]
          have hc : coeff c=homogeneousQuotientNativeChartElement I hI 0
              (MvPolynomial.C c) (MvPolynomial.isHomogeneous_C _ c) := by
            apply HomogeneousLocalization.val_injective (Submonoid.powers a₀)
            rw [hcoeff]
            dsimp only [homogeneousQuotientNativeChartElement]
            rw [HomogeneousLocalization.Away.val_mk]
            simp only [pow_zero]
            exact (Localization.mk_algebraMap c).symm
          rw [hc,hψhom]
          simp only [affineChartPolynomialMap,MvPolynomial.aeval_C]
          rfl
        · intro i
          simp only [RingHom.comp_apply,φ,MvPolynomial.eval₂Hom_X']
          rw [hψhom]
          simp only [affineChartPolynomialMap,MvPolynomial.aeval_X,Fin.cases_succ]
          rfl
      exact RingHom.congr_fun he P
    exact Function.LeftInverse.injective hleft
  have hsurj : Function.Surjective φq := by
    intro b
    obtain ⟨m,a,ha,rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hgrade b
    have ham : a ∈ 𝒜 m := by simpa only [smul_eq_mul,mul_one] using ha
    obtain ⟨H,hH,rfl⟩ := (homogeneousQuotientPiece_mem_iff I m a).mp ham
    refine ⟨Ideal.Quotient.mk J (affineChartPolynomialMap H),?_⟩
    exact hhom m H hH
  refine ⟨RingEquiv.ofBijective φq ⟨hinj,hsurj⟩,?_⟩
  intro m H hH
  exact hhom m H hH

end LinearStudy
