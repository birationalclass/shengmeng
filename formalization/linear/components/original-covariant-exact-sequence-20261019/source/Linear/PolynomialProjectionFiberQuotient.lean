module
public import Linear.FiniteProjectionTensorFibers
public import Mathlib.RingTheory.TensorProduct.Maps
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace LinearStudy

/-- The actual affine fiber ideal, including the original source ideal. -/
def polynomialProjectionFiberIdeal {K σ τ : Type*} [CommRing K]
    (I : Ideal (MvPolynomial σ K)) (L : τ → MvPolynomial σ K) (w : τ → K) :
    Ideal (MvPolynomial σ K) := I ⊔ Ideal.span (Set.range (fun i => L i-MvPolynomial.C (w i)))

/-- The explicit fiber-equation quotient has the actual base-change
universal property. This proves a ring-level statement, not just equality
of scalar-valued point sets. -/
theorem polynomialProjectionFiber_exists_unique_lift {K σ τ C : Type*}
    [CommRing K] [CommRing C] [Algebra K C]
    (I : Ideal (MvPolynomial σ K)) (L : τ → MvPolynomial σ K) (w : τ → K)
    (χ : (MvPolynomial σ K ⧸ I) →ₐ[K] C)
    (hχ : χ.comp ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L))=
      (Algebra.ofId K C).comp (MvPolynomial.aeval w)) :
    ∃! u : (MvPolynomial σ K ⧸ polynomialProjectionFiberIdeal I L w) →ₐ[K] C,
      u.comp (Ideal.Quotient.mkₐ K (polynomialProjectionFiberIdeal I L w))=
        χ.comp (Ideal.Quotient.mkₐ K I) := by
  let η := χ.comp (Ideal.Quotient.mkₐ K I)
  have hL (i : τ) : η (L i)=algebraMap K C (w i) := by
    have h := AlgHom.congr_fun hχ (MvPolynomial.X i)
    dsimp only [η]
    simpa only [AlgHom.comp_apply,MvPolynomial.aeval_X,Algebra.ofId_apply] using h
  have hJ : ∀ P ∈ polynomialProjectionFiberIdeal I L w,η P=0 := by
    have hle : polynomialProjectionFiberIdeal I L w ≤ RingHom.ker η.toRingHom := by
      apply sup_le
      · intro P hP
        change χ (Ideal.Quotient.mk I P)=0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP,map_zero]
      · apply Ideal.span_le.mpr
        rintro P ⟨i,rfl⟩
        change η (L i-MvPolynomial.C (w i))=0
        rw [map_sub,MvPolynomial.algHom_C,hL,sub_self]
    exact fun P hP => RingHom.mem_ker.mp (hle hP)
  let u := Ideal.Quotient.liftₐ (polynomialProjectionFiberIdeal I L w) η hJ
  refine ⟨u,?_,?_⟩
  · ext P
    rfl
  · intro u' hu'
    apply AlgHom.ext
    intro z
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective z
    exact AlgHom.congr_fun hu' P

/-- Actual tensor fiber equals the explicit equation quotient, with the
original coefficient-field algebra structures. This is not inferred from
a bijection of points. -/
theorem polynomialProjectionFiber_exists_tensor_equiv {K σ τ : Type*} [CommRing K]
    (I : Ideal (MvPolynomial σ K)) (L : τ → MvPolynomial σ K) (w : τ → K) :
    let R := MvPolynomial τ K
    let A := MvPolynomial σ K ⧸ I
    let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
    letI : Algebra R A := φ.toRingHom.toAlgebra
    letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
    letI : Module R A := Algebra.toModule
    letI : Algebra R K := (MvPolynomial.aeval w).toRingHom.toAlgebra
    letI : SMul R K := (MvPolynomial.aeval w).toRingHom.toAlgebra.toSMul
    letI : Module R K := Algebra.toModule
    letI : IsScalarTower K R A := IsScalarTower.of_algHom φ
    Nonempty ((A ⊗[R] K) ≃ₐ[K]
      (MvPolynomial σ K ⧸ polynomialProjectionFiberIdeal I L w)) := by
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let J := polynomialProjectionFiberIdeal I L w
  let Q := MvPolynomial σ K ⧸ J
  let AKQ : Algebra K Q := inferInstance
  letI : Algebra K Q := AKQ
  letI : SMul K Q := AKQ.toSMul
  letI : Module K Q := Algebra.toModule
  let φ := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval L)
  let ρ : R →ₐ[K] K := MvPolynomial.aeval w
  letI : Algebra R A := φ.toRingHom.toAlgebra
  letI : SMul R A := φ.toRingHom.toAlgebra.toSMul
  letI : Module R A := Algebra.toModule
  letI : Algebra R K := ρ.toRingHom.toAlgebra
  letI : SMul R K := ρ.toRingHom.toAlgebra.toSMul
  letI : Module R K := Algebra.toModule
  letI : IsScalarTower K R A := IsScalarTower.of_algHom φ
  letI : IsScalarTower K R K := IsScalarTower.of_algHom ρ
  letI : IsScalarTower R R A := ⟨fun r s a => by
    change φ (r*s)*a=φ r*(φ s*a)
    rw [map_mul,mul_assoc]⟩
  have hIJ : I ≤ J := le_sup_left
  let q : A →ₐ[K] Q := Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K J)
    (fun P hP => Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hP))
  have hφX (i : τ) : φ (MvPolynomial.X i)=Ideal.Quotient.mk I (L i) := by
    simp [φ]
  have hρX (i : τ) : ρ (MvPolynomial.X i)=w i := by
    exact MvPolynomial.aeval_X w i
  have hqP (P : MvPolynomial σ K) : q (Ideal.Quotient.mk I P)=Ideal.Quotient.mk J P :=
    Ideal.Quotient.lift_mk _ _ _
  have hq : q.comp φ=(Algebra.ofId K Q).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro i
    change q (φ (MvPolynomial.X i))=(Algebra.ofId K Q) (ρ (MvPolynomial.X i))
    rw [hφX,hqP,hρX,Algebra.ofId_apply]
    have hzero : Ideal.Quotient.mk J (L i-MvPolynomial.C (w i))=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span (Set.range (fun i => L i-MvPolynomial.C (w i))) ≤ J from le_sup_right)
        (Ideal.subset_span (Set.mem_range_self i)))
    rw [map_sub] at hzero
    exact (sub_eq_zero.mp hzero).trans (MvPolynomial.algHom_C (Ideal.Quotient.mkₐ K J) (w i))
  let T := A ⊗[R] K
  letI : Algebra K T := Algebra.TensorProduct.leftAlgebra
  letI : SMul K T := (Algebra.TensorProduct.leftAlgebra (R:=R) (S:=K) (A:=A) (B:=K)).toSMul
  let ι : A →ₐ[K] T := Algebra.TensorProduct.includeLeft
  have hr (c : K) :
      (Algebra.TensorProduct.includeRight (R:=R) (A:=A) (B:=K)) c=
      ι (algebraMap K A c) := by
    have h := RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R:=R) (A:=A) (B:=K))
        (algebraMap K R c)
    change Algebra.TensorProduct.includeLeftRingHom (φ (algebraMap K R c))=
      Algebra.TensorProduct.includeRight.toRingHom (ρ (algebraMap K R c)) at h
    rw [φ.commutes,ρ.commutes] at h
    exact h.symm
  have hι : ι.comp φ=(Algebra.ofId K T).comp ρ := by
    apply AlgHom.ext
    intro b
    exact (RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R:=R) (A:=A) (B:=K)) b).trans
        ((hr (ρ b)).trans (ι.commutes (ρ b)))
  obtain ⟨u,hu,_⟩ := polynomialProjectionFiber_exists_unique_lift (C:=T) I L w ι
    (by change ι.comp φ=(Algebra.ofId K T).comp ρ; exact hι)
  letI : Algebra R Q := ((algebraMap K Q).comp ρ.toRingHom).toAlgebra
  letI : SMul R Q := (((algebraMap K Q).comp ρ.toRingHom).toAlgebra).toSMul
  letI : Module R Q := Algebra.toModule
  letI : IsScalarTower R K Q := ⟨fun r c z => by
    simp only [Algebra.smul_def]
    change algebraMap K Q (ρ r*c)*z=
      algebraMap K Q (ρ r)*(algebraMap K Q c*z)
    rw [map_mul,mul_assoc]⟩
  letI : IsScalarTower R R Q := ⟨fun r s z => by
    change algebraMap R Q (r*s)*z=algebraMap R Q r*(algebraMap R Q s*z)
    rw [map_mul,mul_assoc]⟩
  let qR : A →ₐ[R] Q := { q.toRingHom with commutes' := fun b => AlgHom.congr_fun hq b }
  let v : T →ₐ[R] Q := Algebra.TensorProduct.lift qR
    (IsScalarTower.toAlgHom R K Q) (fun _ _ => Commute.all _ _)
  have hv (a : A) : v (ι a)=q a := by
    change qR a*(IsScalarTower.toAlgHom R K Q) 1=q a
    rw [map_one,mul_one]
    rfl
  have hu' (P : MvPolynomial σ K) : u (Ideal.Quotient.mk J P)=ι (Ideal.Quotient.mk I P) :=
    AlgHom.congr_fun hu P
  have hvu : Function.LeftInverse v u := by
    intro z
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hu',hv]
    rfl
  have huv : Function.RightInverse v u := by
    intro z
    have hρ : Function.Surjective (algebraMap R K) := fun c =>
      ⟨algebraMap K R c,ρ.commutes c⟩
    obtain ⟨a,rfl⟩ := Algebra.TensorProduct.includeLeft_surjective K A hρ z
    obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hv]
    exact hu' P
  let vK : T →ₐ[K] Q :=
    { v.toRingHom with
      commutes' := by
        intro c
        exact (congrArg v (ι.commutes c).symm).trans
          ((hv (algebraMap K A c)).trans (q.commutes c)) }
  exact ⟨AlgEquiv.ofBijective vK ⟨huv.injective,hvu.surjective⟩⟩

end LinearStudy
