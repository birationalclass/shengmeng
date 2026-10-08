module
public import Linear.ProjectiveAffineFiberUniversal
public import Mathlib.RingTheory.TensorProduct.Maps
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace LinearStudy
variable {n : ℕ}

/-- The tensor-product fiber ring of the ORIGINAL chart pullback is
isomorphic to its explicit polynomial fiber-equation quotient. -/
theorem projectiveAffineFiber_exists_tensor_equiv
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hq : 0 < f.degree) (hf : Function.Surjective f.onPoints)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (y : Fin n → ℂ)
    (hy : normalizedProjectivePoint y ∈ V.zeroSet) :
    let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
    let A := Localization.Away (projectiveChartDenominator f V)
    let φ := projectiveChartOpenMap f V hq hf hV y hy
    let ρ := V.affinePointEvaluation y hy
    letI : Algebra B A := φ.toRingHom.toAlgebra
    letI : SMul B A := (φ.toRingHom.toAlgebra).toSMul
    letI : Module B A := Algebra.toModule
    letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
    Nonempty ((A ⊗[B] ℂ) ≃ₐ[ℂ]
      (MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y)) := by
  let B := MvPolynomial (Fin n) ℂ ⧸ V.affineIdeal
  let A := Localization.Away (projectiveChartDenominator f V)
  let Q := MvPolynomial (Fin n) ℂ ⧸ projectiveAffineFiberIdeal f V y
  let φ := projectiveChartOpenMap f V hq hf hV y hy
  let ρ := V.affinePointEvaluation y hy
  let q := projectiveAffineFiberChartMap f V y
  letI : Algebra B A := φ.toRingHom.toAlgebra
  letI : SMul B A := (φ.toRingHom.toAlgebra).toSMul
  letI : Module B A := Algebra.toModule
  letI : Algebra B ℂ := ρ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ B A := IsScalarTower.of_algHom φ
  letI : IsScalarTower ℂ B ℂ := IsScalarTower.of_algHom ρ
  letI : IsScalarTower B B A := ⟨fun r s a => by
    change φ (r * s) * a = φ r * (φ s * a)
    rw [map_mul, mul_assoc]⟩
  letI : Algebra B Q := ((algebraMap ℂ Q).comp ρ.toRingHom).toAlgebra
  letI : SMul B Q := (((algebraMap ℂ Q).comp ρ.toRingHom).toAlgebra).toSMul
  letI : IsScalarTower B ℂ Q := IsScalarTower.of_algebraMap_eq
    (R := B) (S := ℂ) (A := Q) (fun _ => rfl)
  letI : IsScalarTower B B Q := ⟨fun r s a => by
    change (algebraMap ℂ Q (ρ (r * s))) * a =
      algebraMap ℂ Q (ρ r) * (algebraMap ℂ Q (ρ s) * a)
    rw [map_mul, map_mul, mul_assoc]⟩
  let T := A ⊗[B] ℂ
  let ι : A →ₐ[ℂ] T := Algebra.TensorProduct.includeLeft
  have hr (c : ℂ) : (Algebra.TensorProduct.includeRight : ℂ →ₐ[B] T) c =
      algebraMap ℂ T c := by
    have h := RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := B) (A := A) (B := ℂ))
        (algebraMap ℂ B c)
    change Algebra.TensorProduct.includeLeftRingHom (φ (algebraMap ℂ B c)) =
      Algebra.TensorProduct.includeRight.toRingHom (ρ (algebraMap ℂ B c)) at h
    rw [φ.commutes, ρ.commutes] at h
    exact h.symm
  have hι : ι.comp φ = (Algebra.ofId ℂ T).comp ρ := by
    apply AlgHom.ext
    intro b
    have h := RingHom.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := B) (A := A) (B := ℂ)) b
    change ι (φ b) = algebraMap ℂ T (ρ b)
    exact h.trans (hr (ρ b))
  obtain ⟨u, hu, _⟩ := projectiveAffineFiberChartMap_exists_unique_lift
    f V hq hf hV y hy ι hι
  have hu' (a : A) : u (q a) = ι a := AlgHom.congr_fun hu a
  let qB : A →ₐ[B] Q :=
    { q.toRingHom with
      commutes' := fun b => AlgHom.congr_fun
        (projectiveAffineFiberChartMap_pullback f V hq hf hV y hy) b }
  let v : T →ₐ[B] Q := Algebra.TensorProduct.lift qB
    (IsScalarTower.toAlgHom B ℂ Q) (fun _ _ => Commute.all _ _)
  have hv (a : A) : v (ι a) = q a := by
    change qB a * (IsScalarTower.toAlgHom B ℂ Q) 1 = q a
    rw [map_one, mul_one]
    rfl
  have hvu : Function.LeftInverse v u := by
    intro z
    obtain ⟨a, rfl⟩ := projectiveAffineFiberChartMap_surjective f V y z
    change v (u (q a)) = q a
    rw [hu', hv]
  have huv : Function.RightInverse v u := by
    intro z
    have hρ : Function.Surjective (algebraMap B ℂ) := by
      intro c
      refine ⟨algebraMap ℂ B c, ?_⟩
      exact ρ.commutes c
    obtain ⟨a, rfl⟩ := Algebra.TensorProduct.includeLeft_surjective ℂ A hρ z
    change u (v (ι a)) = ι a
    rw [hv, hu']
  have hvK (c : ℂ) : v (algebraMap ℂ T c) = algebraMap ℂ Q c := by
    exact (hv (algebraMap ℂ A c)).trans (q.commutes c)
  exact ⟨{
    toRingEquiv := { v.toRingHom with invFun := u, left_inv := huv, right_inv := hvu }
    commutes' := hvK }⟩

end LinearStudy
