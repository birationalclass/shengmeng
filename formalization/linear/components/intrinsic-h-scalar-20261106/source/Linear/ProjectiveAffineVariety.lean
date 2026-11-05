module
public import Linear.ProjectiveAffinePoint
public import Linear.ProjectiveRationalInvariance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem normalizedCoordinateVector_ne_zero (x : Fin n → ℂ) :
    (Fin.cases 1 x : CoordinateVector n) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

def normalizedProjectivePoint (x : Fin n → ℂ) : ProjectivePoint n :=
  Projectivization.mk ℂ (Fin.cases 1 x) (normalizedCoordinateVector_ne_zero x)

def IntegralProjectiveEquations.affineIdeal (V : IntegralProjectiveEquations n) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  V.ideal.toIdeal.map affineChartPolynomialMap.toRingHom

theorem IntegralProjectiveEquations.normalizedPoint_mem_iff
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ) :
    normalizedProjectivePoint x ∈ V.zeroSet ↔
      Fin.cases 1 x ∈ MvPolynomial.zeroLocus ℂ V.ideal.toIdeal :=
  V.mem_zeroSet_mk _ _

theorem IntegralProjectiveEquations.affineIdeal_isPrime_of_point
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) : V.affineIdeal.IsPrime := by
  letI := V.prime
  exact affineChartPolynomialMap_ideal_isPrime_of_point V.ideal.toIdeal
    V.ideal.isHomogeneous x ((V.normalizedPoint_mem_iff x).mp hx)

theorem IntegralProjectiveEquations.affineIdeal_le_pointKernel
    (V : IntegralProjectiveEquations n) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet) :
    V.affineIdeal ≤ RingHom.ker (MvPolynomial.aeval (R := ℂ) x).toRingHom :=
  affineChartPolynomialMap_ideal_le_pointKernel V.ideal.toIdeal x
    ((V.normalizedPoint_mem_iff x).mp hx)

theorem IntegralProjectiveEquations.affineIdeal_ne_bot
    (V : IntegralProjectiveEquations n) (hV : V.ideal.toIdeal ≠ ⊥) :
    V.affineIdeal ≠ ⊥ :=
  affineChartPolynomialMap_ideal_ne_bot V.ideal.toIdeal V.ideal.isHomogeneous hV

theorem projective_total_invariance_affine_image_mem
    (f : HomogeneousEndomorphism n) (V : IntegralProjectiveEquations n)
    (hV : f.onPoints ⁻¹' V.zeroSet = V.zeroSet) (x : Fin n → ℂ)
    (hx : normalizedProjectivePoint x ∈ V.zeroSet)
    (hp0 : MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0)) ≠ 0) :
    normalizedProjectivePoint (fun i =>
      MvPolynomial.eval x (affineChartPolynomialMap (f.forms i.succ)) /
      MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0))) ∈ V.zeroSet := by
  let v : CoordinateVector n := Fin.cases 1 x
  let w := f.evalVector v
  have hv : v ≠ 0 := normalizedCoordinateVector_ne_zero x
  have hw : w ≠ 0 := f.noBasePoint v hv
  have hfV : f.onPoints (normalizedProjectivePoint x) ∈ V.zeroSet := by
    have h := congrArg (fun S => normalizedProjectivePoint x ∈ S) hV
    exact h.mpr hx
  have hvan : ∀ H ∈ V.ideal.toIdeal, MvPolynomial.eval w H = 0 := by
    apply (V.mem_zeroSet_mk w hw).mp
    exact hfV
  have he : ∀ i, MvPolynomial.eval x (affineChartPolynomialMap (f.forms i)) = w i := by
    intro i
    have h := congrArg (fun φ : CoordinateRing n →ₐ[ℂ] ℂ => φ (f.forms i))
      (affineChartPolynomialMap_comp_aeval (K := ℂ) x)
    exact h
  have hw0 : w 0 ≠ 0 := by rwa [he] at hp0
  apply (V.normalizedPoint_mem_iff _).mpr
  have hs := homogeneous_ideal_vanish_smul V.ideal w hvan (w 0)⁻¹
  have hvec : (w 0)⁻¹ • w = Fin.cases 1
      (fun i => MvPolynomial.eval x (affineChartPolynomialMap (f.forms i.succ)) /
        MvPolynomial.eval x (affineChartPolynomialMap (f.forms 0))) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Pi.smul_apply, smul_eq_mul, hw0]
    | succ i => simp [Pi.smul_apply, smul_eq_mul, he, div_eq_mul_inv, mul_comm]
  rwa [hvec] at hs

end LinearStudy
