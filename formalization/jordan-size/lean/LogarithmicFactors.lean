import MultilinearFactors
import FlowLeibniz
import ExponentialChains

noncomputable section
namespace JordanSize
variable {K V : Type*} [Field K] [Algebra ℚ K]
  [AddCommGroup V] [Module K V] [Module ℚ V] [IsScalarTower ℚ K V]

def restrictEnd : Module.End K V →+* Module.End ℚ V where
  toFun L := L.restrictScalars ℚ
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable {T : Module.End K V}
def Factors.log (F : Factors T) : Module.End K V :=
  operatorLog (F.u - 1) (nilpotencyClass (F.u - 1))
lemma Factors.log_nilpotent (F : Factors T) : IsNilpotent F.log :=
  operatorLog_nilpotent _ F.unipotent _
lemma Factors.exp_log (F : Factors T) : IsNilpotent.exp F.log = F.u := by
  have h := operatorExpLog (F.u-1) (nilpotencyClass (F.u-1))
    (pow_nilpotencyClass F.unipotent)
  simpa [Factors.log] using h

section Bilinear
variable {W Z : Type*} [AddCommGroup W] [Module K W] [Module ℚ W]
  [IsScalarTower ℚ K W] [AddCommGroup Z] [Module K Z] [Module ℚ Z]
  [IsScalarTower ℚ K Z] [IsAlgClosed K] [FiniteDimensional K V]
  [FiniteDimensional K W] [FiniteDimensional K Z]

theorem logarithm_bilinear (B : V →ₗ[K] W →ₗ[K] Z)
    (T : Module.End K V) (S : Module.End K W) (R : Module.End K Z)
    (FT : Factors T) (FS : Factors S) (FR : Factors R)
    (hB : ∀ x y, R (B x y) = B (T x) (S y)) (x : V) (y : W) :
    FR.log (B x y) = B (FT.log x) y + B x (FS.log y) := by
  let b := B.restrictScalars₁₂ ℚ ℚ
  have hD := FT.log_nilpotent.map (restrictEnd (K := K))
  have hE := FS.log_nilpotent.map (restrictEnd (K := K))
  have hF := FR.log_nilpotent.map (restrictEnd (K := K))
  have he (L : Module.End K V) (hL : IsNilpotent L) :
      flow (restrictEnd L) 1 = restrictEnd (IsNilpotent.exp L) := by
    simpa [flow] using (hL.map_exp (restrictEnd (K := K))).symm
  have heW (L : Module.End K W) (hL : IsNilpotent L) :
      flow (restrictEnd L) 1 = restrictEnd (IsNilpotent.exp L) := by
    simpa [flow] using (hL.map_exp (restrictEnd (K := K))).symm
  have heZ (L : Module.End K Z) (hL : IsNilpotent L) :
      flow (restrictEnd L) 1 = restrictEnd (IsNilpotent.exp L) := by
    simpa [flow] using (hL.map_exp (restrictEnd (K := K))).symm
  have hb : ∀ x y, (flow (restrictEnd FR.log) 1) (b x y) =
      b ((flow (restrictEnd FT.log) 1) x) ((flow (restrictEnd FS.log) 1) y) := by
    intro x y
    rw [heZ _ FR.log_nilpotent, he _ FT.log_nilpotent, heW _ FS.log_nilpotent,
      FR.exp_log, FT.exp_log, FS.exp_log]
    exact unipotent_bilinear B T S R FT FS FR hB x y
  exact flowLeibniz b _ _ _ hD hE hF hb x y
end Bilinear
end JordanSize
#print axioms JordanSize.logarithm_bilinear
