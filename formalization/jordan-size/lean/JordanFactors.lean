import MultiplicativeDecomposition
import GeneralizedProducts
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Multilinear.Curry

noncomputable section
namespace JordanSize
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The ordinary commuting multiplicative Jordan decomposition. -/
structure Factors (T : Module.End K V) where
  s : Module.End K V
  u : Module.End K V
  semisimple : s.IsSemisimple
  s_unit : IsUnit s
  unipotent : IsNilpotent (u - 1)
  u_unit : IsUnit u
  commute : Commute s u
  factor : T = s * u

theorem factorsExist [PerfectField K] [FiniteDimensional K V]
    (T : Module.End K V) (hT : IsUnit T) : Nonempty (Factors T) := by
  obtain ⟨s, u, -, hs, hsu, hu, huu, hc, hf⟩ := multiplicativeDecomposition T hT
  exact ⟨⟨s, u, hs, hsu, hu, huu, hc, hf⟩⟩

def jordanFactors [PerfectField K] [FiniteDimensional K V]
    (T : Module.End K V) (hT : IsUnit T) : Factors T :=
  Classical.choice (factorsExist T hT)

variable {T : Module.End K V} (F : Factors T)

lemma Factors.nilpotent_sub : IsNilpotent (T - F.s) := by
  have h : T - F.s = F.s * (F.u - 1) := by
    calc T - F.s = F.s * F.u - F.s := congrArg (fun L => L - F.s) F.factor
         _ = F.s * (F.u - 1) := by noncomm_ring
  rw [h]
  exact (F.commute.sub_right (Commute.one_right F.s)).isNilpotent_mul_left F.unipotent

lemma Factors.commute_T_s : Commute T F.s := by
  simpa only [F.factor] using (Commute.refl F.s).mul_left F.commute.symm

lemma Factors.T_unit (F : Factors T) : IsUnit T := by
  simpa only [F.factor] using F.s_unit.mul F.u_unit

/-- On each generalized eigenspace the semisimple factor is the scalar. -/
lemma Factors.s_apply {a : K} {x : V} (hx : x ∈ T.maxGenEigenspace a) :
    F.s x = a • x :=
  Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
    hx F.commute_T_s F.semisimple.isFinitelySemisimple F.nilpotent_sub

/-- On each generalized eigenspace the unipotent factor is a^{-1}T.
The zero-eigenvalue subspace is zero, since the semisimple factor is a unit. -/
lemma Factors.u_apply {a : K} {x : V} (hx : x ∈ T.maxGenEigenspace a) :
    F.u x = a⁻¹ • T x := by
  have hs := F.s_apply hx
  by_cases ha : a = 0
  · have hx0 : x = 0 := (Module.End.isUnit_iff F.s).mp F.s_unit |>.1
      (by simpa [ha] using hs)
    simp [hx0]
  · have h : T x = a • F.u x := by
      calc T x = (F.s * F.u) x := congrArg (fun L : Module.End K V => L x) F.factor
           _ = a • F.u x := by rw [F.commute.eq, Module.End.mul_apply, hs, map_smul]
    rw [h, smul_smul, inv_mul_cancel₀ ha, one_smul]

lemma Factors.fixed {x : V} (hx : T x = x) : F.u x = x := by
  have hgen : x ∈ T.maxGenEigenspace 1 := by
    apply T.mem_genEigenspace.mpr
    refine ⟨1, le_top, ?_⟩
    simpa [sub_eq_zero] using hx
  simpa [hx] using F.u_apply hgen

section Bilinear
variable {W Z : Type*} [AddCommGroup W] [Module K W]
  [AddCommGroup Z] [Module K Z]
  [IsAlgClosed K] [FiniteDimensional K V] [FiniteDimensional K W]
  [FiniteDimensional K Z]

/-- Componentwise multiplication followed by linear extension to all vectors. -/
theorem unipotent_bilinear (B : V →ₗ[K] W →ₗ[K] Z)
    (T : Module.End K V) (S : Module.End K W) (R : Module.End K Z)
    (FT : Factors T) (FS : Factors S) (FR : Factors R)
    (hB : ∀ x y, R (B x y) = B (T x) (S y)) (x : V) (y : W) :
    FR.u (B x y) = B (FT.u x) (FS.u y) := by
  have hcomp : ∀ a b x y,
      x ∈ T.maxGenEigenspace a → y ∈ S.maxGenEigenspace b →
      FR.u (B x y) = B (FT.u x) (FS.u y) := by
    intro a b x y hx hy
    obtain ⟨p, -, hp⟩ := (T.mem_genEigenspace).mp hx
    obtain ⟨q, -, hq⟩ := (S.mem_genEigenspace).mp hy
    have hp' : ((T - a • 1)^p) x = 0 := by simpa using hp
    have hq' : ((S - b • 1)^q) y = 0 := by simpa using hq
    have hxy : B x y ∈ R.maxGenEigenspace (a*b) := by
      apply R.mem_genEigenspace.mpr
      refine ⟨p+q-1, le_top, ?_⟩
      simpa using generalizedProduct B T S R hB a b p q x y hp' hq'
    rw [FR.u_apply hxy, FT.u_apply hx, FS.u_apply hy, hB]
    simp [map_smul, smul_smul, mul_inv_rev, mul_comm]
  have hx : x ∈ ⨆ a, T.maxGenEigenspace a := by
    rw [T.iSup_maxGenEigenspace_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun x =>
    FR.u (B x y) = B (FT.u x) (FS.u y)) hx ?_ (by simp) ?_
  · intro a x hx
    have hy : y ∈ ⨆ b, S.maxGenEigenspace b := by
      rw [S.iSup_maxGenEigenspace_eq_top]; trivial
    refine Submodule.iSup_induction _ (motive := fun y =>
      FR.u (B x y) = B (FT.u x) (FS.u y)) hy ?_ (by simp) ?_
    · intro b y hy
      exact hcomp a b x y hx hy
    · intro y z hy hz
      simp only [map_add, hy, hz]
  · intro x z hx hz
    simp only [map_add, LinearMap.add_apply, hx, hz]

end Bilinear
end JordanSize
#print axioms JordanSize.unipotent_bilinear
