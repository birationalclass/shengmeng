module
public import Negativity.ActualRelativeCechHOneReesModule
public import Negativity.GradedModuleMapReuse
public import Mathlib.RingTheory.Noetherian.Basic
public import Negativity.FiniteGradedModuleGeneratorBound

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actual_relative_cech_graded_forget_kernel_preserved
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) (m n : ℕ)
    (r : Γ(Y, ⊤)) (hr : r ∈ (I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m)
    (a : actualClosedCechHOne ((I ^ n).comap f).subschemeι (fun j => (U j).1))
    (ha : actualClosedCechForget ((I ^ n).comap f).subschemeι
      (fun j => (U j).1) a = 0) :
    actualClosedCechForget ((I ^ (m + n)).comap f).subschemeι
      (fun j => (U j).1) (actualRelativeCechGradedHOne f I U hU m n r hr a) = 0 := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective a
  change ((actualClosedCechForgetCycle ((I ^ n).comap f).subschemeι
    (fun j => (U j).1) z) : actualCechHOne X (fun j => (U j).1)) = 0 at ha
  obtain ⟨b, hb⟩ := (QuotientAddGroup.eq_zero_iff _).mp ha
  have hdb : actualCechDifference X (fun j => (U j).1) b = z.1 :=
    congrArg Subtype.val hb
  change ((actualClosedCechForgetCycle ((I ^ (m + n)).comap f).subschemeι
    (fun j => (U j).1) (actualRelativeCechGradedCycle f I U hU m n r hr z)) :
      actualCechHOne X (fun j => (U j).1)) = 0
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨actualCechScaleZero X (fun j => (U j).1) (f.appTop r) b, ?_⟩
  apply Subtype.ext
  change actualCechDifference X (fun j => (U j).1)
    (actualCechScaleZero X (fun j => (U j).1) (f.appTop r) b) =
      actualCechScaleOne X (fun j => (U j).1) (f.appTop r) z.1
  rw [actual_cech_difference_scale, hdb]

def actualRelativeCechForgetKernel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens) (n : ℕ) :
    AddSubgroup (actualClosedCechHOne ((I ^ n).comap f).subschemeι
      (fun j => (U j).1)) :=
  (actualClosedCechForget ((I ^ n).comap f).subschemeι (fun j => (U j).1)).ker

@[instance_reducible]
def actualRelativeCechForgetKernelGradedSMul {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    GradedMonoid.GSMul
      (fun n : ℕ => ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (fun n : ℕ => ↥(actualRelativeCechForgetKernel f I U n)) where
  smul {m n} r a := ⟨actualRelativeCechGradedHOne f I U hU m n r.1 r.2 a.1,
    actual_relative_cech_graded_forget_kernel_preserved f I U hU m n r.1 r.2 a.1 a.2⟩

@[instance_reducible]
def actualRelativeCechForgetKernelGradedModule {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    DirectSum.Gmodule
      (fun n : ℕ => ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (fun n : ℕ => ↥(actualRelativeCechForgetKernel f I U n)) := by
  letI := actualRelativeCechHOneGradedModule f I U hU
  letI := actualRelativeCechForgetKernelGradedSMul f I U hU
  exact actualGradedModuleOfInjective
    (fun n => (actualRelativeCechForgetKernel f I U n).subtype)
    (fun _ => Subtype.val_injective) (by intros; rfl)

@[instance_reducible]
def actualRelativeCechForgetKernelDirectSumModule {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    Module (⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (⨁ n : ℕ, ↥(actualRelativeCechForgetKernel f I U n)) := by
  letI := actualRelativeCechForgetKernelGradedModule f I U hU
  infer_instance

def actualRelativeCechForgetKernelInclusion {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    letI := actualRelativeCechForgetKernelDirectSumModule f I U hU
    letI := actualRelativeCechHOneDirectSumReesModule f I U hU
    (⨁ n : ℕ, ↥(actualRelativeCechForgetKernel f I U n)) →ₗ[
      ⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n)]
      (⨁ n : ℕ, actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) := by
  letI := actualRelativeCechForgetKernelGradedModule f I U hU
  letI := actualRelativeCechHOneGradedModule f I U hU
  exact actualGradedModuleMap
    (fun n => (actualRelativeCechForgetKernel f I U n).subtype) (by intros; rfl)

theorem actual_relative_cech_forget_kernel_finite_of_hone_finite
    {X Y : Scheme.{u}} [IsAffine Y] [IsNoetherianRing Γ(Y, ⊤)]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1))
    (hfinite : letI := actualRelativeCechHOnePolynomialReesModule f I U hU
      Module.Finite (reesAlgebra (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
        (⨁ n : ℕ, actualClosedCechHOne ((I ^ n).comap f).subschemeι
          (fun j => (U j).1))) :
    letI := actualRelativeCechForgetKernelDirectSumModule f I U hU
    Module.Finite (⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (⨁ n : ℕ, ↥(actualRelativeCechForgetKernel f I U n)) := by
  letI := actualRelativeCechForgetKernelGradedModule f I U hU
  letI := actualRelativeCechHOneGradedModule f I U hU
  letI := actualRelativeCechForgetKernelDirectSumModule f I U hU
  letI := actualRelativeCechHOneDirectSumReesModule f I U hU
  letI := actualRelativeCechHOnePolynomialReesModule f I U hU
  let J := I.ideal ⟨⊤, isAffineOpen_top Y⟩
  letI : Module.Finite (reesAlgebra J)
      (⨁ n : ℕ, actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) := hfinite
  letI : Module.Finite (⨁ n : ℕ, ↥(J ^ n))
      (⨁ n : ℕ, actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) :=
    (actualPolynomialReesModule_finite_iff J _).mp hfinite
  letI : IsNoetherianRing (⨁ n : ℕ, ↥(J ^ n)) :=
    isNoetherianRing_of_ringEquiv (reesAlgebra J)
      (actualReesDirectSumAlgEquiv J).symm.toRingEquiv
  apply Module.Finite.of_injective (actualRelativeCechForgetKernelInclusion f I U hU)
  exact actualGradedModuleMap_injective
    (fun n => (actualRelativeCechForgetKernel f I U n).subtype)
    (by intros; rfl) (fun _ => Subtype.val_injective)

#print axioms actual_relative_cech_graded_forget_kernel_preserved
#print axioms actualRelativeCechForgetKernelGradedModule
#print axioms actual_relative_cech_forget_kernel_finite_of_hone_finite
end
end Negativity
