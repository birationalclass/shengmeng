module
public import Negativity.ActualRelativeCechHOneReesModule
public import Negativity.GradedModuleMapReuse
public import Negativity.DirectSumKernelReuse

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualClosedCechKernelDifferential {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :
    (actualCechPullbackOne i U).ker →+ actualCechTwo X U :=
  (actualCechBoundary X U).comp (actualCechPullbackOne i U).ker.subtype

def actualClosedCechKernelCycleEquiv {X Z : Scheme.{u}} (i : Z ⟶ X)
    {ι : Type v} (U : ι → X.Opens) :
    (actualClosedCechKernelDifferential i U).ker ≃+
      actualClosedCechCocycles i U where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def actualGradedClosedCechCycleEquiv
    {X : Scheme.{u}} {κ : Type v} {Z : κ → Scheme.{u}}
    (i : ∀ n, Z n ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    (⨁ n, actualClosedCechCocycles (i n) U) ≃+
      (DirectSum.map (fun n => actualClosedCechKernelDifferential (i n) U)).ker :=
  (DirectSum.congrAddEquiv (fun n => (actualClosedCechKernelCycleEquiv (i n) U).symm)).trans
    (actualDirectSumKernelEquiv (fun n => actualClosedCechKernelDifferential (i n) U))

def actualGradedClosedCechQuotientEquiv
    {X : Scheme.{u}} {κ : Type v} {Z : κ → Scheme.{u}}
    (i : ∀ n, Z n ⟶ X) {ι : Type u} (U : ι → X.Opens) :
    (⨁ n, actualClosedCechCocycles (i n) U) ⧸
        (DirectSum.map (fun n => actualClosedCechBoundary (i n) U)).range ≃+
      ⨁ n, actualClosedCechHOne (i n) U :=
  actualDirectSumQuotientEquiv (fun n => actualClosedCechBoundary (i n) U)

/-- The genuine homogeneous cocycle quotient map respects every scalar
in the complete Rees ring. Its action is the actual geometric action. -/
def actualRelativeCechHOneDirectSumQuotientMap
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type u} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    letI := actualRelativeCechOneModule f (fun j => (U j).1)
    letI := actualRelativeCechCycleGradedSMul f I (fun j => (U j).1) hU
    letI := actualRelativeCechHOneGradedModule f I U hU
    (⨁ n, actualRelativeCechCycleModule f I (fun j => (U j).1) n) →ₗ[
      ⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n)]
      (⨁ n, actualClosedCechHOne ((I ^ n).comap f).subschemeι (fun j => (U j).1)) := by
  letI := actualRelativeCechOneModule f (fun j => (U j).1)
  letI := actualRelativeCechCycleGradedSMul f I (fun j => (U j).1) hU
  letI := actualRelativeCechHOneGradedModule f I U hU
  exact actualGradedModuleMap
    (fun n => QuotientAddGroup.mk' (actualClosedCechBoundary
      ((I ^ n).comap f).subschemeι (fun j => (U j).1)).range) (by intros; rfl)

theorem actual_relative_cech_hone_direct_sum_quotient_map_surjective
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type u} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    Function.Surjective (actualRelativeCechHOneDirectSumQuotientMap f I U hU) :=
  actual_direct_sum_quotient_map_surjective (fun n => actualClosedCechBoundary
    ((I ^ n).comap f).subschemeι (fun j => (U j).1))

@[instance_reducible]
def actualRelativeCechCyclePolynomialReesModule
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type u} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    letI := actualRelativeCechOneModule f (fun j => (U j).1)
    Module (reesAlgebra (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
      (⨁ n, actualRelativeCechCycleModule f I (fun j => (U j).1) n) := by
  letI := actualRelativeCechOneModule f (fun j => (U j).1)
  letI := actualRelativeCechCycleGradedSMul f I (fun j => (U j).1) hU
  exact actualPolynomialReesModule _ _

def actualRelativeCechHOnePolynomialQuotientMap
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type u} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    letI := actualRelativeCechOneModule f (fun j => (U j).1)
    letI := actualRelativeCechCyclePolynomialReesModule f I U hU
    letI := actualRelativeCechHOnePolynomialReesModule f I U hU
    (⨁ n, actualRelativeCechCycleModule f I (fun j => (U j).1) n) →ₗ[
      reesAlgebra (I.ideal ⟨⊤, isAffineOpen_top Y⟩)]
      (⨁ n, actualClosedCechHOne ((I ^ n).comap f).subschemeι (fun j => (U j).1)) := by
  letI := actualRelativeCechOneModule f (fun j => (U j).1)
  letI := actualRelativeCechCycleGradedSMul f I (fun j => (U j).1) hU
  letI := actualRelativeCechHOneGradedModule f I U hU
  letI := actualRelativeCechCyclePolynomialReesModule f I U hU
  letI := actualRelativeCechHOnePolynomialReesModule f I U hU
  let q := actualRelativeCechHOneDirectSumQuotientMap f I U hU
  exact { q.toAddMonoidHom with
    map_smul' := fun p x => q.map_smul
      ((actualReesDirectSumAlgEquiv _).symm p) x }

theorem actual_relative_cech_hone_polynomial_quotient_map_surjective
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type u} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    Function.Surjective (actualRelativeCechHOnePolynomialQuotientMap f I U hU) :=
  actual_relative_cech_hone_direct_sum_quotient_map_surjective f I U hU

#print axioms actualGradedClosedCechCycleEquiv
#print axioms actualGradedClosedCechQuotientEquiv
#print axioms actualRelativeCechHOneDirectSumQuotientMap
#print axioms actualRelativeCechHOnePolynomialQuotientMap
end
end Negativity
