module
public import Negativity.ActualRelativeCechCycleModule
public import Negativity.GradedModuleQuotientReuse
public import Negativity.ReesDirectSumCoordinates

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
open scoped DirectSum
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

@[instance_reducible]
def actualRelativeCechHOneGradedSMul {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    GradedMonoid.GSMul
      (fun n : ℕ => ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (fun n : ℕ => actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) where
  smul {m n} r a := actualRelativeCechGradedHOne f I U hU m n r.1 r.2 a

/-- The action descends through the actual boundary quotient in each degree.
Every graded module axiom is inherited from the already proved cocycle action;
no finite-generation or quotient comparison input is assumed. -/
@[instance_reducible]
def actualRelativeCechHOneGradedModule {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    DirectSum.Gmodule
      (fun n : ℕ => ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (fun n : ℕ => actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) := by
  letI := actualRelativeCechOneModule f (fun j => (U j).1)
  letI := actualRelativeCechCycleGradedSMul f I (fun j => (U j).1) hU
  letI := actualRelativeCechHOneGradedSMul f I U hU
  let q (n : ℕ) : actualRelativeCechCycleModule f I (fun j => (U j).1) n →+
      actualClosedCechHOne ((I ^ n).comap f).subschemeι (fun j => (U j).1) :=
    QuotientAddGroup.mk' (actualClosedCechBoundary ((I ^ n).comap f).subschemeι
      (fun j => (U j).1)).range
  refine actualGradedModuleOfSurjective q (fun n => QuotientAddGroup.mk'_surjective _) ?_
  intro m n r a
  rfl

/-- The full summed actual H¹ carries the Rees-ring module structure built
from its geometric pullback and restriction maps. -/
@[instance_reducible]
def actualRelativeCechHOneDirectSumReesModule {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    Module (⨁ n : ℕ, ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (⨁ n : ℕ, actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) := by
  letI := actualRelativeCechHOneGradedModule f I U hU
  infer_instance

/-- The same genuine action in polynomial Rees coordinates. -/
@[instance_reducible]
def actualRelativeCechHOnePolynomialReesModule {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) :
    Module (reesAlgebra (I.ideal ⟨⊤, isAffineOpen_top Y⟩))
      (⨁ n : ℕ, actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) := by
  letI := actualRelativeCechHOneDirectSumReesModule f I U hU
  exact actualPolynomialReesModule _ _

theorem actual_relative_cech_hone_rees_module_homogeneous_smul
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) {ι : Type v} (U : ι → X.affineOpens)
    (hU : ∀ j k, IsAffineOpen ((U j).1 ⊓ (U k).1)) (m n : ℕ)
    (r : ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ m))
    (a : actualClosedCechHOne ((I ^ n).comap f).subschemeι (fun j => (U j).1)) :
    letI := actualRelativeCechHOnePolynomialReesModule f I U hU
    actualReesPowerMonomial (I.ideal ⟨⊤, isAffineOpen_top Y⟩) m r •
        DirectSum.of (fun n : ℕ => actualClosedCechHOne ((I ^ n).comap f).subschemeι
          (fun j => (U j).1)) n a =
      DirectSum.of (fun n : ℕ => actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) (m + n)
        (actualRelativeCechGradedHOne f I U hU m n r.1 r.2 a) := by
  letI := actualRelativeCechHOneGradedModule f I U hU
  letI := actualRelativeCechHOneDirectSumReesModule f I U hU
  letI := actualRelativeCechHOnePolynomialReesModule f I U hU
  rw [actualPolynomialReesModule_monomial_smul]
  have hact : GradedMonoid.GSMul.smul
      (A := fun n : ℕ => ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (M := fun n : ℕ => actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) r a =
      actualRelativeCechGradedHOne f I U hU m n r.1 r.2 a := by
    rfl
  simpa only [DirectSum.lof_eq_of, vadd_eq_add, hact] using
    (DirectSum.Gmodule.of_smul_of
      (fun n : ℕ => ↥((I.ideal ⟨⊤, isAffineOpen_top Y⟩) ^ n))
      (fun n : ℕ => actualClosedCechHOne ((I ^ n).comap f).subschemeι
        (fun j => (U j).1)) r a)

#print axioms actualRelativeCechHOneDirectSumReesModule
#print axioms actualRelativeCechHOnePolynomialReesModule
#print axioms actual_relative_cech_hone_rees_module_homogeneous_smul
end
end Negativity
