module
public import Linear.DiscreteSchemePushforwardOpenProjector
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped BigOperators
universe u
local instance (D : Scheme.{u}) : DecidableEq D := Classical.decEq D
/-- The actual original singleton open,not a point-coordinate model. -/
def discreteSchemePointOpen (D : Scheme.{u}) [DiscreteTopology D] (x : D) : D.Opens :=
  ⟨{x},isOpen_discrete _⟩
/-- Actual original structure-sheaf idempotent selecting a singleton. -/
def discreteSchemePointIdempotent (D : Scheme.{u}) [DiscreteTopology D] (x : D) : Γ(D,⊤) :=
  discreteSchemeOpenIdempotent D (discreteSchemePointOpen D x)
/-- Literal restriction values on every actual original singleton open. -/
theorem discreteSchemePointIdempotent_selector
    (D : Scheme.{u}) [DiscreteTopology D] (x y : D) :
    D.presheaf.map (discreteSchemePointOpen D x).leTop.op
      (discreteSchemePointIdempotent D y) = if x=y then 1 else 0 := by
  classical
  by_cases h : x=y
  · subst y
    simpa [discreteSchemePointIdempotent] using
      discreteSchemeOpenIdempotent_restrict_one D (discreteSchemePointOpen D x)
  · rw [ite_eq_right h]
    apply discreteSchemeOpenIdempotent_restrict_zero_of_le_complement
    intro z hz
    change z=x at hz
    change z ≠ y
    rw [hz]
    exact h
/-- Actual singleton idempotents sum to one on every finite original
scheme with discrete topology. Only sheaf separatedness and actual
restriction values are used;no product decomposition is assumed. -/
theorem discreteSchemePointIdempotent_sum
    (D : Scheme.{u}) [DiscreteTopology D] [Fintype D] :
    (∑ x : D,discreteSchemePointIdempotent D x)=1 := by
  classical
  let cover : D → D.Opens := discreteSchemePointOpen D
  have hcover : (⊤ : D.Opens) ≤ iSup cover := by
    intro x _
    exact (le_iSup cover x) (show x ∈ cover x from rfl)
  apply D.sheaf.eq_of_locally_eq' cover ⊤ (fun x => (cover x).leTop) hcover
  intro x
  change D.presheaf.map (discreteSchemePointOpen D x).leTop.op
    (∑ y : D,discreteSchemePointIdempotent D y)=D.presheaf.map (discreteSchemePointOpen D x).leTop.op 1
  rw [map_sum,map_one]
  simp only [discreteSchemePointIdempotent_selector]
  simp
/-- Distinct actual point idempotents are orthogonal,without requiring
finite source or a supplied residue-coordinate decomposition. -/
theorem discreteSchemePointIdempotent_mul_eq_zero
    (D : Scheme.{u}) [DiscreteTopology D] (x y : D) (hxy : x ≠ y) :
    discreteSchemePointIdempotent D x * discreteSchemePointIdempotent D y=0 := by
  classical
  let cover : D → D.Opens := discreteSchemePointOpen D
  have hcover : (⊤ : D.Opens) ≤ iSup cover := by
    intro z _
    exact (le_iSup cover z) (show z ∈ cover z from rfl)
  apply D.sheaf.eq_of_locally_eq' cover ⊤ (fun z => (cover z).leTop) hcover
  intro z
  change D.presheaf.map (discreteSchemePointOpen D z).leTop.op
    (discreteSchemePointIdempotent D x * discreteSchemePointIdempotent D y)=
      D.presheaf.map (discreteSchemePointOpen D z).leTop.op 0
  rw [map_mul,map_zero,discreteSchemePointIdempotent_selector,discreteSchemePointIdempotent_selector]
  split_ifs <;> simp_all
end LinearStudy
