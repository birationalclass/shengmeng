module
public import Negativity.ActualProperCechKernelVanishing
public import Negativity.ActualAffineVarietySections
public import Negativity.RelativeCechFormalComparison
public import Negativity.GlobalClosedFiberConnectedness
public import Negativity.FiniteNormalGeometry

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem: the actual affine-neighborhood closed-fiber formal
function comparisons of a proper birational map over an algebraically
closed field are bijective. Actual cohomology bounds, completion
injectivity and section-kernel bounds are proved internally. -/
theorem actual_proper_birational_closed_fiber_formal_functions
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (k : Type u) [Field k] [IsAlgClosed k]
    (b : Y ⟶ Spec (.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsProper f] (hf : BirationalMorphism f)
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ActualClosedFiberFormalFunctions f := by
  intro U v _hv
  letI : IsAffine U.1 := U.2
  letI : Nonempty U.1 := ⟨v⟩
  haveI : Nonempty (f ⁻¹ᵁ U.1) := by
    obtain ⟨x, hx⟩ := (proper_birational_surjective f hf).surj v.1
    refine ⟨⟨x, ?_⟩⟩
    change f x ∈ U.1
    rw [hx]
    exact v.2
  letI := actualAffineVarietySectionAlgebra k U.1 (U.1.ι ≫ b)
  letI : Algebra.FiniteType k Γ(U.1.toScheme, ⊤) :=
    actual_affine_variety_section_algebra_finite_type k U.1 (U.1.ι ≫ b)
  obtain ⟨ι, hι, V, hcover, c, hc⟩ := actual_proper_affine_cech_kernel_vanishing
    (f ∣_ U.1) (actualClosedPointIdeal U.1 v)
  letI : Fintype ι := hι
  exact actual_relative_formal_functions_bijective_of_cech_kernel_vanishing
    k (f ∣_ U.1) (birationalMorphism_restrict f hf U.1)
    (normalStalks_restrict Y U.1 hnY) (actualClosedPointIdeal U.1 v)
    V (le_of_eq hcover.symm) c hc

#print axioms actual_proper_birational_closed_fiber_formal_functions
end
end Negativity
