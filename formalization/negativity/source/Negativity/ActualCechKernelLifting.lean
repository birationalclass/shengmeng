module

public import Negativity.ActualCechCohomologyExact
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Final theorem, explicitly conditional: the actual first-cohomology
kernel transition bound yields actual section lifting. The connecting
homomorphism, its exactness and transition naturality are all proved;
the stated kernel bound must still be established by proper cohomology
finite generation in the eventual uniform application. -/
theorem actual_closed_cech_lifting_of_cohomology_kernel_bound
    {X Z W : Scheme.{u}} (j : W ⟶ Z) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j]
    {ι : Type v} (U : ι → X.affineOpens)
    (hU : (⊤ : X.Opens) ≤ iSup (fun k => (U k).1))
    (hkill : ∀ q : actualClosedCechHOne i (fun k => (U k).1),
      actualClosedCechForget i (fun k => (U k).1) q = 0 →
        actualClosedCechHOneTransition j i (fun k => (U k).1) q = 0)
    (b : Γ(Z, ⊤)) :
    ∃ s : Γ(X, ⊤), (j ≫ i).appTop s = j.appTop b := by
  have hq : actualClosedCechForget i (fun k => (U k).1)
      (actualClosedCechConnecting i U b) = 0 :=
    (actual_closed_cech_cohomology_exact i U hU).le ⟨b, rfl⟩
  have hz := hkill (actualClosedCechConnecting i U b) hq
  rw [actual_closed_cech_connecting_naturality] at hz
  exact (actual_closed_cech_obstruction_zero_iff (j ≫ i) U hU (j.appTop b)).mp hz

end
end Negativity
