module
public import Negativity.SchemeClopenIdempotent
public import Negativity.LocalConnectedness
public import Mathlib.AlgebraicGeometry.Fiber

@[expose] public section
namespace Negativity
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A global idempotent on an actual connected scheme is 0 or 1.
This uses the genuine local rings, basic opens and structure-sheaf
separatedness; no affine or reducedness assumption is required. -/
theorem actual_connected_scheme_global_idempotent_trivial
    (Z : Scheme.{u}) [ConnectedSpace Z] (e : Γ(Z, ⊤))
    (he : e * e = e) : e = 0 ∨ e = 1 := by
  classical
  have hg (x : Z) : Z.presheaf.Γgerm x e = 0 ∨ Z.presheaf.Γgerm x e = 1 := by
    apply localRing_idempotent_trivial (Z.presheaf.stalk x)
    exact (map_mul (Z.presheaf.Γgerm x).hom e e).symm.trans
      (congrArg (Z.presheaf.Γgerm x) he)
  have hcompl : (Z.basicOpen e : Set Z)ᶜ = (Z.basicOpen (1 - e) : Set Z) := by
    ext x
    change (¬ x ∈ Z.basicOpen e) ↔ x ∈ Z.basicOpen (1 - e)
    rw [Z.mem_basicOpen_top e x, Z.mem_basicOpen_top (1 - e) x]
    change (¬ IsUnit (Z.presheaf.Γgerm x e)) ↔
      IsUnit (Z.presheaf.Γgerm x (1 - e))
    rcases hg x with hx | hx <;>
      simp [map_sub, map_one, hx]
  have hclopen : IsClopen (Z.basicOpen e : Set Z) := by
    refine ⟨?_, (Z.basicOpen e).isOpen⟩
    exact isOpen_compl_iff.mp (hcompl.symm ▸ (Z.basicOpen (1 - e)).isOpen)
  rcases (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace Z)).2
      (Z.basicOpen e : Set Z) hclopen with hzero | hone
  · left
    apply TopCat.Presheaf.section_ext Z.sheaf ⊤
    intro x _
    change Z.presheaf.Γgerm x e = Z.presheaf.Γgerm x 0
    rw [map_zero]
    rcases hg x with hx | hx
    · exact hx
    · have hu : x ∈ Z.basicOpen e :=
        (Z.mem_basicOpen_top e x).mpr (hx ▸ isUnit_one)
      have hnot : x ∉ (Z.basicOpen e : Set Z) := by rw [hzero]; simp
      exact False.elim (hnot hu)
  · right
    apply TopCat.Presheaf.section_ext Z.sheaf ⊤
    intro x _
    change Z.presheaf.Γgerm x e = Z.presheaf.Γgerm x 1
    rw [map_one]
    rcases hg x with hx | hx
    · have hu : IsUnit (Z.presheaf.Γgerm x e) :=
        (Z.mem_basicOpen_top e x).mp (by
          change x ∈ (Z.basicOpen e : Set Z)
          rw [hone]; trivial)
      rw [hx] at hu
      exact False.elim (not_isUnit_zero hu)
    · exact hx

/-- Once connectedness of the actual fiber has been proved, every actual
fiber idempotent lifts from a genuine global function on X: the lift is
one of the two constants. This supplementary algebraic consequence does
not itself prove the connectedness hypothesis. -/
theorem actual_connected_fiber_idempotent_lifts_from_global
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    [ConnectedSpace (f.fiber y)] (e : Γ(f.fiber y, ⊤))
    (he : e * e = e) :
    ∃ s : Γ(X, ⊤), (f.fiberι y).appTop s = e := by
  rcases actual_connected_scheme_global_idempotent_trivial (f.fiber y) e he with h0 | h1
  · exact ⟨0, (map_zero _).trans h0.symm⟩
  · exact ⟨1, (map_one _).trans h1.symm⟩

#print axioms actual_connected_scheme_global_idempotent_trivial
#print axioms actual_connected_fiber_idempotent_lifts_from_global
end
end Negativity
