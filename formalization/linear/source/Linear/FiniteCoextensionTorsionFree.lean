module
public import Linear.ExtendScalarsActualTensor
public import Mathlib.RingTheory.Algebraic.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Algebra.IsAlgebraic R S]

/-- The actual coextension dual is torsion-free over S. Algebraicity
supplies a nonzero R multiple in bS for each nonzero b; this does not assume
an S-linear embedding or identify the dual with a canonical sheaf. -/
theorem coextension_smul_eq_zero
    (b : S) (ell : (ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))
    (h : b • ell = 0) : b = 0 ∨ ell = 0 := by
  classical
  by_cases hb : b = 0
  · exact Or.inl hb
  right
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro x
  change ell (x : S) = 0
  let l := ModuleCat.CoextendScalars.equiv (algebraMap R S) (ModuleCat.of R R) ell
  obtain ⟨c,d,hd,hxc⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul R (S := S) (x : S) hb
  have hx' : (d • x : (ModuleCat.restrictScalars (algebraMap R S)).obj
      (ModuleCat.of S S)) = (b*c : S) := by
    simpa only [ModuleCat.restrictScalars.smul_def,smul_eq_mul,Algebra.smul_def] using hxc
  have hz : ell (b*c) = 0 := by
    have h' := congrArg (fun z : (ModuleCat.coextendScalars (algebraMap R S)).obj
      (ModuleCat.of R R) => z c) h
    change ell (c*b) = 0 at h'
    simpa only [mul_comm] using h'
  have hdz : d * l x = 0 := by
    calc
      d * l x = l (d • x) := (l.map_smul d x).symm
      _ = l (b*c) := congrArg l hx'
      _ = 0 := hz
  exact (mul_eq_zero.mp hdz).resolve_left hd

end LinearStudy
