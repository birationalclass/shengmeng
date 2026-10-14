module
public import Linear.FinitePiDualEquiv
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
variable {R : Type*} [CommRing R] {I : Type} [Fintype I]

/-- The actual chosen ModuleCat biproduct comparison sends each element
into its original projection coordinates. -/
theorem finiteBiproductCoordinate_apply (f : I → ModuleCat R) (x : (⨁ f : ModuleCat R)) (i : I) :
    ((ModuleCat.biproductIsoPi f).hom x) i = (biproduct.π f i) x := by
  have hp := (ModuleCat.biproductIsoPi f).inv_comp_eq.mp
    (ModuleCat.biproductIsoPi_inv_comp_π f i)
  exact (congrArg (fun h => h x) hp).symm

variable [DecidableEq I]

/-- Its original categorical inclusion is the actual original Pi.single
inclusion,not an independently specified coordinate map. -/
theorem finiteBiproductCoordinate_ι (f : I → ModuleCat R) (i : I) (x : f i) :
    (ModuleCat.biproductIsoPi f).hom ((biproduct.ι f i) x) = Pi.single i x := by
  funext j
  rw [finiteBiproductCoordinate_apply]
  by_cases h : i = j
  · subst j
    rw [Pi.single_eq_same]
    change ((biproduct.ι f i ≫ biproduct.π f i) x) = x
    rw [biproduct.ι_π_self]
    rfl
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    change ((biproduct.ι f i ≫ biproduct.π f j) x) = 0
    rw [biproduct.ι_π_ne f h]
    rfl

/-- Assemble the ACTUAL finite categorical sum of component duals into
the dual of the original coefficient tuple module. -/
def finiteBiproductDualIso (f : I → ModuleCat R) :
    (⨁ fun i => ModuleCat.of R (Module.Dual R (f i))) ≅
      ModuleCat.of R (Module.Dual R (∀ i, f i)) :=
  (ModuleCat.biproductIsoPi (fun i => ModuleCat.of R (Module.Dual R (f i)))).trans
    (finitePiDualEquiv (fun i => f i)).toModuleIso

/-- The constructed dual assembly respects each original categorical
inclusion and its original coordinate pairing. -/
theorem finiteBiproductDualIso_ι_apply (f : I → ModuleCat R) (i : I)
    (φ : Module.Dual R (f i)) (x : ∀ i, f i) :
    (finiteBiproductDualIso f).hom
      ((biproduct.ι (fun i => ModuleCat.of R (Module.Dual R (f i))) i) φ) x = φ (x i) := by
  change finitePiDualEquiv (fun i => f i)
    ((ModuleCat.biproductIsoPi (fun i => ModuleCat.of R (Module.Dual R (f i)))).hom
      ((biproduct.ι (fun i => ModuleCat.of R (Module.Dual R (f i))) i) φ)) x = φ (x i)
  rw [finiteBiproductCoordinate_ι,finitePiDualEquiv_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j hj hji
    rw [Pi.single_eq_of_ne hji]
    rfl
  · simp

end LinearStudy
