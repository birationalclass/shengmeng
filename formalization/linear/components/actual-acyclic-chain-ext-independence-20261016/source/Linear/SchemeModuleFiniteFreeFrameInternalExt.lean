module
public import Linear.SchemeModuleFiniteFreeInternalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- An ACTUAL source isomorphism acts on derived SHEAF Ext by the
SAME original inverse source map. Avoid reducing opposite-functor isos. -/
def schemeModuleInternalExtSourceIso {P Q : X.Modules} (e : P ≅ Q)
    (N : X.Modules) (q : ℕ) :
    schemeModuleInternalExt P N q ≅ schemeModuleInternalExt Q N q where
  hom := schemeModuleInternalExtSourceMap e.inv N q
  inv := schemeModuleInternalExtSourceMap e.hom N q
  hom_inv_id := by
    rw [← schemeModuleInternalExtSourceMap_comp,e.hom_inv_id,
      schemeModuleInternalExtSourceMap_id]
  inv_hom_id := by
    rw [← schemeModuleInternalExtSourceMap_comp,e.inv_hom_id,
      schemeModuleInternalExtSourceMap_id]

/-- Any ACTUAL finite-free frame transfers positive derived SHEAF Ext
vanishing to the SAME actual source P. The supplied frame is a genuine
module-sheaf isomorphism,not the desired Ext comparison or vanishing. -/
theorem schemeModuleFiniteFreeFrameInternalExt_succ (N : X.Modules)
    (ι : Type u) [Finite ι] {P : X.Modules}
    (e : P ≅ SheafOfModules.free (R := X.ringCatSheaf) ι) (q : ℕ) :
    IsZero (schemeModuleInternalExt P N (q+1)) :=
  IsZero.of_iso (schemeModuleFiniteFreeInternalExt_succ N ι q)
    (schemeModuleInternalExtSourceIso e N (q+1))

end LinearStudy
