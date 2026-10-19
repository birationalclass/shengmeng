module
public import Linear.SchemeModuleLocalInternalExtIso
public import Linear.SchemeModuleFreeOverIso
public import Linear.SchemeModuleFiniteFreeInternalExt
public import Linear.SchemeModuleZeroFromOpenCover
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- GENUINE finite-free frame on SAME original U DERIVES vanishing of
ACTUAL higher SHEAF Ext after restriction. No local Ext-vanishing input. -/
theorem schemeModuleLocalFiniteFreeInternalExt_succ (P N : X.Modules)
    (U : X.Opens) (ι : Type u) [Finite ι]
    (e : P.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) ι) (q : ℕ) :
    IsZero ((schemeModuleInternalExt P N (q+1)).over U) := by
  letI := schemeModuleOverFunctor_additive X U
  let e' := e ≪≫ (schemeModuleFreeOverIso U ι).symm
  exact IsZero.of_iso
    ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).map_isZero
      (schemeModuleFiniteFreeInternalExt_succ N ι q))
    (schemeModuleLocalInternalExtSourceIso U e' N (q+1) (injectiveResolution N))

/-- Positive ACTUAL SHEAF Ext vanishes for an actual finite locally free
source given genuine native finite frames on a COVER of ORIGINAL opens.
Both local vanishing and gluing are PROVED,not additional premises. -/
theorem schemeModuleFiniteLocallyFreeInternalExt_succ_of_cover (P N : X.Modules)
    {κ : Type u} (U : κ → X.Opens) (hcover : iSup U = ⊤)
    (ι : κ → Type u) [∀ i, Finite (ι i)]
    (e : ∀ i, P.over (U i) ≅
      SheafOfModules.free (R := X.ringCatSheaf.over (U i)) (ι i)) (q : ℕ) :
    IsZero (schemeModuleInternalExt P N (q+1)) :=
  schemeModule_isZero_of_over_cover _ U hcover
    (fun i => schemeModuleLocalFiniteFreeInternalExt_succ P N (U i) (ι i) (e i) q)

end LinearStudy
