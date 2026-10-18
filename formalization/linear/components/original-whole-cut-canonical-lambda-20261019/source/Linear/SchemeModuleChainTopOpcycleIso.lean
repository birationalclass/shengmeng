module
public import Linear.SchemeModuleChainOpcycleSequence
public import Linear.SchemeModuleHomPrecompose
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- With actual next term ZERO,SAME original quotient projection identifies
top source with its actual opcycles. Native cokernel universal property. -/
def schemeModuleChainTopOpcycleIso (K : ChainComplex X.Modules ℕ) (p : ℕ)
    (hAbove : IsZero (K.X (p+1))) : K.X p ≅ K.opcycles p := by
  letI : IsIso (K.pOpcycles p) := CokernelCofork.IsColimit.isIso_π
    (CokernelCofork.ofπ (K.pOpcycles p) (K.d_pOpcycles (p+1) p))
    (K.opcyclesIsCokernel (p+1) p (by simp))
    (hAbove.eq_of_src (K.d (p+1) p) 0)
  exact asIso (K.pOpcycles p)

/-- Actual original Hom source iso with SAME precomposition maps. -/
def schemeModuleHomSourceIso {P Q : X.Modules} (e : P ≅ Q) (N : X.Modules) :
    schemeModuleHomModuleSheaf P N ≅ schemeModuleHomModuleSheaf Q N where
  hom := schemeModuleHomPrecompose e.inv
  inv := schemeModuleHomPrecompose e.hom
  hom_inv_id := by rw [← schemeModuleHomPrecompose_comp,e.hom_inv_id,schemeModuleHomPrecompose_id]
  inv_hom_id := by rw [← schemeModuleHomPrecompose_comp,e.inv_hom_id,schemeModuleHomPrecompose_id]

/-- Last ACTUAL opcycles-Hom cokernel is SAME original differential-Hom
cokernel,by SAME top quotient projection. -/
def schemeModuleChainTopHomCokernelIso (K : ChainComplex X.Modules ℕ) (N : X.Modules)
    (p : ℕ) (hAbove : IsZero (K.X (p+2))) :
    cokernel (schemeModuleHomPrecompose (N := N) (K.fromOpcycles (p+1) p)) ≅
      cokernel (schemeModuleHomPrecompose (N := N) (K.d (p+1) p)) :=
  cokernel.mapIso _ _ (Iso.refl _)
    (schemeModuleHomSourceIso (schemeModuleChainTopOpcycleIso K (p+1) hAbove).symm N) (by
      change schemeModuleHomPrecompose (N := N) (K.fromOpcycles (p+1) p) ≫
          schemeModuleHomPrecompose (K.pOpcycles (p+1)) =
        𝟙 _ ≫ schemeModuleHomPrecompose (K.d (p+1) p)
      rw [← schemeModuleHomPrecompose_comp,K.p_fromOpcycles,Category.id_comp])

/-- SAME original top quotient projection is retained by cokernel comparison. -/
theorem schemeModuleChainTopHomCokernelIso_hom (K : ChainComplex X.Modules ℕ)
    (N : X.Modules) (p : ℕ) (hAbove : IsZero (K.X (p+2))) :
    cokernel.π (schemeModuleHomPrecompose (N := N) (K.fromOpcycles (p+1) p)) ≫
        (schemeModuleChainTopHomCokernelIso K N p hAbove).hom =
      schemeModuleHomPrecompose (N := N) (K.pOpcycles (p+1)) ≫
        cokernel.π (schemeModuleHomPrecompose (N := N) (K.d (p+1) p)) := by
  dsimp only [schemeModuleChainTopHomCokernelIso]
  erw [cokernel.mapIso_hom,cokernel.π_desc]
  rfl

end LinearStudy
