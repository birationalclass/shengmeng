module
public import Linear.SchemeModuleLocalHomPrecompose
public import Linear.SchemeModuleInternalHomCoefficientFunctor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}} {P Q : X.Modules}

/-- A GENUINE LOCAL source frame induces actual INTERNAL Hom iso on
that SAME original open;no global source frame is assumed. -/
def schemeModuleLocalHomSourceIso (U : X.Opens) (e : P.over U ≅ Q.over U)
    (N : X.Modules) :
    (schemeModuleHomModuleSheaf P N).over U ≅
      (schemeModuleHomModuleSheaf Q N).over U where
  hom := schemeModuleLocalHomPrecompose U e.inv
  inv := schemeModuleLocalHomPrecompose U e.hom
  hom_inv_id := by
    rw [← schemeModuleLocalHomPrecompose_comp,e.hom_inv_id,
      schemeModuleLocalHomPrecompose_id]
  inv_hom_id := by
    rw [← schemeModuleLocalHomPrecompose_comp,e.inv_hom_id,
      schemeModuleLocalHomPrecompose_id]

/-- SAME LOCAL frame comparison is natural in EVERY actual coefficient. -/
def schemeModuleLocalHomCoefficientIso (U : X.Opens) (e : P.over U ≅ Q.over U) :
    schemeModuleInternalHomCoefficientFunctor X P ⋙ SheafOfModules.overFunctor X.ringCatSheaf U ≅
      schemeModuleInternalHomCoefficientFunctor X Q ⋙ SheafOfModules.overFunctor X.ringCatSheaf U :=
  NatIso.ofComponents (schemeModuleLocalHomSourceIso U e) (by
    intro M N c
    apply SheafOfModules.hom_ext
    ext W f
    apply Subtype.ext
    change (_ : (Over.forget W.unop.left).op ⋙ Q.presheaf ⟶
      (Over.forget W.unop.left).op ⋙ N.presheaf) = _
    ext T x
    rfl)

end LinearStudy
