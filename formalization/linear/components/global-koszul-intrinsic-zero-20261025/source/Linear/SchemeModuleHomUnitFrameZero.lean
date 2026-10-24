module
public import Linear.SchemeModuleHomTransportIso
public import Linear.SchemeModuleUnitHomIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v w
variable {X : Scheme.{u}}
/-- ORIGINAL unit currying followed by the ACTUAL unit-Hom evaluation
returns the SAME original morphism. -/
theorem schemeModuleUnitHomIso_curry {N : X.Modules}
    (a : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    (schemeModuleHomUnitAddEquiv _ N).symm a ≫ (schemeModuleUnitHomIso N).hom=a := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  let x : Γ(X,U.unop) := r
  change X.presheaf.map (𝟙 U.unop).op x •
    (show Γ(N,U.unop) from a.val.app U (1 : Γ(X,U.unop)))=a.val.app U x
  simp only [op_id]
  rw [X.presheaf.map_id]
  change x • (show Γ(N,U.unop) from a.val.app U (1 : Γ(X,U.unop)))=a.val.app U x
  have h := (a.val.app U).hom.map_smul x (1 : Γ(X,U.unop))
  simpa only [smul_eq_mul,mul_one] using h.symm
attribute [local irreducible] schemeModuleHomUnitAddEquiv schemeModuleUnitHomIso
/-- An ACTUAL source line frame gives an ACTUAL internal-Hom isomorphism
without choosing or assuming any frame of the target coefficient. -/
def schemeModuleLineFrameHomIso {P N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ≅ P) :
    schemeModuleHomModuleSheaf P N ≅ N :=
  (schemeModuleInternalHomFunctor X N).mapIso s.op ≪≫ schemeModuleUnitHomIso N
theorem schemeModuleLineFrameHomIso_hom {P N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ≅ P) :
    (schemeModuleLineFrameHomIso (N:=N) s).hom=
      schemeModuleHomPrecompose (N:=N) s.hom ≫ (schemeModuleUnitHomIso N).hom := rfl
attribute [local irreducible] schemeModuleLineFrameHomIso
/-- The isomorphism retains the SAME original coefficient morphism. -/
theorem schemeModuleLineFrameHomIso_curry {P N : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ≅ P) (a : P ⟶ N) :
    (schemeModuleHomUnitAddEquiv P N).symm a ≫ (schemeModuleLineFrameHomIso (N:=N) s).hom=
      s.hom ≫ a := by
  rw [schemeModuleLineFrameHomIso_hom,← Category.assoc,
    ← schemeModuleHomUnitAddEquiv_symm_precompose]
  exact schemeModuleUnitHomIso_curry (s.hom ≫ a)
/-- Vanishing after ANY original zero-preserving functor is independent
of the source line frame. In particular,this applies to the ACTUAL
scheme pullback to the cut;faithful pullback is NOT assumed. -/
theorem schemeModuleLineFrame_curry_map_zero_iff
    {A : Type v} [Category.{w} A] [HasZeroMorphisms A]
    (F : X.Modules ⥤ A) [F.PreservesZeroMorphisms]
    {P N : X.Modules} (s : SheafOfModules.unit X.ringCatSheaf ≅ P) (a : P ⟶ N) :
    F.map ((schemeModuleHomUnitAddEquiv P N).symm a)=0 ↔ F.map a=0 := by
  have hh := congrArg (fun b => F.map b) (schemeModuleLineFrameHomIso_curry s a)
  rw [F.map_comp,F.map_comp] at hh
  constructor
  · intro hz
    apply (cancel_epi (F.map s.hom)).mp
    rw [← hh,hz,zero_comp,comp_zero]
  · intro hz
    apply (cancel_mono (F.map (schemeModuleLineFrameHomIso (N:=N) s).hom)).mp
    rw [hh,hz,comp_zero,zero_comp]
end LinearStudy
