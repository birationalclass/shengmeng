module
public import Linear.PushforwardHomSourceAction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 80000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

theorem schemePushforwardHomSourceActionSection_zero
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    schemePushforwardHomSourceActionSection f N U 0 h = 0 := by
  apply Subtype.ext
  change (_ : (Over.forget U).op ⋙ _ ⟶ (Over.forget U).op ⋙ _) = _
  ext W x
  change h.val.app W (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op 0 *
    (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)) = 0
  rw [map_zero,zero_mul,map_zero]

theorem schemePushforwardHomSourceActionSection_map_zero
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens) (b : Γ(X,f ⁻¹ᵁ U)) :
    schemePushforwardHomSourceActionSection f N U b 0 = 0 := by
  apply Subtype.ext
  change (_ : (Over.forget U).op ⋙ _ ⟶ (Over.forget U).op ⋙ _) = _
  ext W x
  rfl

/-- Let U be an ORIGINAL base open. Then the ORIGINAL internal Hom
sections form a module over the ACTUAL source functions on f^-1(U).
This is a constructed module structure, not a scalar-compatibility input. -/
@[instance_reducible] def schemePushforwardHomSourceModule (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens) :
    letI : SMul (Γ(X,f ⁻¹ᵁ U))
      (Γ(schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U)) :=
      ⟨schemePushforwardHomSourceActionSection f N U⟩
    Module (Γ(X,f ⁻¹ᵁ U))
      (Γ(schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U)) := by
  letI : SMul (Γ(X,f ⁻¹ᵁ U))
      (Γ(schemeModuleHomModuleSheaf
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U)) :=
      ⟨schemePushforwardHomSourceActionSection f N U⟩
  exact {
    one_smul := schemePushforwardHomSourceActionSection_one f N U
    mul_smul := schemePushforwardHomSourceActionSection_mul f N U
    smul_zero := schemePushforwardHomSourceActionSection_map_zero f N U
    smul_add := schemePushforwardHomSourceActionSection_map_add f N U
    add_smul := schemePushforwardHomSourceActionSection_add f N U
    zero_smul := schemePushforwardHomSourceActionSection_zero f N U }

/-- The source action induced by an actual pulled-back base function is
the SAME original O_Y-linear scalar action on the internal Hom. -/
theorem schemePushforwardHomSourceActionSection_base_smul
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens) (r : Γ(Y,U))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    schemePushforwardHomSourceActionSection f N U (f.app U r) h = r • h := by
  apply Subtype.ext
  change (_ : (Over.forget U).op ⋙ _ ⟶ (Over.forget U).op ⋙ _) = _
  ext W x
  change h.val.app W
      (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op (f.app U r) *
        (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)) =
    Y.presheaf.map W.unop.hom.op r •
      (show Γ(N,W.unop.left) from h.val.app W x)
  have hn := congr($(f.naturality W.unop.hom.op) r)
  change f.app W.unop.left (Y.presheaf.map W.unop.hom.op r) =
    X.presheaf.map ((Opens.map f.base).map W.unop.hom).op (f.app U r) at hn
  rw [← hn]
  exact h.property W (Y.presheaf.map W.unop.hom.op r) x

/-- The source action respects the ACTUAL original restrictions of the
Hom sheaf and source structure sheaf on every pair of original opens. -/
theorem schemePushforwardHomSourceActionSection_restrict
    (f : X ⟶ Y) (N : Y.Modules) {U V : Y.Opens} (i : V ⟶ U)
    (b : Γ(X,f ⁻¹ᵁ U))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    let H := schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) N
    H.presheaf.map i.op (schemePushforwardHomSourceActionSection f N U b h) =
      schemePushforwardHomSourceActionSection f N V
        (X.presheaf.map ((Opens.map f.base).map i).op b) (H.presheaf.map i.op h) := by
  dsimp only
  apply Subtype.ext
  change (_ : (Over.forget V).op ⋙ _ ⟶ (Over.forget V).op ⋙ _) = _
  ext W x
  change h.val.app (op (Over.mk (W.unop.hom ≫ i)))
      (X.presheaf.map ((Opens.map f.base).map (W.unop.hom ≫ i)).op b *
        (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)) =
    h.val.app (op (Over.mk (W.unop.hom ≫ i)))
      (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op
        (X.presheaf.map ((Opens.map f.base).map i).op b) *
        (show Γ(X,f ⁻¹ᵁ W.unop.left) from x))
  congr 1
  congr 1
  rw [Functor.map_comp,op_comp,X.presheaf.map_comp]
  rfl

end LinearStudy
