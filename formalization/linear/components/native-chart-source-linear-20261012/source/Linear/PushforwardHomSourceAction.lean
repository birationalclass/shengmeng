module
public import Linear.SchemeModuleHomPrecomposeComparison
public import Linear.OriginalGlobalModuleScalar
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

/-- A source section acts on the actual original internal Hom by
precomposition with its restrictions on every original subopen. -/
def schemePushforwardHomSourceActionSection (f : X ⟶ Y) (N : Y.Modules)
    (U : Y.Opens) (b : Γ(X,f ⁻¹ᵁ U))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) N,U) := by
  let P := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  let t : (presheafHom P.presheaf N.presheaf).obj (op U) := {
    app W := AddCommGrpCat.ofHom {
      toFun := fun x => h.val.app W
        (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b *
          (show Γ(X,f ⁻¹ᵁ W.unop.left) from x))
      map_zero' := by
        change h.val.app W
          (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b *
            (0 : Γ(X,f ⁻¹ᵁ W.unop.left))) = 0
        rw [mul_zero,map_zero]
      map_add' x y := by
        change h.val.app W
          (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b *
            ((show Γ(X,f ⁻¹ᵁ W.unop.left) from x) + (show Γ(X,f ⁻¹ᵁ W.unop.left) from y))) = _
        rw [mul_add,map_add] }
    naturality W Z i := by
      ext x
      have hf := congr($(h.val.naturality i)
        (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b *
          (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)))
      change h.val.app Z
        (X.presheaf.map ((Opens.map f.base).map Z.unop.hom).op b *
          X.presheaf.map ((Opens.map f.base).map i.unop.left).op
            (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)) =
        N.presheaf.map i.unop.left.op (h.val.app W
          (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b *
            (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)))
      change h.val.app Z
        (X.presheaf.map ((Opens.map f.base).map i.unop.left).op
          (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b *
            (show Γ(X,f ⁻¹ᵁ W.unop.left) from x))) =
        N.presheaf.map i.unop.left.op (h.val.app W
          (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b *
            (show Γ(X,f ⁻¹ᵁ W.unop.left) from x))) at hf
      rw [← hf]
      congr 1
      symm
      rw [map_mul]
      congr 1
      have he : X.presheaf.map ((Opens.map f.base).map W.unop.hom).op ≫
          X.presheaf.map ((Opens.map f.base).map i.unop.left).op =
          X.presheaf.map ((Opens.map f.base).map Z.unop.hom).op := by
        rw [← X.presheaf.map_comp,← op_comp,← Functor.map_comp,i.unop.w]
      exact congr($(he) b) }
  refine ⟨t,?_⟩
  intro W r x
  change h.val.app W
    (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b *
      (f.app W.unop.left r * (show Γ(X,f ⁻¹ᵁ W.unop.left) from x))) =
    r • (show Γ(N,W.unop.left) from h.val.app W
      (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b * (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)))
  rw [← mul_assoc,mul_comm _ (f.app W.unop.left r),mul_assoc]
  exact h.property W r _

theorem schemePushforwardHomSourceActionSection_evaluation
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (b : Γ(X,f ⁻¹ᵁ U))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) N,U))
    (W : (Over U)ᵒᵖ) (x : Γ(X,f ⁻¹ᵁ W.unop.left)) :
    (schemePushforwardHomSourceActionSection f N U b h).val.app W x =
      h.val.app W
        (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b * x) := rfl

theorem schemePushforwardHomSourceActionSection_one
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    schemePushforwardHomSourceActionSection f N U 1 h = h := by
  apply Subtype.ext
  change (_ : (Over.forget U).op ⋙ _ ⟶ (Over.forget U).op ⋙ _) = _
  ext W x
  change h.val.app W (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op 1 * (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)) = h.val.app W x
  rw [map_one,one_mul]

theorem schemePushforwardHomSourceActionSection_mul
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (b c : Γ(X,f ⁻¹ᵁ U))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    schemePushforwardHomSourceActionSection f N U (b*c) h =
      schemePushforwardHomSourceActionSection f N U b
        (schemePushforwardHomSourceActionSection f N U c h) := by
  apply Subtype.ext
  change (_ : (Over.forget U).op ⋙ _ ⟶ (Over.forget U).op ⋙ _) = _
  ext W x
  change h.val.app W (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op (b*c) * (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)) =
    h.val.app W (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op c * (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b * (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)))
  rw [map_mul (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op).hom b c]
  congr 1
  ac_rfl

theorem schemePushforwardHomSourceActionSection_add
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (b c : Γ(X,f ⁻¹ᵁ U))
    (h : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    schemePushforwardHomSourceActionSection f N U (b+c) h =
      schemePushforwardHomSourceActionSection f N U b h +
        schemePushforwardHomSourceActionSection f N U c h := by
  apply Subtype.ext
  change (_ : (Over.forget U).op ⋙ _ ⟶ (Over.forget U).op ⋙ _) = _
  ext W x
  change h.val.app W (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op (b+c) * (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)) =
    h.val.app W (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op b * (show Γ(X,f ⁻¹ᵁ W.unop.left) from x)) + h.val.app W (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op c * (show Γ(X,f ⁻¹ᵁ W.unop.left) from x))
  rw [map_add (X.presheaf.map ((Opens.map f.base).map W.unop.hom).op).hom b c,add_mul,map_add]

theorem schemePushforwardHomSourceActionSection_map_add
    (f : X ⟶ Y) (N : Y.Modules) (U : Y.Opens)
    (b : Γ(X,f ⁻¹ᵁ U))
    (h k : Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward f).obj
        (SheafOfModules.unit X.ringCatSheaf)) N,U)) :
    schemePushforwardHomSourceActionSection f N U b (h+k) =
      schemePushforwardHomSourceActionSection f N U b h +
        schemePushforwardHomSourceActionSection f N U b k := by
  apply Subtype.ext
  change (_ : (Over.forget U).op ⋙ _ ⟶ (Over.forget U).op ⋙ _) = _
  ext W x
  rfl

end LinearStudy
