module
public import Linear.SchemeModuleCanonicalGlobalToInternalExt
public import Linear.NativeExtUniverseTransport
public import Linear.ChainExplicitTopExtNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
universe u
variable {X : Scheme.{u}}

/-- SAME original standard derived roof,transported by native universe
equivalence into the native small Ext of actual scheme modules. Retain
original complex,augmentation,quasiiso and top functional. -/
def schemeModuleOriginalChainTopExtClassSmall (C : ChainComplex X.Modules ℕ)
    {E M : X.Modules} (r : ℕ) (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
    (hAlpha : QuasiIso alpha) (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0) :
    Ext.{u} E M r := by
  letI : HasExt.{u+1} X.Modules := HasExt.standard X.Modules
  exact nativeExtUniverseEquiv.{u+1,u,u+1,u} E M r
    (originalChainExplicitStandardTopExtClass C r alpha hAlpha a ha)

/-- SAME original standard class retains actual coefficient pushforward
after native universe transport. No desired class equality is input. -/
theorem schemeModuleOriginalChainTopExtClassSmall_comp_mk₀ (C : ChainComplex X.Modules ℕ)
    {E M N : X.Modules} (r : ℕ) (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
    (hAlpha : QuasiIso alpha) (a : C.X r ⟶ M) (ha : C.d (r+1) r ≫ a = 0)
    (g : M ⟶ N) :
    (schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha a ha).comp
        (Ext.mk₀ g) (add_zero _) =
      schemeModuleOriginalChainTopExtClassSmall C r alpha hAlpha (a ≫ g)
        (by simp [reassoc_of% ha]) := by
  letI : HasExt.{u+1} X.Modules := HasExt.standard X.Modules
  unfold schemeModuleOriginalChainTopExtClassSmall
  have hmk : (nativeExtUniverseEquiv.{u+1,u,u+1,u} M N 0 (Ext.mk₀ g : Ext.{u+1} M N 0) :
      Ext.{u} M N 0) = Ext.mk₀.{u,u,u+1} g := nativeExtUniverseEquiv_mk₀.{u+1,u,u+1,u} g
  rw [← hmk]
  rw [← nativeExtUniverseEquiv_comp]
  rw [originalChainExplicitStandardTopExtClass_comp_mk₀]

/-- The ACTUAL global-to-local map applied to SAME original coefficient
pushforward class is the original class followed by the ACTUAL SHEAF
Ext coefficient map. This does NOT compute Koszul SHEAF Ext or restriction. -/
theorem schemeModuleOriginalChainClass_globalToLocal_coefficient
    (C : ChainComplex X.Modules ℕ) {E M N : X.Modules} (n : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (a : C.X (n+1) ⟶ M) (ha : C.d (n+1+1) (n+1) ≫ a = 0) (g : M ⟶ N) :
    schemeModuleGlobalToInternalExt E N n
        (schemeModuleOriginalChainTopExtClassSmall C (n+1) alpha hAlpha (a ≫ g)
          (by simp [reassoc_of% ha])) =
      schemeModuleGlobalToInternalExt E M n
        (schemeModuleOriginalChainTopExtClassSmall C (n+1) alpha hAlpha a ha) ≫
          (schemeModuleInternalExtFunctor E (n+1)).map g := by
  rw [← schemeModuleOriginalChainTopExtClassSmall_comp_mk₀]
  exact schemeModuleGlobalToInternalExt_naturality E g n _

end LinearStudy
