module
public import Linear.SchemeModuleOriginalActualSectionBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
/-- Actual global sections of the SAME native pushforward are actual
sections of the ORIGINAL sheaf, via the actual inverse image of top. -/
def schemeModulePushforwardGlobalSectionsAddEquiv {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : X.Modules) :
    Γ((Scheme.Modules.pushforward f).obj M,⊤) ≃+ Γ(M,⊤) :=
  Iso.addCommGroupIsoToAddEquiv
    (M.presheaf.mapIso (eqToIso (show f ⁻¹ᵁ ⊤ = (⊤ : X.Opens) from by simp)).op).symm
/-- This identification retains the original coefficient map on EVERY
actual global section. No section-comparison certificate is an input. -/
theorem schemeModulePushforwardGlobalSectionsAddEquiv_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M N : X.Modules} (g : M ⟶ N)
    (s : Γ((Scheme.Modules.pushforward f).obj M,⊤)) :
    schemeModulePushforwardGlobalSectionsAddEquiv f N
      (((Scheme.Modules.pushforward f).map g).app ⊤ s) =
      g.app ⊤ (schemeModulePushforwardGlobalSectionsAddEquiv f M s) := by
  let h : f ⁻¹ᵁ ⊤ = (⊤ : X.Opens) := by simp
  change N.presheaf.map (eqToHom h.symm).op (g.app (f ⁻¹ᵁ ⊤) s) =
    g.app ⊤ (M.presheaf.map (eqToHom h.symm).op s)
  exact (ConcreteCategory.congr_hom
    (g.mapPresheaf.naturality (eqToHom h.symm).op) s).symm
/-- An actual native module-sheaf isomorphism gives its actual additive
section equivalence, by the same original component maps. -/
def schemeModuleIsoGlobalSectionsAddEquiv {X : Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) : Γ(M,⊤) ≃+ Γ(N,⊤) where
  toFun := e.hom.app ⊤
  invFun := e.inv.app ⊤
  left_inv s := congrArg (fun g : M ⟶ M => g.app ⊤ s) e.hom_inv_id
  right_inv s := congrArg (fun g : N ⟶ N => g.app ⊤ s) e.inv_hom_id
  map_add' s t := map_add (e.hom.app ⊤).hom s t
/-- Transport ONLY the source of the ACTUAL augmentation through a proved
zero-term isomorphism. Its kernel/image law is preserved,section by section. -/
theorem schemeModuleActualSectionBoundary_kernel_of_zeroIso {X : Scheme.{u}}
    {A B E M : X.Modules} {n : ℕ} (a : A ⟶ E) (e : A ≅ B)
    (epsilon : CategoryTheory.Abelian.Ext.{u} E M n)
    (h : ∀ s : Γ(E,⊤),schemeModuleExtClassActualSectionBoundary epsilon s = 0 ↔
      ∃ z : Γ(A,⊤),a.app ⊤ z = s) (s : Γ(E,⊤)) :
    schemeModuleExtClassActualSectionBoundary epsilon s = 0 ↔
      ∃ z : Γ(B,⊤),(e.inv ≫ a).app ⊤ z = s := by
  rw [h]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨e.hom.app ⊤ z,?_⟩
    have H : (e.inv ≫ a).app ⊤ (e.hom.app ⊤ z) = a.app ⊤ z := by
      change a.app ⊤ ((e.hom ≫ e.inv).app ⊤ z) = a.app ⊤ z
      rw [e.hom_inv_id]
      rfl
    exact H.trans hz
  · rintro ⟨z,hz⟩
    exact ⟨e.inv.app ⊤ z,hz⟩
end LinearStudy
