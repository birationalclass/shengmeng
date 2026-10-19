module
public import Linear.CochainResolutionExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w d
variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasExt.{w} A] [HasDerivedCategory.{d} A]
/-- ACTUAL source naturality for arbitrary morphisms of augmented
resolutions,not only source isomorphisms. The same roofs and cocycle
are retained. This supplies the source-lift step for the ORIGINAL
Koszul connecting map;no class-vanishing condition is a premise. -/
theorem cochainResolutionExtClass_sourceSquare
    (K L : CochainComplex A ℤ) {E F N : A} (r : ℕ)
    (alpha : K ⟶ (CochainComplex.singleFunctor A 0).obj E) [QuasiIso alpha]
    (tau : L ⟶ (CochainComplex.singleFunctor A 0).obj F) [QuasiIso tau]
    (gamma : L ⟶ K) (u : F ⟶ E)
    (hsq : gamma ≫ alpha = tau ≫ (CochainComplex.singleFunctor A 0).map u)
    (beta : ShiftedHom K ((CochainComplex.singleFunctor A 0).obj N) (r : ℤ)) :
    (Ext.mk₀ u).comp (cochainResolutionExtClass K r alpha beta) (zero_add r) =
      cochainResolutionExtClass L r tau
        ((ShiftedHom.mk₀ 0 rfl gamma).comp beta (add_zero _)) := by
  have hs : DerivedCategory.Q.map ((CochainComplex.singleFunctor A 0).map u) ≫
        inv (DerivedCategory.Q.map alpha) =
      inv (DerivedCategory.Q.map tau) ≫ DerivedCategory.Q.map gamma := by
    apply (cancel_mono (DerivedCategory.Q.map alpha)).mp
    simp only [Category.assoc,IsIso.inv_hom_id,Category.comp_id]
    rw [← Functor.map_comp,hsq,Functor.map_comp]
    simp
  apply Ext.ext
  simp only [Ext.comp_hom,Ext.mk₀_hom,cochainResolutionExtClass_hom,
    ShiftedHom.mk₀_comp,ShiftedHom.comp_mk₀,ShiftedHom.map,
    Functor.map_comp,Category.assoc]
  rw [NatTrans.naturality_assoc]
  simp only [Functor.comp_map]
  rw [reassoc_of% hs]
end LinearStudy
