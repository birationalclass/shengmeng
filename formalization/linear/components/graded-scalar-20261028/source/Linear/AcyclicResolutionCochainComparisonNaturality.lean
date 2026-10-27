module
public import Linear.AcyclicResolutionHomologyCoefficientNaturality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
/-- Transfer the ALREADY PROVED relative-acyclic-resolution naturality
through an actual Hom/cochain isomorphism square. That cochain square is
an explicit input here and is DERIVED in the geometric Cech application.
No desired global-H naturality or new cohomology model is an input. -/
theorem acyclicResolutionActualCochainComparison_coefficient_naturality
    (K : ChainComplex A ℕ) (Z : A) (f : K ⟶ (ChainComplex.single₀ A).obj Z)
    [QuasiIso f] {F G : A} (a : F ⟶ G)
    (hF : ∀ p j,Subsingleton (Ext (K.X p) F (j+1)))
    (hG : ∀ p j,Subsingleton (Ext (K.X p) G (j+1)))
    {C D : CochainComplex AddCommGrpCat.{v} ℕ}
    (eF : chainActualHomCochain K F ≅ C) (eG : chainActualHomCochain K G ≅ D)
    (b : C ⟶ D)
    (hb : chainActualHomCochainCoefficientMap K a ≫ eG.hom = eF.hom ≫ b)
    (q : ℕ) :
    HomologicalComplex.homologyMap b (q+1) ≫
      (((HomologicalComplex.homologyFunctor _ _ (q+1)).mapIso eG.symm) ≪≫
        (acyclicResolutionGlobalExtActualHomologyIso K Z f G hG q).symm).hom =
    (((HomologicalComplex.homologyFunctor _ _ (q+1)).mapIso eF.symm) ≪≫
      (acyclicResolutionGlobalExtActualHomologyIso K Z f F hF q).symm).hom ≫
        AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp Z (add_zero (q+1))) := by
  let T := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) (q+1)
  have hco : CommSq (chainActualHomCochainCoefficientMap K a) eF.hom eG.hom b := ⟨hb⟩
  have hc := T.map_commSq hco
  have hs := CommSq.vert_inv (g:=T.mapIso eF) (h:=T.mapIso eG) hc
  let dF := acyclicResolutionGlobalExtActualHomologyIso K Z f F hF q
  let dG := acyclicResolutionGlobalExtActualHomologyIso K Z f G hG q
  have hd : CommSq (AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp Z (add_zero (q+1))))
      dF.hom dG.hom
      (HomologicalComplex.homologyMap (chainActualHomCochainCoefficientMap K a) (q+1)) :=
    ⟨acyclicResolutionGlobalExtActualHomologyIso_coefficient_naturality K Z f a hF hG q⟩
  have ht := CommSq.vert_inv (g:=dF) (h:=dG) hd
  exact (hs.vert_comp ht).w
end LinearStudy
