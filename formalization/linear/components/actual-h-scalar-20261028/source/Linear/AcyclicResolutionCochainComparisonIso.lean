module
public import Linear.AcyclicResolutionCochainComparisonNaturality
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
/-- Name the SAME explicit cochain/Ext comparison,so concrete applications
can use a small interface without re-elaborating its full construction. -/
def acyclicResolutionActualCochainExtIso
    (K : ChainComplex A ℕ) (Z : A) (f : K ⟶ (ChainComplex.single₀ A).obj Z)
    [QuasiIso f] (F : A) (hF : ∀ p j,Subsingleton (Ext (K.X p) F (j+1)))
    {C : CochainComplex AddCommGrpCat.{v} ℕ}
    (eF : chainActualHomCochain K F ≅ C) (q : ℕ) :
    C.homology (q+1) ≅ AddCommGrpCat.of (Ext Z F (q+1)) :=
  (HomologicalComplex.homologyFunctor _ _ (q+1)).mapIso eF.symm ≪≫
    (acyclicResolutionGlobalExtActualHomologyIso K Z f F hF q).symm
/-- Naturality of the SAME named comparison follows from the already
proved generic transport theorem. Cochain naturality remains an EXPLICIT
input here and is derived for original geometric Cech complexes. -/
theorem acyclicResolutionActualCochainExtIso_coefficient_naturality
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
      (acyclicResolutionActualCochainExtIso K Z f G hG eG q).hom =
    (acyclicResolutionActualCochainExtIso K Z f F hF eF q).hom ≫
      AddCommGrpCat.ofHom ((Ext.mk₀ a).postcomp Z (add_zero (q+1))) :=
  acyclicResolutionActualCochainComparison_coefficient_naturality K Z f a hF hG eF eG b hb q
end LinearStudy
