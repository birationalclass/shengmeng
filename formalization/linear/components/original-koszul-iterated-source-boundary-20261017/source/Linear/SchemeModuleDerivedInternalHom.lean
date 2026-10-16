module
public import Linear.SchemeModuleInternalHomCoefficientFunctor
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

/-- ACTUAL derived internal SHEAF Ext,using native right derived functors
of ACTUAL internal Hom in its coefficient variable. Enough injectives
come from native Grothendieck abelian structure,not an added premise.
This definition alone does not compute the Koszul or global Ext comparison. -/
def schemeModuleInternalExtFunctor (P : X.Modules) (q : ℕ) : X.Modules ⥤ X.Modules :=
  (schemeModuleInternalHomCoefficientFunctor X P).rightDerived q

def schemeModuleInternalExt (P N : X.Modules) (q : ℕ) : X.Modules :=
  (schemeModuleInternalExtFunctor P q).obj N

/-- Compute ACTUAL derived SHEAF Ext by any actual injective resolution
of the coefficient sheaf. The desired Koszul comparison is NOT an input
and has not been inferred from this injective computation. -/
def schemeModuleInternalExtInjectiveResolutionIso (P N : X.Modules) (q : ℕ)
    (I : InjectiveResolution N) :
    schemeModuleInternalExt P N q ≅
      (((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q :=
  I.isoRightDerivedObj (schemeModuleInternalHomCoefficientFunctor X P) q

theorem schemeModuleInternalExt_injective_succ (P N : X.Modules) [Injective N] (q : ℕ) :
    IsZero (schemeModuleInternalExt P N (q+1)) :=
  Functor.isZero_rightDerived_obj_injective_succ
    (schemeModuleInternalHomCoefficientFunctor X P) q N

/-- SAME actual lift between injective resolutions gives the actual
coefficient map on derived SHEAF Ext,with its native homology map. -/
theorem schemeModuleInternalExtInjectiveResolutionIso_naturality
    (P : X.Modules) {M N : X.Modules} (c : M ⟶ N) (q : ℕ)
    (I : InjectiveResolution M) (J : InjectiveResolution N)
    (phi : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ phi.f 0 = c ≫ J.ι.f 0) :
    (schemeModuleInternalExtFunctor P q).map c ≫
        (schemeModuleInternalExtInjectiveResolutionIso P N q J).hom =
      (schemeModuleInternalExtInjectiveResolutionIso P M q I).hom ≫
        (HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℕ) q).map
          (((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
            (ComplexShape.up ℕ)).map phi) :=
  InjectiveResolution.isoRightDerivedObj_hom_naturality c I J phi comm
    (schemeModuleInternalHomCoefficientFunctor X P) q

end LinearStudy
