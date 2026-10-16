module
public import Linear.SchemeModuleLocalHomSourceIso
public import Linear.SchemeModuleOverHomology
public import Linear.SchemeModuleDerivedInternalHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}} {P Q : X.Modules}

/-- A genuine LOCAL source frame compares the SAME actual coefficient
Hom complexes AFTER actual original open restriction. -/
def schemeModuleLocalHomCoefficientComplexIso (U : X.Opens)
    (e : P.over U ≅ Q.over U) (K : CochainComplex X.Modules ℕ) :
    ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K) ≅
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (((schemeModuleInternalHomCoefficientFunctor X Q).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K) := by
  letI := schemeModuleOverFunctor_additive X U
  letI := schemeModuleInternalHomCoefficientFunctor_additive X P
  letI := schemeModuleInternalHomCoefficientFunctor_additive X Q
  letI : (schemeModuleInternalHomCoefficientFunctor X P ⋙
      SheafOfModules.overFunctor.{u} X.ringCatSheaf U).Additive := inferInstance
  letI : (schemeModuleInternalHomCoefficientFunctor X Q ⋙
      SheafOfModules.overFunctor.{u} X.ringCatSheaf U).Additive := inferInstance
  exact (NatIso.mapHomologicalComplex (schemeModuleLocalHomCoefficientIso U e)
    (ComplexShape.up ℕ)).app K

/-- Actual higher SHEAF Ext is local in the SOURCE under a genuine local
frame. The comparison is constructed from SAME coefficient resolution,
PROVED local Hom iso,and PROVED restriction/cohomology comparison. -/
def schemeModuleLocalInternalExtSourceIso (U : X.Opens)
    (e : P.over U ≅ Q.over U) (N : X.Modules) (q : ℕ)
    (I : InjectiveResolution N) :
    (schemeModuleInternalExt P N q).over U ≅ (schemeModuleInternalExt Q N q).over U :=
  (SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapIso
      (schemeModuleInternalExtInjectiveResolutionIso P N q I) ≪≫
    (schemeModuleOverHomologyIso U
      (((schemeModuleInternalHomCoefficientFunctor X P).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex) q).symm ≪≫
    (HomologicalComplex.homologyFunctor (SheafOfModules.{u} (X.ringCatSheaf.over U))
      (ComplexShape.up ℕ) q).mapIso (schemeModuleLocalHomCoefficientComplexIso U e I.cocomplex) ≪≫
    schemeModuleOverHomologyIso U
      (((schemeModuleInternalHomCoefficientFunctor X Q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex) q ≪≫
    ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapIso
      (schemeModuleInternalExtInjectiveResolutionIso Q N q I)).symm

end LinearStudy
