module
public import Linear.SchemeModuleSourceHomCoefficientComplex
public import Linear.SchemeModuleDerivedInternalHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}

/-- Actual source-index equality transport commutes with coefficient action. -/
theorem schemeModuleInternalExtSourceIndex_coefficientNaturality (P : ℕ → X.Modules)
    (i j : ℕ) (h : i=j) {N M : X.Modules} (c : N ⟶ M) (q : ℕ) :
    (schemeModuleInternalExtFunctor (P i) q).map c ≫
        eqToHom (congrArg (fun z => schemeModuleInternalExt (P z) M q) h) =
      eqToHom (congrArg (fun z => schemeModuleInternalExt (P z) N q) h) ≫
        (schemeModuleInternalExtFunctor (P j) q).map c := by
  subst j
  exact (Category.comp_id ((schemeModuleInternalExtFunctor (P i) q).map c)).trans (Category.id_comp ((schemeModuleInternalExtFunctor (P i) q).map c)).symm

/-- Actual Ext-degree equality transport commutes with coefficient action. -/
theorem schemeModuleInternalExtDegree_coefficientNaturality (P : X.Modules)
    (i j : ℕ) (h : i=j) {N M : X.Modules} (c : N ⟶ M) :
    (schemeModuleInternalExtFunctor P i).map c ≫
        eqToHom (congrArg (fun z => schemeModuleInternalExt P M z) h) =
      eqToHom (congrArg (fun z => schemeModuleInternalExt P N z) h) ≫
        (schemeModuleInternalExtFunctor P j).map c := by
  subst j
  exact (Category.comp_id ((schemeModuleInternalExtFunctor P i).map c)).trans (Category.id_comp ((schemeModuleInternalExtFunctor P i).map c)).symm

/-- Native cohomology-degree equality transport commutes with coefficients. -/
theorem schemeModuleSourceHomCohomologyDegree_coefficientNaturality
    (K : ChainComplex X.Modules ℕ) (i j : ℕ) (h : i=j) {N M : X.Modules} (c : N ⟶ M) :
    (schemeModuleSourceHomCohomologyFunctor K i).map c ≫
        eqToHom (congrArg (fun z => (schemeModuleInternalHomCochainComplex M K).homology z) h) =
      eqToHom (congrArg (fun z => (schemeModuleInternalHomCochainComplex N K).homology z) h) ≫
        (schemeModuleSourceHomCohomologyFunctor K j).map c := by
  subst j
  exact (Category.comp_id ((schemeModuleSourceHomCohomologyFunctor K i).map c)).trans (Category.id_comp ((schemeModuleSourceHomCohomologyFunctor K i).map c)).symm

end LinearStudy
