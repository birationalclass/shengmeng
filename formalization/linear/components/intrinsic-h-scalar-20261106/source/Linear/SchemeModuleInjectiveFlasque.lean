module
public import Linear.OverOpenInjectiveUnitExtension
public import Linear.SchemeModuleUnitHomSections
public import Linear.SchemeModuleFlasqueKernelSectionLifting
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- Every section of an actual injective module sheaf extends to the original top open. -/
theorem schemeModule_injective_globalRestriction_surjective (X : Scheme.{u})
    (I : X.Modules) [Injective I] (U : X.Opens) :
    Function.Surjective (I.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  intro s
  let sl := (schemeModuleOverSectionsEquiv I U).symm s
  let a := (I.over U).unitHomEquiv.symm sl
  obtain ⟨b,hb⟩ := overOpenUnitHom_extend_of_injective X.ringCatSheaf U I a
  have hs : Scheme.Modules.Hom.app b U (1 : Γ(X,U)) = s := by
    change schemeModuleOverSectionsEquiv I U
      ((I.over U).unitHomEquiv ((SheafOfModules.overFunctor X.ringCatSheaf U).map b)) = s
    exact (congrArg (fun g => schemeModuleOverSectionsEquiv I U
      ((I.over U).unitHomEquiv g)) hb).trans
        ((congrArg (schemeModuleOverSectionsEquiv I U)
          ((I.over U).unitHomEquiv.apply_symm_apply sl)).trans
            ((schemeModuleOverSectionsEquiv I U).apply_symm_apply s))
  refine ⟨Scheme.Modules.Hom.app b ⊤ (1 : Γ(X,⊤)), ?_⟩
  have h := moduleSheafMap_restriction_apply b (show U ≤ ⊤ from le_top) (1 : Γ(X,⊤))
  have hone : (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).map
      (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X,⊤)) = (1 : Γ(X,U)) := by
    change X.presheaf.map _ (1 : Γ(X,⊤)) = 1
    exact map_one _
  rw [hone] at h
  exact h.trans hs

/-- The actual underlying abelian sheaf of an injective module sheaf is flasque.
It is not asserted to be injective in the category of abelian sheaves. -/
theorem schemeModule_injective_isFlasque (X : Scheme.{u})
    (I : X.Modules) [Injective I] :
    TopCat.Sheaf.IsFlasque ((schemeModuleToActualAbelianSheaf X).obj I) := by
  constructor
  intro U V f
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  obtain ⟨x,hx⟩ := schemeModule_injective_globalRestriction_surjective X I V.unop s
  refine ⟨I.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x, ?_⟩
  change I.presheaf.map f
    (I.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x) = s
  have hcomp : I.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op ≫
      I.presheaf.map f = I.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op := by
    rw [← I.presheaf.map_comp]
    exact congrArg I.presheaf.map (Subsingleton.elim _ _)
  exact (congrArg (fun g => g x) hcomp).trans hx
end LinearStudy
