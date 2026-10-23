module
public import Linear.TopOpenFreeAbelianSheafSectionsNaturality
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
/-- Every actual injective abelian sheaf on the original space is flasque. -/
theorem topAbelianSheaf_injective_isFlasque (X : TopCat.{u})
    (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I] :
    TopCat.Sheaf.IsFlasque I := by
  constructor
  intro U V f
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  let a := (topOpenFreeAbelianSheafHomEquiv X V.unop I).symm s
  let m := (topOpenFreeAbelianSheafFunctor X).map f.unop
  haveI : Mono m := topOpenFreeAbelianSheaf_map_mono X f.unop
  let b := Injective.factorThru a m
  refine ⟨topOpenFreeAbelianSheafHomEquiv X U.unop I b, ?_⟩
  exact (topOpenFreeAbelianSheafHomEquiv_restrict X f.unop I b).symm.trans
    ((congrArg (topOpenFreeAbelianSheafHomEquiv X V.unop I)
      (Injective.comp_factorThru a m)).trans
        ((topOpenFreeAbelianSheafHomEquiv X V.unop I).apply_symm_apply s))
end LinearStudy
