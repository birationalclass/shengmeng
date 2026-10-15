module
public import Linear.TildeKoszulCoforkActualModuleExt
public import Mathlib.CategoryTheory.Abelian.Exact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- Native tilde reflects exactness by its faithful action on Hom. This
uses the existing abelian-category reflection theorem,not an Ext inverse. -/
theorem tilde_chainComplex_exactAt_iff (R : CommRingCat.{u})
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ) :
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.down ℕ)).obj C).ExactAt j ↔
      C.ExactAt j := by
  constructor
  · intro h
    change ((C.sc j).map (tilde.functor R)).Exact at h
    exact (tilde.functor R).reflects_exact_of_faithful (C.sc j) h
  · exact tilde_chainComplex_exactAt R C j

/-- Derive positive MODULE Koszul exactness from the SAME actual original
quotient-cofork sheaf augmentation's quasi-isomorphism. Hence the module
resolution does not require a new exactness hypothesis in applications. -/
theorem tildeKoszul_moduleExact_of_coforkQuasiIso
    (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    [QuasiIso (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H))]
    (j : ℕ) (hj : 0 < j) :
    (koszulComplex (Fintype.linearCombination R H)).ExactAt j := by
  apply (tilde_chainComplex_exactAt_iff R _ j).1
  change (tildeFunctionKoszulComplex R H).ExactAt j
  apply (exactAt_iff_of_quasiIsoAt
    (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H)) j).2
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  apply ChainComplex.exactAt_succ_single_obj

end LinearStudy
