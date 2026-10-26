module
public import Linear.TildeActualCocycleModuleExt
public import Linear.TildeKoszulCoforkAugmentationComparison
public import Linear.OriginalChainTopExtTargetIso
public import Linear.KoszulExactResolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u

/-- Actual positive MODULE Koszul exactness gives the SAME original
quotient-cofork sheaf augmentation a quasiiso,using its proved whole-map
comparison with the native tilde quotient augmentation. -/
theorem tildeKoszulCoforkAugmentation_quasiIso_of_exact
    (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j) :
    QuasiIso (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
      (tildeKoszulOriginalCutCokernelCofork R H)) := by
  let P := functionKoszulResolutionOfExact H he
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  letI := mappedOriginalChainAugmentation_quasiIso (tilde.functor R) P.complex P.π
  rw [tildeKoszulOriginalCoforkAugmentation_eq_mappedModule]
  change QuasiIso (mappedOriginalChainAugmentation (tilde.functor R) P.complex P.π ≫
    (ChainComplex.single₀ (Spec R).Modules).map
      (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom)
  infer_instance

/-- Explicit STATEMENT linking the actual original affine quotient-cofork
roof to the MODULE Ext class constructed from the SAME sheaf cocycle.
The native quotient target iso is retained;no Ext-bijectivity is asserted. -/
def tildeKoszulCoforkActualCocycleModuleExtLaw
    (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (ell : ℕ) (N : ModuleCat.{u} R)
    (a : (tilde.functor R).obj ((functionKoszulResolutionOfExact H he).complex.X ell) ⟶
      (tilde.functor R).obj N)
    (ha : (tilde.functor R).map ((functionKoszulResolutionOfExact H he).complex.d (ell+1) ell) ≫ a = 0) : Prop :=
  let P := functionKoszulResolutionOfExact H he
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  letI := tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he
  (Ext.mk₀ (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom).comp
    (originalChainTopExtClass (tildeFunctionKoszulComplex R H) ell
      (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
        (tildeKoszulOriginalCutCokernelCofork R H)) a ha) (zero_add _) =
    (tildeActualCocycleModuleExt R P ell a ha).mapExactFunctor (tilde.functor R)

/-- PROVE the actual original affine quotient-roof/MODULE representative
comparison from the proved augmentation map identity,target-iso action
and constructed Hom preimage. Exactness and the original cocycle are
explicit at this affine boundary;original applications derive them. -/
theorem tildeKoszulCoforkActualCocycleModuleExtLaw_proof
    (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (ell : ℕ) (N : ModuleCat.{u} R)
    (a : (tilde.functor R).obj ((functionKoszulResolutionOfExact H he).complex.X ell) ⟶
      (tilde.functor R).obj N)
    (ha : (tilde.functor R).map ((functionKoszulResolutionOfExact H he).complex.d (ell+1) ell) ≫ a = 0) :
    tildeKoszulCoforkActualCocycleModuleExtLaw R H he ell N a ha := by
  let P := functionKoszulResolutionOfExact H he
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  letI := tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he
  letI := mappedOriginalChainAugmentation_quasiIso (tilde.functor R) P.complex P.π
  let rho := tildeQuotientPushforwardIso R (Ideal.span (Set.range H))
  have hm := tildeActualCocycleModuleExtLaw_proof R P ell a ha
  dsimp only [tildeActualCocycleModuleExtLaw] at hm
  have ht := originalChainTopExtClass_targetIso (tildeFunctionKoszulComplex R H) ell rho
    (mappedOriginalChainAugmentation (tilde.functor R) P.complex P.π) a ha
  have hbeta := tildeKoszulOriginalCoforkAugmentation_eq_mappedModule R H
  have hc : originalChainTopExtClass (tildeFunctionKoszulComplex R H) ell
      (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
        (tildeKoszulOriginalCutCokernelCofork R H)) a ha =
      originalChainTopExtClass (tildeFunctionKoszulComplex R H) ell
        (mappedOriginalChainAugmentation (tilde.functor R) P.complex P.π ≫
          (ChainComplex.single₀ (Spec R).Modules).map rho.hom) a ha := by
    congr 1
  dsimp only [tildeKoszulCoforkActualCocycleModuleExtLaw]
  rw [hc]
  exact ht.trans hm.symm

end LinearStudy
