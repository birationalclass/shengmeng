module
public import Linear.TildeKoszulCoforkActualModuleExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u

/-- The SAME actual affine cocycle,transported through an actual
coefficient iso. The coefficient identification is explicit here. -/
def tildeKoszulIsoCocycle (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (ell : ℕ) {M : (Spec R).Modules} (N : ModuleCat.{u} R)
    (lambda : M ≅ (tilde.functor R).obj N)
    (a : (tildeFunctionKoszulComplex R H).X ell ⟶ M) := a ≫ lambda.hom

theorem tildeKoszulIsoCocycle_isCocycle (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (ell : ℕ) {M : (Spec R).Modules} (N : ModuleCat.{u} R)
    (lambda : M ≅ (tilde.functor R).obj N)
    (a : (tildeFunctionKoszulComplex R H).X ell ⟶ M)
    (ha : (tildeFunctionKoszulComplex R H).d (ell+1) ell ≫ a = 0) :
    (tilde.functor R).map ((koszulComplex (Fintype.linearCombination R H)).d (ell+1) ell) ≫
      tildeKoszulIsoCocycle R H ell N lambda a = 0 := by
  change (tildeFunctionKoszulComplex R H).d (ell+1) ell ≫ (a ≫ lambda.hom) = 0
  rw [← Category.assoc,ha,zero_comp]

/-- Construct the actual MODULE class from that SAME transported cocycle. -/
def tildeKoszulIsoCocycleModuleExt (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (ell : ℕ) {M : (Spec R).Modules} (N : ModuleCat.{u} R)
    (lambda : M ≅ (tilde.functor R).obj N)
    (a : (tildeFunctionKoszulComplex R H).X ell ⟶ M)
    (ha : (tildeFunctionKoszulComplex R H).d (ell+1) ell ≫ a = 0) :=
  tildeActualCocycleModuleExt R (functionKoszulResolutionOfExact H he) ell
    (tildeKoszulIsoCocycle R H ell N lambda a)
    (tildeKoszulIsoCocycle_isCocycle R H ell N lambda a ha)

/-- Explicit STATEMENT:coefficient push along lambda and original quotient
target comparison rho give the forward image of the constructed MODULE
class. This has no Ext inverse or coefficient trivialization premise
hidden in a proof field. Original applications construct lambda. -/
def tildeKoszulCoforkModuleExtIsoLaw (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (ell : ℕ) {M : (Spec R).Modules} (N : ModuleCat.{u} R)
    (lambda : M ≅ (tilde.functor R).obj N)
    (a : (tildeFunctionKoszulComplex R H).X ell ⟶ M)
    (ha : (tildeFunctionKoszulComplex R H).d (ell+1) ell ≫ a = 0) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  letI := tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he
  (Ext.mk₀ (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom).comp
    ((originalChainTopExtClass (tildeFunctionKoszulComplex R H) ell
      (originalChainCoforkAugmentation (tildeFunctionKoszulComplex R H)
        (tildeKoszulOriginalCutCokernelCofork R H)) a ha).comp
          (Ext.mk₀ lambda.hom) (add_zero _)) (zero_add _) =
    (tildeKoszulIsoCocycleModuleExt R H he ell N lambda a ha).mapExactFunctor (tilde.functor R)

theorem tildeKoszulCoforkModuleExtIsoLaw_proof (R : CommRingCat.{u}) {r : ℕ} (H : Fin r → R)
    (he : ∀ j : ℕ,0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)
    (ell : ℕ) {M : (Spec R).Modules} (N : ModuleCat.{u} R)
    (lambda : M ≅ (tilde.functor R).obj N)
    (a : (tildeFunctionKoszulComplex R H).X ell ⟶ M)
    (ha : (tildeFunctionKoszulComplex R H).d (ell+1) ell ≫ a = 0) :
    tildeKoszulCoforkModuleExtIsoLaw R H he ell N lambda a ha := by
  letI := HasDerivedCategory.standard (ModuleCat.{u} R)
  letI := HasExt.standard (Spec R).Modules
  letI := HasDerivedCategory.standard (Spec R).Modules
  letI := tilde_functor_preservesHomology R
  letI := Functor.preservesFiniteLimits_of_preservesHomology (tilde.functor R)
  letI := Functor.preservesFiniteColimits_of_preservesHomology (tilde.functor R)
  letI := tildeKoszulCoforkAugmentation_quasiIso_of_exact R H he
  dsimp only [tildeKoszulCoforkModuleExtIsoLaw]
  rw [originalChainTopExtClass_comp_mk₀]
  exact tildeKoszulCoforkActualCocycleModuleExtLaw_proof R H he ell N
    (tildeKoszulIsoCocycle R H ell N lambda a)
    (tildeKoszulIsoCocycle_isCocycle R H ell N lambda a ha)

end LinearStudy
