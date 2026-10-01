module

public import Negativity.CurveDegree
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.TranscendentalSeparable
import Mathlib.Tactic
import Mathlib.Algebra.GroupWithZero.Torsion

@[expose] public section
namespace Negativity
open Module
open scoped nonZeroDivisors

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SeparableNormalClosure
variable (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]
local instance : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra _ _
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S
local notation3 "E" => IntermediateField.normalClosure K L (AlgebraicClosure L)
local instance : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
local instance : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl

/-- Integral closure in the normal closure, using extension separability
instead of perfectness of the base fraction field. -/
def Ring : Type _ := integralClosure S E
local notation3 "T" => Ring R S
instance : CommRing T := inferInstanceAs (CommRing (integralClosure S E))
instance : IsDomain T := inferInstanceAs (IsDomain (integralClosure S E))
instance : Algebra S T := inferInstanceAs (Algebra S (integralClosure S E))
instance : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
instance : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
local instance : FaithfulSMul S E := (faithfulSMul_iff_algebraMap_injective S E).mpr <|
  (FaithfulSMul.algebraMap_injective L E).comp (FaithfulSMul.algebraMap_injective S L)
instance : Module.IsTorsionFree S T := Subalgebra.instIsTorsionFree (integralClosure S E)
instance : FaithfulSMul R T :=
  (faithfulSMul_iff_algebraMap_injective R T).mpr <|
    (FaithfulSMul.algebraMap_injective S T).comp (FaithfulSMul.algebraMap_injective R S)
local instance : Algebra T E := inferInstanceAs (Algebra (integralClosure S E) E)
local instance : IsScalarTower S T E :=
  inferInstanceAs (IsScalarTower S (integralClosure S E) E)
local instance : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
local instance : IsScalarTower R L E := IsScalarTower.to₁₃₄ R K L E
local instance : IsScalarTower R S E := IsScalarTower.to₁₂₄ R S L E
local instance : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E
variable [Module.Finite R S]
local instance : FiniteDimensional L E := Module.Finite.right K L E
local instance : IsFractionRing T E := integralClosure.isFractionRing_of_finite_extension L E
instance : IsIntegrallyClosed T := integralClosure.isIntegrallyClosedOfFiniteExtension L

variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
local instance : Algebra.IsSeparable K E := by
  rw [normalClosure_def]
  have (f : L →ₐ[K] AlgebraicClosure L) : Algebra.IsSeparable K f.fieldRange :=
    Algebra.IsSeparable.of_algHom (F := K) («E» := f.fieldRange) (E' := L)
      (AlgEquiv.ofInjectiveField f).symm.toAlgHom
  exact IntermediateField.isSeparable_iSup K (AlgebraicClosure L)
local instance : Algebra.IsSeparable L E :=
  Algebra.isSeparable_tower_top_of_isSeparable K L E
local instance : IsGalois K E := ⟨⟩
instance : IsGalois K (FractionRing T) := by
  refine IsGalois.of_equiv_equiv (F := K) («E» := E)
    (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
    (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
  ext
  simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
    (FractionRing.algEquiv T E).symm _
variable [IsDedekindDomain S]
set_option linter.overlappingInstances false
instance : Module.Finite S T := IsIntegralClosure.finite S L E T
instance : Module.Finite R T := Module.Finite.trans S T
instance : IsDedekindDomain T := integralClosure.isDedekindDomain S L E
end SeparableNormalClosure
attribute [local instance] FractionRing.liftAlgebra

/-- Prime ideal norms for finite separable extensions of Dedekind domains.
The base fraction field need not be perfect. In particular this does not
impose characteristic zero on a curve's rational function field. -/
theorem separable_prime_ideal_norm (R S : Type*)
    [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
    (P : Ideal S) (p : Ideal R) [P.IsMaximal] [p.IsMaximal] [P.LiesOver p] :
    Ideal.relNorm R P = p ^ P.inertiaDeg R := by
  let T := SeparableNormalClosure.Ring R S
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h := Ideal.relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S) _
  rwa [← Ideal.relNorm_relNorm R S, Ideal.relNorm_eq_pow_of_isPrime_isGalois Q P,
    map_pow, Ideal.inertiaDeg_tower (R := R) P Q, pow_mul,
    pow_left_inj (Ideal.inertiaDeg_pos Q S).ne'] at h

end
end Negativity
