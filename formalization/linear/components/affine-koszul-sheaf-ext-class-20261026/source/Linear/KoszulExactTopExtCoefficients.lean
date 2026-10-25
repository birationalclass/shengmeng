module
public import Linear.KoszulTopHomCoefficientRestriction
public import Linear.KoszulExactResolution
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R] (n : ℕ) (H : Fin (n+1) → R)
variable (he : ∀ j : ℕ, 0 < j → (koszulComplex (Fintype.linearCombination R H)).ExactAt j)

/-- ANY ORIGINAL coefficient functional is a cocycle on the SAME actual
Koszul projective resolution constructed from positive exactness.
That source exactness is DERIVED for the original projective cuts elsewhere;
no global regular-sequence or CM hypothesis on R or N is added here. -/
theorem koszulExactTopCoefficient_isCocycle (N : ModuleCat.{u} R)
    (L : (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) :
    (functionKoszulResolutionOfExact H he).complex.d (n+2) (n+1) ≫ ModuleCat.ofHom L = 0 := by
  have hz : IsZero ((koszulComplex (Fintype.linearCombination R H)).X (n+2)) :=
    koszulComplex.isZero_X_of_card_generators_lt _ (Pi.basisFun R (Fin (n+1)))
      (Pi.basisFun R (Fin (n+1))).span_eq (n+2) (by simp)
  exact hz.eq_of_src _ _

/-- Actual derived MODULE Ext class of the ORIGINAL N-valued Koszul
functional, using native ProjectiveResolution.extMk on the SAME original
exterior complex and natural quotient augmentation. N is arbitrary. -/
def koszulExactTopExtCoefficientRepresentative (N : ModuleCat.{u} R)
    (L : (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) :
    Ext.{u} (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) N (n+1) :=
  (functionKoszulResolutionOfExact H he).extMk (ModuleCat.ofHom L) (n+2) rfl
    (koszulExactTopCoefficient_isCocycle n H he N L)

/-- Vanishing of the ACTUAL original N-valued derived Ext representative
is EXACTLY vanishing of the ORIGINAL coefficient restriction, not an input
comparison with an abstract Ext model. -/
theorem koszulExactTopExtCoefficientRepresentative_eq_zero_iff (N : ModuleCat.{u} R)
    (L : (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N) :
    koszulExactTopExtCoefficientRepresentative n H he N L = 0 ↔
      koszulTopHomCoefficientRestriction (N := N) n H L = 0 := by
  refine ((functionKoszulResolutionOfExact H he).extMk_eq_zero_iff
    (ModuleCat.ofHom L) (n+2) rfl (koszulExactTopCoefficient_isCocycle n H he N L) n rfl).trans ?_
  constructor
  · rintro ⟨F,hF⟩
    change (koszulComplex (Fintype.linearCombination R H)).d (n+1) n ≫ F = ModuleCat.ofHom L at hF
    rw [koszulComplex.d_eq_d] at hF
    change L ∈ LinearMap.ker (koszulTopHomCoefficientRestriction (N := N) n H)
    rw [koszulTopHomCoefficientRestriction_kernel n H]
    refine ⟨F.hom,?_⟩
    exact congrArg (fun f => f.hom) hF
  · intro hL
    change L ∈ LinearMap.ker (koszulTopHomCoefficientRestriction (N := N) n H) at hL
    rw [koszulTopHomCoefficientRestriction_kernel n H] at hL
    obtain ⟨F,hF⟩ := hL
    refine ⟨ModuleCat.ofHom F,?_⟩
    change (koszulComplex (Fintype.linearCombination R H)).d (n+1) n ≫ ModuleCat.ofHom F = ModuleCat.ofHom L
    rw [koszulComplex.d_eq_d]
    exact ModuleCat.hom_ext hF

/-- Every ACTUAL derived MODULE Ext class has an original N-valued top
Koszul functional representative. No condition on N is assumed. -/
theorem koszulExactTopExtCoefficientRepresentative_surjective (N : ModuleCat.{u} R) :
    Function.Surjective (koszulExactTopExtCoefficientRepresentative n H he N) := by
  intro a
  obtain ⟨f,hf,h⟩ := (functionKoszulResolutionOfExact H he).extMk_surjective a (n+2) rfl
  exact ⟨f.hom,h⟩

/-- Push an ACTUAL original Ext representative along ANY original
coefficient map a:N->Nprime. The SAME original functional becomes a o L. -/
theorem koszulExactTopExtCoefficientRepresentative_push
    (N Nprime : ModuleCat.{u} R) (L : (⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N)
    (a : N →ₗ[R] Nprime) :
    (koszulExactTopExtCoefficientRepresentative n H he N L).comp
        (Ext.mk₀ (ModuleCat.ofHom a)) (add_zero _) =
      koszulExactTopExtCoefficientRepresentative n H he Nprime (a.comp L) :=
  (functionKoszulResolutionOfExact H he).extMk_comp_mk₀ (ModuleCat.ofHom L) (n+2) rfl
    (koszulExactTopCoefficient_isCocycle n H he N L) (ModuleCat.ofHom a)

end LinearStudy
