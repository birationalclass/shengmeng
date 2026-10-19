module
public import Linear.ExtCovariantFiniteBiproduct
public import Linear.NativeProjectiveKoszulComplex
public import Linear.SchemeModuleDerivedInternalHom
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [HasExt.{w} (Proj 𝓑).Modules]
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local irreducible] nativeProjectiveKoszulTerm nativeProjectiveModuleSheaf
  nativeProjectiveRingIntegerPiece
/-- A SINGLE explicit Serre bound for ACTUAL integer twists gives GLOBAL
relative Ext vanishing of the SAME actual Koszul term. The bound is an
UNPROVED geometric input here;local freeness is not substituted for it. -/
theorem nativeKoszulRelativeExt_term_of_twist_bound
    (O : (Proj 𝓑).Modules) (N : ℕ)
    (hSerre : ∀ s : ℤ,(N : ℤ) ≤ s → ∀ i : ℕ,0 < i → Subsingleton
      (Ext O (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) s) i))
    (r d p : ℕ) (k : ℤ) (hk : (N : ℤ) ≤ k-(p : ℤ)*(d : ℤ))
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (Ext O (nativeProjectiveKoszulTerm 𝓑 r d p k) i) := by
  let e := nativeProjectiveKoszulTermTwistIso 𝓑 r d p k
  exact ((extFunctorObj O i).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr.mpr
    (extCovariantFiniteBiproduct_subsingleton O _ i
      (fun _ => hSerre _ hk i hi))
/-- ORIGINAL twist t=r*d-r-1 makes EVERY middle term exceed the SAME
Serre bound when d>=N+r+1. This retains the actual original native
complex,not a chosen acyclic replacement or an assumed Ext certificate. -/
theorem nativeKoszulRelativeExt_middle_of_Serre_bound
    (O : (Proj 𝓑).Modules) (N : ℕ)
    (hSerre : ∀ s : ℤ,(N : ℤ) ≤ s → ∀ i : ℕ,0 < i → Subsingleton
      (Ext O (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) s) i))
    {r d : ℕ} (H : Fin r → S) (hH : ∀ j,H j ∈ 𝓑 d)
    (hd : N+r+1 ≤ d) (p : ℕ) (hp : p < r) (i : ℕ) (hi : 0 < i) :
    Subsingleton (Ext O
      ((nativeProjectiveKoszulComplex 𝓑 H hH ((r : ℤ)*(d : ℤ)-(r : ℤ)-1)).X p) i) := by
  rw [nativeProjectiveKoszulComplex_X]
  apply nativeKoszulRelativeExt_term_of_twist_bound 𝓑 O N hSerre r d p _ _ i hi
  have hpd : (p : ℤ)+1 ≤ (r : ℤ) := by exact_mod_cast hp
  have hdn : 0 ≤ (d : ℤ) := by positivity
  have hbd : (N : ℤ)+(r : ℤ)+1 ≤ (d : ℤ) := by exact_mod_cast hd
  nlinarith
/-- Choose m BEFORE ALL original degree D and ALL iterate degree d. One
SINGLE Serre bound supplies the actual middle vanishings whenever d>mD.
The Serre theorem itself remains an explicit unproved input. -/
theorem nativeKoszulRelativeExt_uniform_bound
    (O : (Proj 𝓑).Modules) (N r : ℕ)
    (hSerre : ∀ s : ℤ,(N : ℤ) ≤ s → ∀ i : ℕ,0 < i → Subsingleton
      (Ext O (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) s) i)) :
    ∃ m : ℕ,0 < m ∧ ∀ D : ℕ,1 ≤ D → ∀ d : ℕ,m*D < d →
      ∀ (H : Fin r → S) (hH : ∀ j,H j ∈ 𝓑 d),
      ∀ p : ℕ,p < r → ∀ i : ℕ,0 < i → Subsingleton
        (Ext O ((nativeProjectiveKoszulComplex 𝓑 H hH ((r : ℤ)*(d : ℤ)-(r : ℤ)-1)).X p) i) := by
  refine ⟨N+r+1,by omega,?_⟩
  intro D hD d hd H hH p hp i hi
  apply nativeKoszulRelativeExt_middle_of_Serre_bound 𝓑 O N hSerre H hH _ p hp i hi
  have hm : N+r+1 ≤ (N+r+1)*D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N+r+1) hD
  omega
end LinearStudy
