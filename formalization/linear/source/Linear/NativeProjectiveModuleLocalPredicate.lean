module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
public import Mathlib.Algebra.Module.LocalizedModule.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
variable {K S D : Type*} [Field K] [CommRing S] [Algebra K S]
variable [AddCommGroup D] [Module S D] [Module K D]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable (𝒟 : ℤ → Submodule K D)

/-- Actual module localization at the ORIGINAL homogeneous prime.
The full localization is used as an ambient space for degree-k fractions. -/
abbrev nativeProjectiveModuleAtPrime (p : ProjectiveSpectrum 𝓑) : Type _ :=
  LocalizedModule p.asHomogeneousIdeal.toIdeal.primeCompl D

/-- A section is represented by one actual homogeneous fraction whose
numerator degree is denominator degree plus k, on the original open U. -/
def nativeProjectiveModuleIsFraction (k : ℤ)
    {U : Opens (ProjectiveSpectrum.top 𝓑)}
    (f : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1) : Prop :=
  ∃ (n : ℕ) (ell : 𝒟 ((n : ℤ)+k)) (b : 𝓑 n)
    (hb : ∀ p : U, (b : S) ∉ p.1.asHomogeneousIdeal),
    ∀ p : U, f p = LocalizedModule.mk (ell : D) ⟨(b : S),hb p⟩

/-- Restricting a genuine homogeneous fraction preserves its degree. -/
def nativeProjectiveModuleFractionPrelocal (k : ℤ) :
    PrelocalPredicate (fun p : ProjectiveSpectrum.top 𝓑 =>
      nativeProjectiveModuleAtPrime (D := D) 𝓑 p) where
  pred f := nativeProjectiveModuleIsFraction 𝓑 𝒟 k f
  res := by
    rintro U V i f ⟨n,ell,b,hb,hf⟩
    exact ⟨n,ell,b,(fun p => hb (i p)),(fun p => hf (i p))⟩

/-- The actual local-fraction predicate on the original Proj space. -/
def nativeProjectiveModuleLocalPredicate (k : ℤ) :
    LocalPredicate (fun p : ProjectiveSpectrum.top 𝓑 =>
      nativeProjectiveModuleAtPrime (D := D) 𝓑 p) :=
  (nativeProjectiveModuleFractionPrelocal 𝓑 𝒟 k).sheafify

/-- The actual associated-module local-fraction sheaf, currently
bundled in Type. Module structure and comparison with chart modules
are separate constructions, not assumptions of this definition. -/
def nativeProjectiveModuleSheafInType (k : ℤ) :
    Sheaf (Type _) (ProjectiveSpectrum.top 𝓑) :=
  subsheafToTypes (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k)

theorem nativeProjectiveModuleLocalPredicate_zero (k : ℤ)
    (U : Opens (ProjectiveSpectrum.top 𝓑)) :
    (nativeProjectiveModuleLocalPredicate 𝓑 𝒟 k).pred
      (0 : ∀ p : U, nativeProjectiveModuleAtPrime (D := D) 𝓑 p.1) := by
  intro p
  refine ⟨U,p.property,𝟙 U,0,⟨0,(𝒟 _).zero_mem⟩,
    ⟨1,SetLike.one_mem_graded 𝓑⟩,?_,?_⟩
  · intro q
    exact q.1.asHomogeneousIdeal.toIdeal.one_notMem
  · intro q
    exact (LocalizedModule.zero_mk _).symm

end LinearStudy
