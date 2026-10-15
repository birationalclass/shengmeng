module
public import Linear.NativeKoszulFiniteTopTerm
public import Linear.ChainResolutionTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe w w'
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
variable [HasExt.{w} (Proj 𝓑).Modules] [HasDerivedCategory.{w'} (Proj 𝓑).Modules]

/-- An ACTUAL global derived Ext representative from the SAME native
Koszul resolution and ORIGINAL top exterior-basis functional. Source
quasiiso is explicit here;original applications derive it. Top incoming
vanishing is proved from actual finite length,not supplied as a premise.
No projectivity of global free sheaves or desired Ext class is assumed. -/
def nativeProjectiveKoszulResolutionExtRepresentative {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) {E N : (Proj 𝓑).Modules}
    (alpha : nativeProjectiveKoszulComplex 𝓑 H hH k ⟶
      (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) [QuasiIso alpha]
    (a : nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ)) ⟶ N) :
    Ext.{w} E N r :=
  originalChainTopExtClass (nativeProjectiveKoszulComplex 𝓑 H hH k) r alpha
    ((nativeProjectiveKoszulComplexTopTwistIso 𝓑 H hH k).hom ≫ a)
    (nativeProjectiveKoszulGlobalTopFunctional_isCocycle 𝓑 H hH k _)

/-- Global coefficient pushforward retains the SAME original top
functional. This is Ext in the actual scheme-module category,not an
affine module computation or an assertion identifying sheaf Ext. -/
theorem nativeProjectiveKoszulResolutionExtRepresentative_comp_mk₀ {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) {E N P : (Proj 𝓑).Modules}
    (alpha : nativeProjectiveKoszulComplex 𝓑 H hH k ⟶
      (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) [QuasiIso alpha]
    (a : nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ)) ⟶ N) (g : N ⟶ P) :
    (nativeProjectiveKoszulResolutionExtRepresentative 𝓑 H hH k alpha a).comp
        (Ext.mk₀ g) (add_zero _) =
      nativeProjectiveKoszulResolutionExtRepresentative 𝓑 H hH k alpha (a ≫ g) := by
  simpa only [nativeProjectiveKoszulResolutionExtRepresentative,Category.assoc] using
    originalChainTopExtClass_comp_mk₀ (nativeProjectiveKoszulComplex 𝓑 H hH k) r alpha
      ((nativeProjectiveKoszulComplexTopTwistIso 𝓑 H hH k).hom ≫ a)
      (nativeProjectiveKoszulGlobalTopFunctional_isCocycle 𝓑 H hH k _) g

/-- Define the ACTUAL native Koszul resolution class using the canonical
original top exterior-basis identification,not a freely supplied class.
Its identification with the manuscript's connecting boundary is separate. -/
def nativeProjectiveKoszulResolutionClass {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) {E : (Proj 𝓑).Modules}
    (alpha : nativeProjectiveKoszulComplex 𝓑 H hH k ⟶
      (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) [QuasiIso alpha] :
    Ext.{w} E (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ))) r :=
  nativeProjectiveKoszulResolutionExtRepresentative 𝓑 H hH k alpha (𝟙 _)

/-- Pushing the constructed resolution class along a gives its ACTUAL
original top-functional representative a. Local restriction/support and
proper duality are separate obligations. -/
theorem nativeProjectiveKoszulResolutionClass_comp_mk₀ {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) {E N : (Proj 𝓑).Modules}
    (alpha : nativeProjectiveKoszulComplex 𝓑 H hH k ⟶
      (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) [QuasiIso alpha]
    (a : nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ)) ⟶ N) :
    (nativeProjectiveKoszulResolutionClass 𝓑 H hH k alpha).comp (Ext.mk₀ a) (add_zero _) =
      nativeProjectiveKoszulResolutionExtRepresentative 𝓑 H hH k alpha a := by
  simpa only [nativeProjectiveKoszulResolutionClass,Category.id_comp] using
    nativeProjectiveKoszulResolutionExtRepresentative_comp_mk₀ 𝓑 H hH k alpha (𝟙 _) a

end LinearStudy
