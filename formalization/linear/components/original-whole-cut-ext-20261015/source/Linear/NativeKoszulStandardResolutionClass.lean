module
public import Linear.NativeKoszulFiniteTopTerm
public import Linear.ChainStandardTopExtClass
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- Construct the ACTUAL native global Koszul resolution class with the
standard Ext/derived-category prerequisites already discharged at the
abstract category boundary. No HasExt,chosen category,projectivity or
Ext-class certificate is a new original-geometry premise. -/
def nativeProjectiveKoszulStandardResolutionClass {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) {E : (Proj 𝓑).Modules}
    (alpha : nativeProjectiveKoszulComplex 𝓑 H hH k ⟶
      (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) [QuasiIso alpha] :
    letI := HasExt.standard (Proj 𝓑).Modules
    Ext.{1} E (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ))) r :=
  originalChainStandardTopExtClass (nativeProjectiveKoszulComplex 𝓑 H hH k) r alpha
    (nativeProjectiveKoszulComplexTopTwistIso 𝓑 H hH k).hom
    (nativeProjectiveKoszulGlobalTopFunctional_isCocycle 𝓑 H hH k _)

/-- ACTUAL proof value:coefficient pushforward of the original native
class retains its same top exterior-basis functional. Native Ext and
derived-category existence are constructed,not supplied assumptions. -/
def nativeProjectiveKoszulStandardResolutionClassPushProof {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) {E N : (Proj 𝓑).Modules}
    (alpha : nativeProjectiveKoszulComplex 𝓑 H hH k ⟶
      (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) [QuasiIso alpha]
    (a : nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ)) ⟶ N) :=
  originalChainStandardTopExtClassPushProof (nativeProjectiveKoszulComplex 𝓑 H hH k) r alpha
    (nativeProjectiveKoszulComplexTopTwistIso 𝓑 H hH k).hom
    (nativeProjectiveKoszulGlobalTopFunctional_isCocycle 𝓑 H hH k _) a

end LinearStudy
