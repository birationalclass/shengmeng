module
public import Linear.NativeKoszulFiniteTopTerm
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
/-- The ACTUAL degree-zero exterior basis consists of its original empty
subset. Thus the SAME original zero Koszul term is the native O(k). -/
def nativeProjectiveKoszulZeroTermTwistIso (rank q : ℕ) (k : ℤ) :
    nativeProjectiveKoszulTerm B rank q 0 k ≅
      nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
        (nativeProjectiveRingIntegerPiece_graded B) k := by
  letI : Unique (Set.powersetCard (Fin rank) 0) :=
    { default := ⟨∅,rfl⟩
      uniq := fun s => Subtype.ext (Finset.card_eq_zero.mp s.property) }
  simpa only [Nat.cast_zero,zero_mul,sub_zero] using
    nativeProjectiveKoszulTermTwistIso B rank q 0 k ≪≫ biproductUniqueIso _
/-- Retain the original actual chain object as the source of its native
zero-term O(k) identification. No replacement complex or augmentation. -/
def nativeProjectiveKoszulComplexZeroTwistIso {rank q : ℕ} (H : Fin rank → S)
    (hH : ∀ i,H i ∈ B q) (k : ℤ) :
    (nativeProjectiveKoszulComplex B H hH k).X 0 ≅
      nativeProjectiveModuleSheaf B (nativeProjectiveRingIntegerPiece B)
        (nativeProjectiveRingIntegerPiece_graded B) k :=
  eqToIso (nativeProjectiveKoszulComplex_X B H hH k 0) ≪≫
    nativeProjectiveKoszulZeroTermTwistIso B rank q k
end LinearStudy
