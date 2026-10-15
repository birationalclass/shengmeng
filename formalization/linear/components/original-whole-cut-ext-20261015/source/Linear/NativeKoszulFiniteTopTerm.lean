module
public import Linear.NativeProjectiveKoszulComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- The ACTUAL original global Koszul sheaf is zero ABOVE its rank,
by its original exterior basis and the already proved native-twist
biproduct comparison. No regularity or exactness is assumed. -/
theorem nativeProjectiveKoszulTerm_isZero_above_rank (r q p : ℕ) (k : ℤ) (hp : r < p) :
    IsZero (nativeProjectiveKoszulTerm 𝓑 r q p k) := by
  letI : IsEmpty (Set.powersetCard (Fin r) p) := ⟨fun s => by
    have hn := Finset.card_le_univ (s : Finset (Fin r))
    have hs := Set.powersetCard.card_eq s
    simp only [Fintype.card_fin] at hn
    omega⟩
  have hz : IsZero (biproduct (fun _ : Set.powersetCard (Fin r) p =>
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(p:ℤ)*(q:ℤ)))) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro s
    exact isEmptyElim s
  exact hz.of_iso (nativeProjectiveKoszulTermTwistIso 𝓑 r q p k)

/-- The original top exterior basis contains exactly the full index set.
Use that ACTUAL basis vector to identify the top term with its native twist. -/
def nativeProjectiveKoszulTopTermTwistIso (r q : ℕ) (k : ℤ) :
    nativeProjectiveKoszulTerm 𝓑 r q r k ≅
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ)) := by
  letI : Unique (Set.powersetCard (Fin r) r) :=
    { default := ⟨Finset.univ,by simp⟩
      uniq := fun s => Subtype.ext
        (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
          (by simpa using s.property.ge)) }
  exact nativeProjectiveKoszulTermTwistIso 𝓑 r q r k ≪≫ biproductUniqueIso _

/-- Retain the SAME original complex as source when identifying its
actual top term;the source equality is proved,not a replacement datum. -/
def nativeProjectiveKoszulComplexTopTwistIso {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) :
    (nativeProjectiveKoszulComplex 𝓑 H hH k).X r ≅
      nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(r:ℤ)*(q:ℤ)) :=
  eqToIso (nativeProjectiveKoszulComplex_X 𝓑 H hH k r) ≪≫
    nativeProjectiveKoszulTopTermTwistIso 𝓑 r q k

/-- Every ACTUAL original top functional is a cocycle because the next
native global term is zero. This is independent of source exactness. -/
theorem nativeProjectiveKoszulGlobalTopFunctional_isCocycle {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i,H i ∈ 𝓑 q) (k : ℤ) {M : (Proj 𝓑).Modules}
    (f : (nativeProjectiveKoszulComplex 𝓑 H hH k).X r ⟶ M) :
    (nativeProjectiveKoszulComplex 𝓑 H hH k).d (r+1) r ≫ f = 0 := by
  have hz : IsZero ((nativeProjectiveKoszulComplex 𝓑 H hH k).X (r+1)) := by
    rw [nativeProjectiveKoszulComplex_X]
    exact nativeProjectiveKoszulTerm_isZero_above_rank 𝓑 r q (r+1) k (by omega)
  exact hz.eq_of_src _ _

end LinearStudy
