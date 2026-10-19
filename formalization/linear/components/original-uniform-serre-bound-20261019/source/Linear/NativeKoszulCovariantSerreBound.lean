module
public import Linear.NativeKoszulRelativeExtSerreBound
public import Linear.SchemeModuleOriginalCovariantAtSource
public import Linear.NativeKoszulFiniteTopTerm
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
/-- Statement only of ACTUAL original exactness at twist t=r*d-r-1.
The SAME original native complex,augmentation and top exterior iso are
retained. The following theorem proves it from ONE twist Serre bound. -/
def nativeKoszulCovariantAtOriginalTwistStatement
    {r d : ℕ} (H : Fin r → S) (hH : ∀ j,H j ∈ 𝓑 d)
    {E : (Proj 𝓑).Modules}
    (alpha : nativeProjectiveKoszulComplex 𝓑 H hH ((r : ℤ)*(d : ℤ)-(r : ℤ)-1) ⟶
      (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) (hAlpha : QuasiIso alpha)
    (O : (Proj 𝓑).Modules) : Prop :=
  schemeModuleOriginalCovariantAtSourceStatement
    (nativeProjectiveKoszulComplex 𝓑 H hH ((r : ℤ)*(d : ℤ)-(r : ℤ)-1)) r alpha hAlpha
    (by
      rw [nativeProjectiveKoszulComplex_X]
      exact nativeProjectiveKoszulTerm_isZero_above_rank 𝓑 r d (r+1) _ (by omega))
    (nativeProjectiveKoszulComplexTopTwistIso 𝓑 H hH _) O
/-- ONE bound for actual integer-twist GLOBAL relative Ext supplies the
previously explicit middle-term hypotheses,then SAME original covariant
exactness. Geometric Serre vanishing itself remains UNPROVED input. -/
theorem nativeKoszulCovariantAtOriginalTwistStatement_of_Serre
    {r d : ℕ} (hr : 0 < r) (H : Fin r → S) (hH : ∀ j,H j ∈ 𝓑 d)
    {E : (Proj 𝓑).Modules}
    (alpha : nativeProjectiveKoszulComplex 𝓑 H hH ((r : ℤ)*(d : ℤ)-(r : ℤ)-1) ⟶
      (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) (hAlpha : QuasiIso alpha)
    (O : (Proj 𝓑).Modules) (N : ℕ) (hd : N+r+1 ≤ d)
    (hSerre : ∀ s : ℤ,(N : ℤ) ≤ s → ∀ i : ℕ,0 < i → Subsingleton
      (Ext O (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) s) i)) :
    nativeKoszulCovariantAtOriginalTwistStatement 𝓑 H hH alpha hAlpha O := by
  apply schemeModuleOriginalCovariantAtSourceStatement_proof _ r hr alpha hAlpha
  intro j hj i hi
  exact nativeKoszulRelativeExt_middle_of_Serre_bound 𝓑 O N hSerre H hH hd
    (r-j-1) (by omega) i hi
/-- m is chosen from the SAME N,r BEFORE EVERY original degree D and
EVERY iterate degree d. No input certifies the desired exact sequence;
only a single geometric Serre bound remains as an explicit premise. -/
theorem nativeKoszul_uniformCovariantExact_from_Serre
    (O : (Proj 𝓑).Modules) (N r : ℕ) (hr : 0 < r)
    (hSerre : ∀ s : ℤ,(N : ℤ) ≤ s → ∀ i : ℕ,0 < i → Subsingleton
      (Ext O (nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
        (nativeProjectiveRingIntegerPiece_graded 𝓑) s) i)) :
    ∃ m : ℕ,0 < m ∧ ∀ D : ℕ,1 ≤ D → ∀ d : ℕ,m*D < d →
      ∀ (H : Fin r → S) (hH : ∀ j,H j ∈ 𝓑 d) (E : (Proj 𝓑).Modules)
        (alpha : nativeProjectiveKoszulComplex 𝓑 H hH ((r : ℤ)*(d : ℤ)-(r : ℤ)-1) ⟶
          (ChainComplex.single₀ (Proj 𝓑).Modules).obj E) (hAlpha : QuasiIso alpha),
        nativeKoszulCovariantAtOriginalTwistStatement 𝓑 H hH alpha hAlpha O := by
  refine ⟨N+r+1,by omega,?_⟩
  intro D hD d hd H hH E alpha hAlpha
  apply nativeKoszulCovariantAtOriginalTwistStatement_of_Serre 𝓑 hr H hH alpha hAlpha O N _ hSerre
  have hm : N+r+1 ≤ (N+r+1)*D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N+r+1) hD
  omega
end LinearStudy
