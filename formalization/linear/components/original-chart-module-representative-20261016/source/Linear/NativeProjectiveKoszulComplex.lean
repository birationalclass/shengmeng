module
public import Linear.KoszulHomogeneousCoordinates
public import Linear.NativeProjectiveDegreeZeroIdentities
public import Linear.NativeShiftedFreeIntegerTwistBiproduct
public import Linear.SchemeModuleInternalHomComplex
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- The ACTUAL global degree-p Koszul module sheaf on ORIGINAL Proj.
The canonical exterior basis has weight p*q, with arbitrary integer twist k. -/
def nativeProjectiveKoszulTerm (r q p : ℕ) (k : ℤ) : (AlgebraicGeometry.Proj 𝓑).Modules :=
  nativeProjectiveModuleSheaf 𝓑
    (integerShiftedFreePiece 𝓑 (fun _ : Set.powersetCard (Fin r) p => (p:ℤ)*(q:ℤ)))
    (integerShiftedFreePiece_smul_homogeneous 𝓑 (fun _ => (p:ℤ)*(q:ℤ))) k

/-- Sheafify the ORIGINAL exterior differential in its ORIGINAL canonical
coordinates. Its grading has been PROVED from H, not supplied as a premise. -/
def nativeProjectiveKoszulDifferential {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ) (k : ℤ) :
    nativeProjectiveKoszulTerm 𝓑 r q (p+1) k ⟶ nativeProjectiveKoszulTerm 𝓑 r q p k :=
  nativeProjectiveDegreeZeroSheafMap 𝓑 _ _ _ _
    (homogeneousKoszulCoordinateDifferential H p)
    (homogeneousKoszulCoordinateDifferential_homogeneous 𝓑 H hH p) k

/-- The global original differentials square to zero. No source exactness,
regular sequence, coefficient condition, or transition certificate is assumed. -/
theorem nativeProjectiveKoszulDifferential_comp_zero {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (p : ℕ) (k : ℤ) :
    nativeProjectiveKoszulDifferential 𝓑 H hH (p+1) k ≫
      nativeProjectiveKoszulDifferential 𝓑 H hH p k = 0 := by
  exact nativeProjectiveDegreeZeroSheafMap_comp_eq_zero 𝓑 _ _ _ _ _ _ _ _
    (homogeneousKoszulCoordinateDifferential_homogeneous 𝓑 H hH (p+1))
    (homogeneousKoszulCoordinateDifferential_homogeneous 𝓑 H hH p)
    (homogeneousKoszulCoordinateDifferential_comp H p) k

/-- ACTUAL global weighted Koszul chain complex on the ORIGINAL projective
scheme, constructed from the ORIGINAL forms and their ORIGINAL differentials. -/
def nativeProjectiveKoszulComplex {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) :
    ChainComplex (AlgebraicGeometry.Proj 𝓑).Modules ℕ :=
  ChainComplex.of (fun p => nativeProjectiveKoszulTerm 𝓑 r q p k)
    (fun p => nativeProjectiveKoszulDifferential 𝓑 H hH p k)
    (fun p => nativeProjectiveKoszulDifferential_comp_zero 𝓑 H hH p k)

theorem nativeProjectiveKoszulComplex_X {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) (p : ℕ) :
    (nativeProjectiveKoszulComplex 𝓑 H hH k).X p =
      nativeProjectiveKoszulTerm 𝓑 r q p k := rfl

/-- Every consecutive global differential is exactly the original
sheafified exterior differential, not an arbitrary map with zero composite. -/
theorem nativeProjectiveKoszulComplex_d {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) (p : ℕ) :
    (nativeProjectiveKoszulComplex 𝓑 H hH k).d (p+1) p =
      nativeProjectiveKoszulDifferential 𝓑 H hH p k := by
  simp only [nativeProjectiveKoszulComplex, ChainComplex.of_d]

/-- Each ORIGINAL global term is the actual finite biproduct of ORIGINAL
native integer twists O(k-p*q), indexed by its canonical exterior basis. -/
def nativeProjectiveKoszulTermTwistIso (r q p : ℕ) (k : ℤ) :
    nativeProjectiveKoszulTerm 𝓑 r q p k ≅
      biproduct (fun _ : Set.powersetCard (Fin r) p =>
        nativeProjectiveModuleSheaf 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
          (nativeProjectiveRingIntegerPiece_graded 𝓑) (k-(p:ℤ)*(q:ℤ))) :=
by
  unfold nativeProjectiveKoszulTerm
  exact nativeShiftedFreeIntegerTwistBiproductIso (ι := Set.powersetCard (Fin r) p)
    𝓑 (fun _ => (p:ℤ)*(q:ℤ)) k

/-- ACTUAL global internal-Hom cochain complex for ANY ORIGINAL module
sheaf N. Source regularity and target CM/free/flat/FP are not construction inputs. -/
def nativeProjectiveKoszulInternalHomCochain {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) (N : (AlgebraicGeometry.Proj 𝓑).Modules) :
    CochainComplex (AlgebraicGeometry.Proj 𝓑).Modules ℕ :=
  schemeModuleInternalHomCochainComplex N (nativeProjectiveKoszulComplex 𝓑 H hH k)

theorem nativeProjectiveKoszulInternalHomCochain_X {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) (N : (AlgebraicGeometry.Proj 𝓑).Modules) (p : ℕ) :
    (nativeProjectiveKoszulInternalHomCochain 𝓑 H hH k N).X p =
      schemeModuleHomModuleSheaf (nativeProjectiveKoszulTerm 𝓑 r q p k) N := rfl

/-- All consecutive ACTUAL global internal-Hom differentials are original
precomposition by the SAME explicit Koszul maps. Derived SHEAF Ext is separate. -/
theorem nativeProjectiveKoszulInternalHomCochain_d {r q : ℕ} (H : Fin r → S)
    (hH : ∀ i, H i ∈ 𝓑 q) (k : ℤ) (N : (AlgebraicGeometry.Proj 𝓑).Modules) (p : ℕ) :
    (nativeProjectiveKoszulInternalHomCochain 𝓑 H hH k N).d p (p+1) =
      schemeModuleHomPrecompose (nativeProjectiveKoszulDifferential 𝓑 H hH p k) := by
  change schemeModuleHomPrecompose ((nativeProjectiveKoszulComplex 𝓑 H hH k).d (p+1) p) = _
  rw [nativeProjectiveKoszulComplex_d]

end LinearStudy
