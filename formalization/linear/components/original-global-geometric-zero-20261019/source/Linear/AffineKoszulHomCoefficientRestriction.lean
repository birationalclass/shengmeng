module
public import Linear.AffineTildeHomTargetNaturality
public import Linear.AffineKoszulTermInternalDualHom
public import Linear.TildeKoszulHomCoefficientRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- ACTUAL original Koszul Hom-term into ANY original coefficient N.
The ORIGINAL exterior source FP is PROVED;no FP/invertibility of N. -/
def affineKoszulTermHomCoefficientIso (R : CommRingCat.{u}) (N : ModuleCat.{u} R)
    (r j : ℕ) :
    tilde (ModuleCat.of R ((⋀[R]^j (Fin r → R)) →ₗ[R] N)) ≅
      schemeModuleHomModuleSheaf (tilde (ModuleCat.of R (⋀[R]^j (Fin r → R)))) (tilde N) := by
  letI := affineKoszulTerm_finitePresentation R r j
  exact affineTildeFinitePresentationHomIso R (ModuleCat.of R (⋀[R]^j (Fin r → R))) N

/-- ACTUAL original Koszul differential commutes with arbitrary original
N-coefficient internal-Hom identification. Desired square is PROVED. -/
theorem affineKoszulTermHomCoefficientIso_differential (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (r j : ℕ) (H : Fin r → R) :
    (tilde.functor R).map
        (ModuleCat.ofHom (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) j))) ≫
      (affineKoszulTermHomCoefficientIso R N r (j+1)).hom =
    (affineKoszulTermHomCoefficientIso R N r j).hom ≫
      schemeModuleHomPrecompose (N := tilde N) ((tilde.functor R).map
        (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) j))) := by
  unfold affineKoszulTermHomCoefficientIso
  exact @affineTildeFinitePresentationHomIso_precompose R
    (ModuleCat.of R (⋀[R]^(j+1) (Fin r → R)))
    (ModuleCat.of R (⋀[R]^j (Fin r → R))) N
    (affineKoszulTerm_finitePresentation R r (j+1))
    (affineKoszulTerm_finitePresentation R r j)
    (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) j))

/-- ACTUAL internal-Hom top sequence with ANY ORIGINAL coefficient N.
Same original precomposition d and same original quotient-tensor cut
coefficient are retained;no desired exactness or iso certificate. -/
def affineKoszulHomCoefficientRestrictionPresentation (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) : ShortComplex (Spec R).Modules where
  X₁ := schemeModuleHomModuleSheaf (tilde (ModuleCat.of R (⋀[R]^n (Fin (n+1) → R)))) (tilde N)
  X₂ := schemeModuleHomModuleSheaf (tilde (ModuleCat.of R (⋀[R]^(n+1) (Fin (n+1) → R)))) (tilde N)
  X₃ := (tildeKoszulHomCoefficientRestrictionPresentation R N n H).X₃
  f := schemeModuleHomPrecompose (N := tilde N) ((tilde.functor R).map
    (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) n)))
  g := (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv ≫
    (tildeKoszulHomCoefficientRestrictionPresentation R N n H).g
  zero := by
    have hd := affineKoszulTermHomCoefficientIso_differential R N (n+1) n H
    apply (cancel_epi (affineKoszulTermHomCoefficientIso R N (n+1) n).hom).mp
    simp only [comp_zero]
    calc
      _ = ((affineKoszulTermHomCoefficientIso R N (n+1) n).hom ≫
          schemeModuleHomPrecompose (N := tilde N) ((tilde.functor R).map
            (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) n)))) ≫
          (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv ≫
          (tildeKoszulHomCoefficientRestrictionPresentation R N n H).g := by simp only [Category.assoc]
      _ = ((tildeKoszulHomCoefficientRestrictionPresentation R N n H).f ≫
          (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom) ≫
          (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv ≫
          (tildeKoszulHomCoefficientRestrictionPresentation R N n H).g := by rw [← hd];rfl
      _ = (tildeKoszulHomCoefficientRestrictionPresentation R N n H).f ≫
          (tildeKoszulHomCoefficientRestrictionPresentation R N n H).g := by
        simp only [Category.assoc,Iso.hom_inv_id_assoc]
      _ = 0 := (tildeKoszulHomCoefficientRestrictionPresentation R N n H).zero

/-- PROVED actual original associated-Hom/internal-Hom short-complex iso. -/
def affineKoszulHomCoefficientRestrictionPresentationIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    tildeKoszulHomCoefficientRestrictionPresentation R N n H ≅
      affineKoszulHomCoefficientRestrictionPresentation R N n H := by
  refine ShortComplex.isoMk (affineKoszulTermHomCoefficientIso R N (n+1) n)
    (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)) (Iso.refl _) ?_ ?_
  · exact (affineKoszulTermHomCoefficientIso_differential R N (n+1) n H).symm
  · change (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
      ((affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv ≫
        (tildeKoszulHomCoefficientRestrictionPresentation R N n H).g) = _
    simp only [Iso.hom_inv_id_assoc,Iso.refl_hom,Category.comp_id]

/-- ACTUAL original arbitrary-coefficient internal-Hom top sequence is
exact. No regularity/FP/free/flat/invertibility/CM conditions on N. -/
theorem affineKoszulHomCoefficientRestrictionPresentation_exact (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulHomCoefficientRestrictionPresentation R N n H).Exact :=
  ShortComplex.exact_of_iso (affineKoszulHomCoefficientRestrictionPresentationIso R N n H)
    (tildeKoszulHomCoefficientRestrictionPresentation_exact R N n H)

/-- ACTUAL original arbitrary-coefficient internal-Hom restriction is epi
onto SAME actual cut pushforward coefficient sheaf. -/
theorem affineKoszulHomCoefficientRestrictionPresentation_epi (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    Epi (affineKoszulHomCoefficientRestrictionPresentation R N n H).g := by
  letI := tildeKoszulHomCoefficientRestrictionPresentation_epi R N n H
  change Epi ((affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv ≫
    (tildeKoszulHomCoefficientRestrictionPresentation R N n H).g)
  infer_instance

/-- ACTUAL general-N internal-Hom restriction agrees with SAME original
coefficient quotient restriction under SAME original term identification. -/
theorem affineKoszulHomCoefficientRestrictionPresentation_restriction (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
      (affineKoszulHomCoefficientRestrictionPresentation R N n H).g =
        (tildeKoszulHomCoefficientRestrictionPresentation R N n H).g := by
  change (affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).hom ≫
    ((affineKoszulTermHomCoefficientIso R N (n+1) (n+1)).inv ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

end LinearStudy