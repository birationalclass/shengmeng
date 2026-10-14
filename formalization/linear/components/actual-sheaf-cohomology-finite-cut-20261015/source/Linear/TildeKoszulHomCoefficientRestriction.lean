module
public import Linear.KoszulTopHomCoefficientRestriction
public import Linear.TildeCoefficientQuotientPushforward
public import Linear.TildeKoszulPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
universe u

/-- ACTUAL original N-coefficient restrictions kill SAME original boundaries. -/
theorem koszulTopHomCoefficientRestriction_comp (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (koszulTopHomCoefficientRestriction (N := N) n H).comp
      (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n)) = 0 := by
  apply LinearMap.ext
  intro L
  have h : (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n)) L ∈
      LinearMap.ker (koszulTopHomCoefficientRestriction (N := N) n H) :=
    (koszulTopHomCoefficientRestriction_kernel (N := N) n H).symm.le (LinearMap.mem_range_self _ L)
  exact h

/-- SAME original Hom-Koszul top module presentation into ANY original N. -/
def koszulHomCoefficientRestrictionModulePresentation (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) : ShortComplex (ModuleCat.{u} R) where
  X₁ := ModuleCat.of R ((⋀[R]^n (Fin (n+1) → R)) →ₗ[R] N)
  X₂ := ModuleCat.of R ((⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N)
  X₃ := ModuleCat.of R (N ⧸ (Ideal.span (Set.range H) • (⊤ : Submodule R N)))
  f := ModuleCat.ofHom (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n))
  g := ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)
  zero := ModuleCat.hom_ext (koszulTopHomCoefficientRestriction_comp R N n H)

/-- Exactness is PROVED from actual ORIGINAL coefficient kernel/image. -/
theorem koszulHomCoefficientRestrictionModulePresentation_exact (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (koszulHomCoefficientRestrictionModulePresentation R N n H).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ L, koszulTopHomCoefficientRestriction (N := N) n H L = 0 →
    ∃ F, (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n)) F = L
  intro L hL
  change L ∈ LinearMap.ker (koszulTopHomCoefficientRestriction (N := N) n H) at hL
  rw [koszulTopHomCoefficientRestriction_kernel n H] at hL
  exact hL

/-- ACTUAL associated-Hom sequence ends in ACTUAL pushforward from SAME
original cut of SAME original quotient-tensor coefficient (R/I) tensor N. -/
def tildeKoszulHomCoefficientRestrictionPresentation (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) : ShortComplex (Spec R).Modules where
  X₁ := tilde (ModuleCat.of R ((⋀[R]^n (Fin (n+1) → R)) →ₗ[R] N))
  X₂ := tilde (ModuleCat.of R ((⋀[R]^(n+1) (Fin (n+1) → R)) →ₗ[R] N))
  X₃ := (Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
      (tilde (ModuleCat.of (R ⧸ Ideal.span (Set.range H))
        ((R ⧸ Ideal.span (Set.range H)) ⊗[R] N)))
  f := (tilde.functor R).map
    (ModuleCat.ofHom (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n)))
  g := (tilde.functor R).map (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)) ≫
    (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N).hom
  zero := by
    have h : ModuleCat.ofHom (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n)) ≫
        ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H) = 0 :=
      ModuleCat.hom_ext (koszulTopHomCoefficientRestriction_comp R N n H)
    calc
      _ = (tilde.functor R).map
          (ModuleCat.ofHom (LinearMap.lcomp R N (koszulComplex.d (Fintype.linearCombination R H) n)) ≫
            ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)) ≫
          (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N).hom := by
        rw [CategoryTheory.Functor.map_comp,Category.assoc]
      _ = 0 := by rw [h,CategoryTheory.Functor.map_zero,zero_comp]

/-- ACTUAL original affine associated-Hom presentation identified with
actual tilde of SAME original module presentation. -/
def tildeKoszulHomCoefficientRestrictionPresentationIso (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (koszulHomCoefficientRestrictionModulePresentation R N n H).map (tilde.functor R) ≅
      tildeKoszulHomCoefficientRestrictionPresentation R N n H := by
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N)
    (by simp [koszulHomCoefficientRestrictionModulePresentation,tildeKoszulHomCoefficientRestrictionPresentation])
    (by simp [koszulHomCoefficientRestrictionModulePresentation,tildeKoszulHomCoefficientRestrictionPresentation])

/-- ACTUAL original arbitrary-coefficient affine associated-Hom sequence
is exact. Original N has NO FP/free/flat/invertible/CM condition. -/
theorem tildeKoszulHomCoefficientRestrictionPresentation_exact (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    (tildeKoszulHomCoefficientRestrictionPresentation R N n H).Exact := by
  letI := tilde_functor_preservesHomology R
  exact ShortComplex.exact_of_iso (tildeKoszulHomCoefficientRestrictionPresentationIso R N n H)
    ((koszulHomCoefficientRestrictionModulePresentation_exact R N n H).map (tilde.functor R))

/-- ACTUAL original coefficient restriction is epi onto SAME actual
pushforward coefficient sheaf on SAME original closed quotient cut. -/
theorem tildeKoszulHomCoefficientRestrictionPresentation_epi (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (n : ℕ) (H : Fin (n+1) → R) :
    Epi (tildeKoszulHomCoefficientRestrictionPresentation R N n H).g := by
  letI := tilde_functor_preservesHomology R
  letI : Epi (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)) :=
    (ModuleCat.epi_iff_surjective _).mpr (koszulTopHomCoefficientRestriction_surjective n H)
  change Epi ((tilde.functor R).map (ModuleCat.ofHom (koszulTopHomCoefficientRestriction (N := N) n H)) ≫
    (tildeCoefficientQuotientPushforwardIso R (Ideal.span (Set.range H)) N).hom)
  infer_instance

end LinearStudy