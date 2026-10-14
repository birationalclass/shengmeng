module
public import Linear.KoszulTopDualCokernelRestriction
public import Linear.TildeKoszulPresentation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

/-- ACTUAL ORIGINAL dual-top boundaries vanish under ORIGINAL restriction. -/
theorem koszulTopFunctionalRestriction_comp_dualDifferential
    {R : Type u} [CommRing R] (n : ℕ) (H : Fin (n+1) → R) :
    (koszulTopFunctionalRestriction n H).comp
      (koszulComplex.d (Fintype.linearCombination R H) n).dualMap=0 := by
  apply LinearMap.ext
  intro L
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (koszul_top_differential_functional_mem n H L)

/-- The ACTUAL ORIGINAL dual-top module presentation,ending in the
ORIGINAL cut R/(H),with original top-coefficient restriction. -/
def koszulDualTopRestrictionModulePresentation (R : CommRingCat.{u})
    (n : ℕ) (H : Fin (n+1) → R) : ShortComplex (ModuleCat.{u} R) where
  X₁ := ModuleCat.of R (Module.Dual R (⋀[R]^n (Fin (n+1) → R)))
  X₂ := ModuleCat.of R (Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R)))
  X₃ := ModuleCat.of R (R ⧸ Ideal.span (Set.range H))
  f := ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) n).dualMap
  g := ModuleCat.ofHom (koszulTopFunctionalRestriction n H)
  zero := ModuleCat.hom_ext (koszulTopFunctionalRestriction_comp_dualDifferential n H)

theorem koszulDualTopRestrictionModulePresentation_exact (R : CommRingCat.{u})
    (n : ℕ) (H : Fin (n+1) → R) :
    (koszulDualTopRestrictionModulePresentation R n H).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ L, koszulTopFunctionalRestriction n H L=0 →
    ∃ F, (koszulComplex.d (Fintype.linearCombination R H) n).dualMap F=L
  intro L hL
  change L ∈ LinearMap.ker (koszulTopFunctionalRestriction n H) at hL
  rw [koszulTopFunctionalRestriction_kernel n H] at hL
  exact hL

/-- The ACTUAL affine associated-sheaf dual-top presentation ends in
the ACTUAL original closed-cut structure sheaf pushed forward along
Spec(R/(H))->Spec(R). Original quotient/ring maps are retained. This
still requires the internal sheaf-Hom and global extension bridges. -/
def tildeKoszulDualTopRestrictionPresentation (R : CommRingCat.{u})
    (n : ℕ) (H : Fin (n+1) → R) : ShortComplex (Spec R).Modules where
  X₁ := tilde (ModuleCat.of R (Module.Dual R (⋀[R]^n (Fin (n+1) → R))))
  X₂ := tilde (ModuleCat.of R (Module.Dual R (⋀[R]^(n+1) (Fin (n+1) → R))))
  X₃ := (Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span (Set.range H)))))).obj
      (SheafOfModules.unit.{u}
        (Spec (CommRingCat.of (R ⧸ Ideal.span (Set.range H)))).ringCatSheaf)
  f := (tilde.functor R).map
    (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) n).dualMap)
  g := (tilde.functor R).map (ModuleCat.ofHom (koszulTopFunctionalRestriction n H)) ≫
    (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom
  zero := by
    have h : ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) n).dualMap ≫
        ModuleCat.ofHom (koszulTopFunctionalRestriction n H)=0 :=
      ModuleCat.hom_ext (koszulTopFunctionalRestriction_comp_dualDifferential n H)
    calc
      _ = (tilde.functor R).map
          (ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) n).dualMap ≫
            ModuleCat.ofHom (koszulTopFunctionalRestriction n H)) ≫
          (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom := by
        rw [Functor.map_comp,Category.assoc]
      _ = 0 := by rw [h,Functor.map_zero,zero_comp]

/-- ACTUAL affine dual-top sheaf restriction is exact. Exactness is
DERIVED from ORIGINAL module kernel/image equality and the already
proved actual tilde exact functor,not supplied as a certificate. -/
theorem tildeKoszulDualTopRestrictionPresentation_exact (R : CommRingCat.{u})
    (n : ℕ) (H : Fin (n+1) → R) :
    (tildeKoszulDualTopRestrictionPresentation R n H).Exact := by
  letI := tilde_functor_preservesHomology R
  have h := (koszulDualTopRestrictionModulePresentation_exact R n H).map (tilde.functor R)
  apply (ShortComplex.exact_iff_of_iso ?_).mp h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (tildeQuotientPushforwardIso R (Ideal.span (Set.range H)))
    (by simp [koszulDualTopRestrictionModulePresentation,tildeKoszulDualTopRestrictionPresentation])
    (by simp [koszulDualTopRestrictionModulePresentation,tildeKoszulDualTopRestrictionPresentation])

/-- ORIGINAL affine coefficient restriction onto the ACTUAL original
closed-cut structure sheaf is an epimorphism. -/
theorem tildeKoszulDualTopRestrictionPresentation_epi (R : CommRingCat.{u})
    (n : ℕ) (H : Fin (n+1) → R) :
    Epi (tildeKoszulDualTopRestrictionPresentation R n H).g := by
  letI := tilde_functor_preservesHomology R
  letI : Epi (ModuleCat.ofHom (koszulTopFunctionalRestriction n H)) :=
    (ModuleCat.epi_iff_surjective _).mpr (koszulTopFunctionalRestriction_surjective n H)
  change Epi ((tilde.functor R).map (ModuleCat.ofHom (koszulTopFunctionalRestriction n H)) ≫
    (tildeQuotientPushforwardIso R (Ideal.span (Set.range H))).hom)
  infer_instance

end LinearStudy
