module

public import Linear.KoszulResolution

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits RingTheory.Sequence
namespace LinearStudy
variable {R : Type*} [CommRing R] {n : ℕ}

theorem ideal_ofFn (H : Fin n → R) :
    Ideal.ofList (List.ofFn H) = Ideal.span (Set.range H) := by
  simp [Ideal.ofList, List.mem_ofFn, Set.range]

theorem koszul_ofFn (H : Fin n → R) :
    koszulComplex.ofList (List.ofFn H) = koszulComplex (Fintype.linearCombination R H) := by
  simp only [koszulComplex.ofList]
  have hg : (List.ofFn H).get = H ∘ Fin.cast (List.length_ofFn (f := H)) := by
    funext i
    exact List.get_ofFn H i
  rw [hg]
  have hc : ∀ {m k : ℕ} (h : m = k) (v : Fin k → R),
      koszulComplex (Fintype.linearCombination R (v ∘ Fin.cast h)) =
        koszulComplex (Fintype.linearCombination R v) := by
    intro m k h v
    subst m
    rfl
  exact hc (List.length_ofFn (f := H)) H

def functionKoszulAugmentation (H : Fin n → R) :
    (⋀[R]^0 (Fin n → R)) →ₗ[R] R ⧸ Ideal.span (Set.range H) :=
  (Ideal.Quotient.mkₐ R (Ideal.span (Set.range H))).toLinearMap.comp
    (exteriorPower.zeroEquiv R (Fin n → R)).toLinearMap

theorem functionKoszulAugmentation_comp_d (H : Fin n → R) :
    (functionKoszulAugmentation H).comp
      (koszulComplex.d (Fintype.linearCombination R H) 0) = 0 := by
  rw [functionKoszulAugmentation, LinearMap.comp_assoc,
    koszulComplex.equiv_comp_koszulComplex.d_zero_eq]
  apply LinearMap.ext
  intro v
  change Ideal.Quotient.mk (Ideal.span (Set.range H))
    (Fintype.linearCombination R H (exteriorPower.oneEquiv R _ v)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change _ ∈ Submodule.span R (Set.range H)
  rw [← Fintype.range_linearCombination]
  exact LinearMap.mem_range_self _ _

def functionKoszulAugmentationMap (H : Fin n → R) :
    koszulComplex (Fintype.linearCombination R H) ⟶
      (ChainComplex.single₀ (ModuleCat R)).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (functionKoszulAugmentation H), by
    change ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) 0) ≫ _ = 0
    exact ModuleCat.hom_ext (functionKoszulAugmentation_comp_d H)⟩

theorem functionKoszulAugmentation_exact (H : Fin n → R) :
    (ShortComplex.mk (koszulComplex (Fintype.linearCombination R H) |>.d 1 0)
      (ModuleCat.ofHom (functionKoszulAugmentation H))
      (by change ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R H) 0) ≫ _ = 0
          exact ModuleCat.hom_ext (functionKoszulAugmentation_comp_d H))).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ v : ⋀[R]^0 (Fin n → R), functionKoszulAugmentation H v = 0 →
    ∃ w : ⋀[R]^1 (Fin n → R), koszulComplex.d (Fintype.linearCombination R H) 0 w = v
  intro v hv
  have hv' : exteriorPower.zeroEquiv R (Fin n → R) v ∈ Ideal.span (Set.range H) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hv
  change _ ∈ Submodule.span R (Set.range H) at hv'
  rw [← Fintype.range_linearCombination] at hv'
  obtain ⟨w, hw⟩ := hv'
  refine ⟨(exteriorPower.oneEquiv R _).symm w, ?_⟩
  apply (exteriorPower.zeroEquiv R _).injective
  have he := LinearMap.congr_fun
    (koszulComplex.equiv_comp_koszulComplex.d_zero_eq (Fintype.linearCombination R H))
    ((exteriorPower.oneEquiv R _).symm w)
  exact he.trans (by simpa using hw)

def functionKoszulResolution (H : Fin n → R) (hreg : IsRegular R (List.ofFn H)) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span (Set.range H))) where
  complex := koszulComplex (Fintype.linearCombination R H)
  projective k := ModuleCat.projective_of_free ((Pi.basisFun R (Fin n)).exteriorPower k)
  π := functionKoszulAugmentationMap H
  quasiIso := ⟨fun k => by
    cases k with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨functionKoszulAugmentation_exact H, ?_⟩
        · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
            (by simp [functionKoszulAugmentationMap, ChainComplex.toSingle₀Equiv_symm_apply_f_zero])
        · apply (ModuleCat.epi_iff_surjective _).mpr
          intro v
          obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
          refine ⟨(exteriorPower.zeroEquiv R _).symm w, ?_⟩
          change Ideal.Quotient.mk _ ((exteriorPower.zeroEquiv R _)
            ((exteriorPower.zeroEquiv R _).symm w)) = _
          rw [LinearEquiv.apply_symm_apply]
      all_goals rfl
    | succ k =>
      rw [quasiIsoAt_iff_exactAt']
      · have he := koszulComplex.exactAt_of_isRegular (List.ofFn H) hreg (k + 1) (by omega)
        rw [koszul_ofFn] at he
        exact he
      · apply ChainComplex.exactAt_succ_single_obj⟩

end LinearStudy
