module

public import Linear.Vendor.KoszulComplex
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open RingTheory.Sequence
namespace LinearStudy

variable {R : Type*} [CommRing R]

def koszulAugmentation (rs : List R) :
    (⋀[R]^0 (Fin rs.length → R)) →ₗ[R] R ⧸ Ideal.ofList rs :=
  (Ideal.Quotient.mkₐ R (Ideal.ofList rs)).toLinearMap.comp
    (exteriorPower.zeroEquiv R (Fin rs.length → R)).toLinearMap

theorem koszulAugmentation_comp_d (rs : List R) :
    (koszulAugmentation rs).comp (koszulComplex.d (Fintype.linearCombination R rs.get) 0) = 0 := by
  rw [koszulAugmentation, LinearMap.comp_assoc,
    koszulComplex.equiv_comp_koszulComplex.d_zero_eq]
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk (Ideal.ofList rs)
    (Fintype.linearCombination R rs.get (exteriorPower.oneEquiv R _ x)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  have hr : (Fintype.linearCombination R rs.get).range = Ideal.ofList rs := by
    simp [Fintype.range_linearCombination, Ideal.ofList]
  rw [← hr]
  exact LinearMap.mem_range_self _ _

def koszulAugmentationMap (rs : List R) :
    koszulComplex.ofList rs ⟶ (ChainComplex.single₀ (ModuleCat R)).obj
      (ModuleCat.of R (R ⧸ Ideal.ofList rs)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom (koszulAugmentation rs), by
    change ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R rs.get) 0) ≫ _ = 0
    exact ModuleCat.hom_ext (koszulAugmentation_comp_d rs)⟩

theorem koszulAugmentation_exact (rs : List R) :
    (ShortComplex.mk (koszulComplex.ofList rs |>.d 1 0)
      (ModuleCat.ofHom (koszulAugmentation rs))
      (by change ModuleCat.ofHom (koszulComplex.d (Fintype.linearCombination R rs.get) 0) ≫ _ = 0
          exact ModuleCat.hom_ext (koszulAugmentation_comp_d rs))).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ x : ⋀[R]^0 (Fin rs.length → R), koszulAugmentation rs x = 0 →
    ∃ y : ⋀[R]^1 (Fin rs.length → R),
      koszulComplex.d (Fintype.linearCombination R rs.get) 0 y = x
  intro x hx
  have hx' : exteriorPower.zeroEquiv R (Fin rs.length → R) x ∈ Ideal.ofList rs := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  have hr : (Fintype.linearCombination R rs.get).range = Ideal.ofList rs := by
    simp [Fintype.range_linearCombination, Ideal.ofList]
  rw [← hr] at hx'
  obtain ⟨v, hv⟩ := hx'
  refine ⟨(exteriorPower.oneEquiv R _).symm v, ?_⟩
  apply (exteriorPower.zeroEquiv R _).injective
  change exteriorPower.zeroEquiv R (Fin rs.length → R)
      (koszulComplex.d (Fintype.linearCombination R rs.get) 0
        ((exteriorPower.oneEquiv R _).symm v)) = _
  have he := LinearMap.congr_fun
    (koszulComplex.equiv_comp_koszulComplex.d_zero_eq (Fintype.linearCombination R rs.get))
    ((exteriorPower.oneEquiv R _).symm v)
  exact he.trans (by simpa using hv)

def regularKoszulResolution (rs : List R) (hreg : IsRegular R rs) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList rs)) where
  complex := koszulComplex.ofList rs
  projective n := ModuleCat.projective_of_free ((Pi.basisFun R (Fin rs.length)).exteriorPower n)
  π := koszulAugmentationMap rs
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      ·
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨koszulAugmentation_exact rs, ?_⟩
        · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
            (by simp [koszulAugmentationMap, ChainComplex.toSingle₀Equiv_symm_apply_f_zero])
        · apply (ModuleCat.epi_iff_surjective _).mpr
          intro x
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
          refine ⟨(exteriorPower.zeroEquiv R _).symm y, ?_⟩
          change Ideal.Quotient.mk (Ideal.ofList rs)
            ((exteriorPower.zeroEquiv R _)
              ((exteriorPower.zeroEquiv R _).symm y)) = Ideal.Quotient.mk _ y
          rw [LinearEquiv.apply_symm_apply]
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact koszulComplex.exactAt_of_isRegular rs hreg _ (by omega)
      · apply ChainComplex.exactAt_succ_single_obj⟩

end LinearStudy
