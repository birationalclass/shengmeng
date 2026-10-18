module

public import Linear.KoszulTop
public import Linear.KoszulResolution

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace LinearStudy
variable {R : Type*} [CommRing R] (n : ℕ)

theorem koszul_top_differential_functional_mem
    (H : Fin (n + 1) → R)
    (L : (⋀[R]^n (Fin (n + 1) → R)) →ₗ[R] R) :
    L (koszulComplex.d (Fintype.linearCombination R H) n
      (topKoszulGenerator (n + 1))) ∈ Ideal.span (Set.range H) := by
  classical
  rw [topKoszulGenerator, koszulComplex.d,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    koszulComplex.dAlternating_apply, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  simp only [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul]
  change ((-1 : R) ^ (i : ℕ) * H i) * _ ∈ _
  apply Ideal.mul_mem_right
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

theorem homotopic_koszul_top_coordinates_congr
    (H : Fin (n + 1) → R)
    (f g : koszulComplex (Fintype.linearCombination R H) ⟶
      koszulComplex (Fintype.linearCombination R H))
    (ht : Homotopy f g) :
    topKoszulCoordinate (n + 1) ((f.f (n + 1)).hom (topKoszulGenerator (n + 1))) -
      topKoszulCoordinate (n + 1) ((g.f (n + 1)).hom (topKoszulGenerator (n + 1)))
        ∈ Ideal.span (Set.range H) := by
  classical
  have hz : IsZero ((koszulComplex (Fintype.linearCombination R H)).X (n + 2)) :=
    koszulComplex.isZero_X_of_card_generators_lt _ (Pi.basisFun R (Fin (n + 1)))
      (Pi.basisFun R (Fin (n + 1))).span_eq (n + 2) (by simp)
  have hc := ht.comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
    hz.eq_of_tgt (ht.hom (n + 1) (n + 2)) 0, zero_comp, add_zero] at hc
  have he := congrArg (fun k => topKoszulCoordinate (n + 1)
      (k.hom (topKoszulGenerator (n + 1)))) hc
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.comp_apply, map_add, koszulComplex.d_eq_d] at he
  change _ = topKoszulCoordinate (n + 1)
      (((ht.hom n (n + 1)).hom)
        (koszulComplex.d (Fintype.linearCombination R H) n
          (topKoszulGenerator (n + 1)))) + _ at he
  rw [sub_eq_iff_eq_add.mpr he]
  exact koszul_top_differential_functional_mem n H
    ((topKoszulCoordinate (n + 1)).comp (ht.hom n (n + 1)).hom)

end LinearStudy
