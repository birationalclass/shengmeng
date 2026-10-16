module

public import Linear.KoszulFunctionResolution
public import Linear.KoszulSocleMap
public import Linear.DeterminantAnnihilator
public import Linear.SoclePairing

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open CategoryTheory RingTheory.Sequence
open scoped BigOperators
namespace LinearStudy
variable {R : Type*} [CommRing R] {n : ℕ}

theorem equationIdeal_le_coordinateIdeal (H x : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (h : M.mulVec x = H) :
    Ideal.span (Set.range H) ≤ Ideal.span (Set.range x) := by
  classical
  apply Ideal.span_le.mpr
  rintro a ⟨i, rfl⟩
  rw [← h]
  change ∑ j, M i j * x j ∈ Ideal.span (Set.range x)
  apply Submodule.sum_mem
  intro j hj
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))

def equationQuotientMap (H x : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (h : M.mulVec x = H) :
    (R ⧸ Ideal.span (Set.range H)) →ₗ[R] (R ⧸ Ideal.span (Set.range x)) :=
  Submodule.factor (equationIdeal_le_coordinateIdeal H x M h)

theorem coefficientComparison_augmentation (H x : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (h : M.mulVec x = H) :
    coefficientKoszulComparison H x M h ≫ functionKoszulAugmentationMap x =
      functionKoszulAugmentationMap H ≫ (ChainComplex.single₀ (ModuleCat R)).map
        (ModuleCat.ofHom (equationQuotientMap H x M h)) := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  simp only [ChainComplex.toSingle₀Equiv_apply_coe, HomologicalComplex.comp_f,
    functionKoszulAugmentationMap, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
    ChainComplex.single₀_map_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change functionKoszulAugmentation x
      (exteriorPower.map 0 (Matrix.toLin' M.transpose) v) =
    equationQuotientMap H x M h (functionKoszulAugmentation H v)
  have he := LinearMap.congr_fun
    (exteriorPower.zeroEquiv_naturality (Matrix.toLin' M.transpose)) v
  change Ideal.Quotient.mk _ ((exteriorPower.zeroEquiv R _)
      (exteriorPower.map 0 (Matrix.toLin' M.transpose) v)) =
    Ideal.Quotient.mk _ ((exteriorPower.zeroEquiv R _) v)
  exact congrArg (Ideal.Quotient.mk _) he

theorem equationMap_socleMap_comp (H x : Fin n → R)
    (M : Matrix (Fin n) (Fin n) R) (h : M.mulVec x = H) (a : R)
    (ha : Ideal.Quotient.mk (Ideal.span (Set.range H)) a ∈
      ((Ideal.span (Set.range x)).map
        (Ideal.Quotient.mk (Ideal.span (Set.range H)))).annihilator) :
    (socleQuotientMap _ _ (Ideal.Quotient.mk _ a) ha).comp
      (equationQuotientMap H x M h) = a • LinearMap.id := by
  apply LinearMap.ext
  intro v
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
  change b • Ideal.Quotient.mk _ a = a • Ideal.Quotient.mk _ b
  simp only [Algebra.smul_def]
  exact mul_comm _ _

theorem socle_element_coefficientDeterminant_multiple
    {k : ℕ} (H x : Fin (k + 1) → R)
    (hH : IsRegular R (List.ofFn H)) (hx : IsRegular R (List.ofFn x))
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (h : M.mulVec x = H) (a : R)
    (ha : Ideal.Quotient.mk (Ideal.span (Set.range H)) a ∈
      ((Ideal.span (Set.range x)).map
        (Ideal.Quotient.mk (Ideal.span (Set.range H)))).annihilator) :
    ∃ b : R, Ideal.Quotient.mk (Ideal.span (Set.range H)) a =
      Ideal.Quotient.mk (Ideal.span (Set.range H)) (M.det * b) := by
  classical
  let P := functionKoszulResolution H hH
  let Q := functionKoszulResolution x hx
  let c : koszulComplex (Fintype.linearCombination R H) ⟶
      koszulComplex (Fintype.linearCombination R x) := coefficientKoszulComparison H x M h
  let φ := ModuleCat.ofHom (equationQuotientMap H x M h)
  let ψ := ModuleCat.ofHom
    (socleQuotientMap _ _ (Ideal.Quotient.mk _ a) ha)
  let b : koszulComplex (Fintype.linearCombination R x) ⟶
      koszulComplex (Fintype.linearCombination R H) := ProjectiveResolution.lift ψ Q P
  have hφψ : φ ≫ ψ = a • 𝟙 _ := by
    apply ModuleCat.hom_ext
    exact equationMap_socleMap_comp H x M h a ha
  have hc : c ≫ Q.π = P.π ≫ (ChainComplex.single₀ (ModuleCat R)).map φ :=
    coefficientComparison_augmentation H x M h
  have hb : b ≫ P.π = Q.π ≫ (ChainComplex.single₀ (ModuleCat R)).map ψ :=
    ProjectiveResolution.lift_commutes ψ Q P
  have hg : (c ≫ b) ≫ P.π = P.π ≫
      (ChainComplex.single₀ (ModuleCat R)).map (a • 𝟙 _) := by
    rw [Category.assoc, hb, ← Category.assoc, hc, Category.assoc,
      ← Functor.map_comp, hφψ]
  have hs : (a • 𝟙 P.complex) ≫ P.π = P.π ≫
      (ChainComplex.single₀ (ModuleCat R)).map (a • 𝟙 _) := by
    apply (ChainComplex.toSingle₀Equiv _ _).injective
    apply Subtype.ext
    simp only [ChainComplex.toSingle₀Equiv_apply_coe, HomologicalComplex.comp_f,
      HomologicalComplex.smul_f_apply,
      ChainComplex.single₀_map_f_zero, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp]
    simp
  let ht := ProjectiveResolution.liftHomotopy (a • 𝟙 _) (c ≫ b)
    (a • 𝟙 P.complex) hg hs
  have he := homotopic_koszul_top_coordinates_congr k H (c ≫ b)
    (a • 𝟙 P.complex) ht
  let u := topKoszulCoordinate (k + 1)
    ((b.f (k + 1)).hom (topKoszulGenerator (k + 1)))
  have he' : M.det * u - a ∈ Ideal.span (Set.range H) := by
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at he
    have hct : (c.f (k + 1)).hom (topKoszulGenerator (k + 1)) =
        M.det • topKoszulGenerator (k + 1) := coefficientKoszulComparison_top H x M h _
    rw [hct] at he
    change topKoszulCoordinate (k + 1) ((b.f (k + 1)).hom
        (M.det • topKoszulGenerator (k + 1))) -
      topKoszulCoordinate (k + 1) (a • topKoszulGenerator (k + 1)) ∈ _ at he
    simpa only [u, map_smul, topKoszulCoordinate_generator, smul_eq_mul, mul_one] using he
  refine ⟨u, ?_⟩
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr he'
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

theorem coordinate_annihilator_eq_coefficientDeterminant
    {k : ℕ} (H x : Fin (k + 1) → R)
    (hH : IsRegular R (List.ofFn H)) (hx : IsRegular R (List.ofFn x))
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (h : M.mulVec x = H) :
    ((Ideal.span (Set.range x)).map
        (Ideal.Quotient.mk (Ideal.span (Set.range H)))).annihilator =
      Ideal.span {Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det} := by
  let I := Ideal.span (Set.range H)
  let J := Ideal.span (Set.range x)
  let q := Ideal.Quotient.mk I
  apply le_antisymm
  · intro a ha
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, hb⟩ := socle_element_coefficientDeterminant_multiple H x hH hx M h u ha
    rw [Ideal.mem_span_singleton]
    refine ⟨q b, ?_⟩
    simpa [q, I, map_mul] using hb
  · apply Ideal.span_le.mpr
    rintro a (rfl : a = q M.det)
    have hm := coefficientDeterminant_annihilates_quotient H x M h
    have hm' := (annihilates_iff_mem_annihilator _ _).mp hm
    simpa [Ideal.map_span, ← Set.range_comp, Function.comp_def] using hm'

theorem coefficientDeterminant_ne_zero_of_local_artinian
    {k : ℕ} (H x : Fin (k + 1) → R)
    (hH : IsRegular R (List.ofFn H)) (hx : IsRegular R (List.ofFn x))
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (h : M.mulVec x = H)
    [IsArtinianRing (R ⧸ Ideal.span (Set.range H))]
    [IsLocalRing (R ⧸ Ideal.span (Set.range H))]
    (hm : (Ideal.span (Set.range x)).map (Ideal.Quotient.mk (Ideal.span (Set.range H))) =
      IsLocalRing.maximalIdeal (R ⧸ Ideal.span (Set.range H))) :
    Ideal.Quotient.mk (Ideal.span (Set.range H)) M.det ≠ 0 := by
  obtain ⟨z, hz, hz0, hs⟩ := nonzero_ideal_meets_socle
    (⊤ : Ideal (R ⧸ Ideal.span (Set.range H))) top_ne_bot
  have he := coordinate_annihilator_eq_coefficientDeterminant H x hH hx M h
  rw [hm] at he
  rw [he] at hs
  intro hd
  have hz' : z = 0 := by simpa [hd] using hs
  exact hz0 hz'

end LinearStudy
