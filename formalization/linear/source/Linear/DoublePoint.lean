module

public import Linear.Primitive
public import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# A constructive square-zero family

For A = B ⊕ Bε with ε² = 0, the coefficient of ε gives an explicitly
constructed perfect multiplication pairing. There is no pairing-existence
hypothesis in the results of this file. An identification with a power-series
presentation B[[z]]/(z²) is not claimed to have been formalized here.
-/

@[expose] public section

namespace LinearStudy

variable (B : Type*) [CommRing B]

abbrev DoublePoint := TrivSqZeroExt B B

def epsilon : DoublePoint B := TrivSqZeroExt.inr 1

theorem doublePoint_decomposition (a : DoublePoint B) :
    a = a.fst • (1 : DoublePoint B) + a.snd • epsilon B := by
  ext <;> simp [epsilon, smul_eq_mul]

/-- Multiplication followed by the ε coefficient, with x fixed. -/
def doublePointPairingMap (x : DoublePoint B) : DoublePoint B →ₗ[B] B where
  toFun a := x.fst * a.snd + x.snd * a.fst
  map_add' a b := by simp [mul_add]; ring
  map_smul' b a := by simp [smul_eq_mul]; ring

/-- Construct the perfect pairing by exchanging the two coordinate values. -/
noncomputable def doublePointPerfectPairing :
    PerfectMultiplicationPairing (B := B) (A := DoublePoint B) where
  functional := TrivSqZeroExt.sndHom B B
  equiv :=
    { toFun := doublePointPairingMap B
      invFun := fun g => (g (epsilon B), g 1)
      left_inv := by
        intro x
        ext <;> simp [doublePointPairingMap, epsilon]
      right_inv := by
        intro g
        ext a
        change g (epsilon B) * a.snd + g 1 * a.fst = g a
        conv_rhs => rw [doublePoint_decomposition B a]
        rw [map_add, map_smul, map_smul]
        simp only [smul_eq_mul]
        ring
      map_add' := by
        intro x y
        ext a
        simp [doublePointPairingMap, add_mul]
        ring
      map_smul' := by
        intro b x
        ext a
        simp [doublePointPairingMap, smul_eq_mul]
        ring }
  equiv_apply := by
    intro x a
    change x.fst * a.snd + x.snd * a.fst = (x * a).snd
    simp [TrivSqZeroExt.snd_mul, smul_eq_mul]

/-- Over a reduced base, the square-zero kernel is exactly the nilradical. -/
theorem doublePoint_nilradical [IsReduced B] :
    nilradical (DoublePoint B) = TrivSqZeroExt.kerIdeal B B := by
  ext a
  rw [mem_nilradical]
  change IsNilpotent a ↔ a.fst = 0
  constructor
  · intro ha
    exact (ha.map (TrivSqZeroExt.fstHom B B B).toRingHom).eq_zero
  · intro ha
    refine ⟨2, ?_⟩
    ext <;> simp [pow_two, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha]

theorem doublePoint_epsilon_is_dualGenerator :
    dualGenerator (TrivSqZeroExt.fstHom B B B) (doublePointPerfectPairing B) =
      epsilon B := by
  apply (doublePointPerfectPairing B).equiv.injective
  unfold dualGenerator
  rw [LinearEquiv.apply_symm_apply]
  ext a
  change a.fst = (epsilon B).fst * a.snd + (epsilon B).snd * a.fst
  simp [epsilon]

/-- The actual square-zero kernel has a generator, with no pairing input. -/
theorem doublePoint_annihilator_generated (x : DoublePoint B) :
    x ∈ (TrivSqZeroExt.kerIdeal B B).annihilator ↔ ∃ b : B, x = b • epsilon B := by
  rw [← annihilates_iff_mem_annihilator]
  change Annihilates (RingHom.ker (TrivSqZeroExt.fstHom B B B).toRingHom) x ↔ _
  rw [annihilator_iff_scalar_multiple _ (doublePointPerfectPairing B),
    doublePoint_epsilon_is_dualGenerator]

/-- The relative annihilator conclusion for this concrete reduced-base family. -/
theorem doublePoint_nilradical_annihilator [IsReduced B] (x : DoublePoint B) :
    x ∈ (nilradical (DoublePoint B)).annihilator ↔ ∃ b : B, x = b • epsilon B := by
  rw [doublePoint_nilradical]
  exact doublePoint_annihilator_generated B x

/-- The generator survives every quotient controlled by a proper base ideal. -/
theorem doublePoint_quotient_generator_nonzero (J : Ideal (DoublePoint B))
    (m : Ideal B) (hm : m ≠ ⊤)
    (hJ : ∀ a ∈ J, a.snd ∈ m) :
    Ideal.Quotient.mk J (epsilon B) ≠ 0 := by
  rw [← doublePoint_epsilon_is_dualGenerator]
  exact dualGenerator_quotient_nonzero (TrivSqZeroExt.fstHom B B B)
    (doublePointPerfectPairing B) J m (by simpa only [Ideal.ne_top_iff_one] using hm) hJ

/-- The normalized socle-evaluation mechanism in this family. -/
theorem doublePoint_residue_to_evaluation (a : DoublePoint B) :
    (TrivSqZeroExt.sndHom B B) (epsilon B * a) = a.fst := by
  simp [epsilon, TrivSqZeroExt.snd_mul, smul_eq_mul]

end LinearStudy
