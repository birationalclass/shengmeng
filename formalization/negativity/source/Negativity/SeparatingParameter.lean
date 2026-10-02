module

public import Mathlib.FieldTheory.TranscendentalSeparable
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open scoped IntermediateField
set_option backward.isDefEq.respectTransparency false

/-- A finitely generated one-variable function field over a perfect field
has an actual transcendental generator over which the remaining extension
is finite and separable, in arbitrary characteristic. -/
theorem exists_finite_separable_transcendental_parameter
    (k L : Type*) [Field k] [PerfectField k] [Field L] [Algebra k L]
    [Algebra.EssFiniteType k L] (hd : Algebra.trdeg k L = 1) :
    ∃ t : L, Transcendental k t ∧
      FiniteDimensional k⟮t⟯ L ∧ Algebra.IsSeparable k⟮t⟯ L := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L
  have hc : s.card = 1 := by
    have hcard := hs.cardinalMk_eq_trdeg.trans hd
    simp only [Cardinal.mk_fintype, Fintype.card_coe] at hcard
    exact_mod_cast hcard
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hc
  have hmem : t ∈ s := ht.symm ▸ Finset.mem_singleton_self t
  have htrans := hs.1.transcendental (⟨t, hmem⟩ : s)
  have hset : (s : Set L) = {t} := by simp only [ht, Finset.coe_singleton]
  rw [hset] at hsep
  have hsep' : Algebra.IsSeparable k⟮t⟯ L := hsep
  have := hsep'
  have : Algebra.EssFiniteType k⟮t⟯ L := Algebra.EssFiniteType.of_comp k k⟮t⟯ L
  exact ⟨t, htrans, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep'⟩

/-- Final theorem: construct the compatible embedding k(t)→L itself,
with finiteness and separability under its induced algebra structure.
Perfectness is required only for the actual constant field k, not k(t).
For an actual curve, deriving essential finite type and transcendence degree
one from its finite-type Scheme geometry remains a separate bridge. -/
theorem exists_compatible_finite_separable_ratFunc_embedding
    (k L : Type*) [Field k] [PerfectField k] [Field L] [Algebra k L]
    [Algebra.EssFiniteType k L] (hd : Algebra.trdeg k L = 1) :
    ∃ f : RatFunc k →ₐ[k] L,
      letI : Algebra (RatFunc k) L := f.toRingHom.toAlgebra
      FiniteDimensional (RatFunc k) L ∧ Algebra.IsSeparable (RatFunc k) L := by
  obtain ⟨t, ht, hfin, hsep⟩ := exists_finite_separable_transcendental_parameter k L hd
  let e := RatFunc.algEquivOfTranscendental t ht
  let f : RatFunc k →ₐ[k] L := (IntermediateField.adjoin k {t}).val.comp e.toAlgHom
  refine ⟨f, ?_⟩
  let : Algebra (RatFunc k) L := f.toRingHom.toAlgebra
  have := hfin
  have := hsep
  exact ⟨Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) (by
    ext x
    change (e (e.symm x) : L) = (x : L)
    rw [e.apply_symm_apply]),
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) (by
      ext x
      change (e (e.symm x) : L) = (x : L)
      rw [e.apply_symm_apply])⟩

end Negativity
