module
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Construct the ACTUAL degree-zero cochain lift and degree-one cocycle
for EVERY short exact sequence and EVERY target complex with injective degree0.
No lift,comparison square or desired extension-class equation is assumed. -/
theorem shortExactInjectiveCochainLift_exists (S : ShortComplex A) (hS : S.ShortExact)
    (K : CochainComplex A ℤ) [Injective (K.X 0)]
    (a : (CochainComplex.singleFunctor A 0).obj S.X₁ ⟶ K) :
    ∃ (b : Cochain ((CochainComplex.singleFunctor A 0).obj S.X₂) K 0)
      (c : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₃) K 1),
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.f)).comp b (zero_add 0) =
        Cochain.ofHom a ∧
      δ 0 1 b = (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp c.val
        (zero_add 1) := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  obtain ⟨a0,ha0,haeq⟩ := Cocycle.fromSingleMk_surjective (Cocycle.ofHom a) 0 rfl 1 rfl
  have hae : Cochain.fromSingleMk a0 (zero_add 0) = Cochain.ofHom a :=
    congrArg (fun z : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₁) K 0 => z.val) haeq
  let b0 := Injective.factorThru a0 S.f
  have hb0 : S.f ≫ b0 = a0 := Injective.comp_factorThru a0 S.f
  have hz : S.f ≫ (b0 ≫ K.d 0 1) = 0 := by rw [← Category.assoc,hb0,ha0]
  let c0 := hS.exact.desc (b0 ≫ K.d 0 1) hz
  have hc0 : S.g ≫ c0 = b0 ≫ K.d 0 1 := hS.exact.g_desc _ _
  have hcc : c0 ≫ K.d 1 2 = 0 := by
    apply (cancel_epi S.g).mp
    rw [← Category.assoc,hc0,Category.assoc,K.d_comp_d,comp_zero,comp_zero]
  refine ⟨Cochain.fromSingleMk b0 (zero_add 0),
    Cocycle.fromSingleMk c0 (zero_add 1) 2 rfl hcc,?_,?_⟩
  · rw [← Cochain.fromSingleMk_precomp,hb0]
    exact hae
  · change δ 0 1 (Cochain.fromSingleMk b0 (zero_add 0)) =
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp
        (Cochain.fromSingleMk c0 (zero_add 1)) (zero_add 1)
    rw [Cochain.δ_fromSingleMk b0 (zero_add 0) 1 1 (zero_add 1),
      ← Cochain.fromSingleMk_precomp,hc0]

end LinearStudy
