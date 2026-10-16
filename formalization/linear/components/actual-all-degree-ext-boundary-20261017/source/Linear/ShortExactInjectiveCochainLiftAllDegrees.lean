module
public import Linear.ShortExactInjectiveCochainLift
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

/-- In EVERY integer degree q,CONSTRUCT actual cochain lifts through a short
exact source sequence when K^q is injective. No source lift or class equality
is supplied. The all-degree cone CLASS/sign calculation is separate. -/
theorem shortExactInjectiveCochainLift_allDegrees_exists
    (S : ShortComplex A) (hS : S.ShortExact) (K : CochainComplex A ℤ)
    (q : ℤ) [Injective (K.X q)]
    (a : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₁) K q) :
    ∃ (b : Cochain ((CochainComplex.singleFunctor A 0).obj S.X₂) K q)
      (c : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₃) K (q+1)),
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.f)).comp b (zero_add q) =
        a.val ∧
      δ q (q+1) b = (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp
        c.val (zero_add (q+1)) := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  obtain ⟨a0,ha0,haeq⟩ := Cocycle.fromSingleMk_surjective a q (zero_add q) (q+1) rfl
  have hae : Cochain.fromSingleMk a0 (zero_add q) = a.val :=
    congrArg (fun z : Cocycle ((CochainComplex.singleFunctor A 0).obj S.X₁) K q => z.val) haeq
  let b0 := Injective.factorThru a0 S.f
  have hb0 : S.f ≫ b0 = a0 := Injective.comp_factorThru a0 S.f
  have hz : S.f ≫ (b0 ≫ K.d q (q+1)) = 0 := by rw [← Category.assoc,hb0,ha0]
  let c0 := hS.exact.desc (b0 ≫ K.d q (q+1)) hz
  have hc0 : S.g ≫ c0 = b0 ≫ K.d q (q+1) := hS.exact.g_desc _ _
  have hcc : c0 ≫ K.d (q+1) (q+1+1) = 0 := by
    apply (cancel_epi S.g).mp
    rw [← Category.assoc,hc0,Category.assoc,K.d_comp_d,comp_zero,comp_zero]
  refine ⟨Cochain.fromSingleMk b0 (zero_add q),
    Cocycle.fromSingleMk c0 (zero_add (q+1)) (q+1+1) rfl hcc,?_,?_⟩
  · rw [← Cochain.fromSingleMk_precomp,hb0]
    exact hae
  · change δ q (q+1) (Cochain.fromSingleMk b0 (zero_add q)) =
      (Cochain.ofHom ((CochainComplex.singleFunctor A 0).map S.g)).comp
        (Cochain.fromSingleMk c0 (zero_add (q+1))) (zero_add (q+1))
    rw [Cochain.δ_fromSingleMk b0 (zero_add q) (q+1) (q+1) (zero_add (q+1)),
      ← Cochain.fromSingleMk_precomp,hc0]

end LinearStudy
