/-
Adapted from CBirkbeck/AINTLIB at ab1451487da02cd4483d0e2cdb2cc9e44bbbac17,
ModularCurves/ForMathlib/SheafCohomologyExact.lean.
Released under Apache 2.0; the upstream statement uses actual mathlib
sheaf cohomology and its actual connecting morphism.
-/
module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LinearStudy
open CategoryTheory Opposite
universe w' w v u

/-- Let 0 -> A -> B -> C -> 0 be an ACTUAL short exact sequence of
additive sheaves. If H^1(A)=0, then B(T) -> C(T) is surjective at the
terminal object T. This is the exact-sequence step required after Serre
vanishing in original Lemma4.2; no eventual vanishing is assumed proven. -/
theorem sheafShortExact_sections_surjective_of_H1_vanish
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact)
    {T : C} (hT : Limits.IsTerminal T)
    [Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1)] :
    Function.Surjective (S.g.hom.app (op T)) :=
  fun x => CategoryTheory.Sheaf.H.longSequence_equiv₀_exact₃ hS hT x
    (Subsingleton.elim _ _)
end LinearStudy
