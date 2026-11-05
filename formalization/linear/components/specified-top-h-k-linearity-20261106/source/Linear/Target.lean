module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Artinian.Module
public import Linear.Reduction

/-!
# Exact target for manuscript Lemma 3.1

This file DEFINES the goal. It contains no proof of the full lemma. A checked
Prop definition is not a checked theorem. The ideal in each closed fiber is
required to be maximal, making its annihilator precisely the socle.
-/

@[expose] public section

noncomputable section

namespace LinearStudy

abbrev ParameterRing (r : ℕ) := MvPowerSeries (Fin r) ℂ
abbrev AmbientRing (r c : ℕ) := MvPowerSeries (Fin c) (ParameterRing r)

def equationIdeal {r c : ℕ} (H : Fin c → AmbientRing r c) : Ideal (AmbientRing r c) :=
  Ideal.span (Set.range H)

abbrev CompleteIntersection {r c : ℕ} (H : Fin c → AmbientRing r c) :=
  AmbientRing r c ⧸ equationIdeal H

noncomputable def relativeJacobian {r c : ℕ} (H : Fin c → AmbientRing r c) :
    CompleteIntersection H :=
  Ideal.Quotient.mk (equationIdeal H)
    (Matrix.det (fun i j => MvPowerSeries.pderiv j (H i)))

/-- The complete Lemma 3.1, including arbitrary lifts of a parameter system.
`q` packages A_red ≃ B as a B-algebra: it is automatically split on B, and its
kernel is required to be the nilradical. No perfect pairing is assumed here. -/
def Lemma31Goal (r c : ℕ) : Prop :=
  ∀ (H : Fin c → AmbientRing r c),
    0 < r → 0 < c →
    RingTheory.Sequence.IsRegular (AmbientRing r c) (List.ofFn H) →
    Module.Finite (ParameterRing r) (CompleteIntersection H) →
    Module.Flat (ParameterRing r) (CompleteIntersection H) →
    ∀ (q : CompleteIntersection H →ₐ[ParameterRing r] ParameterRing r),
      RingHom.ker q.toRingHom = nilradical (CompleteIntersection H) →
      (∀ x : CompleteIntersection H,
        Annihilates (nilradical (CompleteIntersection H)) x ↔
          ∃ b : ParameterRing r, x = b • relativeJacobian H) ∧
      (∀ (τ : Fin r → CompleteIntersection H),
        Ideal.span (Set.range (fun i => q (τ i))) =
          IsLocalRing.maximalIdeal (ParameterRing r) →
        let J := Ideal.span (Set.range τ)
        let Q := CompleteIntersection H ⧸ J
        let m := (nilradical (CompleteIntersection H)).map (Ideal.Quotient.mk J)
        IsArtinianRing Q ∧ m.IsMaximal ∧
          m.annihilator = Ideal.span {Ideal.Quotient.mk J (relativeJacobian H)} ∧
          Ideal.Quotient.mk J (relativeJacobian H) ≠ 0)

end LinearStudy
