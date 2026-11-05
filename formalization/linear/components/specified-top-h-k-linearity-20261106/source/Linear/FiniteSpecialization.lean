module
public import Linear.RegularSpecialization
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite closed fibers of actual relative complete intersections

Use the actual coefficient-specialization quotient map as a surjective
semilinear map. Finiteness of the relative algebra then implies finite
dimension over the coefficient field, without a tensor or closed-fiber
finiteness input. Combining flatness and regularity already proved yields
the constructed perfect pairing and trace formula on this actual fiber.
This still does not identify the coefficient determinant with the Jacobian.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace LinearStudy
variable {B K R S : Type*} [CommRing B] [CommRing K] [CommRing R] [CommRing S]
  [Algebra B R] [Algebra K S]

theorem quotientSpecialization_finite
    (cc : B →+* K) (f : R →+* S) (hf : Function.Surjective f)
    (hcoeff : ∀ b, f (algebraMap B R b) = algebraMap K S (cc b))
    (I : Ideal R) [Module.Finite B (R ⧸ I)] :
    Module.Finite K (S ⧸ I.map f) := by
  let q := quotientSpecialization f I
  let l : (R ⧸ I) →ₛₗ[cc] (S ⧸ I.map f) :=
    { q.toAddMonoidHom with
      map_smul' := by
        intro b a
        change q (b • a) = cc b • q a
        rw [Algebra.smul_def, Algebra.smul_def, q.map_mul]
        congr 1
        change Ideal.Quotient.mk (I.map f) (f (algebraMap B R b)) =
          Ideal.Quotient.mk (I.map f) (algebraMap K S (cc b))
        rw [hcoeff] }
  exact Module.Finite.of_surjective l (quotientSpecialization_surjective f hf I)

theorem powerSeries_specialized_quotient_finite
    {F : Type*} [Field F] {r c : ℕ}
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) F))
    [Module.Finite (MvPowerSeries (Fin (r + 1)) F)
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) F) ⧸ Ideal.span (Set.range H))] :
    FiniteDimensional F (MvPowerSeries (Fin c) F ⧸
      Ideal.span (Set.range (fun i => parameterSpecialization (H i)))) := by
  let f := parameterSpecialization (K := F) (r := r) (c := c)
  have hI : (Ideal.span (Set.range H)).map f =
      Ideal.span (Set.range (fun i => f (H i))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  change Module.Finite F (MvPowerSeries (Fin c) F ⧸
    Ideal.span (Set.range (fun i => f (H i))))
  rw [← hI]
  apply quotientSpecialization_finite (B := MvPowerSeries (Fin (r + 1)) F)
    (K := F) MvPowerSeries.constantCoeff f
    parameterSpecialization_surjective
  intro b
  simp [f, parameterSpecialization, MvPowerSeries.algebraMap_apply]

theorem powerSeries_specialized_quotient_artinian
    {F : Type*} [Field F] {r c : ℕ}
    (H : Fin c → MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) F))
    [Module.Finite (MvPowerSeries (Fin (r + 1)) F)
      (MvPowerSeries (Fin c) (MvPowerSeries (Fin (r + 1)) F) ⧸ Ideal.span (Set.range H))] :
    IsArtinianRing (MvPowerSeries (Fin c) F ⧸
      Ideal.span (Set.range (fun i => parameterSpecialization (H i)))) := by
  let := powerSeries_specialized_quotient_finite H
  exact IsArtinianRing.of_finite F _

theorem finiteFlat_closedFiber_traceElement
    {F : Type*} [Field F] {r n : ℕ}
    (H : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) F))
    (hH : RingTheory.Sequence.IsRegular
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) F)) (List.ofFn H))
    [Module.Finite (MvPowerSeries (Fin (r + 1)) F)
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) F) ⧸ Ideal.span (Set.range H))]
    [Module.Flat (MvPowerSeries (Fin (r + 1)) F)
      (MvPowerSeries (Fin (n + 1)) (MvPowerSeries (Fin (r + 1)) F) ⧸ Ideal.span (Set.range H))] :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPowerSeries (Fin (n + 1)) F),
      M.mulVec MvPowerSeries.X = (fun i => parameterSpecialization (H i)) ∧
      ∃ p : PerfectMultiplicationPairing (B := F)
        (A := MvPowerSeries (Fin (n + 1)) F ⧸
          Ideal.span (Set.range (fun i => parameterSpecialization (H i)))),
        p.functional (Ideal.Quotient.mk _ M.det) = 1 ∧
        traceElement p = Module.finrank F
          (MvPowerSeries (Fin (n + 1)) F ⧸
            Ideal.span (Set.range (fun i => parameterSpecialization (H i)))) •
          Ideal.Quotient.mk _ M.det := by
  let := powerSeries_specialized_quotient_finite H
  let := powerSeries_specialized_quotient_artinian H
  exact powerSeries_completeIntersection_traceElement _
    (powerSeries_specialized_equations_regular H hH)
    (powerSeries_specialized_equations_zeroConstant H hH)

end LinearStudy
