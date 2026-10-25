module
public import Linear.PolynomialPointOriginalLocalTrace
public import Linear.NativeLocalizedSourceFiberPoints
public import Linear.NativeLocalizedSourceReducedFiber
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory TensorProduct
universe u
/-- Only ORIGINAL closed-fiber reducedness and ORIGINAL source-point
local CM/dimension at EVERY original point above y are inputs. Actual
localized reducedness,point identification and local freeness are DERIVED.
SAME original C,source projector and literal eval1 retained. Original
geometric chart/Ext/top-H calibration remain OPEN. -/
theorem polynomial_point_original_coextension_trace_one_of_original_fiber
    {K S : Type u} [Field K] [CommRing S] {r : ℕ}
    [Algebra (MvPolynomial (Fin r) K) S] [Module.Finite (MvPolynomial (Fin r) K) S]
    (y : Fin r → K)
    (hred : let R := MvPolynomial (Fin r) K
      let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
      IsReduced (S ⧸ m.map (algebraMap R S)))
    (hgeom : ∀ (p : Ideal S) (_ : p.IsMaximal),
      p.comap (algebraMap (MvPolynomial (Fin r) K) S)=
        RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom →
      IsCohenMacaulayLocalRing (Localization.AtPrime p) ∧
        (r : WithBot ℕ∞)=ringKrullDim (Localization.AtPrime p)) :
    let R := MvPolynomial (Fin r) K
    letI : Algebra R K := (MvPolynomial.aeval (R:=K) y).toRingHom.toAlgebra
    ∀ e : K ⊗[R] S,e ≠ 0 → e*e=e →
      ∃ z : K ⊗[R] ((ModuleCat.restrictScalars (algebraMap R S)).obj
        ((ModuleCat.coextendScalars (algebraMap R S)).obj (ModuleCat.of R R))),
        coextensionOriginalResidueFiberPointEnd
          (show Function.Surjective (algebraMap R K) from
            fun a => ⟨MvPolynomial.C a,by
              change (MvPolynomial.aeval (R:=K) y) (MvPolynomial.C a)=a
              exact (MvPolynomial.aeval (R:=K) y).commutes a⟩) e z=z ∧
          coextensionOriginalBaseChangedEvaluationAtOne (R:=R) (S:=S) (K:=K) z=1 := by
  let R := MvPolynomial (Fin r) K
  let m := RingHom.ker (MvPolynomial.aeval (R:=K) y).toRingHom
  have hres : Function.Surjective (MvPolynomial.aeval (R:=K) y).toRingHom :=
    fun a => ⟨MvPolynomial.C a,(MvPolynomial.aeval (R:=K) y).commutes a⟩
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hres
  refine polynomial_point_original_coextension_trace_one_of_original_points y ?_ ?_
  · letI : IsReduced (S ⧸ m.map (algebraMap R S)) := hred
    exact nativeLocalizedSourceClosedFiber_reduced (S:=S) m
  · dsimp only
    intro p hp
    letI : p.IsMaximal := hp
    let q := p.comap (LocalizedModule.numeratorRingHom (S:=m.primeCompl) (A:=S))
    exact hgeom q (nativeLocalizedSourcePoint_original_maximal m p)
      (nativeLocalizedSourcePoint_base_comap m p)
end LinearStudy
