module
public import Linear.ConormalGenerators
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy

theorem extension_cotangent_free_of_formallySmooth {K S : Type*}
    [CommRing K] [CommRing S] [Algebra K S] [IsLocalRing S]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    [Algebra.FormallySmooth K S]
    (hP : P.ker.FG) : Module.Free S P.Cotangent := by
  obtain ⟨l, hl⟩ :=
    (Algebra.Extension.formallySmooth_iff_split_injection P).mp inferInstance
  let : Module.Projective S P.CotangentSpace := inferInstance
  let : Module.Projective S P.Cotangent := Module.Projective.of_split P.cotangentComplex l hl
  let : Module.Finite S P.Cotangent := Algebra.Extension.Cotangent.finite (P := P) hP
  exact Module.free_of_flat_of_isLocalRing

theorem exists_local_extension_generators_of_cotangent_basis {K S ι : Type*}
    [CommRing K] [CommRing S] [Algebra K S]
    (P : Algebra.Extension K S) [IsNoetherianRing P.Ring] [IsLocalRing P.Ring]
    (hP : P.ker ≠ ⊤) (b : Module.Basis ι S P.Cotangent) :
    ∃ G : ι → P.ker,
      (∀ i, Algebra.Extension.Cotangent.mk (G i) = b i) ∧
      Ideal.span (Set.range (fun i => (G i : P.Ring))) = P.ker := by
  choose G hG using fun i => Algebra.Extension.Cotangent.mk_surjective (b i)
  refine ⟨G, hG, ideal_generators_of_conormal_span P.ker hP G ?_⟩
  have hs : Submodule.span P.Ring (Set.range (fun i =>
      Algebra.Extension.Cotangent.mk (G i))) = ⊤ := by
    rw [← Submodule.restrictScalars_span P.Ring S P.algebraMap_surjective]
    simp_rw [hG]
    rw [b.span_eq, Submodule.restrictScalars_top]
  have hm := congrArg (Submodule.map P.cotangentEquivCotangentKer.toLinearMap) hs
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearMap.range_eq_top_of_surjective _ P.cotangentEquivCotangentKer.surjective] at hm
  exact hm

theorem exists_local_extension_generators_of_formallySmooth {K S : Type*}
    [CommRing K] [CommRing S] [Algebra K S] [IsLocalRing S]
    (P : Algebra.Extension K S) [IsNoetherianRing P.Ring] [IsLocalRing P.Ring]
    [Algebra.FormallySmooth K P.Ring] [Algebra.FormallySmooth K S]
    (hP : P.ker ≠ ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) S P.Cotangent) (G : Fin n → P.ker),
      (∀ i, Algebra.Extension.Cotangent.mk (G i) = b i) ∧
      Ideal.span (Set.range (fun i => (G i : P.Ring))) = P.ker := by
  let : Module.Finite S P.Cotangent := Algebra.Extension.Cotangent.finite
    (P := P) (IsNoetherian.noetherian P.ker)
  let : Module.Free S P.Cotangent := extension_cotangent_free_of_formallySmooth P
    (IsNoetherian.noetherian P.ker)
  let b := Module.finBasis S P.Cotangent
  obtain ⟨G, hG, hs⟩ := exists_local_extension_generators_of_cotangent_basis P hP b
  exact ⟨Module.finrank S P.Cotangent, b, G, hG, hs⟩

end LinearStudy
