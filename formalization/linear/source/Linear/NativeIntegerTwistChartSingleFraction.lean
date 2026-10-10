module
public import Linear.NativeProjectiveTwistSectionEquiv
public import Linear.NativeProjectiveChartSections
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
namespace LinearStudy
open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
universe u
variable {K S : Type u} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local instance] nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule

/-- An actual degree-zero ring-module section on the native degree-one
chart is one homogeneous fraction with a power of the original coordinate.
This follows from mathlib's actual structure-section isomorphism. -/
theorem nativeZeroTwistChart_section_singleFraction
    (a : S) (ha : a ∈ 𝓑 1)
    (f : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) 0
      (op (ProjectiveSpectrum.basicOpen 𝓑 a))) :
    ∃ n : ℕ, ∃ ell : S, ell ∈ 𝓑 n ∧
      ∀ p : ProjectiveSpectrum.basicOpen 𝓑 a,
        f.1 p = LocalizedModule.mk ell
          (⟨a^n,p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem p.2 n⟩ :
            p.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
  let r := (nativeStructureRingZeroModuleSectionEquiv 𝓑
    (op (ProjectiveSpectrum.basicOpen 𝓑 a))).symm f
  let E := Proj.basicOpenIsoAway 𝓑 a ha (by omega : 0 < (1 : ℕ))
  let c := E.inv r
  have hc : (ProjectiveSpectrum.Proj.awayToSection 𝓑 a).hom c = r := by
    change E.hom (E.inv r) = r
    exact congrArg (fun h => h r) E.inv_hom_id
  obtain ⟨n,ell,hell,hc'⟩ := HomogeneousLocalization.Away.mk_surjective 𝓑 ha c
  refine ⟨n,ell,by simpa using hell,?_⟩
  intro p
  have hf := congrArg (fun z => z.1 p)
    ((nativeStructureRingZeroModuleSectionEquiv 𝓑
      (op (ProjectiveSpectrum.basicOpen 𝓑 a))).apply_symm_apply f)
  change nativeHomogeneousLocalRingModuleEmbedding 𝓑 p.1 (r.1 p) = f.1 p at hf
  rw [← hf, ← hc, ← hc']
  exact nativeHomogeneousLocalRingModuleEmbedding_mk 𝓑 p.1 n
    ⟨ell,by simpa using hell⟩
    ⟨a^n,by simpa using SetLike.pow_mem_graded n ha⟩
    (p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem p.2 n)

/-- Every actual integer-twist section on a native degree-one chart is
one homogeneous fraction. The denominator exponent compensates negative
twists; no supplied chart trivialization or section-surjectivity is used. -/
theorem nativeIntegerTwistChart_section_singleFraction
    (a : S) (ha : a ∈ 𝓑 1) (k : ℤ)
    (f : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) k
      (op (ProjectiveSpectrum.basicOpen 𝓑 a))) :
    ∃ n : ℕ, ∃ ell : S,
      ell ∈ nativeProjectiveRingIntegerPiece 𝓑 ((n : ℤ)+k) ∧
      ∀ p : ProjectiveSpectrum.basicOpen 𝓑 a,
        f.1 p = LocalizedModule.mk ell
          (⟨a^n,p.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem p.2 n⟩ :
            p.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
  cases k with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast] at f ⊢
    let g : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) 0
      (op (ProjectiveSpectrum.basicOpen 𝓑 a)) :=
      ⟨fun p => (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a p.2 m).symm (f.1 p), by
        change (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) 0).pred (fun p => (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a p.2 m).symm (f.1 p))
        exact nativeProjectiveTwistLocalFraction_backward 𝓑 a ha m 0
          (fun p => p.2) (by have hf := f.property; change (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) (m : ℤ)).pred f.1 at hf; simpa only [zero_add] using hf)⟩
    obtain ⟨n,ell,hell,hg⟩ := nativeZeroTwistChart_section_singleFraction 𝓑 a ha g
    have hell' : ell ∈ nativeProjectiveRingIntegerPiece 𝓑 (n : ℤ) := by
      simpa only [nativeProjectiveRingIntegerPiece, Int.natCast_nonneg,
        ite_true,Int.toNat_natCast] using hell
    refine ⟨n,a^m*ell,?_,?_⟩
    · simpa only [smul_eq_mul,add_comm] using
        nativeProjectiveRingIntegerPiece_graded 𝓑 m (n : ℤ) (a^m)
          (by simpa using SetLike.pow_mem_graded m ha) ell hell'
    · intro p
      have h : nativeProjectivePrimeTwistEquiv 𝓑 p.1 a p.2 m (g.1 p) = f.1 p :=
        (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a p.2 m).apply_symm_apply _
      rw [← h,hg p,nativeProjectivePrimeTwistEquiv_mk]
  | negSucc m =>
    have hk : Int.negSucc m + ((m+1 : ℕ) : ℤ) = 0 := by omega
    let g : nativeProjectiveModuleSections 𝓑 (nativeProjectiveRingIntegerPiece 𝓑)
      (nativeProjectiveRingIntegerPiece_graded 𝓑) 0
      (op (ProjectiveSpectrum.basicOpen 𝓑 a)) :=
      ⟨fun p => nativeProjectivePrimeTwistEquiv 𝓑 p.1 a p.2 (m+1) (f.1 p), by
        change (nativeProjectiveModuleLocalPredicate 𝓑 (nativeProjectiveRingIntegerPiece 𝓑) 0).pred (fun p => nativeProjectivePrimeTwistEquiv 𝓑 p.1 a p.2 (m+1) (f.1 p))
        simpa only [hk] using nativeProjectiveTwistLocalFraction_forward 𝓑 a ha
          (m+1) (Int.negSucc m) (fun p => p.2) f.property⟩
    obtain ⟨n,ell,hell,hg⟩ := nativeZeroTwistChart_section_singleFraction 𝓑 a ha g
    refine ⟨n+(m+1),ell,?_,?_⟩
    · have hd : ((n+(m+1) : ℕ) : ℤ)+Int.negSucc m = n := by omega
      rw [hd]
      simpa only [nativeProjectiveRingIntegerPiece,Int.natCast_nonneg,
        ite_true,Int.toNat_natCast] using hell
    · intro p
      have h : (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a p.2 (m+1)).symm (g.1 p) = f.1 p :=
        (nativeProjectivePrimeTwistEquiv 𝓑 p.1 a p.2 (m+1)).symm_apply_apply _
      rw [← h,hg p,nativeProjectivePrimeTwistEquiv_symm_mk]
      congr 1
      apply Subtype.ext
      change a^n * a^(m+1) = a^(n+(m+1))
      exact (pow_add a n (m+1)).symm

end LinearStudy
