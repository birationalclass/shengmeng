module
public import Linear.NativeBaseSourceWeightedSectionsLinear
public import Linear.NativeProjectiveChartSectionsOverlap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {K R S M : Type u} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [AddCommGroup M] [Module K M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (A : ℕ → Submodule K R) [GradedAlgebra A]
variable (B : ℕ → Submodule K S) [GradedAlgebra B] [SetLike.GradedSMul A B]
variable (D : ℤ → Submodule K M)
variable (hR : ∀ n : ℕ,∀ j : ℤ,∀ c : R,c ∈ A n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
variable (hS : ∀ n : ℕ,∀ j : ℤ,∀ c : S,c ∈ B n → ∀ x : M,x ∈ D j → c • x ∈ D ((n : ℤ)+j))
attribute [local instance] LocalizedModule.moduleOfIsLocalization nativeHomogeneousAwayModuleScalar
  nativeProjectiveAtPrimeModuleScalar nativeProjectiveAmbientSectionModule
attribute [local irreducible] nativeProjectiveChartDegreeZeroSectionMap
  nativeBaseSourceWeightedChartSectionLinearMap
/-- Compare the ACTUAL two weighted-chart section groups using their SAME
localized module.The bijectivity inputs are explicit,not assertions of global
Cech/cohomology comparison;the following naturality theorem proves the maps. -/
def nativeWeightedSourceAmbientSectionAddEquiv
    (d : ℕ) (a : R) (ha : a ∈ A d)
    (hA : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha))
    (hB : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS d
      (algebraMap R S a) ((normalizationBaseGradedRingHom A B).map_mem ha))) :
    nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A a)) ≃+
      nativeProjectiveModuleSections B D hS 0 (op (Proj.basicOpen B (algebraMap R S a))) :=
  (AddEquiv.ofBijective (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha).toAddMonoidHom hA).symm.trans
    (AddEquiv.ofBijective
      (nativeBaseSourceWeightedChartSectionLinearMap A B D hR hS d a ha).toAddMonoidHom
      (nativeBaseSourceWeightedChartSectionLinearMap_bijective A B D hR hS d a ha hB))
/-- The constructed comparison takes each ORIGINAL ambient fraction section
to precisely its ORIGINAL source fraction section. -/
theorem nativeWeightedSourceAmbientSectionAddEquiv_chart
    (d : ℕ) (a : R) (ha : a ∈ A d)
    (hA : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha))
    (hB : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS d
      (algebraMap R S a) ((normalizationBaseGradedRingHom A B).map_mem ha)))
    (x : nativeGradedModuleAwayDegreeZero A D d a) :
    nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS d a ha hA hB
      (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha x) =
      nativeBaseSourceWeightedChartSection A B D hR hS d a ha x := by
  let eA := AddEquiv.ofBijective
    (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha).toAddMonoidHom hA
  change nativeBaseSourceWeightedChartSectionLinearMap A B D hR hS d a ha
    (eA.symm (eA x)) = _
  rw [eA.symm_apply_apply]
  exact nativeBaseSourceWeightedChartSectionLinearMap_eq A B D hR hS d a ha x
attribute [local irreducible] nativeWeightedSourceAmbientSectionAddEquiv
/-- Every original weighted overlap restriction commutes with the ACTUAL
ambient/source additive comparison.The second factor has its true degree e;
there is no assumed naturality square or degree-one product replacement. -/
theorem nativeWeightedSourceAmbientSectionAddEquiv_overlap
    (d e : ℕ) (a b : R) (ha : a ∈ A d) (hb : b ∈ A e)
    (hA : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR d a ha))
    (hB : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS d
      (algebraMap R S a) ((normalizationBaseGradedRingHom A B).map_mem ha)))
    (hAB : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap A D hR (d+e)
      (a*b) (SetLike.mul_mem_graded ha hb)))
    (hBB : Function.Bijective (nativeProjectiveChartDegreeZeroSectionMap B D hS (d+e)
      (algebraMap R S (a*b)) ((normalizationBaseGradedRingHom A B).map_mem (SetLike.mul_mem_graded ha hb))))
    (s : nativeProjectiveModuleSections A D hR 0 (op (Proj.basicOpen A a))) :
    nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS (d+e) (a*b)
      (SetLike.mul_mem_graded ha hb) hAB hBB
      ((nativeProjectiveModulePresheaf A D hR 0).map
        (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left A a b)).op s) =
      (nativeProjectiveModulePresheaf B D hS 0).map
        (homOfLE (show Proj.basicOpen B (algebraMap R S (a*b)) ≤
          Proj.basicOpen B (algebraMap R S a) from by
            rw [map_mul];exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)).op
        (nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS d a ha hA hB s) := by
  obtain ⟨x,rfl⟩ := hA.surjective s
  let y := nativeGradedModuleWeightedOverlapMap A D hR d e a b ha hb x
  have h0 := nativeWeightedSourceAmbientSectionAddEquiv_chart A B D hR hS d a ha hA hB x
  have h1 := nativeWeightedSourceAmbientSectionAddEquiv_chart A B D hR hS (d+e) (a*b)
    (SetLike.mul_mem_graded ha hb) hAB hBB y
  have hr := nativeProjectiveChartDegreeZeroSectionMap_overlap A D hR d e a b ha hb x
  have hs := nativeBaseSourceWeightedChartSection_overlap A B D hR hS d e a b ha hb x
  exact (congrArg
    (nativeWeightedSourceAmbientSectionAddEquiv A B D hR hS (d+e) (a*b)
      (SetLike.mul_mem_graded ha hb) hAB hBB) hr).trans
    (h1.trans (hs.symm.trans (congrArg
      ((nativeProjectiveModulePresheaf B D hS 0).map
        (homOfLE (show Proj.basicOpen B (algebraMap R S (a*b)) ≤
          Proj.basicOpen B (algebraMap R S a) from by
            rw [map_mul];exact ProjectiveSpectrum.basicOpen_mul_le_left B _ _)).op) h0.symm)))
end LinearStudy
