module
public import Linear.NativeKoszulCoefficientUnit
public import Linear.NativeGlobalKoszulChartSectionComplex
public import Linear.KoszulFunctionUnit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]
attribute [local irreducible] nativeProjectiveKoszulComplex nativeProjectiveKoszulTerm

/-- On EVERY actual subopen of D_+(a) intersect D_+(H_i),the SAME
original GLOBAL Koszul SECTION complex is positive exact at EVERY integer
twist. The SAME original H_i/a^q is proved to be a unit; the original
coordinate/exterior chain isomorphisms transport unit-Koszul exactness.
No regular sequence,local/global exactness or coefficient assumption. -/
theorem nativeProjectiveKoszul_sections_exactAt_offCut {r q : ℕ}
    (H : Fin r → S) (hH : ∀ i,H i ∈ 𝓑 q) (i : Fin r) (k : ℤ)
    (a : S) (ha : a ∈ 𝓑 1) (U : (Proj 𝓑).Opens)
    (hU : U ≤ Proj.basicOpen 𝓑 a) (hcut : U ≤ Proj.basicOpen 𝓑 (H i))
    (p : ℕ) (hp : 0 < p) :
    (((SheafOfModules.forget (Proj 𝓑).ringCatSheaf ⋙
      PresheafOfModules.evaluation (Proj 𝓑).ringCatSheaf.obj (op U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (nativeProjectiveKoszulComplex 𝓑 H hH k)).ExactAt p := by
  let h : Fin r → (Proj 𝓑).presheaf.obj (op U) :=
    fun l => nativeHomogeneousChartCoefficientSection 𝓑 q ⟨H l,hH l⟩ a ha U hU
  have hu : IsUnit (h i) :=
    nativeHomogeneousChartCoefficientSection_isUnit 𝓑 q ⟨H i,hH i⟩ a ha U hU hcut
  have he := functionKoszul_unit_exactAt h i hu p hp
  have hc := he.of_iso (homogeneousKoszulCoordinateComplexIso h)
  exact hc.of_iso (nativeGlobalKoszulChartSectionComplexIso 𝓑 H hH k a ha U hU).symm

end LinearStudy