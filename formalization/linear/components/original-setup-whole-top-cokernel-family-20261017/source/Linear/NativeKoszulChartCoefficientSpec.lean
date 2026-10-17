module
public import Linear.NativeHomogeneousIntegerFrameMultiply
public import Linear.OriginalProjectiveWeightedChartScalarTransport
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- On the full ORIGINAL chart,the actual homogeneous coefficient section
is the SAME original away-ring fraction under the native chart map. -/
theorem nativeHomogeneousChartCoefficientSection_full (q : ℕ) (ell : 𝓑 q)
    (a : S) (ha : a ∈ 𝓑 1) :
    nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha (Proj.basicOpen 𝓑 a) le_rfl =
      (Proj.awayToSection 𝓑 a)
        (HomogeneousLocalization.Away.mk 𝓑 ha q (ell:S)
          (by simpa using ell.property)) := by
  unfold nativeHomogeneousChartCoefficientSection
  change ((Proj 𝓑).presheaf.map (𝟙 (op (Proj.basicOpen 𝓑 a)))) _ = _
  rw [(Proj 𝓑).presheaf.map_id]
  rfl

/-- Transport the SAME ACTUAL original chart coefficient through the ACTUAL
Spec chart and Gamma-Spec scalar maps. It is exactly the ORIGINAL fraction,
not an arbitrary coordinate/compatibility input. -/
theorem nativeHomogeneousChartCoefficientSection_Spec (q : ℕ) (ell : 𝓑 q)
    (a : S) (ha : a ∈ 𝓑 1) :
    let U := Proj.basicOpen 𝓑 a
    let e := Proj.basicOpenIsoSpec 𝓑 a ha one_pos
    (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).hom
      (e.inv.appTop (U.topIso.inv
        (nativeHomogeneousChartCoefficientSection 𝓑 q ell a ha U le_rfl))) =
      HomogeneousLocalization.Away.mk 𝓑 ha q (ell:S)
        (by simpa using ell.property) := by
  dsimp only
  rw [nativeHomogeneousChartCoefficientSection_full]
  have h := congrArg (fun f : CommRingCat.of (HomogeneousLocalization.Away 𝓑 a) ⟶
      (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).presheaf.obj (op ⊤) =>
        f (HomogeneousLocalization.Away.mk 𝓑 ha q (ell:S)
          (by simpa using ell.property)))
    (originalProjectiveWeightedChartScalarTransport 𝓑 1 one_pos a ha)
  change (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝓑 a))).hom
    (((Proj.awayToSection 𝓑 a ≫ (Proj.basicOpen 𝓑 a).topIso.inv ≫
      (Proj.basicOpenIsoSpec 𝓑 a ha one_pos).inv.appTop)) _) = _
  rw [h]
  exact Iso.inv_hom_id_apply _ _

end LinearStudy
