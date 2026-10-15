module
public import Linear.NativeIntegerShiftedFreeSectionFrames
public import Linear.SchemeModuleSpecChartSectionsNaturality
public import Linear.OriginalProjectiveWeightedChartSectionRing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K S I : Type} [Field K] [CommRing S] [Algebra K S]
variable (𝓑 : ℕ → Submodule K S) [GradedAlgebra 𝓑]

/-- SAME original chart scalar isomorphism,bundled linearly over the
ORIGINAL away ring via its ACTUAL awayToSection scalar action. -/
def nativeProjectiveChartScalarLinearEquiv (a : S) (ha : a ∈ 𝓑 1) :
    let U := Proj.basicOpen 𝓑 a
    letI : Module (HomogeneousLocalization.Away 𝓑 a) Γ(Proj 𝓑,U) :=
      Module.compHom Γ(Proj 𝓑,U) (Proj.awayToSection 𝓑 a).hom
    HomogeneousLocalization.Away 𝓑 a ≃ₗ[HomogeneousLocalization.Away 𝓑 a] Γ(Proj 𝓑,U) := by
  let U := Proj.basicOpen 𝓑 a
  letI : Module (HomogeneousLocalization.Away 𝓑 a) Γ(Proj 𝓑,U) :=
    Module.compHom Γ(Proj 𝓑,U) (Proj.awayToSection 𝓑 a).hom
  let E := (Proj.basicOpenIsoAway 𝓑 a ha one_pos).commRingCatIsoToRingEquiv
  exact {toAddEquiv := E.toAddEquiv,map_smul' := fun c x => E.map_mul c x}

/-- ORIGINAL integer shifted-free chart frame on ACTUAL Spec global sections.
Every scalar and section map is the SAME original away chart map.
ALL integer k and arbitrary original weights are retained. -/
def nativeIntegerShiftedFreeSpecChartFrame [DecidableEq I] [Fintype I]
    (w : I → ℤ) (k : ℤ) (a : S) (ha : a ∈ 𝓑 1) :
    let R := CommRingCat.of (HomogeneousLocalization.Away 𝓑 a)
    let M := nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k
    (I → HomogeneousLocalization.Away 𝓑 a) ≃ₗ[HomogeneousLocalization.Away 𝓑 a]
      moduleSpecΓFunctor.obj (M.restrict (Proj.awayι 𝓑 a ha one_pos)) := by
  let U := Proj.basicOpen 𝓑 a
  let j := Proj.awayι 𝓑 a ha one_pos
  let φ := Proj.awayToSection 𝓑 a
  let M := nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
    (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k
  have hi : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans
    (Proj.opensRange_awayι 𝓑 a ha one_pos)
  letI : Module (HomogeneousLocalization.Away 𝓑 a) Γ(Proj 𝓑,U) :=
    Module.compHom Γ(Proj 𝓑,U) φ.hom
  letI : Module (HomogeneousLocalization.Away 𝓑 a) (I → Γ(Proj 𝓑,U)) :=
    Module.compHom (I → Γ(Proj 𝓑,U)) φ.hom
  letI : Module (HomogeneousLocalization.Away 𝓑 a) Γ(M,U) :=
    Module.compHom Γ(M,U) φ.hom
  let F : (I → Γ(Proj 𝓑,U)) ≃ₗ[Γ(Proj 𝓑,U)] Γ(M,U) :=
    nativeIntegerShiftedFreeSectionFrame 𝓑 w k a ha (op U) (fun p => p.2)
  let FR : (I → Γ(Proj 𝓑,U)) ≃ₗ[HomogeneousLocalization.Away 𝓑 a] Γ(M,U) :=
    {toAddEquiv := F.toAddEquiv,map_smul' := fun c x => F.map_smul' (φ c) x}
  let E : (I → HomogeneousLocalization.Away 𝓑 a) ≃ₗ[HomogeneousLocalization.Away 𝓑 a]
      (I → Γ(Proj 𝓑,U)) :=
    LinearEquiv.piCongrRight (fun _ => nativeProjectiveChartScalarLinearEquiv 𝓑 a ha)
  exact (E.trans FR).trans (schemeModuleSpecChartSectionsLinearEquiv M j U hi φ
    (originalProjectiveWeightedChartScalar_appLE 𝓑 1 one_pos a ha))

/-- The constructed Spec frame has EXACTLY the original chart section map,
original integer frame and original scalar coordinates as its components. -/
theorem nativeIntegerShiftedFreeSpecChartFrame_apply [DecidableEq I] [Fintype I]
    (w : I → ℤ) (k : ℤ) (a : S) (ha : a ∈ 𝓑 1)
    (v : I → HomogeneousLocalization.Away 𝓑 a) :
    let U := Proj.basicOpen 𝓑 a
    let j := Proj.awayι 𝓑 a ha one_pos
    let M := nativeProjectiveModuleSheaf 𝓑 (integerShiftedFreePiece 𝓑 w)
      (integerShiftedFreePiece_smul_homogeneous 𝓑 w) k
    let hi : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans
      (Proj.opensRange_awayι 𝓑 a ha one_pos)
    nativeIntegerShiftedFreeSpecChartFrame 𝓑 w k a ha v =
      schemeModuleSpecChartSectionsLinearEquiv M j U hi (Proj.awayToSection 𝓑 a)
        (originalProjectiveWeightedChartScalar_appLE 𝓑 1 one_pos a ha)
        (nativeIntegerShiftedFreeSectionFrame 𝓑 w k a ha (op U) (fun p => p.2)
          (fun i => (Proj.awayToSection 𝓑 a) (v i))) := rfl

end LinearStudy
