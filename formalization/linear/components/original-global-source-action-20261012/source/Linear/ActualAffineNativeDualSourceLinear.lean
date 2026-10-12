module
public import Linear.ActualAffineNativeDualSourceCompatibility
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 150000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The original affine Hom module carries the original source-ring action,
transported only through mathlib's actual Gamma-Spec ring isomorphism. -/
@[instance_reducible] def actualAffineOriginalHomSourceModule :
    Module B (Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤)) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let N : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let H := Γ(schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)) N,⊤)
  letI : SMul (Γ(Spec (CommRingCat.of B), f ⁻¹ᵁ ⊤)) H :=
    ⟨schemePushforwardHomSourceActionSection f N ⊤⟩
  letI : Module (Γ(Spec (CommRingCat.of B), f ⁻¹ᵁ ⊤)) H :=
    schemePushforwardHomSourceModule f N ⊤
  letI : Module (Γ(Spec (CommRingCat.of B),⊤)) H := by
    change Module (Γ(Spec (CommRingCat.of B), f ⁻¹ᵁ ⊤)) H
    exact schemePushforwardHomSourceModule f N ⊤
  exact Module.compHom H (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

/-- The actual native affine dual and actual internal Hom are linearly
equivalent over B itself, with their original source action. -/
def actualAffineNativeDualOriginalHomSourceLinearEquiv :
    let H := Γ(schemeModuleHomModuleSheaf
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf),⊤)
    letI : Module B H := actualAffineOriginalHomSourceModule (A := A) (B := B)
    ((ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)) ≃ₗ[B] H := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let N : (Spec (CommRingCat.of A)).Modules :=
    SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let H := Γ(schemeModuleHomModuleSheaf
    ((Scheme.Modules.pushforward f).obj
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)) N,⊤)
  letI : Module B H := actualAffineOriginalHomSourceModule (A := A) (B := B)
  let E := (nativeCoextensionOriginalDualEquiv (R := A) (S := B)).trans
    (actualAffineAlgebraDualInternalHomSectionsLinearEquiv (A := A) (B := B))
  refine { __ := E.toEquiv, map_add' := E.map_add, map_smul' := ?_ }
  intro b ell
  change E (b • ell) = schemePushforwardHomSourceActionSection f N ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) (E ell)
  have hb := eq_of_heq
    (actualAffineAlgebraStructurePushforwardIso_element_value (A := A) b)
  have hc := actualAffineNativeDualInternalHom_original_source_action (A := A) ell b
  rw [hb] at hc
  exact hc

end LinearStudy
