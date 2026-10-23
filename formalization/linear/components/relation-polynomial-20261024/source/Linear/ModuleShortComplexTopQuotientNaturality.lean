module
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace CategoryTheory.ShortComplex
universe u v
variable {R : Type u} [Ring R] {S T : ShortComplex (ModuleCat.{v} R)}

/-- A genuine short-complex morphism preserves its actual boundary submodules. -/
theorem moduleCatMorphism_preserves_boundaries (φ : S ⟶ T) :
    S.f.hom.range ≤ T.f.hom.range.comap φ.τ₂.hom := by
  rintro _ ⟨x,rfl⟩
  exact ⟨φ.τ₁ x, ConcreteCategory.congr_hom φ.comm₁₂ x⟩

/-- The actual quotient map induced by the middle component of a
short-complex morphism. No abstract homology equivalence defines this map. -/
def moduleCatBoundaryQuotientMap (φ : S ⟶ T) :
    (S.X₂ ⧸ S.f.hom.range) →ₗ[R] (T.X₂ ⧸ T.f.hom.range) :=
  Submodule.mapQ _ _ φ.τ₂.hom (moduleCatMorphism_preserves_boundaries φ)

/-- mathlib's abstract opcycles map agrees with the actual quotient map. -/
theorem moduleCatOpcyclesIso_naturality (φ : S ⟶ T) :
    opcyclesMap φ ≫ T.moduleCatOpcyclesIso.hom =
    S.moduleCatOpcyclesIso.hom ≫ ModuleCat.ofHom (moduleCatBoundaryQuotientMap φ) := by
  rw [← cancel_epi S.pOpcycles, p_opcyclesMap_assoc,
    pOpcycles_comp_moduleCatOpcyclesIso_hom_assoc,
    pOpcycles_comp_moduleCatOpcyclesIso_hom]
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- When both outgoing differentials vanish, the standard actual
homology-to-boundary-quotient isomorphisms are natural for the original morphism. -/
theorem moduleCatTopHomologyQuotient_naturality (φ : S ⟶ T)
    (hs : S.g = 0) (ht : T.g = 0) :
    homologyMap φ ≫ (T.asIsoHomologyι ht ≪≫ T.moduleCatOpcyclesIso).hom =
    (S.asIsoHomologyι hs ≪≫ S.moduleCatOpcyclesIso).hom ≫
      ModuleCat.ofHom (moduleCatBoundaryQuotientMap φ) := by
  change homologyMap φ ≫ (T.homologyι ≫ T.moduleCatOpcyclesIso.hom) =
    (S.homologyι ≫ S.moduleCatOpcyclesIso.hom) ≫ _
  rw [← Category.assoc, homologyι_naturality, Category.assoc,
    moduleCatOpcyclesIso_naturality, ← Category.assoc]

end CategoryTheory.ShortComplex
