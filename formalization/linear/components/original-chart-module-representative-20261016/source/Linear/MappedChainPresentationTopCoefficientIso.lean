module
public import Linear.MappedChainPresentationOriginalExt
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
universe v u v' u'
variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- Evaluate the actual original chart complex iso in degree r. -/
def mappedChainPresentationTermIso (p : mappedChainPresentationData F) (r : ℕ) :
    F.obj (p.1.X r) ≅ p.2.1.X r := by
  change (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj p.1).X r) ≅ p.2.1.X r
  exact (HomologicalComplex.eval B (ComplexShape.down ℕ) r).mapIso p.2.2.1

/-- An ACTUAL original top-term iso gives an actual chart coefficient
iso. Its map is exactly the SAME transported original functional. This
chooses the frame induced by that actual chart map,not an independent
ordered-frame formula whose comparison would still need proof. -/
def mappedChainPresentationOriginalTopIso (p : mappedChainPresentationData F)
    {M : A} (r : ℕ) (phi : p.1.X r ≅ M) : p.2.1.X r ≅ F.obj M :=
  (mappedChainPresentationTermIso F p r).symm ≪≫ F.mapIso phi

theorem mappedChainPresentationOriginalTopIso_hom (p : mappedChainPresentationData F)
    {M : A} (r : ℕ) (phi : p.1.X r ≅ M) :
    (mappedChainPresentationOriginalTopIso F p r phi).hom =
      mappedChainPresentationOriginalTopFunctional F p r phi.hom := rfl

/-- Normalize the SAME actual top cocycle using the INVERSE of its
constructed coefficient iso. No unit,sign or cocycle identity is assumed.
Independent conventional chart frames still require their own comparison. -/
theorem mappedChainPresentationOriginalTopIso_normalize (p : mappedChainPresentationData F)
    {M : A} (r : ℕ) (phi : p.1.X r ≅ M) :
    mappedChainPresentationOriginalTopFunctional F p r phi.hom ≫
      (mappedChainPresentationOriginalTopIso F p r phi).inv = 𝟙 _ :=
  (mappedChainPresentationOriginalTopIso F p r phi).hom_inv_id

end LinearStudy
