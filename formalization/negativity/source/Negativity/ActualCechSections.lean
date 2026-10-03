module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Tactic

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory TopologicalSpace
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

def actualSectionRestriction (X : Scheme.{u}) {U V : X.Opens} (h : U ≤ V) :
    Γ(X, V) →+* Γ(X, U) := (X.presheaf.map (homOfLE h).op).hom

theorem actual_section_restriction_trans (X : Scheme.{u})
    {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W) (s : Γ(X, W)) :
    actualSectionRestriction X hUV (actualSectionRestriction X hVW s) =
      actualSectionRestriction X (hUV.trans hVW) s := by
  change (X.presheaf.map (homOfLE hUV).op)
    ((X.presheaf.map (homOfLE hVW).op) s) = _
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

def actualCechZero (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :=
  ∀ i, Γ(X, U i)

def actualCechOne (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :=
  ∀ i j, Γ(X, U i ⊓ U j)

def actualCechTwo (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :=
  ∀ i j k, Γ(X, (U i ⊓ U j) ⊓ U k)

instance (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    AddCommGroup (actualCechZero X U) := inferInstanceAs (AddCommGroup (∀ i, Γ(X, U i)))
instance (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    AddCommGroup (actualCechOne X U) := inferInstanceAs (AddCommGroup (∀ i j, Γ(X, U i ⊓ U j)))
instance (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    AddCommGroup (actualCechTwo X U) := inferInstanceAs
      (AddCommGroup (∀ i j k, Γ(X, (U i ⊓ U j) ⊓ U k)))

def actualCechDifference (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    actualCechZero X U →+ actualCechOne X U where
  toFun a i j := actualSectionRestriction X inf_le_right (a j) -
    actualSectionRestriction X inf_le_left (a i)
  map_zero' := by
    funext i j
    change actualSectionRestriction X inf_le_right 0 -
      actualSectionRestriction X inf_le_left 0 = 0
    simp
  map_add' a b := by
    funext i j
    change actualSectionRestriction X inf_le_right (a j + b j) -
      actualSectionRestriction X inf_le_left (a i + b i) =
      (actualSectionRestriction X inf_le_right (a j) -
        actualSectionRestriction X inf_le_left (a i)) +
      (actualSectionRestriction X inf_le_right (b j) -
        actualSectionRestriction X inf_le_left (b i))
    simp only [map_add]
    abel

def actualCechBoundary (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    actualCechOne X U →+ actualCechTwo X U where
  toFun a i j k :=
    actualSectionRestriction X (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (a j k) -
    actualSectionRestriction X (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (a i k) +
    actualSectionRestriction X inf_le_left (a i j)
  map_zero' := by
    funext i j k
    change actualSectionRestriction X _ 0 -
      actualSectionRestriction X _ 0 + actualSectionRestriction X _ 0 = 0
    simp
  map_add' a b := by
    funext i j k
    change actualSectionRestriction X _ (a j k + b j k) -
      actualSectionRestriction X _ (a i k + b i k) +
      actualSectionRestriction X _ (a i j + b i j) =
      (actualSectionRestriction X _ (a j k) - actualSectionRestriction X _ (a i k) +
        actualSectionRestriction X _ (a i j)) +
      (actualSectionRestriction X _ (b j k) - actualSectionRestriction X _ (b i k) +
        actualSectionRestriction X _ (b i j))
    simp only [map_add]
    abel

def actualCechGlobalRestriction (X : Scheme.{u}) {ι : Type v} (U : ι → X.Opens) :
    Γ(X, ⊤) →+ actualCechZero X U where
  toFun s i := actualSectionRestriction X le_top s
  map_zero' := by funext i; exact map_zero _
  map_add' a b := by funext i; exact map_add _ _ _

theorem actual_cech_boundary_difference_zero (X : Scheme.{u})
    {ι : Type v} (U : ι → X.Opens) (a : actualCechZero X U) :
    actualCechBoundary X U (actualCechDifference X U a) = 0 := by
  funext i j k
  change _ - _ + _ = (0 : Γ(X, (U i ⊓ U j) ⊓ U k))
  simp only [actualCechBoundary, actualCechDifference, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, map_sub, actual_section_restriction_trans]
  abel

/-- Final theorem: actual sections on an actual open cover form the
degree-zero kernel of the actual Cech differential. The gluing is supplied
by the actual scheme structure sheaf, not by a presumed exactness input.
This does not assert higher-cohomology finiteness for proper schemes. -/
theorem actual_cech_global_sections_exact (X : Scheme.{u})
    {ι : Type v} (U : ι → X.Opens) (hU : (⊤ : X.Opens) ≤ iSup U) :
    AddMonoidHom.range (actualCechGlobalRestriction X U) =
      AddMonoidHom.ker (actualCechDifference X U) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    change actualCechDifference X U (actualCechGlobalRestriction X U s) = 0
    funext i j
    change actualSectionRestriction X inf_le_right
        (actualSectionRestriction X le_top s) -
      actualSectionRestriction X inf_le_left (actualSectionRestriction X le_top s) = 0
    rw [actual_section_restriction_trans, actual_section_restriction_trans, sub_self]
  · intro ha
    have hd : actualCechDifference X U a = 0 := ha
    have hc : TopCat.Presheaf.IsCompatible X.presheaf U a := by
      intro i j
      have hij := congrArg (fun t : actualCechOne X U => t i j) hd
      exact (sub_eq_zero.mp hij).symm
    obtain ⟨s, hs, _⟩ := X.sheaf.existsUnique_gluing' U ⊤
      (fun _ => homOfLE le_top) hU a hc
    exact ⟨s, funext hs⟩

end
end Negativity
