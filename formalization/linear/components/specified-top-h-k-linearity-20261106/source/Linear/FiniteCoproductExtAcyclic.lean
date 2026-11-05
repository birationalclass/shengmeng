module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v w t
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- Source-Ext vanishing is transported along an actual constructed source isomorphism. -/
theorem ext_subsingleton_of_source_iso {O P F : A} (e : O ≅ P) (n : ℕ)
    (h : Subsingleton (Ext O F n)) : Subsingleton (Ext P F n) := by
  letI := h
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : (Ext.mk₀ e.hom).comp x (zero_add _) = 0 := Subsingleton.elim _ _
  have hc := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add n)) hx
  simpa only [Ext.mk₀_comp_mk₀_assoc,e.inv_hom_id,Ext.mk₀_id_comp,Ext.comp_zero] using hc
/-- A finite coproduct of actual Ext-acyclic sources is Ext-acyclic,through the native
biproduct Ext additive equivalence. No result-specific coproduct vanishing premise. -/
theorem finiteCoproduct_ext_subsingleton {J : Type t} [Finite J]
    (O : J → A) (F : A) (n : ℕ) (h : ∀ j, Subsingleton (Ext (O j) F n)) :
    Subsingleton (Ext (∐ O) F n) := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  letI : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts
  letI (j : J) : Subsingleton (Ext (O j) F n) := h j
  have hb : Subsingleton (Ext (biproduct O) F n) :=
    (Ext.biproductAddEquiv (biproduct.isBilimit O) F n).injective.subsingleton
  exact ext_subsingleton_of_source_iso (biproduct.isoCoproduct O) n hb
end LinearStudy
