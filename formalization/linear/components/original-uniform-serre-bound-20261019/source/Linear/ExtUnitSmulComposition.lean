module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
variable {O E N : A} {m n k : ℕ}
/-- Native Ext composition respects integer UNITS in the coefficient slot. -/
theorem ext_comp_unit_smul (x : Ext O E m) (s : ℤˣ) (e : Ext E N n) (h : m+n=k) :
    x.comp (s • e) h = s • x.comp e h := by
  change (x.precomp N h) (s • e) = s • (x.precomp N h) e
  simp only [Units.smul_def,map_zsmul]
/-- Native Ext composition respects integer UNITS in the source class. -/
theorem ext_unit_smul_comp (s : ℤˣ) (e : Ext O E m) (x : Ext E N n) (h : m+n=k) :
    (s • e).comp x h = s • e.comp x h := by
  change (x.postcomp O h) (s • e) = s • (x.postcomp O h) e
  simp only [Units.smul_def,map_zsmul]
/-- A constructed unit change of sign preserves the ACTUAL connecting
map kernel. No new class comparison or kernel certificate is input. -/
theorem ext_comp_unit_smul_zero_iff (x : Ext O E m) (s : ℤˣ) (e : Ext E N n) (h : m+n=k) :
    x.comp (s • e) h = 0 ↔ x.comp e h = 0 := by
  rw [ext_comp_unit_smul,smul_eq_zero_iff_eq]
/-- The same constructed unit change preserves ACTUAL surjectivity. -/
theorem ext_postcomp_unit_smul_surjective (s : ℤˣ) (e : Ext E N n) (h : m+n=k)
    (he : Function.Surjective (e.postcomp O h)) :
    Function.Surjective ((s • e).postcomp O h) := by
  intro x
  obtain ⟨y,hy⟩ := he (s⁻¹ • x)
  change y.comp e h = s⁻¹ • x at hy
  refine ⟨y,?_⟩
  change y.comp (s • e) h = x
  rw [ext_comp_unit_smul,hy,smul_inv_smul]
end LinearStudy
