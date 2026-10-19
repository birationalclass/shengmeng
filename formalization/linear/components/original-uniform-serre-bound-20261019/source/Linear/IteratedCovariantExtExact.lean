module
public import Linear.IteratedCovariantExtSurjective
public import Linear.IteratedCovariantExtInjective
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
variable (Z B : ℕ → A) (f : ∀ j,Z j ⟶ B j) (g : ∀ j,B j ⟶ Z (j+1))
variable (hfg : ∀ j,f j ≫ g j = 0) (r : ℕ)
variable (hS : ∀ j,j < r → (ShortComplex.mk (f j) (g j) (hfg j)).ShortExact)
/-- Kernel of the ACTUAL full connecting map on degree zero is exactly
the image of the last actual middle-term projection. Relative positive
Ext vanishings are explicit;their geometric Serre proof is separate. -/
theorem iteratedCovariantExtClass_kernel
    (O : A) (n : ℕ) (hn : n+1 ≤ r)
    (hvan : ∀ j,j < n → ∀ q,0 < q → Subsingleton (Ext O (B j) q))
    (x : Ext O (Z (n+1)) 0) :
    x.comp (iteratedCovariantExtClass Z B f g hfg r hS (n+1) hn) (zero_add _) = 0 ↔
      ∃ y : Ext O (B n) 0,y.comp (Ext.mk₀ (g n)) (add_zero _) = x := by
  let S := ShortComplex.mk (f n) (g n) (hfg n)
  have hs : S.ShortExact := hS n (by omega)
  have hcomp (z : Ext O (Z (n+1)) 0) :
      (z.comp hs.extClass (zero_add _)).comp
        (iteratedCovariantExtClass Z B f g hfg r hS n (by omega)) (show 1+n=n+1 by omega) =
      z.comp (iteratedCovariantExtClass Z B f g hfg r hS (n+1) hn) (zero_add _) := by
    rw [iteratedCovariantExtClass_succ,Ext.comp_assoc]
    all_goals omega
  have hinj : Function.Injective
      ((iteratedCovariantExtClass Z B f g hfg r hS n (by omega)).postcomp O
        (show 1+n=n+1 by omega)) := by
    exact iteratedCovariantExtClass_postcomp_injective Z B f g hfg r hS O n
      (by omega) hvan 1 (n+1) (by omega) (by omega)
  constructor
  · intro hx
    have hx1 : x.comp hs.extClass (zero_add _) = 0 := by
      apply hinj
      change (x.comp hs.extClass (zero_add _)).comp
          (iteratedCovariantExtClass Z B f g hfg r hS n (by omega)) (show 1+n=n+1 by omega) =
        (0 : Ext O (Z n) 1).comp
          (iteratedCovariantExtClass Z B f g hfg r hS n (by omega)) (show 1+n=n+1 by omega)
      rw [hcomp,Ext.zero_comp]
      exact hx
    exact Ext.covariant_sequence_exact₃ O hs x rfl hx1
  · rintro ⟨y,rfl⟩
    have hs0 : (Ext.mk₀ (g n)).comp hs.extClass (zero_add _) = 0 := hs.comp_extClass
    have hzero : (y.comp (Ext.mk₀ (g n)) (add_zero 0)).comp hs.extClass (zero_add 1) = 0 := by
      rw [Ext.comp_assoc y (Ext.mk₀ (g n)) hs.extClass (add_zero 0) (zero_add 1) (zero_add 1)]
      rw [hs0,Ext.comp_zero]
    rw [← hcomp,hzero,Ext.zero_comp]
end LinearStudy
