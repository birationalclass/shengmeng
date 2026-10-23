module
public import Linear.RelativeAcyclicCovariantBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
variable (Z B : ℕ → A) (f : ∀ j,Z j ⟶ B j) (g : ∀ j,B j ⟶ Z (j+1))
variable (hfg : ∀ j,f j ≫ g j = 0) (r : ℕ)
variable (hS : ∀ j,j < r → (ShortComplex.mk (f j) (g j) (hfg j)).ShortExact)
/-- SAME actual finite sequence's iterated Yoneda extension. No derived
class, comparison identity or cohomological exactness is input. -/
def iteratedCovariantExtClass (n : ℕ) (hn : n ≤ r) : Ext (Z n) (Z 0) n := by
  induction n with
  | zero => exact Ext.mk₀ (𝟙 (Z 0))
  | succ n ih => exact (hS n (by omega)).extClass.comp (ih (by omega)) (by omega)
theorem iteratedCovariantExtClass_zero :
    iteratedCovariantExtClass Z B f g hfg r hS 0 (Nat.zero_le r) = Ext.mk₀ (𝟙 (Z 0)) := rfl
theorem iteratedCovariantExtClass_succ (n : ℕ) (hn : n+1 ≤ r) :
    iteratedCovariantExtClass Z B f g hfg r hS (n+1) hn =
      (hS n (by omega)).extClass.comp
        (iteratedCovariantExtClass Z B f g hfg r hS n (by omega)) (by omega) := rfl
end LinearStudy
