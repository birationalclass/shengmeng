module
public import Linear.IteratedCovariantExtClass
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
/-- Above degree zero,the SAME iterated actual boundary is one-to-one
under explicit positive relative Ext vanishings. It need not be
one-to-one on Hom;that kernel is the original restriction image. -/
theorem iteratedCovariantExtClass_postcomp_injective
    (O : A) (n : ℕ) (hn : n ≤ r)
    (hvan : ∀ j,j < n → ∀ q,0 < q → Subsingleton (Ext O (B j) q))
    (m k : ℕ) (hm : 0 < m) (hdegree : m+n=k) :
    Function.Injective
      ((iteratedCovariantExtClass Z B f g hfg r hS n hn).postcomp O hdegree) := by
  induction n generalizing m k with
  | zero =>
    intro x y hxy
    have hmk : m=k := by omega
    subst k
    change x.comp (Ext.mk₀ (𝟙 (Z 0))) (by omega) =
      y.comp (Ext.mk₀ (𝟙 (Z 0))) (by omega) at hxy
    simpa only [Ext.comp_mk₀_id] using hxy
  | succ n ih =>
    intro x y hxy
    let S := ShortComplex.mk (f n) (g n) (hfg n)
    have hs : S.ShortExact := hS n (by omega)
    have hcomp (z : Ext O (Z (n+1)) m) :
        (z.comp hs.extClass rfl).comp
          (iteratedCovariantExtClass Z B f g hfg r hS n (by omega)) (show m+1+n=k by omega) =
        z.comp (iteratedCovariantExtClass Z B f g hfg r hS (n+1) hn) hdegree := by
      rw [iteratedCovariantExtClass_succ,Ext.comp_assoc]
      all_goals omega
    have hxy' :
        (x.comp hs.extClass rfl).comp
          (iteratedCovariantExtClass Z B f g hfg r hS n (by omega)) (show m+1+n=k by omega) =
        (y.comp hs.extClass rfl).comp
          (iteratedCovariantExtClass Z B f g hfg r hS n (by omega)) (show m+1+n=k by omega) := by
      rw [hcomp,hcomp]
      exact hxy
    have hz := ih (by omega) (fun j hj q hq => hvan j (by omega) q hq)
      (m+1) k (by omega) (by omega) hxy'
    haveI : Subsingleton (Ext O (B n) m) := hvan n (by omega) m hm
    exact relativeAcyclicCovariantBoundary_injective O hs m (m+1) rfl hz
end LinearStudy
