module
public import Linear.IteratedCovariantExtClass
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
/-- Iterated ACTUAL covariant connecting map is onto under explicit
positive relative Ext vanishings of the middle terms. This does NOT
assume terms are globally projective or that geometry proves vanishings. -/
theorem iteratedCovariantExtClass_postcomp_surjective
    (O : A) (n : ℕ) (hn : n ≤ r)
    (hvan : ∀ j,j < n → ∀ q,0 < q → Subsingleton (Ext O (B j) q))
    (m k : ℕ) (hdegree : m+n=k) :
    ∀ x : Ext O (Z 0) k,∃ y : Ext O (Z n) m,
      y.comp (iteratedCovariantExtClass Z B f g hfg r hS n hn) hdegree = x := by
  induction n generalizing m k with
  | zero =>
    intro x
    have hmk : m=k := by omega
    subst k
    refine ⟨x,?_⟩
    simpa only [iteratedCovariantExtClass_zero] using Ext.comp_mk₀_id x
  | succ n ih =>
    intro x
    obtain ⟨y,hy⟩ := ih (by omega) (fun j hj q hq => hvan j (by omega) q hq)
      (m+1) k (by omega) x
    let S := ShortComplex.mk (f n) (g n) (hfg n)
    have hs : S.ShortExact := hS n (by omega)
    haveI : Subsingleton (Ext O (B n) (m+1)) := hvan n (by omega) (m+1) (by omega)
    have hz : y.comp (Ext.mk₀ S.f) (add_zero _) = 0 := Subsingleton.elim _ _
    obtain ⟨z,hz⟩ := Ext.covariant_sequence_exact₁ O hs y hz (show m+1=m+1 from rfl)
    refine ⟨z,?_⟩
    calc
      z.comp (iteratedCovariantExtClass Z B f g hfg r hS (n+1) hn) hdegree =
          (z.comp hs.extClass rfl).comp
            (iteratedCovariantExtClass Z B f g hfg r hS n (by omega)) (show m+1+n=k by omega) := by
        rw [iteratedCovariantExtClass_succ,Ext.comp_assoc]
        all_goals omega
      _ = x := by rw [hz];exact hy
end LinearStudy
