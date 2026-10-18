module
public import Linear.NativeProjectiveOpenKoszulExactChart
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]
variable (B : ℕ → Submodule K S) [GradedAlgebra B]
variable [IsNoetherianRing S] {J : Type} (b : J → S) (hb : ∀ i,b i ∈ B 1)
variable (hgen : Algebra.adjoin K (Set.range b) = ⊤)
variable {r q : ℕ} (H : Fin r → S) (hH : ∀ i,H i ∈ B q) (k : ℤ)
variable (z : S) (hz : z ∈ B 1)
/-- The constructed chart ring is the ACTUAL original homogeneous away ring. -/
theorem nativeProjectiveOpenKoszulExactChart_ring :
    (nativeProjectiveOpenKoszulExactChart B b hb hgen H hH k z hz).1 =
      CommRingCat.of (HomogeneousLocalization.Away B z) :=
  Eq.refl ((nativeProjectiveOpenKoszulExactChart B b hb hgen H hH k z hz).1)
/-- Its inclusion is the SAME original Proj away inclusion,not a substituted chart. -/
theorem nativeProjectiveOpenKoszulExactChart_inclusion :
    HEq (nativeProjectiveOpenKoszulExactChart B b hb hgen H hH k z hz).2.1
      (Proj.awayι B z hz one_pos) :=
  HEq.refl ((nativeProjectiveOpenKoszulExactChart B b hb hgen H hH k z hz).2.1)
/-- Its equations are the SAME original degree-q fractions H_i/z^q. -/
theorem nativeProjectiveOpenKoszulExactChart_equations :
    HEq (nativeProjectiveOpenKoszulExactChart B b hb hgen H hH k z hz).2.2.2.1
      (fun i => HomogeneousLocalization.Away.mk B hz q (H i) (by simpa using hH i)) :=
  HEq.refl ((nativeProjectiveOpenKoszulExactChart B b hb hgen H hH k z hz).2.2.2.1)
end LinearStudy

