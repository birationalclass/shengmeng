module
public import Mathlib.Logic.Function.Basic
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000
namespace LinearStudy
variable {P K L T Q U : Type*}
/-- Pure quotient-chart separation with explicit zero values. No module
structure is transported across a comparison. -/
theorem actualChartQuotient_zero
    (q : P → Q) (s : P → T) (v : Q → U) (g : T → U)
    (i : K → P) (j : L → T) (k : K → L) (qzero : Q) (uzero : U)
    (hq : Function.Surjective q) (hs : Function.Injective s) (hk : Function.Surjective k)
    (hex : ∀ y : T,g y = uzero → ∃ z : L,j z = y)
    (hqs : ∀ x : P,v (q x) = g (s x))
    (hks : ∀ x : K,s (i x) = j (k x)) (hqi : ∀ x : K,q (i x) = qzero)
    (x : Q) (hx : v x = uzero) : x = qzero := by
  obtain ⟨y,hy⟩ := hq x
  obtain ⟨z,hz⟩ := hex (s y) ((hqs y).symm.trans ((congrArg v hy).trans hx))
  obtain ⟨w,hw⟩ := hk z
  have hi : i w = y := hs ((hks w).trans ((congrArg j hw).trans hz))
  exact hy.symm.trans ((congrArg q hi).symm.trans (hqi w))
end LinearStudy
