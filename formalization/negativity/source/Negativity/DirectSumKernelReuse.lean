module
public import Negativity.DirectSumQuotientReuse

@[expose] public section
namespace Negativity
open scoped DirectSum
universe u v w
noncomputable section
variable {κ : Type u} {A : κ → Type v} {B : κ → Type w}
  [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]

def actualDirectSumKernelMap (g : ∀ n, A n →+ B n) :
    (⨁ n, (g n).ker) →+ (DirectSum.map g).ker :=
  (DirectSum.map (fun n => (g n).ker.subtype)).codRestrict _ (by
    intro x
    ext n
    simp only [DirectSum.map_apply, DFinsupp.zero_apply]
    exact (x n).2)

theorem actual_direct_sum_kernel_map_bijective (g : ∀ n, A n →+ B n) :
    Function.Bijective (actualDirectSumKernelMap g) := by
  constructor
  · intro a b hab
    apply (DirectSum.map_injective (fun n => (g n).ker.subtype)).mpr
      (fun n => Subtype.val_injective)
    exact congrArg Subtype.val hab
  · intro x
    have hx : ∀ n, x.1 n ∈ ((g n).ker.subtype).range := by
      intro n
      refine ⟨⟨x.1 n, ?_⟩, rfl⟩
      change g n (x.1 n) = 0
      have hn := congrArg (fun a => a n) x.2
      simpa only [DirectSum.map_apply, DFinsupp.zero_apply] using hn
    obtain ⟨a, ha⟩ := (actual_direct_sum_map_range
      (fun n => (g n).ker.subtype) x.1).mpr hx
    exact ⟨a, Subtype.ext ha⟩

/-- Actual finitely supported cocycles equal the kernel of the actual
direct-sum differential; the inverse has no support or finiteness premise. -/
def actualDirectSumKernelEquiv (g : ∀ n, A n →+ B n) :
    (⨁ n, (g n).ker) ≃+ (DirectSum.map g).ker :=
  AddEquiv.ofBijective (actualDirectSumKernelMap g)
    (actual_direct_sum_kernel_map_bijective g)

@[simp]
theorem actualDirectSumKernelEquiv_apply (g : ∀ n, A n →+ B n)
    (x : ⨁ n, (g n).ker) (n : κ) :
    (actualDirectSumKernelEquiv g x).1 n = (x n).1 := rfl

#print axioms actualDirectSumKernelEquiv
end
end Negativity
