module
public import Linear.OriginalChainOpcycleEmbedding
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open CategoryTheory
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
/-- Native original quotient identification preserves explicit equality transport of source indices. -/
theorem originalChainAsCochainOpcyclesIso_index (C : ChainComplex A ℕ) (j : ℤ)
    (n m : ℕ) (hn : -(n : ℤ)=j) (hm : -(m : ℤ)=j) (h : n=m) :
    (originalChainAsCochainOpcyclesIso C j n hn).hom ≫
      eqToHom (congrArg (fun z => C.opcycles z) h) =
        (originalChainAsCochainOpcyclesIso C j m hm).hom := by
  subst m
  simp only [eqToHom_refl,Category.comp_id]
end LinearStudy
