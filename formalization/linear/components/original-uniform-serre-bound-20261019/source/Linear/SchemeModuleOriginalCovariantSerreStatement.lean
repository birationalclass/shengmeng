module
public import Linear.SchemeModuleOriginalCovariantAtSource
public import Linear.ExtCovariantComplexSerreBound
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
/-- Statement only:for EVERY original source O,ONE Serre bound for T
implies exactness for SAME C,alpha,phi. Quantification stays INSIDE the
abstract module-sheaf interface,so concrete native Ext is not expanded.
No existence of a geometric Serre bound is asserted. -/
def schemeModuleOriginalCovariantSerreStatement
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M)
    (T : ℤ → X.Modules) (N d : ℕ)
    (e : ∀ p : ℕ,C.X p ≅ biproduct (fun _ : Set.powersetCard (Fin r) p =>
      T ((r : ℤ)*(d : ℤ)-(r : ℤ)-1-(p : ℤ)*(d : ℤ)))) : Prop :=
  ∀ O : X.Modules,
    (∀ s : ℤ,(N : ℤ) ≤ s → ∀ i : ℕ,0 < i → Subsingleton (Ext O (T s) i)) →
    schemeModuleOriginalCovariantAtSourceStatement C r alpha hAlpha hAbove phi O
/-- Prove the entire conditional implication on abstract actual module
sheaves. Actual original term isos transfer the single bound;original
roof exactness is reused. No desired kernel/image equality is an input. -/
theorem schemeModuleOriginalCovariantSerreStatement_proof
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M)
    (T : ℤ → X.Modules) (N d : ℕ)
    (e : ∀ p : ℕ,C.X p ≅ biproduct (fun _ : Set.powersetCard (Fin r) p =>
      T ((r : ℤ)*(d : ℤ)-(r : ℤ)-1-(p : ℤ)*(d : ℤ))))
    (hd : N+r+1 ≤ d) :
    schemeModuleOriginalCovariantSerreStatement C r alpha hAlpha hAbove phi T N d e := by
  intro O hSerre
  exact schemeModuleOriginalCovariantAtSourceStatement_proof C r hr alpha hAlpha hAbove phi O
    (extCovariantComplex_middle_from_Serre_bound C O T N r d e hd hSerre)
end LinearStudy
