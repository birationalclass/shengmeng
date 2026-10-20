module
public import Linear.SchemeModuleOriginalActualSectionBoundary
public import Linear.SchemeModuleOriginalCovariantSerreStatement
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u
variable {X : Scheme.{u}}
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
/-- Actual unit-Serre vanishing of original twists implies the SAME
actual-section exactness for ANY proved top-term coefficient isomorphism.
No separate desired boundary surjectivity or kernel equality is a premise. -/
theorem schemeModuleOriginalActualSectionExact_of_unitSerre
    (C : ChainComplex X.Modules ℕ) {E M : X.Modules} (r : ℕ) (hr : 0 < r)
    (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E) (hAlpha : QuasiIso alpha)
    (hAbove : IsZero (C.X (r+1))) (phi : C.X r ≅ M)
    (T : ℤ → X.Modules) (N d : ℕ)
    (e : ∀ p : ℕ,C.X p ≅ biproduct (fun _ : Set.powersetCard (Fin r) p =>
      T ((r : ℤ)*(d : ℤ)-(r : ℤ)-1-(p : ℤ)*(d : ℤ))))
    (hd : N+r+1 ≤ d)
    (hSerre : ∀ s : ℤ,(N : ℤ) ≤ s → ∀ q : ℕ,0 < q →
      Subsingleton (Ext.{u} (SheafOfModules.unit X.ringCatSheaf) (T s) q)) :
    schemeModuleOriginalActualSectionExactStatement C r alpha hAlpha hAbove phi := by
  apply schemeModuleOriginalActualSectionExactStatement_of_unit
  exact schemeModuleOriginalCovariantSerreStatement_proof C r hr alpha hAlpha hAbove phi T N d e hd
    (SheafOfModules.unit X.ringCatSheaf) hSerre
end LinearStudy
