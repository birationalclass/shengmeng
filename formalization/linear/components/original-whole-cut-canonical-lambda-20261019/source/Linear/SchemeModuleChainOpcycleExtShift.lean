module
public import Linear.SchemeModuleChainOpcycleSequence
public import Linear.SchemeModuleInternalExtSourceBoundaryIso
public import Linear.SchemeModuleHomSourceBoundaryCokernel
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
variable {X : Scheme.{u}}

/-- SAME original-chain successive quotients give actual SHEAF Ext
dimension shifts when source-term acyclicity holds. The needed actual
short exact sequence is DERIVED from source exactness. -/
def schemeModuleChainOpcycleExtShiftIso (K : ChainComplex X.Modules ℕ)
    (p : ℕ) (hK : K.ExactAt (p+1)) (N : X.Modules) (I : InjectiveResolution N)
    (q : ℕ) (hA : ∀ j, IsZero (schemeModuleInternalExt (K.X p) N (j+1))) :
    schemeModuleInternalExt (K.opcycles (p+1)) N (q+1) ≅
      schemeModuleInternalExt (K.opcycles p) N (q+2) :=
  schemeModuleInternalExtSourceBoundaryIsoViaResolution
    (schemeModuleChainOpcycleSequence K p) (schemeModuleChainOpcycleSequence_shortExact K p hK)
    N I (q+1) (hA q) (hA (q+1))

/-- The shift hom is SAME actual native-snake boundary for SAME quotient sequence. -/
theorem schemeModuleChainOpcycleExtShiftIso_hom (K : ChainComplex X.Modules ℕ)
    (p : ℕ) (hK : K.ExactAt (p+1)) (N : X.Modules) (I : InjectiveResolution N)
    (q : ℕ) (hA : ∀ j, IsZero (schemeModuleInternalExt (K.X p) N (j+1))) :
    (schemeModuleChainOpcycleExtShiftIso K p hK N I q hA).hom =
      schemeModuleInternalExtSourceBoundaryViaResolution (schemeModuleChainOpcycleSequence K p)
        (schemeModuleChainOpcycleSequence_shortExact K p hK) N I (q+1) := rfl

/-- Degree-zero last step is the ACTUAL Hom-precomposition cokernel,
not a replacement source map or an assumed Ext comparison. -/
def schemeModuleChainOpcycleHomCokernelIso (K : ChainComplex X.Modules ℕ)
    (p : ℕ) (hK : K.ExactAt (p+1)) (N : X.Modules) (I : InjectiveResolution N)
    (hA : IsZero (schemeModuleInternalExt (K.X p) N 1)) :
    cokernel (schemeModuleHomPrecompose (N := N) (K.fromOpcycles (p+1) p)) ≅
      schemeModuleInternalExt (K.opcycles p) N 1 :=
  schemeModuleHomSourceBoundaryCokernelIso (schemeModuleChainOpcycleSequence K p)
    (schemeModuleChainOpcycleSequence_shortExact K p hK) N I hA

/-- Iterate the SAME actual source boundaries through original opcycles.
No projectivity or chosen target Ext-comparison is a premise. -/
def schemeModuleChainOpcycleIteratedExtIso (K : ChainComplex X.Modules ℕ)
    (hK : ∀ p, K.ExactAt (p+1)) (N : X.Modules) (I : InjectiveResolution N)
    (hA : ∀ p j, IsZero (schemeModuleInternalExt (K.X p) N (j+1))) (p q : ℕ) :
    schemeModuleInternalExt (K.opcycles p) N (q+1) ≅
      schemeModuleInternalExt (K.opcycles (p+q)) N 1 := by
  induction q generalizing p with
  | zero => exact Iso.refl _
  | succ q ih =>
    exact (schemeModuleChainOpcycleExtShiftIso K p (hK p) N I q (hA p)).symm ≪≫
      ih (p+1) ≪≫ eqToIso (congrArg
        (fun z => schemeModuleInternalExt (K.opcycles z) N 1)
        (by omega : (p+1)+q = p+(q+1)))

/-- High actual SHEAF Ext is computed by the final ACTUAL original
Hom/opcycles cokernel,using only source exactness and source acyclicity. -/
def schemeModuleChainOpcycleExtCokernelIso (K : ChainComplex X.Modules ℕ)
    (hK : ∀ p, K.ExactAt (p+1)) (N : X.Modules) (I : InjectiveResolution N)
    (hA : ∀ p j, IsZero (schemeModuleInternalExt (K.X p) N (j+1))) (p q : ℕ) :
    schemeModuleInternalExt (K.opcycles p) N (q+1) ≅
      cokernel (schemeModuleHomPrecompose (N := N) (K.fromOpcycles (p+q+1) (p+q))) :=
  schemeModuleChainOpcycleIteratedExtIso K hK N I hA p q ≪≫
    (schemeModuleChainOpcycleHomCokernelIso K (p+q) (hK (p+q)) N I (hA (p+q) 0)).symm

end LinearStudy
