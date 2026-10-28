module
public import Linear.AcyclicResolutionExtVanishing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]
/-- Unsigned native Yoneda source boundary is ONTO from relative middle-term
Ext vanishing. The signed standard contravariant delta is not identified here. -/
theorem relativeAcyclicContravariantBoundary_surjective
    (F : A) {S : ShortComplex A} (hS : S.ShortExact) (n m : ℕ) (hm : 1+n=m)
    [Subsingleton (Ext S.X₂ F m)] :
    Function.Surjective (hS.extClass.precomp F hm) := by
  intro x
  exact Ext.contravariant_sequence_exact₃ hS F x (Subsingleton.elim _ _) hm
/-- Unsigned native Yoneda source boundary is injective from relative
middle-term Ext vanishing in the PREVIOUS degree. -/
theorem relativeAcyclicContravariantBoundary_injective
    (F : A) {S : ShortComplex A} (hS : S.ShortExact) (n m : ℕ) (hm : 1+n=m)
    [Subsingleton (Ext S.X₂ F n)] :
    Function.Injective (hS.extClass.precomp F hm) := by
  intro x y hxy
  have hz : hS.extClass.comp (x-y) hm = 0 := by
    change (hS.extClass.precomp F hm) (x-y) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  obtain ⟨z,hz⟩ := Ext.contravariant_sequence_exact₁ hS F (x-y) hm hz
  have hzero : z = 0 := Subsingleton.elim _ _
  rw [hzero,Ext.comp_zero] at hz
  exact sub_eq_zero.mp hz.symm
/-- Additive equivalence given by SAME native Yoneda boundary;no replacement
source,class or asserted signed-normalization compatibility. -/
def relativeAcyclicContravariantBoundaryAddEquiv
    (F : A) {S : ShortComplex A} (hS : S.ShortExact) (n m : ℕ) (hm : 1+n=m)
    [Subsingleton (Ext S.X₂ F n)] [Subsingleton (Ext S.X₂ F m)] :
    Ext S.X₁ F n ≃+ Ext S.X₃ F m :=
  AddEquiv.ofBijective (hS.extClass.precomp F hm)
    ⟨relativeAcyclicContravariantBoundary_injective F hS n m hm,
      relativeAcyclicContravariantBoundary_surjective F hS n m hm⟩
/-- GLOBAL Ext shift for SAME original opcycle sequence. Its actual short
exactness is DERIVED from original positive exactness;no projectivity input. -/
def acyclicChainOpcycleGlobalExtShiftAddEquiv
    (K : ChainComplex A ℕ) (F : A) (p q : ℕ) (hK : K.ExactAt (p+1))
    (hA : ∀ j,Subsingleton (Ext (K.X p) F (j+1))) :
    Ext (K.opcycles p) F (q+2) ≃+ Ext (K.opcycles (p+1)) F (q+1) := by
  letI : Subsingleton (Ext (chainOpcycleSequence K p).X₂ F (q+1)) := hA q
  letI : Subsingleton (Ext (chainOpcycleSequence K p).X₂ F (q+2)) := hA (q+1)
  exact (relativeAcyclicContravariantBoundaryAddEquiv F
    (chainOpcycleSequence_shortExact K p hK) (q+1) (q+2) (by omega)).symm
/-- Iterate SAME actual GLOBAL Yoneda source boundaries along original
opcycles. This is an explicit additive equivalence,not vanishing alone. -/
def acyclicChainOpcycleIteratedGlobalExtAddEquiv
    (K : ChainComplex A ℕ) (F : A) (hK : ∀ p,K.ExactAt (p+1))
    (hA : ∀ p j,Subsingleton (Ext (K.X p) F (j+1))) (p q : ℕ) :
    Ext (K.opcycles p) F (q+1) ≃+ Ext (K.opcycles (p+q)) F 1 := by
  induction q generalizing p with
  | zero => exact AddEquiv.refl _
  | succ q ih =>
    let e := (acyclicChainOpcycleGlobalExtShiftAddEquiv K F p q (hK p) (hA p)).trans (ih (p+1))
    have h : (p+1)+q=p+(q+1) := by omega
    have hdeg : q+2=q+1+1 := by omega
    exact (congrArg₂ (fun a b => Ext (K.opcycles p) F a ≃+ Ext (K.opcycles b) F 1) hdeg h).mp e
/-- Existing native contravariant Ext functor transports an ACTUAL source
isomorphism. This reuses mathlib extFunctor rather than a replacement Ext. -/
def acyclicResolutionExtSourceIsoAddEquiv {P Q : A} (e : P ≅ Q) (F : A) (n : ℕ) :
    Ext Q F n ≃+ Ext P F n :=
  (((extFunctor n).mapIso e.op).app F).addCommGroupIsoToAddEquiv
/-- Actual source-isomorphism transport is precisely native precomposition. -/
theorem acyclicResolutionExtSourceIsoAddEquiv_apply {P Q : A} (e : P ≅ Q) (F : A)
    (n : ℕ) (z : Ext Q F n) :
    acyclicResolutionExtSourceIsoAddEquiv e F n z = (Ext.mk₀ e.hom).comp z (zero_add n) := rfl
/-- Actual (possibly unbounded) acyclic resolution computes positive GLOBAL
Ext by Ext^1 of SAME successive opcycles. No desired Ext/H comparison,
source projectivity,coefficient injectivity or signed-delta law is a premise. -/
def acyclicResolutionGlobalExtOpcycleAddEquiv
    (K : ChainComplex A ℕ) (Z : A) (f : K ⟶ (ChainComplex.single₀ A).obj Z)
    [QuasiIso f] (F : A) (hA : ∀ p j,Subsingleton (Ext (K.X p) F (j+1))) (q : ℕ) :
    Ext Z F (q+1) ≃+ Ext (K.opcycles q) F 1 := by
  have hK (p : ℕ) : K.ExactAt (p+1) :=
    (exactAt_iff_of_quasiIsoAt f (p+1)).mpr (ChainComplex.exactAt_succ_single_obj Z p)
  let e := acyclicChainOpcycleIteratedGlobalExtAddEquiv K F hK hA 0 q
  have h := congrArg (fun j => Ext (K.opcycles 0) F (q+1) ≃+ Ext (K.opcycles j) F 1) (Nat.zero_add q)
  exact (acyclicResolutionExtSourceIsoAddEquiv (chainResolutionOpcycleZeroIso K Z f) F (q+1)).trans (h.mp e)
end LinearStudy
