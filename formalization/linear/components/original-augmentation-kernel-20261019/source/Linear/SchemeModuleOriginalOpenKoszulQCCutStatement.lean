module
public import Linear.SchemeModuleOriginalOpenKoszulCutStatement
public import Linear.SchemeModuleOpenQuasicoherentCoefficientIso
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 50000
namespace LinearStudy
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] schemeModuleOpenRestriction_additive
attribute [local irreducible] schemeModuleOriginalOpenKoszulCutStatement
variable (R : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
variable (p : ℕ) (H : Fin (p+1) → R) (C : ChainComplex X.Modules ℕ)
variable (gamma : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅
  tildeFunctionKoszulComplex R H)
variable {E : X.Modules} (alpha : C ⟶ (ChainComplex.single₀ X.Modules).obj E)
variable (hAlpha : QuasiIso alpha) (hAbove : IsZero (C.X (p+2)))
/-- The SAME class statement for EVERY actual quasicoherent coefficient and EVERY top functional. Its affine tilde frame and closedness are constructed. This is a Prop definition, not a proof. -/
def schemeModuleOriginalOpenKoszulQCCutStatement : Prop :=
  ∀ (N : X.Modules) (hN : N.IsQuasicoherent) (a : C.X (p+1) ⟶ N),
    letI := hN
    schemeModuleOriginalOpenKoszulCutStatement R j p H C gamma N
      ((moduleSpecΓFunctor (R := R)).obj (N.restrict j))
      (schemeModuleOpenQuasicoherentCoefficientIso R j N) alpha hAlpha a
      (hAbove.eq_of_src _ _)
/-- Prove the all-coefficient statement from actual source internal Ext vanishing; no frame, Hom square or desired class formula is a hypothesis. -/
theorem schemeModuleOriginalOpenKoszulQCCutStatement_proof
    (hA : ∀ (N : X.Modules) (hN : N.IsQuasicoherent) q v,
      IsZero (schemeModuleInternalExt (C.X q) N (v+1))) :
    schemeModuleOriginalOpenKoszulQCCutStatement R j p H C gamma alpha hAlpha hAbove := by
  intro N hN a
  letI := hN
  exact schemeModuleOriginalOpenKoszulCutStatement_proof R j p H C gamma N
    ((moduleSpecΓFunctor (R := R)).obj (N.restrict j))
    (schemeModuleOpenQuasicoherentCoefficientIso R j N) alpha hAlpha
    (injectiveResolution N) (hA N hN) hAbove a (hAbove.eq_of_src _ _)
end LinearStudy
