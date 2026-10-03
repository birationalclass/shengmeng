module
public import Negativity.ActualNativeUnitCechCycles
public import Negativity.ActualCechAmbientModule

@[expose] public section
namespace Negativity
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem actualNativeUnitCechCycleEquiv_smul {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) (r : Γ(S,⊤))
    (a : ((Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).sc' 0 1 2).g.hom.ker) :
    letI := actualCechCycleGlobalModule X U
    letI : Module Γ(S,⊤) (actualCechCocycles X U) :=
      Module.compHom (actualCechCocycles X U) f.appTop.hom
    actualNativeUnitCechCycleEquiv f U (r • a) =
      r • actualNativeUnitCechCycleEquiv f U a := by
  letI := actualCechCycleGlobalModule X U
  letI : Module Γ(S,⊤) (actualCechCocycles X U) :=
    Module.compHom (actualCechCocycles X U) f.appTop.hom
  apply Subtype.ext
  exact actualNativeUnitCechOneEquiv_smul f U r a.1

/-- Native structure-sheaf H¹ and actual all-pairs H¹ agree for every
base scalar, through actual native cycles and their actual boundaries. -/
def actualNativeUnitCechHOneLinearEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type u} (U : ι → X.Opens) :
    letI := actualCechHOneGlobalModule X U
    letI : Module Γ(S,⊤) (actualCechHOne X U) :=
      Module.compHom (actualCechHOne X U) f.appTop.hom
    (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).homology 1 ≃ₗ[Γ(S,⊤)]
      actualCechHOne X U := by
  letI := actualCechCycleGlobalModule X U
  letI : Module Γ(S,⊤) (actualCechCocycles X U) :=
    Module.compHom (actualCechCocycles X U) f.appTop.hom
  letI := actualCechHOneGlobalModule X U
  letI : Module Γ(S,⊤) (actualCechHOne X U) :=
    Module.compHom (actualCechHOne X U) f.appTop.hom
  refine { actualNativeUnitCechHOneAddEquiv f U with map_smul' := ?_ }
  intro r x
  let K := (Scheme.Modules.baseCechComplex f (SheafOfModules.unit X.ringCatSheaf) U).sc' 0 1 2
  let q := QuotientAddGroup.congr _ _ (actualNativeUnitCechCycleEquiv f U)
    (actualNativeUnitCechCycleEquiv_range f U)
  have hq (z : K.moduleCatLeftHomologyData.H) : q (r • z) = r • q z := by
    induction z using QuotientAddGroup.induction_on with
    | H a =>
      change QuotientAddGroup.mk' _ (actualNativeUnitCechCycleEquiv f U (r • a)) =
        QuotientAddGroup.mk' _ (r • actualNativeUnitCechCycleEquiv f U a)
      rw [actualNativeUnitCechCycleEquiv_smul]
  change q (K.moduleCatHomologyIso.toLinearEquiv
      ((actualNativeUnitCechHOneExplicitIso f U).toLinearEquiv (r • x))) =
    r • q (K.moduleCatHomologyIso.toLinearEquiv
      ((actualNativeUnitCechHOneExplicitIso f U).toLinearEquiv x))
  simp only [map_smul]
  exact hq _

#print axioms actualNativeUnitCechHOneLinearEquiv
end
end Negativity
