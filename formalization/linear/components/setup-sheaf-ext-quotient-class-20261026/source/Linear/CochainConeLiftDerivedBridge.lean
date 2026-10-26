module
public import Linear.CochainConeLiftClassBridge
public import Mathlib.Algebra.Homology.DerivedCategory.SmallShiftedHom
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LinearStudy
open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
universe u v d
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{d} A]

/-- Equal ACTUAL Hom-complex classes induce the SAME derived morphism. -/
theorem cochainDerivedMap_eq_of_classEq {K L : CochainComplex A ℤ} {n : ℤ}
    (x y : Cocycle K L n) (h : CohomologyClass.mk x = CohomologyClass.mk y) :
    ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q =
      ShiftedHom.map (Cocycle.equivHomShift.symm y) DerivedCategory.Q := by
  have hq := congrArg (CohomologyClass.toHom) h
  simp only [CohomologyClass.toHom_mk] at hq
  have ho := HomotopyCategory.homotopyOfEq _ _ hq
  dsimp only [ShiftedHom.map]
  rw [DerivedCategory.Q_map_eq_of_homotopy A ho]

/-- The actual cone lift relations give the SAME derived maps,without K-injectivity
or global projectivity. The original geometric lift data must still be constructed. -/
theorem cochainConeLiftDerivedBridge
    (S : ShortComplex (CochainComplex A ℤ)) (K : CochainComplex A ℤ)
    (a : Cocycle S.X₁ K 0) (b : Cochain S.X₂ K 0) (c : Cocycle S.X₃ K 1)
    (hb : (Cochain.ofHom S.f).comp b (zero_add 0) = a.val)
    (hc : δ 0 1 b = (Cochain.ofHom S.g).comp c.val (zero_add 1)) :
    ShiftedHom.map (Cocycle.equivHomShift.symm
      ((CochainComplex.mappingCone.fst S.f).postcomp (Cocycle.homOf a))) DerivedCategory.Q =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (c.precomp (CochainComplex.mappingCone.descShortComplex S))) DerivedCategory.Q :=
  cochainDerivedMap_eq_of_classEq _ _ (cochainConeLiftClassBridge S K a b c hb hc)

omit [HasDerivedCategory A] in
/-- The native triangle third map is induced by MINUS the native cone fst cocycle.
Retain this sign before relating the original ordered Koszul functional. -/
theorem cochainConeTriangle_mor3_neg_fst {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (CochainComplex.mappingCone.triangle f).mor₃ =
      Cocycle.equivHomShift.symm (-CochainComplex.mappingCone.fst f) := rfl

end LinearStudy
