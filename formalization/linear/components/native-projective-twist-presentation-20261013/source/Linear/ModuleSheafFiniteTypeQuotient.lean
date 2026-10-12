/- Minimal adaptation of CBirkbeck/AINTLIB at ab1451487da02cd4483d0e2cdb2cc9e44bbbac17, projects/ModularCurves/ModularCurves/ForMathlib/SheafModuleFiniteTypeQuotient.lean. Names and namespace changed; original Apache attribution retained. This finite-type closure lemma supports the next Serre-presentation step and does not prove eventual vanishing or original4.1/4.2. -/
/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `SheafFiniteTypeQuotient.lean`
in Vilin97/Clawristotle.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Finite-type sheaves of modules and quotients

Finite local generators descend along an epimorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option autoImplicit false
open SheafOfModules

universe u

namespace LinearStudy

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A quotient of a finite-type sheaf of modules is finite type. -/
theorem moduleSheafIsFiniteType_of_epi
    {M N : SheafOfModules.{u} R} (p : M ⟶ N)
    [Epi p] [M.IsFiniteType] :
    N.IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  letI : P.IsFiniteType := hP
  have hEpi (i : P.I) : Epi (p.over (P.X i)) := by
    let adj := overPushforwardOverAdj (R := R) (P.X i)
    letI :
        PreservesColimitsOfShape WalkingSpan
          (overFunctor R (P.X i)) :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    apply Functor.map_epi
  let Q : N.LocalGeneratorsData :=
    { I := P.I
      X := P.X
      coversTop := P.coversTop
      generators := fun i => by
        letI : Epi (p.over (P.X i)) := hEpi i
        exact (P.generators i).ofEpi (p.over (P.X i)) }
  refine ⟨⟨Q, ?_⟩⟩
  constructor
  intro i
  letI : (P.generators i).IsFiniteType :=
    LocalGeneratorsData.IsFiniteType.isFiniteType (p := P) i
  refine { finite := ?_ }
  dsimp [Q]
  exact GeneratingSections.IsFiniteType.finite
    (σ := P.generators i)

end LinearStudy
