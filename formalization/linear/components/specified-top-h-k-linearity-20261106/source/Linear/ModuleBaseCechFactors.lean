/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Linear.ModuleBaseCechBasic
public import Mathlib.Algebra.Category.ModuleCat.Products

/- Minimal adaptation of CBirkbeck/AINTLIB, commit ab1451487da02cd4483d0e2cdb2cc9e44bbbac17
   projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleBaseCechFlat.lean
   Upstream SHA-256 eeec8c9329708b147b57e17ba8f68b21f25d9f597bd1668f12d30c3dfaf1f927
   Actual intersection factors and Pi comparison only; omit flatness/Common imports.
   Original4.1/4.2 and the uniform positive-twist bound remain open. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- One intersection-section factor in a degree of the base-linear Cech
complex. -/
abbrev baseCechFactor {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) (i : Fin (n + 1) → ι) :=
  (baseModulePresheaf π M).obj (op (∏ᶜ fun k : Fin (n + 1) => U (i k)))

/-- A degree of the base-linear Cech complex is the concrete dependent
product of its intersection-section factors. -/
def baseCechXIsoPi {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (n : ℕ) : (baseCechComplex π M U).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : Fin (n + 1) → ι, baseCechFactor π M U n i) :=
  ModuleCat.piIsoPi _

end
end AlgebraicGeometry.Scheme.Modules
