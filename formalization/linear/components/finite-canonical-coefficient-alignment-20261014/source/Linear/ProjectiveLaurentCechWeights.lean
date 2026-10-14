/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
module
public import Linear.ProjectiveLaurentInitialRestriction
/- Minimal pure weight objects and cofaces adapted from the pinned
AINTLIB source. No divisor-twist model or geometric hypothesis is imported. -/
@[expose] public section
namespace MvPolynomial
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance coordinateLaurentWeightsDecidableEq : DecidableEq σ := Classical.decEq σ

/-- Ordered Cech terms indexed by global homogeneous Laurent weights. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechObject
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    ModuleCat.{u} Γ(Spec (CommRingCat.of R),
      (⊤ : (Spec (CommRingCat.of R)).Opens)) :=
  ∏ᶜ fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
    ModuleCat.of
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      (AddMonoidAlgebra
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        {e : HomogeneousLaurentExponent σ d //
          e.IsAllowedOn (fun k => (a.1 k).down)})

/-- The ordered Cech coface on homogeneous Laurent weights deletes one entry from the ordered
tuple and extends each allowed weight to the larger intersection. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechCoface
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2)) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d (n + 1) :=
  Pi.lift fun a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
    Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
      ModuleCat.of
        Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
        (AddMonoidAlgebra
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          {e : HomogeneousLaurentExponent σ d //
            e.IsAllowedOn (fun l => (b.1 l).down)})) (a.delete k) ≫
      ModuleCat.ofHom
        (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d)

/-- Projecting a homogeneous-weight coface to an ordered tuple gives the corresponding deletion
map on allowed weights. -/
@[reassoc]
theorem coordinateHomogeneousLaurentOrderedCechCoface_comp_π
    [LinearOrder σ] (d : ℤ) (n : ℕ) (k : Fin (n + 2))
    (a : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1)) :
    coordinateHomogeneousLaurentOrderedCechCoface
        (R := R) (σ := σ) d n k ≫
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1) =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun l => (b.1 l).down)})) a =
      Pi.π (fun b : Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n =>
        ModuleCat.of
          Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
          (AddMonoidAlgebra
            Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
            {e : HomogeneousLaurentExponent σ d //
              e.IsAllowedOn (fun l => (b.1 l).down)})) (a.delete k) ≫
        ModuleCat.ofHom
          (coordinateHomogeneousLaurentDeleteLinearMap (R := R) a k d) := by
  exact Pi.lift_comp_π _ a

/-- The alternating ordered Cech differential in homogeneous Laurent weights. -/
noncomputable def coordinateHomogeneousLaurentOrderedCechDifferential
    [LinearOrder σ] (d : ℤ) (n : ℕ) :
    coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d n ⟶
      coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d (n + 1) :=
  ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
    coordinateHomogeneousLaurentOrderedCechCoface (R := R) (σ := σ) d n k

end
end MvPolynomial
