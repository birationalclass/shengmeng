module
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.RingTheory.Artinian.Module
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearStudy
open AlgebraicGeometry CategoryTheory
universe u v

/-- The ACTUAL Spec of a finite algebra over a field is Artinian,using
native finite-module Artinian and native Artinian-scheme equivalence. -/
theorem finiteFieldAlgebra_spec_isArtinian
    (k : Type v) [Field k] (R : CommRingCat.{u}) [Algebra k R]
    [Module.Finite k R] : IsArtinianScheme (Spec R) := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite k R
  infer_instance

/-- Transfer Artinian structure through an ACTUAL scheme isomorphism
with the SAME finite original coordinate algebra. -/
theorem finiteFieldAlgebra_scheme_isArtinian_of_iso
    (k : Type v) [Field k] (R : CommRingCat.{u}) [Algebra k R]
    [Module.Finite k R] (X : Scheme.{u}) (e : X ≅ Spec R) :
    IsArtinianScheme X := by
  letI := finiteFieldAlgebra_spec_isArtinian k R
  letI : IsLocallyArtinian X := IsLocallyArtinian.of_isImmersion e.hom
  letI : CompactSpace X := e.hom.homeomorph.symm.compactSpace
  exact {}

/-- In particular the ACTUAL original finite cut scheme has finite
underlying points and discrete topology,without assuming either. -/
theorem finiteFieldAlgebra_scheme_finite_discrete_of_iso
    (k : Type v) [Field k] (R : CommRingCat.{u}) [Algebra k R]
    [Module.Finite k R] (X : Scheme.{u}) (e : X ≅ Spec R) :
    Finite X ∧ DiscreteTopology X := by
  letI := finiteFieldAlgebra_scheme_isArtinian_of_iso k R X e
  exact ⟨inferInstance,inferInstance⟩

end LinearStudy
