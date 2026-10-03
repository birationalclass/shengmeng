module

/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A replacement for the eight-line finite-product flatness leaf in AINTLIB.Common.
It imports only the relevant Mathlib development, dropping the unrelated
Dirichlet-bounds dependency.
Original blob SHA-256: a83460e5fedab60f6c9e8a88e6785cb145bd27c98d2d7b48cdf2b5b3b77d010b.
The identical blob appears under the root Apache 2.0 license at
commit 1c1c74664e40071c2c2165bc55ca2616a67ccd6b.
-/

public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

/-- A finite product of flat modules is flat, by its linear equivalence with a direct sum. -/
instance Module.Flat.pi {R : Type*} [CommSemiring R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] : Module.Flat R (∀ i, M i) := by
  cases nonempty_fintype ι
  exact Module.Flat.of_linearEquiv
    (DirectSum.linearEquivFunOnFintype R ι M).symm
