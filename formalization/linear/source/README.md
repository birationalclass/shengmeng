# Linear: manuscript Lemma 3.1

## Verified scope

Lean checks 11 auxiliary theorems on actual commutative rings, algebra maps,
ideal quotients, and B-linear multiplication pairings. `Linear.Target` defines
the full `Lemma31Goal`, including the specified power-series Jacobian and
arbitrary lifts of parameters. **The full goal is not yet proved.**

The perfect multiplication pairing is an explicit input to `Linear.Duality`.
The library proves its consequences, not its existence for complete
intersections. The dual generator η has not yet been identified with Δ.

Open bridges:

1. Construct the perfect pairing for finite flat complete intersections.
2. Formalize the Scheja–Storch Jacobian theorem on the generic and closed
   fibers, descend annihilation, and prove the primitive-generator assertion.
3. Construct formal parameter substitution for arbitrary lifts τ, establish
   finite freeness over the new parameter ring, and prove the final socle claim.

## Reproduce

Install elan, then in this directory run:

```sh
lake update
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

The toolchain and mathlib commit are pinned in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. The audit permits only Lean's
standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
Passing the audit does not discharge explicit theorem hypotheses.

The webpage's arrows show mathematical dependencies in the manuscript and
formalization plan. They are not an automatically extracted kernel graph.
