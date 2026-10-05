# Linear: manuscript Lemma 3.1

## Verified scope

Lean checks 36 auxiliary theorems on actual commutative rings, algebra maps,
ideal quotients, and B-linear multiplication pairings. `Linear.Target` defines
the full `Lemma31Goal`, including the specified power-series Jacobian and
arbitrary lifts of parameters. **The full goal is not yet proved.**

The perfect multiplication pairing is an explicit input to `Linear.Duality`.
The library proves its consequences, not its existence for complete
intersections. The general primitive-generator coefficient step is now proved in `Linear.Primitive`. The specific Jacobian still has not been shown to satisfy its hypotheses.

`Linear.DoublePoint` constructs a perfect pairing for `A = B ⊕ Bε` and
identifies its nilradical over a reduced base. `Linear.FirstJet` now proves
the actual `B[[X]]/(X²)` presentation and identifies the actual defining
Jacobian with `2ε`. If 2 is a unit, the first Jacobian-annihilator conclusion
is proved for this genuine power-series family. The arbitrary-equation
universal theorem and its arbitrary-parameter-lift conclusion remain open.

`Linear.GenericFiber` proves localization injectivity from flatness and
descends ideal annihilation from that localization. It still takes the
localized SS identity as input. `Linear.PairingMatrix` constructs the perfect
pairing from a finite basis, a functional, and its nonzero reduced Gram
determinant. It does not yet construct the functional from the Gorenstein
complete-intersection theorem.

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

## Publish a checked checkpoint

After building, write the exact declaration audit and whole-module audit logs.
The publisher refuses failed builds, disallowed axioms, an empty module audit,
or an un-audited theorem. Run from the module directory:

```sh
python3 scripts/export_snapshot.py --build-log /path/to/build.log \
  --axiom-log /path/to/axioms.log --full-audit /path/to/full-audit.json
```

The entire module audit uses `axiom-audit` v0.1.2, commit
`46024e005996495c65ef609368e11ab39c4222e3`, with `--root Linear`.
`LinearStudy` is the declaration namespace, not the importable module root.
Keep `mainTheoremVerified` false until the full `Lemma31Goal` has a proved
declaration with its original hypotheses and a clean axiom audit.
