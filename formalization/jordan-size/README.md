# Jordan Size — Lemma 1.1

The integrated declaration is `JordanSize.lemma_1_1` in `lean/Lemma11.lean`.
The scalar-extension bridge is `JordanSize.log_baseChange`.

Checked environment: Lean 4.35.0-rc3 and mathlib commit
`2a885768dae569d938bb9ff3474da6a8753bb90a`.
Compile the source modules in the import order recorded by their `import`
statements, with this `lean` directory and the mathlib build libraries on
`LEAN_PATH`. `lean/AuditComplete.lean` checks every displayed declaration's
exact type and axioms. The complete build and type-check logs are included.
`audit.json` records SHA-256 hashes of every exported Lean source file.

The statement is ordinary finite-dimensional linear algebra over an
algebraically closed characteristic-zero coefficient field, including
arbitrary equivariant multilinear maps. The rational-to-real/complex
operator extension is checked separately. Jordan sizes are represented
through generalized-eigenspace annihilation and the full kernel-growth
profile; an explicit Jordan basis is not constructed. The coefficient
field is distinct from any possible geometric base field.

This is an independent module. The Negativity interface is reused, but
its mathematical declarations are not dependencies of this project.
Private study manuscripts are not included.
