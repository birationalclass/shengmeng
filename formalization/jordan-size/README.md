# Jordan Size — Lemmas 1.1–1.4

`lemma_1_2`, `lemma_1_3`, and `lemma_1_4` verify the chain-product calculation, perfect-pairing transport and maximal-endpoint vanishing. The new chains are explicit independent families. Lemma 1.3 verifies all shifted-power kernel dimensions and constructs transferred chains. Corollary 1.4 deduces both vanishing statements without assuming them.

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

The final proof world targets Corollary 1.4, with independent nested modules for Lemmas 1.2 and 1.3. Lemma 1.1 remains independently accessible; it is not presented as a dependency of Corollary 1.4. Current evidence: `chains-build.log`, `chains-types.log`, and `audit.json`.
