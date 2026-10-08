# Nagata: imported official formalization

Repository: https://github.com/openai/math
Pinned commit: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
Target: OAI.Nagata.nagata_conjecture
117 project-source files, complete transitive OAI import closure.
Upstream version: Lean 4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

The project lakefile is reduced to the mathlib dependency used by this closure.
The OAI proof source files are unchanged. Original release configuration and
Comparator references are supplied separately in release-metadata.

Reproduce using the fixed toolchain:
    lake update
    lake exe cache get
    lake build
    lake env lean CheckAxioms.lean

This imports the existing published proof; it is not a new proof by the user or Codex.
The accompanying Comparator challenge contains intentional `sorry` targets for
comparison. It is a reference statement, not the solution proof, and is not
imported by OAI.lean or CheckAxioms.lean. Run the upstream Comparator workflow
separately; ordinary Lean compilation does not establish Comparator success.

See the atlas evidence for actual local build status. An installed-version
compatibility attempt is distinguished from reproduction at the upstream pins.

Local verification: all 117 original source files compiled at the upstream pins; nine named declarations passed the kernel/axiom audit.
Comparator was not replayed locally. No independent mathematical refereeing is claimed.
