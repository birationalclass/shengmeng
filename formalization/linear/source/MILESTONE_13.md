# Milestone 13: exact card counts and arbitrary-parameter linear part

The full Linearity Theorem and full Lemma31Goal remain unproved.
299 project proofs and 74 definitions pass the kernel audit. The 463
audited declarations have no sorryAx or new project axiom.

## Source counting

Ordinary cards and gold targets count their own compiler-recorded
declaration range only. Pack covers include every member's code and
actual project-code dependencies; intervals in the same file are merged.
External mathlib code is excluded. The header separately counts all
exported Lean files. Missing declarations show unavailable or a partial
pack count, not zero and not a changed proof-status badge.

For primitive_annihilator_generates the actual range is
Linear/Primitive.lean:69-78, ten physical lines. Its proof package uses
352 distinct project-source lines. Shared dependencies count once.
505 source-range records were extracted from the compiled environment
using Lean.findDeclarationRanges? and ConstantInfo.getUsedConstantsAsSet.
An independent set of individual file/line pairs checks every pack total;
additional checks cover duplicate dependencies, overlapping intervals,
same-file statements of different lengths and missing metadata.

The personal lean-explain skill and its interface reference now prescribe
the same distinction for future independent projects.

## Mathematical advance

If as many actual power series T_i as variables generate the maximal
ideal of K[[s]], their constant terms vanish and their derivative matrix
at zero has unit determinant. The proof expresses every coordinate in
the T_i ideal and differentiates that exact identity to produce a left
inverse matrix. This is a prerequisite for the arbitrary-parameter
construction; a formal inverse, the new parameter-base action, finite
flatness and socle comparison remain unfinished.

No publication or source-size measure completes the geometric theorem.
