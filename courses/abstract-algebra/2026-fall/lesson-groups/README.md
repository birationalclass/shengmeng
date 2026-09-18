# Chapters 1–2 · Interactive group theory courseware

Public student courseware for Abstract Algebra I, Autumn 2026. It follows the course's Han–Lin–Du third-edition section outline and reuses the first lesson's notebook, theme settings, keyboard navigation, and responsive layout. The existing §1.1–§1.2 and encrypted teacher plan are unchanged.

## Coverage and teaching sequence

| Section | Main content | Demonstrations |
| --- | --- | --- |
| 1.3 | Subgroup criteria; intersections; generators; center and centralizers | Select subsets in cyclic/dihedral groups and compute closure |
| 1.4 | Isomorphisms; invariants; Cayley; automorphisms | Fourth roots; order counts; regular permutations; conjugation |
| 1.5 | Cyclic classification; subgroups; orders of powers; generators | Vary modulus and element; generated sets and divisor subgroups |
| 1.6 | Composition; disjoint cycles; orders; parity; alternating groups | Track composition point by point; compute cycles, order and sign |
| 1.7 (optional) | Dihedral, tetrahedral and cube symmetry groups | Labeled polygon transformations |
| 2.1 | Cosets; index; Lagrange; prime-order groups; index multiplication | Compute all cosets and left/right translates |
| 2.2 | Normality; index two; well-defined products; quotient axioms | Nonnormal witness; quotient table; all representative products |
| 2.3 | Homomorphisms; kernel/image; fibers; first isomorphism theorem; correspondence; iterated quotients | Change a residue map and inspect every fiber |
| 2.4 | External/internal products; element orders; cyclic products; CRT | Walk in a product of cycles |
| 2.5 | Actions; orbits/stabilizers; class equation; p-group centers; Burnside; coset actions | Vertex/diagonal actions; conjugacy classes; binary square colorings |
| 2.6 | Sylow statements and normalizers; uniqueness; applications in orders 15,21,30,12 | Filter subgroup-count candidates; distinguish necessary constraints from realizability |
| 2.7 (optional) | Reduced words; free groups; universal property; presentations | Enter words; step through cancellation; derive dihedral normal forms |

The current published schedule has §1.1 in meeting 1, §1.2–§1.3 in meeting 2, then §1.4, §1.5, §1.6 in meetings 3–5. Meetings 6–8 cover §2.1–§2.3. Meeting 9 covers §2.4 and the beginning of §2.5; meeting 10 continues §2.5; meeting 11 covers Sylow applications and synthesis. §1.7 and §2.7 are optional and do not add required meetings.

New material: 76 reading entries, 57 stepwise proofs, 48 multiple-choice questions and 12 written exercises with solutions. The original first lesson contributes the first two sections in addition. Questions are original and do not claim textbook exercise numbers. The section outline is the reference; no unverified theorem numbering or page numbers have been added.

## Interface

Open the semester portal with `?view=lesson&section=2.5`, for example. The directory lists every topic and the previous/next header buttons move between sections. On desktop, left-hand statements remain alongside the right-hand demonstration or proof. On mobile, a section-entry selector and one reading column replace the two-column layout. Enter/Space and the Continue button advance the shared reader; arrows move through entries. A proof begins only after the full statement is displayed. Chinese and English text is available throughout. Quiz answers and proof notes are stored locally by section, never sent to a server.

## Files and checks

- `content.js`, `chapter-two.js`: bilingual original notes, mathematical statements and proof steps.
- `models.js`: exact finite groups, closure, cosets, conjugation, cycle decomposition, Sylow constraints and word reduction.
- `visuals.js`: diagrams driven by these models.
- `exercises.js`: original questions, explanations and written problems.
- `lesson.js`: first-lesson-compatible renderer and saved self-check state.
- `groups.css`: diagram styles using the existing theme variables.
- `../group-sections.js`: directory topic manifest, matching entry IDs.
- `models.test.cjs`: exhaustive small-group checks, minimal generated subgroups, coset partitions, quotient representative independence, cyclic-order formulas, Burnside counts, word associativity and all TeX statements.

Run `node courses/abstract-algebra/2026-fall/lesson-groups/models.test.cjs` from the repository root. KaTeX is loaded from the site's existing local vendor directory; there is no new remote runtime dependency.
