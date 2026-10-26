# Finite Groups of Orders 1–100

The page starts with order 1 and proceeds through order 100. It uses the current
`abundance/note.css` reading layout, shared gallery palette, local KaTeX fonts,
and native, initially closed proof controls. It does not inherit the Abundance
note's author-supplied verification badges.

`lecture.tex` is the PDF source. `content.json` holds the order-by-order prose
and proofs, with the source SHA-256 checked by `build.mjs`. `groups.json` contains
all 1,048 SmallGroups identifiers and exact pc presentations. Its 862
nonabelian solvable presentations were independently reconstructed with
`SingleCollector`, `SetPower`, and `SetCommutator`, and checked using `IdGroup`.
The other types are 185 abelian groups and A5.

Build with `node study/finite-groups/build.mjs` from the repository root.
All formulas, including the initially hidden presentations, are parsed at build
time with errors fatal. Presentation formulas are rendered in the browser when
opened. Full group descriptions and classification conclusions remain visible.
Proofs, without invented completeness arguments for larger orders, are folded.

The PDF is `finite-groups-1-100.pdf`. Its Chinese CID fonts include explicit
Unicode maps for portable searching and copying.

For future updates, keep groups sorted by order and SmallGroups index, preserve
all types, update the TeX and prose together, rebuild, and check desktop/mobile
formulas, keyboard controls, anchor links and the deployed PDF. No edits to
the original Abundance journal or reading page are needed.

## Title font

The title uses LiXuKe (selected sample 13), with permission for public web use.
`fonts/lixuke-title.ttf` is a seven-character title subset and retains the
original `(c) Copyright LiXuKe` notice. The existing OFL file applies to the
retained Liu Jian Mao Cao font, not to LiXuKe.
