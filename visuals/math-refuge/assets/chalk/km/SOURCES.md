# Kollár–Mori reading seminar

Original bilingual teaching notes organised around the 7 chapters and 38 sections of János Kollár and Shigefumi Mori, *Birational Geometry of Algebraic Varieties*, Cambridge Tracts in Mathematics 134 (1998), https://doi.org/10.1017/CBO9780511662560 . The source book was consulted locally. No scans, source PDF or full book text are included.

336 boards: 260 substantive boards, 38 section title boards and 38 section closing boards. Each student session covers one section, not an entire chapter. §1.1 has 32 substantive boards, developed against printed pp.8–15: assumptions, rigidity, both bend-and-break arguments, deformation bounds, Frobenius and bounded-degree return to characteristic zero. The deformation theory and Hodge index theorem are explicitly invoked prerequisites. Other sections currently remain preparation outlines, not completed detailed student talks. Each original section has a prerequisite list, learning objective, definitions, calculations, theorem statements or explicit proof maps. Advanced proof maps are labelled as such: they are not claimed to replace all technical lemmas or the full proofs in the book. The scope is the 1998 text; statements about arbitrary-dimensional existence, termination or abundance are not silently upgraded to modern results.

Original diagrams illustrate ADE graphs, a common resolution, the blow-up of two crossing lines, and two small models over a common target. These are schematic redrawings of mathematical constructions, not reproductions of book figures.

## Lemma 5.17(2) erratum

Osamu Fujino, *What is log terminal?*, author preprint dated 23 April 2004, Remark 10.3, p.16:
https://www.math.nagoya-u.ac.jp/~fujino/what-HP.pdf

Published in *Flips for 3-folds and 4-folds* (2007), pp.49–62; published chapter numbering Remark 3.10.6:
https://doi.org/10.1093/acprof:oso/9780198570615.003.0003

The equality in KM98 Lemma 5.17(2) is false in general. For X=P², B=L one line, and H a general other line, KM's exceptional-divisor discrepancy of (X,L) is 0. Blowing up L∩H gives coefficient 1−1−1=−1. The snc pair is lc, so discrep(X,L+H)=−1, whereas the asserted right-hand side is 0. Six consecutive boards work through this computation. The log discrepancy of this exceptional divisor is 0; switching conventions does not repair the original equality.

Part (1) is distinguished from the erroneous part (2). Notes explain that Corollary 5.18 uses the restriction statement, and later adjunction/cover arguments do not use the false equality. The navigation has an always-visible erratum warning when the KM curriculum is open and a direct jump to the computation.

## Rebuilding

`node build-chalk-notes.mjs /path/to/mathjax-full-3.2.2 km`

The build renders local MathJax SVG assets; the runtime uses the shared printed-math and handwritten-prose renderer. Rebuild the shared Chinese font subset using `build-chalk-font.py` after changing Chinese text.
