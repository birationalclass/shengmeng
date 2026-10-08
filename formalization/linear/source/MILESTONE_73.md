# Local checkpoint 73: a whole reduced fiber and its exact point count

The exact `LinearityTheoremGoal` remains **unproved**.

Starting from the ORIGINAL positive-degree base-point-free homogeneous map,
its surjectivity on projective points, the original homogeneous-prime V,
total invariance and an inhabited standard affine chart, the construction
now gives a target y whose ENTIRE point fiber is finite and avoids the source
coordinate hyperplane. Its explicit polynomial fiber-equation quotient Q_y
is finite-dimensional and reduced, and the cardinality of the entire
projective fiber equals `Module.finrank ℂ Q_y`.

Neither reducedness, a point-count formula, a good whole fiber, nor a
replacement algebra action is assumed. The denominator class in Q_y is
proved a unit from no base point, even before removing possible nilpotents.
The actual localization quotient map is surjective and its composition with
the original chart pullback equals target evaluation followed by scalars.
The constructed target unramified open then implies reducedness by the
pinned formally-unramified field theorem. Actual residue maps and the Chinese
remainder theorem identify a finite reduced complex algebra with its point
function algebra. Explicit coordinate-ratio maps identify those points with
the ENTIRE projective point fiber.

This checkpoint adds 26 theorem proofs and 4 definitions across 12 modules.
The full audit passes: 975 project theorem proofs, 192 definitions,
1363 audited declarations, and 284 Lean source files. Only `propext`,
`Classical.choice` and `Quot.sound` occur; no `sorryAx` or new project axiom.

Open: Q_y has NOT yet been identified with the tensor-product/Scheme fiber
in this audited checkpoint, and its dimension has NOT been proved to be q^r.
General good fibers, Bertini choices, geometric dimension comparisons,
uniform global Koszul/duality/Serre polynomial lifting and actual geometric
Bezout remain obligations. Point count equals vector-space dimension alone
does not establish the Linearity Theorem.
