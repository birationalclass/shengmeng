# Milestone 38: actual formal coordinate rings are Cohen–Macaulay

A regular sequence generating a Noetherian local ring maximal ideal proves its Cohen–Macaulay property: the audited height theorem identifies dimension with sequence length, and the depth supremum theorem supplies the matching lower bound. Apply to the actual power-series coordinate sequence. Both Cohen–Macaulay property and exact dimension n are proved for K[[Fin n]], n > 0, over any field.

Transport along the existing constructed nestedPowerSeriesEquiv proves the same property and dimension r+c of K[[s_1,...,s_r]][[z_1,...,z_c]]. Neither property nor dimension is assumed. This serves the remaining regularity and flatness bridge for the manuscript thickening.

Discovery: inspected the official pinned mathlib tree online for regular/free and Krull dimension code; the subsequent raw-source fetch timed out and is not counted as successful. Reuses the fully inspected pinned Regular/Free.lean interface and the previously audited minimally ported CM/depth declarations whose provenance remains recorded. The existing public variable-regularity proof supplies the actual regular sequence.

The global Linearity Theorem remains unproved. No new axiom or opaque dimension/regularity assumption.
