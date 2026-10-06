# Milestone 15 — lifted parameters and finite freeness foundations

The full Linearity Theorem and full `Lemma31Goal` are still UNPROVED. This milestone advances the arbitrary-parameter part of the original target; the paper source was not edited.

New compiled work:

- `RegularGeneratorsFree`: a weakly regular sequence generating the maximal ideal of a local Noetherian ring makes every finite module on which it is weakly regular free. The proof descends to the residue field and uses mathlib's `Module.free_quotSMulTop_iff_free` to ascend. An algebra-map variant connects regularity in the algebra to freeness over its base.
- `LiftedParametersRegular`: arbitrary lifts whose reductions generate the power-series parameter maximal ideal are regular. Flatness first carries base regularity to the algebra; the difference from a canonical lift lies in the nilradical; the compiled nilpotent-perturbation theorem applies. A corollary has the exact original `CompleteIntersection H` notation and derives its local Noetherian hypotheses from the original regular equations.
- `LiftedParameterCoordinates`: construct a genuine ambient ring automorphism from representatives P whose normal constant coefficients generate the parameter maximal ideal. It sends parameter variables to P and fixes normal variables. Composing its restriction with the equation quotient constructs an actual parameter ring homomorphism and Algebra structure; no substitution inverse or new algebra action is taken as an assumption.

Precisely unfinished: use the original reduction and centering to obtain the required representatives for every arbitrary parameter lift; identify the induced reduction as the actual base parameter automorphism; prove finiteness and freeness of the new action; construct its perfect pairing and compare the socle. `ParameterPairingChange` still has explicit compatibility and pairing inputs. No helper discharges those inputs merely by definition.

Library discovery: pinned `Mathlib/RingTheory/Regular/Free.lean`, `Regular/RegularSequence.lean`, `Finiteness/NilpotentKer.lean`, `LocalRing/RingHom/Basic.lean`, the existing project coordinate chart and parameter substitution modules. Online primary-source searches for the exact freeness declaration returned no indexed result; the official raw pinned source URL could not be fetched. The complete pinned local source and exact theorem types were inspected and reused. No claim that no other implementation exists is made.

Build and complete axiom/type/source-range audit are recorded in `build.log`, `full-audit.json`, `snapshot.json` and `axioms.log`. Published snapshots and newer local work remain separately recorded in `release.json`.
