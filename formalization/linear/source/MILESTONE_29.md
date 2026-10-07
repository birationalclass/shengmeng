# Milestone 29: highest-part regularity derived from origin-only zeros

The full Linearity Theorem remains **UNPROVED**. The manuscript is unchanged.

The highest homogeneous parts of the actual affine equations no longer need a separate regular-sequence hypothesis in the new final affine pairing and weighted-relation theorems. Positive degrees and an origin-only common zero locus over an algebraically closed characteristic-zero field imply that hypothesis. The point-relation theorem still explicitly requires the chosen Theta to generate each local nilradical annihilator.

The proof derives regularity at the origin using actual polynomial Cohen–Macaulayness, the actual origin maximal ideal and its height. It then descends weak regularity to the polynomial ring using homogeneous-ideal saturation and contraction under origin localization. The homogeneous quotient's properness yields the complete regular sequence. An actual projective coordinate chart with a hyperplane avoiding the selected fiber also supplies this regularity, provided the specified boundary forms are nonzero. Chart existence is still open.

Eleven new project proofs have passed root compilation and the complete axiom audit. Current totals: 488 project theorem/lemma proofs, 96 definitions; 780 audited declarations including attributed ports; 109 exported Lean files. Only `propext`, `Classical.choice` and `Quot.sound` occur among audited axioms. The exact original relative local `Lemma31Goal` remains proved by `lemma31_complete`; the full global target remains unproved.

Library-first discovery used Guan–Hu's primary formalization paper <https://arxiv.org/html/2510.24818v1>, official mathlib documentation and original open mathlib pull requests 26218, 26245 and 28599. Five missing modules were inspected and adapted from fixed commits, with original Apache-2.0 notices, source URLs, original/adapted hashes and exact declarations in `vendor-provenance.json`. Those results are attributed ports, not claims about availability in the pinned mathlib. The local project continues to use Lean 4.35.0-rc3 and mathlib 2a885768dae569d938bb9ff3474da6a8753bb90a.

Next: construct the actual ambient completion quotient comparison and transfer local socle generators, then derive the remaining smooth-coordinate/geometric and uniform-duality inputs. The last verified deployed version remains milestone 18; milestone 19 publication awaits the pending user response after two automatic push-approval timeouts. This local milestone is not claimed as deployed.
