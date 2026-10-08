# Checkpoint 85: separate the original cone scaling coordinate

This checkpoint is partial progress toward the original Linearity Theorem.
The final theorem is not proved.

- The actual original cone pullback's module rank equals the degree over its actual fraction-field image.
- Combining this with checkpoint 84 computes that **cone** degree as `q^C.natDegree`, with C the derived cumulative Hilbert polynomial of the original ideal.
- Construct actual homogeneous scaling maps. They act identically on the projective points and fix the entire original coordinate-ratio field.
- Use infinitely many scaling images to prove the original nonzero cone coordinate transcendental over the original ratio field.
- Prove the original cone fraction field is generated over that ratio field by this coordinate; construct the actual rational-function-field algebra isomorphism and its value on X.
- For the original homogeneous pullback, construct a nonzero coefficient u in the original ratio field and prove its scaling-coordinate image is `u*t^q`.
- Reuse mathlib's rational-function degree formula to prove the scaled-power subextension has degree q, and transfer it through an actual rational-function algebra isomorphism.

No transcendence assumption, arbitrary replacement map, growth function, or supplied degree formula discharges any of these original-object conclusions. The general degree-transfer lemma has its rational-function isomorphism as an explicit input; the original geometric application constructs that isomorphism separately.

The **full** identity relating the cone image-field degree to q times the original projective image-field degree is still open. So are the identification of Hilbert polynomial degree with geometric dimension, the resulting `D=q^dim(V)`, the global geometric duality/Serre lifting, and the actual Cartier/Bézout inequality. This checkpoint proves neither the main theorem nor the full manuscript Lemmas 3.1/4.2.

Source/type/hash and axiom evidence: snapshot.json, full-audit.json, build.log, and research/checkpoint85-private-provenance.json. Read these after the required public build and full audit; private compilation alone does not certify the public checkpoint.
