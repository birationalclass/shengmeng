# Milestone 32: arbitrary-point ambient formal coordinates

Constructed actual ring isomorphisms, not assumed comparison fields:

- Polynomial translation transports the origin ideal to the evaluation kernel.
- It induces a point-localization isomorphism with a canonical polynomial-image formula.
- Compatible quotient-ring isomorphisms induce a completion isomorphism, including its action on original elements.
- Composing these with the audited origin comparison yields `polynomialPointFormalCompletionEquiv` over any field and finite set of variables.
- A translated polynomial maps precisely to the completion image of the original polynomial at the given point.

Discovery reused the already audited project `polynomialTranslation`, pinned mathlib `IsLocalization.ringEquivOfRingEquiv`, `Ideal.quotientEquiv`, maximal-ideal transport, and actual completion inverse limits. Official docs inspected: https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPowerSeries/Equiv.html and https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/AtPrime/Basic.html.

Still unproved: smooth-subvariety split coordinates, relative-equation/Jacobian comparison, remaining uniform geometric lifting and intersection inputs. The global Linearity Theorem is not proved. Full build and axiom audit must succeed before counting this checkpoint.
