# Chapters 3 and 4: authoring and reference audit

Textbook: 韩士安、林磊、杜荣《近世代数》第三版, the supplied 277-page PDF.
Source SHA-256: `aee38591bb521ac7b6dce93fdb40de7221c8df74c05c72ba4dbac9087de22259`.
For these chapters, PDF page number = printed page number + 12.

| Section | Printed reading pages | Cards | Numbered definitions | Numbered theorems |
|---|---|---:|---|---|
| 3.1 | 124–132 | 8 | 3.1.1–2 | 3.1.1–3 |
| 3.2 | 135–143 | 7 | 3.2.1–5 | 3.2.1 |
| 3.3 | 146–152 | 7 | 3.3.1–3 | 3.3.1–4 |
| 3.4 | 154–161 | 8 | 3.4.1–2 | 3.4.1–5 |
| 3.5 | 165–168 | 6 | 3.5.1–2 | 3.5.1–3 |
| 3.6 | 170–173 | 6 | 3.6.1–2 | 3.6.1–5 |
| 4.1 | 175–179 | 6 | 4.1.1–3 | 4.1.1–3 |
| 4.2 | 180–186 | 6 | 4.2.1 | 4.2.1–2 |
| 4.3 | 187–197 | 10 | 4.3.1–10 | 4.3.1–9 |
| 4.4 | 200–207 | 11 | 4.4.1–2 | 4.4.1–6 |
| 4.5 | 210–214 | 9 | 4.5.1 | 4.5.1–6 |

There are also five original exercises per section: four multiple-choice
questions with explanations and one written proof with a reference solution.
The exercises have no invented textbook exercise numbers.

Conventions retained from this edition:

- A ring need not be commutative or unital. A subring need not share an identity.
- A ring homomorphism need not preserve identity. Conditions ensuring it does
  are presented in Theorem 3.4.2.
- Zero is excluded from zero-divisors. An integral domain has 1≠0 and commutes.
- Prime and maximal ideals are treated in commutative rings; quotient
  domain/field criteria explicitly require identity.
- The degree of the zero polynomial is undefined. It is not displayed as 0.
- Factorizations and gcds are unique only up to units/associates.
- UFD does not imply Bézout or PID. The ideal (2,x) in ℤ[x] separates them.
- The finite-grid norm demonstration has a complete elementary bound; the
  Gaussian checkerboard is an illustrative finite window of an infinite ideal.
- A root test is used only for degrees two and three. A reducible reduction
  modulo p does not establish reducibility over ℚ.

The 3.1 motivation, finite-domain result, fraction-field universal property,
content notation, and reduction-mod-p criterion are explicitly marked as
supplementary exposition. Their page references indicate related textbook
material, not an invented numbered theorem. The field material remains basic:
no extension degrees or Galois theory are added.

Theorem 4.4.6 includes both the textbook's reversed-quotient recurrence and an
equivalent forward extended-Euclidean recurrence. The proof explains the
relationship and treats an immediately zero remainder separately.
Theorem 4.5.1 is proved by factoring content and primitive parts and comparing
the two unique factorizations; this is an original organization of the proof.

Each authoring entry stores its exact source label and one-based PDF pages.
The generated JSON carries only that section. Ring models use bounded integer
arithmetic; polynomial division demos operate over explicitly selected finite
prime fields. No external rendering service or content CDN is required.
