# Autoformalization review patterns

Recurring issues found while reviewing the autoformalization section-by-section,
with a detector (how to find them) and the standard fix. When asked to
"apply review patterns to Section X", run each detector over that section's file,
fix the hits, then rebuild the section.

Derived from the review-pass commits: 0777fe5 (5D), cf54f39 (5E),
96b53e3 (6A), 53dbf0a (6B). Correct / extend this list as new patterns show up.

---

## P1 — Examples left as prose instead of formalized

- **Symptom:** a `/-! X.Y Example (not formalized ...) -/` comment where the book
  gives a concrete operator/computation that *can* be stated in Lean.
- **Detect:** `rg -n "not formalized" LinearAlgebraDoneRightLean/`
- **Why:** the book's worked examples are the point; leaving them as prose skips
  the formalization work and hides whether mathlib can express them.
- **Fix:** replace the prose with a concrete `def`/`theorem` (e.g. `T_5_57`,
  eigenvalue theorems, the `Tⁿ` closed form). Keep the book's numbering in the
  docstring. If a genuine mathlib gap blocks it, say so explicitly rather than
  silently omitting.
- **Example:** 5.57/5.59/5.60/5.61 in 0777fe5; 6.44 Riesz computation in 53dbf0a.

## P2 — Statement over-specialized below the book's generality

- **Symptom:** matrix size pinned to `Fin 2`/`Fin 3`, or the vector space pinned to
  a concrete `(Fin n → 𝔽)`, or the field pinned to ℝ/ℂ, when the book states the
  result generally or "for some vector space".
- **Detect:** `rg -n "Fin 2|Fin 3" LinearAlgebraDoneRightLean/Section_X.lean` in
  *exercise/theorem statements* (not in concrete worked examples, where a fixed
  size is correct); read against the book to see if it's meant to be general.
- **Why:** narrows the theorem below what the book claims.
- **Fix:** quantify — `{n : ℕ}` over matrix size; `∃ (V : Type) (_ : AddCommGroup V)
  (_ : Module 𝔽 V) (_ : Module.Finite 𝔽 V), …` when the book leaves the space free;
  generalize the field where the proof allows.
- **Example:** 5E.4 (matrix size); 5D.14a/5D.19 (quantify the space) in 0777fe5.

## P3 — Ad-hoc statement instead of the mathlib idiom

- **Symptom:** a hand-rolled statement where mathlib has the canonical predicate.
- **Detect:**
  - commuting operators written `S ∘ₗ T = T ∘ₗ S` → `Commute S T`
  - eigenvector written `T v = μ • v` (with `v ≠ 0`) → `HasEigenvector T μ v`
  - upper-triangular via a flag/span condition → `IsUpperTriangular (matrixOf …)`
  - `rg -n "∘ₗ.*=.*∘ₗ|• v" LinearAlgebraDoneRightLean/Section_X.lean`
- **Why:** matches the rest of mathlib, lets downstream lemmas (`Commute.*`,
  `HasEigenvector.*`, `tfae_upperTriangular`) apply directly.
- **Fix:** restate with the mathlib predicate; convert at the boundary if a
  consumer still needs the old form.
- **Example:** Schur → `IsUpperTriangular` in 53dbf0a (7B converts back via
  `tfae_upperTriangular`); Commute/HasEigenvector refactor in cf54f39.

## P4 — Exercise statement doesn't match the book

- **Symptom:** the Lean statement asserts the wrong thing (e.g. states a form *is*
  an inner product when the exercise is to show it *isn't*, or asserts the wrong
  set of axioms).
- **Detect:** not greppable — read each exercise statement against the PDF
  (`LADR4e.pdf`) before trusting it.
- **Fix:** correct the statement to the book's actual claim.
- **Example:** 6A.3 (not-an-inner-product), 6A.29 (product-form axioms) in 96b53e3;
  5D.16 restated as the book's existential direct-sum form in 0777fe5.

## P5 — Missing exercises or examples

- **Symptom:** the exercise ore example set for a section is incomplete.
- **Detect:** list the exercise numbers present vs. the book's range for the
  section; note gaps. Every number from X.Y should be present in a comment.
- **Fix:** add the missing exercises (stubbed with `sorry` is fine if not proving
  them now), keeping book numbering.
- **Example:** 6A.12b/6A.14/6A.18/6A.25/6A.27–35 added in 96b53e3; full 6B.1–23
  present in 53dbf0a.

## P6 — "Find …" answer exercises collapsed into one theorem

- **Symptom:** an exercise whose book prompt is "Find / Determine / Give an example
  of …" is squashed into a single theorem, entangling the answer with its proof
  obligation.
- **Detect:** exercises phrased as "Find"/"Determine" in the book; check whether the
  Lean form separates the answer from the claim.
- **Fix:** split into an answer `def` (value, may be `sorry`) + a `theorem` stating
  the property that answer satisfies.
- **Example:** 5D.21b/c split into answer-def + property-theorem in 0777fe5.

## P7 — Repeated inline predicate should be extracted

- **Symptom:** the same predicate body (e.g. "is a real inner product",
  "is an inner-product form") written inline across several statements.
- **Detect:** duplicated `fun`/`↔` predicate bodies across exercises in a section.
- **Fix:** extract a named predicate (`IsRealInnerProduct`, `IsInnerProductForm`)
  and reuse it.
- **Example:** predicates extracted in 96b53e3.

## P8 — Naming convention for free scalar/eigenvalue variables

- **Symptom:** a *bound/free* eigenvalue or scalar variable named `lam`.
- **Detect:** `rg -n "\blam\b" LinearAlgebraDoneRightLean/Section_X.lean`
- **Fix:** use `γ` (not \lambda as it is reserved in lean) for the free eigenvalue variable, for
  consistency with the reviewed sections.
- **Example:** `lam → γ` throughout 5D exercises in 0777fe5.

## P9 — Numbered result weakened to its "key step"

- **Symptom:** a numbered theorem from the book is formalized only as the
  intermediate lemma its proof goes through, with the book's actual conclusion
  left in prose. Tell-tale docstring phrasing: "we record the key step", "the
  main ingredient", "which gives …".
- **Detect:** `rg -n "key step|main ingredient|the essential point"
  LinearAlgebraDoneRightLean/`; then check each numbered `/-! X.Y … -/` block
  against the PDF and confirm some declaration actually states X.Y's conclusion.
- **Why:** the section then doesn't contain the result it claims to; downstream
  sections can't cite it, and the gap is invisible to the README progress table.
- **Fix:** keep the intermediate lemma (it is usually reusable) and add the
  book's conclusion as its own theorem, deriving it from the lemma. Rewrite the
  docstring to name both.
- **Example:** 7.26 stated only as `quadratic_pos` (positivity of
  `⟨(T² + bT + cI)v, v⟩`); the book's claim — `T² + bT + cI` is invertible —
  added as `quadratic_isInvertible`.

## P10 — Proof-internal coercion leaking into a statement

- **Symptom:** a hypothesis or conclusion carries a type-synonym lift that only the
  *proof* needs — most often columns of a matrix pushed through
  `(EuclideanSpace.equiv n 𝕜).symm` so Gram–Schmidt applies, in a statement whose
  claim (linear independence, triangularity) is purely algebraic.
- **Detect:** `rg -n "EuclideanSpace.equiv|WithLp.toLp|PiLp" LinearAlgebraDoneRightLean/Section_X.lean`,
  then ask of each hit in a *statement*: does the claim use the ℓ² norm or inner
  product? If not, the lift belongs inside the proof.
- **Why:** a reader must check the round-trip changes nothing, and callers must
  manufacture the lift; `LinearIndependent 𝕜 A.col` is directly mathlib's idiom
  (`Matrix.linearIndependent_cols_iff_isUnit`) while the lifted form is not.
- **Fix:** state the plain form and transfer inside the proof along
  `WithLp.linearEquiv` (`LinearIndependent.map'` in both directions). Prefer
  `A.col`/`A.row` over `Aᵀ i`/eta-expanded lambdas, and `WithLp.toLp 2` over
  `(EuclideanSpace.equiv …).symm` where a lift genuinely is needed (e.g. a norm).
- **Example:** `QR_factorization`, `cholesky_factorization`, 7D.20 and 9.66/9C.19
  restated on `A.col`; the ℓ² lift kept only where Hadamard's inequality measures
  `‖·‖`.
