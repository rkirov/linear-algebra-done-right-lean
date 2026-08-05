# Lean Companion to Axler's *Linear Algebra Done Right* (4e)

A Lean 4 companion to Sheldon Axler's [*Linear Algebra Done Right*](https://linear.axler.net/) (4th edition; freely available as a [PDF](https://linear.axler.net/LADR4e.pdf)).

## What is a companion?

A Lean project that mirrors a specific math textbook: a Lean translation of all
definitions, proofs, examples, and exercises (without solutions). It contains
**no narrative** — that stays in the original text — and is meant to be:

1. read concurrently with the text;
2. cloned and worked through, replacing each `sorry` with a real proof.

The canonical existing example is Tao's *Real Analysis I* companion
([blog post](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/),
[repo](https://github.com/teorth/analysis)). This project plays the same role
for Axler.

## Who is it for?

Lean familiarity is the prerequisite. Beyond that:

1. If you already know linear algebra, you're here to practice Lean and pick
   up the parts of mathlib that cover linear algebra.
2. If you don't, you learn the math alongside by reading the book.

**This companion will not teach you Lean.** Lean basics are out of scope —
if you're new to Lean, work through one of the standard introductions first:

- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) (chapters 1–7 are enough; later chapters go beyond what this companion needs)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Natural Number Game](https://adam.math.hhu.de/)

## Conventions

Authored under the conventions in
[companion-helper](https://github.com/rkirov/companion-helper):

- **Use mathlib directly.** Where Axler introduces a concept already in
  mathlib (`Field`, `Module`, `Submodule`, …), the companion uses the mathlib
  definition rather than redefining it. `recall` bridges Axler's axioms to
  mathlib's typeclass methods.
- **`@[avoiding …]`** from `companion-helper` marks exercises whose one-line
  mathlib solution would defeat the pedagogical point.
- No cross-imports between companions; mathlib is the only shared layer.

## On AI usage

AI generates the initial draft of each chapter from the freely available
PDF. Every draft is then reviewed and revised line-by-line by a human (with
AI assistance) — roughly 1–2 hours of focused review per subsection. More
on the human-vs-AI split as we accumulate playthroughs.

## Status

A row is *drafted* once the section's `.lean` file exists with all numbered
Axler results stated and proved and all exercises stated as `sorry`. It is
*reviewed* once a human has read it line-by-line and revised problems they
found. *Playtested* means someone (other than the author) has worked through
the section's exercises.

| Section | Drafted | Reviewed | Playtested |
|---|---|---|---|
| 1A. ℝⁿ and ℂⁿ | ✓ | ✓ | — |
| 1B. Definition of vector space | ✓ | ✓ | — |
| 1C. Subspaces | ✓ | ✓ | — |
| 2A. Span and Linear Independence | ✓ | ✓ | — |
| 2B. Bases | ✓ | ✓ | — |
| 2C. Dimension | ✓ | ✓ | — |
| 3A. Vector Space of Linear Maps | ✓ | ✓ | — |
| 3B. Null Spaces and Ranges | ✓ | ✓ | — |
| 3C. Matrices | ✓ | ✓ | — |
| 3D. Invertibility and Isomorphisms | ✓ | ✓ | — |
| 3E. Products and Quotients of Vector Spaces | ✓ | ✓ | — |
| 3F. Duality | ✓ | ✓ | — |
| 4. Polynomials | ✓ | ✓ | — |
| 5A. Invariant Subspaces | ✓ | ✓ | — |
| 5B. The Minimal Polynomial | ✓ | ✓ | — |
| 5C. Upper-Triangular Matrices | ✓ | ✓ | — |
| 5D. Diagonalizable Operators | ✓ | ✓ | — |
| 5E. Commuting Operators | ✓ | ✓ | — |
| 6A. Inner Products and Norms | ✓ | ✓ | — |
| 6B. Orthonormal Bases | ✓ | ✓ | — |
| 6C. Orthogonal Complements and Minimization Problems | ✓ | ✓ | — |
| 7A. Self-Adjoint and Normal Operators | ✓ | ✓ | — |
| 7B. Spectral Theorem | ✓ | — | — |
| 7C. Positive Operators | ✓ | — | — |
| 7D. Isometries, Unitary Operators, and Matrix Factorization | ✓* | — | — |
| 7E. Singular Value Decomposition | ✓* | — | — |
| 7F. Consequences of Singular Value Decomposition | ✓* | — | — |
| 8A. Generalized Eigenvectors and Nilpotent Operators | ✓* | — | — |
| 8B. Generalized Eigenspace Decomposition | ✓* | — | — |
| 8C. Consequences of Generalized Eigenspace Decomposition | ✓* | — | — |
| 8D. Trace | ✓ | — | — |
| 9A. Bilinear Forms and Quadratic Forms | ✓ | — | — |
| 9B. Alternating Multilinear Forms | ✓ | — | — |
| 9C. Determinants | ✓ | — | — |
| 9D. Tensor Products | ✓ | — | — |

The whole book (Chapters 1–9) is now drafted. A full top-to-bottom pass against
the text confirms that every numbered Axler item — Definition, Result, and
Example — is accounted for in the corresponding section file: stated and proved,
or, where it needs machinery genuinely absent from the pinned mathlib or relies on
Axler's own informal/analytic constructions, recorded with an explicit prose note.
Exercises remain as `sorry`. There are no silent `sorry`s on numbered results, and
no numbered item is omitted. **Every named Axler result (numbered theorem) is
proved in Lean** — none is left as a prose deferral. The concrete worked
*examples* are likewise formalized: the orthonormal-eigenbasis diagonalizations
7.30/7.33, the positive operator 7.35(a), the square root 7.37, the positive
square root 7.41, the annihilating polynomial 5.28, the generalized-eigenspace
decomposition 8.21, the traces 8.48/8.53, the product of bilinear forms and the
trace form 9.26, and — on the skippable `L²[a,b]` infrastructure — the Legendre
orthogonality 6.34 and the linear functional 6.41 are all real Lean computations.
The only prose-only items that remain are Axler's own informal *definitions* (e.g.
the intuitive box/volume definitions 7.108–7.110 and the matrix-of-a-basis
Jordan-form definition 8.44, both captured elsewhere in a formal, matrix-free way)
and two analytically heavy integral-inner-product worked *examples* — the Riesz
computation 6.44 and the sine-approximation 6.63 — which would need repeated
integration by parts and projection machinery on top of the same `sorry`-backed
`L²[a,b]` space.

\* A `✓*` marks a section that prose-defers one or more numbered results. These
deferrals cluster around a few missing pieces: the *matrix-of-a-basis normal-form
theory* — the strictly-upper-triangular normal form of a nilpotent operator
8.18(c) is now proved (8A) and, with it, the per-block content of the
block-diagonal form 8.37 and the diagonal-multiplicity count 8.31 are now
proved (8B); the existence of square roots of invertible complex operators 8.41
is now proved (8C, by gluing per-eigenspace roots along the generalized
eigenspace decomposition), and the Jordan-form theorems are now proved (8C: the
nilpotent Jordan basis 8.45 by Axler's induction on dimension, and the full Jordan
form over `ℂ` 8.46 by applying 8.45 to each `(T − λ)|_{G(λ,T)}` and gluing along
the generalized eigenspace decomposition) — both stated matrix-free via families
of eigenvalue chains that form a basis, so only the Definition 8.44's literal
`ℳ(T, basis)` phrasing stays in prose; *matrix factorizations* (the
QR factorization 7.58 is now fully proved via Gram–Schmidt, existence and
uniqueness; the Cholesky factorization 7.63 is now proved in 7D, existence and
uniqueness, built on QR; and in 7F the matrix SVD `A = B D C*` 7.80, the
operator-norm ↔ largest-singular-value bridge 7.88(a)/7.85, the
positive-singular-value count 7.68(b)(c), the pseudoinverse SVD 7.75, the
ellipsoid-image results 7.99/7.101, and the best rank-`k` approximation 7.92 are
now proved — in 7F only Axler's informal box/volume *definitions* below remain in
prose); Axler's informal box/volume *definitions* 7.108–7.110 (the headline
volume theorem 7.111, `volume T(Ω) = (s₁ ⋯ sₙ)·volume Ω`, is proved
measure-theoretically in 9C via the Haar change-of-variables and 9.60); and a
handful of purely numeric worked examples. Section 9D now carries no numbered-result deferral: the
`PiTensorProduct` dimension theory 9.87/9.89/9.90 is proved via
`Basis.piTensorProduct` (with 9.87 dual to 9.89 through `PiTensorProduct.lift`),
alongside the previously proved inner product on a binary tensor product
9.80–9.83. In 9C the
determinant/adjoint results 9.56(c), 9.58, 9.59, 9.60 and Hadamard's inequality
9.66 are now proved (9.60 in both its `‖det T‖ = √det(T*T)` and
product-of-singular-values `|det T| = s₁ ⋯ sₙ` forms) — 9C carries no remaining
numbered-result deferral. The Chapters 1–7C sections carry no `✓*` — every
numbered result there is fully proved.

## Building

```bash
lake update mathlib && lake exe cache get   # first time only
lake build
```
Toolchain: `leanprover/lean4:v4.30.0-rc2`. Mathlib is pinned at `v4.30.0-rc2`.

## Contributing

PRs fixing typos or improving comments are welcome. Please **don't** send PRs
to `main` filling in the `sorry`s — they're the exercises. Solutions in your
own fork (or a separate branch here) are fine; they just shouldn't land on
`main`.

## License

Apache-2.0.
