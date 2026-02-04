# Lean Companion to Axler's Linear Algebra Done Right

A Lean 4 formalization companion to Sheldon Axler's [*Linear Algebra Done Right*](https://linear.axler.net/) (4th edition). The book is freely available as a PDF.

## Philosophy

Following the style of [Terry Tao's Analysis I companion](https://github.com/teorth/analysis):

- **Faithful to the text:** Definitions and theorems mirror the book's presentation
- **Exercises as `sorry`s:** Reader exercises are stated as theorems — fork and fill them in!
- **Mathlib-based:** Uses Mathlib definitions (Module, Submodule, etc.) rather than custom ones
- **Readable over optimal:** Prioritizes clarity and learning over proof golf

## Progress

- [x] Chapter 1: Vector Spaces (definitions, basic properties, exercises)
- [ ] Chapter 2: Finite-Dimensional Vector Spaces
- [ ] Chapter 3: Linear Maps
- [ ] Chapter 4: Polynomials
- [ ] Chapter 5: Eigenvalues and Eigenvectors
- [ ] Chapter 6: Inner Product Spaces
- [ ] Chapter 7: Operators on Inner Product Spaces
- [ ] Chapter 8: Operators on Complex Vector Spaces
- [ ] Chapter 9: Operators on Real Vector Spaces
- [ ] Chapter 10: Trace and Determinant

## Structure

```
LinearAlgebraDoneRightLean/
├── Basic.lean                    -- Common imports
├── Chapter1_VectorSpaces.lean    -- Sections 1A-1C
├── Chapter2_FiniteDim.lean       -- (coming)
...
```

## Building

Requires [Lean 4](https://lean-lang.org/lean4/doc/setup.html) and [elan](https://github.com/leanprover/elan).

```bash
lake exe cache get   # Download prebuilt Mathlib
lake build
```

## Contributing

PRs welcome! Especially:
- Filling in `sorry` proofs
- Adding more exercises
- Improving documentation
- Alternative proof strategies

## Resources

- [Linear Algebra Done Right (free PDF)](https://linear.axler.net/LADR4e.pdf)
- [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)

## License

MIT
