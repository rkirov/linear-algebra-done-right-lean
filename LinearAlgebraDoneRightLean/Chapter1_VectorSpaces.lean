import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Chapter 1: Vector Spaces

This chapter introduces the fundamental concepts of linear algebra:
- Complex numbers and Fⁿ (Section 1A)
- Definition of vector space (Section 1B)  
- Subspaces (Section 1C)

We follow Axler's presentation closely. Exercises are left as `sorry` for the reader.

Reference: Axler, *Linear Algebra Done Right*, 4th edition
https://linear.axler.net/LADR4e.pdf
-/

namespace LADR

/-!
## Section 1A: ℝⁿ and ℂⁿ

Axler begins with complex numbers and the notation Fⁿ for n-tuples over a field F.
-/

section Section1A

/-
1.1 Definition: Complex Numbers

Mathlib provides `Complex` (notation: ℂ). Key properties:
- z = a + bi where a, b ∈ ℝ
- i² = -1
-/

-- Verify basic properties (Axler 1.2-1.3)
example : Complex.I ^ 2 = -1 := Complex.I_sq
example (a b : ℂ) : a + b = b + a := add_comm a b
example (a b : ℂ) : a * b = b * a := mul_comm a b

/-
1.5 Notation: F

Throughout, F denotes ℝ or ℂ. We generalize to any field when possible.
-/

/-
1.8 Definition: list, length

Fⁿ is the set of n-tuples (x₁, ..., xₙ) with xᵢ ∈ F.
In Lean: `Fin n → F` (functions from {0, ..., n-1} to F).
-/

abbrev Vec (F : Type*) (n : ℕ) := Fin n → F

-- Example: vectors in ℝ³ and ℂ²
example : Vec ℝ 3 := ![1, 2, 3]
example : Vec ℂ 2 := ![1, Complex.I]

/-
1.10 Definition: addition in Fⁿ
Componentwise: (x + y)ᵢ = xᵢ + yᵢ
-/

example (x y : Vec ℝ 3) : x + y = fun i => x i + y i := rfl

/-
1.11 Commutativity of addition in Fⁿ
-/

theorem Vec.add_comm' {F : Type*} [AddCommMonoid F] {n : ℕ} (x y : Vec F n) : 
    x + y = y + x := by
  ext i
  exact add_comm (x i) (y i)

/-
1.12 Definition: 0 (the zero vector)
-/

example : (0 : Vec ℝ 3) = ![0, 0, 0] := by ext i; fin_cases i <;> rfl

/-
1.14 Definition: scalar multiplication in Fⁿ
Componentwise: (c • x)ᵢ = c * xᵢ
-/

example (c : ℝ) (x : Vec ℝ 3) : c • x = fun i => c * x i := rfl

end Section1A

/-!
## Section 1B: Definition of Vector Space

The central definition of this chapter.
-/

section Section1B

/-
1.19-1.20 Definition: vector space

A vector space over F is a set V with addition and scalar multiplication
satisfying eight axioms. Mathlib calls this a `Module` over F.

We state Axler's axioms explicitly, then note that `Module F V` captures them.
-/

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

-- Axler's 8 axioms are satisfied by Module:

-- (1) Commutativity: u + v = v + u
example (u v : V) : u + v = v + u := add_comm u v

-- (2) Associativity: (u + v) + w = u + (v + w)  
example (u v w : V) : (u + v) + w = u + (v + w) := add_assoc u v w

-- (3) Additive identity: v + 0 = v
example (v : V) : v + 0 = v := add_zero v

-- (4) Additive inverse: v + (-v) = 0
example (v : V) : v + (-v) = 0 := add_neg_cancel v

-- (5) Multiplicative identity: 1 • v = v
example (v : V) : (1 : F) • v = v := one_smul F v

-- (6) Distributivity (scalar over vector addition): a • (u + v) = a • u + a • v
example (a : F) (u v : V) : a • (u + v) = a • u + a • v := smul_add a u v

-- (7) Distributivity (field addition over scalar mult): (a + b) • v = a • v + b • v
example (a b : F) (v : V) : (a + b) • v = a • v + b • v := add_smul a b v

-- (8) Associativity of scalar multiplication: (ab) • v = a • (b • v)
example (a b : F) (v : V) : (a * b) • v = a • (b • v) := mul_smul a b v

/-
1.21 Example: Fⁿ is a vector space

This is automatic in Mathlib: `Fin n → F` has a Module instance.
-/

example : Module ℝ (Vec ℝ 3) := inferInstance

/-
1.22 Example: F^∞ (infinite sequences)
-/

example : Module ℝ (ℕ → ℝ) := inferInstance

/-
1.25 Unique additive identity
-/

theorem unique_zero (z : V) (hz : ∀ v, v + z = v) : z = 0 := by
  have := hz 0
  rwa [zero_add] at this

/-
1.26 Unique additive inverse  
-/

theorem unique_neg (v w : V) (hw : v + w = 0) : w = -v := by
  have h : -w = v := neg_eq_of_add_eq_zero_left hw
  rw [← h, neg_neg]

/-
1.29 Zero scalar times any vector
-/

example (v : V) : (0 : F) • v = 0 := zero_smul F v

/-
1.30 Any scalar times zero vector
-/

example (a : F) : a • (0 : V) = 0 := smul_zero a

/-
1.31 (-1) • v = -v
-/

example (v : V) : (-1 : F) • v = -v := neg_one_smul F v

end Section1B

/-!
## Section 1C: Subspaces
-/

section Section1C

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-
1.33-1.34 Definition: subspace

A subset U ⊆ V is a subspace if:
(a) 0 ∈ U
(b) u, v ∈ U ⟹ u + v ∈ U  
(c) a ∈ F, u ∈ U ⟹ a • u ∈ U

Mathlib: `Submodule F V`
-/

-- Example: the trivial subspace {0}
example : Submodule F V := ⊥

-- Example: the whole space V
example : Submodule F V := ⊤

/-
1.35 Example: Subspaces of ℝ²

The subspaces of ℝ² are exactly: {0}, ℝ², and lines through the origin.
-/

-- A line through origin in ℝ²: {t • v | t ∈ ℝ} for some nonzero v
def lineThrough (v : Vec ℝ 2) : Submodule ℝ (Vec ℝ 2) := Submodule.span ℝ {v}

-- Exercise 1.C.6: Verify this is a subspace of ℝ³
example : Submodule ℝ (Vec ℝ 3) where
  carrier := {v | v 0 + 2 * v 1 + 3 * v 2 = 0}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    linarith
  zero_mem' := by simp
  smul_mem' := by
    intro a v hv
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    calc a * v 0 + 2 * (a * v 1) + 3 * (a * v 2) 
        = a * (v 0 + 2 * v 1 + 3 * v 2) := by ring
      _ = a * 0 := by rw [hv]
      _ = 0 := by ring

/-
1.36 Definition: Sum of subspaces

U₁ + U₂ = {u₁ + u₂ | u₁ ∈ U₁, u₂ ∈ U₂}
-/

-- Mathlib uses the `⊔` (sup) notation for subspace sum
example (U W : Submodule F V) : Submodule F V := U ⊔ W

/-
1.39 Definition: Direct sum

U + W is direct if every element has a unique representation u + w.
Notation: U ⊕ W (internal direct sum)

In Mathlib: `IsCompl U W` or `U ⊓ W = ⊥`
-/

/-
1.41 Condition for direct sum

U + W is direct ⟺ U ∩ W = {0}
-/

theorem direct_sum_iff_inter_trivial (U W : Submodule F V) :
    U ⊓ W = ⊥ ↔ ∀ v, v ∈ U → v ∈ W → v = 0 := by
  rw [Submodule.eq_bot_iff]
  constructor
  · intro h v hu hw
    exact h v ⟨hu, hw⟩
  · intro h v ⟨hu, hw⟩
    exact h v hu hw

end Section1C

/-!
## Exercises

Selected exercises from Chapter 1. Proofs are left as `sorry`.
-/

section Exercises

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

-- Exercise 1.B.1: Prove -(-v) = v
theorem exercise_1B1 (v : V) : -(-v) = v := by
  sorry

-- Exercise 1.B.2: If a • v = 0, then a = 0 or v = 0
theorem exercise_1B2 (a : F) (v : V) (h : a • v = 0) : a = 0 ∨ v = 0 := by
  sorry

-- Exercise 1.B.3: Prove 2v = v + v (where 2 = 1 + 1)
theorem exercise_1B3 (v : V) : (2 : F) • v = v + v := by
  sorry

-- Exercise 1.C.1: Show {(x₁,x₂,x₃) ∈ F³ | x₁ + 2x₂ + 3x₃ = 0} is a subspace
-- (Done above as example)

-- Exercise 1.C.2: Show {(x₁,x₂,x₃) ∈ F³ | x₁ + 2x₂ + 3x₃ = 4} is NOT a subspace
theorem exercise_1C2_not_subspace : 
    ¬∃ (S : Submodule ℝ (Vec ℝ 3)), (S : Set (Vec ℝ 3)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 4} := by
  sorry

-- Exercise 1.C.3: Show the intersection of subspaces is a subspace
-- (This is automatic in Mathlib: U ⊓ W)
example (U W : Submodule F V) : Submodule F V := U ⊓ W

-- Exercise 1.C.4: Is union of subspaces a subspace?
-- Answer: Only if one contains the other
theorem exercise_1C4 (U W : Submodule F V) :
    (∃ S : Submodule F V, (S : Set V) = (U : Set V) ∪ (W : Set V)) ↔ U ≤ W ∨ W ≤ U := by
  sorry

end Exercises

end LADR
