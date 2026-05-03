import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 1A: ℝⁿ and ℂⁿ
-/

namespace LADR.Section_1A

open Complex

/-! 1.1 Definition: complex numbers -/
variable {a b c d : ℝ}
example : ℂ := ⟨a, b⟩
example : ⟨a, b⟩ + ⟨c, d⟩ = (⟨a + c, b + d⟩ : ℂ) := rfl
example : ⟨a, b⟩ * ⟨c, d⟩ = (⟨a * c - b * d, a * d + b * c⟩ : ℂ) := rfl

example : I = ⟨0,1⟩ := rfl
example : I ^ 2 = -1 := I_sq
example : a + b * I = ⟨a, b⟩ := re_add_im ⟨a, b⟩

/-! 1.2 Example: complex arithmetic -/
example : (2 + 3*I) * (4 + 5*I) = -7 + 22*I := by
  calc (2 + 3*I) * (4 + 5*I)
      = 2 * (4 + 5*I) + 3*I * (4 + 5*I)       := by rw [add_mul]
    _ = 2*4 + 2*(5*I) + (3*I)*4 + (3*I)*(5*I) := by rw [mul_add, mul_add, ←add_assoc]
    _ = 8 + 10*I + 12*I + 15*I^2              := by ring
    _ = 8 + 10*I + 12*I + 15*(-1)             := by rw [I_sq]
    _ = -7 + 22*I                             := by ring

/-! 1.3 Properties of complex arithmetic -/

@[avoiding add_comm]
theorem exercise_1A_1 (α β : ℂ) : α + β = β + α := by sorry

/-! 1.4 Example: commutativity of complex multiplication -/

@[avoiding mul_comm]
theorem mul_comm_example (α β : ℂ) : α * β = β * α := by
  rw [← re_add_im α, ← re_add_im β]
  apply Complex.ext
  · ring_nf
  · ring_nf

@[avoiding add_assoc]
theorem exercise_1A_2 (α β γ : ℂ) : (α + β) + γ = α + (β + γ) := by sorry

@[avoiding mul_assoc]
theorem exercise_1A_3 (α β γ : ℂ) : (α * β) * γ = α * (β * γ) := by sorry

@[avoiding mul_add, left_distrib]
theorem exercise_1A_4 (α β γ : ℂ) : γ * (α + β) = γ * α + γ * β := by sorry

example (γ : ℂ) : γ + 0 = γ := add_zero γ
example (γ : ℂ) : γ * 1 = γ := mul_one γ

@[avoiding neg_eq_of_add_eq_zero_left, neg_eq_of_add_eq_zero_right,
    eq_neg_of_add_eq_zero_left, eq_neg_of_add_eq_zero_right]
theorem exercise_1A_5 (α : ℂ) : ∃! β : ℂ, α + β = 0 := by sorry

@[avoiding inv_eq_of_mul_eq_one_left, inv_eq_of_mul_eq_one_right,
    eq_inv_of_mul_eq_one_left, eq_inv_of_mul_eq_one_right]
theorem exercise_1A_6 (α : ℂ) (hα : α ≠ 0) : ∃! β : ℂ, α * β = 1 := by sorry

/-! 1.5 Definition: −α, subtraction, 1/α, division -/

example (α β : ℂ) : α - β = α + (-β) := sub_eq_add_neg α β
example (α : ℂ) : α⁻¹ = 1 / α := (one_div α).symm
example (α β : ℂ) : β / α = β * α⁻¹ := div_eq_mul_inv β α

/-! 1.6 Notation: F -/

variable {F : Type*} [Field F] {n : ℕ}

example (α : F) (m n : ℕ) : (α ^ m) ^ n = α ^ (m * n) := (pow_mul α m n).symm
example (α β : F) (m : ℕ) : (α * β) ^ m = α ^ m * β ^ m := mul_pow α β m

/-! 1.7 Example: ℝ² and ℝ³ -/

example : Fin 2 → ℝ := ![1, 2]
example : Fin 3 → ℝ := ![1, 2, 3]

/-! 1.8 Definition: list, length

Axler's *list of length `n` over `α`* is rendered here as `Fin n → α`, with
the length encoded in the type. **Beware:** Lean has a separate built-in type
`List α` (a variable-length linked list, written with the `[…]` notation
instead of `![…]`) — it is *not* what Axler calls a list. -/

example : Fin 0 → ℝ := ![]

example {α : Type*} (x y : Fin n → α) : x = y ↔ ∀ i, x i = y i :=
  ⟨fun h _ => h ▸ rfl, funext⟩

/-! 1.9 Lists versus sets -/

example : (![3, 5] : Fin 2 → ℕ) ≠ ![5, 3] := by decide
example : ({3, 5} : Set ℕ) = ({5, 3} : Set ℕ) := by ext; simp; tauto
example : ({4, 4} : Set ℕ) = ({4} : Set ℕ) := by ext; simp

/-! 1.11 Definition: Fⁿ, coordinate -/

example : (![10, 20, 30] : Fin 3 → ℕ) 0 = 10 := rfl
example : (![10, 20, 30] : Fin 3 → ℕ) 2 = 30 := rfl

/-! 1.12 Example: ℂ⁴ -/

example : Fin 4 → ℂ := ![1 + 2 * I, 3, -I, 5 - 6 * I]

/-! 1.13 Definition: addition in Fⁿ -/

example (x y : Fin n → F) : x + y = fun i => x i + y i := rfl

/-! 1.14 Commutativity of addition in Fⁿ -/

theorem add_comm_pi (x y : Fin n → F) : x + y = y + x := by
  funext i
  exact add_comm (x i) (y i)

/-! 1.15 Notation: 0 -/

example : (0 : Fin n → F) = fun _ => 0 := rfl

/-! 1.16 Example: context determines which 0 is intended -/

example (x : Fin n → F) : x + 0 = x := add_zero x

/-! 1.17 Definition: additive inverse in Fⁿ, −x -/

example (x : Fin n → F) : -x = fun i => -(x i) := rfl

/-! 1.18 Definition: scalar multiplication in Fⁿ -/

example (a : F) (x : Fin n → F) : a • x = fun i => a * x i := rfl

/-! # Exercises

Exercises 1A.1–1A.6 are stated inline in Properties 1.3 above. -/

theorem exercise_1A_7 :
    ((-1 + Real.sqrt 3 * I) / 2) ^ 3 = 1 := by
  sorry

theorem exercise_1A_8 :
    ∃ z w : ℂ, z ≠ w ∧ z ^ 2 = I ∧ w ^ 2 = I := by
  sorry

theorem exercise_1A_9 :
    ∃ x : Fin 4 → ℝ,
      (![4, -3, 1, 7] : Fin 4 → ℝ) + (2 : ℝ) • x = ![5, 9, -6, 8] := by
  sorry

theorem exercise_1A_10 :
    ¬ ∃ lam : ℂ, lam • (![2 - 3 * I, 5 + 4 * I, -6 + 7 * I] : Fin 3 → ℂ) =
      ![12 - 5 * I, 7 + 22 * I, -32 - 9 * I] := by
  sorry

@[avoiding add_assoc]
theorem exercise_1A_11 (x y z : Fin n → F) :
    (x + y) + z = x + (y + z) := by
  sorry

@[avoiding mul_smul, smul_smul]
theorem exercise_1A_12 (a b : F) (x : Fin n → F) :
    (a * b) • x = a • (b • x) := by
  sorry

@[avoiding one_smul]
theorem exercise_1A_13 (x : Fin n → F) : (1 : F) • x = x := by
  sorry

@[avoiding smul_add]
theorem exercise_1A_14 (γ : F) (x y : Fin n → F) :
    γ • (x + y) = γ • x + γ • y := by
  sorry

@[avoiding add_smul]
theorem exercise_1A_15 (a b : F) (x : Fin n → F) :
    (a + b) • x = a • x + b • x := by
  sorry

end LADR.Section_1A
