import Mathlib.Algebra.Module.Pi
import Mathlib.Analysis.Complex.Basic
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
example : a + b * I = ⟨a, b⟩ := re_add_im ⟨a, b⟩

example : ⟨a, b⟩ + ⟨c, d⟩ = (⟨a + c, b + d⟩ : ℂ) := rfl
example : ⟨a, b⟩ * ⟨c, d⟩ = (⟨a * c - b * d, a * d + b * c⟩ : ℂ) := rfl

example : I = ⟨0,1⟩ := rfl
example : I ^ 2 = -1 := I_sq

/-! 1.2 Example: complex arithmetic -/
example : (2 + 3*I) * (4 + 5*I) = -7 + 22*I := by
  calc (2 + 3*I) * (4 + 5*I)
      = 2 * (4 + 5*I) + 3*I * (4 + 5*I)       := by rw [add_mul]
    _ = 2*4 + 2*(5*I) + (3*I)*4 + (3*I)*(5*I) := by rw [mul_add, mul_add, ←add_assoc]
    _ = 8 + 10*I + 12*I + 15*I^2              := by ring
    _ = 8 + 10*I + 12*I + 15*(-1)             := by rw [I_sq]
    _ = -7 + 22*I                             := by ring

/-! 1.3 Properties of complex arithmetic -/
variable {α β γ : ℂ}
-- Commutativity
example : α + β = β + α                     := add_comm α β
example : α * β = β * α                     := mul_comm α β
-- Associativity
example : (α + β) + γ = α + (β + γ)         := add_assoc α β γ
example : (α * β) * γ = α * (β * γ)         := mul_assoc α β γ
-- Identities
example : γ + 0 = γ                         := add_zero γ
example : γ * 1 = γ                         := mul_one γ
-- Inverses
example : ∃! β : ℂ, α + β = 0               := ⟨-α, add_neg_cancel α,
                                                fun _ => eq_neg_of_add_eq_zero_right⟩
example (hα : α ≠ 0) : ∃! β : ℂ, α * β = 1  := ⟨α⁻¹, mul_inv_cancel₀ hα,
                                                fun _ => eq_inv_of_mul_eq_one_right⟩
-- Distrbutive Property
example : γ * (α + β) = γ * α + γ * β       := mul_add γ α β

/-! 1.4 Example: commutativity of complex multiplication -/
attribute [-instance] Complex.commRing in
attribute [-instance] Complex.instCommSemiring in
attribute [-instance] Complex.instField in
example (α β : ℂ) : α * β = β * α := by
  obtain ⟨a, b⟩ := α; obtain ⟨c, d⟩ := β
  calc (⟨a, b⟩ : ℂ) * ⟨c, d⟩
      = ⟨a*c - b*d, a*d + b*c⟩ := rfl
    _ = ⟨c*a - d*b, c*b + d*a⟩ := by
      rw [mul_comm, mul_comm b d, mul_comm a d, mul_comm c b, add_comm]
    _ = ⟨c, d⟩ * ⟨a, b⟩        := rfl

/-! 1.5 Definition: −α, subtraction, 1/α, division -/
variable {α β : ℂ}
example : α + -α = 0               := add_neg_cancel α
example : α - β = α + (-β)         := sub_eq_add_neg α β
example : 1 / α = α⁻¹              := one_div α
example (hα : α ≠ 0) : α * α⁻¹ = 1 := mul_inv_cancel₀ hα
example : β / α = β * α⁻¹          := div_eq_mul_inv β α

/-! 1.6 Notation: F -/
variable {F : Type*} [Field F]
example (a : F) (m : ℕ) : a ^ m = (List.replicate m a).prod := (List.prod_replicate m a).symm
example (α : F) (m n : ℕ) : (α ^ m) ^ n = α ^ (m * n) := (pow_mul α m n).symm
example (α β : F) (m : ℕ) : (α * β) ^ m = (α ^ m) * (β ^ m) := mul_pow α β m

/-! 1.7 Example: ℝ² and ℝ³ -/
example (x y : ℝ)   : Fin 2 → ℝ := ![x, y]
example (x y z : ℝ) : Fin 3 → ℝ := ![x, y, z]

/-! 1.8 Definition: list, length -/
example : Fin 0 → F := ![]
example {α : Type*} {n : ℕ} (x y : Fin n → α) : x = y ↔ ∀ i, x i = y i := ⟨fun h _ => h ▸ rfl, funext⟩

/-! 1.9 Lists versus sets -/
example : ![3, 5] ≠ ![5, 3] := by decide
example : ({3, 5} : Set ℕ) = ({5, 3} : Set ℕ) := by ext; simp; tauto
-- `(4, 4) ≠ (4)` is type-enforced: `![4, 4] : Fin 2 → ℕ`, `![4] : Fin 1 → ℕ`.
example : ({4, 4} : Set ℕ) = ({4} : Set ℕ) := by ext; simp

/-! 1.10 Notation: n -/
variable {n : ℕ}

/-! 1.11 Definition: F^n, coordinate -/
example (x : Fin n → F) (k : Fin n) : F := x k

/-! 1.12 Example: ℂ⁴ -/
example (z₁ z₂ z₃ z₄ : ℂ) : Fin 4 → ℂ := ![z₁, z₂, z₃, z₄]

/-! 1.13 Definition: addition in Fⁿ -/
example (x y : Fin n → F) : x + y = fun i ↦ x i + y i := rfl

/-! 1.14 Commutativity of addition in Fⁿ -/
theorem add_comm_pi (x y : Fin n → F) : x + y = y + x :=
  calc x + y
      = fun i => x i + y i := rfl
    _ = fun i => y i + x i := funext fun _ ↦ add_comm _ _
    _ = y + x              := rfl

/-! 1.15 Notation: 0 -/
example : (0 : Fin n → F) = fun _ => 0 := rfl

/-! 1.16 Example: context determines which 0 is intended -/
example (x : Fin n → F) : x + 0 = x := add_zero x

/-! 1.17 Definition: additive inverse in Fⁿ, −x -/
example (x : Fin n → F) : -x = fun i => -(x i) := rfl

/-! 1.18 Definition: scalar multiplication in Fⁿ -/
example (a : F) (x : Fin n → F) : a • x = fun i => a * x i := rfl

/-! # Exercises -/
section
-- These instances are removed so that the algebra of `ℂ` cannot be invoked
-- as a one-line typeclass call (e.g. `add_comm α β`). Beyond the obvious
-- `commRing` / `field` chain, several *normed* / *RCLike* instances also
-- propagate `AddCommSemigroup ℂ`, `Semigroup ℂ`, `Distrib ℂ`, so they need
-- to be removed too.  The reader is expected to destructure `α = ⟨a, b⟩`
-- and reduce to `add_comm`, `add_assoc`, … on `ℝ`.
attribute [-instance] Complex.addCommGroup
attribute [-instance] Complex.addGroupWithOne
attribute [-instance] Complex.commRing
attribute [-instance] Complex.instRing
attribute [-instance] Complex.instCommSemiring
attribute [-instance] Complex.instSemiring
attribute [-instance] Complex.instDivInvMonoid
attribute [-instance] Complex.instField
attribute [-instance] Complex.instNormedField
attribute [-instance] Complex.instDenselyNormedField
attribute [-instance] Complex.instRCLike
attribute [-instance] Complex.instNormedAddCommGroup

theorem exercise_1A_1 (α β : ℂ) : α + β = β + α := by sorry

theorem exercise_1A_2 (α β γ : ℂ) : (α + β) + γ = α + (β + γ) := by sorry

theorem exercise_1A_3 (α β γ : ℂ) : (α * β) * γ = α * (β * γ) := by sorry

theorem exercise_1A_4 (α β γ : ℂ) : γ * (α + β) = γ * α + γ * β := by sorry
end

@[avoiding neg_eq_of_add_eq_zero_left, neg_eq_of_add_eq_zero_right,
    eq_neg_of_add_eq_zero_left, eq_neg_of_add_eq_zero_right,
    add_eq_zero_iff_eq_neg, add_eq_zero_iff_neg_eq,
    add_eq_zero_iff_eq_neg', add_eq_zero_iff_neg_eq',
    eq_neg_iff_add_eq_zero, neg_eq_iff_add_eq_zero,
    add_neg_eq_zero, neg_add_eq_zero,
    add_left_cancel, add_right_cancel,
    add_left_cancel_iff, add_right_cancel_iff,
    add_left_injective, add_right_injective,
    add_left_inj, add_right_inj,
    neg_unique, left_neg_eq_right_neg, Lean.Grind]
theorem exercise_1A_5 (α : ℂ) : ∃! β : ℂ, α + β = 0 := by sorry

@[avoiding inv_eq_of_mul_eq_one_left, inv_eq_of_mul_eq_one_right,
    eq_inv_of_mul_eq_one_left, eq_inv_of_mul_eq_one_right,
    mul_eq_one_iff_eq_inv, mul_eq_one_iff_inv_eq,
    mul_eq_one_iff_eq_inv', mul_eq_one_iff_inv_eq',
    eq_inv_iff_mul_eq_one, inv_eq_iff_mul_eq_one,
    mul_inv_eq_one, inv_mul_eq_one,
    mul_eq_one_iff_eq_inv₀, mul_eq_one_iff_inv_eq₀,
    mul_inv_eq_one₀, inv_mul_eq_one₀,
    mul_left_cancel, mul_right_cancel,
    mul_left_cancel₀, mul_right_cancel₀,
    mul_left_cancel_iff, mul_right_cancel_iff,
    mul_left_injective, mul_right_injective,
    mul_left_inj, mul_right_inj,
    mul_left_inj', mul_right_inj',
    inv_unique, left_inv_eq_right_inv, Lean.Grind]
theorem exercise_1A_6 (α : ℂ) (hα : α ≠ 0) : ∃! β : ℂ, α * β = 1 := by sorry

theorem exercise_1A_7 :
    ((-1 + Real.sqrt 3 * I) / 2) ^ 3 = 1 := by
  sorry

theorem exercise_1A_8 :
    ∃ z w : ℂ, z ≠ w ∧ z ^ 2 = I ∧ w ^ 2 = I := by
  sorry

theorem exercise_1A_9 :
    ∃ x : Fin 4 → ℝ,
      ![4, -3, 1, 7] + (2 : ℝ) • x = ![5, 9, -6, 8] := by
  sorry

theorem exercise_1A_10 :
    ¬ ∃ z : ℂ, z • ![2 - 3*I, 5 + 4*I, -6 + 7*I] =
      ![12 - 5*I, 7 + 22*I, -32 - 9*I] := by
  sorry

section
attribute [-instance] Pi.addSemigroup Pi.addCommSemigroup Pi.addMonoid
  Pi.addCommMonoid Pi.addGroup Pi.addCommGroup Pi.addMonoidWithOne
  Pi.addGroupWithOne Pi.addZeroClass Pi.subNegMonoid Pi.subtractionMonoid
  Pi.subNegZeroMonoid Pi.instSubtractionCommMonoid
  Pi.addCancelCommMonoid Pi.addCancelMonoid Pi.addLeftCancelSemigroup
  Pi.addRightCancelSemigroup Pi.addLeftCancelMonoid Pi.addRightCancelMonoid
  Pi.ring Pi.commRing Pi.semiring Pi.commSemiring Pi.nonAssocRing
  Pi.nonAssocSemiring Pi.nonUnitalRing Pi.nonUnitalSemiring
  Pi.nonUnitalNonAssocRing Pi.nonUnitalNonAssocSemiring Pi.nonUnitalCommRing
  Pi.nonUnitalCommSemiring
  Pi.mulAction Pi.distribMulAction Pi.module Pi.Function.module
  Pi.mulActionWithZero Pi.distribSMul Pi.smulWithZero Pi.smulZeroClass

theorem exercise_1A_11 (x y z : Fin n → F) :
    (x + y) + z = x + (y + z) := by
  sorry

theorem exercise_1A_12 (a b : F) (x : Fin n → F) :
    (a * b) • x = a • (b • x) := by
  sorry

theorem exercise_1A_13 (x : Fin n → F) : (1 : F) • x = x := by
  sorry

theorem exercise_1A_14 (γ : F) (x y : Fin n → F) :
    γ • (x + y) = γ • x + γ • y := by
  sorry

theorem exercise_1A_15 (a b : F) (x : Fin n → F) :
    (a + b) • x = a • x + b • x := by
  sorry
end

end LADR.Section_1A
