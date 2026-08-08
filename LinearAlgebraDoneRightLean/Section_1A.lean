import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FinCases
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

example : ℂ := ⟨1, 2⟩
example : (⟨1, 2⟩ : ℂ).re = 1 := rfl
example : (⟨1, 2⟩ : ℂ).im = 2 := rfl

example : ℂ := I
example : I ^ 2 = -1 := I_sq

recall Complex.re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z

example (z : ℂ) : ∃ a b : ℝ, z = a + b * I :=
  ⟨z.re, z.im, (re_add_im z).symm⟩

recall Complex.add_re (z w : ℂ) : (z + w).re = z.re + w.re
recall Complex.add_im (z w : ℂ) : (z + w).im = z.im + w.im
recall Complex.mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im
recall Complex.mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re

/-! 1.2 Example: complex arithmetic -/

example : (2 + 3 * I) * (4 + 5 * I) = -7 + 22 * I := by
  apply Complex.ext <;> simp <;> ring

/-! 1.3 Properties of complex arithmetic -/

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_1 (α β : ℂ) : α + β = β + α := by
  apply Complex.ext
  · simp only [Complex.add_re]; ring
  · simp only [Complex.add_im]; ring

/-! 1.4 Example: commutativity of complex multiplication -/

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem mul_comm_example (α β : ℂ) : α * β = β * α := by
  apply Complex.ext
  · simp only [Complex.mul_re]; ring
  · simp only [Complex.mul_im]; ring

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_2 (α β γ : ℂ) : (α + β) + γ = α + (β + γ) := by
  apply Complex.ext
  · simp only [Complex.add_re]; ring
  · simp only [Complex.add_im]; ring

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_3 (α β γ : ℂ) : (α * β) * γ = α * (β * γ) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im]; ring
  · simp only [Complex.mul_re, Complex.mul_im]; ring

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_4 (α β γ : ℂ) : γ * (α + β) = γ * α + γ * β := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_re, Complex.add_re, Complex.add_im]
    ring
  · simp only [Complex.mul_im, Complex.add_im, Complex.add_re]
    ring

example (γ : ℂ) : γ + 0 = γ := add_zero γ
example (γ : ℂ) : γ * 1 = γ := mul_one γ

@[avoiding Complex.instNeg, Complex.instSub, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
theorem exercise_1A_5 (α : ℂ) : ∃! β : ℂ, α + β = 0 := by
  use ⟨-α.re, -α.im⟩
  constructor
  . simp only
    apply Complex.ext
    . simp only [add_re, add_neg_cancel, zero_re]
    . simp only [add_im, add_neg_cancel, zero_im]
  · intro β h
    apply Complex.ext
    . simp only
      have := Complex.add_re α β
      rw [h] at this
      simp at this
      linarith
    . simp only
      have := Complex.add_im α β
      rw [h] at this
      simp at this
      linarith

@[avoiding Complex.instInv, Complex.instDivInvMonoid, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
theorem exercise_1A_6 (α : ℂ) (hα : α ≠ 0) : ∃! β : ℂ, α * β = 1 := by
  -- `1` is a multiplicative identity: the one fact about ℂ we still have to check
  -- coordinatewise, since the ring structure on ℂ is off limits here.
  have mul_one' : ∀ γ : ℂ, γ * 1 = γ := by
    intro γ
    apply Complex.ext
    · simp only [Complex.mul_re, one_re, one_im]; ring
    · simp only [Complex.mul_im, one_re, one_im]; ring
  have hne : α.re ^ 2 + α.im ^ 2 ≠ 0 := by
    contrapose! hα
    apply Complex.ext
    · rw [zero_re]
      nlinarith [sq_nonneg α.re, sq_nonneg α.im]
    · rw [zero_im]
      nlinarith [sq_nonneg α.re, sq_nonneg α.im]
  -- Existence: exhibit the inverse in coordinates.
  obtain ⟨γ, hγ⟩ : ∃ γ : ℂ, α * γ = 1 := by
    refine ⟨⟨α.re / (α.re ^ 2 + α.im ^ 2), -α.im / (α.re ^ 2 + α.im ^ 2)⟩, ?_⟩
    apply Complex.ext
    · simp only [Complex.mul_re]
      field_simp [hne]
      rw [one_re]
      ring_nf
    · simp only [Complex.mul_im]
      field_simp [hne]
      rw [one_im]
      ring_nf
  -- Uniqueness: pure algebra
  use γ, hγ
  intro β h
  calc β = β * 1 := (mul_one' β).symm
    _ = β * (α * γ) := by rw [hγ]
    _ = β * α * γ := (exercise_1A_3 β α γ).symm
    _ = α * β * γ := by rw [mul_comm_example β α]
    _ = 1 * γ := by rw [h]
    _ = γ * 1 := mul_comm_example 1 γ
    _ = γ := mul_one' γ

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

Axler's *list of length {lit}`n` over {lit}`α`* is rendered here as
{lit}`Fin n → α`, with the length encoded in the type. **Beware:** Lean has a
separate built-in type {lit}`List α` (a variable-length linked list, written
with the {lit}`[…]` notation instead of {lit}`![…]`) — it is *not* what Axler
calls a list. -/

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
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [pow_succ, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [hs, Real.sqrt_nonneg 3]

theorem exercise_1A_8 :
    ∃ z w : ℂ, z ≠ w ∧ z ^ 2 = I ∧ w ^ 2 = I := by
  have hs : (√2 : ℂ) ^ 2 = 2 := by
    norm_cast; rw [Real.sq_sqrt]; norm_num
  have hne : (√2 : ℂ) ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  have hz : ((1 + I) / √2 : ℂ) ^ 2 = I := by
    rw [div_pow, hs]
    have h1 : (1 + I : ℂ) ^ 2 = 2 * I := by ring_nf; rw [I_sq]; ring
    rw [h1]
    field_simp
  use (1 + I) / √2, -((1 + I) / √2)
  refine ⟨?_, hz, ?_⟩
  · intro h
    rw [Complex.ext_iff] at h
    simp at h
    field_simp at h
    linarith
  · rw [neg_pow]
    simpa using hz

theorem exercise_1A_9 :
    ∃ x : Fin 4 → ℝ,
      (![4, -3, 1, 7] : Fin 4 → ℝ) + (2 : ℝ) • x = ![5, 9, -6, 8] := by
  use ![0.5, 6, -3.5, 0.5]
  ext i
  fin_cases i <;> norm_num

theorem exercise_1A_10 :
    ¬ ∃ lam : ℂ, lam • (![2 - 3 * I, 5 + 4 * I, -6 + 7 * I] : Fin 3 → ℂ) =
      ![12 - 5 * I, 7 + 22 * I, -32 - 9 * I] := by
  rintro ⟨lam, h⟩
  -- the first coordinate forces `lam = 3 + 2 * I`, which the third then contradicts
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp [Pi.smul_apply, smul_eq_mul] at h0 h2
  rw [Complex.ext_iff] at h0 h2
  simp [Complex.mul_re, Complex.mul_im] at h0 h2
  obtain ⟨h0re, h0im⟩ := h0
  obtain ⟨h2re, h2im⟩ := h2
  linarith

@[avoiding Pi.addSemigroup]
theorem exercise_1A_11 (x y z : Fin n → F) :
    (x + y) + z = x + (y + z) := by
  ext i
  simp only [Pi.add_apply]
  ring

@[avoiding mul_smul, smul_smul]
theorem exercise_1A_12 (a b : F) (x : Fin n → F) :
    (a * b) • x = a • (b • x) := by
  ext i
  simp only [Pi.smul_apply]
  ring

@[avoiding one_smul]
theorem exercise_1A_13 (x : Fin n → F) : (1 : F) • x = x := by
  ext i
  simp only [Pi.smul_apply]
  ring

@[avoiding smul_add]
theorem exercise_1A_14 (γ : F) (x y : Fin n → F) :
    γ • (x + y) = γ • x + γ • y := by
  ext i
  simp only [Pi.smul_apply, Pi.add_apply]
  ring

@[avoiding add_smul]
theorem exercise_1A_15 (a b : F) (x : Fin n → F) :
    (a + b) • x = a • x + b • x := by
  ext i
  simp only [Pi.smul_apply, Pi.add_apply]
  ring

end LADR.Section_1A
