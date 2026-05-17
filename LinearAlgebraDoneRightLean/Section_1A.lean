import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
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

attribute [push] Complex.add_re Complex.add_im Complex.mul_re Complex.mul_im

/-! 1.2 Example: complex arithmetic -/

example : (2 + 3 * I) * (4 + 5 * I) = -7 + 22 * I := by
  apply Complex.ext <;> simp <;> ring

/-! 1.3 Properties of complex arithmetic -/

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_1 (α β : ℂ) : α + β = β + α := by
  apply Complex.ext
  -- push Complex.re
  <;> grind [add_re, add_im]

/-! 1.4 Example: commutativity of complex multiplication -/

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem mul_comm_example (α β : ℂ) : α * β = β * α := by
  apply Complex.ext
  · simp only [Complex.mul_re]; ring
  · simp only [Complex.mul_im]; ring

theorem exercise_1A_2' (α β γ : ℂ) : (α + β) + γ = α + (β + γ) := by
  apply Complex.ext <;> grind [add_re, add_im]

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_3 (α β γ : ℂ) : (α * β) * γ = α * (β * γ) := by
  apply Complex.ext <;> grind [Complex.mul_re, Complex.mul_im]

@[avoiding Complex.commRing, Complex.instCommSemiring, Complex.instField]
theorem exercise_1A_4 (α β γ : ℂ) : γ * (α + β) = γ * α + γ * β := by
  apply Complex.ext
  · simp ; grind
  · simp ; grind

example (γ : ℂ) : γ + 0 = γ := add_zero γ
example (γ : ℂ) : γ * 1 = γ := mul_one γ

@[avoiding Complex.instNeg, Complex.instSub, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
theorem exercise_1A_5 (α : ℂ) : ∃! β : ℂ, α + β = 0 := by
  use ⟨ -α.re, -α.im ⟩
  constructor
  · apply Complex.ext <;> simp
  · intro y
    dsimp
    intro h
    apply Complex.ext <;> simp
    · have := congr(Complex.re $h)
      simp at this
      grind
    · have := congr(Complex.im $h)
      simp at this
      grind

noncomputable abbrev my_inv (α : ℂ) : ℂ := (Complex.mk
    (α.re / (α.re ^ 2 + α.im ^ 2))
    (-α.im / (α.re ^ 2 + α.im ^ 2))
  )

@[avoiding Complex.instInv, Complex.instDivInvMonoid, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
lemma mul_inv_cancel (α : ℂ) (hα : α ≠ 0) : α * (my_inv α) = 1 := by
  nth_rewrite 1 [← Complex.eta α]
  rw [Complex.mk_mul_mk]
  apply Complex.ext
  · field_simp
    simp
    intro h
    apply hα
    apply Complex.ext <;> norm_num <;> nlinarith
  · field_simp
    norm_num

@[avoiding Complex.instInv, Complex.instDivInvMonoid, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
lemma inv_mul_cancel' (α : ℂ) (hα : α ≠ 0) : (my_inv α) * α = 1 := by
  nth_rewrite 2 [← Complex.eta α]
  rw [Complex.mk_mul_mk]
  apply Complex.ext
  · field_simp
    simp
    intro h
    apply hα
    apply Complex.ext <;> norm_num <;> nlinarith
  · field_simp
    norm_num

@[avoiding Complex.instInv, Complex.instDivInvMonoid, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
lemma one_mul' (α : ℂ) : 1 * α = α := by
  rw [show (1 : ℂ) = Complex.mk 1 0 by rfl, mk_mul_mk]
  simp

@[avoiding Complex.instInv, Complex.instDivInvMonoid, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
lemma mul_assoc' (α β γ : ℂ) : (α * β) * γ = α * (β * γ) := by
  rw [Complex.mk_mul_mk, Complex.mk_mul_mk, Complex.mk_mul_mk, Complex.mk_mul_mk]
  grind

@[avoiding Complex.instInv, Complex.instDivInvMonoid, Complex.commRing, Complex.instCommSemiring,
    Complex.instField]
theorem exercise_1A_6 (α : ℂ) (hα : α ≠ 0) : ∃! β : ℂ, α * β = 1 := by
  use my_inv α
  constructor
  · dsimp
    exact mul_inv_cancel α hα
  · dsimp
    intro y h
    have h' := congr((my_inv α) * $h)
    rw [← mul_assoc'] at h'
    simp at h'
    rw [inv_mul_cancel' α hα] at h'
    rw [one_mul'] at h'
    exact h'

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

Axler's *list of length {lit}`n` over {lit}`α`* is rendered here as `{lean}Fin n → α`, with
the length encoded in the type. **Beware:** Lean has a separate built-in type
{lit}`List α` (a variable-length linked list, written with the `[…]` notation
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

lemma interchange2 (r : ℝ) : (Complex.ofReal r) ^ 2 = Complex.ofReal (r ^ 2) := by
  grind [ofReal_pow]

lemma interchange3 (r : ℝ) : (Complex.ofReal r) ^ 3 = Complex.ofReal (r ^ 3) := by
  grind [ofReal_pow]

lemma im_ofReal (r : ℝ) : (Complex.ofReal r).im = 0 := by
  rw [ofReal_im]

example : (Complex.ofReal (√3 ^ 3) * -I).re = 0 := by
  simp [-ofReal_pow]

example : Complex.ofReal (√3 ^ 2) = 3 := by
  rw [Real.sq_sqrt]
  <;> norm_num

theorem exercise_1A_7 :
    ((-1 + Real.sqrt 3 * I) / 2) ^ 3 = 1 := by
  ring_nf
  rw [show I ^ 2 = -1 by norm_num]
  rw [show I ^ 3 = -I by norm_num]
  rw [interchange2]
  rw [interchange3]
  apply Complex.ext
  · simp [-ofReal_pow] -- disable nonconfluent lemma
    norm_num
  · simp [-ofReal_pow] -- disable nonconfluent lemma
    field_simp
    norm_num

theorem exercise_1A_8 :
    ∃ z w : ℂ, z ≠ w ∧ z ^ 2 = I ∧ w ^ 2 = I := by
  use (1 + I) / √2, (-1 - I) / √2
  and_intros
  · intro h
    have h := congr(Complex.re $h)
    simp at h
    field_simp at h
    norm_num at h
  · ring_nf
    simp [-ofReal_pow]
    rw [interchange2]
    norm_num
    field_simp
  · ring_nf
    simp [-ofReal_pow]
    rw [interchange2]
    norm_num
    field_simp

theorem exercise_1A_9 :
    ∃ x : Fin 4 → ℝ,
      (![4, -3, 1, 7] : Fin 4 → ℝ) + (2 : ℝ) • x = ![5, 9, -6, 8] := by
  use ![1/2, 6, -7/2, 1/2]
  ext i
  fin_cases i <;> dsimp <;> norm_num

lemma test (p q r : ℂ) : (p * q) / r = p * (q / r) := by
  field_simp

attribute [push] Complex.div_re

theorem exercise_1A_10 :
    ¬ ∃ lam : ℂ, lam • (![2 - 3 * I, 5 + 4 * I, -6 + 7 * I] : Fin 3 → ℂ) =
      ![12 - 5 * I, 7 + 22 * I, -32 - 9 * I] := by
  rintro ⟨ lam, hlam ⟩
  have := congr($hlam 0)
  dsimp at this
  have h := congr($this / (2 - 3 * I))
  rw [test] at h
  have : (2 - 3 * I) / (2 - 3 * I) = 1 := by
    field_simp
    norm_num
    intro h
    have h := congr(Complex.re $h)
    simp at h
  rw [this] at h
  simp at h
  subst h
  have h2 := congr(($hlam 2).im)
  simp at h2
  rw [Complex.div_re, Complex.div_im] at h2
  simp [normSq] at h2
  norm_num at h2

@[avoiding add_assoc]
theorem exercise_1A_11 (x y z : Fin n → F) :
    (x + y) + z = x + (y + z) := by
  ext i
  simp
  grind

@[avoiding mul_smul, smul_smul]
theorem exercise_1A_12 (a b : F) (x : Fin n → F) :
    (a * b) • x = a • (b • x) := by
  ext i
  simp
  grind

@[avoiding one_smul]
theorem exercise_1A_13 (x : Fin n → F) : (1 : F) • x = x := by
  ext i
  simp

@[avoiding smul_add]
theorem exercise_1A_14 (γ : F) (x y : Fin n → F) :
    γ • (x + y) = γ • x + γ • y := by
  ext i
  simp
  grind

@[avoiding add_smul]
theorem exercise_1A_15 (a b : F) (x : Fin n → F) :
    (a + b) • x = a • x + b • x := by
  ext i
  simp
  grind

end LADR.Section_1A
