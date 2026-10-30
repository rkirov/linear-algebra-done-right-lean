import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 6A: Inner Products and Norms
-/

namespace LADR.Section_6A

/-! # The field and the inner product convention

Axler's inner product spaces are over {lit}`𝔽`, which is always {lit}`ℝ` or
{lit}`ℂ`. mathlib captures exactly "{lit}`ℝ` or {lit}`ℂ`" with the typeclass
{name}`RCLike`, so throughout this chapter our scalar field is {lit}`𝕜` with
{lit}`[RCLike 𝕜]`. An inner product space is {name}`InnerProductSpace`, built on
top of a {name}`NormedAddCommGroup` (the norm and the inner product are packaged
together — see 6.7). The inner product {lit}`⟨u, v⟩` is written {lit}`⟪u, v⟫_𝕜`
(after {lit}`open scoped InnerProductSpace`), and {name}`inner` is the underlying
function.

**One important divergence.** Axler's inner product (6.2) is *linear in the first
slot* and conjugate-linear in the second. mathlib uses the opposite (physicists')
convention — see Axler's margin remark after 6.2 — so mathlib's inner product is
*conjugate-linear in the first slot* and linear in the second. Concretely,
mathlib's {lit}`⟪u, v⟫_𝕜` equals Axler's {lit}`⟨v, u⟩`. Every numbered *result*
in this section is symmetric under swapping the two slots (Pythagorean theorem,
Cauchy–Schwarz, the triangle and parallelogram identities, …), so the difference
never affects a statement; it only flips which slot carries the conjugate in the
homogeneity axiom. -/

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-! # Inner Products -/

/-! 6.1 Definition: dot product

For {lit}`x, y ∈ ℝⁿ`, the dot product is {lit}`x · y = x₁y₁ + ⋯ + xₙyₙ`. In
mathlib {lit}`ℝⁿ` as an inner product space is {name}`EuclideanSpace` {lit}`ℝ`
{lit}`(Fin n)`, and its (real) inner product is exactly the dot product. -/

example {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  congr 1; ext i
  exact real_inner_comm (y i) (x i) ▸ rfl

/-- The dot product of a vector with itself is the square of its norm:
{lit}`x · x = ‖x‖²`. -/
example {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 :=
  real_inner_self_eq_norm_sq x

/-! 6.2 Definition: inner product

An inner product on {lit}`V` takes each ordered pair {lit}`(u, v)` to a scalar
{lit}`⟨u, v⟩ ∈ 𝕜` satisfying positivity, definiteness, additivity and
homogeneity in a slot, and conjugate symmetry. The following {lit}`recall`s are
mathlib's axioms; note (per the discussion above) that the additivity and
homogeneity axioms live in the *first* slot in Axler and in whichever slot we
name below in mathlib. -/

/-- Positivity: {lit}`⟨v, v⟩ ≥ 0` (a real, nonnegative number). -/
recall inner_self_nonneg {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x : E} :
    0 ≤ RCLike.re ⟪x, x⟫_𝕜

/-- Definiteness: {lit}`⟨v, v⟩ = 0` if and only if {lit}`v = 0`. -/
recall inner_self_eq_zero {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x : E} :
    ⟪x, x⟫_𝕜 = 0 ↔ x = 0

/-- Additivity (in mathlib's first slot):
{lit}`⟨u + v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩`. -/
recall inner_add_left {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y z : E) :
    ⟪x + y, z⟫_𝕜 = ⟪x, z⟫_𝕜 + ⟪y, z⟫_𝕜

/-- Conjugate homogeneity (in mathlib's first slot):
{lit}`⟨λu, v⟩ = λ̄ ⟨u, v⟩`. In Axler's convention the conjugate is instead in the
second slot, and the first slot is genuinely homogeneous. -/
recall inner_smul_left {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) (r : 𝕜) :
    ⟪r • x, y⟫_𝕜 = conj r * ⟪x, y⟫_𝕜

recall inner_smul_right {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) (r : 𝕜) :
    ⟪x, r • y⟫_𝕜 = r * ⟪x, y⟫_𝕜

/-- Conjugate symmetry: {lit}`⟨u, v⟩ = conj ⟨v, u⟩`. -/
example (u v : V) : ⟪u, v⟫_𝕜 = conj ⟪v, u⟫_𝕜 := (inner_conj_symm u v).symm

/-! 6.3 Example: inner products

(a) The Euclidean inner product on {lit}`𝔽ⁿ`, {name}`EuclideanSpace`, is the one
    used above. -/

example {n : ℕ} (w z : EuclideanSpace 𝕜 (Fin n)) :
    ⟪w, z⟫_𝕜 = ∑ i, conj (w i) * z i := by
  rw [PiLp.inner_apply]
  congr 1; ext i
  rw [RCLike.inner_apply']

/-! (b) If {lit}`c₁, …, cₙ` are positive numbers, then a *weighted* inner product
on {lit}`𝔽ⁿ` is defined by {lit}`⟨w, z⟩ = c₁w̄₁z₁ + ⋯ + cₙw̄ₙzₙ`. We package the
five inner-product axioms (in mathlib's slot convention, so the conjugate sits in
the first slot) as an {name}`InnerProductSpace.Core` — mathlib's bundle of "the
data of an inner product satisfying the axioms", from which a genuine
{name}`InnerProductSpace` can be built. -/

@[reducible] noncomputable def weightedCore {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    InnerProductSpace.Core 𝕜 (Fin n → 𝕜) where
  inner w z := ∑ i, conj (w i) * (c i : 𝕜) * z i
  conj_inner_symm w z := by
    simp only [map_sum]
    congr 1; ext i
    simp only [map_mul, RCLike.conj_conj, RCLike.conj_ofReal]
    ring
  re_inner_nonneg w := by
    rw [map_sum]
    apply Finset.sum_nonneg
    intro i _
    have : conj (w i) * (c i : 𝕜) * w i = ((c i * ‖w i‖ ^ 2 : ℝ) : 𝕜) := by
      rw [mul_comm (conj (w i)) _, mul_assoc, RCLike.conj_mul]
      push_cast; ring
    rw [this, RCLike.ofReal_re]
    exact mul_nonneg (hc i).le (sq_nonneg _)
  add_left w w' z := by
    simp only [Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
    congr 1; ext i; ring
  smul_left w z r := by
    rw [Finset.mul_sum]
    congr 1; ext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  definite w hw := by
    have hsum : ∑ i, ((c i * ‖w i‖ ^ 2 : ℝ) : 𝕜) = 0 := by
      rw [← hw]; congr 1; ext i
      rw [mul_comm (conj (w i)) _, mul_assoc, RCLike.conj_mul]
      push_cast; ring
    rw [← RCLike.ofReal_sum] at hsum
    have hreal : ∑ i, (c i * ‖w i‖ ^ 2 : ℝ) = 0 := by exact_mod_cast hsum
    have hz : ∀ i ∈ Finset.univ, c i * ‖w i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i).le (sq_nonneg _)).mp hreal
    funext i
    have hi := hz i (Finset.mem_univ i)
    have : ‖w i‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hi with h | h
      · exact absurd h (hc i).ne'
      · exact h
    simpa using this

/-! Examples (c)–(e) equip infinite-dimensional function spaces with genuine inner
products defined by integration. Unlike (a)/(b) these live at the analysis edge of
the subject, but they are bona fide inner products: we *define* the form
{lit}`⟨·, ·⟩` and verify every axiom, the substantive one being *definiteness*.

(c) On the continuous real-valued functions on {lit}`[-1, 1]`, the inner product
is {lit}`⟨f, g⟩ = ∫₋₁¹ fg`. We model such a function by a continuous
{lit}`f : C(ℝ, ℝ)`, pairing two of them through their values on the interval; on
that space definiteness is the statement that {lit}`⟨f, f⟩ = 0` forces {lit}`f` to
vanish throughout {lit}`[-1, 1]`. -/

section ContinuousInnerProduct
open MeasureTheory

/-- The {lit}`(c)` inner product {lit}`⟨f, g⟩ = ∫₋₁¹ fg` on continuous functions. -/
noncomputable def contInner (f g : C(ℝ, ℝ)) : ℝ := ∫ x in (-1:ℝ)..1, f x * g x

/-- Symmetry: {lit}`⟨f, g⟩ = ⟨g, f⟩`. -/
example (f g : C(ℝ, ℝ)) : contInner f g = contInner g f :=
  intervalIntegral.integral_congr (fun _ _ => mul_comm _ _)

/-- Additivity in the first slot: {lit}`⟨f + g, h⟩ = ⟨f, h⟩ + ⟨g, h⟩`. -/
example (f g h : C(ℝ, ℝ)) : contInner (f + g) h = contInner f h + contInner g h := by
  have hI1 : IntervalIntegrable (fun x => f x * h x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hI2 : IntervalIntegrable (fun x => g x * h x) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [contInner, contInner, contInner,
    show (fun x => (f + g) x * h x) = (fun x => f x * h x + g x * h x) from by
      funext x; simp only [ContinuousMap.add_apply]; ring,
    intervalIntegral.integral_add hI1 hI2]

/-- Homogeneity in the first slot: {lit}`⟨r • f, g⟩ = r ⟨f, g⟩`. -/
example (f g : C(ℝ, ℝ)) (r : ℝ) : contInner (r • f) g = r * contInner f g := by
  rw [contInner, contInner,
    show (fun x => (r • f) x * g x) = (fun x => r * (f x * g x)) from by
      funext x; simp only [ContinuousMap.smul_apply, smul_eq_mul]; ring,
    intervalIntegral.integral_const_mul]

/-- Positivity: {lit}`⟨f, f⟩ ≥ 0`. -/
example (f : C(ℝ, ℝ)) : 0 ≤ contInner f f :=
  intervalIntegral.integral_nonneg (by norm_num) (fun x _ => mul_self_nonneg _)

/-- Definiteness: {lit}`⟨f, f⟩ = 0` forces {lit}`f` to vanish on {lit}`[-1, 1]`. A
nonzero value at one point would, by continuity, make the integral of the
nonnegative {lit}`f²` strictly positive. -/
example (f : C(ℝ, ℝ)) (h : contInner f f = 0) :
    ∀ x ∈ Set.Icc (-1:ℝ) 1, f x = 0 := by
  intro x hx
  by_contra hne
  have hpos : (0:ℝ) < ∫ t in (-1:ℝ)..1, f t * f t := by
    apply intervalIntegral.integral_pos (by norm_num)
    · exact Continuous.continuousOn (by fun_prop)
    · intro t _; exact mul_self_nonneg _
    · exact ⟨x, hx, (mul_self_nonneg (f x)).lt_of_ne (Ne.symm (mul_ne_zero hne hne))⟩
  rw [contInner] at h; rw [h] at hpos
  exact lt_irrefl _ hpos

end ContinuousInnerProduct

section PolynomialInnerProducts
open Polynomial Asymptotics Filter MeasureTheory

/-- Helper: for any polynomial {lit}`s`, the function {lit}`s(x)e⁻ˣ` is integrable
on {lit}`(0, ∞)`, because a polynomial is dominated by {lit}`e^{x/2}` at infinity
while {lit}`e⁻ˣ` decays like {lit}`e^{-x/2}` faster. -/
theorem polyExpIntegrable (s : Polynomial ℝ) :
    IntegrableOn (fun x => s.eval x * Real.exp (-x)) (Set.Ioi (0:ℝ)) volume := by
  apply integrable_of_isBigO_exp_neg (b := 1/2) (by norm_num)
  · fun_prop
  · have key : (fun x => s.eval x) =O[atTop] (fun x : ℝ => x ^ s.natDegree) := by
      have hh := Polynomial.isBigO_atTop_of_degree_le s ((X : ℝ[X]) ^ s.natDegree)
        (by rw [Polynomial.degree_X_pow]; exact Polynomial.degree_le_natDegree)
      simpa using hh
    have h1 : (fun x => s.eval x) =O[atTop] (fun x : ℝ => Real.exp ((1/2) * x)) :=
      key.trans (isLittleO_pow_exp_pos_mul_atTop _ (by norm_num)).isBigO
    calc (fun x => s.eval x * Real.exp (-x))
        =O[atTop] (fun x => Real.exp ((1/2) * x) * Real.exp (-x)) := h1.mul (isBigO_refl _ _)
      _ = (fun x => Real.exp (-(1/2) * x)) := by funext x; rw [← Real.exp_add]; ring_nf

/-- (d) The inner product {lit}`⟨p, q⟩ = p(0)q(0) + ∫₋₁¹ p′q′` on {lit}`𝒫(ℝ)`,
packaged as an {name}`InnerProductSpace.Core`. Definiteness holds on the genuine
polynomial space, so this really is an inner product: if
{lit}`p(0)² + ∫₋₁¹ (p′)² = 0`, both nonnegative terms vanish, so {lit}`p(0) = 0`
and (as in (c)) {lit}`p′` vanishes on {lit}`[-1, 1]`; having infinitely many
roots, {lit}`p′` is the zero polynomial, so {lit}`p` is constant, and
{lit}`p(0) = 0` forces {lit}`p = 0`. -/
@[reducible] noncomputable def polyInnerCore_d : InnerProductSpace.Core ℝ (Polynomial ℝ) where
  inner p q := p.eval 0 * q.eval 0
    + ∫ x in (-1:ℝ)..1, p.derivative.eval x * q.derivative.eval x
  conj_inner_symm p q := by
    simp only [starRingEnd_apply, star_trivial]
    rw [mul_comm (q.eval 0)]
    congr 1
    exact intervalIntegral.integral_congr (fun x _ => mul_comm _ _)
  re_inner_nonneg p := by
    rw [RCLike.re_to_real]
    have h1 : (0:ℝ) ≤ p.eval 0 * p.eval 0 := mul_self_nonneg _
    have h2 : (0:ℝ) ≤ ∫ x in (-1:ℝ)..1, p.derivative.eval x * p.derivative.eval x :=
      intervalIntegral.integral_nonneg (by norm_num) (fun x _ => mul_self_nonneg _)
    linarith
  add_left p₁ p₂ q := by
    have hI1 : IntervalIntegrable (fun x => p₁.derivative.eval x * q.derivative.eval x)
        volume (-1) 1 := by apply Continuous.intervalIntegrable; fun_prop
    have hI2 : IntervalIntegrable (fun x => p₂.derivative.eval x * q.derivative.eval x)
        volume (-1) 1 := by apply Continuous.intervalIntegrable; fun_prop
    simp only [eval_add, Polynomial.derivative_add]
    rw [show (fun x => (p₁.derivative.eval x + p₂.derivative.eval x) * q.derivative.eval x)
        = (fun x => p₁.derivative.eval x * q.derivative.eval x
          + p₂.derivative.eval x * q.derivative.eval x) from by funext x; ring,
      intervalIntegral.integral_add hI1 hI2]
    ring
  smul_left p q r := by
    simp only [starRingEnd_apply, star_trivial, eval_smul, smul_eq_mul, derivative_smul]
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    ring
  definite p hp := by
    have t1 : (0:ℝ) ≤ p.eval 0 * p.eval 0 := mul_self_nonneg _
    have t2 : (0:ℝ) ≤ ∫ x in (-1:ℝ)..1, p.derivative.eval x * p.derivative.eval x :=
      intervalIntegral.integral_nonneg (by norm_num) (fun x _ => mul_self_nonneg _)
    rw [add_eq_zero_iff_of_nonneg t1 t2] at hp
    obtain ⟨h0, hI⟩ := hp
    have heval0 : p.eval 0 = 0 := by rcases mul_eq_zero.mp h0 with h | h <;> exact h
    have hderiv_zero : ∀ x ∈ Set.Icc (-1:ℝ) 1, p.derivative.eval x = 0 := by
      intro x hx
      by_contra hne
      have hpos : (0:ℝ) < ∫ t in (-1:ℝ)..1, p.derivative.eval t * p.derivative.eval t := by
        apply intervalIntegral.integral_pos (by norm_num)
        · exact Continuous.continuousOn (by fun_prop)
        · intro t _; exact mul_self_nonneg _
        · exact ⟨x, hx, (mul_self_nonneg _).lt_of_ne (Ne.symm (mul_ne_zero hne hne))⟩
      rw [hI] at hpos; exact lt_irrefl _ hpos
    have hderiv : p.derivative = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot _
        ((Set.Icc_infinite (by norm_num)).mono (fun x hx => hderiv_zero x hx))
    rw [Polynomial.eq_C_of_natDegree_eq_zero
        (Polynomial.natDegree_eq_zero_of_derivative_eq_zero hderiv),
      show p.coeff 0 = 0 from by rw [Polynomial.coeff_zero_eq_eval_zero]; exact heval0]
    simp

/-- (e) The inner product {lit}`⟨p, q⟩ = ∫₀^∞ p(x)q(x)e⁻ˣ dx` on {lit}`𝒫(ℝ)`,
packaged as an {name}`InnerProductSpace.Core` via {name}`polyExpIntegrable`.
Definiteness: if {lit}`∫₀^∞ p²e⁻ˣ = 0` but {lit}`p ≠ 0`, then {lit}`p` is nonzero
at some point of {lit}`[1, 2]` (only finitely many roots), so {lit}`∫₁² p²e⁻ˣ > 0`,
and since {lit}`p²e⁻ˣ ≥ 0` this forces the integral over {lit}`(0, ∞)` to be
strictly positive — a contradiction. -/
@[reducible] noncomputable def polyInnerCore_e : InnerProductSpace.Core ℝ (Polynomial ℝ) where
  inner p q := ∫ x in Set.Ioi (0:ℝ), (p * q).eval x * Real.exp (-x)
  conj_inner_symm p q := by
    simp only [starRingEnd_apply, star_trivial]
    rw [mul_comm q p]
  re_inner_nonneg p := by
    rw [RCLike.re_to_real]
    apply setIntegral_nonneg measurableSet_Ioi
    intro x _; rw [eval_mul]; exact mul_nonneg (mul_self_nonneg _) (Real.exp_nonneg _)
  add_left p₁ p₂ q := by
    rw [show (fun x => ((p₁ + p₂) * q).eval x * Real.exp (-x))
        = (fun x => (p₁ * q).eval x * Real.exp (-x) + (p₂ * q).eval x * Real.exp (-x)) from by
          funext x; simp only [add_mul, eval_add],
      MeasureTheory.integral_add (polyExpIntegrable _) (polyExpIntegrable _)]
  smul_left p q r := by
    simp only [starRingEnd_apply, star_trivial]
    rw [show (fun x => ((r • p) * q).eval x * Real.exp (-x))
        = (fun x => r * ((p * q).eval x * Real.exp (-x))) from by
          funext x; rw [smul_mul_assoc, eval_smul, smul_eq_mul]; ring,
      MeasureTheory.integral_const_mul]
  definite p hp := by
    simp_rw [eval_mul, ← pow_two] at hp
    have hint : IntegrableOn (fun x => (p.eval x) ^ 2 * Real.exp (-x))
        (Set.Ioi (0:ℝ)) volume := by
      have hh := polyExpIntegrable (p * p)
      simp_rw [eval_mul, ← pow_two] at hh; exact hh
    by_contra hp0
    have hc : ∃ c ∈ Set.Icc (1:ℝ) 2, p.eval c ≠ 0 := by
      by_contra hcon
      apply hp0
      apply Polynomial.eq_zero_of_infinite_isRoot p
      apply (Set.Icc_infinite (show (1:ℝ) < 2 by norm_num)).mono
      intro x hx; by_contra hx0; exact hcon ⟨x, hx, hx0⟩
    obtain ⟨c, hcIcc, hcne⟩ := hc
    have hgpos : (0:ℝ) < ∫ x in (1:ℝ)..2, (p.eval x) ^ 2 * Real.exp (-x) := by
      apply intervalIntegral.integral_pos (by norm_num)
      · exact Continuous.continuousOn (by fun_prop)
      · intro x _; positivity
      · refine ⟨c, hcIcc, ?_⟩
        have : (0:ℝ) < (p.eval c) ^ 2 := by positivity
        positivity
    have hmono : ∫ x in Set.Ioc (1:ℝ) 2, (p.eval x) ^ 2 * Real.exp (-x)
        ≤ ∫ x in Set.Ioi (0:ℝ), (p.eval x) ^ 2 * Real.exp (-x) := by
      apply setIntegral_mono_set hint
      · filter_upwards with x using by positivity
      · filter_upwards with x hx using lt_trans (by norm_num) hx.1
    rw [intervalIntegral.integral_of_le (by norm_num)] at hgpos
    rw [hp] at hmono
    linarith

end PolynomialInnerProducts

/-! 6.4 Definition: inner product space

An inner product space is a vector space together with an inner product; this is
mathlib's {name}`InnerProductSpace`. -/

example : InnerProductSpace 𝕜 V := inferInstance

/-! 6.5 Notation: {lit}`V`, {lit}`W`

For the rest of this chapter and the next, {lit}`V` and {lit}`W` denote inner
product spaces over {lit}`𝕜` — the {lit}`variable` declarations above. -/

/-! 6.6 Basic properties of an inner product -/

/-- (a) For each fixed {lit}`v`, the map {lit}`u ↦ ⟨u, v⟩` is linear. In mathlib's
convention it is the *second* slot that is linear, so we record the linear map
{lit}`u ↦ ⟨v, u⟩`, namely {name}`innerSL`. -/
example (v : V) (u : V) : innerSL 𝕜 v u = ⟪v, u⟫_𝕜 := rfl

example (v : V) (u₁ u₂ : V) : ⟪v, u₁ + u₂⟫_𝕜 = ⟪v, u₁⟫_𝕜 + ⟪v, u₂⟫_𝕜 :=
  inner_add_right v u₁ u₂

example (v u : V) (r : 𝕜) : ⟪v, r • u⟫_𝕜 = r * ⟪v, u⟫_𝕜 := inner_smul_right v u r

/-- (b) {lit}`⟨0, v⟩ = 0`. -/
example (v : V) : ⟪(0 : V), v⟫_𝕜 = 0 := inner_zero_left v

/-- (c) {lit}`⟨v, 0⟩ = 0`. -/
example (v : V) : ⟪v, (0 : V)⟫_𝕜 = 0 := inner_zero_right v

/-- (d) {lit}`⟨u, v + w⟩ = ⟨u, v⟩ + ⟨u, w⟩`. -/
example (u v w : V) : ⟪u, v + w⟫_𝕜 = ⟪u, v⟫_𝕜 + ⟪u, w⟫_𝕜 := inner_add_right u v w

/-- (e) {lit}`⟨u, λv⟩ = λ⟨u, v⟩` (with the conjugate on the other slot in Axler's
convention). -/
example (u v : V) (r : 𝕜) : ⟪u, r • v⟫_𝕜 = r * ⟪u, v⟫_𝕜 := inner_smul_right u v r
example (u v : V) (r : 𝕜) : ⟪r • u, v⟫_𝕜 = (conj r) * ⟪u, v⟫_𝕜 := inner_smul_left u v r

/-! # Norms -/

/-! 6.7 Definition: norm, {lit}`‖v‖`

The norm of {lit}`v` is {lit}`‖v‖ = √⟨v, v⟩`. In mathlib the norm comes first (as
part of the {name}`NormedAddCommGroup`) and the inner product is compatible with
it; this compatibility is exactly Axler's defining equation. -/

example (v : V) : ‖v‖ = Real.sqrt (RCLike.re ⟪v, v⟫_𝕜) :=
  norm_eq_sqrt_re_inner (𝕜 := 𝕜) v

/-- Over a real inner product space the conjugate/real-part bookkeeping drops
away: {lit}`‖v‖ = √⟨v, v⟩`. -/
example (w : W) : ⟪w, w⟫_𝕜 = (‖w‖ : 𝕜) ^ 2 := inner_self_eq_norm_sq_to_K w

/-! 6.8 Example: norms

(a) {lit}`‖(z₁, …, zₙ)‖ = √(|z₁|² + ⋯ + |zₙ|²)` for {lit}`𝔽ⁿ` with the Euclidean
inner product. -/

example {n : ℕ} (z : EuclideanSpace 𝕜 (Fin n)) :
    ‖z‖ = Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]

/-- (b) For {lit}`f` in the continuous functions on {lit}`[-1, 1]` with the inner
product of 6.3(c), the induced norm {lit}`‖f‖ = √⟨f, f⟩` (Definition 6.7) is
{lit}`√∫₋₁¹ f²`. -/
example (f : C(ℝ, ℝ)) :
    Real.sqrt (contInner f f) = Real.sqrt (∫ x in (-1:ℝ)..1, (f x) ^ 2) := by
  unfold contInner
  exact congrArg Real.sqrt (intervalIntegral.integral_congr (fun x _ => (sq (f x)).symm))

/-! 6.9 Basic properties of the norm

Suppose {lit}`v ∈ V`. -/

/-- (a) {lit}`‖v‖ = 0` if and only if {lit}`v = 0`: {lit}`‖v‖ = 0` iff
{lit}`⟨v, v⟩ = 0`, iff {lit}`v = 0` by definiteness. -/
example (v : V) : ‖v‖ = 0 ↔ v = 0 := by
  have h : ⟪v, v⟫_𝕜 = 0 ↔ v = 0 := inner_self_eq_zero
  rw [inner_self_eq_norm_sq_to_K] at h
  rw [← h]
  constructor
  · intro h0; rw [h0]; simp
  · intro h0; exact_mod_cast (pow_eq_zero_iff two_ne_zero).mp h0

/-- (b) {lit}`‖λv‖ = |λ| ‖v‖` for all {lit}`λ ∈ 𝕜`: both sides are nonnegative
and {lit}`‖λv‖² = ⟨λv, λv⟩ = λλ̄⟨v, v⟩ = |λ|²‖v‖²`. -/
example (v : V) (r : 𝕜) : ‖r • v‖ = ‖r‖ * ‖v‖ := by
  have h : ((‖r • v‖ ^ 2 : ℝ) : 𝕜) = (((‖r‖ * ‖v‖) ^ 2 : ℝ) : 𝕜) := by
    push_cast
    rw [← inner_self_eq_norm_sq_to_K, inner_smul_left, inner_smul_right,
      inner_self_eq_norm_sq_to_K, ← mul_assoc, RCLike.conj_mul]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp (by exact_mod_cast h)

/-! 6.10 Definition: orthogonal

Two vectors {lit}`u, v ∈ V` are *orthogonal* if {lit}`⟨u, v⟩ = 0`. -/

/-- {lit}`u` and {lit}`v` are orthogonal. -/
def Orthogonal (u v : V) : Prop := ⟪u, v⟫_𝕜 = 0

/-- Orthogonality does not depend on the order of the two vectors. -/
theorem orthogonal_comm (u v : V) : Orthogonal (𝕜 := 𝕜) u v ↔ Orthogonal (𝕜 := 𝕜) v u :=
  inner_eq_zero_symm

/-! 6.11 Orthogonality and 0 -/

/-- (a) {lit}`0` is orthogonal to every vector in {lit}`V`. -/
theorem zero_orthogonal (v : V) : Orthogonal (𝕜 := 𝕜) 0 v := inner_zero_left v

/-- (b) {lit}`0` is the only vector in {lit}`V` orthogonal to itself. -/
theorem orthogonal_self_iff (v : V) : Orthogonal (𝕜 := 𝕜) v v ↔ v = 0 :=
  inner_self_eq_zero

/-! 6.12 Pythagorean theorem

If {lit}`u` and {lit}`v` are orthogonal, then {lit}`‖u + v‖² = ‖u‖² + ‖v‖²`. -/

/-- The computation behind 6.12, 6.17 and 6.21:
{lit}`‖u + v‖² = ⟨u + v, u + v⟩ = ‖u‖² + ‖v‖² + ⟨u, v⟩ + ⟨v, u⟩`, and
{lit}`⟨u, v⟩ + ⟨v, u⟩ = ⟨u, v⟩ + conj ⟨u, v⟩ = 2 Re ⟨u, v⟩`. -/
@[avoiding norm_add_sq]
theorem norm_add_sq_expand (u v : V) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * RCLike.re ⟪u, v⟫_𝕜 := by
  have h : ((‖u + v‖ ^ 2 : ℝ) : 𝕜) = ⟪u, u⟫_𝕜 + ⟪v, v⟫_𝕜 + (⟪u, v⟫_𝕜 + ⟪v, u⟫_𝕜) := by
    push_cast
    rw [← inner_self_eq_norm_sq_to_K, inner_add_left, inner_add_right, inner_add_right]
    ring
  have h' := congrArg RCLike.re h
  rw [RCLike.ofReal_re, map_add, map_add, map_add, inner_re_symm (𝕜 := 𝕜) v u] at h'
  rw [h', ← norm_sq_eq_re_inner (𝕜 := 𝕜) u, ← norm_sq_eq_re_inner (𝕜 := 𝕜) v]
  ring

/-- The same computation with {lit}`−v`:
{lit}`‖u − v‖² = ‖u‖² + ‖v‖² − 2 Re ⟨u, v⟩`. -/
@[avoiding norm_sub_sq]
theorem norm_sub_sq_expand (u v : V) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * RCLike.re ⟪u, v⟫_𝕜 := by
  rw [sub_eq_add_neg, norm_add_sq_expand (𝕜 := 𝕜), norm_neg, inner_neg_right, map_neg]
  ring

@[avoiding norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero]
theorem pythagorean (u v : V) (h : Orthogonal (𝕜 := 𝕜) u v) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  -- `‖u + v‖² = ‖u‖² + ‖v‖² + 2 Re ⟨u, v⟩` and `⟨u, v⟩ = 0`
  rw [norm_add_sq_expand (𝕜 := 𝕜), show ⟪u, v⟫_𝕜 = 0 from h, map_zero, mul_zero, add_zero]

/-! 6.13 An orthogonal decomposition

Suppose {lit}`u, v ∈ V` with {lit}`v ≠ 0`. Writing {lit}`c = ⟨u, v⟩ / ‖v‖²` and
{lit}`w = u − cv`, we get {lit}`u = cv + w` with {lit}`w` orthogonal to {lit}`v`.
(Again reading Axler's {lit}`⟨u, v⟩` as mathlib's {lit}`⟪v, u⟫`.) -/

theorem orthogonal_decomposition (u v : V) (hv : v ≠ 0) :
    ∃ (c : 𝕜) (w : V), u = c • v + w ∧ Orthogonal (𝕜 := 𝕜) v w := by
  have hvv : ⟪v, v⟫_𝕜 ≠ 0 := fun h => hv (inner_self_eq_zero.mp h)
  refine ⟨⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜, u - (⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜) • v, by abel, ?_⟩
  unfold Orthogonal
  rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hvv, sub_self]

/-! 6.14 Cauchy–Schwarz inequality

For {lit}`u, v ∈ V`, {lit}`|⟨u, v⟩| ≤ ‖u‖ ‖v‖`, with equality if and only if one
of {lit}`u, v` is a scalar multiple of the other. -/

/-- The heart of Axler's proof of 6.14. Write {lit}`u = cv + w` with
{lit}`w` orthogonal to {lit}`v` (6.13). By the Pythagorean theorem
{lit}`‖u‖² = |c|²‖v‖² + ‖w‖²`, and {lit}`⟨u, v⟩ = c‖v‖²`; multiplying the first
equation by {lit}`‖v‖²` gives {lit}`‖u‖²‖v‖² = |⟨u, v⟩|² + ‖w‖²‖v‖²`. -/
theorem cauchy_schwarz_aux {u v w : V} {c : 𝕜} (hu : u = c • v + w)
    (hw : Orthogonal (𝕜 := 𝕜) v w) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 = ‖⟪u, v⟫_𝕜‖ ^ 2 + ‖w‖ ^ 2 * ‖v‖ ^ 2 := by
  have hcvw : Orthogonal (𝕜 := 𝕜) (c • v) w := by
    unfold Orthogonal at hw ⊢
    rw [inner_smul_left, hw, mul_zero]
  have hpyth : ‖u‖ ^ 2 = ‖c‖ ^ 2 * ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [hu, pythagorean _ _ hcvw, norm_smul, mul_pow]
  have hinner : ⟪u, v⟫_𝕜 = conj c * ((‖v‖ : 𝕜) ^ 2) := by
    have hwv : ⟪w, v⟫_𝕜 = 0 := (orthogonal_comm v w).mp hw
    rw [hu, inner_add_left, inner_smul_left, hwv, add_zero, inner_self_eq_norm_sq_to_K]
  rw [hpyth, hinner, norm_mul, RCLike.norm_conj, norm_pow, RCLike.norm_ofReal, abs_norm]
  ring

@[avoiding norm_inner_le_norm]
theorem cauchy_schwarz (u v : V) : ‖⟪u, v⟫_𝕜‖ ≤ ‖u‖ * ‖v‖ := by
  -- if `v = 0`, both sides are `0`
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, inner_zero_right, norm_zero, norm_zero, mul_zero]
  -- otherwise decompose `u = cv + w` with `w ⟂ v`, so `‖u‖²‖v‖² ≥ |⟨u, v⟩|²`
  obtain ⟨c, w, hu, hw⟩ := orthogonal_decomposition (𝕜 := 𝕜) u v hv
  have h := cauchy_schwarz_aux hu hw
  have hsq : ‖⟪u, v⟫_𝕜‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    rw [mul_pow, h]
    nlinarith [sq_nonneg ‖w‖, sq_nonneg ‖v‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The equality case (stated, as in mathlib, for nonzero vectors; the case where
one vector is {lit}`0` makes both sides {lit}`0`). -/
@[avoiding norm_inner_eq_norm_iff]
theorem cauchy_schwarz_eq_iff {u v : V} :
    ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖ ↔ ∃ r : 𝕜, v = r • u ∨ u = r • v := by
  constructor
  · intro h
    rcases eq_or_ne u 0 with hu | hu
    · exact ⟨0, Or.inr (by rw [hu, zero_smul])⟩
    · rcases eq_or_ne v 0 with hv | hv
      · exact ⟨0, Or.inl (by rw [hv, zero_smul])⟩
      · -- equality forces `‖w‖²‖v‖² = 0` in the decomposition `u = cv + w`, so `w = 0`
        obtain ⟨c, w, hcw, hw⟩ := orthogonal_decomposition (𝕜 := 𝕜) u v hv
        have haux := cauchy_schwarz_aux hcw hw
        rw [← mul_pow, ← h, left_eq_add] at haux
        have hw0 : w = 0 := by
          have hv2 : ‖v‖ ^ 2 ≠ 0 := by positivity
          have hw2 : ‖w‖ ^ 2 = 0 := (mul_eq_zero.mp haux).resolve_right hv2
          exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hw2)
        exact ⟨c, Or.inr (by rw [hcw, hw0, add_zero])⟩
  · rintro ⟨r, hr | hr⟩
    · subst hr
      rw [inner_smul_right, norm_mul, norm_smul, inner_self_eq_norm_sq_to_K, norm_pow,
        RCLike.norm_ofReal, abs_norm]
      ring
    · subst hr
      rw [inner_smul_left, norm_mul, norm_smul, RCLike.norm_conj, inner_self_eq_norm_sq_to_K,
        norm_pow, RCLike.norm_ofReal, abs_norm]
      ring

/-! 6.16 Example: Cauchy–Schwarz inequality

(a) {lit}`(x₁y₁ + ⋯ + xₙyₙ)² ≤ (x₁² + ⋯ + xₙ²)(y₁² + ⋯ + yₙ²)` for reals, from
applying 6.14 to {lit}`ℝⁿ`. -/

example {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * (∑ i, y i ^ 2) := by
  have hcs := cauchy_schwarz (𝕜 := ℝ) x y
  have hxy : ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
    rw [PiLp.inner_apply]; congr 1; ext i; exact real_inner_comm (y i) (x i) ▸ rfl
  have hxx : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    congr 1; ext i; rw [real_inner_comm]; exact (real_inner_self_eq_norm_sq (x i)).trans (by
      rw [Real.norm_eq_abs, sq_abs])
  have hyy : ‖y‖ ^ 2 = ∑ i, y i ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    congr 1; ext i; rw [real_inner_comm]; exact (real_inner_self_eq_norm_sq (y i)).trans (by
      rw [Real.norm_eq_abs, sq_abs])
  rw [hxy] at hcs
  have h2 : (∑ i, x i * y i) ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    rw [Real.norm_eq_abs] at hcs
    nlinarith [abs_nonneg (∑ i, x i * y i), sq_abs (∑ i, x i * y i)]
  rw [mul_pow, hxx, hyy] at h2
  exact h2

/-! (b) For continuous {lit}`f, g` on {lit}`[-1, 1]`, Cauchy–Schwarz for the
6.3(c) inner product reads {lit}`(∫₋₁¹ fg)² ≤ (∫₋₁¹ f²)(∫₋₁¹ g²)`. It follows from
{lit}`∫₋₁¹ (f - tg)² ≥ 0` for every {lit}`t`: the right side is a nonnegative
quadratic in {lit}`t`, so its discriminant is {lit}`≤ 0`. -/

section
open MeasureTheory

example (f g : C(ℝ, ℝ)) :
    (∫ x in (-1:ℝ)..1, f x * g x) ^ 2
      ≤ (∫ x in (-1:ℝ)..1, (f x) ^ 2) * (∫ x in (-1:ℝ)..1, (g x) ^ 2) := by
  have key : ∀ t : ℝ, 0 ≤ (∫ x in (-1:ℝ)..1, (g x) ^ 2) * (t * t)
      + (-2 * ∫ x in (-1:ℝ)..1, f x * g x) * t + ∫ x in (-1:ℝ)..1, (f x) ^ 2 := by
    intro t
    have i1 : IntervalIntegrable (fun x => (f x) ^ 2) volume (-1) 1 :=
      (by fun_prop : Continuous fun x => (f x) ^ 2).intervalIntegrable (-1) 1
    have i2 : IntervalIntegrable (fun x => 2 * t * (f x * g x)) volume (-1) 1 :=
      (by fun_prop : Continuous fun x => 2 * t * (f x * g x)).intervalIntegrable (-1) 1
    have i3 : IntervalIntegrable (fun x => t ^ 2 * (g x) ^ 2) volume (-1) 1 :=
      (by fun_prop : Continuous fun x => t ^ 2 * (g x) ^ 2).intervalIntegrable (-1) 1
    have hexp : ∫ x in (-1:ℝ)..1, (f x - t * g x) ^ 2
        = (∫ x in (-1:ℝ)..1, (g x) ^ 2) * (t * t)
          + (-2 * ∫ x in (-1:ℝ)..1, f x * g x) * t + ∫ x in (-1:ℝ)..1, (f x) ^ 2 := by
      rw [show (fun x => (f x - t * g x) ^ 2)
          = (fun x => ((f x) ^ 2 - 2 * t * (f x * g x)) + t ^ 2 * (g x) ^ 2) from by
            funext x; ring,
        intervalIntegral.integral_add (i1.sub i2) i3,
        intervalIntegral.integral_sub i1 i2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring
    rw [← hexp]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith [hd]

end

/-! 6.17 Triangle inequality

{lit}`‖u + v‖ ≤ ‖u‖ + ‖v‖`, with equality if and only if one of {lit}`u, v` is a
nonnegative real multiple of the other. -/

include 𝕜 in
@[avoiding norm_add_le]
theorem triangle_inequality (u v : V) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  -- `‖u + v‖² = ‖u‖² + ‖v‖² + 2 Re ⟨u, v⟩ ≤ ‖u‖² + ‖v‖² + 2|⟨u, v⟩|
  --   ≤ ‖u‖² + ‖v‖² + 2‖u‖‖v‖ = (‖u‖ + ‖v‖)²`, using Cauchy–Schwarz
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    rw [norm_add_sq_expand (𝕜 := 𝕜)]
    nlinarith [RCLike.re_le_norm ⟪u, v⟫_𝕜, cauchy_schwarz (𝕜 := 𝕜) u v]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- The equality case: {lit}`‖u + v‖ = ‖u‖ + ‖v‖` if and only if {lit}`u` and
{lit}`v` point in the same direction, i.e. one is a nonnegative real multiple of the
other. mathlib packages "same direction" as {name}`SameRay` over {lit}`ℝ`. We state
it for real inner product spaces, where {lit}`Re ⟨u, v⟩ = ⟨u, v⟩`. Following the
book, equality holds iff both inequalities in the proof above are equalities,
i.e. iff {lit}`⟨u, v⟩ = ‖u‖‖v‖`; by the equality case of Cauchy–Schwarz that
happens iff one vector is a multiple of the other, and the multiple must then be
nonnegative. -/
@[avoiding sameRay_iff_norm_add]
theorem triangle_inequality_eq_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (u v : V) :
    ‖u + v‖ = ‖u‖ + ‖v‖ ↔ SameRay ℝ u v := by
  -- `‖u + v‖ = ‖u‖ + ‖v‖` iff `⟨u, v⟩ = ‖u‖‖v‖`
  have hexp := norm_add_sq_expand (𝕜 := ℝ) u v
  rw [RCLike.re_to_real] at hexp
  have h618 : ‖u + v‖ = ‖u‖ + ‖v‖ ↔ ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖ := by
    rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, hexp]
    constructor <;> intro h <;> linarith
  rw [h618]
  constructor
  · intro h
    -- equality in Cauchy–Schwarz, so one vector is a multiple of the other
    have hcs : ‖⟪u, v⟫_ℝ‖ = ‖u‖ * ‖v‖ := by
      rw [h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    obtain ⟨r, hr | hr⟩ := (cauchy_schwarz_eq_iff (𝕜 := ℝ)).mp hcs
    · -- `v = ru`: then `r‖u‖² = |r|‖u‖²`, so `r ≥ 0` (or `u = 0`)
      rcases eq_or_ne u 0 with hu | hu
      · rw [hu]; exact SameRay.zero_left v
      subst hr
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
        Real.norm_eq_abs] at h
      have hu2 : 0 < ‖u‖ ^ 2 := by positivity
      have hr0 : 0 ≤ r := by
        have : r = |r| := by nlinarith
        rw [this]; exact abs_nonneg r
      exact SameRay.sameRay_nonneg_smul_right u hr0
    · -- `u = rv`: symmetric
      rcases eq_or_ne v 0 with hv | hv
      · rw [hv]; exact SameRay.zero_right u
      subst hr
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul,
        Real.norm_eq_abs] at h
      have hv2 : 0 < ‖v‖ ^ 2 := by positivity
      have hr0 : 0 ≤ r := by
        have : r = |r| := by nlinarith
        rw [this]; exact abs_nonneg r
      exact SameRay.sameRay_nonneg_smul_left v hr0
  · intro h
    -- conversely, if `v = ru` with `r > 0`, then `⟨u, v⟩ = r‖u‖² = ‖u‖‖v‖`
    rcases eq_or_ne u 0 with hu | hu
    · rw [hu, inner_zero_left, norm_zero, zero_mul]
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv, inner_zero_right, norm_zero, mul_zero]
    obtain ⟨r, hr, rfl⟩ := h.exists_pos_left hu hv
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    ring

/-! 6.21 Parallelogram equality

{lit}`‖u + v‖² + ‖u − v‖² = 2(‖u‖² + ‖v‖²)`. -/

@[avoiding parallelogram_law_with_norm]
theorem parallelogram {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] (u v : V) :
    ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  -- expand `⟨u + v, u + v⟩ + ⟨u − v, u − v⟩`; the cross terms cancel
  rw [norm_add_sq_expand (𝕜 := 𝕜), norm_sub_sq_expand (𝕜 := 𝕜)]
  ring

/-! # Exercises 6A -/

/-- 6A.1 Prove or give a counterexample: if {lit}`v₁, …, vₘ ∈ V`, then
{lit}`∑ⱼ ∑ₖ ⟨vⱼ, vₖ⟩ ≥ 0`. -/
def exercise_6A_1 {m : ℕ} (v : Fin m → V) :
    Decidable (0 ≤ RCLike.re (∑ j, ∑ k, ⟪v j, v k⟫_𝕜)) := by
  sorry

/-- 6A.2 For {lit}`S ∈ ℒ(V)`, the form {lit}`(u, v) ↦ ⟨Su, Sv⟩` is an inner
product on {lit}`V` if and only if {lit}`S` is injective. Additivity and
homogeneity in the first slot, conjugate symmetry, and positivity hold for every
{lit}`S` (inherited from the inner product on {lit}`V` by linearity of {lit}`S`);
the definiteness axiom is the one that characterizes injectivity. -/
theorem exercise_6A_2 (S : V →ₗ[𝕜] V) :
    ((∀ u v w : V, ⟪S (u + v), S w⟫_𝕜 = ⟪S u, S w⟫_𝕜 + ⟪S v, S w⟫_𝕜) ∧
      (∀ (r : 𝕜) (u v : V), ⟪S (r • u), S v⟫_𝕜 = conj r * ⟪S u, S v⟫_𝕜) ∧
      (∀ u v : V, ⟪S u, S v⟫_𝕜 = conj ⟪S v, S u⟫_𝕜) ∧
      (∀ v : V, 0 ≤ RCLike.re ⟪S v, S v⟫_𝕜) ∧
      (∀ v : V, ⟪S v, S v⟫_𝕜 = 0 → v = 0)) ↔ Function.Injective S := by
  sorry

/-- The five axioms defining a real inner product on {lit}`Fin n → ℝ` (additivity
and homogeneity in the first slot, symmetry, positivity, definiteness); used to
state that a given form fails to be an inner product. -/
def IsRealInnerProduct {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ) → ℝ) : Prop :=
  (∀ u v w : Fin n → ℝ, f (u + v) w = f u w + f v w) ∧
  (∀ (r : ℝ) (u v : Fin n → ℝ), f (r • u) v = r * f u v) ∧
  (∀ u v : Fin n → ℝ, f u v = f v u) ∧
  (∀ v : Fin n → ℝ, 0 ≤ f v v) ∧
  (∀ v : Fin n → ℝ, f v v = 0 → v = 0)

/-- The five axioms characterizing an inner product {lit}`f` on a {lit}`𝕜`-module
{lit}`M`, in mathlib's convention (additivity and conjugate homogeneity in the
first slot, conjugate symmetry, positivity, definiteness). Over {lit}`ℝ` the
conjugation and real-part maps are the identity. -/
def IsInnerProductForm {𝕜 : Type*} [RCLike 𝕜] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] (f : M → M → 𝕜) : Prop :=
  (∀ u v w : M, f (u + v) w = f u w + f v w) ∧
  (∀ (r : 𝕜) (u v : M), f (r • u) v = conj r * f u v) ∧
  (∀ u v : M, f u v = conj (f v u)) ∧
  (∀ v : M, 0 ≤ RCLike.re (f v v)) ∧
  (∀ v : M, f v v = 0 → v = 0)

/-- 6A.3 (a) The function {lit}`((x₁,x₂),(y₁,y₂)) ↦ |x₁y₁| + |x₂y₂|` is not an inner
product on {lit}`ℝ²`: the absolute values break additivity and homogeneity in the
first slot. -/
theorem exercise_6A_3a :
    ¬ IsRealInnerProduct (fun x y : Fin 2 → ℝ => |x 0 * y 0| + |x 1 * y 1|) := by
  sorry

/-- 6A.3 (b) The function {lit}`((x₁,x₂,x₃),(y₁,y₂,y₃)) ↦ x₁y₁ + x₃y₃` is not an
inner product on {lit}`ℝ³`: it fails definiteness, vanishing on the nonzero vector
{lit}`(0, 1, 0)`. -/
theorem exercise_6A_3b :
    ¬ IsRealInnerProduct (fun x y : Fin 3 → ℝ => x 0 * y 0 + x 2 * y 2) := by
  sorry

/-- 6A.4 If {lit}`T ∈ ℒ(V)` satisfies {lit}`‖Tv‖ ≤ ‖v‖` for every {lit}`v`, then
{lit}`T − √2 I` is injective. -/
theorem exercise_6A_4 (T : V →ₗ[𝕜] V) (h : ∀ v : V, ‖T v‖ ≤ ‖v‖) :
    Function.Injective (T - (Real.sqrt 2 : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) := by
  sorry

/-- 6A.5 (a) In a real inner product space, {lit}`⟨u + v, u − v⟩ = ‖u‖² − ‖v‖²`. -/
theorem exercise_6A_5a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) : ⟪u + v, u - v⟫_ℝ = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  sorry

/-- 6A.5 (b) If {lit}`u, v` have the same norm, then {lit}`u + v` is orthogonal to
{lit}`u − v`. -/
theorem exercise_6A_5b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (h : ‖u‖ = ‖v‖) : Orthogonal (𝕜 := ℝ) (u + v) (u - v) := by
  sorry

/-- 6A.6 {lit}`⟨u, v⟩ = 0` if and only if {lit}`‖u‖ ≤ ‖u + av‖` for all {lit}`a`. -/
theorem exercise_6A_6 (u v : V) :
    ⟪u, v⟫_𝕜 = 0 ↔ ∀ a : 𝕜, ‖u‖ ≤ ‖u + a • v‖ := by
  sorry

/-- 6A.7 {lit}`‖au + bv‖ = ‖bu + av‖` for all real {lit}`a, b` if and only if
{lit}`‖u‖ = ‖v‖`. -/
theorem exercise_6A_7 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) :
    (∀ a b : ℝ, ‖a • u + b • v‖ = ‖b • u + a • v‖) ↔ ‖u‖ = ‖v‖ := by
  sorry

/-- 6A.8 If {lit}`a² + b² + c² + x² + y² ≤ 1`, then
{lit}`a + b + c + 4x + 9y ≤ 10`. -/
theorem exercise_6A_8 (a b c x y : ℝ) (h : a^2 + b^2 + c^2 + x^2 + y^2 ≤ 1) :
    a + b + c + 4*x + 9*y ≤ 10 := by
  sorry

/-- 6A.9 If {lit}`‖u‖ = ‖v‖ = 1` and {lit}`⟨u, v⟩ = 1`, then {lit}`u = v`. -/
theorem exercise_6A_9 (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_𝕜 = 1) :
    u = v := by
  sorry

/-- 6A.10 If {lit}`‖u‖ ≤ 1` and {lit}`‖v‖ ≤ 1`, then
{lit}`√(1 − ‖u‖²) √(1 − ‖v‖²) ≤ 1 − |⟨u, v⟩|`. -/
theorem exercise_6A_10 (u v : V) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    Real.sqrt (1 - ‖u‖ ^ 2) * Real.sqrt (1 - ‖v‖ ^ 2) ≤ 1 - ‖⟪u, v⟫_𝕜‖ := by
  sorry

/-- 6A.11 Find {lit}`u, v ∈ ℝ²` such that {lit}`u` is a scalar multiple of
{lit}`(1, 3)`, {lit}`v` is orthogonal to {lit}`(1, 3)`, and {lit}`(1, 2) = u + v`. -/
theorem exercise_6A_11 :
    ∃ u v : EuclideanSpace ℝ (Fin 2),
      (∃ c : ℝ, u = c • (!₂[1, 3] : EuclideanSpace ℝ (Fin 2))) ∧
      Orthogonal (𝕜 := ℝ) v (!₂[1, 3] : EuclideanSpace ℝ (Fin 2)) ∧
      (!₂[1, 2] : EuclideanSpace ℝ (Fin 2)) = u + v := by
  sorry

/-- 6A.12 (a) For positive {lit}`a, b, c, d`,
{lit}`(a + b + c + d)(1/a + 1/b + 1/c + 1/d) ≥ 16`. -/
theorem exercise_6A_12a (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) : 16 ≤ (a + b + c + d) * (1/a + 1/b + 1/c + 1/d) := by
  sorry

/-- 6A.12 (b) The inequality in (a) is an equality if and only if
{lit}`a = b = c = d`. -/
theorem exercise_6A_12b (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    (a + b + c + d) * (1/a + 1/b + 1/c + 1/d) = 16 ↔ a = b ∧ b = c ∧ c = d := by
  sorry

/-- 6A.13 The square of an average is at most the average of the squares. -/
theorem exercise_6A_13 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ((∑ i, a i) / n) ^ 2 ≤ (∑ i, (a i) ^ 2) / n := by
  sorry

/-- 6A.14 For {lit}`v ≠ 0`, {lit}`v/‖v‖` is the unique closest element on the unit
sphere to {lit}`v`: for every unit vector {lit}`u`,
{lit}`‖v − v/‖v‖‖ ≤ ‖v − u‖`, with equality if and only if {lit}`u = v/‖v‖`. -/
theorem exercise_6A_14 (v : V) (hv : v ≠ 0) (u : V) (hu : ‖u‖ = 1) :
    ‖v - (‖v‖⁻¹ : 𝕜) • v‖ ≤ ‖v - u‖ ∧
      (‖v - (‖v‖⁻¹ : 𝕜) • v‖ = ‖v - u‖ ↔ u = (‖v‖⁻¹ : 𝕜) • v) := by
  sorry

-- 6A.15 and 16 not formalizable, need geometry.

/-- 6A.17 {lit}`(∑ₖ aₖbₖ)² ≤ (∑ₖ k aₖ²)(∑ₖ bₖ²/k)` for reals. -/
theorem exercise_6A_17 {n : ℕ} (a b : Fin n → ℝ) :
    (∑ k : Fin n, a k * b k) ^ 2 ≤
      (∑ k : Fin n, ((k : ℝ) + 1) * a k ^ 2) *
        (∑ k : Fin n, b k ^ 2 / ((k : ℝ) + 1)) := by
  sorry

section
open MeasureTheory

/-- 6A.18 (a) For continuous {lit}`f : [1, ∞) → [0, ∞)`,
{lit}`(∫₁^∞ f)² ≤ ∫₁^∞ x² f(x)² dx`. -/
theorem exercise_6A_18a (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x in Set.Ici (1:ℝ), f x) ^ 2 ≤ ∫ x in Set.Ici (1:ℝ), x ^ 2 * f x ^ 2 := by
  sorry

/-- 6A.18 (b) The inequality in (a) is an equality with both sides finite if and
only if {lit}`f(x) = c/x²` for some constant {lit}`c ≥ 0` (the Cauchy–Schwarz
equality case, where {lit}`x f(x)` is proportional to {lit}`1/x`). -/
theorem exercise_6A_18b (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    (IntegrableOn f (Set.Ici (1:ℝ)) ∧
      IntegrableOn (fun x => x ^ 2 * f x ^ 2) (Set.Ici (1:ℝ)) ∧
      (∫ x in Set.Ici (1:ℝ), f x) ^ 2 = ∫ x in Set.Ici (1:ℝ), x ^ 2 * f x ^ 2) ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x ≥ (1:ℝ), f x = c / x ^ 2 := by
  sorry

end

/-- 6A.19 If {lit}`v₁, …, vₙ` is a basis of {lit}`V`, {lit}`T ∈ ℒ(V)`, and
{lit}`λ` is an eigenvalue of {lit}`T`, then {lit}`|λ|² ≤ ∑ⱼ ∑ₖ |ℳ(T)ⱼ,ₖ|²`. -/
theorem exercise_6A_19 {n : ℕ} (b : Module.Basis (Fin n) 𝕜 V) (T : V →ₗ[𝕜] V)
    (lam : 𝕜) (h : ∃ v : V, v ≠ 0 ∧ T v = lam • v) :
    ‖lam‖ ^ 2 ≤ ∑ j, ∑ k, ‖LinearMap.toMatrix b b T j k‖ ^ 2 := by
  sorry

/-- 6A.20 Reverse triangle inequality: {lit}`| ‖u‖ − ‖v‖ | ≤ ‖u − v‖`. -/
@[avoiding abs_norm_sub_norm_le, norm_sub_norm_le]
theorem exercise_6A_20 (u v : V) : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := by
  sorry

/-- 6A.21 If {lit}`‖u‖ = 3`, {lit}`‖u + v‖ = 4`, {lit}`‖u − v‖ = 6`, find
{lit}`‖v‖`. Fill in the first sorry with a concrete value and then prove. -/
theorem exercise_6A_21 (u v : V) (h1 : ‖u‖ = 3) (h2 : ‖u + v‖ = 4)
    (h3 : ‖u - v‖ = 6) : ‖v‖ = sorry := by
  sorry

/-- 6A.22 {lit}`‖u + v‖ ‖u − v‖ ≤ ‖u‖² + ‖v‖²`. -/
theorem exercise_6A_22 (u v : V) : ‖u + v‖ * ‖u - v‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  sorry

/-- 6A.23 If {lit}`‖vₖ‖ ≤ 1` for each {lit}`k`, then there exist signs
{lit}`aₖ ∈ {1, −1}` with {lit}`‖a₁v₁ + ⋯ + aₘvₘ‖ ≤ √m`. -/
theorem exercise_6A_23 {m : ℕ} (v : Fin m → V) (h : ∀ k, ‖v k‖ ≤ 1) :
    ∃ a : Fin m → 𝕜, (∀ k, a k = 1 ∨ a k = -1) ∧
      ‖∑ k, a k • v k‖ ≤ Real.sqrt m := by
  sorry

/-- 6A.24 Prove or give a counterexample: if {lit}`‖·‖` is the norm from an inner
product on {lit}`ℝ²`, then there is {lit}`(x, y)` with
{lit}`‖(x, y)‖ ≠ max{|x|, |y|}`. -/
def exercise_6A_24 :
    Decidable (∃ x y : ℝ, ‖(!₂[x, y] : EuclideanSpace ℝ (Fin 2))‖ ≠ max |x| |y|) := by
  sorry

/-- 6A.25 For {lit}`p > 0`, there is an inner product on {lit}`ℝ²` whose associated
norm is {lit}`‖(x, y)‖ = (|x|ᵖ + |y|ᵖ)^(1/p)` if and only if {lit}`p = 2` (the
parallelogram equality holds for this norm exactly when {lit}`p = 2`). -/
theorem exercise_6A_25 (p : ℝ) (hp : 0 < p) :
    (∃ f : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ, IsRealInnerProduct f ∧
      ∀ v : Fin 2 → ℝ, Real.sqrt (f v v) = (|v 0| ^ p + |v 1| ^ p) ^ (1 / p)) ↔ p = 2 := by
  sorry

/-- 6A.26 In a real inner product space,
{lit}`⟨u, v⟩ = (‖u + v‖² − ‖u − v‖²)/4`. -/
theorem exercise_6A_26 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) : ⟪u, v⟫_ℝ = (‖u + v‖ ^ 2 - ‖u - v‖ ^ 2) / 4 := by
  sorry

/-- 6A.27 In a complex inner product space, the complex polarization identity
{lit}`⟨u, v⟩ = (‖u+v‖² − ‖u−v‖² + ‖u+iv‖²i − ‖u−iv‖²i)/4`. Axler's {lit}`⟨u, v⟩` is
mathlib's {lit}`⟪v, u⟫` (the conjugate sits in the first slot), so the identity is
stated for {lit}`⟪v, u⟫_ℂ`. -/
theorem exercise_6A_27 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (u v : V) :
    ⟪v, u⟫_ℂ = (((‖u + v‖ ^ 2 : ℝ) : ℂ) - ((‖u - v‖ ^ 2 : ℝ) : ℂ)
      + ((‖u + Complex.I • v‖ ^ 2 : ℝ) : ℂ) * Complex.I
      - ((‖u - Complex.I • v‖ ^ 2 : ℝ) : ℂ) * Complex.I) / 4 := by
  sorry

/-- 6A.28 A norm satisfying the parallelogram equality comes from an inner product
(Jordan–von Neumann): if the norm on a real vector space {lit}`U` satisfies
{lit}`‖u+v‖² + ‖u−v‖² = 2‖u‖² + 2‖v‖²`, then there is an inner product {lit}`f` on
{lit}`U` — additive, homogeneous, and symmetric, with {lit}`f v v > 0` for
{lit}`v ≠ 0` — whose associated norm is {lit}`‖u‖ = √(f u u)`. -/
theorem exercise_6A_28 {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (hpar : ∀ u v : U, ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) :
    ∃ f : U → U → ℝ, IsInnerProductForm f ∧ ∀ u, ‖u‖ = Real.sqrt (f u u) := by
  sorry

/-- 6A.29 If {lit}`V₁, …, Vₘ` are inner product spaces, then
{lit}`⟨(u₁, …), (v₁, …)⟩ = ⟨u₁, v₁⟩ + ⋯ + ⟨uₘ, vₘ⟩` defines an inner product on the
product {lit}`V₁ × ⋯ × Vₘ`. The exercise is to verify the inner-product axioms for
this form: additivity and conjugate homogeneity in the first slot, conjugate
symmetry, positivity, and definiteness. -/
theorem exercise_6A_29 {m : ℕ} (E : Fin m → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)] :
    IsInnerProductForm (fun u v : ∀ i, E i => ∑ i, ⟪u i, v i⟫_𝕜) := by
  sorry

/-- 6A.30 The complexification {lit}`V_ℂ` of a real inner product space {lit}`V`,
modeled as {lit}`V × V` with {lit}`(u, v)` standing for {lit}`u + iv`, carries the
inner product {lit}`⟨u+iv, w+ix⟩ = ⟨u,w⟩ + ⟨v,x⟩ + (⟨v,w⟩ − ⟨u,x⟩)i`. -/
noncomputable def complexificationInner {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (p q : V × V) : ℂ :=
  (⟪p.1, q.1⟫_ℝ : ℂ) + (⟪p.2, q.2⟫_ℝ : ℂ)
    + ((⟪p.2, q.1⟫_ℝ : ℂ) - (⟪p.1, q.2⟫_ℝ : ℂ)) * Complex.I

/-- The complex scalar action on {lit}`V_ℂ = V × V`: {lit}`c • (u, v)` represents
{lit}`c (u + iv) = (c.re · u − c.im · v) + i (c.im · u + c.re · v)`. -/
def complexificationSmul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : ℂ) (p : V × V) : V × V :=
  (c.re • p.1 - c.im • p.2, c.im • p.1 + c.re • p.2)

/-- 6A.30 (a) The form above makes {lit}`V_ℂ` a complex inner product space (in
Axler's convention — linear in the first slot): it is additive, homogeneous under
the complex action, conjugate symmetric, positive, and definite. -/
theorem exercise_6A_30a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    (∀ p q r : V × V, complexificationInner (p + q) r
        = complexificationInner p r + complexificationInner q r) ∧
      (∀ (c : ℂ) (p q : V × V), complexificationInner (complexificationSmul c p) q
        = c * complexificationInner p q) ∧
      (∀ p q : V × V, complexificationInner p q = conj (complexificationInner q p)) ∧
      (∀ p : V × V, 0 ≤ (complexificationInner p p).re) ∧
      (∀ p : V × V, complexificationInner p p = 0 → p = 0) := by
  sorry

/-- 6A.30 (b) For {lit}`u, v ∈ V`, the complexification inner product restricts to
the original {lit}`⟨u, v⟩` on {lit}`V` (embedded as {lit}`(u, 0)`), and
{lit}`‖u + iv‖² = ‖u‖² + ‖v‖²`. -/
theorem exercise_6A_30b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) :
    complexificationInner (u, 0) (v, 0) = (⟪u, v⟫_ℝ : ℂ) ∧
      complexificationInner (u, v) (u, v) = ((‖u‖ ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ) := by
  sorry

/-- 6A.31 For {lit}`u, v, w ∈ V`,
{lit}`‖w − ½(u+v)‖² = (‖w−u‖² + ‖w−v‖²)/2 − ‖u−v‖²/4`. -/
theorem exercise_6A_31 (u v w : V) :
    ‖w - (2 : 𝕜)⁻¹ • (u + v)‖ ^ 2
      = (‖w - u‖ ^ 2 + ‖w - v‖ ^ 2) / 2 - ‖u - v‖ ^ 2 / 4 := by
  sorry

/-- 6A.32 If {lit}`E ⊆ V` is closed under midpoints ({lit}`u, v ∈ E ⟹ ½(u+v) ∈ E`),
then for any {lit}`w` there is at most one point of {lit}`E` closest to {lit}`w`. -/
theorem exercise_6A_32 (E : Set V)
    (hE : ∀ u ∈ E, ∀ v ∈ E, (2 : 𝕜)⁻¹ • (u + v) ∈ E) (w : V) :
    ∀ u₁ ∈ E, ∀ u₂ ∈ E, (∀ x ∈ E, ‖w - u₁‖ ≤ ‖w - x‖) →
      (∀ x ∈ E, ‖w - u₂‖ ≤ ‖w - x‖) → u₁ = u₂ := by
  sorry

/-- 6A.33 (a) For differentiable {lit}`f, g : ℝ → ℝⁿ`, the product rule for the
inner product: {lit}`⟨f, g⟩′ = ⟨f′, g⟩ + ⟨f, g′⟩`. -/
theorem exercise_6A_33a {n : ℕ} (f g : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    deriv (fun s => ⟪f s, g s⟫_ℝ) t = ⟪deriv f t, g t⟫_ℝ + ⟪f t, deriv g t⟫_ℝ := by
  sorry

/-- 6A.33 (b) If {lit}`f : ℝ → ℝⁿ` is differentiable with constant norm
{lit}`‖f(t)‖ = c`, then {lit}`⟨f′(t), f(t)⟩ = 0` for every {lit}`t`. -/
theorem exercise_6A_33b {n : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin n))
    (hf : ∀ t, DifferentiableAt ℝ f t) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ t, ‖f t‖ = c) (t : ℝ) :
    ⟪deriv f t, f t⟫_ℝ = 0 := by
  sorry

/-- 6A.34 Apollonius's identity. For a triangle with a vertex at {lit}`0` and the
other two at {lit}`u, v` — sides {lit}`a = ‖v‖`, {lit}`b = ‖u‖`, {lit}`c = ‖u−v‖`,
and median {lit}`d = ‖½(u+v)‖` to side {lit}`c` — one has
{lit}`a² + b² = ½c² + 2d²`. -/
theorem exercise_6A_34 (u v : V) :
    ‖v‖ ^ 2 + ‖u‖ ^ 2
      = (1 / 2) * ‖u - v‖ ^ 2 + 2 * ‖(2 : 𝕜)⁻¹ • (u + v)‖ ^ 2 := by
  sorry

/-- 6A.35 Every polynomial {lit}`q` on {lit}`ℝⁿ` agrees on the unit sphere with a
harmonic polynomial {lit}`p` (one whose Laplacian {lit}`∑ᵢ ∂²p/∂xᵢ²` vanishes). -/
theorem exercise_6A_35 {n : ℕ} (q : MvPolynomial (Fin n) ℝ) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      (∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i p) = 0) ∧
      (∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 →
        MvPolynomial.eval x p = MvPolynomial.eval x q) := by
  sorry

end LADR.Section_6A
