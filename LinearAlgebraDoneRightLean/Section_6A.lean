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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import LinearAlgebraDoneRightLean.Section_1B
import LinearAlgebraDoneRightLean.HarmonicPolynomial
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
open LADR.Section_1B (Complexification exercise_1B_8)

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
  apply isTrue
  -- use linearity to show ∑ j, ∑ k, ⟪v j, v k⟫ = ⟪∑ j, v j, ∑ k, v k⟫
  have hlin : ∑ j, ∑ k, ⟪v j, v k⟫_𝕜 = ⟪∑ j, v j, ∑ k, v k⟫_𝕜 := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
  -- equal to |∑ j, v j|² thus ≥ 0
  rw [hlin, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  exact sq_nonneg _

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
      (∀ v : V, ⟪S v, S v⟫_𝕜 = 0 ↔ v = 0)) ↔ Function.Injective S := by
  constructor
  · rintro ⟨-, -, -, -, hdef⟩
    -- conversely, if ⟨S v , S v⟩ = 0 implies v = 0, and we assume S v = 0
    -- then ⟪S v, S v⟫_𝕜 = 0, so v = 0, showing injectivity.
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact (hdef v).mp (by rw [hv, inner_zero_left])
  · intro hinj
    -- linearity is trivial from the linearity the inner product
    refine ⟨fun u v w => by rw [map_add, inner_add_left],
      fun r u v => by rw [map_smul, inner_smul_left], ?_, ?_, ?_⟩
    -- same as symmetry of the inner product and non-negativity of the inner product.
    · exact fun u v => (inner_conj_symm _ _).symm
    · exact fun v => inner_self_nonneg
    -- only thing left is definiteness
    -- If S is injective, and v ≠ 0, S v ≠ 0, so ⟪S v, S v⟫_𝕜 ≠ 0, satisfying definiteness.
    · intro v
      constructor
      · intro h
        exact hinj (by rw [inner_self_eq_zero.mp h, map_zero])
      · intro h
        rw [h, map_zero, inner_zero_left]

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
first slot, conjugate symmetry, positivity, definiteness). Positivity
{lit}`⟨v, v⟩ ≥ 0` means, as in the book, that {lit}`⟨v, v⟩` is real and nonnegative.
Over {lit}`ℝ` the conjugation and real-part maps are the identity. -/
def IsInnerProductForm {𝕜 : Type*} [RCLike 𝕜] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] (f : M → M → 𝕜) : Prop :=
  (∀ u v w : M, f (u + v) w = f u w + f v w) ∧
  (∀ (r : 𝕜) (u v : M), f (r • u) v = conj r * f u v) ∧
  (∀ u v : M, f u v = conj (f v u)) ∧
  (∀ v : M, RCLike.im (f v v) = 0 ∧ 0 ≤ RCLike.re (f v v)) ∧
  (∀ v : M, f v v = 0 ↔ v = 0)

/-- 6A.3 (a) The function {lit}`((x₁,x₂),(y₁,y₂)) ↦ |x₁y₁| + |x₂y₂|` is not an inner
product on {lit}`ℝ²`: the absolute values break additivity and homogeneity in the
first slot. -/
theorem exercise_6A_3a :
    ¬ IsRealInnerProduct (fun x y : Fin 2 → ℝ => |x 0 * y 0| + |x 1 * y 1|) := by
  -- fails linearity with (-1, 0) and (1, 0)
  -- ⟨(-1, 0), (1, 0)⟩ = 1
  -- ⟨(1, 0), (1, 0)⟩ = 1
  -- ⟨(-1, 0) + (1, 0), (1, 0)⟩ = ⟨(0, 0), (1, 0)⟩ = 0
  rintro ⟨hadd, -, -, -, -⟩
  have h := hadd ![-1, 0] ![1, 0] ![1, 0]
  norm_num at h

/-- 6A.3 (b) The function {lit}`((x₁,x₂,x₃),(y₁,y₂,y₃)) ↦ x₁y₁ + x₃y₃` is not an
inner product on {lit}`ℝ³`: it fails definiteness, vanishing on the nonzero vector
{lit}`(0, 1, 0)`. -/
theorem exercise_6A_3b :
    ¬ IsRealInnerProduct (fun x y : Fin 3 → ℝ => x 0 * y 0 + x 2 * y 2) := by
  -- fails definteness with (0, 1, 0)
  rintro ⟨-, -, -, -, hdef⟩
  have h := congrFun (hdef ![0, 1, 0] (by simp)) 1
  simp at h

/-- 6A.4 If {lit}`T ∈ ℒ(V)` satisfies {lit}`‖Tv‖ ≤ ‖v‖` for every {lit}`v`, then
{lit}`T − √2 I` is injective. -/
theorem exercise_6A_4 (T : V →ₗ[𝕜] V) (h : ∀ v : V, ‖T v‖ ≤ ‖v‖) :
    Function.Injective (T - (Real.sqrt 2 : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) := by
  -- by contra, if not inj, exits v, s.t Tv = √2 v
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hv0
  have hTv : T v = (Real.sqrt 2 : 𝕜) • v := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hv
    exact hv
  -- then ||Tv|| = √2 ||v|| > ||v||, contradicting the assumption
  have hle := h v
  rw [hTv, norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg 2)] at hle
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hsqrt : 1 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  nlinarith

/-- 6A.5 (a) In a real inner product space, {lit}`⟨u + v, u − v⟩ = ‖u‖² − ‖v‖²`. -/
theorem exercise_6A_5a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) : ⟪u + v, u - v⟫_ℝ = ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
  -- expand ⟪u + v, u - v⟫ = ⟪u, u⟫ - ⟪u, v⟫ + ⟪v, u⟫ - ⟪v, v⟫
  rw [inner_add_left, inner_sub_right, inner_sub_right]
  -- (in real inner product space, ⟪v, u⟫ = ⟪u, v⟫) so ⟪u + v, u - v⟫ = ⟪u, u⟫ - ⟪v, v⟫ = ‖u‖² - ‖v‖²
  rw [real_inner_comm u v, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- 6A.5 (b) If {lit}`u, v` have the same norm, then {lit}`u + v` is orthogonal to
{lit}`u − v`. -/
theorem exercise_6A_5b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (h : ‖u‖ = ‖v‖) : Orthogonal (𝕜 := ℝ) (u + v) (u - v) := by
  -- trivial from a
  unfold Orthogonal
  rw [exercise_6A_5a, h, sub_self]

/-- 6A.6 {lit}`⟨u, v⟩ = 0` if and only if {lit}`‖u‖ ≤ ‖u + av‖` for all {lit}`a`. -/
theorem exercise_6A_6 (u v : V) :
    ⟪u, v⟫_𝕜 = 0 ↔ ∀ a : 𝕜, ‖u‖ ≤ ‖u + a • v‖ := by
  -- ||u + a v||^2 = ⟪u + a v, u + a v⟫ = ⟪u, u⟫ + a⟪u, v⟫ + a⟪v, u⟫ + a^2⟪v, v⟫ = ‖u‖^2 + 2 Re(a⟪u, v⟫) + |a|^2 ‖v‖^2
  constructor
  -- If ⟪u, v⟫ = 0, then ||u + a v||^2 = ‖u‖^2 + |a|^2 ‖v‖^2 ≥ ‖u‖^2, so ||u|| ≤ ||u + a v|| for all a.
  · intro huv a
    have horth : Orthogonal (𝕜 := 𝕜) u (a • v) := by
      unfold Orthogonal; rw [inner_smul_right, huv, mul_zero]
    have hpyth := pythagorean u (a • v) horth
    have hsq : ‖u‖ ^ 2 ≤ ‖u + a • v‖ ^ 2 := by rw [hpyth]; nlinarith [sq_nonneg ‖a • v‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
  · intro h
    rcases eq_or_ne v 0 with hv | hv
    · rw [hv, inner_zero_right]
    -- for the other direction, take a = -⟨u,v⟩/ ‖v‖^2
    -- by theorem (6.13) u + av is the component w of u orthogonal to v, u = c v + w with a = -c
    obtain ⟨c, w, hu, hw⟩ := orthogonal_decomposition (𝕜 := 𝕜) u v hv
    have hw_eq : u + (-c) • v = w := by rw [hu]; module
    -- by Pythagorean ‖u‖² = ‖c v‖² + ‖w‖², so always ‖w‖ ≤ ‖u‖; with ‖u‖ ≤ ‖w‖ this
    -- forces ‖c v‖ = 0
    have hcvw : Orthogonal (𝕜 := 𝕜) (c • v) w := by
      unfold Orthogonal at hw ⊢; rw [inner_smul_left, hw, mul_zero]
    have hpyth : ‖u‖ ^ 2 = ‖c • v‖ ^ 2 + ‖w‖ ^ 2 := by rw [hu, pythagorean _ _ hcvw]
    have hle := h (-c)
    rw [hw_eq] at hle
    have hcv : ‖c • v‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖c • v‖, norm_nonneg u, norm_nonneg w]
    have hc : c = 0 := by
      have : c • v = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hcv)
      exact (smul_eq_zero.mp this).resolve_right hv
    -- it needs to be ≤ ‖u‖, which forces ⟪u, v⟫ = 0
    rw [hu, hc, zero_smul, zero_add]
    exact (orthogonal_comm v w).mp hw

/-- 6A.7 {lit}`‖au + bv‖ = ‖bu + av‖` for all real {lit}`a, b` if and only if
{lit}`‖u‖ = ‖v‖`. -/
theorem exercise_6A_7 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) :
    (∀ a b : ℝ, ‖a • u + b • v‖ = ‖b • u + a • v‖) ↔ ‖u‖ = ‖v‖ := by
  constructor
  -- => pick a = 0, b = 1
  · intro h
    have h01 := h 0 1
    simp only [zero_smul, one_smul, zero_add, add_zero] at h01
    exact h01.symm
  -- <= ‖a • u + b • v‖ ^ 2 = ⟨a • u + b • v, a • u + b • v⟩ =
  -- = a^2 ‖u‖^2 + 2ab ⟪u, v⟫ + b^2 ‖v‖^2 = b^2 ‖u‖^2 + 2ab ⟪u, v⟫ + a^2 ‖v‖^2
  -- = ⟨b • u + a • v, b • u + a • v⟩ = ‖b • u + a • v‖^2
  · intro h a b
    have e1 := norm_add_sq_expand (𝕜 := ℝ) (a • u) (b • v)
    have e2 := norm_add_sq_expand (𝕜 := ℝ) (b • u) (a • v)
    simp only [RCLike.re_to_real, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, mul_pow, sq_abs] at e1 e2
    rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, e1, e2, h]
    ring

/-- Cauchy–Schwarz for {lit}`ℝⁿ` written in coordinates (6.16(a)), for functions
{lit}`Fin n → ℝ`: {lit}`(∑ xᵢyᵢ)² ≤ (∑ xᵢ²)(∑ yᵢ²)`. -/
private theorem sum_mul_sq_le {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i, x i * y i) ^ 2 ≤ (∑ i, x i ^ 2) * (∑ i, y i ^ 2) := by
  set X : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  set Y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hXY : ⟪X, Y⟫_ℝ = ∑ i, x i * y i := by
    rw [PiLp.inner_apply]; congr 1; ext i; exact real_inner_comm (y i) (x i) ▸ rfl
  have hXX : ‖X‖ ^ 2 = ∑ i, x i ^ 2 := by simp [X, EuclideanSpace.norm_sq_eq]
  have hYY : ‖Y‖ ^ 2 = ∑ i, y i ^ 2 := by simp [Y, EuclideanSpace.norm_sq_eq]
  have hcs := pow_le_pow_left₀ (norm_nonneg _) (cauchy_schwarz (𝕜 := ℝ) X Y) 2
  rwa [mul_pow, hXX, hYY, hXY, Real.norm_eq_abs, sq_abs] at hcs

/-- …with equality only when one vector is a multiple of the other (6.14). -/
private theorem sum_mul_sq_eq {n : ℕ} (x y : Fin n → ℝ)
    (h : (∑ i, x i * y i) ^ 2 = (∑ i, x i ^ 2) * (∑ i, y i ^ 2)) :
    ∃ r : ℝ, y = r • x ∨ x = r • y := by
  set X : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  set Y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hXY : ⟪X, Y⟫_ℝ = ∑ i, x i * y i := by
    rw [PiLp.inner_apply]; congr 1; ext i; exact real_inner_comm (y i) (x i) ▸ rfl
  have hXX : ‖X‖ ^ 2 = ∑ i, x i ^ 2 := by simp [X, EuclideanSpace.norm_sq_eq]
  have hYY : ‖Y‖ ^ 2 = ∑ i, y i ^ 2 := by simp [Y, EuclideanSpace.norm_sq_eq]
  have heq : ‖⟪X, Y⟫_ℝ‖ = ‖X‖ * ‖Y‖ := by
    rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow, hXX, hYY, hXY,
      Real.norm_eq_abs, sq_abs, h]
  obtain ⟨r, hr | hr⟩ := cauchy_schwarz_eq_iff.mp heq
  · exact ⟨r, Or.inl (by simpa [X, Y] using congrArg WithLp.ofLp hr)⟩
  · exact ⟨r, Or.inr (by simpa [X, Y] using congrArg WithLp.ofLp hr)⟩

/-- 6A.8 If {lit}`a² + b² + c² + x² + y² ≤ 1`, then
{lit}`a + b + c + 4x + 9y ≤ 10`. -/
theorem exercise_6A_8 (a b c x y : ℝ) (h : a^2 + b^2 + c^2 + x^2 + y^2 ≤ 1) :
    a + b + c + 4*x + 9*y ≤ 10 := by
  -- a + b + c + 4x + 9y = ⟨(a, b, c, x, y), (1, 1, 1, 4, 9)⟩
  -- by Cauchy-Schwarz, ⟨(a, b, c, x, y), (1, 1, 1, 4, 9)⟩ ≤ ‖(a, b, c, x, y)‖ * ‖(1, 1, 1, 4, 9)‖
  -- ‖(a, b, c, x, y)‖^2 = a^2 + b^2 + c^2 + x^2 + y^2 ≤ 1
  -- ‖(1, 1, 1, 4, 9)‖^2 = 1 + 1 + 1 + 16 + 81 = 100
  -- so a + b + c + 4x + 9y ≤ √1 * √100 = 10
  have hcs := sum_mul_sq_le ![a, b, c, x, y] ![1, 1, 1, 4, 9]
  simp only [Fin.sum_univ_five, Matrix.cons_val] at hcs
  norm_num at hcs
  nlinarith

/-- 6A.9 If {lit}`‖u‖ = ‖v‖ = 1` and {lit}`⟨u, v⟩ = 1`, then {lit}`u = v`. -/
theorem exercise_6A_9 (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫_𝕜 = 1) :
    u = v := by
  -- 1 = ⟨u, v⟩ ≤ ||u|| * ||v|| = 1, with equality if and only if u and v are collinear
  have heq : ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖ := by rw [huv, hu, hv, norm_one, mul_one]
  obtain ⟨k, hk | hk⟩ := cauchy_schwarz_eq_iff.mp heq
  -- so v = k u (or u = k v) for some k ∈ 𝕜; then ⟨u, v⟩ = k ‖u‖² = k, so k = 1
  · rw [hk, inner_smul_right, inner_self_eq_norm_sq_to_K, hu] at huv
    simp only [RCLike.ofReal_one, one_pow, mul_one] at huv
    rw [hk, huv, one_smul]
  -- symmetrically, if u = k v then ⟨u, v⟩ = conj k ‖v‖² = conj k, so k = 1
  · rw [hk, inner_smul_left, inner_self_eq_norm_sq_to_K, hv] at huv
    simp only [RCLike.ofReal_one, one_pow, mul_one] at huv
    have hk1 : k = 1 := by rw [← RCLike.conj_conj k, huv, map_one]
    -- hence k = 1, so u = v
    rw [hk, hk1, one_smul]

/-- 6A.10 If {lit}`‖u‖ ≤ 1` and {lit}`‖v‖ ≤ 1`, then
{lit}`√(1 − ‖u‖²) √(1 − ‖v‖²) ≤ 1 − |⟨u, v⟩|`. -/
theorem exercise_6A_10 (u v : V) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    Real.sqrt (1 - ‖u‖ ^ 2) * Real.sqrt (1 - ‖v‖ ^ 2) ≤ 1 - ‖⟪u, v⟫_𝕜‖ := by
  -- (1 - |⟨u, v⟩|)^2 ≥ (1 - ‖u‖ * ‖v‖)^2 ≥ (1 - ‖u‖^2) * (1 - ‖v‖^2)
  -- use a lemma for the last one (1-ab)^2 ≥ (1-a^2)(1-b^2) for 0 ≤ a, b ≤ 1
  -- to prove the lemma
  -- (1-ab)^2 - (1-a^2)(1-b^2) = 1 - 2ab + a^2b^2 - (1 - a^2 - b^2 + a^2b^2) =
  -- a^2 + b^2 - 2ab = (a-b)^2 ≥ 0 for any a, b ∈ ℝ
  have hlemma : ∀ a b : ℝ, (1 - a ^ 2) * (1 - b ^ 2) ≤ (1 - a * b) ^ 2 := by
    intro a b
    have hid : (1 - a * b) ^ 2 - (1 - a ^ 2) * (1 - b ^ 2) = (a - b) ^ 2 := by ring
    nlinarith [sq_nonneg (a - b)]
  -- (1 - |⟨u, v⟩|)^2 ≥ (1 - ‖u‖ * ‖v‖)^2, by Cauchy–Schwarz and ‖u‖ * ‖v‖ ≤ 1
  have hcs := cauchy_schwarz (𝕜 := 𝕜) u v
  have hab1 : ‖u‖ * ‖v‖ ≤ 1 := by nlinarith [norm_nonneg u, norm_nonneg v]
  have hsq : (1 - ‖u‖ * ‖v‖) ^ 2 ≤ (1 - ‖⟪u, v⟫_𝕜‖) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  -- take square roots
  have hu2 : 0 ≤ 1 - ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  rw [← Real.sqrt_mul hu2]
  calc Real.sqrt ((1 - ‖u‖ ^ 2) * (1 - ‖v‖ ^ 2))
      ≤ Real.sqrt ((1 - ‖⟪u, v⟫_𝕜‖) ^ 2) :=
        Real.sqrt_le_sqrt ((hlemma ‖u‖ ‖v‖).trans hsq)
    _ = 1 - ‖⟪u, v⟫_𝕜‖ := Real.sqrt_sq (by linarith)

/-- 6A.11 Find {lit}`u, v ∈ ℝ²` such that {lit}`u` is a scalar multiple of
{lit}`(1, 3)`, {lit}`v` is orthogonal to {lit}`(1, 3)`, and {lit}`(1, 2) = u + v`. -/
theorem exercise_6A_11 :
    ∃ u v : EuclideanSpace ℝ (Fin 2),
      (∃ c : ℝ, u = c • (!₂[1, 3] : EuclideanSpace ℝ (Fin 2))) ∧
      Orthogonal (𝕜 := ℝ) v (!₂[1, 3] : EuclideanSpace ℝ (Fin 2)) ∧
      (!₂[1, 2] : EuclideanSpace ℝ (Fin 2)) = u + v := by
  -- use orthogonal decomposition: write (1, 2) = u + v with u parallel to (1, 3)
  -- and v orthogonal to (1, 3)
  -- u = ⟨(1,2) * (1,3)⟩ / ⟨(1,3), (1,3)⟩ * (1,3) = (7/10, 21/10)
  -- v = (1,2) - u = (3/10, -1/10)
  refine ⟨(7 / 10 : ℝ) • !₂[1, 3], !₂[3 / 10, -1 / 10], ⟨7 / 10, rfl⟩, ?_, ?_⟩
  · simp [Orthogonal, PiLp.inner_apply, Fin.sum_univ_two]
    simp [inner]
    norm_num
  · ext i
    fin_cases i <;> simp <;> norm_num

/-- 6A.12 (a) For positive {lit}`a, b, c, d`,
{lit}`(a + b + c + d)(1/a + 1/b + 1/c + 1/d) ≥ 16`. -/
theorem exercise_6A_12a (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) : 16 ≤ (a + b + c + d) * (1/a + 1/b + 1/c + 1/d) := by
  -- by CS (a + b + c + d) = ||(√a, √b, √c, √d)||^2 * ||(1/√a, 1/√b, 1/√c, 1/√d)||^2 ≥ (⟪(√a, √b, √c, √d), (1/√a, 1/√b, 1/√c, 1/√d)⟫)^2
  -- ≥ (⟪(√a, √b, √c, √d), (1/√a, 1/√b, 1/√c, 1/√d)⟫)^2 = (√a * 1/√a + √b * 1/√b + √c * 1/√c + √d * 1/√d)^2 = (1 + 1 + 1 + 1)^2 = 16
  have hcs := sum_mul_sq_le ![√a, √b, √c, √d] ![1 / √a, 1 / √b, 1 / √c, 1 / √d]
  simp only [Fin.sum_univ_four, Matrix.cons_val] at hcs
  simp only [mul_one_div_cancel (Real.sqrt_pos.mpr ha).ne', mul_one_div_cancel
    (Real.sqrt_pos.mpr hb).ne', mul_one_div_cancel (Real.sqrt_pos.mpr hc).ne',
    mul_one_div_cancel (Real.sqrt_pos.mpr hd).ne', div_pow, one_pow, Real.sq_sqrt ha.le,
    Real.sq_sqrt hb.le, Real.sq_sqrt hc.le, Real.sq_sqrt hd.le] at hcs
  norm_num at hcs
  simpa only [one_div] using hcs

/-- 6A.12 (b) The inequality in (a) is an equality if and only if
{lit}`a = b = c = d`. -/
theorem exercise_6A_12b (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) :
    (a + b + c + d) * (1/a + 1/b + 1/c + 1/d) = 16 ↔ a = b ∧ b = c ∧ c = d := by
  constructor
  · intro h
    -- Cauchy-Swartz equality if v = k u for some k,
    have hsa := Real.sqrt_pos.mpr ha
    have hsb := Real.sqrt_pos.mpr hb
    have hsc := Real.sqrt_pos.mpr hc
    have hsd := Real.sqrt_pos.mpr hd
    have hcs : (∑ i, ![√a, √b, √c, √d] i * ![1 / √a, 1 / √b, 1 / √c, 1 / √d] i) ^ 2 =
        (∑ i, ![√a, √b, √c, √d] i ^ 2) * (∑ i, ![1 / √a, 1 / √b, 1 / √c, 1 / √d] i ^ 2) := by
      simp only [Fin.sum_univ_four, Matrix.cons_val]
      simp only [mul_one_div_cancel hsa.ne', mul_one_div_cancel hsb.ne',
        mul_one_div_cancel hsc.ne', mul_one_div_cancel hsd.ne', div_pow, one_pow,
        Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, Real.sq_sqrt hc.le, Real.sq_sqrt hd.le, h]
      norm_num
    obtain ⟨k, hk | hk⟩ := sum_mul_sq_eq _ _ hcs
    -- either 1/√t = k √t for each t, so k t = 1 …
    · have key : ∀ t : ℝ, 0 < t → 1 / √t = k * √t → k * t = 1 := by
        intro t ht h
        rw [div_eq_iff (Real.sqrt_pos.mpr ht).ne', mul_assoc, Real.mul_self_sqrt ht.le] at h
        exact h.symm
      have h0 := key a ha (by simpa using congrFun hk 0)
      have h1 := key b hb (by simpa using congrFun hk 1)
      have h2 := key c hc (by simpa using congrFun hk 2)
      have h3 := key d hd (by simpa using congrFun hk 3)
      have hk0 : k ≠ 0 := by rintro rfl; simp at h0
      refine ⟨?_, ?_, ?_⟩ <;> apply mul_left_cancel₀ hk0 <;> linarith
    -- … or, as in the sketch, √t = k/√t for each t, so t = k
    -- in this case √a = k/√a, and similarly for b, c, d, so a = b = c = d = k for some k.
    · have key : ∀ t : ℝ, 0 < t → √t = k * (1 / √t) → t = k := by
        intro t ht h
        rw [mul_one_div, eq_div_iff (Real.sqrt_pos.mpr ht).ne', Real.mul_self_sqrt ht.le] at h
        exact h
      have h0 := key a ha (by simpa using congrFun hk 0)
      have h1 := key b hb (by simpa using congrFun hk 1)
      have h2 := key c hc (by simpa using congrFun hk 2)
      have h3 := key d hd (by simpa using congrFun hk 3)
      exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    field_simp
    ring

/-- 6A.13 The square of an average is at most the average of the squares. -/
theorem exercise_6A_13 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ((∑ i, a i) / n) ^ 2 ≤ (∑ i, (a i) ^ 2) / n := by
  -- rewrite as (∑ ai) ^2 ≤ n ∑ ai^2
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_pow, div_le_div_iff₀ (by positivity) hn']
  -- same as ⟨a, 1⟩^2 ≤ |1|^2 * |a|^2, where 1 is the vector of all ones.
  -- this is just Cauchy-Swartz inequality.
  have hcs := sum_mul_sq_le a (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hcs
  nlinarith

/-- Equality in the reverse triangle inequality: for nonzero {lit}`u, v`,
{lit}`|‖v‖ − ‖u‖| = ‖v − u‖` if and only if {lit}`u` and {lit}`v` point in the same
direction, {lit}`u/‖u‖ = v/‖v‖`. -/
theorem abs_norm_sub_norm_eq_iff {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) :
    |‖v‖ - ‖u‖| = ‖v - u‖ ↔ (‖u‖⁻¹ : 𝕜) • u = (‖v‖⁻¹ : 𝕜) • v := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- the unit vectors `u/‖u‖` and `v/‖v‖`
  have hunit : ∀ x : V, x ≠ 0 → ‖(‖x‖⁻¹ : 𝕜) • x‖ = 1 := fun x hx => by
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  constructor
  · intro heq
    -- expand ‖v - u‖² = ‖v‖² + ‖u‖² - 2 Re⟨u, v⟩, while |‖v‖ - ‖u‖|² = (‖v‖ - ‖u‖)²,
    -- so equality means Re⟨u, v⟩ = ‖u‖ ‖v‖, i.e. Re⟨u/‖u‖, v/‖v‖⟩ = 1.
    have hvu := norm_sub_sq_expand (𝕜 := 𝕜) v u
    rw [← heq, sq_abs] at hvu
    have hre : RCLike.re ⟪u, v⟫_𝕜 = ‖u‖ * ‖v‖ := by
      rw [inner_re_symm]; nlinarith
    have hre' : RCLike.re ⟪(‖u‖⁻¹ : 𝕜) • u, (‖v‖⁻¹ : 𝕜) • v⟫_𝕜 = 1 := by
      rw [inner_smul_left, inner_smul_right, ← RCLike.ofReal_inv, ← RCLike.ofReal_inv,
        RCLike.conj_ofReal, ← mul_assoc, ← RCLike.ofReal_mul, RCLike.re_ofReal_mul, hre]
      field_simp
    -- then ‖u/‖u‖ - v/‖v‖‖² = 1 + 1 - 2 Re⟨u/‖u‖, v/‖v‖⟩ = 0
    have hsub := norm_sub_sq_expand (𝕜 := 𝕜) ((‖u‖⁻¹ : 𝕜) • u) ((‖v‖⁻¹ : 𝕜) • v)
    rw [hunit u hu, hunit v hv, hre'] at hsub
    have h0 : ‖(‖u‖⁻¹ : 𝕜) • u - (‖v‖⁻¹ : 𝕜) • v‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0))
  · intro h
    -- conversely, with e = u/‖u‖ = v/‖v‖, v - u = (‖v‖ - ‖u‖) e has norm |‖v‖ - ‖u‖|
    have hsplit : ∀ x : V, x ≠ 0 → x = (‖x‖ : 𝕜) • ((‖x‖⁻¹ : 𝕜) • x) := fun x hx => by
      rw [smul_smul, mul_inv_cancel₀ (by simpa using hx), one_smul]
    have hvu : v - u = ((‖v‖ - ‖u‖ : ℝ) : 𝕜) • ((‖v‖⁻¹ : 𝕜) • v) := by
      conv_lhs => rw [hsplit v hv, hsplit u hu, h]
      rw [RCLike.ofReal_sub, sub_smul]
    rw [hvu, norm_smul, RCLike.norm_ofReal, hunit v hv, mul_one]

/-- 6A.14 For {lit}`v ≠ 0`, {lit}`v/‖v‖` is the unique closest element on the unit
sphere to {lit}`v`: for every unit vector {lit}`u`,
{lit}`‖v − v/‖v‖‖ ≤ ‖v − u‖`, with equality if and only if {lit}`u = v/‖v‖`. -/
theorem exercise_6A_14 (v : V) (hv : v ≠ 0) (u : V) (hu : ‖u‖ = 1) :
    ‖v - (‖v‖⁻¹ : 𝕜) • v‖ ≤ ‖v - u‖ ∧
      (‖v - (‖v‖⁻¹ : 𝕜) • v‖ = ‖v - u‖ ↔ u = (‖v‖⁻¹ : 𝕜) • v) := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set e := (‖v‖⁻¹ : 𝕜) • v with he
  -- ‖v - (‖v‖⁻¹ : 𝕜) • v‖ simplies to |‖v‖ - 1| = |‖v‖ - ‖u‖|
  have hve : ‖v - e‖ = |‖v‖ - 1| := by
    have h1 : v - e = ((1 - ‖v‖⁻¹ : ℝ) : 𝕜) • v := by
      rw [he, RCLike.ofReal_sub, RCLike.ofReal_one, RCLike.ofReal_inv, sub_smul, one_smul]
    rw [h1, norm_smul, RCLike.norm_ofReal, ← abs_of_pos hn, ← abs_mul, abs_of_pos hn]
    congr 1
    field_simp
  refine ⟨?_, ?_⟩
  -- so the result is just the reverse triangle inequality.
  · rw [hve, ← hu]
    exact abs_norm_sub_norm_le v u
  -- equality in the reverse triangle inequality holds iff u and v point in the same
  -- direction, u/‖u‖ = v/‖v‖; since ‖u‖ = 1, u must be v / ‖v‖.
  · constructor
    · intro heq
      have hu0 : u ≠ 0 := by rintro rfl; simp at hu
      have h := (abs_norm_sub_norm_eq_iff (𝕜 := 𝕜) hu0 hv).mp (by rw [hu, ← hve, heq])
      simpa [hu] using h
    · intro h
      rw [h]

-- 6A.15 and 16 not formalizable, need geometry.

/-- 6A.17 {lit}`(∑ₖ aₖbₖ)² ≤ (∑ₖ k aₖ²)(∑ₖ bₖ²/k)` for reals. -/
theorem exercise_6A_17 {n : ℕ} (a b : Fin n → ℝ) :
    (∑ k : Fin n, a k * b k) ^ 2 ≤
      (∑ k : Fin n, ((k : ℝ) + 1) * a k ^ 2) *
        (∑ k : Fin n, b k ^ 2 / ((k : ℝ) + 1)) := by
  -- define u and v as follows u i = √(i + 1) a i and v i = b i / √(i + 1)
  have hpos : ∀ k : Fin n, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hs : ∀ k : Fin n, √((k : ℝ) + 1) ≠ 0 := fun k => (Real.sqrt_pos.mpr (hpos k)).ne'
  -- apply Cauchy-Swartz inequality squared to u and v defined above.
  have hcs := sum_mul_sq_le (fun k : Fin n => √((k : ℝ) + 1) * a k)
    (fun k => b k / √((k : ℝ) + 1))
  have huv : ∀ k : Fin n, √((k : ℝ) + 1) * a k * (b k / √((k : ℝ) + 1)) = a k * b k :=
    fun k => by field_simp
  have hu2 : ∀ k : Fin n, (√((k : ℝ) + 1) * a k) ^ 2 = ((k : ℝ) + 1) * a k ^ 2 :=
    fun k => by rw [mul_pow, Real.sq_sqrt (hpos k).le]
  have hv2 : ∀ k : Fin n, (b k / √((k : ℝ) + 1)) ^ 2 = b k ^ 2 / ((k : ℝ) + 1) :=
    fun k => by rw [div_pow, Real.sq_sqrt (hpos k).le]
  simpa only [huv, hu2, hv2] using hcs

section
open MeasureTheory

/-- {lit}`1/x²` is integrable on {lit}`[1, ∞)`… -/
private theorem integrableOn_inv_sq_Ici :
    IntegrableOn (fun x : ℝ => (1 / x) ^ 2) (Set.Ici 1) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) one_pos).congr_fun
    (fun x hx => ?_) measurableSet_Ioi
  rw [Real.rpow_neg (by linarith [Set.mem_Ioi.mp hx]), Real.rpow_two, one_div, inv_pow]

/-- …with {lit}`∫₁^∞ 1/x² = 1`. -/
private theorem integral_inv_sq_Ici : ∫ x in Set.Ici (1:ℝ), (1 / x) ^ 2 = 1 := by
  rw [integral_Ici_eq_integral_Ioi, setIntegral_congr_fun measurableSet_Ioi
    (g := fun x : ℝ => x ^ (-2:ℝ)) (fun x hx => by
      simp only
      rw [Real.rpow_neg (by linarith [Set.mem_Ioi.mp hx]), Real.rpow_two, one_div, inv_pow]),
    integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

/-- The inner product space for 6A.18: the square-integrable functions on
{lit}`[1, ∞)`, i.e. mathlib's {lit}`L²(μ)` for {lit}`μ` Lebesgue measure restricted
to {lit}`[1, ∞)`, an inner product space with {lit}`⟨u, v⟩ = ∫₁^∞ uv`. When
{lit}`x² f²` is integrable, {lit}`u = x f` and {lit}`v = 1/x` belong to it, with
{lit}`⟨u, v⟩ = ∫₁^∞ f`, {lit}`‖u‖² = ∫₁^∞ x² f²` and {lit}`‖v‖² = ∫₁^∞ 1/x² = 1`. -/
private theorem L2_6A_18 (f : ℝ → ℝ) (hf : Continuous f)
    (hint : IntegrableOn (fun x => x ^ 2 * f x ^ 2) (Set.Ici (1:ℝ))) :
    ∃ U V : Lp ℝ 2 (volume.restrict (Set.Ici (1:ℝ))),
      ⟪U, V⟫_ℝ = ∫ x in Set.Ici (1:ℝ), f x ∧
      ‖U‖ ^ 2 = ∫ x in Set.Ici (1:ℝ), x ^ 2 * f x ^ 2 ∧ ‖V‖ ^ 2 = 1 ∧
      U =ᵐ[volume.restrict (Set.Ici (1:ℝ))] (fun x => x * f x) ∧
      V =ᵐ[volume.restrict (Set.Ici (1:ℝ))] (fun x => 1 / x) := by
  set μ := volume.restrict (Set.Ici (1:ℝ))
  -- the inner product of two functions in `L²(μ)` is the integral of their product
  have hinner : ∀ {g h : ℝ → ℝ} (hg : MemLp g 2 μ) (hh : MemLp h 2 μ),
      ⟪hg.toLp g, hh.toLp h⟫_ℝ = ∫ x in Set.Ici (1:ℝ), g x * h x := by
    intro g h hg hh
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [inner, mul_comm]
  have hu : MemLp (fun x => x * f x) 2 μ :=
    (memLp_two_iff_integrable_sq
      (by fun_prop : Continuous fun x : ℝ => x * f x).aestronglyMeasurable).mpr
      (by simpa only [mul_pow] using hint)
  have hv : MemLp (fun x : ℝ => 1 / x) 2 μ :=
    (memLp_two_iff_integrable_sq
      (measurable_const.div measurable_id).aestronglyMeasurable).mpr integrableOn_inv_sq_Ici
  refine ⟨hu.toLp _, hv.toLp _, ?_, ?_, ?_, hu.coeFn_toLp, hv.coeFn_toLp⟩
  · rw [hinner]
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    have : x ≠ 0 := (lt_of_lt_of_le one_pos (Set.mem_Ici.mp hx)).ne'
    field_simp
  · rw [← real_inner_self_eq_norm_sq, hinner]
    congr 1; ext x; ring
  · rw [← real_inner_self_eq_norm_sq, hinner]
    simp_rw [← sq]
    exact integral_inv_sq_Ici

/-- 6A.18 (a) For continuous {lit}`f : [1, ∞) → [0, ∞)`,
{lit}`(∫₁^∞ f)² ≤ ∫₁^∞ x² f(x)² dx`. -/
theorem exercise_6A_18a (f : ℝ → ℝ) (hf : Continuous f) (_ : ∀ x, 0 ≤ f x)
    (hint : IntegrableOn (fun x => x ^ 2 * f x ^ 2) (Set.Ici (1:ℝ))) :
    (∫ x in Set.Ici (1:ℝ), f x) ^ 2 ≤ ∫ x in Set.Ici (1:ℝ), x ^ 2 * f x ^ 2 := by
  -- first show that ∫ x in Set.Ici (1:ℝ), f x g x is inner product on the VS
  -- of functions from [1, ∞) to ℝ
  -- (the square-integrable ones: mathlib's L², see `L2_6A_18`)
  -- then apply the Cauchy–Schwarz inequality for this inner product with
  -- u = x f and v = 1 / x.
  obtain ⟨U, V, hUV, hUU, hVV, -, -⟩ := L2_6A_18 f hf hint
  have hcs := pow_le_pow_left₀ (norm_nonneg _) (cauchy_schwarz (𝕜 := ℝ) U V) 2
  -- since the range is non-negative, we can remove | | from the LHS.
  -- on the right-hand side, ∫ x in Set.Ici (1:ℝ), 1/x^2 = 1
  rwa [mul_pow, hUU, hVV, mul_one, hUV, Real.norm_eq_abs, sq_abs] at hcs

/-- 6A.18 (b) The inequality in (a) is an equality with both sides finite if and
only if {lit}`f(x) = c/x²` for some constant {lit}`c ≥ 0` (the Cauchy–Schwarz
equality case, where {lit}`x f(x)` is proportional to {lit}`1/x`). -/
theorem exercise_6A_18b (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) :
    (IntegrableOn f (Set.Ici (1:ℝ)) ∧
      IntegrableOn (fun x => x ^ 2 * f x ^ 2) (Set.Ici (1:ℝ)) ∧
      (∫ x in Set.Ici (1:ℝ), f x) ^ 2 = ∫ x in Set.Ici (1:ℝ), x ^ 2 * f x ^ 2) ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x ≥ (1:ℝ), f x = c / x ^ 2 := by
  have hS : MeasurableSet (Set.Ici (1:ℝ)) := measurableSet_Ici
  constructor
  · rintro ⟨-, hint, heq⟩
    obtain ⟨U, V, hUV, hUU, hVV, hUae, hVae⟩ := L2_6A_18 f hf hint
    -- cauchy-schwarz equality case: x f(x) is proportional to 1/x.
    have hcs : ‖⟪U, V⟫_ℝ‖ = ‖U‖ * ‖V‖ := by
      rw [← pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow, hUU, hVV,
        mul_one, hUV, Real.norm_eq_abs, sq_abs, heq]
    -- as functions on [1, ∞) the proportionality holds a.e., hence everywhere by continuity
    have hinvc : ContinuousOn (fun x : ℝ => 1 / x) (Set.Ici 1) :=
      continuousOn_const.div continuousOn_id fun x hx => (lt_of_lt_of_le one_pos hx).ne'
    have hcl : Set.Ici (1:ℝ) ⊆ closure (interior (Set.Ici 1)) := by
      rw [interior_Ici, closure_Ioi]
    -- so f(x) = c / x^2 for some constant c ≥ 0 (to keep non-negativty); c = f(1)
    refine ⟨f 1, hf0 1, fun x hx => ?_⟩
    have hx0 : x ≠ 0 := (lt_of_lt_of_le one_pos hx).ne'
    rw [eq_div_iff (pow_ne_zero 2 hx0)]
    obtain ⟨r, hr | hr⟩ := cauchy_schwarz_eq_iff.mp hcs
    · -- v = r u: 1/x = r x f(x)
      have hae : (fun x : ℝ => 1 / x) =ᵐ[volume.restrict (Set.Ici 1)]
          fun x => r * (x * f x) := by
        filter_upwards [hVae, hUae, Lp.coeFn_smul r U] with y h1 h2 h3
        calc 1 / y = V y := h1.symm
          _ = (r • U) y := by rw [hr]
          _ = r * (y * f y) := by rw [h3, Pi.smul_apply, h2, smul_eq_mul]
      have hEq := Measure.eqOn_of_ae_eq hae hinvc
        (continuous_const.mul (continuous_id.mul hf)).continuousOn hcl
      have e1 : r * f 1 = 1 := by simpa using (hEq Set.self_mem_Ici).symm
      have hxe := hEq hx
      simp only at hxe
      rw [div_eq_iff hx0] at hxe
      have e2 : r * (f x * x ^ 2) = 1 := by rw [hxe]; ring
      have hr0 : r ≠ 0 := by rintro rfl; simp at e1
      exact mul_left_cancel₀ hr0 (e2.trans e1.symm)
    · -- u = r v: x f(x) = r/x
      have hae : (fun x : ℝ => x * f x) =ᵐ[volume.restrict (Set.Ici 1)]
          fun x => r * (1 / x) := by
        filter_upwards [hVae, hUae, Lp.coeFn_smul r V] with y h1 h2 h3
        calc y * f y = U y := h2.symm
          _ = (r • V) y := by rw [hr]
          _ = r * (1 / y) := by rw [h3, Pi.smul_apply, h1, smul_eq_mul]
      have hEq := Measure.eqOn_of_ae_eq hae (continuous_id.mul hf).continuousOn
        (continuousOn_const.mul hinvc) hcl
      have e1 : f 1 = r := by simpa using hEq Set.self_mem_Ici
      have hxe := hEq hx
      simp only at hxe
      rw [mul_one_div, eq_div_iff hx0] at hxe
      rw [e1, ← hxe]
      ring
  · rintro ⟨c, hc, hfc⟩
    -- conversely, f = c · (1/x²) and x² f² = c² · (1/x²) on [1, ∞) are integrable
    have hf' : Set.EqOn (fun x : ℝ => c * (1 / x) ^ 2) f (Set.Ici 1) := fun x hx => by
      rw [hfc x hx]; field_simp
    have hg' : Set.EqOn (fun x : ℝ => c ^ 2 * (1 / x) ^ 2) (fun x => x ^ 2 * f x ^ 2)
        (Set.Ici 1) := fun x hx => by
      have hx0 : x ≠ 0 := (lt_of_lt_of_le one_pos (Set.mem_Ici.mp hx)).ne'
      simp only; rw [hfc x hx]; field_simp
    have hint := IntegrableOn.congr_fun (integrableOn_inv_sq_Ici.const_mul (c ^ 2)) hg' hS
    refine ⟨IntegrableOn.congr_fun (integrableOn_inv_sq_Ici.const_mul c) hf' hS, hint, ?_⟩
    -- and u = x f = c/x = c v, so equality holds in Cauchy–Schwarz
    obtain ⟨U, V, hUV, hUU, hVV, hUae, hVae⟩ := L2_6A_18 f hf hint
    have hUcV : U = c • V := by
      apply Lp.ext
      filter_upwards [hUae, hVae, Lp.coeFn_smul c V, ae_restrict_mem hS] with y h1 h2 h3 hy
      have hy0 : y ≠ 0 := (lt_of_lt_of_le one_pos (Set.mem_Ici.mp hy)).ne'
      rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul, hfc y hy]
      field_simp
    have hcs := congrArg (· ^ 2) ((cauchy_schwarz_eq_iff (𝕜 := ℝ)).mpr ⟨c, Or.inr hUcV⟩)
    simp only at hcs
    rwa [mul_pow, hUU, hVV, mul_one, hUV, Real.norm_eq_abs, sq_abs] at hcs
end

/-- Cauchy–Schwarz for {lit}`𝔽ⁿ` in coordinates:
{lit}`|∑ xᵢyᵢ|² ≤ (∑ |xᵢ|²)(∑ |yᵢ|²)`, from 6.14 applied to {lit}`x̄` and
{lit}`y` in {lit}`𝔽ⁿ` (whose inner product is {lit}`∑ x̄ᵢ yᵢ` in mathlib's slots). -/
private theorem norm_sum_mul_sq_le {n : ℕ} (x y : Fin n → 𝕜) :
    ‖∑ i, x i * y i‖ ^ 2 ≤ (∑ i, ‖x i‖ ^ 2) * (∑ i, ‖y i‖ ^ 2) := by
  set X : EuclideanSpace 𝕜 (Fin n) := WithLp.toLp 2 (fun i => conj (x i))
  set Y : EuclideanSpace 𝕜 (Fin n) := WithLp.toLp 2 y
  have hXY : ⟪X, Y⟫_𝕜 = ∑ i, x i * y i := by
    rw [PiLp.inner_apply]; congr 1; ext i
    simp [X, Y, mul_comm]
  have hXX : ‖X‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by simp [X, EuclideanSpace.norm_sq_eq]
  have hYY : ‖Y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by simp [Y, EuclideanSpace.norm_sq_eq]
  have hcs := pow_le_pow_left₀ (norm_nonneg _) (cauchy_schwarz (𝕜 := 𝕜) X Y) 2
  rwa [mul_pow, hXX, hYY, hXY] at hcs

/-- 6A.19 If {lit}`v₁, …, vₙ` is a basis of {lit}`V`, {lit}`T ∈ ℒ(V)`, and
{lit}`λ` is an eigenvalue of {lit}`T`, then {lit}`|λ|² ≤ ∑ⱼ ∑ₖ |ℳ(T)ⱼ,ₖ|²`. -/
theorem exercise_6A_19 {n : ℕ} (b : Module.Basis (Fin n) 𝕜 V) (T : V →ₗ[𝕜] V)
    (lam : 𝕜) (h : ∃ v : V, v ≠ 0 ∧ T v = lam • v) :
    ‖lam‖ ^ 2 ≤ ∑ j, ∑ k, ‖LinearMap.toMatrix b b T j k‖ ^ 2 := by
  -- take the eigenvector v and work in concrete basis, where v
  -- is represented as a list of scalars a in the chosen basis
  -- and T is a matrix A
  obtain ⟨v, hv0, hTv⟩ := h
  set a : Fin n → 𝕜 := ⇑(b.repr v)
  set A := LinearMap.toMatrix b b T
  -- then A a = λ a in each coordinate
  have hA : ∀ i, ∑ k, A i k * a k = lam * a i := by
    intro i
    have := congrFun (LinearMap.toMatrix_mulVec_repr b b T v) i
    rw [hTv, map_smul] at this
    simpa [Matrix.mulVec, dotProduct] using this
  -- which is same as |⟨Ai*, a⟩| = |λ| |ai| for each coordinate i
  -- apply Cauchy–Schwarz inequality to the LHS and square
  -- |λ|^2 |ai|^2 ≤ ‖Ai*‖^2 ‖a‖^2 by Cauchy–Schwarz
  have hcs : ∀ i, ‖lam‖ ^ 2 * ‖a i‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖a k‖ ^ 2 := by
    intro i
    have := norm_sum_mul_sq_le (A i) a
    rwa [hA i, norm_mul, mul_pow] at this
  -- now sum over all i
  -- |λ|^2 ∑i |ai|^2 ≤ ‖a‖^2 ∑i ‖Ai*‖^2
  have hsum : ‖lam‖ ^ 2 * ∑ i, ‖a i‖ ^ 2 ≤ (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ‖a k‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hcs i
  -- after cancelling ‖a‖^2, we get |λ|^2 ≤ ∑i ‖Ai*‖^2 = ∑ j, ∑ k |A j k|^2
  -- (‖a‖ ≠ 0 since v ≠ 0)
  have hpos : 0 < ∑ k, ‖a k‖ ^ 2 := by
    refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => sq_nonneg _) fun h0 => hv0 ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg ‖a k‖).mp h0.symm
    have ha : b.repr v = 0 := by
      ext k
      simpa using hz k (Finset.mem_univ k)
    exact b.repr.map_eq_zero_iff.mp ha
  exact le_of_mul_le_mul_right hsum hpos

include 𝕜 in
/-- 6A.20 Reverse triangle inequality: {lit}`| ‖u‖ − ‖v‖ | ≤ ‖u − v‖`. -/
@[avoiding abs_norm_sub_norm_le, norm_sub_norm_le]
theorem exercise_6A_20 (u v : V) : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := by
  -- enough to prove ‖u‖ - ‖v‖ ≤ ‖u - v‖ and ‖v‖ - ‖u‖ ≤ ‖u - v‖ separately
  rw [abs_sub_le_iff]
  constructor
  -- the first one is just triangle ineq.
  · have h := triangle_inequality (𝕜 := 𝕜) (u - v) v
    rw [sub_add_cancel] at h
    linarith
  -- the second is also triangle ineq. after rewriting ||u-v|| as ||v-u||
  · have h := triangle_inequality (𝕜 := 𝕜) (v - u) u
    rw [sub_add_cancel] at h
    rw [norm_sub_rev]
    linarith

include 𝕜 in
/-- 6A.21 If {lit}`‖u‖ = 3`, {lit}`‖u + v‖ = 4`, {lit}`‖u − v‖ = 6`, find
{lit}`‖v‖`. Fill in the first sorry with a concrete value and then prove. -/
theorem exercise_6A_21 (u v : V) (h1 : ‖u‖ = 3) (h2 : ‖u + v‖ = 4)
    (h3 : ‖u - v‖ = 6) : ‖v‖ = √17 := by
  -- apply parellelogram equality: ‖u + v‖² + ‖u - v‖² = 2‖u‖² + 2‖v‖²
  have h := parallelogram (𝕜 := 𝕜) u v
  rw [h1, h2, h3] at h
  -- so 16 + 36 = 18 + 2‖v‖², i.e. ‖v‖² = 17
  rw [← Real.sqrt_sq (norm_nonneg v)]
  congr 1
  linarith

include 𝕜 in
/-- 6A.22 {lit}`‖u + v‖ ‖u − v‖ ≤ ‖u‖² + ‖v‖²`. -/
theorem exercise_6A_22 (u v : V) : ‖u + v‖ * ‖u - v‖ ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  -- apply parallelogram equality: (‖u + v‖² + ‖u - v‖²)/2 = ‖u‖² + ‖v‖²
  -- then observe that the inequality desired rewrites as
  -- 2ab ≤ a^2 + b^2 -> (a - b)^2 ≥ 0, where a = ‖u + v‖/√2 and b = ‖u - v‖/√2
  have h := parallelogram (𝕜 := 𝕜) u v
  nlinarith [sq_nonneg (‖u + v‖ - ‖u - v‖)]

/-- 6A.23 If {lit}`‖vₖ‖ ≤ 1` for each {lit}`k`, then there exist signs
{lit}`aₖ ∈ {1, −1}` with {lit}`‖a₁v₁ + ⋯ + aₘvₘ‖ ≤ √m`. -/
theorem exercise_6A_23 {m : ℕ} (v : Fin m → V) (h : ∀ k, ‖v k‖ ≤ 1) :
    ∃ a : Fin m → 𝕜, (∀ k, a k = 1 ∨ a k = -1) ∧
      ‖∑ k, a k • v k‖ ≤ Real.sqrt m := by
  -- induction on m, base case (m = 0, the empty sum) is trivial
  induction m with
  | zero => exact ⟨fun _ => 1, fun _ => Or.inl rfl, by simp⟩
  | succ m ih =>
  -- if S = ∑ k, a k • v k has norm ≤ √m for some choice of signs for the first m vectors,
  obtain ⟨a, ha, hS⟩ := ih (fun k => v (Fin.castSucc k)) (fun k => h _)
  set S := ∑ k, a k • v (Fin.castSucc k)
  set w := v (Fin.last m)
  -- then |S|^2 ≤ m by induction
  have hS2 : ‖S‖ ^ 2 ≤ m := by
    have := pow_le_pow_left₀ (norm_nonneg S) hS 2
    rwa [Real.sq_sqrt (Nat.cast_nonneg m)] at this
  -- notice that we can just choose am to have the opposite sign of Re ⟪S, vm⟫ to make the middle term non-positive
  set s : ℝ := if 0 ≤ RCLike.re ⟪S, w⟫_𝕜 then -1 else 1 with hs
  have hmid : s * RCLike.re ⟪S, w⟫_𝕜 ≤ 0 := by
    rw [hs]; split_ifs with hre <;> linarith
  have hs1 : |s| = 1 := by rw [hs]; split_ifs <;> simp
  refine ⟨fun k => Fin.lastCases (s : 𝕜) a k, fun k => ?_, ?_⟩
  · induction k using Fin.lastCases with
    | last => simp only [Fin.lastCases_last, hs]; split_ifs <;> simp
    | cast k => simp only [Fin.lastCases_castSucc]; exact ha k
  -- |S + am vm|^2 = |S|^2 + 2 Re (am ⟪S, vm⟫) + |am|^2 |vm|^2 ≤ m + 1 + 2 am Re ⟪S, vm⟫
  -- and achieve the inequality.
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    have hexp := norm_add_sq_expand (𝕜 := 𝕜) S ((s : 𝕜) • w)
    rw [inner_smul_right, RCLike.re_ofReal_mul, norm_smul, RCLike.norm_ofReal, hs1,
      one_mul] at hexp
    have hw := pow_le_pow_left₀ (norm_nonneg w) (h (Fin.last m)) 2
    rw [Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _), hexp]
    push_cast
    nlinarith

/-- 6A.24 Prove or give a counterexample: if {lit}`‖·‖` is the norm from an inner
product on {lit}`ℝ²`, then there is {lit}`(x, y)` with
{lit}`‖(x, y)‖ ≠ max{|x|, |y|}`. -/
def exercise_6A_24 :
    Decidable (∃ x y : ℝ, ‖(!₂[x, y] : EuclideanSpace ℝ (Fin 2))‖ ≠ max |x| |y|) := by
  apply isTrue
  -- by contra assume that for all x y, ‖(x, y)‖ = max |x| |y|
  by_contra hcon
  push Not at hcon
  -- this breaks the parallelogram equality (6.21) for u = (1, 0), v = (0, 1):
  -- ‖u + v‖² + ‖u − v‖² = 1 + 1, but 2(‖u‖² + ‖v‖²) = 4, giving a contradiction
  have h := parallelogram (𝕜 := ℝ) (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) !₂[0, 1]
  have hadd : (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) + !₂[0, 1] = !₂[1, 1] := by
    ext i; fin_cases i <;> simp
  have hsub : (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) - !₂[0, 1] = !₂[1, -1] := by
    ext i; fin_cases i <;> simp
  rw [hadd, hsub, hcon, hcon, hcon, hcon] at h
  norm_num at h

/-- 6A.25 For {lit}`p > 0`, there is an inner product on {lit}`ℝ²` whose associated
norm is {lit}`‖(x, y)‖ = (|x|ᵖ + |y|ᵖ)^(1/p)` if and only if {lit}`p = 2` (the
parallelogram equality holds for this norm exactly when {lit}`p = 2`). -/
theorem exercise_6A_25 (p : ℝ) (hp : 0 < p) :
    (∃ f : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ, IsRealInnerProduct f ∧
      ∀ v : Fin 2 → ℝ, Real.sqrt (f v v) = (|v 0| ^ p + |v 1| ^ p) ^ (1 / p)) ↔ p = 2 := by
  constructor
  · rintro ⟨f, ⟨hadd, hsmul, hsymm, hpos, -⟩, hnorm⟩
    -- for the otherones observe parallelogram again
    -- (for f it follows from the axioms: expand f(u ± v, u ± v))
    have hexp : ∀ u v, f (u + v) (u + v) = f u u + 2 * f u v + f v v := by
      intro u v
      rw [hadd, hsymm u (u + v), hsymm v (u + v), hadd, hadd, hsymm v u]
      ring
    have hneg : ∀ u v, f u (-v) = -f u v := by
      intro u v
      rw [hsymm, show -v = (-1 : ℝ) • v by simp, hsmul, hsymm]
      ring
    have hnegneg : ∀ v, f (-v) (-v) = f v v := by
      intro v
      rw [hneg, hsymm, hneg, neg_neg]
    have hpar : ∀ u v, f (u + v) (u + v) + f (u - v) (u - v) = 2 * f u u + 2 * f v v := by
      intro u v
      rw [sub_eq_add_neg, hexp, hexp, hneg, hnegneg]
      ring
    have hN : ∀ v, f v v = ((|v 0| ^ p + |v 1| ^ p) ^ (1 / p)) ^ 2 := fun v => by
      rw [← hnorm v, Real.sq_sqrt (hpos v)]
    -- u = (1, 0), v = (0, 1) and check the parallelogram identity
    have h := hpar ![1, 0] ![0, 1]
    -- ||u + v||^2 = ‖(1, 1)‖^2 = 2^2/p
    -- ||u - v||^2 = ‖(1, -1)‖^2 = 2^2/p
    -- ||u||^2 + ||v||^2 = ‖(1, 0)‖^2 + ‖(0, 1)‖^2 = 1 + 1 = 2
    rw [hN, hN, hN (![1, 0]), hN (![0, 1])] at h
    simp [Real.zero_rpow hp.ne'] at h
    -- so 2 * 2 = 2 * 2 ^ 2/p
    have h2 : ((2 : ℝ) ^ p⁻¹) ^ 2 = 2 := by norm_num at h; linarith
    -- 2 ^ 1 = 2 ^ (2/p) -> only works when p = 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h2
    have h3 : p⁻¹ * ((2 : ℕ) : ℝ) = 1 := by
      rwa [← Real.rpow_right_inj (x := 2) (by norm_num) (by norm_num), Real.rpow_one]
    push_cast at h3
    field_simp at h3
    linarith
  -- p = 2 is directly the definition of the standard inner product on ℝ^2
  · rintro rfl
    refine ⟨fun u v => u 0 * v 0 + u 1 * v 1, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro u v w; simp only [Pi.add_apply]; ring
    · intro r u v; simp only [Pi.smul_apply, smul_eq_mul]; ring
    · intro u v; ring
    · intro v; nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1)]
    · intro v hv
      have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      ext i; fin_cases i <;> simp [h0, h1]
    · intro v
      rw [← Real.sqrt_eq_rpow, Real.rpow_two, Real.rpow_two, sq_abs, sq_abs]
      ring_nf

/-- 6A.26 In a real inner product space,
{lit}`⟨u, v⟩ = (‖u + v‖² − ‖u − v‖²)/4`. -/
theorem exercise_6A_26 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) : ⟪u, v⟫_ℝ = (‖u + v‖ ^ 2 - ‖u - v‖ ^ 2) / 4 := by
  -- use the lemma ‖u+v‖^2 = ‖u‖^2 + ‖v‖^2 + 2Re⟨u,v⟩, which in ℝ is just
  -- ‖u+v‖^2 = ‖u‖^2 + ‖v‖^2 + 2⟨u,v⟩
  have h1 := norm_add_sq_expand (𝕜 := ℝ) u v
  -- then ‖u-v‖^2 = ‖u‖^2 + ‖v‖^2 - 2⟨u,v⟩
  have h2 := norm_sub_sq_expand (𝕜 := ℝ) u v
  -- so when subbing, we get the desired answer
  rw [RCLike.re_to_real] at h1 h2
  linarith

/-- 6A.27 In a complex inner product space, the complex polarization identity
{lit}`⟨u, v⟩ = (‖u+v‖² − ‖u−v‖² + ‖u+iv‖²i − ‖u−iv‖²i)/4`. Axler's {lit}`⟨u, v⟩` is
mathlib's {lit}`⟪v, u⟫` (the conjugate sits in the first slot), so the identity is
stated for {lit}`⟪v, u⟫_ℂ`. -/
theorem exercise_6A_27 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (u v : V) :
    ⟪v, u⟫_ℂ = (((‖u + v‖ ^ 2 : ℝ) : ℂ) - ((‖u - v‖ ^ 2 : ℝ) : ℂ)
      + ((‖u + Complex.I • v‖ ^ 2 : ℝ) : ℂ) * Complex.I
      - ((‖u - Complex.I • v‖ ^ 2 : ℝ) : ℂ) * Complex.I) / 4 := by
  -- same as 26, use the lemma
  -- (in mathlib's slots: z = ⟪u, v⟫ is Axler's ⟨v, u⟩, and the goal ⟪v, u⟫ is conj z)
  set z := ⟪u, v⟫_ℂ
  -- ‖u+v‖^2 - ‖u-v‖^2 = 4Re⟨u,v⟩
  have hre : ‖u + v‖ ^ 2 - ‖u - v‖ ^ 2 = 4 * z.re := by
    have h1 := norm_add_sq_expand (𝕜 := ℂ) u v
    have h2 := norm_sub_sq_expand (𝕜 := ℂ) u v
    simp only [RCLike.re_to_complex] at h1 h2
    linarith
  -- i(‖u+iv‖^2 - ‖u-iv‖^2) = i(4Re⟨u,iv⟩) = 4iRe⟨u,iv⟩
  -- now Re⟨u, iv⟩ = Re -i ⟨u, v⟩ = Im ⟨u, v⟩
  -- (in mathlib's slots Re ⟪u, i v⟫ = Re (i z) = -Im z = Im (conj z))
  have him : ‖u + Complex.I • v‖ ^ 2 - ‖u - Complex.I • v‖ ^ 2 = -4 * z.im := by
    have h3 := norm_add_sq_expand (𝕜 := ℂ) u (Complex.I • v)
    have h4 := norm_sub_sq_expand (𝕜 := ℂ) u (Complex.I • v)
    rw [inner_smul_right, norm_smul, Complex.norm_I, one_mul] at h3 h4
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub] at h3 h4
    linarith
  -- so i(‖u+iv‖^2 - ‖u-iv‖^2) = 4i Im ⟨u, v⟩
  -- adding the two parts together gives 4⟨u, v⟩, as desired
  calc ⟪v, u⟫_ℂ = (starRingEnd ℂ) z := (inner_conj_symm v u).symm
    _ = (((4 * z.re : ℝ) : ℂ) + ((-4 * z.im : ℝ) : ℂ) * Complex.I) / 4 := by
      apply Complex.ext <;> simp; ring
    _ = _ := by
      rw [← hre, ← him]
      push_cast
      ring

/-- 6A.28 A norm satisfying the parallelogram equality comes from an inner product
(Jordan–von Neumann): if the norm on a vector space {lit}`U` over {lit}`𝐅` satisfies
{lit}`‖u+v‖² + ‖u−v‖² = 2‖u‖² + 2‖v‖²`, then there is an inner product {lit}`f` on
{lit}`U` whose associated norm is {lit}`‖u‖ = √(f u u)`. -/
theorem exercise_6A_28 {U : Type*} [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    (hpar : ∀ u v : U, ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) :
    ∃ f : U → U → 𝕜, IsInnerProductForm f ∧ ∀ u, ‖u‖ = Real.sqrt (RCLike.re (f u u)) := by
  -- use the formula from 27 to define an inner product from the norm only.
  -- (conjugated, to match mathlib's convention of conjugate-linearity in the first slot)
  -- write g u v = ‖u + v‖ ^ 2 - ‖u - v‖ ^ 2 = 4Re⟨u, v⟩, then
  -- ⟨u, v⟩ = (g u v + i g (iu) v) / 4
  obtain ⟨g, hg⟩ : ∃ g : U → U → ℝ, ∀ u v, g u v = ‖u + v‖ ^ 2 - ‖u - v‖ ^ 2 :=
    ⟨fun u v => ‖u + v‖ ^ 2 - ‖u - v‖ ^ 2, fun _ _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : U → U → 𝕜, ∀ u v,
      f u v = ((4⁻¹ * g u v : ℝ) : 𝕜) +
        RCLike.I * ((4⁻¹ * g ((RCLike.I : 𝕜) • u) v : ℝ) : 𝕜) :=
    ⟨fun u v => ((4⁻¹ * g u v : ℝ) : 𝕜) +
      RCLike.I * ((4⁻¹ * g ((RCLike.I : 𝕜) • u) v : ℝ) : 𝕜), fun _ _ => rfl⟩
  -- we can easily show ⟨u, u⟩ = ||u||^2 by subbing and simplifying
  have hnorm : ∀ u, RCLike.re (f u u) = ‖u‖ ^ 2 := by
    intro u
    have h2 : ‖u + u‖ = 2 * ‖u‖ := by
      rw [← two_smul 𝕜 u, norm_smul, RCLike.norm_ofNat]
    rw [hf, hg, h2, sub_self, norm_zero, map_add, RCLike.ofReal_re, mul_comm RCLike.I,
      RCLike.re_ofReal_mul, RCLike.I_re, mul_zero, add_zero]
    ring
  -- need to show the inner product axioms
  -- 1) positivity and definiteness come directly from the norm properties
  have hpos : ∀ v, 0 ≤ RCLike.re (f v v) := fun v => hnorm v ▸ sq_nonneg _
  have hdef : ∀ v, f v v = 0 ↔ v = 0 := by
    intro v
    constructor
    · intro hv
      have := hnorm v
      rw [hv, map_zero] at this
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this.symm)
    -- ⟨0, 0⟩ = 0 directly from the formula
    · rintro rfl
      simp [hf, hg]
  -- 2) prove negation ⟨-u, v⟩ = -⟨u, v⟩ directly by substituting the definition
  have g_neg : ∀ u v, g (-u) v = -g u v := by
    intro u v
    rw [hg, hg, show -u + v = -(u - v) by abel, show -u - v = -(u + v) by abel,
      norm_neg, norm_neg]
    ring
  -- 3) additivity - will prove it over real and imaginary parts separately
  --    for real part first we use
  --    4 * Re⟨u,v⟩ = (‖u + v‖ ^ 2 - ‖u - v‖ ^ 2)
  --    use the following two parallelogram identities:
  --    ‖u + w + v‖ ^ 2 + ‖u + w - v‖ ^ 2 = 2 * ‖u + w‖ ^ 2 + 2 * ‖v‖ ^ 2
  --    ‖u - w + v‖ ^ 2 + ‖u - w - v‖ ^ 2 = 2 * ‖u - w‖ ^ 2 + 2 * ‖v‖ ^ 2
  --    subtracting the two identities gives
  --    ‖u + v + w‖ ^ 2 - ‖u + v - w‖ ^ 2 + (‖u - v + w‖ ^ 2 - ‖u - v - w‖ ^ 2) =
  --    2 * (‖u + w‖ ^ 2 - ‖u - w‖ ^ 2)
  --    4Re⟨u + v, w⟩ + 4Re⟨u - v, w⟩ = 8Re⟨u, w⟩
  have g_mid : ∀ u v w, g (u + v) w + g (u - v) w = 2 * g u w := by
    intro u v w
    have h1 := hpar (u + w) v
    have h2 := hpar (u - w) v
    rw [show u + w + v = u + v + w by abel, show u + w - v = u - v + w by abel] at h1
    rw [show u - w + v = u + v - w by abel, show u - w - v = u - v - w by abel] at h2
    rw [hg, hg, hg]
    linarith
  --    use the same identity with v and u swapped
  --    4Re⟨v + u, w⟩ + 4Re⟨v - u, w⟩ = 8Re⟨v, w⟩
  --    which is, by negation Re⟨v - u, w⟩ = -Re⟨u - v, w⟩,
  --    4Re⟨u + v, w⟩ - 4Re⟨u - v, w⟩ = 8Re⟨v, w⟩
  --    and by adding the two identities and dividing by 8 we get
  --    Re⟨u + v, w⟩ = Re⟨u, w⟩ + Re⟨v, w⟩
  have g_add : ∀ u v w, g (u + v) w = g u w + g v w := by
    intro u v w
    have h1 := g_mid u v w
    have h2 := g_mid v u w
    rw [add_comm v u, show v - u = -(u - v) by abel, g_neg] at h2
    linarith
  --    repeat the same proof for the imaginary part using
  --    4 * Im⟨u,v⟩ = ‖iu + v‖ ^ 2 - ‖iu - v‖ ^ 2 = g (iu) v
  --    (in fact, it is the same proof applied to iu and iv)
  have f_add : ∀ u v w, f (u + v) w = f u w + f v w := by
    intro u v w
    rw [hf, hf, hf, smul_add, g_add, g_add]
    push_cast
    ring
  -- 4) continuity of ⟨r u, v⟩ as a function of r
  --    derive reverse triangle, from the triangle and then
  --    |‖r u + v‖ - ‖s u + v‖| ≤ |(r - s) * ‖u‖| = |r - s| * ‖u‖
  --    thus lipschitz in r, so ‖r u + v‖ is continuous in r
  --    ⟨ru, v⟩ is continuous in r as well as a polynomial function of ‖r u + v‖  --    reverse triangle: ‖x‖ ≤ ‖x - y‖ + ‖y‖ and ‖y‖ ≤ ‖x - y‖ + ‖x‖
  have hrev : ∀ x y : U, |‖x‖ - ‖y‖| ≤ ‖x - y‖ := by
    intro x y
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa using norm_add_le (x - y) y
    have h2 : ‖y‖ ≤ ‖x - y‖ + ‖x‖ := by
      have := norm_add_le (y - x) x
      rwa [sub_add_cancel, norm_sub_rev] at this
    rw [abs_sub_le_iff]
    constructor <;> linarith
  --    each ‖r a + b‖ is lipschitz in r with constant ‖a‖, so take δ = ε / (‖a‖ + 1)
  have hN : ∀ a b : U, Continuous fun r : ℝ => ‖(r : 𝕜) • a + b‖ := by
    intro a b
    rw [Metric.continuous_iff]
    intro s ε hε
    refine ⟨ε / (‖a‖ + 1), by positivity, fun r hr => ?_⟩
    rw [Real.dist_eq] at hr ⊢
    calc |‖(r : 𝕜) • a + b‖ - ‖(s : 𝕜) • a + b‖|
        ≤ ‖((r : 𝕜) • a + b) - ((s : 𝕜) • a + b)‖ := hrev _ _
      _ = |r - s| * ‖a‖ := by
        rw [add_sub_add_right_eq_sub, ← sub_smul, ← RCLike.ofReal_sub, norm_smul,
          RCLike.norm_ofReal]
      _ ≤ |r - s| * (‖a‖ + 1) := by gcongr; linarith
      _ < ε / (‖a‖ + 1) * (‖a‖ + 1) := mul_lt_mul_of_pos_right hr (by positivity)
      _ = ε := by field_simp
  --    the four norms in ⟨r u, v⟩ are all of this form, with (a, b) = (u, ±v), (iu, ±v)
  have f_cont : ∀ u v, Continuous fun r : ℝ => f ((r : 𝕜) • u) v := by
    intro u v
    have key : (fun r : ℝ => f ((r : 𝕜) • u) v) = fun r : ℝ =>
        ((4⁻¹ * (‖(r : 𝕜) • u + v‖ ^ 2 - ‖(r : 𝕜) • u + -v‖ ^ 2) : ℝ) : 𝕜) +
        RCLike.I * ((4⁻¹ * (‖(r : 𝕜) • ((RCLike.I : 𝕜) • u) + v‖ ^ 2 -
          ‖(r : 𝕜) • ((RCLike.I : 𝕜) • u) + -v‖ ^ 2) : ℝ) : 𝕜) := by
      funext r
      rw [hf, hg, hg, smul_comm (RCLike.I : 𝕜) (r : 𝕜) u, sub_eq_add_neg _ v,
        sub_eq_add_neg _ v]
    rw [key]
    exact (RCLike.continuous_ofReal.comp (continuous_const.mul
        (((hN u v).pow 2).sub ((hN u (-v)).pow 2)))).add
      (continuous_const.mul (RCLike.continuous_ofReal.comp (continuous_const.mul
        (((hN _ v).pow 2).sub ((hN _ (-v)).pow 2)))))
  -- 5) homogeniety
  --    first we prove it for integers n by induction
  --    (base) ⟨0 * u, v⟩ = ⟨0, v⟩ = 0 (which can be proven from the formula directly)
  --    thus 0 = 0 * ⟨u, v⟩
  --    (induction) ⟨(n+1) * u, v⟩ = ⟨n * u + u, v⟩ = ⟨n * u, v⟩ + ⟨u, v⟩ = n * ⟨u, v⟩ + ⟨u, v⟩ = (n+1) * ⟨u, v⟩
  have f_nat : ∀ (n : ℕ) u v, f ((n : 𝕜) • u) v = n * f u v := by
    intro n u v
    induction n with
    | zero => simp [hf, hg]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, f_add, ih]; ring
  --    then extend to whole numbers by considering negative integers and negation proven
  have f_neg : ∀ u v, f (-u) v = -f u v := by
    intro u v
    rw [hf, hf, smul_neg, g_neg, g_neg]
    push_cast
    ring
  have f_int : ∀ (n : ℤ) u v, f ((n : 𝕜) • u) v = n * f u v := by
    intro n u v
    cases n with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
      exact f_nat n u v
    | negSucc n =>
      rw [Int.cast_negSucc, neg_smul, f_neg, f_nat]
      push_cast
      ring
  --    then extend to rationals using q = n / m for integers n and m.
  --    m ⟨q * u, v⟩ = ⟨n * u, v⟩ = n * ⟨u, v⟩ = m * (q * ⟨u, v⟩)
  --    thus ⟨q * u, v⟩ = q * ⟨u, v⟩
  have f_rat : ∀ (q : ℚ) u v, f ((q : 𝕜) • u) v = q * f u v := by
    intro q u v
    have hden : (q.den : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    have hq : (q.den : 𝕜) * (q : 𝕜) = q.num := by
      rw [Rat.cast_def]
      field_simp
    apply mul_left_cancel₀ hden
    rw [← f_nat, smul_smul, hq, f_int, Rat.cast_def]
    field_simp
  --    then use continuity to extend to real scalars ⟨r u, v⟩ and r ⟨u, v⟩ are continuous and agree on Q
  --    so they agree on ℝ.
  have f_real : ∀ (r : ℝ) u v, f ((r : 𝕜) • u) v = r * f u v := by
    intro r u v
    have h := Rat.isDenseEmbedding_coe_real.dense.equalizer (f_cont u v)
      (show Continuous fun r : ℝ => (r : 𝕜) * f u v by fun_prop)
      (funext fun q => by simp [f_rat])
    exact congr_fun h r
  --    finally directly show ⟨i * u, v⟩ = -i * ⟨u, v⟩ by subbing the formula
  have f_I : ∀ u v, f ((RCLike.I : 𝕜) • u) v = conj (RCLike.I : 𝕜) * f u v := by
    intro u v
    by_cases hI : (RCLike.I : 𝕜) = 0
    · simp [hI, hf, hg]
    have hI' := RCLike.I_mul_I_of_nonzero hI
    rw [hf, hf, smul_smul, hI', neg_one_smul, g_neg, RCLike.conj_I]
    push_cast
    linear_combination (4⁻¹ * (g ((RCLike.I : 𝕜) • u) v : 𝕜)) * hI'
  --    by additivity split a complex c into real and imaginary part to
  --    obtain ⟨c * u, v⟩ = conj c * ⟨u, v⟩ for any complex scalar c.
  have f_smul : ∀ (c : 𝕜) u v, f (c • u) v = conj c * f u v := by
    intro c u v
    rw [← RCLike.re_add_im c, add_smul, mul_smul, f_add, f_real, f_real, f_I, map_add,
      map_mul, RCLike.conj_ofReal, RCLike.conj_ofReal]
    ring
  -- 6) conj symmetry --
  --    4⟨u,v⟩ = ‖v + u‖ ^2 - ‖v - u‖^2 + i‖v + iu‖ ^2 - i‖v - iu‖ ^2
  --    = ‖u + v‖ ^2 - (-1)^2 * ‖u - v‖ ^2 + i (i)^2 ‖u - iv‖ ^2 - i (-i)^2 ‖u + iv‖ ^2
  --  using -i*i =1
  --    = ‖u + v‖ ^2 - ‖u - v‖ ^2 - i‖u + iv‖ ^2 + i‖u - iv‖ ^2
  --    = 4 conj ⟨v,u⟩
  have f_conj : ∀ u v, f u v = conj (f v u) := by
    intro u v
    have g_comm : g v u = g u v := by rw [hg, hg, add_comm, norm_sub_rev]
    rw [hf, hf, map_add, map_mul, RCLike.conj_ofReal, RCLike.conj_ofReal, RCLike.conj_I,
      g_comm]
    by_cases hI : (RCLike.I : 𝕜) = 0
    · simp [hI]
    have hI' := RCLike.I_mul_I_of_nonzero hI
    have I_smul : ∀ x : U, ‖(RCLike.I : 𝕜) • x‖ = ‖x‖ := fun x => by
      rw [norm_smul, RCLike.norm_I_of_ne_zero hI, one_mul]
    -- ‖iv + u‖ = ‖i(iv + u)‖ = ‖iu - v‖ and ‖iv - u‖ = ‖iu + v‖
    have h1 : ‖(RCLike.I : 𝕜) • v + u‖ = ‖(RCLike.I : 𝕜) • u - v‖ := by
      rw [← I_smul, smul_add, smul_smul, hI', neg_one_smul, neg_add_eq_sub]
    have h2 : ‖(RCLike.I : 𝕜) • v - u‖ = ‖(RCLike.I : 𝕜) • u + v‖ := by
      rw [← I_smul, smul_sub, smul_smul, hI', neg_one_smul, ← norm_neg]
      congr 1
      abel
    have hgI : g ((RCLike.I : 𝕜) • v) u = -g ((RCLike.I : 𝕜) • u) v := by
      rw [hg, hg, h1, h2]
      ring
    rw [hgI]
    push_cast
    ring
  -- ⟨v, v⟩ is real, since by conj symmetry ⟨v, v⟩ = conj ⟨v, v⟩
  have hreal : ∀ v, RCLike.im (f v v) = 0 := fun v => RCLike.conj_eq_iff_im.mp (f_conj v v).symm
  exact ⟨f, ⟨f_add, f_smul, f_conj, fun v => ⟨hreal v, hpos v⟩, hdef⟩, fun u => by
    rw [hnorm, Real.sqrt_sq (norm_nonneg u)]⟩

/-- 6A.29 If {lit}`V₁, …, Vₘ` are inner product spaces, then
{lit}`⟨(u₁, …), (v₁, …)⟩ = ⟨u₁, v₁⟩ + ⋯ + ⟨uₘ, vₘ⟩` defines an inner product on the
product {lit}`V₁ × ⋯ × Vₘ`. The exercise is to verify the inner-product axioms for
this form: additivity and conjugate homogeneity in the first slot, conjugate
symmetry, positivity, and definiteness. -/
theorem exercise_6A_29 {m : ℕ} (E : Fin m → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)] :
    IsInnerProductForm (fun u v : ∀ i, E i => ∑ i, ⟪u i, v i⟫_𝕜) := by
  -- going through the five axioms
  -- 1) additivity -
  --    ⟨(u1, ..., un) + (v1, ... , vn), (w1, ..., wn)⟩ = ⟨(u1 + v1, ...), (w1, ..., wn)⟩ = ⟨u1, w1⟩ + ⟨v1, w1⟩ + ...
  -- 2) homogeneity under scalar multiplication
  --    ⟨a * (u1, ..., un), (v1, ..., vn)⟩ = ⟨(a * u1, ...), (v1, ..., vn)⟩ = conj a * ⟨(u1, ...), (v1, ..., vn)⟩
  -- 3) conjugate symmetry
  --    ⟨(u1, ..., un), (v1, ..., vn)⟩ = ⟨u1, v1⟩ + ... + ⟨un, vn⟩ = conj (⟨v1, u1⟩ + ... + ⟨vn, un⟩) = conj ⟨(v1, ..., vn), (u1, ..., un)⟩
  -- 4) positivity
  --    ⟨(u1, ..., un), (u1, ..., un)⟩ = ⟨u1, u1⟩ + ... + ⟨un, un⟩, since ⟨ui, ui⟩ ≥ 0 for all i, the sum ≥ 0 too.
  -- 5) definiteness ⟨(u1, ..., un), (u1, ..., un)⟩ = 0 ↔ ∀ i, ⟨ui, ui⟩ = 0 ↔ ∀ i, ui = 0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v w
    simp only [Pi.add_apply, inner_add_left, Finset.sum_add_distrib]
  · intro a u v
    simp only [Pi.smul_apply, inner_smul_left, Finset.mul_sum]
  · intro u v
    rw [map_sum]
    simp only [inner_conj_symm]
  · intro u
    rw [map_sum, map_sum]
    exact ⟨Finset.sum_eq_zero fun i _ => inner_self_im (u i),
      Finset.sum_nonneg fun i _ => inner_self_nonneg⟩
  · intro u
    constructor
    · intro (hu : ∑ i, ⟪u i, u i⟫_𝕜 = 0)
      -- the real parts re ⟨ui, ui⟩ ≥ 0 sum to 0, so each is 0, so each ui = 0
      have hre : ∑ i, RCLike.re ⟪u i, u i⟫_𝕜 = 0 := by rw [← map_sum, hu, map_zero]
      rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => inner_self_nonneg] at hre
      funext i
      exact re_inner_self_nonpos.mp (hre i (Finset.mem_univ i)).le
    · rintro rfl
      simp

/-- 6A.30 The complexification {lit}`V_ℂ` of a real inner product space {lit}`V`
(the {name}`LADR.Section_1B.Complexification` of 1B.8, with {lit}`(u, v)` standing
for {lit}`u + iv`) carries the inner product
{lit}`⟨u+iv, w+ix⟩ = ⟨u,w⟩ + ⟨v,x⟩ + (⟨v,w⟩ − ⟨u,x⟩)i`. -/
noncomputable def complexificationInner {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] : Complexification V → Complexification V → ℂ
  | (u, v), (w, x) => (⟪u, w⟫_ℝ : ℂ) + (⟪v, x⟫_ℝ : ℂ) + ((⟪v, w⟫_ℝ : ℂ) - (⟪u, x⟫_ℝ : ℂ)) * Complex.I

/-- 6A.30 (a) The form above makes {lit}`V_ℂ` (with the complex scalar
multiplication of 1B.8) a complex inner product space. The book's form is linear
in the first slot; {name}`IsInnerProductForm` uses mathlib's convention
(conjugate-linear in the first slot), so it is applied to the form with its
arguments swapped. -/
theorem exercise_6A_30a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    letI := exercise_1B_8 V
    IsInnerProductForm (fun p q : Complexification V => complexificationInner q p) := by
  letI := exercise_1B_8 V
  -- going through the 5 properties, first for the book's form ⟨·,·⟩ (linear in the
  -- first slot), then transfer to the swapped form via conjugate symmetry
  -- 1) additivity
  --   ⟪⟨p1,p2⟩ + ⟨q1,q2⟩, ⟨r1,r2⟩⟫ = ⟪p1 + q1, r1⟫ + ⟪p2 + q2, r2⟫ + ((⟪p2 + q2, r1⟫ - ⟪p1 + q1, r2⟫)i
  --   = ⟪p1, r1⟫ + ⟪q1, r1⟫ + ⟪p2, r2⟫ + ⟪q2, r2⟫ + ((⟪p2, r1⟫ + ⟪q2, r1⟫ - ⟪p1, r2⟫ - ⟪q1, r2⟫)i
  --   = ⟪p1, r1⟫ + ⟪p2, r2⟫ + ((⟪p2, r1⟫ - ⟪p1, r2⟫)i + ⟪q1, r1⟫ + ⟪q2, r2⟫ + ((⟪q2, r1⟫ - ⟪q1, r2⟫)i
  --   = ⟪⟨p1, p2⟩, ⟨r1, r2⟩⟫ + ⟪⟨q1, q2⟩, ⟨r1, r2⟩⟫
  have hadd : ∀ p q r : Complexification V, complexificationInner (p + q) r =
      complexificationInner p r + complexificationInner q r := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩ ⟨r1, r2⟩
    simp only [complexificationInner, inner_add_left]
    push_cast
    ring
  -- 2) homogeneity
  --   c = a + bi acts by c • (p1, p2) = (a p1 - b p2, a p2 + b p1) (1B.8), so
  --   with A = ⟪p1, q1⟫ + ⟪p2, q2⟫ and B = ⟪p2, q1⟫ - ⟪p1, q2⟫, i.e. ⟨p, q⟩ = A + Bi,
  --   ⟪c • ⟨p1, p2⟩, ⟨q1, q2⟩⟫ = ⟪a p1 - b p2, q1⟫ + ⟪a p2 + b p1, q2⟫
  --     + (⟪a p2 + b p1, q1⟫ - ⟪a p1 - b p2, q2⟫)i
  --   = (aA - bB) + (bA + aB)i
  --   = (a + bi)(A + Bi) = c * ⟪⟨p1, p2⟩, ⟨q1, q2⟩⟫
  have hsmul : ∀ (c : ℂ) (p q : Complexification V),
      complexificationInner (c • p) q = c * complexificationInner p q := by
    rintro c ⟨p1, p2⟩ ⟨q1, q2⟩
    change complexificationInner (c.re • p1 - c.im • p2, c.re • p2 + c.im • p1) (q1, q2) = _
    simp only [complexificationInner, inner_sub_left, inner_add_left, real_inner_smul_left]
    conv_rhs => rw [← Complex.re_add_im c]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  -- 3) conjugate symmetry
  --   ⟪⟨p1, p2⟩, ⟨q1, q2⟩⟫ = A + Bi, and the real inner product is symmetric, so
  --   ⟪⟨q1, q2⟩, ⟨p1, p2⟩⟫ = ⟪q1, p1⟫ + ⟪q2, p2⟫ + (⟪q2, p1⟫ - ⟪q1, p2⟫)i
  --   = ⟪p1, q1⟫ + ⟪p2, q2⟫ + (⟪p1, q2⟫ - ⟪p2, q1⟫)i = A - Bi
  --   = conj ⟪⟨p1, p2⟩, ⟨q1, q2⟩⟫
  have hconj : ∀ p q : Complexification V,
      complexificationInner p q = conj (complexificationInner q p) := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩
    simp only [complexificationInner, map_add, map_sub, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    rw [real_inner_comm p1 q1, real_inner_comm p2 q2, real_inner_comm p1 q2,
      real_inner_comm p2 q1]
    ring
  -- 4) positive
  --    ⟪⟨p1, p2⟩, ⟨p1, p2⟩⟫ = ⟪p1, p1⟫ + ⟪p2, p2⟫ + ((⟪p2, p1⟫ - ⟪p1, p2⟫)i
  --    = ⟪p1, p1⟫ + ⟪p2, p2⟫ + 0 (because ⟨p2,p1⟩=⟨p1,p2⟩ for real inner space)
  --    = ‖p1‖² + ‖p2‖², thus real and non-negative
  have hself : ∀ p1 p2 : V,
      complexificationInner (p1, p2) (p1, p2) = ((‖p1‖ ^ 2 + ‖p2‖ ^ 2 : ℝ) : ℂ) := by
    intro p1 p2
    simp only [complexificationInner, real_inner_comm p1 p2, sub_self, zero_mul, add_zero,
      real_inner_self_eq_norm_sq]
    push_cast
    ring
  --  5) definiteness ⟨(p1, p2), (p1, p2)⟩ = 0 ↔ p1 = 0 ∧ p2 = 0
  --    <= trivial
  --    => ⟪p1, p1⟫ + ⟪p2, p2⟫ + ((⟪p2, p1⟫ - ⟪p1, p2⟫)i = 0
  --    so ⟪p1, p1⟫ + ⟪p2, p2⟫ = 0 -> by positive definiteness of ⟪.,.⟫, p1 = 0 ∧ p2 = 0
  have hdef : ∀ p : Complexification V, complexificationInner p p = 0 ↔ p = 0 := by
    rintro ⟨p1, p2⟩
    rw [hself, Complex.ofReal_eq_zero]
    constructor
    · intro h
      have h1 : ‖p1‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p1‖, sq_nonneg ‖p2‖]
      have h2 : ‖p2‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖p1‖, sq_nonneg ‖p2‖]
      rw [sq_eq_zero_iff, norm_eq_zero] at h1 h2
      rw [h1, h2]
      rfl
    · intro h
      rw [Prod.mk_eq_zero] at h
      simp [h.1, h.2]
  -- the swapped form is additive and conjugate homogeneous in its first slot:
  -- ⟨r, p + q⟩ = conj ⟨p + q, r⟩ = conj ⟨p, r⟩ + conj ⟨q, r⟩ = ⟨r, p⟩ + ⟨r, q⟩
  -- ⟨q, c p⟩ = conj ⟨c p, q⟩ = conj c conj ⟨p, q⟩ = conj c ⟨q, p⟩
  refine ⟨fun p q r => ?_, fun c p q => ?_, fun p q => hconj q p, fun p => ?_, hdef⟩
  · dsimp only
    rw [hconj r (p + q), hadd, map_add, ← hconj, ← hconj]
  · dsimp only
    rw [hconj q (c • p), hsmul, map_mul, ← hconj]
  · obtain ⟨p1, p2⟩ := p
    dsimp only
    rw [hself]
    refine ⟨Complex.ofReal_im (‖p1‖ ^ 2 + ‖p2‖ ^ 2), ?_⟩
    rw [RCLike.re_to_complex, Complex.ofReal_re]
    positivity

/-- 6A.30 (b) For {lit}`u, v ∈ V`, the complexification inner product restricts to
the original {lit}`⟨u, v⟩` on {lit}`V` (embedded as {lit}`(u, 0)`), and
{lit}`‖u + iv‖² = ‖u‖² + ‖v‖²`. -/
theorem exercise_6A_30b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) :
    complexificationInner (u, 0) (v, 0) = (⟪u, v⟫_ℝ : ℂ) ∧
      complexificationInner (u, v) (u, v) = ((‖u‖ ^ 2 + ‖v‖ ^ 2 : ℝ) : ℂ) := by
  -- first part is trivial by definition of complexificationInner
  -- ⟨u + iv, u + iv⟩ = ⟨u, u⟩ + ⟨v, v⟩ + ((⟨v, u⟩ - ⟨u, v⟩)i =
  -- = ‖u‖² + ‖v‖² + (⟨v, u⟩ - ⟨u, v⟩)i = ‖u‖² + ‖v‖² + 0i (because ⟨u,v⟩ = ⟨v,u⟩ for real inner)
  refine ⟨?_, ?_⟩
  · simp [complexificationInner]
  · simp only [complexificationInner, real_inner_comm u v, sub_self, zero_mul, add_zero,
      real_inner_self_eq_norm_sq]
    push_cast
    ring

/-- 6A.31 For {lit}`u, v, w ∈ V`,
{lit}`‖w − ½(u+v)‖² = (‖w−u‖² + ‖w−v‖²)/2 − ‖u−v‖²/4`. -/
theorem exercise_6A_31 (u v w : V) :
    ‖w - (2 : 𝕜)⁻¹ • (u + v)‖ ^ 2
      = (‖w - u‖ ^ 2 + ‖w - v‖ ^ 2) / 2 - ‖u - v‖ ^ 2 / 4 := by
  -- apply pallelogram with u = w - u and v = w - v
  -- ‖2w - u - v‖² + ‖u - v‖² = 2‖w - u‖² + 2‖w - v‖²
  -- divide both by 4 and move 4 as 2 inside the ‖ ‖ to get the final result
  have h := parallelogram (𝕜 := 𝕜) (w - u) (w - v)
  have h1 : w - (2 : 𝕜)⁻¹ • (u + v) = (2 : 𝕜)⁻¹ • ((w - u) + (w - v)) := by module
  have h2 : (w - u) - (w - v) = -(u - v) := by abel
  rw [h2, norm_neg] at h
  rw [h1, norm_smul, mul_pow, norm_inv, RCLike.norm_ofNat]
  linarith

/-- 6A.32 If {lit}`E ⊆ V` is closed under midpoints ({lit}`u, v ∈ E ⟹ ½(u+v) ∈ E`),
then for any {lit}`w` there is at most one point of {lit}`E` closest to {lit}`w`. -/
theorem exercise_6A_32 (E : Set V)
    (hE : ∀ u ∈ E, ∀ v ∈ E, (2 : 𝕜)⁻¹ • (u + v) ∈ E) (w : V) :
    ∀ u₁ ∈ E, ∀ u₂ ∈ E, (∀ x ∈ E, ‖w - u₁‖ ≤ ‖w - x‖) →
      (∀ x ∈ E, ‖w - u₂‖ ≤ ‖w - x‖) → u₁ = u₂ := by
  -- by contradiction, assume u and v are two distinct closest points to w in E
  -- thus ‖w - u‖ = ‖w - v‖ and ‖w - e‖ ≥ ‖w - u‖ for all e ∈ E
  -- consider the midpoint m = ½(u + v) ∈ E
  -- by exercise 6A.31, ‖w - m‖² = (‖w - u‖² + ‖w - v‖²)/2 - ‖u - v‖²/4
  -- since ‖w - u‖ = ‖w - v‖, this simplifies to ‖w - m‖² = ‖w - u‖² - ‖u - v‖²/4
  -- but ‖w - m‖² ≥ ‖w - u‖² by minimality, a contradiction
  intro u hu v hv hmu hmv
  by_contra hne
  have heq : ‖w - u‖ = ‖w - v‖ := le_antisymm (hmu v hv) (hmv u hu)
  have hmid := exercise_6A_31 (𝕜 := 𝕜) u v w
  rw [← heq] at hmid
  have hmin : ‖w - u‖ ^ 2 ≤ ‖w - (2 : 𝕜)⁻¹ • (u + v)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hmu _ (hE u hu v hv)) 2
  have hpos : 0 < ‖u - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith

/-- 6A.33 (a) For differentiable {lit}`f, g : ℝ → ℝⁿ`, the product rule for the
inner product: {lit}`⟨f, g⟩′ = ⟨f′, g⟩ + ⟨f, g′⟩`. -/
theorem exercise_6A_33a {n : ℕ} (f g : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    deriv (fun s => ⟪f s, g s⟫_ℝ) t = ⟪deriv f t, g t⟫_ℝ + ⟪f t, deriv g t⟫_ℝ := by
  -- ⟨f,g⟩' = (f1g1 + f2g2 + ... + fngn)' = (f1g1)' + (f2g2)' + ... + (fngn)'
  -- = f1'g1 + f1g1' + f2'g2 + f2g2' + ... + fn'gn + fngn'
  -- = ⟨f', g⟩ + ⟨f, g'⟩
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪x, y⟫_ℝ = ∑ i, x i * y i := by
    intro x y
    simp only [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- the coordinates of a differentiable curve are differentiable, with (h')ᵢ = (hᵢ)'
  have hcoord : ∀ h : ℝ → EuclideanSpace ℝ (Fin n), DifferentiableAt ℝ h t → ∀ i,
      HasDerivAt (fun s => h s i) (deriv h t i) t := fun h hh i =>
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      hh.hasDerivAt
  have hsum : HasDerivAt (fun s => ∑ i, f s i * g s i)
      (∑ i, (deriv f t i * g t i + f t i * deriv g t i)) t :=
    HasDerivAt.fun_sum fun i _ => (hcoord f hf i).mul (hcoord g hg i)
  simp only [hinner]
  rw [hsum.deriv, Finset.sum_add_distrib]

/-- 6A.33 (b) If {lit}`f : ℝ → ℝⁿ` is differentiable with constant norm
{lit}`‖f(t)‖ = c`, then {lit}`⟨f′(t), f(t)⟩ = 0` for every {lit}`t`. -/
theorem exercise_6A_33b {n : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin n))
    (hf : ∀ t, DifferentiableAt ℝ f t) (c : ℝ) (_hc : 0 < c)
    (hnorm : ∀ t, ‖f t‖ = c) (t : ℝ) :
    ⟪deriv f t, f t⟫_ℝ = 0 := by
  -- by a) differentiate both sides
  -- ⟨f,f⟩ = ‖f‖² = c², differentiate both sides to get 2⟪f', f⟫ = 0, hence ⟪f', f⟫ = 0
  have ha := exercise_6A_33a f f t (hf t) (hf t)
  have hconst : (fun s => ⟪f s, f s⟫_ℝ) = fun _ => c ^ 2 := by
    funext s
    rw [real_inner_self_eq_norm_sq, hnorm]
  rw [hconst, deriv_const] at ha
  linarith [real_inner_comm (f t) (deriv f t)]

-- 6A.33 c a curve lying on an n-dimensional sphere has its velocity vector orthogonal to its position vector

/-- 6A.34 Apollonius's identity. For a triangle with a vertex at {lit}`0` and the
other two at {lit}`u, v` — sides {lit}`a = ‖v‖`, {lit}`b = ‖u‖`, {lit}`c = ‖u−v‖`,
and median {lit}`d = ‖½(u+v)‖` to side {lit}`c` — one has
{lit}`a² + b² = ½c² + 2d²`. -/
theorem exercise_6A_34 (u v : V) :
    ‖v‖ ^ 2 + ‖u‖ ^ 2
      = (1 / 2) * ‖u - v‖ ^ 2 + 2 * ‖(2 : 𝕜)⁻¹ • (u + v)‖ ^ 2 := by
  -- just parallelogram identity for u and v, d = (u + v)/2 actually
  -- (2d² = 2 · ¼‖u + v‖² = ½‖u + v‖²)
  have h := parallelogram (𝕜 := 𝕜) u v
  rw [norm_smul, mul_pow, norm_inv, RCLike.norm_ofNat]
  linarith

open LADR.HarmonicPolynomial MvPolynomial in
/-- 6A.35 Every polynomial {lit}`q` on {lit}`ℝⁿ` agrees on the unit sphere with a
harmonic polynomial {lit}`p` (one whose Laplacian {lit}`∑ᵢ ∂²p/∂xᵢ²` vanishes).
The one fact about harmonic functions the book allows you to use — a harmonic
polynomial vanishing on the unit sphere is zero — is
{name}`LADR.HarmonicPolynomial.eq_zero_of_harmonic`. -/
theorem exercise_6A_35 {n : ℕ} (q : MvPolynomial (Fin n) ℝ) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      (∑ i, MvPolynomial.pderiv i (MvPolynomial.pderiv i p) = 0) ∧
      (∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 →
        MvPolynomial.eval x p = MvPolynomial.eval x q) := by
  -- for n = 0 the unit sphere is empty, so p = 0 works
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, by simp, fun x hx => by simp at hx⟩
  -- the idea is to find a polynomial r, s.t. the solution is p = q + (1-‖x‖²) * r
  -- clearly p(x) = q(x) for ‖x‖ = 1, no matter what the choice of r is
  -- so we just need to choose r such that the Laplacian of p vanishes.
  -- the Laplacian of p is the Laplacian of q plus the Laplacian of (1-‖x‖²) * r
  let Lap : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
    ∑ i, (pderiv i : Derivation ℝ (MvPolynomial (Fin n) ℝ) _).toLinearMap ∘ₗ
      (pderiv i : Derivation ℝ (MvPolynomial (Fin n) ℝ) _).toLinearMap
  have hLap : ∀ f, Lap f = ∑ i, pderiv i (pderiv i f) := by
    intro f
    simp [Lap, LinearMap.coe_sum, Finset.sum_apply]
  -- consider the Laplacian of (1-‖x‖²) * r as a linear operator on polynomials of degree
  -- at most the degree m of q. This is a finite-dimensional vector space
  -- and the laplacian lowers the total poly degree by 2, which offsets the ‖x‖² factor
  -- in (1-‖x‖²) * r
  have hLapdeg : ∀ f, (Lap f).totalDegree ≤ f.totalDegree - 2 := by
    intro f
    rw [hLap]
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    have h1 := totalDegree_pderiv_le i (pderiv i f)
    have h2 := totalDegree_pderiv_le i f
    omega
  have hdeg1 : (1 - normSq : MvPolynomial (Fin n) ℝ).totalDegree ≤ 2 := by
    refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    simp
  set m := q.totalDegree
  let W := restrictTotalDegree (Fin n) ℝ m
  let A : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
    Lap ∘ₗ LinearMap.mulLeft ℝ (1 - normSq)
  have hA : ∀ r ∈ W, A r ∈ W := by
    intro r hr
    rw [mem_restrictTotalDegree] at hr ⊢
    have h1 := hLapdeg ((1 - normSq) * r)
    have h2 := totalDegree_mul (1 - normSq : MvPolynomial (Fin n) ℝ) r
    change (Lap ((1 - normSq) * r)).totalDegree ≤ m
    omega
  let T : W →ₗ[ℝ] W := A.restrict hA
  -- so we can solve Laplacian of p = 0 by choosing Laplacian (1 - ‖x‖²) * r = - Laplacian of q
  -- as long as that operator is surjective.
  -- since this is finite-dimensional, surjective is equivalent to injective.
  -- assume laplacian of (1 - ‖x‖²) * r = 0 for some poly r
  -- but since (1 - ‖x‖²) * r vanishes on the unit sphere, by the maximum principle for
  -- harmonic polynomials (HarmonicPolynomial.lean) it must vanish identically,
  -- hence r = 0, proving injectivity of the operator.
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have hu : Lap ((1 - normSq) * (r : MvPolynomial (Fin n) ℝ)) = 0 := congrArg Subtype.val hr
    have hu0 : (1 - normSq) * (r : MvPolynomial (Fin n) ℝ) = 0 :=
      eq_zero_of_harmonic hn _ (by rw [← hLap]; exact hu)
        (fun x hx => by simp [eval_normSq, hx])
    have hne : (1 - normSq : MvPolynomial (Fin n) ℝ) ≠ 0 := fun h => by
      have := congrArg (eval 0) h
      rw [map_sub, map_one, eval_normSq, map_zero] at this
      simp at this
    exact Subtype.ext ((mul_eq_zero.mp hu0).resolve_left hne)
  have hq : -Lap q ∈ W := by
    rw [mem_restrictTotalDegree, totalDegree_neg]
    have := hLapdeg q
    omega
  obtain ⟨r, hr⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨-Lap q, hq⟩
  have hr' : Lap ((1 - normSq) * (r : MvPolynomial (Fin n) ℝ)) = -Lap q :=
    congrArg Subtype.val hr
  refine ⟨q + (1 - normSq) * (r : MvPolynomial (Fin n) ℝ), ?_,
    fun x hx => by simp [eval_normSq, hx]⟩
  rw [← hLap, map_add, hr', add_neg_cancel]

end LADR.Section_6A
