module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.Compact

/-!
# Skippable infrastructure: the maximum principle for harmonic polynomials

**A reader of the companion can skip this file entirely.** It contains no Axler
content — it exists only for exercise 6A.35, whose statement says that "the only
fact about harmonic functions that you need" is that a harmonic function on
{lit}`ℝⁿ` vanishing on the unit sphere is zero. Mathlib defines harmonic functions
but does not (yet) have a maximum principle, so we prove the fact here, for
polynomials (which is all 6A.35 needs), with the Laplacian written in terms of
{name}`MvPolynomial.pderiv`.

The proof is the classical one. If {lit}`Δu = 0`, then {lit}`v = u + ε‖x‖²` has
{lit}`Δv = 2nε > 0`, so {lit}`v` has no interior maximum on the closed unit ball
(at an interior maximum every second derivative along a coordinate line is
{lit}`≤ 0`). Its maximum over the (compact) ball is therefore on the sphere, which
bounds {lit}`u ≤ ε` on the ball; letting {lit}`ε → 0` gives {lit}`u ≤ 0`. Applying
this to {lit}`±u` shows {lit}`u` vanishes on the ball, hence everywhere (along each
ray through the origin it is a one-variable polynomial with infinitely many roots).

We also record that a partial derivative lowers the total degree, used to set up
the finite-dimensional linear map in 6A.35.
-/

@[expose] public section

namespace LADR.HarmonicPolynomial

open MvPolynomial Filter Topology

variable {n : ℕ}

/-- A partial derivative lowers the total degree by (at least) one. -/
theorem totalDegree_pderiv_le (i : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  -- monomial by monomial: ∂ᵢ x^s = sᵢ x^(s - eᵢ)
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases hsi : s i = 0
  · simp [hsi]
  · have hle : Finsupp.single i 1 ≤ s :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hsi)
    have hsplit : (s.sum fun _ e => e) = ((s - Finsupp.single i 1).sum fun _ e => e) + 1 := by
      conv_lhs => rw [← tsub_add_cancel_of_le hle]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have := le_totalDegree hs
    refine (totalDegree_monomial_le _ _).trans ?_
    show ((s - Finsupp.single i 1).sum fun _ e => e) ≤ _
    omega

/-- The restriction {lit}`t ↦ u(x + t w)` of {lit}`u` to a line, as a one-variable
polynomial. -/
noncomputable def line (x w : Fin n → ℝ) (u : MvPolynomial (Fin n) ℝ) : Polynomial ℝ :=
  aeval (fun j => Polynomial.C (x j) + Polynomial.C (w j) * Polynomial.X) u

theorem eval_line (x w : Fin n → ℝ) (u : MvPolynomial (Fin n) ℝ) (t : ℝ) :
    (line x w u).eval t = eval (x + t • w) u := by
  induction u using MvPolynomial.induction_on with
  | C a => simp [line]
  | add p q hp hq =>
    simp only [line] at hp hq ⊢
    rw [map_add, Polynomial.eval_add, hp, hq, map_add]
  | mul_X p j hp =>
    simp only [line] at hp ⊢
    rw [map_mul, Polynomial.eval_mul, hp]
    simp only [aeval_X, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, map_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Differentiating the restriction to the {lit}`i`-th coordinate line is taking the
{lit}`i`-th partial derivative. -/
theorem derivative_line (x : Fin n → ℝ) (i : Fin n) (u : MvPolynomial (Fin n) ℝ) :
    Polynomial.derivative (line x (Pi.single i 1) u) = line x (Pi.single i 1) (pderiv i u) := by
  induction u using MvPolynomial.induction_on with
  | C a => simp [line]
  | add p q hp hq =>
    simp only [line] at hp hq ⊢
    rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p j hp =>
    simp only [line] at hp ⊢
    rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, map_add, smul_eq_mul,
      smul_eq_mul, map_mul, map_mul]
    by_cases hji : j = i
    · subst hji
      simp
      ring
    · simp [pderiv_X_of_ne hji, Pi.single_apply, hji]
      ring

/-- {lit}`‖x‖² = ∑ xᵢ²` as a polynomial. -/
noncomputable def normSq : MvPolynomial (Fin n) ℝ := ∑ j, X j ^ 2

theorem eval_normSq (x : Fin n → ℝ) : eval x (normSq (n := n)) = ∑ j, x j ^ 2 := by
  simp [normSq]

theorem pderiv_pderiv_normSq (i : Fin n) : pderiv i (pderiv i (normSq (n := n))) = 2 := by
  simp [normSq, map_sum, Derivation.leibniz_pow, pderiv_X, Pi.single_apply]
  rw [← map_ofNat C 2, pderiv_C]

/-- Weak maximum principle: a harmonic polynomial that is {lit}`≤ 0` on the unit
sphere is {lit}`≤ 0` on the closed unit ball. -/
theorem le_zero_of_harmonic (hn : 0 < n) (u : MvPolynomial (Fin n) ℝ)
    (hΔ : ∑ i, pderiv i (pderiv i u) = 0)
    (hS : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → eval x u ≤ 0)
    (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 ≤ 1) : eval x u ≤ 0 := by
  set K : Set (Fin n → ℝ) := {x | ∑ i, x i ^ 2 ≤ 1} with hK
  have hcont_sq : Continuous fun x : Fin n → ℝ => ∑ i, x i ^ 2 := by fun_prop
  -- the closed unit ball is compact
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont_sq continuous_const)
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun y hy => ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hi := Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    exact hi.trans hy
  apply le_of_forall_pos_le_add
  intro ε hε
  rw [zero_add]
  -- v = u + ε‖x‖² attains its maximum over the ball at some x₀
  set V : MvPolynomial (Fin n) ℝ := u + C ε * normSq with hV
  have hevalV : ∀ y, eval y V = eval y u + ε * ∑ j, y j ^ 2 := by
    intro y
    simp [hV, eval_normSq]
  obtain ⟨x0, hx0K, hmax⟩ := hKc.exists_isMaxOn ⟨0, by simp [K]⟩
    (MvPolynomial.continuous_eval V).continuousOn
  -- x₀ is on the sphere: otherwise Δv(x₀) = 2nε > 0 contradicts maximality
  have hsphere : ∑ j, x0 j ^ 2 = 1 := by
    by_contra hne
    have hlt : ∑ j, x0 j ^ 2 < 1 := lt_of_le_of_ne hx0K hne
    -- restricted to each coordinate line through x₀, v has a local maximum at x₀
    have hlocal : ∀ i, IsLocalMax (fun t => (line x0 (Pi.single i 1) V).eval t) 0 := by
      intro i
      have hc : Continuous fun t : ℝ =>
          ∑ j, (x0 + t • (Pi.single i 1 : Fin n → ℝ)) j ^ 2 := by
        fun_prop
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∑ j, (x0 + t • (Pi.single i 1 : Fin n → ℝ)) j ^ 2 < 1 :=
        hc.continuousAt.eventually_lt continuousAt_const (by simpa using hlt)
      filter_upwards [hev] with t ht
      rw [eval_line, eval_line, zero_smul, add_zero]
      exact isMaxOn_iff.mp hmax _ ht.le
    -- the second derivative along the i-th line is ∂ᵢ²v(x₀)
    have hd2 : ∀ i, deriv (deriv fun t => (line x0 (Pi.single i 1) V).eval t) 0
        = eval x0 (pderiv i (pderiv i V)) := by
      intro i
      have h1 : deriv (fun t => (line x0 (Pi.single i 1) V).eval t)
          = fun t => (Polynomial.derivative (line x0 (Pi.single i 1) V)).eval t :=
        funext fun t => Polynomial.deriv _
      rw [h1, Polynomial.deriv, derivative_line, derivative_line, eval_line, zero_smul,
        add_zero]
    -- Δv = Δu + ε Δ‖x‖² = 2nε
    have hsum : ∑ i, eval x0 (pderiv i (pderiv i V)) = 2 * n * ε := by
      rw [← map_sum]
      simp only [hV, map_add, pderiv_C_mul, Finset.sum_add_distrib, hΔ,
        pderiv_pderiv_normSq, ← Finset.mul_sum]
      simp
      ring
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < eval x0 (pderiv i (pderiv i V)) := by
      by_contra h
      simp only [Finset.mem_univ, true_and, not_exists, not_lt] at h
      have := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => h i
      have : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      nlinarith
    -- so v also has a local minimum along that line, hence is locally constant there,
    -- and its second derivative vanishes — contradiction
    set g := fun t => (line x0 (Pi.single i 1) V).eval t with hg
    have hmin : IsLocalMin g 0 :=
      isLocalMin_of_deriv_deriv_pos (by rw [hd2]; exact hi) (hlocal i).deriv_eq_zero
        (Polynomial.continuous _).continuousAt
    have hconst : g =ᶠ[𝓝 0] fun _ => g 0 := by
      filter_upwards [hlocal i, hmin] with t h1 h2 using le_antisymm h1 h2
    have h0 : deriv (deriv g) 0 = 0 := by
      rw [hconst.deriv.deriv_eq]
      simp
    rw [hd2] at h0
    linarith
  -- so u(x) ≤ v(x) ≤ v(x₀) = u(x₀) + ε ≤ ε
  have h := isMaxOn_iff.mp hmax x hx
  rw [hevalV, hevalV, hsphere] at h
  have : 0 ≤ ε * ∑ j, x j ^ 2 := by positivity
  linarith [hS x0 hsphere]

/-- A harmonic polynomial on {lit}`ℝⁿ` ({lit}`n ≥ 1`) that vanishes on the unit sphere
is zero. -/
theorem eq_zero_of_harmonic (hn : 0 < n) (u : MvPolynomial (Fin n) ℝ)
    (hΔ : ∑ i, pderiv i (pderiv i u) = 0)
    (hS : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 = 1 → eval x u = 0) : u = 0 := by
  -- u vanishes on the closed ball, by the maximum principle applied to ±u
  have hball : ∀ x : Fin n → ℝ, ∑ i, x i ^ 2 ≤ 1 → eval x u = 0 := by
    intro x hx
    have h1 := le_zero_of_harmonic hn u hΔ (fun y hy => (hS y hy).le) x hx
    have h2 := le_zero_of_harmonic hn (-u) (by simp [hΔ, Finset.sum_neg_distrib])
      (fun y hy => by simp [hS y hy]) x hx
    simp at h2
    linarith
  -- along the ray through any y, u is a polynomial with infinitely many roots
  refine MvPolynomial.funext fun y => ?_
  rw [map_zero]
  set s := ∑ i, y i ^ 2
  have hs : 0 ≤ s := by positivity
  have hQ : line 0 y u = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ (Set.Icc_infinite (show (0 : ℝ) < 1 / (1 + s) by positivity))
    intro t ht
    have ht0 := ht.1
    have ht1 : t * (1 + s) ≤ 1 := (le_div_iff₀ (by positivity)).mp ht.2
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, eval_line, zero_add]
    apply hball
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    nlinarith
  have := eval_line 0 y u 1
  rw [hQ, Polynomial.eval_zero, zero_add, one_smul] at this
  exact this.symm

end LADR.HarmonicPolynomial
