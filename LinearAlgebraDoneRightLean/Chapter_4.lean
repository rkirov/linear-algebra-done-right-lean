import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3F
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Chapter 4: Polynomials
-/

namespace LADR.Chapter_4

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open Module (finrank)

/-! 4.1 Definition: real part {lit}`Re z`, imaginary part {lit}`Im z` -/

example (z : ℂ) : ℝ := z.re
example (z : ℂ) : ℝ := z.im
example (z : ℂ) : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm

/-! 4.2 Definition: complex conjugate {lit}`z̄`, absolute value {lit}`|z|`.

In mathlib the conjugate is the {lit}`conj` notation from the
{lit}`ComplexConjugate` scope. The absolute value is the {lit}`Norm`
notation {lit}`‖z‖ = √(Re z)² + (Im z)²`. -/

open scoped ComplexConjugate

example (z : ℂ) : ℂ := conj z
example (z : ℂ) : conj z = z.re - z.im * Complex.I := by
  apply Complex.ext <;> simp

/-- You should verify that {lit}`z̄ = z` if and only if {lit}`z` is a real
number. -/
example (z : ℂ) : conj z = z ↔ ∃ r : ℝ, z = r := Complex.conj_eq_iff_real

noncomputable example (z : ℂ) : ℝ := ‖z‖
example (z : ℂ) : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) :=
  Complex.norm_eq_sqrt_sq_add_sq z

/-! 4.3 Example: properties of {lit}`3 + 2i`.

{lit}`• |𝑧| = √(3² + 2²) = √13.` -/

example : (3 + 2 * Complex.I : ℂ).re = 3 := by simp
example : (3 + 2 * Complex.I : ℂ).im = 2 := by simp
example : conj (3 + 2 * Complex.I) = 3 - 2 * Complex.I := by
  apply Complex.ext <;> simp
example : ‖(3 + 2 * Complex.I : ℂ)‖ = Real.sqrt 13 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  norm_num

/-! 4.4 Properties of complex numbers — provided by mathlib. -/

example (z : ℂ) : z + conj z = 2 * z.re := by
  apply Complex.ext <;> simp; ring

example (z : ℂ) : z - conj z = 2 * z.im * Complex.I := by
  apply Complex.ext <;> simp; ring

example (z : ℂ) : z * conj z = (‖z‖ : ℂ) ^ 2 := by
  rw [Complex.mul_conj, ← Complex.sq_norm z]
  push_cast
  rfl

example (w z : ℂ) : conj (w + z) = conj w + conj z := map_add _ _ _

example (w z : ℂ) : conj (w * z) = conj w * conj z := map_mul _ _ _

example (z : ℂ) : conj (conj z) = z := by
  apply Complex.ext <;> simp

example (z : ℂ) : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z

example (z : ℂ) : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z

example (z : ℂ) : ‖conj z‖ = ‖z‖ := Complex.norm_conj _

example (w z : ℂ) : ‖w * z‖ = ‖w‖ * ‖z‖ := norm_mul w z

/-- (triangle inequality) -/
example (w z : ℂ) : ‖w + z‖ ≤ ‖w‖ + ‖z‖ := by
  have key : ‖w + z‖ ^ 2 ≤ (‖w‖ + ‖z‖) ^ 2 :=
    calc ‖w + z‖ ^ 2
        _ = ‖w‖ ^ 2 + ‖z‖ ^ 2 + 2 * (w * conj z).re := by
          rw [Complex.sq_norm, Complex.normSq_add, ← Complex.sq_norm w,
            ← Complex.sq_norm z]
        _ ≤ ‖w‖ ^ 2 + ‖z‖ ^ 2 + 2 * ‖w * conj z‖ := by
          gcongr; exact Complex.re_le_norm _
        _ = ‖w‖ ^ 2 + ‖z‖ ^ 2 + 2 * (‖w‖ * ‖z‖) := by
          rw [norm_mul, Complex.norm_conj]
        _ = (‖w‖ + ‖z‖) ^ 2 := by ring
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) key

/-! Zeros of Polynomials.

Following Axler, a polynomial is a formal expression in {lit}`z` of the form
sum of coefficients times powers of {lit}`z`. In mathlib this is
{lit}`Polynomial F`, with evaluation {name}`Polynomial.eval`. -/

variable {F : Type*} [Field F]

/-! 4.5 Definition: zero of a polynomial — mathlib's
{name}`Polynomial.IsRoot`. -/

example (p : Polynomial F) (γ : F) : Prop := p.IsRoot γ

example (p : Polynomial F) (γ : F) : p.IsRoot γ ↔ p.eval γ = 0 :=
  Polynomial.IsRoot.def

/-! 4.6 Each zero of a polynomial corresponds to a degree-one factor -/

theorem isRoot_iff_dvd (p : Polynomial F) (γ : F) :
    p.IsRoot γ ↔ (Polynomial.X - Polynomial.C γ) ∣ p :=
  Polynomial.dvd_iff_isRoot.symm

/-- Axler's quantitative form of 4.6: {lit}`p(λ) = 0` iff there exists
{lit}`q` of degree {lit}`(natDegree p) − 1` with {lit}`p = (X − λ) · q`. -/
theorem isRoot_iff_eq_mul (p : Polynomial F) (γ : F) (m : ℕ) (hm : 1 ≤ m)
    (hp_deg : p.natDegree = m) :
    p.IsRoot γ ↔
      ∃ q : Polynomial F, q.natDegree = m - 1 ∧
        p = (Polynomial.X - Polynomial.C γ) * q := by
  have hp_ne : p ≠ 0 := by
    intro hpz; rw [hpz, Polynomial.natDegree_zero] at hp_deg; omega
  have hxc_ne : (Polynomial.X - Polynomial.C γ : Polynomial F) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero γ
  constructor
  · intro hroot
    have hdvd : (Polynomial.X - Polynomial.C γ) ∣ p :=
      Polynomial.dvd_iff_isRoot.mpr hroot
    obtain ⟨q, hpeq⟩ := hdvd
    have hq_ne : q ≠ 0 := by
      intro hqz; rw [hqz, mul_zero] at hpeq; exact hp_ne hpeq
    refine ⟨q, ?_, hpeq⟩
    have hnd : p.natDegree =
        (Polynomial.X - Polynomial.C γ).natDegree + q.natDegree := by
      rw [hpeq, Polynomial.natDegree_mul hxc_ne hq_ne]
    rw [Polynomial.natDegree_X_sub_C] at hnd
    omega
  · rintro ⟨q, _, hpeq⟩
    rw [Polynomial.IsRoot.def, hpeq]
    simp

/-! 4.8 Degree {lit}`m` implies at most {lit}`m` zeros -/

theorem card_roots_le_natDegree (p : Polynomial F) :
    p.roots.card ≤ p.natDegree := by
  -- Axler 4.8: strong induction on the degree `m` of `p`.
  suffices H : ∀ m, ∀ p : Polynomial F, p.natDegree = m → p.roots.card ≤ m by
    simpa using H p.natDegree p rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hm
    -- If `p = 0` the multiset of roots is empty.
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    -- If `p` has no zeros in `F`, the bound holds trivially.
    rcases eq_or_ne p.roots 0 with h0 | h0
    · simp [h0]
    -- Otherwise pick a zero `lam` and factor `p = (X - lam) * q` (by 4.6).
    obtain ⟨lam, hlam⟩ := Multiset.exists_mem_of_ne_zero h0
    have hroot : p.IsRoot lam := (Polynomial.mem_roots'.mp hlam).2
    obtain ⟨q, hpq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    have hq : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; exact hp hpq
    have hxc : (Polynomial.X - Polynomial.C lam : Polynomial F) ≠ 0 :=
      Polynomial.X_sub_C_ne_zero lam
    -- `deg q = m - 1`, so the induction hypothesis applies to `q`.
    have hdeg : p.natDegree = q.natDegree + 1 := by
      rw [hpq, Polynomial.natDegree_mul hxc hq, Polynomial.natDegree_X_sub_C]; ring
    have hlt : q.natDegree < m := by omega
    -- The zeros of `p` are exactly the zeros of `q` together with `lam`.
    have hroots : p.roots = q.roots + {lam} := by
      rw [hpq, Polynomial.roots_mul (hpq ▸ hp), Polynomial.roots_X_sub_C]
      rw [add_comm]
    calc p.roots.card = q.roots.card + 1 := by rw [hroots]; simp
      _ ≤ q.natDegree + 1 := by have := ih _ hlt q rfl; omega
      _ = m := by omega

/-! Division Algorithm for Polynomials. -/

/-! 4.9 For {lit}`p, s ∈ 𝒫(F)` with {lit}`s ≠ 0`, there exist unique
{lit}`q, r ∈ 𝒫(F)` with {lit}`p = s · q + r` and {lit}`deg r < deg s`. -/

open Polynomial in
theorem division_algorithm (p s : Polynomial F) (hs : s ≠ 0) :
    ∃! qr : Polynomial F × Polynomial F,
      p = s * qr.1 + qr.2 ∧ qr.2.degree < s.degree := by
  classical
  have hsdeg : s.degree = (s.natDegree : WithBot ℕ) := degree_eq_natDegree hs
  -- Existence, by Axler's linear-algebra argument: the map sending a remainder
  -- {lit}`r` (of degree {lit}`< m`) and a quotient {lit}`q` to {lit}`r + s·q` is
  -- an injective linear map between spaces of equal (finite) dimension, hence
  -- onto — the formal counterpart of Axler's "a linearly independent list of the
  -- right length is a basis", so every {lit}`p` is in its image.
  have hex : ∃ q r : Polynomial F, p = s * q + r ∧ r.degree < s.degree := by
    set m := s.natDegree
    set k := p.natDegree + 1 with hk
    set N := m + k with hN
    have finLT : ∀ j : ℕ, Module.finrank F (degreeLT F j) = j := fun j => by
      rw [(degreeLTEquiv F j).finrank_eq, Module.finrank_pi, Fintype.card_fin]
    -- {lit}`Φ (r, q) = r + s · q` on the degree-bounded spaces 𝒫ₘ × 𝒫ₖ.
    set Φ : (degreeLT F m) × (degreeLT F k) →ₗ[F] Polynomial F :=
      (Submodule.subtype _).coprod
        ((LinearMap.mulLeft F s).comp (Submodule.subtype _)) with hΦ
    have happ : ∀ (r : degreeLT F m) (q : degreeLT F k),
        Φ (r, q) = (r : Polynomial F) + s * q := fun r q => by simp [hΦ]
    -- `Φ` is injective: if `r + s·q = 0` with `deg r < m = deg s`, a degree count
    -- forces `q = 0` and then `r = 0`.
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨r, q⟩ hx
      rw [LinearMap.mem_ker, happ] at hx
      have hrlt : (r : Polynomial F).degree < (m : WithBot ℕ) := mem_degreeLT.mp r.2
      have hq0 : (q : Polynomial F) = 0 := by
        by_contra hq
        have heq : (r : Polynomial F) = -(s * q) := by linear_combination hx
        have h1 : (r : Polynomial F).degree = (s * (q : Polynomial F)).degree := by
          rw [heq, degree_neg]
        rw [degree_mul, hsdeg] at h1
        have : (m : WithBot ℕ) ≤ (r : Polynomial F).degree := by
          rw [h1]; exact le_add_of_nonneg_right (zero_le_degree_iff.mpr hq)
        exact absurd (lt_of_le_of_lt this hrlt) (lt_irrefl _)
      have hr0 : (r : Polynomial F) = 0 := by rw [hq0, mul_zero, add_zero] at hx; exact hx
      simp [Submodule.coe_eq_zero.mp hr0, Submodule.coe_eq_zero.mp hq0]
    -- The image lands in 𝒫_N with `N = m + k`, and both have dimension `N`,
    -- so `Φ` is onto 𝒫_N (injective + equal dimension ⟹ surjective).
    have hrange : LinearMap.range Φ ≤ degreeLT F N := by
      rintro _ ⟨⟨r, q⟩, rfl⟩
      rw [mem_degreeLT, happ]
      refine (degree_add_le _ _).trans_lt ?_
      rw [max_lt_iff]
      refine ⟨lt_of_lt_of_le (mem_degreeLT.mp r.2)
        (by exact_mod_cast Nat.le_add_right m k), ?_⟩
      rw [degree_mul, hsdeg]
      calc (m : WithBot ℕ) + (q : Polynomial F).degree
          < (m : WithBot ℕ) + (k : WithBot ℕ) :=
            WithBot.add_lt_add_left (by exact_mod_cast WithBot.coe_ne_bot) (mem_degreeLT.mp q.2)
        _ = (N : WithBot ℕ) := by rw [hN]; push_cast; ring
    have hrangeEq : LinearMap.range Φ = degreeLT F N :=
      Submodule.eq_of_le_of_finrank_eq hrange (by
        rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, finLT, finLT, finLT])
    -- `p ∈ 𝒫_N`, hence `p` is in the image: `p = s·q + r` with `deg r < deg s`.
    have hpN : p ∈ degreeLT F N := by
      rw [mem_degreeLT]
      exact lt_of_le_of_lt degree_le_natDegree (by rw [Nat.cast_lt, hN, hk]; omega)
    rw [← hrangeEq] at hpN
    obtain ⟨⟨r, q⟩, hx⟩ := hpN
    rw [happ] at hx
    exact ⟨q, r, by rw [← hx]; ring, by rw [hsdeg]; exact mem_degreeLT.mp r.2⟩
  -- Uniqueness: if `s·q + r = s·q' + r'` with both remainders of degree `< deg s`,
  -- then `s·(q − q') = r' − r` has degree `< deg s`, forcing `q = q'`, then `r = r'`.
  obtain ⟨q, r, hpqr, hrdeg⟩ := hex
  refine ⟨⟨q, r⟩, ⟨hpqr, hrdeg⟩, ?_⟩
  rintro ⟨q', r'⟩ ⟨hpqr', hrdeg'⟩
  have hkey : s * (q - q') = r' - r := by linear_combination hpqr' - hpqr
  have hqq : q = q' := by
    by_contra hne
    have h2 : s.degree ≤ (s * (q - q')).degree := by
      rw [degree_mul]
      exact le_add_of_nonneg_right (zero_le_degree_iff.mpr (sub_ne_zero.mpr hne))
    rw [hkey] at h2
    exact absurd (lt_of_le_of_lt h2
      (lt_of_le_of_lt (degree_sub_le _ _) (max_lt hrdeg' hrdeg))) (lt_irrefl _)
  have hrr : r' = r := by rw [hqq] at hpqr; linear_combination hpqr - hpqr'
  simp [hqq, hrr]

/-! Factorization of Polynomials over ℂ. -/

/-! 4.12 Fundamental theorem of algebra, first version. mathlib provides
this as {name}`Complex.exists_root`. -/

theorem fundamental_theorem_of_algebra (p : Polynomial ℂ) (hp : 0 < p.degree) :
    ∃ z : ℂ, p.IsRoot z :=
  Complex.exists_root hp

/-! 4.12 (from scratch) Axler proves 4.12 himself, rather than citing it. mathlib's
{name}`Complex.exists_root` uses Liouville's theorem; the proof below instead
reproduces Axler's argument. The continuous map {lit}`z ↦ |p(z)|` attains a global
minimum at some {lit}`ζ` (because {lit}`|p|` is proper —
{name}`Polynomial.exists_forall_norm_le`). If {lit}`p(ζ) ≠ 0`, a "descent" using a
{lit}`k`-th root of {lit}`−p(ζ)/aₖ` (the lowest nonconstant coefficient) produces a
nearby point of strictly smaller modulus, contradicting minimality. As Axler notes,
the proof genuinely uses analysis: that the minimum exists, and that every complex
number has a {lit}`k`-th root. -/

section FtaAxler
open Polynomial

/-- Trailing-term decomposition: {lit}`g = C (g 0) + Xᵏ · g₂` with {lit}`k ≥ 1` and
{lit}`g₂ 0 ≠ 0`, where {lit}`Xᵏ` peels off the lowest nonconstant term. -/
private lemma fta_decomp (g : Polynomial ℂ) (hg : 0 < g.degree) :
    ∃ (k : ℕ) (g₂ : Polynomial ℂ), 1 ≤ k ∧ g₂.eval 0 ≠ 0 ∧
      g = C (g.eval 0) + X ^ k * g₂ := by
  set g₁ := g - C (g.eval 0) with hg1
  have hg1ne : g₁ ≠ 0 := by
    intro h; rw [hg1, sub_eq_zero] at h; rw [h] at hg
    exact absurd hg (not_lt.mpr degree_C_le)
  have hcoeff0 : g₁.coeff 0 = 0 := by
    rw [hg1, coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero, sub_self]
  set k := g₁.natTrailingDegree with hk
  have hk1 : 1 ≤ k := by
    rw [hk]; apply Polynomial.le_natTrailingDegree hg1ne
    intro m hm; have hm0 : m = 0 := by omega
    rw [hm0]; exact hcoeff0
  obtain ⟨g₂, hg2⟩ : X ^ k ∣ g₁ := by
    rw [X_pow_dvd_iff]; intro d hd; exact coeff_eq_zero_of_lt_natTrailingDegree hd
  refine ⟨k, g₂, hk1, ?_, ?_⟩
  · rw [← coeff_zero_eq_eval_zero]
    have hkey : (X ^ k * g₂).coeff k = g₂.coeff 0 := by simpa using coeff_X_pow_mul g₂ k 0
    have hg1k : g₁.coeff k ≠ 0 := by
      have := trailingCoeff_eq_zero.not.mpr hg1ne; rwa [trailingCoeff, ← hk] at this
    rw [← hkey, ← hg2]; exact hg1k
  · rw [← hg2, hg1]; ring

open Complex in
/-- De Moivre's theorem, Axler's starting point:
{lit}`(cos θ + i sin θ)ⁿ = cos (nθ) + i sin (nθ)`. -/
private lemma de_moivre (z : ℂ) (n : ℕ) :
    (Complex.cos z + Complex.sin z * I) ^ n
      = Complex.cos (n * z) + Complex.sin (n * z) * I := by
  rw [← Complex.exp_mul_I, ← Complex.exp_mul_I, ← Complex.exp_nat_mul]
  congr 1; ring

open Complex in
/-- Every complex number has an n-th root: write it in polar form and apply
De Moivre's theorem (Axler's argument). -/
private lemma exists_pow_eq (w : ℂ) {n : ℕ} (hn : n ≠ 0) : ∃ β, β ^ n = w := by
  set θ : ℂ := ↑(Complex.arg w) / ↑n with hθ
  refine ⟨↑(‖w‖ ^ ((n : ℝ)⁻¹)) * (Complex.cos θ + Complex.sin θ * I), ?_⟩
  rw [mul_pow, de_moivre, ← Complex.ofReal_pow, Real.rpow_inv_natCast_pow (norm_nonneg w) hn]
  have hnz : (↑n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hθn : (↑n : ℂ) * θ = ↑(Complex.arg w) := by rw [hθ]; field_simp
  rw [hθn, Complex.norm_mul_cos_add_sin_mul_I]

/-- d'Alembert descent at {lit}`0`: if {lit}`g 0 ≠ 0` and {lit}`g` is nonconstant,
some point has strictly smaller modulus than {lit}`g 0`. -/
private lemma fta_descent_at_zero (g : Polynomial ℂ) (hg : 0 < g.degree)
    (h0 : g.eval 0 ≠ 0) : ∃ z, ‖g.eval z‖ < ‖g.eval 0‖ := by
  obtain ⟨k, g₂, hk1, ha, hdecomp⟩ := fta_decomp g hg
  set c₀ := g.eval 0 with hc0def
  set a := g₂.eval 0 with hadef
  have hk0 : k ≠ 0 := by omega
  -- a k-th root β of -c₀/a (so βᵏ·a = -c₀), obtained from De Moivre's theorem
  obtain ⟨β, hβk⟩ := exists_pow_eq (-c₀ / a) hk0
  have hβka : β ^ k * a = -c₀ := by rw [hβk]; field_simp
  have heval : ∀ z : ℂ, g.eval z = c₀ + z ^ k * g₂.eval z := by
    intro z; rw [hdecomp]; simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
  have hpos : (0:ℝ) < ‖c₀‖ := norm_pos_iff.mpr h0
  -- the error term `‖βᵏ‖·‖g₂(tβ) - a‖` is continuous and vanishes at t = 0
  have hcont : Continuous (fun t : ℝ => ‖β ^ k‖ * ‖g₂.eval (↑t * β) - a‖) := by
    apply continuous_const.mul
    apply Continuous.norm
    apply Continuous.sub _ continuous_const
    exact (Polynomial.continuous g₂).comp (Complex.continuous_ofReal.mul continuous_const)
  have hev0 := Filter.Tendsto.eventually_lt (hcont.tendsto 0) tendsto_const_nhds
    (show (fun t : ℝ => ‖β ^ k‖ * ‖g₂.eval (↑t * β) - a‖) 0 < ‖c₀‖ by
      simpa [← hadef] using hpos)
  -- pick a small t ∈ (0, 1) with the error term below ‖c₀‖
  obtain ⟨t, ht0, ht1, htF⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ‖β ^ k‖ * ‖g₂.eval (↑t * β) - a‖ < ‖c₀‖ := by
    have e1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), (0:ℝ) < t := self_mem_nhdsWithin
    have e2base : ∀ᶠ t in nhds (0:ℝ), t < 1 := Iio_mem_nhds (by norm_num)
    have e2 := e2base.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    have e3 := hev0.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    exact (e1.and (e2.and e3)).exists
  refine ⟨↑t * β, ?_⟩
  have hsk : (0:ℝ) < t ^ k := pow_pos ht0 k
  have hskle : t ^ k ≤ 1 := pow_le_one₀ ht0.le ht1.le
  have hzk : ((↑t : ℂ) * β) ^ k = ↑(t ^ k) * β ^ k := by rw [mul_pow, Complex.ofReal_pow]
  -- g(tβ) = c₀(1 - tᵏ) + tᵏ·βᵏ·(g₂(tβ) - a)
  have hz : g.eval (↑t * β)
      = c₀ * (1 - ↑(t ^ k)) + ↑(t ^ k) * (β ^ k * (g₂.eval (↑t * β) - a)) := by
    rw [heval, hzk]; linear_combination (↑(t ^ k) : ℂ) * hβka
  have hn1 : ‖(1 : ℂ) - (↑(t ^ k) : ℂ)‖ = 1 - t ^ k := by
    rw [show (1:ℂ) - ↑(t ^ k) = ((1 - t ^ k : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_of_nonneg (by linarith)]
  have hn2 : ‖(↑(t ^ k) : ℂ)‖ = t ^ k := Complex.norm_of_nonneg hsk.le
  rw [hz]
  calc ‖c₀ * (1 - ↑(t ^ k)) + ↑(t ^ k) * (β ^ k * (g₂.eval (↑t * β) - a))‖
      ≤ ‖c₀ * (1 - ↑(t ^ k))‖ + ‖↑(t ^ k) * (β ^ k * (g₂.eval (↑t * β) - a))‖ :=
        norm_add_le _ _
    _ = ‖c₀‖ * (1 - t ^ k) + t ^ k * (‖β ^ k‖ * ‖g₂.eval (↑t * β) - a‖) := by
        rw [norm_mul, norm_mul, norm_mul, hn1, hn2]
    _ < ‖c₀‖ * (1 - t ^ k) + t ^ k * ‖c₀‖ := by nlinarith [htF, hsk]
    _ = ‖c₀‖ := by ring

/-- The descent at an arbitrary point {lit}`ζ`, via the translation
{lit}`g(z) = f(z + ζ)`. -/
private lemma fta_descent_lt (f : Polynomial ℂ) (hf : 0 < f.degree) (ζ : ℂ)
    (hζ : f.eval ζ ≠ 0) : ∃ w, ‖f.eval w‖ < ‖f.eval ζ‖ := by
  set g := f.comp (X + C ζ) with hgdef
  have hgeval : ∀ z, g.eval z = f.eval (z + ζ) := by
    intro z; rw [hgdef, eval_comp, eval_add, eval_X, eval_C]
  have hg0 : g.eval 0 = f.eval ζ := by rw [hgeval, zero_add]
  have hgdeg : 0 < g.degree := by
    rw [← natDegree_pos_iff_degree_pos] at hf ⊢
    rw [hgdef, natDegree_comp, natDegree_X_add_C, mul_one]; exact hf
  obtain ⟨z, hz⟩ := fta_descent_at_zero g hgdeg (by rw [hg0]; exact hζ)
  exact ⟨z + ζ, by rw [← hgeval, ← hg0]; exact hz⟩

/-- 4.12, proved from scratch following Axler (minimum modulus + d'Alembert
descent), independently of mathlib's Liouville-based {name}`Complex.exists_root`. -/
theorem fundamental_theorem_of_algebra_axler (f : Polynomial ℂ) (hf : 0 < f.degree) :
    ∃ z, f.IsRoot z := by
  obtain ⟨ζ, hζmin⟩ := f.exists_forall_norm_le
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw⟩ := fta_descent_lt f hf ζ (hcon ζ)
  exact absurd (hζmin w) (not_le.mpr hw)

end FtaAxler

/-! 4.13 Fundamental theorem of algebra, second version: factorization into
linear factors over {lit}`ℂ`. Stated using a {name}`Multiset` of roots
(closer to Axler's "list of zeros λ₁, …, λₘ"). -/

theorem fta_factorization (p : Polynomial ℂ) :
    Polynomial.C p.leadingCoeff *
      (Multiset.map (fun a => Polynomial.X - Polynomial.C a) p.roots).prod
        = p := by
  by_cases hp : p = 0
  · subst hp; simp
  apply Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
  exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits p))

/-! Factorization of Polynomials over ℝ. -/

/-! 4.14 Polynomials with real coefficients have nonreal zeros in pairs -/

theorem real_coeffs_nonreal_zero_pair
    (p : Polynomial ℂ) (hp_real : ∀ k, (p.coeff k).im = 0) (γ : ℂ)
    (hlam : p.IsRoot γ) : p.IsRoot (conj γ) := by
  rw [Polynomial.IsRoot.def] at hlam ⊢
  -- {lit}`p(λ̄) = conj (p(λ)) = conj 0 = 0`.
  have hcoeff_conj : ∀ k, conj (p.coeff k) = p.coeff k := by
    intro k
    apply Complex.ext
    · simp
    · simp [hp_real k]
  have h : p.eval (conj γ) = conj (p.eval γ) := by
    rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
    rw [Polynomial.sum_def, Polynomial.sum_def, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_mul, map_pow, hcoeff_conj]
  rw [h, hlam, map_zero]

/-! 4.15 {lit}`x² + bx + c` factors over {lit}`ℝ` iff {lit}`b² ≥ 4c`. -/

theorem quadratic_factor (b c : ℝ) :
    (∃ lam₁ lam₂ : ℝ,
      Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c =
        (Polynomial.X - Polynomial.C lam₁) *
        (Polynomial.X - Polynomial.C lam₂)) ↔ b ^ 2 ≥ 4 * c := by
  constructor
  · rintro ⟨lam₁, lam₂, heq⟩
    -- Evaluate at 0 and 1 to extract {lit}`c = lam₁ lam₂` and
    -- {lit}`b = -(lam₁ + lam₂)`. Then
    -- {lit}`b² − 4c = (lam₁ − lam₂)² ≥ 0`.
    have h0 := congrArg (Polynomial.eval 0) heq
    have h1 := congrArg (Polynomial.eval 1) heq
    simp at h0 h1
    have h_sum_lam : lam₁ + lam₂ = -b := by nlinarith
    have h_sq_diff : (lam₁ - lam₂) ^ 2 = b ^ 2 - 4 * c := by
      have h_id : (lam₁ - lam₂) ^ 2 =
          (lam₁ + lam₂) ^ 2 - 4 * (lam₁ * lam₂) := by ring
      rw [h_id, h_sum_lam, ← h0]; ring
    linarith [sq_nonneg (lam₁ - lam₂), h_sq_diff]
  · intro hbc
    have hpos : 0 ≤ b ^ 2 / 4 - c := by linarith
    set d := Real.sqrt (b ^ 2 / 4 - c)
    refine ⟨-b / 2 + d, -b / 2 - d, ?_⟩
    have hd_sq : d * d = b ^ 2 / 4 - c := Real.mul_self_sqrt hpos
    have h_sum_lam : (-b / 2 + d) + (-b / 2 - d) = -b := by ring
    have h_prod_lam : (-b / 2 + d) * (-b / 2 - d) = c := by nlinarith
    have h_sum_C : Polynomial.C (-b / 2 + d) + Polynomial.C (-b / 2 - d) =
        -Polynomial.C b := by
      rw [← Polynomial.C_add, h_sum_lam, Polynomial.C_neg]
    have h_prod_C : Polynomial.C (-b / 2 + d) * Polynomial.C (-b / 2 - d) =
        Polynomial.C c := by
      rw [← Polynomial.C_mul, h_prod_lam]
    linear_combination Polynomial.X * h_sum_C - h_prod_C

/-! 4.16 Factorization of a polynomial over {lit}`ℝ`.

Strong induction on {lit}`p.natDegree`. Base case: {lit}`natDegree 0`
gives {lit}`p = C c`. Inductive step splits on whether {lit}`p` has a
real root: if yes, peel off {lit}`(X − λ)` and recurse; if no, by FTA
{lit}`p` has a nonreal complex root {lit}`z`, and the quadratic
{lit}`X² − (2 Re z) X + |z|²` divides {lit}`p` (mathlib's
{name}`Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero`); peel that
off and recurse. The discriminant is
{lit}`(2 Re z)² − 4|z|² = −4(Im z)² < 0`. -/

/-- Helper for 4.16: a quadratic {lit}`X² - C(2α) X + C β` has natDegree 2. -/
private lemma natDegree_quadratic_aux (α β : ℝ) :
    (Polynomial.X ^ 2 - Polynomial.C (2 * α) * Polynomial.X +
      Polynomial.C β).natDegree = 2 := by
  have hform :
      Polynomial.X ^ 2 - Polynomial.C (2 * α) * Polynomial.X + Polynomial.C β =
      Polynomial.C 1 * Polynomial.X ^ 2 +
        Polynomial.C (-(2 * α)) * Polynomial.X + Polynomial.C β := by
    rw [Polynomial.C_neg, Polynomial.C_1]; ring
  rw [hform]
  exact Polynomial.natDegree_quadratic one_ne_zero

/-- Helper for 4.16: if {lit}`p : ℝ[X]` has no real root and {lit}`z : ℂ`
is a root of the lift of {lit}`p` to {lit}`ℂ[X]`, then {lit}`z.im ≠ 0`. -/
private lemma complex_root_nonreal_of_no_real_root (p : Polynomial ℝ)
    (hreal : ∀ x : ℝ, ¬ p.IsRoot x) {z : ℂ}
    (hz : (p.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im ≠ 0 := by
  intro hzim
  -- {lit}`z = z.re` (as a complex number with zero imaginary part).
  have hz_eq : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hzim]
  -- Evaluate the lift at {lit}`z.re`.
  refine hreal z.re ?_
  rw [Polynomial.IsRoot.def]
  have hpC_eval : (p.map (algebraMap ℝ ℂ)).eval ((z.re : ℂ)) = 0 := by
    rw [hz_eq]; exact hz
  rw [Polynomial.eval_map] at hpC_eval
  -- {lit}`eval₂ (algebraMap ℝ ℂ) (z.re : ℂ) p = (algebraMap ℝ ℂ) (p.eval z.re)`.
  rw [show ((z.re : ℝ) : ℂ) = (algebraMap ℝ ℂ) z.re from rfl,
      Polynomial.eval₂_at_apply] at hpC_eval
  -- {lit}`algebraMap ℝ ℂ = Complex.ofReal`, which is injective.
  have hcast : ((Polynomial.eval z.re p : ℝ) : ℂ) = 0 := hpC_eval
  exact_mod_cast hcast

/-- Helper for 4.16: the discriminant {lit}`(2 Re z)² - 4|z|²` is negative
when {lit}`z.im ≠ 0`. -/
private lemma discriminant_neg_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    (-(2 * z.re)) ^ 2 < 4 * ‖z‖ ^ 2 := by
  have hsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hsq]
  have him_pos : 0 < z.im ^ 2 := by positivity
  nlinarith

/-! 4.16 Factorization of a polynomial over {lit}`ℝ`.

Strong induction on {lit}`p.natDegree`. Base case: {lit}`natDegree 0`
gives {lit}`p = C c`. Inductive step splits on whether {lit}`p` has a
real root: if yes, peel off {lit}`(X − λ)` and recurse; if no, by FTA
{lit}`p` has a nonreal complex root {lit}`z`, and the quadratic
{lit}`X² − (2 Re z) X + |z|²` divides {lit}`p` (mathlib's
{name}`Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero`); peel that
off and recurse. -/

theorem real_polynomial_factorization (p : Polynomial ℝ) (hp : p ≠ 0) :
    ∃ (c : ℝ) (m M : ℕ) (lams : Fin m → ℝ) (bs cs : Fin M → ℝ),
      (∀ k, bs k ^ 2 < 4 * cs k) ∧
      p = Polynomial.C c *
        (∏ k, (Polynomial.X - Polynomial.C (lams k))) *
        (∏ k, (Polynomial.X ^ 2 + Polynomial.C (bs k) * Polynomial.X +
          Polynomial.C (cs k))) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn_zero | hn_pos
    · -- Base case: {lit}`natDegree p = 0`, so {lit}`p = C (p.coeff 0)`.
      subst hn_zero
      refine ⟨p.coeff 0, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_⟩
      · intro k; exact k.elim0
      · simp
        exact Polynomial.eq_C_of_natDegree_eq_zero hn
    · classical
      by_cases hreal : ∃ lam : ℝ, p.IsRoot lam
      · -- Peel off a real root: {lit}`p = (X − λ) q`, recurse on q.
        obtain ⟨lam, hlam⟩ := hreal
        obtain ⟨q, hpq⟩ : (Polynomial.X - Polynomial.C lam) ∣ p :=
          Polynomial.dvd_iff_isRoot.mpr hlam
        have hxc_ne : (Polynomial.X - Polynomial.C lam : Polynomial ℝ) ≠ 0 :=
          Polynomial.X_sub_C_ne_zero lam
        have hq_ne : q ≠ 0 := fun hqz => by
          rw [hqz, mul_zero] at hpq; exact hp hpq
        have hq_deg : q.natDegree = n - 1 := by
          have := Polynomial.natDegree_mul hxc_ne hq_ne
          rw [← hpq, Polynomial.natDegree_X_sub_C] at this
          omega
        have hq_lt : q.natDegree < n := by omega
        obtain ⟨c, m', M, lams', bs, cs, hdisc, hfact⟩ :=
          ih q.natDegree hq_lt q hq_ne rfl
        refine ⟨c, m' + 1, M, Fin.cons lam lams', bs, cs, hdisc, ?_⟩
        rw [hpq, hfact]
        have h_prod : ∏ k : Fin (m' + 1),
            (Polynomial.X - Polynomial.C (Fin.cons lam lams' k)) =
            (Polynomial.X - Polynomial.C lam) *
              ∏ i : Fin m', (Polynomial.X - Polynomial.C (lams' i)) := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
        rw [h_prod]
        ring
      · -- No real root: peel off a real quadratic from a nonreal root.
        push Not at hreal
        have hpC_ne : p.map (algebraMap ℝ ℂ) ≠ 0 := by
          rw [Ne, Polynomial.map_eq_zero_iff
            (Complex.ofReal_injective : Function.Injective (algebraMap ℝ ℂ))]
          exact hp
        have hpC_deg : 0 < (p.map (algebraMap ℝ ℂ)).degree := by
          rw [← Polynomial.natDegree_pos_iff_degree_pos,
              Polynomial.natDegree_map]
          omega
        obtain ⟨z, hz⟩ := Complex.exists_root hpC_deg
        rw [Polynomial.IsRoot.def] at hz
        have hz_im : z.im ≠ 0 :=
          complex_root_nonreal_of_no_real_root p hreal hz
        have h_aeval_zero : Polynomial.aeval z p = 0 := by
          rw [Polynomial.aeval_def, ← Polynomial.eval_map]
          exact hz
        obtain ⟨q, hpq⟩ :=
          Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero p h_aeval_zero
            hz_im
        set s : Polynomial ℝ := Polynomial.X ^ 2 -
            Polynomial.C (2 * z.re) * Polynomial.X + Polynomial.C (‖z‖ ^ 2)
            with hs_def
        have hs_deg : s.natDegree = 2 := natDegree_quadratic_aux z.re (‖z‖ ^ 2)
        have hs_ne : s ≠ 0 := fun hsz => by
          rw [hsz, Polynomial.natDegree_zero] at hs_deg; omega
        have hq_ne : q ≠ 0 := fun hqz => by
          rw [hqz, mul_zero] at hpq; exact hp hpq
        have hq_deg : q.natDegree = n - 2 := by
          have h_mul := Polynomial.natDegree_mul hs_ne hq_ne
          rw [← hpq, hs_deg, hn] at h_mul
          omega
        have hq_lt : q.natDegree < n := by omega
        obtain ⟨c, m', M', lams', bs, cs, hdisc, hfact⟩ :=
          ih q.natDegree hq_lt q hq_ne rfl
        refine ⟨c, m', M' + 1, lams',
          Fin.cons (-(2 * z.re)) bs, Fin.cons (‖z‖ ^ 2) cs, ?_, ?_⟩
        · intro k
          induction k using Fin.cases with
          | zero => exact discriminant_neg_of_im_ne_zero hz_im
          | succ k => exact hdisc k
        · rw [hpq, hfact]
          have hs_form : s = Polynomial.X ^ 2 +
              Polynomial.C (-(2 * z.re)) * Polynomial.X +
              Polynomial.C (‖z‖ ^ 2) := by
            show Polynomial.X ^ 2 - Polynomial.C (2 * z.re) * Polynomial.X +
                  Polynomial.C (‖z‖ ^ 2) =
                Polynomial.X ^ 2 + Polynomial.C (-(2 * z.re)) * Polynomial.X +
                  Polynomial.C (‖z‖ ^ 2)
            rw [Polynomial.C_neg]; ring
          have h_prod :
            ∏ k : Fin (M' + 1), (Polynomial.X ^ 2 +
              Polynomial.C (Fin.cons (-(2 * z.re)) bs k) * Polynomial.X +
              Polynomial.C (Fin.cons (‖z‖ ^ 2) cs k)) =
            s * ∏ i : Fin M', (Polynomial.X ^ 2 +
              Polynomial.C (bs i) * Polynomial.X + Polynomial.C (cs i)) := by
            rw [Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [hs_form]
          rw [h_prod]
          ring

/-! 4.16 (uniqueness) Axler also states that the factorization above is unique
"except for the order of the factors". We formalize this: any two such
factorizations have the same leading constant {lit}`c`, and their lists of real
linear factors (and of quadratic factors) agree up to a permutation.

Following Axler, the proof reduces to the complex case (4.13). The real linear
factors are exactly the real roots {lit}`p.roots`. After mapping to {lit}`ℂ[X]`,
each real quadratic {lit}`X² + bX + c` with {lit}`b² < 4c` splits as
{lit}`(X − z)(X − z̄)` for a unique upper-half-plane root {lit}`z`; the multiset
of these complex roots is determined by {lit}`p` (this is the content of 4.13),
and recovering {lit}`(b, c)` from {lit}`z` plus a sorting argument turns the
resulting multiset equalities into the desired index permutations. -/

section RealFactorizationUniqueness
open Polynomial Complex

/-- Helper: the monic quadratic {lit}`X² + bX + c` is monic. -/
private lemma monic_quad_aux (b c : ℝ) : (X ^ 2 + C b * X + C c).Monic := by
  have h : (X ^ 2 + C b * X + C c : Polynomial ℝ) = X ^ 2 + (C b * X + C c) := by ring
  rw [h]
  apply monic_X_pow_add
  compute_degree!

/-- The upper-half-plane root of {lit}`X² + bX + c` (when {lit}`b² < 4c`). -/
private noncomputable def upperRoot (b c : ℝ) : ℂ := ⟨-b / 2, Real.sqrt (c - b ^ 2 / 4)⟩

private lemma upperRoot_im_pos (b c : ℝ) (h : b ^ 2 < 4 * c) : 0 < (upperRoot b c).im := by
  simp only [upperRoot]; exact Real.sqrt_pos.mpr (by nlinarith)

/-- Over {lit}`ℂ`, the quadratic splits into conjugate linear factors (4.14). -/
private lemma quad_map_C_eq (b c : ℝ) (h : b ^ 2 < 4 * c) :
    (X ^ 2 + C b * X + C c).map (algebraMap ℝ ℂ)
      = (X - C (upperRoot b c)) * (X - C (conj (upperRoot b c))) := by
  have hs : Real.sqrt (c - b ^ 2 / 4) ^ 2 = c - b ^ 2 / 4 := Real.sq_sqrt (by nlinarith)
  have h1 : upperRoot b c + conj (upperRoot b c) = -(algebraMap ℝ ℂ b) := by
    apply Complex.ext <;> simp [upperRoot]
  have h2 : upperRoot b c * conj (upperRoot b c) = algebraMap ℝ ℂ c := by
    apply Complex.ext <;> simp [upperRoot] <;> nlinarith [hs]
  have hexp : (X - C (upperRoot b c)) * (X - C (conj (upperRoot b c)))
      = X ^ 2 - C (upperRoot b c + conj (upperRoot b c)) * X
        + C (upperRoot b c * conj (upperRoot b c)) := by rw [C_add, C_mul]; ring
  rw [hexp, h1, h2]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X,
    Polynomial.map_C, C_neg]
  ring

/-- The upper-half-plane root is the unique complex root of the mapped quadratic
that lies strictly above the real axis. -/
private lemma quad_roots_filter (b c : ℝ) (h : b ^ 2 < 4 * c) :
    Multiset.filter (fun z : ℂ => 0 < z.im)
      ((X ^ 2 + C b * X + C c).map (algebraMap ℝ ℂ)).roots = {upperRoot b c} := by
  have hneg : ¬ (0 < (conj (upperRoot b c)).im) := by
    simp only [Complex.conj_im]; exact not_lt.mpr (by linarith [upperRoot_im_pos b c h])
  rw [quad_map_C_eq b c h, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C, Multiset.filter_add, Multiset.filter_singleton,
    Multiset.filter_singleton, if_pos (upperRoot_im_pos b c h), if_neg hneg]
  simp

/-- The upper-half-plane roots of {lit}`∏ (X² + bₖX + cₖ)` mapped to {lit}`ℂ[X]`
are exactly the family {lit}`upperRoot bₖ cₖ`. -/
private lemma upperRoot_filter_roots {n : ℕ} (B D : Fin n → ℝ) (hBD : ∀ k, B k ^ 2 < 4 * D k) :
    Multiset.filter (fun z : ℂ => 0 < z.im)
      ((∏ k, (X ^ 2 + C (B k) * X + C (D k))).map (algebraMap ℝ ℂ)).roots
    = Multiset.map (fun k => upperRoot (B k) (D k)) Finset.univ.val := by
  have hne : (∏ k, (X ^ 2 + C (B k) * X + C (D k)).map (algebraMap ℝ ℂ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun k _ => ?_)
    rw [quad_map_C_eq (B k) (D k) (hBD k)]
    exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  rw [Polynomial.map_prod, Polynomial.roots_prod _ _ hne, Multiset.filter_bind]
  have hfun : (fun k => Multiset.filter (fun z : ℂ => 0 < z.im)
      ((X ^ 2 + C (B k) * X + C (D k)).map (algebraMap ℝ ℂ)).roots)
      = (fun k => ({upperRoot (B k) (D k)} : Multiset ℂ)) :=
    funext fun k => quad_roots_filter (B k) (D k) (hBD k)
  rw [hfun, Multiset.bind_singleton]

/-- Recover {lit}`(b, c)` from the upper-half-plane root. -/
private lemma recover_upperRoot (b c : ℝ) (h : b ^ 2 < 4 * c) :
    (toLex (-2 * (upperRoot b c).re, (upperRoot b c).re ^ 2 + (upperRoot b c).im ^ 2)
      : ℝ ×ₗ ℝ) = toLex (b, c) := by
  have hs : Real.sqrt (c - b ^ 2 / 4) ^ 2 = c - b ^ 2 / 4 := Real.sq_sqrt (by nlinarith)
  simp only [upperRoot]
  congr 1
  rw [Prod.mk.injEq]
  refine ⟨by ring, ?_⟩
  rw [hs]; ring

/-- Helper: two finite families with the same multiset of values differ by a
permutation of the index (extracted via sorting). -/
private lemma exists_perm_of_map_eq {α : Type*} [LinearOrder α] {m m' : ℕ}
    (f : Fin m → α) (g : Fin m' → α)
    (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ σ : Fin m ≃ Fin m', g ∘ σ = f := by
  have hmm : m = m' := by
    have hcard := congrArg Multiset.card h
    simpa using hcard
  subst hmm
  have hperm : (List.ofFn f).Perm (List.ofFn g) := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]; exact h
  have hp2 : (List.ofFn (f ∘ Tuple.sort f)).Perm (List.ofFn (g ∘ Tuple.sort g)) :=
    ((Equiv.Perm.ofFn_comp_perm (Tuple.sort f) f).trans hperm).trans
      (Equiv.Perm.ofFn_comp_perm (Tuple.sort g) g).symm
  have key : f ∘ Tuple.sort f = g ∘ Tuple.sort g := by
    apply List.ofFn_injective
    exact hp2.eq_of_sortedLE
      ((List.sortedLE_ofFn_iff).mpr (Tuple.monotone_sort f))
      ((List.sortedLE_ofFn_iff).mpr (Tuple.monotone_sort g))
  refine ⟨Tuple.sort g * (Tuple.sort f)⁻¹, ?_⟩
  funext i
  have hk := congrFun key.symm ((Tuple.sort f)⁻¹ i)
  simpa [Function.comp_apply, Equiv.Perm.mul_apply] using hk

/-- 4.16 (uniqueness): the real factorization is unique up to reordering of the
factors. -/
theorem real_polynomial_factorization_unique (p : Polynomial ℝ) (hp : p ≠ 0)
    {c c' : ℝ} {m m' M M' : ℕ}
    {lams : Fin m → ℝ} {lams' : Fin m' → ℝ}
    {bs : Fin M → ℝ} {cs : Fin M → ℝ} {bs' : Fin M' → ℝ} {cs' : Fin M' → ℝ}
    (hdisc : ∀ k, bs k ^ 2 < 4 * cs k) (hdisc' : ∀ k, bs' k ^ 2 < 4 * cs' k)
    (hfact : p = C c * (∏ k, (X - C (lams k))) *
      (∏ k, (X ^ 2 + C (bs k) * X + C (cs k))))
    (hfact' : p = C c' * (∏ k, (X - C (lams' k))) *
      (∏ k, (X ^ 2 + C (bs' k) * X + C (cs' k)))) :
    c = c' ∧ ∃ (σ : Fin m ≃ Fin m') (τ : Fin M ≃ Fin M'),
      lams' ∘ σ = lams ∧ bs' ∘ τ = bs ∧ cs' ∘ τ = cs := by
  classical
  -- Leading coefficients: the products of factors are monic, so `c = leadingCoeff p`.
  have hmonP : (∏ k, (X - C (lams k)) : Polynomial ℝ).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hmonQ : (∏ k, (X ^ 2 + C (bs k) * X + C (cs k)) : Polynomial ℝ).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_quad_aux _ _)
  have hmonP' : (∏ k, (X - C (lams' k)) : Polynomial ℝ).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hmonQ' : (∏ k, (X ^ 2 + C (bs' k) * X + C (cs' k)) : Polynomial ℝ).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_quad_aux _ _)
  have hc : p.leadingCoeff = c := by
    rw [hfact, mul_assoc, leadingCoeff_mul, (hmonP.mul hmonQ).leadingCoeff, mul_one, leadingCoeff_C]
  have hc' : p.leadingCoeff = c' := by
    rw [hfact', mul_assoc, leadingCoeff_mul, (hmonP'.mul hmonQ').leadingCoeff, mul_one,
      leadingCoeff_C]
  have hcc : c = c' := by rw [← hc, hc']
  have hc0 : c ≠ 0 := by rw [← hc]; exact leadingCoeff_ne_zero.mpr hp
  -- The real roots of `p` are exactly the `lams` (the quadratics have no real root).
  have hlinroots : ∀ {j : ℕ} (g : Fin j → ℝ),
      (∏ k, (X - C (g k)) : Polynomial ℝ).roots = Multiset.map g Finset.univ.val := by
    intro j g
    have hconv : (∏ k, (X - C (g k)) : Polynomial ℝ)
        = (Multiset.map (fun a => X - C a) (Finset.univ.val.map g)).prod := by
      rw [Multiset.map_map]; exact Finset.prod_eq_multiset_prod _ _
    rw [hconv, Polynomial.roots_multiset_prod_X_sub_C]
  have hquadroots0 : ∀ {j : ℕ} (B D : Fin j → ℝ), (∀ k, B k ^ 2 < 4 * D k) →
      (∏ k, (X ^ 2 + C (B k) * X + C (D k)) : Polynomial ℝ).roots = 0 := by
    intro j B D hBD
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro x hx
    have hr := Polynomial.isRoot_of_mem_roots hx
    rw [IsRoot.def, eval_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨k, -, hk⟩ := hr
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X] at hk
    nlinarith [sq_nonneg (2 * x + B k), hk, hBD k]
  have hplams : p.roots = Multiset.map lams Finset.univ.val := by
    rw [hfact, mul_assoc, roots_C_mul _ hc0,
      roots_mul (mul_ne_zero hmonP.ne_zero hmonQ.ne_zero),
      hlinroots lams, hquadroots0 bs cs hdisc, add_zero]
  have hplams' : p.roots = Multiset.map lams' Finset.univ.val := by
    rw [hfact', mul_assoc, roots_C_mul _ (by rw [← hcc]; exact hc0),
      roots_mul (mul_ne_zero hmonP'.ne_zero hmonQ'.ne_zero),
      hlinroots lams', hquadroots0 bs' cs' hdisc', add_zero]
  have hmaplams : Multiset.map lams Finset.univ.val = Multiset.map lams' Finset.univ.val := by
    rw [← hplams, hplams']
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq lams lams' hmaplams
  -- The products of linear factors agree, hence so do the products of quadratics.
  have hconvlin : ∀ {j : ℕ} (g : Fin j → ℝ), (∏ k, (X - C (g k)) : Polynomial ℝ)
      = (Multiset.map (fun a => X - C a) (Finset.univ.val.map g)).prod :=
    fun {j} g => by rw [Multiset.map_map]; exact Finset.prod_eq_multiset_prod _ _
  have hlineq : (∏ k, (X - C (lams k)) : Polynomial ℝ) = ∏ k, (X - C (lams' k)) := by
    rw [hconvlin lams, hconvlin lams', hmaplams]
  have hquadeq : (∏ k, (X ^ 2 + C (bs k) * X + C (cs k)) : Polynomial ℝ)
      = ∏ k, (X ^ 2 + C (bs' k) * X + C (cs' k)) := by
    apply mul_left_cancel₀ (mul_ne_zero (C_ne_zero.mpr hc0) hmonP.ne_zero)
    calc C c * (∏ k, (X - C (lams k))) * (∏ k, (X ^ 2 + C (bs k) * X + C (cs k)))
        = p := hfact.symm
      _ = C c' * (∏ k, (X - C (lams' k))) * (∏ k, (X ^ 2 + C (bs' k) * X + C (cs' k))) := hfact'
      _ = C c * (∏ k, (X - C (lams k))) * (∏ k, (X ^ 2 + C (bs' k) * X + C (cs' k))) := by
          rw [← hcc, ← hlineq]
  -- The upper-half complex roots of the quadratic part agree (4.13).
  have hUR : Multiset.map (fun k => upperRoot (bs k) (cs k)) Finset.univ.val
      = Multiset.map (fun k => upperRoot (bs' k) (cs' k)) Finset.univ.val := by
    rw [← upperRoot_filter_roots bs cs hdisc, ← upperRoot_filter_roots bs' cs' hdisc', hquadeq]
  -- Recover the `(b, c)` pairs from those roots, then obtain the permutation.
  have hpair : Multiset.map (fun k => (toLex (bs k, cs k) : ℝ ×ₗ ℝ)) Finset.univ.val
      = Multiset.map (fun k => (toLex (bs' k, cs' k) : ℝ ×ₗ ℝ)) Finset.univ.val := by
    have e1 : Multiset.map (fun k => (toLex (bs k, cs k) : ℝ ×ₗ ℝ)) Finset.univ.val
        = Multiset.map (fun z : ℂ => (toLex (-2 * z.re, z.re ^ 2 + z.im ^ 2) : ℝ ×ₗ ℝ))
            (Multiset.map (fun k => upperRoot (bs k) (cs k)) Finset.univ.val) := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro k _
      exact (recover_upperRoot (bs k) (cs k) (hdisc k)).symm
    have e2 : Multiset.map (fun k => (toLex (bs' k, cs' k) : ℝ ×ₗ ℝ)) Finset.univ.val
        = Multiset.map (fun z : ℂ => (toLex (-2 * z.re, z.re ^ 2 + z.im ^ 2) : ℝ ×ₗ ℝ))
            (Multiset.map (fun k => upperRoot (bs' k) (cs' k)) Finset.univ.val) := by
      rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro k _
      exact (recover_upperRoot (bs' k) (cs' k) (hdisc' k)).symm
    rw [e1, e2, hUR]
  obtain ⟨τ, hτ⟩ := exists_perm_of_map_eq
    (fun k => (toLex (bs k, cs k) : ℝ ×ₗ ℝ)) (fun k => (toLex (bs' k, cs' k) : ℝ ×ₗ ℝ)) hpair
  refine ⟨hcc, σ, τ, hσ, ?_, ?_⟩
  · funext k
    have hk := congrArg ofLex (congrFun hτ k)
    simpa using congrArg Prod.fst hk
  · funext k
    have hk := congrArg ofLex (congrFun hτ k)
    simpa using congrArg Prod.snd hk

end RealFactorizationUniqueness

/-! # Exercises -/

/-- 4.1 (a) -/
@[avoiding Complex.add_conj]
theorem exercise_4_1a (z : ℂ) : z + conj z = 2 * z.re := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.re_ofNat,
    Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.conj_im, add_neg_cancel, Complex.mul_im, Complex.re_ofNat,
    Complex.ofReal_im, mul_zero, Complex.im_ofNat, Complex.ofReal_re, zero_mul, add_zero]


/-- 4.1 (b) -/
@[avoiding Complex.sub_conj]
theorem exercise_4_1b (z : ℂ) :
    z - conj z = 2 * z.im * Complex.I := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.conj_re, sub_self, Complex.mul_re, Complex.re_ofNat,
    Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re,
    Complex.mul_im, zero_mul, add_zero, Complex.I_im, mul_one]
  · simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.mul_im, Complex.mul_re,
    Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.I_im, mul_one, zero_mul, add_zero, Complex.I_re]
    ring

/-- `‖z‖² = (Re z)² + (Im z)²`, used in 4.1 (c) and (f). -/
lemma norm_sq_eq_re_sq_add_im_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z), Complex.normSq_apply]
  ring

/-- 4.1 (c) -/
@[avoiding Complex.mul_conj, Complex.sq_norm]
theorem exercise_4_1c (z : ℂ) : z * conj z = (‖z‖ : ℂ) ^ 2 := by
  -- ||z||^2 = z.re^2 + z.im^2
  -- z * conj z = (z.re + z.im * I) * (z.re - z.im * I) = z.re^2 + z.im^2
  rw [← Complex.ofReal_pow, norm_sq_eq_re_sq_add_im_sq]
  apply Complex.ext
  · rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re]; ring
  · rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]; ring

/-- 4.1 (d) -/
@[avoiding map_add, map_mul, RingHom.map_add, RingHom.map_mul, star_add, star_mul']
theorem exercise_4_1d (w z : ℂ) :
    conj (w + z) = conj w + conj z ∧
    conj (w * z) = conj w * conj z := by
  -- (w.re + I * w.im) * (z.re + I * z.im) = (w.re * z.re - w.im * z.im) + I * (w.re * z.im + w.im * z.re)
  -- conj = (w.re * z.re - w.im * z.im) - I * (w.re * z.im + w.im * z.re)
  -- (w.re - I * w.im) * (z.re - I * z.im) =
  -- = (w.re * z.re - w.im * z.im) - I * (w.re * z.im + w.im * z.re)
  constructor
  · apply Complex.ext
    · simp only [Complex.add_re, Complex.conj_re]
    · simp only [Complex.add_im, Complex.conj_im]; ring
  · apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

/-- 4.1 (e) -/
@[avoiding Complex.conj_conj]
theorem exercise_4_1e (z : ℂ) : conj (conj z) = z := by
  apply Complex.ext
  · rw [Complex.conj_re, Complex.conj_re]
  · rw [Complex.conj_im, Complex.conj_im, neg_neg]

/-- 4.1 (f) -/
@[avoiding Complex.abs_re_le_norm, Complex.abs_im_le_norm]
theorem exercise_4_1f (z : ℂ) : |z.re| ≤ ‖z‖ ∧ |z.im| ≤ ‖z‖ := by
  -- show |z.re|^2 ≤ ‖z‖^2 and |z.im|^2 ≤ ‖z‖^2 first then follow by sqrt
  -- |z.re|^2 = z.re^2 ≤ z.re^2 + z.im^2 = ‖z‖^2
  -- |z.im|^2 = z.im^2 ≤ z.re^2 + z.im^2 = ‖z‖^2
  constructor
  · rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, norm_sq_eq_re_sq_add_im_sq]
    linarith [sq_nonneg z.im]
  · rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs, norm_sq_eq_re_sq_add_im_sq]
    linarith [sq_nonneg z.re]

/-- 4.1 (g) -/
@[avoiding Complex.norm_conj]
theorem exercise_4_1g (z : ℂ) : ‖conj z‖ = ‖z‖ := by
  -- follows from ||conj z||^2 = ||z||^2
  -- ||conj z||^2 = z.re^2 + (-z.im)^2 = z.re^2 + z.im^2 = ||z||^2
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_re_sq_add_im_sq,
    norm_sq_eq_re_sq_add_im_sq, Complex.conj_re, Complex.conj_im, neg_sq]

/-- 4.1 (h) -/
@[avoiding norm_mul]
theorem exercise_4_1h (w z : ℂ) : ‖w * z‖ = ‖w‖ * ‖z‖ := by
  -- follows from ||w * z||^2 = ||w||^2 * ||z||^2
  -- ||w * z||^2 = |w * z * conj (w * z)|
  -- = ||w * conj w * z * conj z|| = ||w * conj w|| * ||z * conj z|| = ‖w‖^2 * ‖z‖^2
  have h : ((‖w * z‖ ^ 2 : ℝ) : ℂ) = ((‖w‖ * ‖z‖) ^ 2 : ℝ) := by
    push_cast
    rw [← exercise_4_1c, mul_pow, ← exercise_4_1c, ← exercise_4_1c, (exercise_4_1d w z).2]
    ring
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact Complex.ofReal_injective h

/-- 4.2 Reverse triangle inequality. -/
@[avoiding abs_norm_sub_norm_le]
theorem exercise_4_2 (w z : ℂ) : |‖w‖ - ‖z‖| ≤ ‖w - z‖ := by
  -- apply triangle to w and z - w,
  -- ||w|| + ||z - w|| ≤ ||w + (z - w)|| = ||z||
  -- ||w|| - ||z|| ≤ ||w - z|| (since ||-x|| = ||x||)
  -- by symmetry,
  -- ||z|| - ||w|| ≤ ||w - z||
  -- thus |‖w‖ - ‖z‖| ≤ ‖w - z‖
  have h1 : ‖z‖ - ‖w‖ ≤ ‖w - z‖ := by
    have := norm_add_le w (z - w)
    rw [add_sub_cancel, norm_sub_rev] at this
    linarith
  have h2 : ‖w‖ - ‖z‖ ≤ ‖w - z‖ := by
    have := norm_add_le z (w - z)
    rw [add_sub_cancel] at this
    linarith
  exact abs_sub_le_iff.2 ⟨h2, h1⟩

/-- 4.3 -/
theorem exercise_4_3 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (φ : V →ₗ[ℂ] ℂ) (v : V) :
    φ v = (φ v).re - Complex.I * (φ (Complex.I • v)).re := by
  -- φ v = (φ v).re - I * (φ (I • v)).re
  -- = (φ v).re - I * (I * φ (v)).re (using Re I*c = - Im c)
  -- = (φ v).re + I * (φ (v)).im
  -- = φ v
  rw [map_smul, smul_eq_mul, Complex.I_mul_re, Complex.ofReal_neg, mul_neg, sub_neg_eq_add,
    mul_comm, Complex.re_add_im]

/-- 4.4 -/
def exercise_4_4 (m : ℕ) (hm : 1 ≤ m) :
    Decidable (∃ (U : Submodule F (Polynomial F)),
      ∀ p : Polynomial F, p ∈ U ↔ p = 0 ∨ p.natDegree = m) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- both x^p and -x^p - 1 are in U, but their sum is -1, which is not.
  rintro ⟨U, hU⟩
  have h1 : (Polynomial.X ^ m : Polynomial F) ∈ U :=
    (hU _).2 (Or.inr (Polynomial.natDegree_X_pow m))
  have h2 : (-Polynomial.X ^ m - 1 : Polynomial F) ∈ U := by
    refine (hU _).2 (Or.inr ?_)
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_neg,
      Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_pow, Polynomial.natDegree_one]
    omega
  have h3 := U.add_mem h1 h2
  rw [show (Polynomial.X ^ m + (-Polynomial.X ^ m - 1) : Polynomial F) = -1 by ring] at h3
  rcases (hU _).1 h3 with h | h
  · exact one_ne_zero (neg_eq_zero.1 h)
  · rw [Polynomial.natDegree_neg, Polynomial.natDegree_one] at h
    omega

/-- 4.5 -/
def exercise_4_5 :
    Decidable (∃ (U : Submodule F (Polynomial F)),
      ∀ p : Polynomial F, p ∈ U ↔ p = 0 ∨ Even p.natDegree) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- x^2 and -x^2 + x are in U, but their sum is x, which is not of even degree.
  rintro ⟨U, hU⟩
  have h1 : (Polynomial.X ^ 2 : Polynomial F) ∈ U :=
    (hU _).2 (Or.inr ⟨1, by rw [Polynomial.natDegree_X_pow]⟩)
  have h2 : (-Polynomial.X ^ 2 + Polynomial.X : Polynomial F) ∈ U :=
    (hU _).2 (Or.inr ⟨1, by
      rw [show (-Polynomial.X ^ 2 + Polynomial.X : Polynomial F).natDegree = 2 by
        compute_degree!]⟩)
  have h3 := U.add_mem h1 h2
  rw [add_neg_cancel_left] at h3
  rcases (hU _).1 h3 with h | h
  · exact Polynomial.X_ne_zero h
  · rw [Polynomial.natDegree_X] at h
    exact Nat.not_even_one h

/-- 4.6 The zeros of {lit}`p` are exactly {lit}`Set.range lams`, with {lit}`deg p = n`. -/
theorem exercise_4_6 (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (lams : Fin m → F) :
    ∃ p : Polynomial F, p.natDegree = n ∧ {x | p.IsRoot x} = Set.range lams := by
  -- take (x - λ₁) ⋯ (x - λₘ) (x - λ₁)^(n - m)
  let i₀ : Fin m := ⟨0, hm⟩
  have hq : (∏ i, (Polynomial.X - Polynomial.C (lams i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (lams i)
  have hr : ((Polynomial.X - Polynomial.C (lams i₀)) ^ (n - m)).Monic :=
    (Polynomial.monic_X_sub_C _).pow _
  refine ⟨(∏ i, (Polynomial.X - Polynomial.C (lams i))) *
    (Polynomial.X - Polynomial.C (lams i₀)) ^ (n - m), ?_, ?_⟩
  · rw [hq.natDegree_mul hr, Polynomial.natDegree_prod_of_monic _ _
      fun i _ => Polynomial.monic_X_sub_C (lams i), (Polynomial.monic_X_sub_C _).natDegree_pow]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  · ext x
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      mul_eq_zero, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, pow_eq_zero_iff',
      sub_eq_zero, Set.mem_range]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨rfl, -⟩)
      · exact ⟨i, rfl⟩
      · exact ⟨i₀, rfl⟩
    · rintro ⟨i, rfl⟩
      exact Or.inl ⟨i, rfl⟩

/-- 4.7 Lagrange interpolation. -/
theorem exercise_4_7 {m : ℕ} (z : Fin (m + 1) → F) (hz : Function.Injective z)
    (w : Fin (m + 1) → F) :
    ∃! p : Polynomial.degreeLT F (m + 1),
      ∀ k, (p : Polynomial F).eval (z k) = w k := by
  -- each eval at z k is a unique functional φ_i from P{m+1} -> F
  -- by 3F_25, the map Γ sending a polynomial to its evaluations at z k
  -- is surjective if φi are LI
  -- to show that φi are LI, assume a linear combination ∑ a_i φ_i = 0
  -- evaluate at the polynomial Π {i ≠ j} (z - zi) for each j
  -- that shows aj = 0, and hence all a_i = 0, proving linear independence of φi
  -- uniqueness follows from the injectivity of the evaluation map (3E_25b)
  -- which can be done with dimension count (surjective endomap has to be injective)
  set V := Polynomial.degreeLT F (m + 1)
  have hV : finrank F V = finrank F (Fin (m + 1) → F) :=
    (Polynomial.degreeLTEquiv F (m + 1)).finrank_eq
  haveI : Module.Finite F V := Module.Finite.equiv (Polynomial.degreeLTEquiv F (m + 1)).symm
  -- φ k is evaluation at z k
  let φ : Fin (m + 1) → Module.Dual F V := fun k => (Polynomial.leval (z k)).comp V.subtype
  let Γ : V →ₗ[F] (Fin (m + 1) → F) := LinearMap.pi φ
  have hLI : LinearIndependent F φ := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    -- ℓ = ∏_{i ≠ j} (x - z i), of degree m
    let ℓ : Polynomial F := ∏ i ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (z i))
    have hmonic : ∀ i ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (z i)).Monic :=
      fun i _ => Polynomial.monic_X_sub_C (z i)
    have hℓ : ℓ ∈ V := by
      rw [Polynomial.mem_degreeLT,
        Polynomial.degree_eq_natDegree (Polynomial.monic_prod_of_monic _ _ hmonic).ne_zero,
        Polynomial.natDegree_prod_of_monic _ _ hmonic]
      simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
        Nat.add_sub_cancel]
      exact_mod_cast Nat.lt_succ_self m
    have hφ (i : Fin (m + 1)) : φ i ⟨ℓ, hℓ⟩ = ℓ.eval (z i) := rfl
    -- ℓ vanishes at z i for i ≠ j, but not at z j
    have hzero (i : Fin (m + 1)) (hij : i ≠ j) : ℓ.eval (z i) = 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩) (by simp)
    have hne : ℓ.eval (z j) ≠ 0 := by
      rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro i hi
      simpa [sub_eq_zero] using hz.ne (Finset.ne_of_mem_erase hi).symm
    have h := LinearMap.congr_fun ha ⟨ℓ, hℓ⟩
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, hφ, smul_eq_mul,
      LinearMap.zero_apply] at h
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [hzero i hij, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)] at h
    exact (mul_eq_zero.1 h).resolve_right hne
  have hsurj : Function.Surjective Γ := (LADR.Section_3F.exercise_3F_25 φ).2.1 hLI
  have hinj : Function.Injective Γ :=
    (LADR.Section_3D.injective_iff_surjective hV Γ).2 hsurj
  obtain ⟨p, hp⟩ := hsurj w
  refine ⟨p, fun k => congr_fun hp k, fun q hq => hinj ?_⟩
  rw [hp]
  exact funext hq

open Polynomial in
/-- 4.8 {lit}`p` has {lit}`deg p` distinct zeros iff {lit}`p` and {lit}`p'` have no common zero. -/
theorem exercise_4_8 (p : Polynomial ℂ) (hp : 0 < p.natDegree) :
    p.roots.toFinset.card = p.natDegree ↔
      ∀ z : ℂ, p.IsRoot z → ¬ p.derivative.IsRoot z := by
  -- => if unique roots, p = (z - z₁) * ... * (z - z_n) for distinct z_i
  -- then p' = ∑_{i=1}^n ∏_{j ≠ i} (x - z_j)
  -- so p'(z_i) = ∏_{j ≠ i} (z_i - z_j) ≠ 0 since roots unique for all i
  -- so p and p' have no common roots
  -- <= (by counterpositive) if not unique roots, p = (x - z_i)^2 * r for some root z_i and some polynomial r
  -- p' = 2 * (x - z_i) * r + (x - z_i)^2 * r', so p'(z_i) = 0, which is common root
  classical
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hcard : p.roots.card = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  rw [← hcard, Multiset.toFinset_card_eq_card_iff_nodup]
  constructor
  · intro hnd z hz hz'
    set s := p.roots.toFinset
    have hfac : p = C p.leadingCoeff * ∏ a ∈ s, (X - C a) := by
      conv_lhs => rw [← fta_factorization p]
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnd.dedup]
    have hzs : z ∈ s := Multiset.mem_toFinset.2 ((mem_roots hp0).2 hz)
    rw [hfac, IsRoot.def, derivative_C_mul, derivative_prod_finset, eval_mul, eval_C,
      eval_finset_sum, Finset.sum_eq_single z] at hz'
    · -- p'(z) = c * ∏_{b ≠ z} (z - b) ≠ 0
      simp only [derivative_X_sub_C, mul_one, eval_prod, eval_sub, eval_X, eval_C] at hz'
      rcases mul_eq_zero.1 hz' with h | h
      · exact leadingCoeff_ne_zero.2 hp0 h
      · obtain ⟨b, hb, hb0⟩ := Finset.prod_eq_zero_iff.1 h
        exact Finset.ne_of_mem_erase hb (sub_eq_zero.1 hb0).symm
    · -- the other terms contain the factor (x - z)
      intro b _ hbz
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hbz, hzs⟩)
        (by simp), zero_mul]
    · exact fun h => absurd hzs h
  · intro h
    by_contra hnd
    rw [Multiset.nodup_iff_count_le_one] at hnd
    push Not at hnd
    obtain ⟨z, hz⟩ := hnd
    rw [count_roots] at hz
    obtain ⟨r, hr⟩ := (le_rootMultiplicity_iff hp0 (n := 2)).1 hz
    apply h z
    · rw [hr, IsRoot.def]; simp
    · rw [hr, IsRoot.def]; simp [derivative_mul, derivative_pow]

/-- 4.9 Every odd-degree real polynomial has a real zero. -/
theorem exercise_4_9 (p : Polynomial ℝ) (hp : Odd p.natDegree) :
    ∃ x : ℝ, p.IsRoot x := by
  -- by theorem 4.16, p can be factorized as a product of linear and quadratic factors.
  -- because odd, at least one linear, thus zero
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  obtain ⟨c, m, M, lams, bs, cs, -, hfac⟩ := real_polynomial_factorization p hp0
  rcases m with _ | m
  · -- no linear factors: deg p = 2M is even
    exfalso
    have hc : c ≠ 0 := by rintro rfl; simp [hfac] at hp0
    have hquad : ∀ k ∈ Finset.univ, (Polynomial.X ^ 2 + Polynomial.C (bs k) * Polynomial.X +
        Polynomial.C (cs k)).Monic := fun k _ => by monicity!
    have hdeg : p.natDegree = M * 2 := by
      rw [hfac, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
        Polynomial.natDegree_C_mul hc, Polynomial.natDegree_prod_of_monic _ _ hquad]
      simp only [show ∀ k, (Polynomial.X ^ 2 + Polynomial.C (bs k) * Polynomial.X +
        Polynomial.C (cs k)).natDegree = 2 from fun k => by compute_degree!,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [hdeg, Nat.odd_iff] at hp
    omega
  · -- a linear factor x - λ₀ gives the zero λ₀
    refine ⟨lams 0, ?_⟩
    rw [hfac, Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ 0) (by simp), mul_zero,
      zero_mul]

/-- 4.10 The difference-quotient linear map
{lit}`(Tp)(x) = (p(x) − p(3))/(x − 3)`. The map is stated for the underlying
function; mathlib representation is left to the solver. -/
-- expand p(x) - p(3) = ∑i ai (x^i - 3^i)
-- using x^i - 3^i = (x - 3) * (x^(i-1) + x^(i-2) * 3 + ... + 3^(i-1))
-- p(x) - p(3) = (x - 3) * ∑i ai (x^(i-1) + x^(i-2) * 3 + ... + 3^(i-1))
-- so T(p)(x) = ∑i=1^n ai ∑j=0^(i-1) x^j * 3^i-1-j
-- when x = 3, the second sum simplifies to (i-1) * 3^i-1 which is the definition of derivative.
-- only thing left is to prove that this is a linear map for polynomials.
-- which is clear by observing how ai is used in the forumula for T(p)
noncomputable def exercise_4_10_T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
  Polynomial.lsum fun i => LinearMap.smulRight LinearMap.id
    (∑ j ∈ Finset.range i, Polynomial.X ^ j * Polynomial.C (3 ^ (i - 1 - j)))

/-- {lit}`(Tp)(y) = ∑ᵢ aᵢ ∑_{j<i} yʲ 3^{i-1-j}`. -/
lemma exercise_4_10_T_eval (p : Polynomial ℝ) (y : ℝ) :
    (exercise_4_10_T p).eval y =
      p.sum fun i a => a * ∑ j ∈ Finset.range i, y ^ j * 3 ^ (i - 1 - j) := by
  simp [exercise_4_10_T, Polynomial.lsum_apply, Polynomial.sum, Polynomial.eval_finset_sum]

theorem exercise_4_10a (p : Polynomial ℝ) (x : ℝ) (hx : x ≠ 3) :
    (exercise_4_10_T p).eval x = (p.eval x - p.eval 3) / (x - 3) := by
  rw [eq_div_iff (sub_ne_zero.2 hx), exercise_4_10_T_eval, Polynomial.eval_eq_sum,
    Polynomial.eval_eq_sum, Polynomial.sum, Polynomial.sum, Polynomial.sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- x^i - 3^i = (x - 3) * ∑_{j<i} x^j 3^(i-1-j)
  rw [mul_assoc, geom_sum₂_mul, mul_sub]

theorem exercise_4_10b (p : Polynomial ℝ) :
    (exercise_4_10_T p).eval 3 = p.derivative.eval 3 := by
  rw [exercise_4_10_T_eval, Polynomial.derivative_apply, Polynomial.sum, Polynomial.sum,
    Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- at x = 3 the inner sum is ∑_{j<i} 3^(i-1) = i * 3^(i-1)
  rw [Finset.sum_congr rfl fun j hj => by
      rw [← pow_add, show j + (i - 1 - j) = i - 1 by have := Finset.mem_range.1 hj; omega],
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-- 4.11 (setup) The candidate polynomial {lit}`q = p · p̄`, where
{lit}`p̄ = p.map conj` conjugates the coefficients, satisfies
{lit}`q.eval z = p(z) · conj (p(conj z))` — i.e. it realizes Axler's
{lit}`q(z) = p(z) · conj (p(conj z))` as an honest polynomial.
This solves the first part of exercise 4.11, showing the function is a polynomial. -/
lemma exercise_4_11_eval (p : Polynomial ℂ) (z : ℂ) :
    p.eval z * conj (p.eval (conj z)) = (p * p.map conj).eval z := by
  -- conj preserves + and *, and z = conj (conj z)
  rw [Polynomial.eval_mul, Polynomial.eval_map]
  rw [← Polynomial.eval₂_at_apply, Complex.conj_conj]

/-- 4.11 That polynomial {lit}`q` has real coefficients: every coefficient has
zero imaginary part. -/
theorem exercise_4_11 (p : Polynomial ℂ) :
    ∀ k, ((p * p.map conj).coeff k).im = 0 := by
  -- if p = ∑ ai x^i, then p.map conj = ∑ conj(ai) x^i
  -- so k-th coeff of p * p.map conj is ∑_{i+j=k} a_i * conj(a_j)
  -- to show this sum is real, notice by symmetry
  -- a_i * conj(a_j) + a_j * conj(a_i) is real for all i ≠ j,
  -- as it is a_i * conj(a_j) + conj(a_i * conj(a_j)) (see ex1)
  -- and if i = j, then a_i * conj(a_i) is real as well.
  intro k
  rw [Polynomial.coeff_mul]
  simp_rw [Polynomial.coeff_map]
  -- S = ∑_{i+j=k} a_i * conj(a_j) equals its conjugate: swap i and j
  apply Complex.conj_eq_iff_im.1
  rw [map_sum, ← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [Prod.fst_swap, Prod.snd_swap, map_mul, Complex.conj_conj, mul_comm]

/-- 4.12 -/
theorem exercise_4_12 {m : ℕ} (p : Polynomial.degreeLT ℂ (m + 1))
    (x : Fin (m + 1) → ℝ) (hx : Function.Injective x)
    (hpx : ∀ k, ((p : Polynomial ℂ).eval ((x k : ℝ) : ℂ)).im = 0) :
    ∀ k : ℕ, ((p : Polynomial ℂ).coeff k).im = 0 := by
  -- by ex7, exists a polynomial with real coeff that agrees with p
  -- on the points x k of deg ≤ m. p - that polynomial is a poly,
  -- of degree ≤ m with m + 1 zeros, hence zero, hence p has real coefficients.
  intro k
  -- real interpolant r with r(x k) = p(x k) (which is real)
  obtain ⟨r, hr, -⟩ := exercise_4_7 x hx (fun k => ((p : Polynomial ℂ).eval (x k : ℂ)).re)
  set r' : Polynomial ℂ := (r : Polynomial ℝ).map Complex.ofRealHom
  have hr'mem : r' ∈ Polynomial.degreeLT ℂ (m + 1) := by
    rw [Polynomial.mem_degreeLT]
    exact Polynomial.degree_map_le.trans_lt (Polynomial.mem_degreeLT.1 r.2)
  -- uniqueness in ex 7 over ℂ: p and r' agree at the m + 1 distinct points x k
  obtain ⟨q, -, huniq⟩ := exercise_4_7 (fun k => (x k : ℂ))
    (Complex.ofReal_injective.comp hx) (fun k => (p : Polynomial ℂ).eval (x k))
  have h1 := huniq p fun k => rfl
  have h2 := huniq ⟨r', hr'mem⟩ fun k => by
    change r'.eval (Complex.ofRealHom (x k)) = _
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hr k]
    exact Complex.ext (by simp) (by simp [hpx k])
  have hpr : (p : Polynomial ℂ) = r' := congrArg Subtype.val (h1.trans h2.symm)
  rw [hpr, Polynomial.coeff_map]
  simp

/-- 4.13 The subspace {lit}`U = {p · q : q ∈ 𝒫(F)}`. Mathlib knows that is
  a subspace of {lit}`Polynomial F`. -/
noncomputable def exercise_4_13_U (p : Polynomial F) : Submodule F (Polynomial F) :=
  LinearMap.range (LinearMap.mulLeft F p)

/-- 4.13 The map {lit}`r ↦ r + U` from polynomials of degree {lit}`< deg p` to
{lit}`𝒫(F)/U` is an isomorphism. -/
noncomputable def exercise_4_13_equiv (p : Polynomial F) (hp : p ≠ 0) :
    Polynomial.degreeLT F p.natDegree ≃ₗ[F] (Polynomial F ⧸ exercise_4_13_U p) :=
  LinearEquiv.ofBijective ((exercise_4_13_U p).mkQ ∘ₗ (Polynomial.degreeLT F p.natDegree).subtype)
    ⟨by
      -- unique: if r ∈ U then r = p * s, and deg r < deg p forces s = 0
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨r, hr⟩ h
      rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
      obtain ⟨s, hs⟩ := LinearMap.mem_range.1 h
      replace hs : p * s = r := hs
      refine Subtype.ext ?_
      by_contra hr0
      replace hr0 : r ≠ 0 := hr0
      have hs0 : s ≠ 0 := by rintro rfl; simp [← hs] at hr0
      rw [Polynomial.mem_degreeLT, ← hs, Polynomial.degree_eq_natDegree (mul_ne_zero hp hs0),
        Polynomial.natDegree_mul hp hs0] at hr
      have : p.natDegree + s.natDegree < p.natDegree := by exact_mod_cast hr
      omega,
    by
      -- exists: x = p * q + r with deg r < deg p, and r + U = x + U
      intro x
      induction x using Submodule.Quotient.induction_on with | _ x => ?_
      obtain ⟨⟨q, r⟩, ⟨hx, hr⟩, -⟩ := division_algorithm x p hp
      refine ⟨⟨r, ?_⟩, ?_⟩
      · rwa [Polynomial.mem_degreeLT, ← Polynomial.degree_eq_natDegree hp]
      · rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        exact ⟨-q, by simp [hx]⟩⟩

/-- 4.13 (a) {lit}`dim 𝒫(F)/U = deg p`. -/
-- any coset of U has a representative of degree less than deg p.
-- if x is in the coset, using division with remainder by p, we can write x = q * p + r with deg r < deg p.
-- Then r is a representative of the same coset.
-- to show these are unique, assume q + U = r + U for q, r of deg less than deg p
-- then q - r ∈ U, so q - r = p * s for some s
-- but deg(q - r) < deg p, so s must be zero, hence q = r
-- so P(F)/U is isomorphic to the space of polynomials of degree less than deg p, which has dimension deg p.
-- and basis 1,X,X^2,...,X^(deg p - 1).
theorem exercise_4_13a (p : Polynomial F) (hp : p ≠ 0) :
    finrank F (Polynomial F ⧸ exercise_4_13_U p) = p.natDegree := by
  rw [← (exercise_4_13_equiv p hp).finrank_eq,
    (Polynomial.degreeLTEquiv F p.natDegree).finrank_eq, Module.finrank_fin_fun]

/-- 4.13 (b) -/
noncomputable def exercise_4_13b (p : Polynomial F) (hp : p ≠ 0) :
    Module.Basis (Fin p.natDegree) F (Polynomial F ⧸ exercise_4_13_U p) :=
  -- the image of the basis 1, x, …, x^(deg p - 1) of polynomials of degree < deg p
  (Pi.basisFun F (Fin p.natDegree)).map
    ((Polynomial.degreeLTEquiv F p.natDegree).symm ≪≫ₗ exercise_4_13_equiv p hp)

/-- 4.14 (a) The map {lit}`T(r, s) = r·p + s·q` from
{lit}`𝒫_{n−1}(ℂ) × 𝒫_{m−1}(ℂ)` to {lit}`𝒫_{m+n−1}(ℂ)`.) -/
noncomputable def exercise_4_14_T (m n : ℕ) (p q : Polynomial ℂ)
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    Polynomial.degreeLT ℂ n × Polynomial.degreeLT ℂ m →ₗ[ℂ]
      Polynomial.degreeLT ℂ (m + n) where
  toFun := fun ⟨r, s⟩ => ⟨r.val * p + s.val * q, by
    -- deg (r p) ≤ deg r + deg p < n + m, and likewise for s q
    have key : ∀ {a b : ℕ} (f g : Polynomial ℂ), f ∈ Polynomial.degreeLT ℂ a →
        g.natDegree ≤ b → f * g ∈ Polynomial.degreeLT ℂ (a + b) := by
      intro a b f g hf hg
      by_cases hf0 : f = 0
      · simp [hf0]
      rw [Polynomial.mem_degreeLT] at hf ⊢
      have hfa := (Polynomial.natDegree_lt_iff_degree_lt hf0).2 hf
      calc (f * g).degree ≤ (f * g).natDegree := Polynomial.degree_le_natDegree
        _ ≤ (f.natDegree + g.natDegree : ℕ) := by exact_mod_cast Polynomial.natDegree_mul_le
        _ < (a + b : ℕ) := by exact_mod_cast (by omega : f.natDegree + g.natDegree < a + b)
    refine Submodule.add_mem _ ?_ ?_
    · rw [add_comm]; exact key _ _ r.2 hp
    · exact key _ _ s.2 hq⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    ring
  map_smul' _ _ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply, smul_mul_assoc, smul_add]

theorem exercise_4_14a (p q : Polynomial ℂ) (hpq : ∀ z, ¬ (p.IsRoot z ∧ q.IsRoot z))
    (m n : PNat) (hpdeg : p.natDegree = m) (hqdeg : q.natDegree = n) :
    Function.Injective (exercise_4_14_T m n p q hpdeg.le hqdeg.le) := by
  -- assume rp + sq = 0 for some r and s
  -- then rp = -sq, so each zero of p has to be a zero of s,
  -- but s is of lower degree, so only possible if s = 0, which then leads to rp = 0, and r = 0.
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ h
  have h' : r * p + s * q = 0 := congrArg Subtype.val h
  have hp0 : p ≠ 0 := by rintro rfl; have := m.pos; simp at hpdeg; omega
  have hq0 : q ≠ 0 := by rintro rfl; have := n.pos; simp at hqdeg; omega
  have hs0 : s = 0 := by
    by_contra hs0
    have hsq : -s * q ≠ 0 := mul_ne_zero (neg_ne_zero.2 hs0) hq0
    have hrp : r * p = -s * q := by rw [neg_mul]; exact eq_neg_of_add_eq_zero_left h'
    have hrp0 : r * p ≠ 0 := hrp ▸ hsq
    -- every zero of p is a zero of -s, with at least the same multiplicity
    have hle : p.roots ≤ (-s).roots := by
      classical
      rw [Multiset.le_iff_count]
      intro a
      rw [Polynomial.count_roots, Polynomial.count_roots]
      by_cases hpa : p.IsRoot a
      · have := congrArg (Polynomial.rootMultiplicity a) hrp
        rw [Polynomial.rootMultiplicity_mul hrp0, Polynomial.rootMultiplicity_mul hsq,
          Polynomial.rootMultiplicity_eq_zero (fun hqa => hpq a ⟨hpa, hqa⟩)] at this
        omega
      · rw [Polynomial.rootMultiplicity_eq_zero hpa]
        exact Nat.zero_le _
    -- so deg s ≥ #roots of p = m, contradicting deg s < m
    have h1 := Multiset.card_le_card hle
    rw [IsAlgClosed.card_roots_eq_natDegree, hpdeg] at h1
    have h2 := Polynomial.card_roots' (-s)
    rw [Polynomial.natDegree_neg] at h2
    have h3 := (Polynomial.natDegree_lt_iff_degree_lt hs0).2 (Polynomial.mem_degreeLT.1 hs)
    omega
  subst hs0
  rw [zero_mul, add_zero] at h'
  have hr0 : r = 0 := (mul_eq_zero.1 h').resolve_right hp0
  subst hr0
  rfl

/-- 4.14 (b) The same map is surjective. -/
theorem exercise_4_14b (p q : Polynomial ℂ) (hpq : ∀ z, ¬ (p.IsRoot z ∧ q.IsRoot z))
    (m n : PNat) (hpdeg : p.natDegree = m) (hqdeg : q.natDegree = n) :
    Function.Surjective (exercise_4_14_T m n p q hpdeg.le hqdeg.le) := by
  -- dimension count - so inj -> surj since T is iso between same dim spaces.
  haveI (k : ℕ) : Module.Finite ℂ (Polynomial.degreeLT ℂ k) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℂ k).symm
  have hdeg (k : ℕ) : finrank ℂ (Polynomial.degreeLT ℂ k) = k := by
    rw [(Polynomial.degreeLTEquiv ℂ k).finrank_eq, Module.finrank_fin_fun]
  have hdim : finrank ℂ (Polynomial.degreeLT ℂ n × Polynomial.degreeLT ℂ m) =
      finrank ℂ (Polynomial.degreeLT ℂ (m + n)) := by
    rw [Module.finrank_prod, hdeg, hdeg, hdeg, add_comm]
  exact (LADR.Section_3D.injective_iff_surjective hdim _).1 (exercise_4_14a p q hpq m n hpdeg hqdeg)

/-- 4.14 (c) Bezout: there exist {lit}`r ∈ 𝒫_{n−1}(ℂ)`, {lit}`s ∈ 𝒫_{m−1}(ℂ)`
with {lit}`rp + sq = 1`. -/
theorem exercise_4_14c (p q : Polynomial ℂ) (hp : p.natDegree ≠ 0)
    (hq : q.natDegree ≠ 0) (hpq : ∀ z, ¬ (p.IsRoot z ∧ q.IsRoot z)) :
    ∃ (r : Polynomial.degreeLT ℂ q.natDegree) (s : Polynomial.degreeLT ℂ p.natDegree),
      r.val * p + s.val * q = 1 := by
  -- apply the surjectivity of exercise_4_14_T to 1
  have h1 : (1 : Polynomial ℂ) ∈ Polynomial.degreeLT ℂ (p.natDegree + q.natDegree) := by
    rw [Polynomial.mem_degreeLT, Polynomial.degree_one]
    exact_mod_cast (by omega : 0 < p.natDegree + q.natDegree)
  obtain ⟨⟨r, s⟩, hrs⟩ := exercise_4_14b p q hpq ⟨p.natDegree, Nat.pos_of_ne_zero hp⟩
    ⟨q.natDegree, Nat.pos_of_ne_zero hq⟩ rfl rfl ⟨1, h1⟩
  exact ⟨r, s, congrArg Subtype.val hrs⟩

end LADR.Chapter_4
