import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import Mathlib.Tactic.TFAE
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_3F
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5A: Invariant Subspaces
-/

namespace LADR.Section_5A

open LADR.Section_2B (IsBasis)
open LADR.Section_3D (IsInvertible)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! 5.1 Definition: operator

A linear map from a vector space to itself is called an *operator*;
Axler writes {lit}`ℒ(V) = ℒ(V, V)`. In Lean an operator is simply
{lit}`T : V →ₗ[F] V`; mathlib's {name}`Module.End` is a synomym
for linear endomorphisms. -/

example : Module.End F V = (V →ₗ[F] V) := rfl

/-! 5.2 Definition: invariant subspace -/

/-- A subspace {lit}`U` of {lit}`V` is *invariant under* {lit}`T ∈ ℒ(V)` if
{lit}`Tu ∈ U` for every {lit}`u ∈ U`. -/
def InvariantUnder (T : V →ₗ[F] V) (U : Submodule F V) : Prop :=
  ∀ u ∈ U, T u ∈ U

/-- Equivalently, {lit}`U` is invariant under {lit}`T` iff the image of
{lit}`U` under {lit}`T` is contained in {lit}`U`. (In mathlib the lattice of
invariant submodules is {name}`Module.End.invtSubmodule`.) -/
theorem invariantUnder_iff_map_le (T : V →ₗ[F] V) (U : Submodule F V) :
    InvariantUnder T U ↔ U.map T ≤ U := by
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    exact h u hu
  · intro h u hu
    exact h ⟨u, hu, rfl⟩

/-- Thus {lit}`U` is invariant under {lit}`T` iff {lit}`T` restricts to an
operator {lit}`T|_U ∈ ℒ(U)` — mathlib's {name}`LinearMap.restrict`. -/
noncomputable def InvariantUnder.restrict {T : V →ₗ[F] V} {U : Submodule F V}
    (h : InvariantUnder T U) : U →ₗ[F] U :=
  T.restrict h

@[simp]
theorem InvariantUnder.restrict_apply {T : V →ₗ[F] V} {U : Submodule F V}
    (h : InvariantUnder T U) (u : U) :
    (h.restrict u : V) = T u := rfl

/-! 5.3 Example: {lit}`𝒫₄(ℝ)` (here {lit}`degreeLT ℝ 5`) is invariant under
the differentiation operator {lit}`p ↦ p′` on {lit}`𝒫(ℝ)`, because
differentiation does not raise degree. -/

example : InvariantUnder (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
    (Polynomial.degreeLT ℝ 5) := by
  intro p hp
  rw [Polynomial.mem_degreeLT] at hp ⊢
  exact lt_of_le_of_lt (Polynomial.degree_derivative_le (p := p)) hp

/-! 5.4 Example: four invariant subspaces, not necessarily all different:
{lit}`{0}`, {lit}`V`, {lit}`null T`, {lit}`range T`. (In mathlib's lattice of
submodules we write {lit}`⊥` for {lit}`{0}` and {lit}`⊤` for {lit}`V`.) -/

example (T : V →ₗ[F] V) : InvariantUnder T ⊥ := by
  intro u hu
  rw [Submodule.mem_bot] at hu ⊢
  rw [hu, map_zero]

example (T : V →ₗ[F] V) : InvariantUnder T ⊤ :=
  fun _ _ => Submodule.mem_top

example (T : V →ₗ[F] V) : InvariantUnder T (ker T) := by
  intro u hu
  rw [LinearMap.mem_ker] at hu ⊢
  rw [hu, map_zero]

example (T : V →ₗ[F] V) : InvariantUnder T (range T) :=
  fun u _ => LinearMap.mem_range_self T u

theorem span_singleton_invariant_iff (T : V →ₗ[F] V) {v : V} :
    InvariantUnder T (Submodule.span F {v}) ↔ ∃ γ : F, T v = γ • v := by
  constructor
  · intro h
    have hTv : T v ∈ Submodule.span F {v} :=
      h v (Submodule.mem_span_singleton_self v)
    obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hTv
    exact ⟨lam, hlam.symm⟩
  · rintro ⟨lam, hlam⟩ u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, hlam, smul_smul]
    exact Submodule.mem_span_singleton.mpr ⟨a * lam, rfl⟩

/-! 5.5 Definition: eigenvalue.

Axler defines {lit}`λ ∈ F` to be an *eigenvalue* of {lit}`T ∈ ℒ(V)` when there
exists {lit}`v ≠ 0` with {lit}`Tv = λv`. In mathlib this is exactly
{name}`Module.End.HasEigenvalue` (defined via a nontrivial eigenspace
{lit}`E(λ, T) ≠ {0}`); we use it throughout under the short name
{lit}`HasEigenvalue`. -/

open Module.End (HasEigenvalue)

/-- {lit}`HasEigenvalue` unfolds to Axler's definition 5.5: {lit}`γ` is an
eigenvalue of {lit}`T` iff some nonzero {lit}`v` satisfies {lit}`Tv = γv`.
This bridges mathlib's eigenspace-based definition to the explicit witness, so
eigenvalue proofs can {lit}`rw` to and from {lit}`⟨v, hv, hTv⟩`. -/
theorem _root_.Module.End.hasEigenvalue_iff_exists {T : V →ₗ[F] V} {γ : F} :
    HasEigenvalue T γ ↔ ∃ v : V, v ≠ 0 ∧ T v = γ • v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, Module.End.mem_eigenspace_iff.mp hv.1⟩
  · rintro ⟨v, hv, hTv⟩
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hTv, hv⟩

/-! 5.6 Example: {lit}`T(x, y, z) = (7x + 3z, 3x + 6y + 9z, −6y)` on
{lit}`F³` has eigenvalue {lit}`6`, with eigenvector {lit}`(3, 1, −1)`. -/

def T_5_6 : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun v := ![7 * v 0 + 3 * v 2, 3 * v 0 + 6 * v 1 + 9 * v 2, -(6 * v 1)]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

example : HasEigenvalue (T_5_6 (F := F)) 6 := by
  rw [Module.End.hasEigenvalue_iff_exists]
  refine ⟨![3, 1, -1], ?_, ?_⟩
  · intro h
    have h1 : (![3, 1, -1] : Fin 3 → F) 1 = 0 := by rw [h]; rfl
    simp at h1
  · funext i
    fin_cases i <;> simp [T_5_6] <;> norm_num

/-! 5.7 -/
theorem tfae_isEigenvalue [Finite F V] (T : V →ₗ[F] V) (γ : F) :
    [HasEigenvalue T γ,
      ¬ Function.Injective (T - γ • (LinearMap.id : V →ₗ[F] V)),
      ¬ Function.Surjective (T - γ • (LinearMap.id : V →ₗ[F] V)),
      ¬ IsInvertible (T - γ • (LinearMap.id : V →ₗ[F] V))].TFAE := by
  have h365 := LADR.Section_3D.tfae_isInvertible (F := F) (V := V) (W := V)
    rfl (T - γ • LinearMap.id)
  -- (a) ↔ (b): {lit}`Tv = λv` iff {lit}`(T − λI)v = 0`.
  tfae_have 1 ↔ 2 := by
    rw [Module.End.hasEigenvalue_iff_exists]
    constructor
    · rintro ⟨v, hv, hTv⟩ hinj
      apply hv
      have h0 : (T - γ • (LinearMap.id : V →ₗ[F] V)) v = 0 := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
          hTv, sub_self]
      exact hinj (by simpa using h0)
    · intro hinj
      rw [LADR.Section_3B.injective_iff_ker_eq_bot] at hinj
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinj
      refine ⟨v, hv_ne, ?_⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero] at hv_mem
      exact hv_mem
  tfae_have 2 ↔ 3 := not_congr (h365.out 1 2)
  tfae_have 2 ↔ 4 := not_congr (h365.out 1 0)
  tfae_finish

/-! 5.8 Definition: eigenvector -/

open Module.End (HasEigenvector)

/-- {lit}`HasEigenvector` unfolds to Axler's definition 5.8: {lit}`v` is an
eigenvector of {lit}`T` for {lit}`λ` iff {lit}`v ≠ 0` and {lit}`Tv = λv`.
This bridges mathlib's eigenspace-based definition to the explicit conditions,
so eigenvector proofs can {lit}`rw` to and from {lit}`⟨hv, hTv⟩`. -/
theorem _root_.Module.End.hasEigenvector_iff_and {T : V →ₗ[F] V} {γ : F}
    {v : V} : HasEigenvector T γ v ↔ v ≠ 0 ∧ T v = γ • v := by
  constructor
  · rintro ⟨hmem, hv⟩
    exact ⟨hv, Module.End.mem_eigenspace_iff.mp hmem⟩
  · rintro ⟨hv, hTv⟩
    exact ⟨Module.End.mem_eigenspace_iff.mpr hTv, hv⟩

/-- A nonzero vector {lit}`v` is an eigenvector of {lit}`T` corresponding to
{lit}`γ` iff {lit}`v ∈ null (T − γI)`. -/
theorem isEigenvector_iff_mem_ker (T : V →ₗ[F] V) (γ : F) (v : V) :
    HasEigenvector T γ v ↔ v ≠ 0 ∧ v ∈ ker (T - γ • LinearMap.id) := by
  rw [Module.End.hasEigenvector_iff_and, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero]
  simp [eq_comm]

/-! 5.9 Example: {lit}`T(w, z) = (−z, w)`.

(a) Over {lit}`ℝ` this is rotation by 90°, which sends no nonzero vector to a
scalar multiple of itself: {lit}`T` has no (real) eigenvalues.

(b) Over {lit}`ℂ`, solving {lit}`T(w, z) = λ(w, z)` (equations 5.10) leads to
{lit}`λ² = −1`, so the eigenvalues are exactly {lit}`i` and {lit}`−i`. -/

def T_5_9 (F : Type*) [Field F] : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![-v 1, v 0]
  map_add' x y := by
    funext i
    fin_cases i
    · simp [add_comm]
    · simp
  map_smul' a x := by
    funext i
    fin_cases i <;> simp

example : ¬ ∃ γ : ℝ, HasEigenvalue (T_5_9 ℝ) γ := by
  rintro ⟨γ, hev⟩
  obtain ⟨v, hv, hTv⟩ := Module.End.hasEigenvalue_iff_exists.mp hev
  -- The two coordinates of {lit}`Tv = λv` say {lit}`−v₁ = λv₀` and
  -- {lit}`v₀ = λv₁`; together {lit}`(λ² + 1)v₁ = 0` and {lit}`(λ² + 1)v₀ = 0`.
  have h0 : -v 1 = γ * v 0 := congrFun hTv 0
  have h1 : v 0 = γ * v 1 := congrFun hTv 1
  have h2 : (1 + γ ^ 2) * v 0 = 0 := by linear_combination h1 - γ * h0
  have h3 : (1 + γ ^ 2) * v 1 = 0 := by linear_combination -h0 - γ * h1
  have hpos : (0 : ℝ) < 1 + γ ^ 2 := by positivity
  apply hv
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp h2).resolve_left (ne_of_gt hpos)
  · exact (mul_eq_zero.mp h3).resolve_left (ne_of_gt hpos)

example : ∀ γ : ℂ, HasEigenvalue (T_5_9 ℂ) γ ↔
    γ = Complex.I ∨ γ = -Complex.I := by
  intro γ
  rw [Module.End.hasEigenvalue_iff_exists]
  constructor
  · rintro ⟨v, hv, hTv⟩
    have h0 : -v 1 = γ * v 0 := congrFun hTv 0
    have h1 : v 0 = γ * v 1 := congrFun hTv 1
    -- {lit}`−v₁ = λ²v₁`; if {lit}`v₁ = 0` then also {lit}`v₀ = 0`,
    -- contradicting {lit}`v ≠ 0`. Hence {lit}`λ² = −1`.
    have hv1 : v 1 ≠ 0 := by
      intro h
      apply hv
      funext i
      fin_cases i
      · simpa [h] using h1
      · exact h
    have hlam_sq : γ ^ 2 = -1 := by
      have h2 : γ ^ 2 * v 1 = -v 1 := by
        rw [pow_two, mul_assoc, ← h1, ← h0]
      have h3 : (γ ^ 2 + 1) * v 1 = 0 := by linear_combination h2
      rcases mul_eq_zero.mp h3 with h | h
      · linear_combination h
      · exact absurd h hv1
    have hfactor : (γ - Complex.I) * (γ + Complex.I) = 0 := by
      have : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination hlam_sq - this
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · rintro (rfl | rfl)
    · -- eigenvector {lit}`(1, −i)` for {lit}`λ = i`
      refine ⟨![1, -Complex.I], ?_, ?_⟩
      · intro h
        have h0 : (![1, -Complex.I] : Fin 2 → ℂ) 0 = 0 := by rw [h]; rfl
        simp at h0
      · funext i
        fin_cases i <;> simp [T_5_9]
    · -- eigenvector {lit}`(1, i)` for {lit}`λ = −i`
      refine ⟨![1, Complex.I], ?_, ?_⟩
      · intro h
        have h0 : (![1, Complex.I] : Fin 2 → ℂ) 0 = 0 := by rw [h]; rfl
        simp at h0
      · funext i
        fin_cases i <;> simp [T_5_9]

/-! 5.11 Linearly independent eigenvectors.

Axler's proof takes a dependence relation and applies {lit}`T − λI` to peel off
one eigenvalue at a time. We follow that argument by induction on the number of
eigenvectors: given a dependence {lit}`∑ cᵢvᵢ = 0`, applying
{lit}`T − λₘI` annihilates the last term and leaves a dependence among the
first {lit}`m` eigenvectors, which are independent by the induction hypothesis;
since the surviving coefficients carry nonzero factors {lit}`λᵢ − λₘ` they must
vanish, and then {lit}`cₘvₘ = 0` forces {lit}`cₘ = 0` as well.
(mathlib's own version is {name}`Module.End.eigenvectors_linearIndependent'`.) -/

theorem eigenvectors_linearIndependent (T : V →ₗ[F] V) {m : ℕ}
    (lam : Fin m → F) (hlam : Function.Injective lam) (v : Fin m → V)
    (hv : ∀ k, HasEigenvector T (lam k) (v k)) :
    LinearIndependent F v := by
  induction m with
  | zero =>
    rw [Fintype.linearIndependent_iff]
    exact fun c _ i => Fin.elim0 i
  | succ m ih =>
    -- Work with the linear-combination characterization of independence.
    rw [Fintype.linearIndependent_iff]
    intro c hc
    set μ := lam (Fin.last m) with hμ
    -- Apply {lit}`T − μI` to the dependence {lit}`∑ cᵢ vᵢ = 0`. On each
    -- eigenvector it acts as multiplication by {lit}`λᵢ − μ`.
    have key : ∀ i, (T - μ • (LinearMap.id : V →ₗ[F] V)) (v i) =
        (lam i - μ) • v i := by
      intro i
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [Module.End.mem_eigenspace_iff.mp (hv i).1, sub_smul]
    have hD : ∑ i, c i • ((lam i - μ) • v i) = 0 := by
      have h : (T - μ • (LinearMap.id : V →ₗ[F] V)) (∑ i, c i • v i) = 0 := by
        rw [hc, map_zero]
      rw [map_sum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, key i]
    -- The last term vanishes ({lit}`λₘ − μ = 0`), leaving a dependence among
    -- the first {lit}`m` eigenvectors.
    rw [Fin.sum_univ_castSucc] at hD
    simp only [hμ, sub_self, zero_smul, smul_zero, add_zero] at hD
    -- By the induction hypothesis those eigenvectors are independent.
    have hli : LinearIndependent F (v ∘ Fin.castSucc) :=
      ih (lam ∘ Fin.castSucc) (hlam.comp (Fin.castSucc_injective m))
        (v ∘ Fin.castSucc) fun k => hv k.castSucc
    rw [Fintype.linearIndependent_iff] at hli
    have hzero : ∀ i : Fin m, c i.castSucc * (lam i.castSucc - μ) = 0 := by
      apply hli
      simpa only [smul_smul, Function.comp_apply] using hD
    -- Distinct eigenvalues make each factor {lit}`λᵢ − μ` nonzero, so each
    -- surviving coefficient is zero.
    have hc0 : ∀ i : Fin m, c i.castSucc = 0 := by
      intro i
      rcases mul_eq_zero.mp (hzero i) with h | h
      · exact h
      · exact absurd (hlam (sub_eq_zero.mp h)) (Fin.castSucc_lt_last i).ne
    -- Finally {lit}`cₘ vₘ = 0` with {lit}`vₘ ≠ 0` forces {lit}`cₘ = 0`.
    have hclast : c (Fin.last m) = 0 := by
      rw [Fin.sum_univ_castSucc] at hc
      rw [Finset.sum_eq_zero fun i _ => by rw [hc0 i, zero_smul], zero_add] at hc
      exact (smul_eq_zero.mp hc).resolve_right (hv (Fin.last m)).2
    exact fun i => Fin.lastCases hclast hc0 i

/-! 5.12 An operator cannot have more eigenvalues than the dimension of the
vector space. -/

theorem card_eigenvalues_le_finrank [Finite F V] (T : V →ₗ[F] V) {m : ℕ}
    (lam : Fin m → F) (hlam : Function.Injective lam)
    (hev : ∀ k, HasEigenvalue T (lam k)) : m ≤ finrank F V := by
  -- Choose an eigenvector for each eigenvalue; by 5.11 the list is linearly
  -- independent, so its length is at most {lit}`dim V` (2.22).
  simp only [Module.End.hasEigenvalue_iff_exists] at hev
  choose v hv_ne hv_eq using hev
  have hli : LinearIndependent F v :=
    eigenvectors_linearIndependent T lam hlam v
      fun k => Module.End.hasEigenvector_iff_and.mpr ⟨hv_ne k, hv_eq k⟩
  simpa using hli.fintype_card_le_finrank

/-! Polynomials Applied to Operators -/

/-! 5.13 Notation: {lit}`Tᵐ`.

Because {lit}`V →ₗ[F] V` is mathlib's {name}`Module.End`, it is a monoid
under composition and the power {lit}`T ^ m` is available, with
{lit}`T⁰ = I` (mathlib's {lit}`1 = LinearMap.id`). For invertible {lit}`T`
the negative powers are {lit}`T⁻ᵐ = (T⁻¹)ᵐ`. -/

example (T : V →ₗ[F] V) (m : ℕ) : V →ₗ[F] V := T ^ m

example (T : V →ₗ[F] V) : T ^ 0 = LinearMap.id := rfl

example (T : V →ₗ[F] V) : T ^ 1 = T := pow_one T

example (T S : V →ₗ[F] V) : T * S = T ∘ₗ S := rfl

-- {lit}`T⁻ᵐ = (T⁻¹)ᵐ` for invertible {lit}`T`, via 3D's inverse.
noncomputable example (T : V →ₗ[F] V) (h : IsInvertible T) (m : ℕ) :
    V →ₗ[F] V :=
  h.inv ^ m

-- "You should verify that ...": {lit}`TᵐTⁿ = Tᵐ⁺ⁿ` and {lit}`(Tᵐ)ⁿ = Tᵐⁿ`.
example (T : V →ₗ[F] V) (m n : ℕ) : T ^ m * T ^ n = T ^ (m + n) :=
  (pow_add T m n).symm

example (T : V →ₗ[F] V) (m n : ℕ) : (T ^ m) ^ n = T ^ (m * n) :=
  (pow_mul T m n).symm

/-! 5.14 Notation: {lit}`p(T)`.

For {lit}`p(z) = a₀ + a₁z + ⋯ + aₘzᵐ`, the operator {lit}`p(T)` is
{lit}`a₀I + a₁T + ⋯ + aₘTᵐ`. In mathlib this is {name}`Polynomial.aeval`
(evaluation of a polynomial in the {lit}`F`-algebra {lit}`ℒ(V)`). -/

noncomputable example (T : V →ₗ[F] V) (p : Polynomial F) : V →ₗ[F] V :=
  aeval T p

example (T : V →ₗ[F] V) (p : Polynomial F) :
    aeval T p = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • T ^ k :=
  Polynomial.aeval_eq_sum_range (R := F) T

-- The constant term becomes {lit}`a₀ I`:
example (T : V →ₗ[F] V) (a : F) :
    aeval T (Polynomial.C a) = a • LinearMap.id := by
  rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  rfl

example (T : V →ₗ[F] V) : aeval T (Polynomial.X : Polynomial F) = T :=
  Polynomial.aeval_X T

/-! 5.15 Example: for the differentiation operator {lit}`D q = q′` and
{lit}`p(x) = 7 − 3x + 5x²`, we get {lit}`p(D) q = 7q − 3q′ + 5q″`. -/

example (q : Polynomial ℝ) :
    aeval (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
        (Polynomial.C (7 : ℝ) - Polynomial.C 3 * Polynomial.X +
          Polynomial.C 5 * Polynomial.X ^ 2) q =
      (7 : ℝ) • q - (3 : ℝ) • Polynomial.derivative q +
        (5 : ℝ) • Polynomial.derivative (Polynomial.derivative q) := by
  simp only [map_add, map_sub, map_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one, pow_two,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply]

/-- For fixed {lit}`T`, the function {lit}`p ↦ p(T)` from {lit}`𝒫(F)` to
{lit}`ℒ(V)` is linear (as you should verify). -/
example (T : V →ₗ[F] V) (a : F) (p q : Polynomial F) :
    aeval T (a • p + q) = a • aeval T p + aeval T q := by
  rw [map_add, map_smul]

/-! 5.16 Definition: product of polynomials — mathlib's {lit}`p * q`,
satisfying {lit}`(pq)(z) = p(z)q(z)`. -/

example (p q : Polynomial F) (z : F) : (p * q).eval z = p.eval z * q.eval z :=
  Polynomial.eval_mul

/-! 5.17 Multiplicative properties: {lit}`(pq)(T) = p(T)q(T)` and
{lit}`p(T)q(T) = q(T)p(T)`. Both follow because {lit}`aeval T` is a ring
homomorphism into the commutative image generated by {lit}`T`. -/

theorem aeval_mul_eq_comp (T : V →ₗ[F] V) (p q : Polynomial F) :
    aeval T (p * q) = aeval T p ∘ₗ aeval T q := by
  rw [map_mul]
  rfl

theorem aeval_comp_comm (T : V →ₗ[F] V) (p q : Polynomial F) :
    aeval T p ∘ₗ aeval T q = aeval T q ∘ₗ aeval T p := by
  rw [← aeval_mul_eq_comp, ← aeval_mul_eq_comp, mul_comm]

/-- In particular {lit}`p(T)` commutes with {lit}`T` itself (take
{lit}`q = X` in 5.17). -/
theorem aeval_comm_self (T : V →ₗ[F] V) (p : Polynomial F) (v : V) :
    aeval T p (T v) = T (aeval T p v) := by
  have h := aeval_comp_comm T p Polynomial.X
  rw [Polynomial.aeval_X] at h
  exact LinearMap.congr_fun h v

/-! 5.18 Null space and range of {lit}`p(T)` are invariant under {lit}`T`. -/

theorem ker_aeval_invariant (T : V →ₗ[F] V) (p : Polynomial F) :
    InvariantUnder T (ker (aeval T p)) := by
  intro u hu
  rw [LinearMap.mem_ker] at hu ⊢
  rw [aeval_comm_self, hu, map_zero]

theorem range_aeval_invariant (T : V →ₗ[F] V) (p : Polynomial F) :
    InvariantUnder T (range (aeval T p)) := by
  rintro u hu
  obtain ⟨v, rfl⟩ := hu
  exact ⟨T v, aeval_comm_self T p v⟩

/-! # Exercises -/

/-- 5A.1 (a) -/
theorem exercise_5A_1a (T : V →ₗ[F] V) (U : Submodule F V)
    (h : U ≤ ker T) : InvariantUnder T U := by
  rw [InvariantUnder]
  intro u hu
  have : u ∈ ker T := h hu
  have : T u = 0 := by rw [LinearMap.mem_ker] at this; exact this
  rw [this]
  exact Submodule.zero_mem U

/-- 5A.1 (b) -/
theorem exercise_5A_1b (T : V →ₗ[F] V) (U : Submodule F V)
    (h : range T ≤ U) : InvariantUnder T U := by
  rw [InvariantUnder]
  intro u hu
  exact h (LinearMap.mem_range.mpr ⟨u, rfl⟩)

/-- 5A.2 -/
theorem exercise_5A_2 (T : V →ₗ[F] V) {m : ℕ} (W : Fin m → Submodule F V)
    (h : ∀ i, InvariantUnder T (W i)) : InvariantUnder T (⨆ i, W i) := by
  rw [InvariantUnder]
  intro u hu
  classical
  -- turn u into a finite sum ∑ i, wᵢ with each wᵢ ∈ W i
  rw [show (⨆ i, W i) = ⨆ i ∈ (Finset.univ : Finset (Fin m)), W i by simp,
      Submodule.mem_iSup_finset_iff_exists_sum] at hu
  obtain ⟨w, rfl⟩ := hu
  rw [map_sum]
  apply Submodule.sum_mem
  intro i hi
  specialize h i
  have := h (w i) (w i).2
  exact Submodule.mem_iSup_of_mem i this

/-- 5A.3 -/
theorem exercise_5A_3 (T : V →ₗ[F] V) (𝒮 : Set (Submodule F V))
    (h : ∀ U ∈ 𝒮, InvariantUnder T U) : InvariantUnder T (sInf 𝒮) := by
  intro u hu
  rw [Submodule.mem_sInf] at hu ⊢
  intro U hU
  specialize h U hU
  exact h u (hu U hU)

/-- 5A.4 Prove or give a counterexample: if {lit}`U` is invariant under every
operator on a finite-dimensional {lit}`V`, then {lit}`U = {0}` or
{lit}`U = V`. -/
def exercise_5A_4 [Finite F V] :
    Decidable (∀ U : Submodule F V,
      (∀ T : V →ₗ[F] V, InvariantUnder T U) → U = ⊥ ∨ U = ⊤) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  intro U hU
  -- proof by contradiction: assume U is invariant under every operator, yet
  -- U ≠ ⊥ and U ≠ ⊤.
  by_contra hcon
  push Not at hcon
  obtain ⟨hbot, htop⟩ := hcon
  -- pick u ∈ U with u ≠ 0, and v ∉ U.
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  rw [ne_eq, Submodule.eq_top_iff'] at htop
  push Not at htop
  obtain ⟨v, hvU⟩ := htop
  classical
  -- Since u ≠ 0 the singleton {u} is linearly independent; extend it to a basis
  -- w of V (2.32, `exists_basis_extending`), with u sitting at index castLE 0.
  have hli : LinearIndependent F (fun _ : Fin 1 => u) :=
    linearIndependent_unique_iff.mpr hu0
  obtain ⟨n, w, hn, hbasis, hpres⟩ :=
    LADR.Section_2B.exists_basis_extending (fun _ : Fin 1 => u) hli
  have hwu : w (Fin.castLE hn 0) = u := hpres 0
  -- The linear map lemma (3.4, `linearMap_lemma`) yields the operator sending
  -- that basis vector to v and every other basis vector to 0; so T u = v.
  obtain ⟨T, hT, -⟩ := LADR.Section_3A.linearMap_lemma w hbasis
    (fun j => if j = Fin.castLE hn 0 then v else 0)
  have hTu : T u = v := by rw [← hwu, hT (Fin.castLE hn 0)]; simp
  -- Invariance forces v = T u ∈ U, contradicting v ∉ U.
  exact hvU (hTu ▸ hU T u huU)

/-- 5A.5 {lit}`T(x, y) = (−3y, x)` on {lit}`ℝ²`: find the eigenvalues. -/
def T_ex_5A_5 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![-(3 * v 1), v 0]
  map_add' x y := by
    funext i
    fin_cases i
    · simp [mul_add, add_comm]
    · simp
  map_smul' a x := by
    funext i
    fin_cases i
    · simp [mul_left_comm]
    · simp

/-- The set of eigenvalues of {lit}`T_ex_5A_5` — to be determined by the
solver. -/
def eigenvalues_5A_5 : Set ℝ := ∅

theorem exercise_5A_5 (γ : ℝ) :
    HasEigenvalue T_ex_5A_5 γ ↔ γ ∈ eigenvalues_5A_5 := by
  -- There are no (real) eigenvalues: `Tv = γv` forces `(γ² + 3)·v₁ = 0`, and
  -- `γ² + 3 > 0`, so `v₁ = 0` and then `v₀ = γ·v₁ = 0`, i.e. `v = 0`.
  rw [eigenvalues_5A_5, Set.mem_empty_iff_false, iff_false,
    Module.End.hasEigenvalue_iff_exists]
  rintro ⟨v, hv, hTv⟩
  -- Read off the two coordinate equations of `T v = γ • v`.
  have e0 : -(3 * v 1) = γ * v 0 := by
    have := congrFun hTv 0; simpa [T_ex_5A_5] using this
  have e1 : v 0 = γ * v 1 := by
    have := congrFun hTv 1; simpa [T_ex_5A_5] using this
  have key : (γ ^ 2 + 3) * v 1 = 0 := by linear_combination -e0 - γ * e1
  have hv1 : v 1 = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (by positivity)
    · exact h
  have hv0 : v 0 = 0 := by rw [e1, hv1, mul_zero]
  exact hv (by funext i; fin_cases i <;> simp [hv0, hv1])

/-- 5A.6 {lit}`T(w, z) = (z, w)` on {lit}`F²`: find all eigenvalues and
eigenvectors. -/
def T_ex_5A_6 : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![v 1, v 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' a x := by
    funext i
    fin_cases i <;> simp

/-- The set of eigenvalues of {lit}`T_ex_5A_6`. Solving {lit}`T v = lam v`
gives {lit}`lam² = 1`, so the eigenvalues are {lit}`1` and {lit}`-1`. -/
def eigenvalues_5A_6 (F : Type*) [Field F] : Set F := {1, -1}

/-- The set of eigenvectors of {lit}`T_ex_5A_6` for a scalar {lit}`lam` (empty
when {lit}`lam` is not an eigenvalue). The {lit}`1`-eigenvectors are the nonzero
multiples of {lit}`(1, 1)` (the vectors with {lit}`v₀ = v₁`); the
{lit}`-1`-eigenvectors are the nonzero multiples of {lit}`(1, -1)`. -/
noncomputable def eigenvectors_5A_6 (F : Type*) [Field F] (lam : F) :
    Set (Fin 2 → F) :=
  open Classical in
  if lam = 1 then {v | v 0 = v 1 ∧ v ≠ 0}
  else if lam = -1 then {v | v 1 = -v 0 ∧ v ≠ 0}
  else ∅

/-- {lit}`T v = lam • v` unpacks into the two coordinate equations of
{lit}`T(w, z) = (z, w)`. -/
private theorem T_ex_5A_6_apply_eq_smul (lam : F) (v : Fin 2 → F) :
    (T_ex_5A_6 (F := F)) v = lam • v ↔ v 1 = lam * v 0 ∧ v 0 = lam * v 1 := by
  constructor
  · intro h
    exact ⟨by have := congrFun h 0; simpa [T_ex_5A_6] using this,
           by have := congrFun h 1; simpa [T_ex_5A_6] using this⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simpa [T_ex_5A_6] using h0
    · simpa [T_ex_5A_6] using h1

/-- From the two coordinate equations and {lit}`v ≠ 0`, the scalar satisfies
{lit}`lam² = 1`. -/
private theorem T_ex_5A_6_sq (lam : F) (v : Fin 2 → F) (hne : v ≠ 0)
    (h0 : v 1 = lam * v 0) (h1 : v 0 = lam * v 1) : lam * lam = 1 := by
  have hor : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (by funext i; fin_cases i <;> simp [hc.1, hc.2])
  rcases hor with h | h
  · have hz : (lam * lam - 1) * v 0 = 0 := by linear_combination -lam * h0 - h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right h)
  · have hz : (lam * lam - 1) * v 1 = 0 := by linear_combination -h0 - lam * h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right h)

theorem exercise_5A_6a (lam : F) :
    HasEigenvalue (T_ex_5A_6 (F := F)) lam ↔ lam ∈ eigenvalues_5A_6 F := by
  rw [Module.End.hasEigenvalue_iff_exists, eigenvalues_5A_6,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, hv, hTv⟩
    rw [T_ex_5A_6_apply_eq_smul] at hTv
    exact mul_self_eq_one_iff.mp (T_ex_5A_6_sq lam v hv hTv.1 hTv.2)
  · rintro (rfl | rfl)
    · refine ⟨![1, 1], ?_, ?_⟩
      · intro h; have := congrFun h 0; simp at this
      · rw [T_ex_5A_6_apply_eq_smul]; constructor <;> simp
    · refine ⟨![1, -1], ?_, ?_⟩
      · intro h; have := congrFun h 0; simp at this
      · rw [T_ex_5A_6_apply_eq_smul]; constructor <;> simp

theorem exercise_5A_6b (lam : F) (v : Fin 2 → F) :
    HasEigenvector (T_ex_5A_6 (F := F)) lam v ↔ v ∈ eigenvectors_5A_6 F lam := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff,
    T_ex_5A_6_apply_eq_smul, eigenvectors_5A_6]
  by_cases h1 : lam = 1
  · subst h1
    simp only [one_mul]
    constructor
    · rintro ⟨⟨ha, _⟩, hne⟩; exact ⟨ha.symm, hne⟩
    · rintro ⟨h, hne⟩; exact ⟨⟨h.symm, h⟩, hne⟩
  · by_cases h2 : lam = -1
    · subst h2
      simp only [if_neg h1, neg_one_mul]
      constructor
      · rintro ⟨⟨ha, _⟩, hne⟩; exact ⟨ha, hne⟩
      · rintro ⟨h, hne⟩; exact ⟨⟨h, by rw [h, neg_neg]⟩, hne⟩
    · simp only [if_neg h1, if_neg h2, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ha, hb⟩, hne⟩
      rcases mul_self_eq_one_iff.mp (T_ex_5A_6_sq lam v hne ha hb) with h | h
      · exact h1 h
      · exact h2 h

/-- 5A.7 {lit}`T(z₁, z₂, z₃) = (2z₂, 0, 5z₃)` on {lit}`F³`: find all
eigenvalues and eigenvectors. -/
def T_ex_5A_7 : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun v := ![2 * v 1, 0, 5 * v 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp <;> ring

/-- The set of eigenvalues of {lit}`T_ex_5A_7` — to be determined. -/
-- 2 y = l x; 0 = l y; 5 z = l z
-- l = 0 -> z = 0, y = 0, x arbitrary nonzero -> eigenv [x, 0, 0]
-- l =/ 0 -> y = 0, x = 0, z arbitrary nonzero, l = 5 -> eigenv [0, 0, z]
def eigenvalues_5A_7 (F : Type*) [Field F] : Set F := {0, 5}

/-- The set of eigenvectors of {lit}`T_ex_5A_7` for a scalar {lit}`lam` (empty
when {lit}`lam` is not an eigenvalue). For {lit}`lam = 0` these are the nonzero
solutions of {lit}`2·v₁ = 0` and {lit}`5·v₂ = 0` (equations kept unsimplified so
the description stays correct in every characteristic); for {lit}`lam = 5` they
are the nonzero vectors with {lit}`v₀ = v₁ = 0`, i.e. the multiples of
{lit}`(0, 0, 1)`. -/
noncomputable def eigenvectors_5A_7 (F : Type*) [Field F] (lam : F) :
    Set (Fin 3 → F) :=
  open Classical in
  if lam = 0 then {v | 2 * v 1 = 0 ∧ 5 * v 2 = 0 ∧ v ≠ 0}
  else if lam = 5 then {v | v 0 = 0 ∧ v 1 = 0 ∧ v ≠ 0}
  else ∅

/-- {lit}`T v = lam • v` unpacks into the three coordinate equations of
{lit}`T(z₁, z₂, z₃) = (2z₂, 0, 5z₃)`. -/
private theorem T_ex_5A_7_apply_eq_smul (lam : F) (v : Fin 3 → F) :
    (T_ex_5A_7 (F := F)) v = lam • v ↔
      2 * v 1 = lam * v 0 ∧ lam * v 1 = 0 ∧ 5 * v 2 = lam * v 2 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := congrFun h 0; simpa [T_ex_5A_7] using this
    · have := congrFun h 1; simpa [T_ex_5A_7] using this.symm
    · have := congrFun h 2; simpa [T_ex_5A_7] using this
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i
    · simpa [T_ex_5A_7] using h0
    · simpa [T_ex_5A_7] using h1.symm
    · simpa [T_ex_5A_7] using h2

theorem exercise_5A_7a (lam : F) :
    HasEigenvalue (T_ex_5A_7 (F := F)) lam ↔ lam ∈ eigenvalues_5A_7 F := by
  rw [Module.End.hasEigenvalue_iff_exists, eigenvalues_5A_7,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, hv, hTv⟩
    rw [T_ex_5A_7_apply_eq_smul] at hTv
    obtain ⟨h0, h1, h2⟩ := hTv
    by_contra hc
    push Not at hc
    obtain ⟨hlam0, hlam5⟩ := hc
    apply hv
    have hv1 : v 1 = 0 := (mul_eq_zero.mp h1).resolve_left hlam0
    have hv0 : v 0 = 0 := by
      have : lam * v 0 = 0 := by rw [← h0, hv1, mul_zero]
      exact (mul_eq_zero.mp this).resolve_left hlam0
    have hv2 : v 2 = 0 := by
      have h5 : (5 - lam) * v 2 = 0 := by linear_combination h2
      rcases mul_eq_zero.mp h5 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hlam5
      · exact h
    funext i; fin_cases i <;> simp [hv0, hv1, hv2]
  · rintro (rfl | rfl)
    · refine ⟨![1, 0, 0], ?_, ?_⟩
      · intro h; have := congrFun h 0; simp at this
      · rw [T_ex_5A_7_apply_eq_smul]; refine ⟨?_, ?_, ?_⟩ <;> simp
    · refine ⟨![0, 0, 1], ?_, ?_⟩
      · intro h; have := congrFun h 2; simp at this
      · rw [T_ex_5A_7_apply_eq_smul]; refine ⟨?_, ?_, ?_⟩ <;> simp

theorem exercise_5A_7b (lam : F) (v : Fin 3 → F) :
    HasEigenvector (T_ex_5A_7 (F := F)) lam v ↔ v ∈ eigenvectors_5A_7 F lam := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff,
    T_ex_5A_7_apply_eq_smul, eigenvectors_5A_7]
  by_cases h0 : lam = 0
  · rw [if_pos h0, Set.mem_setOf_eq, h0]
    simp only [zero_mul]
    constructor
    · rintro ⟨⟨ha, _, hc⟩, hne⟩; exact ⟨ha, hc, hne⟩
    · rintro ⟨ha, hc, hne⟩; exact ⟨⟨ha, trivial, hc⟩, hne⟩
  · rw [if_neg h0]
    by_cases h5 : lam = 5
    · rw [if_pos h5, Set.mem_setOf_eq, h5]
      have h50 : (5 : F) ≠ 0 := h5 ▸ h0
      constructor
      · rintro ⟨⟨ha, hb, _⟩, hne⟩
        have hv1 : v 1 = 0 := (mul_eq_zero.mp hb).resolve_left h50
        have hv0 : v 0 = 0 := by
          have : (5 : F) * v 0 = 0 := by rw [← ha, hv1, mul_zero]
          exact (mul_eq_zero.mp this).resolve_left h50
        exact ⟨hv0, hv1, hne⟩
      · rintro ⟨hv0, hv1, hne⟩
        exact ⟨⟨by rw [hv0, hv1, mul_zero, mul_zero],
          by rw [hv1, mul_zero], rfl⟩, hne⟩
    · rw [if_neg h5, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ha, hb, hc⟩, hne⟩
      apply hne
      have hv1 : v 1 = 0 := (mul_eq_zero.mp hb).resolve_left h0
      have hv0 : v 0 = 0 := by
        have : lam * v 0 = 0 := by rw [← ha, hv1, mul_zero]
        exact (mul_eq_zero.mp this).resolve_left h0
      have hv2 : v 2 = 0 := by
        have h5' : (5 - lam) * v 2 = 0 := by linear_combination hc
        rcases mul_eq_zero.mp h5' with h | h
        · exact absurd (sub_eq_zero.mp h).symm h5
        · exact h
      funext i; fin_cases i <;> simp [hv0, hv1, hv2]

/-- 5A.8 -/
theorem exercise_5A_8 (P : V →ₗ[F] V) (hP : P ∘ₗ P = P) (γ : F)
    (h : HasEigenvalue P γ) : γ = 0 ∨ γ = 1 := by
  rw [Module.End.hasEigenvalue_iff_exists] at h
  obtain ⟨v, hv, hne⟩ := h
  have := congr_arg (P ·) hne
  simp at this
  rw [show P (P v) = (P ∘ₗ P) v by simp] at this
  rw [hP] at this
  -- Substituting `P v = γ • v` gives `γ • v = (γ * γ) • v`; since `v ≠ 0`,
  -- `γ * γ = γ`, i.e. `γ * (γ - 1) = 0`, so `γ = 0` or `γ = 1`.
  rw [hne, smul_smul] at this
  have hz : (γ * γ - γ) • v = 0 := by rw [sub_smul, ← this, sub_self]
  have hfac : γ * (γ - 1) = 0 := by
    have := (smul_eq_zero.mp hz).resolve_right hv
    linear_combination this
  rcases mul_eq_zero.mp hfac with h0 | h1
  · left; exact h0
  · right; exact sub_eq_zero.mp h1

/-- 5A.9 The differentiation operator on {lit}`𝒫(ℝ)`: find all eigenvalues and
eigenvectors. -/
-- Differentiation strictly lowers degree, so `p' = γp` with `p ≠ 0` forces
-- `γ = 0`; and `γ = 0` is attained (nonzero constants have zero derivative).
-- Hence the only eigenvalue is `0`.
def eigenvalues_5A_9 : Set ℝ := {0}

/-- The eigenvectors of differentiation for a scalar {lit}`lam`: for
{lit}`lam = 0` they are the nonzero polynomials with zero derivative — i.e. the
nonzero constants — and there are none otherwise. -/
noncomputable def eigenvectors_5A_9 (lam : ℝ) : Set (Polynomial ℝ) :=
  if lam = 0 then {p | Polynomial.derivative p = 0 ∧ p ≠ 0} else ∅

/-- Key fact: if a nonzero polynomial is an eigenvector of differentiation, its
eigenvalue must be {lit}`0`, because differentiation strictly lowers degree. -/
private theorem deriv_eigenvalue_eq_zero {p : Polynomial ℝ} (hp : p ≠ 0) {γ : ℝ}
    (h : Polynomial.derivative p = γ • p) : γ = 0 := by
  by_contra hγ
  have hlt := Polynomial.degree_derivative_lt hp
  rw [h, Polynomial.smul_eq_C_mul, Polynomial.degree_mul, Polynomial.degree_C hγ,
    zero_add] at hlt
  exact lt_irrefl _ hlt

theorem exercise_5A_9 :
    (∀ γ : ℝ,
      HasEigenvalue (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
        γ ↔ γ ∈ eigenvalues_5A_9) ∧
    (∀ (γ : ℝ) (p : Polynomial ℝ),
      HasEigenvector (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
        γ p ↔ p ∈ eigenvectors_5A_9 γ) := by
  refine ⟨fun γ => ?_, fun γ p => ?_⟩
  · rw [eigenvalues_5A_9, Set.mem_singleton_iff, Module.End.hasEigenvalue_iff_exists]
    constructor
    · rintro ⟨p, hp, hpe⟩
      exact deriv_eigenvalue_eq_zero hp hpe
    · rintro rfl
      exact ⟨1, one_ne_zero, by rw [Polynomial.derivative_one, zero_smul]⟩
  · rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, eigenvectors_5A_9]
    by_cases hγ : γ = 0
    · subst hγ
      rw [if_pos rfl, Set.mem_setOf_eq, zero_smul]
    · rw [if_neg hγ, Set.mem_empty_iff_false, iff_false]
      rintro ⟨he, hp⟩
      exact hγ (deriv_eigenvalue_eq_zero hp he)

/-- 5A.10 {lit}`(Tp)(x) = x p′(x)` as an operator on {lit}`𝒫₄(ℝ)`
(here {lit}`degreeLT ℝ 5`). -/
noncomputable def T_ex_5A_10 :
    Polynomial.degreeLT ℝ 5 →ₗ[ℝ] Polynomial.degreeLT ℝ 5 where
  toFun p := ⟨Polynomial.X * Polynomial.derivative (p : Polynomial ℝ), by
    rw [Polynomial.mem_degreeLT]
    have hp := Polynomial.mem_degreeLT.mp p.2
    rcases eq_or_ne (Polynomial.derivative (p : Polynomial ℝ)) 0 with hd0 | hd0
    · rw [hd0, mul_zero, Polynomial.degree_zero]
      exact bot_lt_iff_ne_bot.mpr (by simp)
    · have hp0 : (p : Polynomial ℝ) ≠ 0 := fun h => hd0 (by simp [h])
      have hnd0 : (p : Polynomial ℝ).natDegree ≠ 0 := by
        intro h
        obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h
        exact hd0 (by rw [← ha, Polynomial.derivative_C])
      rw [← Polynomial.natDegree_lt_iff_degree_lt
        (mul_ne_zero Polynomial.X_ne_zero hd0),
        Polynomial.natDegree_mul Polynomial.X_ne_zero hd0,
        Polynomial.natDegree_X]
      have h1 := Polynomial.natDegree_derivative_lt hnd0
      have h2 : (p : Polynomial ℝ).natDegree < 5 :=
        (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
      omega⟩
  map_add' p q := by
    ext
    simp [mul_add]
  map_smul' a p := by
    ext
    simp

/-- The set of eigenvalues of {lit}`T_ex_5A_10` — to be determined. -/
-- if a i are the coefficients, i * a i = γ * a i
-- for all i. If two a i are non-zero we can't solve, so all but one must be zero.
-- the eigenvalues are all integers i = 0, 1, 2, 3, 4.
def eigenvalues_5A_10 : Set ℝ := {x.val | x : Fin 5}

/-- The eigenvectors of {lit}`T_ex_5A_10` for a scalar {lit}`lam`: the nonzero
polynomials supported only in degree {lit}`lam` — i.e. the nonzero scalar
multiples of {lit}`X ^ lam` when {lit}`lam ∈ {0, 1, 2, 3, 4}` (and none
otherwise, since a nonzero degree-{lit}`< 5` polynomial must have a nonzero
coefficient at some {lit}`n ∈ {0, …, 4}`). -/
def eigenvectors_5A_10 (γ : ℝ) : Set (Polynomial.degreeLT ℝ 5) :=
  {p | p ≠ 0 ∧ ∀ n : ℕ, (n : ℝ) ≠ γ → (p : Polynomial ℝ).coeff n = 0}

/-- The operator {lit}`p ↦ X · p'` scales the coefficient in degree {lit}`n` by
{lit}`n`. -/
private theorem T_ex_5A_10_coeff (p : Polynomial.degreeLT ℝ 5) (n : ℕ) :
    (T_ex_5A_10 p : Polynomial ℝ).coeff n = (n : ℝ) * (p : Polynomial ℝ).coeff n := by
  show (Polynomial.X * Polynomial.derivative (p : Polynomial ℝ)).coeff n = _
  cases n with
  | zero => simp
  | succ m =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
    push_cast
    ring

/-- The eigenvector equation for {lit}`T_ex_5A_10`, read coefficient-wise. -/
private theorem T_ex_5A_10_eq_smul_iff (γ : ℝ) (p : Polynomial.degreeLT ℝ 5) :
    T_ex_5A_10 p = γ • p ↔
      ∀ n : ℕ, ((n : ℝ) - γ) * (p : Polynomial ℝ).coeff n = 0 := by
  rw [Subtype.ext_iff, Submodule.coe_smul, Polynomial.ext_iff]
  constructor
  · intro h n
    have hn := h n
    rw [T_ex_5A_10_coeff, Polynomial.coeff_smul, smul_eq_mul] at hn
    linear_combination hn
  · intro h n
    rw [T_ex_5A_10_coeff, Polynomial.coeff_smul, smul_eq_mul]
    linear_combination h n

theorem exercise_5A_10a (γ : ℝ) :
    HasEigenvalue T_ex_5A_10 γ ↔ γ ∈ eigenvalues_5A_10 := by
  rw [Module.End.hasEigenvalue_iff_exists, eigenvalues_5A_10]
  constructor
  · rintro ⟨p, hp, hpe⟩
    rw [T_ex_5A_10_eq_smul_iff] at hpe
    have hp' : (p : Polynomial ℝ) ≠ 0 := fun h => hp (Subtype.ext (by rw [h]; rfl))
    obtain ⟨n, hn⟩ : ∃ n, (p : Polynomial ℝ).coeff n ≠ 0 :=
      ⟨_, Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp'⟩
    -- `coeff n ≠ 0` forces `n = γ`, and `n < 5` since `deg p < 5`.
    have hnγ : (n : ℝ) = γ :=
      sub_eq_zero.mp ((mul_eq_zero.mp (hpe n)).resolve_right hn)
    have hn5 : n < 5 := by
      have hd : (p : Polynomial ℝ).natDegree < 5 :=
        (Polynomial.natDegree_lt_iff_degree_lt hp').mpr (Polynomial.mem_degreeLT.mp p.2)
      have := Polynomial.le_natDegree_of_ne_zero hn
      omega
    exact ⟨⟨n, hn5⟩, hnγ⟩
  · rintro ⟨x, rfl⟩
    -- eigenvector for eigenvalue `x` is the monomial `X ^ x`.
    refine ⟨⟨Polynomial.X ^ (x : ℕ), ?_⟩, ?_, ?_⟩
    · rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]
      exact_mod_cast x.isLt
    · rw [ne_eq, Subtype.ext_iff]
      exact pow_ne_zero _ Polynomial.X_ne_zero
    · rw [T_ex_5A_10_eq_smul_iff]
      intro n
      rw [Polynomial.coeff_X_pow]
      by_cases hni : n = (x : ℕ)
      · subst hni; simp
      · rw [if_neg hni, mul_zero]

theorem exercise_5A_10b (γ : ℝ) (p : Polynomial.degreeLT ℝ 5) :
    HasEigenvector T_ex_5A_10 γ p ↔ p ∈ eigenvectors_5A_10 γ := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff,
    T_ex_5A_10_eq_smul_iff, eigenvectors_5A_10, Set.mem_setOf_eq, and_comm]
  refine and_congr_right (fun _ => forall_congr' (fun n => ?_))
  constructor
  · intro h hne
    exact (mul_eq_zero.mp h).resolve_left (fun h0 => hne (sub_eq_zero.mp h0))
  · intro h
    by_cases hng : (n : ℝ) = γ
    · rw [hng, sub_self, zero_mul]
    · rw [h hng, mul_zero]

/-- 5A.11 Stated over {lit}`ℂ`. Same proof should work for {lit}`ℝ`. -/
theorem exercise_5A_11 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (α : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : ℂ, 0 < ‖α - γ‖ → ‖α - γ‖ < δ →
      IsInvertible (T - γ • LinearMap.id) := by
  -- since finite, there are finitely many eigenvalues
  -- take delta < min dist (α, eigenvalue)
  -- now x st. 0 < | α - x | < δ cannot be eigenvalue,
  -- by theorem that is equivalent to T - x I is invertable.
  classical
  have hfin := Module.End.finite_hasEigenvalue T
  set S := hfin.toFinset.filter (fun γ => γ ≠ α) with hS
  -- distances from `α` to the eigenvalues `≠ α`, together with `1` to keep
  -- the set nonempty; `δ` is the least such distance, hence positive.
  set D := insert (1 : ℝ) (S.image (fun γ => ‖α - γ‖)) with hD
  have hDne : D.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨D.min' hDne, ?_, ?_⟩
  · rcases Finset.mem_insert.mp (D.min'_mem hDne) with h1 | h2
    · rw [h1]; norm_num
    · obtain ⟨γ, hγS, hγeq⟩ := Finset.mem_image.mp h2
      rw [← hγeq, norm_pos_iff, sub_ne_zero]
      exact fun h => (Finset.mem_filter.mp hγS).2 h.symm
  · intro γ hpos hlt
    by_contra hni
    -- if `T - γI` is not invertible, then `γ` is an eigenvalue `≠ α`, so its
    -- distance to `α` lies in `D` and is `≥ δ`, contradicting `‖α - γ‖ < δ`.
    have hev : HasEigenvalue T γ := ((tfae_isEigenvalue T γ).out 0 3).mpr hni
    have hγα : γ ≠ α := (sub_ne_zero.mp (norm_pos_iff.mp hpos)).symm
    have hγS : γ ∈ S := Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hev, hγα⟩
    have hmemD : ‖α - γ‖ ∈ D :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hγS)
    exact absurd hlt (not_lt.mpr (D.min'_le _ hmemD))

/-! 5A.12 {lit}`V = U ⊕ W` with {lit}`U, W` nonzero, and the projection
{lit}`P(u + w) = u`: find all eigenvalues and eigenvectors. -/

/-- The eigenvalues of the projection {lit}`P` — to be determined. -/

-- P(u + w) = u , so for eigenvalue eq, either w = 0 -> lam = 1, and eigenvector any u in U
-- or u = 0 - so lam = 0, and eigenvector any w in W.
def eigenvalues_5A_12 (F : Type*) [Field F] : Set F := {0, 1}

/-- The eigenvectors of the projection {lit}`P` onto {lit}`U` along {lit}`W`
for a scalar {lit}`lam` — to be determined (empty when {lit}`lam` is not an
eigenvalue). -/
noncomputable
def eigenvectors_5A_12 (U W : Submodule F V) (γ : F) : Set V :=
  open Classical in
  if γ = 1 then {v | v ∈ U ∧ v ≠ 0}
  else if γ = 0 then {v | v ∈ W ∧ v ≠ 0}
  else ∅

/-- Every vector splits as {lit}`u + w` with {lit}`u ∈ U`, {lit}`w ∈ W`
(since {lit}`U ⊔ W = ⊤`). -/
private lemma proj_5A_12_decomp {U W : Submodule F V} (hUW : IsCompl U W) (v : V) :
    ∃ u ∈ U, ∃ w ∈ W, u + w = v :=
  Submodule.mem_sup.mp (by rw [hUW.sup_eq_top]; exact Submodule.mem_top)

/-- {lit}`P` fixes exactly the vectors of {lit}`U`: {lit}`P v = v ↔ v ∈ U`. -/
private lemma proj_5A_12_fixed_iff {U W : Submodule F V} (hUW : IsCompl U W)
    {P : V →ₗ[F] V} (hP : ∀ u ∈ U, ∀ w ∈ W, P (u + w) = u) (v : V) :
    P v = v ↔ v ∈ U := by
  constructor
  · intro h
    obtain ⟨u, hu, w, hw, rfl⟩ := proj_5A_12_decomp hUW v
    rw [hP u hu w hw] at h
    have hw0 : w = 0 := add_left_cancel (h.symm.trans (add_zero u).symm)
    rw [hw0, add_zero]; exact hu
  · intro hv
    have := hP v hv 0 (Submodule.zero_mem W)
    rwa [add_zero] at this

/-- {lit}`P` kills exactly the vectors of {lit}`W`: {lit}`P v = 0 ↔ v ∈ W`. -/
private lemma proj_5A_12_zero_iff {U W : Submodule F V} (hUW : IsCompl U W)
    {P : V →ₗ[F] V} (hP : ∀ u ∈ U, ∀ w ∈ W, P (u + w) = u) (v : V) :
    P v = 0 ↔ v ∈ W := by
  constructor
  · intro h
    obtain ⟨u, hu, w, hw, rfl⟩ := proj_5A_12_decomp hUW v
    rw [hP u hu w hw] at h
    rw [h, zero_add]; exact hw
  · intro hv
    have := hP 0 (Submodule.zero_mem U) v hv
    rwa [zero_add] at this

/-- A scalar other than {lit}`0` and {lit}`1` is not an eigenvalue of {lit}`P`:
any {lit}`v` with {lit}`P v = γ v` must be {lit}`0`. -/
private lemma proj_5A_12_eigen_trivial {U W : Submodule F V} (hUW : IsCompl U W)
    {P : V →ₗ[F] V} (hP : ∀ u ∈ U, ∀ w ∈ W, P (u + w) = u)
    {γ : F} (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1) {v : V} (h : P v = γ • v) : v = 0 := by
  obtain ⟨u, hu, w, hw, rfl⟩ := proj_5A_12_decomp hUW v
  rw [hP u hu w hw, smul_add] at h
  -- `(1 - γ) u = γ w`, but the left side is in `U` and the right in `W`,
  -- so both lie in `U ⊓ W = ⊥`; with `γ ≠ 0, 1` this forces `u = w = 0`.
  have hx : (1 - γ) • u = γ • w := by rw [sub_smul, one_smul]; exact sub_eq_of_eq_add' h
  have hmem : (1 - γ) • u ∈ U ⊓ W :=
    Submodule.mem_inf.mpr ⟨U.smul_mem _ hu, by rw [hx]; exact W.smul_mem _ hw⟩
  rw [hUW.inf_eq_bot, Submodule.mem_bot] at hmem
  have huz : u = 0 := (smul_eq_zero.mp hmem).resolve_left (sub_ne_zero.mpr hγ1.symm)
  have hwz : w = 0 := (smul_eq_zero.mp (hx ▸ hmem)).resolve_left hγ0
  rw [huz, hwz, add_zero]

theorem exercise_5A_12a (U W : Submodule F V) (hUW : IsCompl U W)
    (hU : U ≠ ⊥) (hW : W ≠ ⊥) (P : V →ₗ[F] V)
    (hP : ∀ u ∈ U, ∀ w ∈ W, P (u + w) = u) :
    ∀ γ : F, HasEigenvalue P γ ↔ γ ∈ eigenvalues_5A_12 F := by
  intro γ
  simp only [eigenvalues_5A_12, Set.mem_insert_iff, Set.mem_singleton_iff,
    Module.End.hasEigenvalue_iff_exists]
  constructor
  · rintro ⟨v, hv0, hpv⟩
    rcases eq_or_ne γ 0 with h0 | h0
    · exact Or.inl h0
    rcases eq_or_ne γ 1 with h1 | h1
    · exact Or.inr h1
    exact absurd (proj_5A_12_eigen_trivial hUW hP h0 h1 hpv) hv0
  · rintro (rfl | rfl)
    · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨w, hw0, by rw [zero_smul]; exact (proj_5A_12_zero_iff hUW hP w).mpr hw⟩
    · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      exact ⟨u, hu0, by rw [one_smul]; exact (proj_5A_12_fixed_iff hUW hP u).mpr hu⟩

theorem exercise_5A_12b (U W : Submodule F V) (hUW : IsCompl U W)
    (P : V →ₗ[F] V) (hP : ∀ u ∈ U, ∀ w ∈ W, P (u + w) = u) (γ : F) (v : V) :
    HasEigenvector P γ v ↔ v ∈ eigenvectors_5A_12 U W γ := by
  rw [Module.End.hasEigenvector_iff_and]
  simp only [eigenvectors_5A_12]
  split_ifs with h1 h0
  · subst h1; rw [one_smul, Set.mem_setOf_eq, proj_5A_12_fixed_iff hUW hP]; tauto
  · subst h0; rw [zero_smul, Set.mem_setOf_eq, proj_5A_12_zero_iff hUW hP]; tauto
  · rw [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hv0, hpv⟩
    exact hv0 (proj_5A_12_eigen_trivial hUW hP h0 h1 hpv)

/-- 5A.13 (a) {lit}`T` and {lit}`S⁻¹TS` have the same eigenvalues. -/
theorem exercise_5A_13a (T S : V →ₗ[F] V) (hS : IsInvertible S) (γ : F) :
    HasEigenvalue T γ ↔ HasEigenvalue (hS.inv ∘ₗ T ∘ₗ S) γ := by
  -- `S` and `S⁻¹` cancel pointwise, both ways.
  have hSinv : ∀ x, S (hS.inv x) = x := fun x => by
    simpa using LinearMap.congr_fun hS.comp_inv x
  have hinvS : ∀ x, hS.inv (S x) = x := fun x => by
    simpa using LinearMap.congr_fun hS.inv_comp x
  rw [Module.End.hasEigenvalue_iff_exists, Module.End.hasEigenvalue_iff_exists]
  constructor
  · -- If `T v = γ v`, then `S⁻¹ v` is an eigenvector of `S⁻¹TS`:
    -- `S⁻¹TS (S⁻¹ v) = S⁻¹ T v = S⁻¹ (γ v) = γ (S⁻¹ v)`.
    rintro ⟨v, hv0, hTv⟩
    refine ⟨hS.inv v, fun hw => hv0 (by rw [← hSinv v, hw, map_zero]), ?_⟩
    simp only [LinearMap.comp_apply, hSinv, hTv, map_smul]
  · -- Conversely, if `S⁻¹TS w = γ w`, then `S w` is an eigenvector of `T`:
    -- apply `S` to `S⁻¹ (T (S w)) = γ w` to get `T (S w) = γ (S w)`.
    rintro ⟨w, hw0, hTw⟩
    refine ⟨S w, fun hv => hw0 (by rw [← hinvS w, hv, map_zero]), ?_⟩
    have hTw' : hS.inv (T (S w)) = γ • w := by simpa [LinearMap.comp_apply] using hTw
    have h := congr_arg S hTw'
    rwa [hSinv, map_smul] at h

/-- The map carrying each eigenvector of {lit}`T` to an eigenvector of
{lit}`S⁻¹TS` for the same eigenvalue — to be determined. -/
noncomputable
def exercise_5A_13_map (S : V →ₗ[F] V) (hS : IsInvertible S) : V →ₗ[F] V := hS.inv

/-- 5A.13 (b) Determine how the eigenvectors of {lit}`S⁻¹TS` are obtained from
those of {lit}`T`: {lit}`v` is an eigenvector of {lit}`T` iff
{lit}`exercise_5A_13_map S hS v` is an eigenvector of {lit}`S⁻¹TS`. -/
theorem exercise_5A_13b (T S : V →ₗ[F] V) (hS : IsInvertible S) (γ : F)
    (v : V) :
    HasEigenvector T γ v ↔
      HasEigenvector (hS.inv ∘ₗ T ∘ₗ S) γ (exercise_5A_13_map S hS v) := by
  -- `S` and `S⁻¹` cancel pointwise, both ways.
  have hSinv : ∀ x, S (hS.inv x) = x := fun x => by
    simpa using LinearMap.congr_fun hS.comp_inv x
  rw [Module.End.hasEigenvector_iff_and, Module.End.hasEigenvector_iff_and,
    exercise_5A_13_map]
  refine and_congr ?_ ?_
  · -- `v ≠ 0 ↔ S⁻¹ v ≠ 0`, since `S⁻¹` is a bijection.
    constructor
    · exact fun hv hw => hv (by rw [← hSinv v, hw, map_zero])
    · exact fun hw hv => hw (by rw [hv, map_zero])
  · -- `T v = γ v ↔ S⁻¹TS (S⁻¹ v) = γ (S⁻¹ v)`; the right side simplifies to
    -- `S⁻¹ (T v) = γ (S⁻¹ v)`, which is the left side hit with `S⁻¹`.
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hSinv]
    constructor
    · intro h; rw [h, map_smul]
    · intro h
      have h' := congr_arg S h
      rwa [hSinv, map_smul, hSinv] at h'

/-- The double 90° rotation {lit}`(w, x, y, z) ↦ (-x, w, -z, y)` — the
{lit}`Fin 4` analogue of {name}`T_5_9`, rotating each of the two coordinate
planes. -/
def T_5A_14 : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := ![-v 1, v 0, -v 3, v 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- 5A.14 -/
theorem exercise_5A_14 :
    ∃ T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ), ∀ γ : ℝ, ¬ HasEigenvalue T γ := by
  -- Rotating each plane by 90° has no real eigenvalue: the eigenvalue equation
  -- forces `(1 + γ²) vᵢ = 0` in every coordinate, and `1 + γ² > 0`, so `v = 0`.
  refine ⟨T_5A_14, fun γ hev => ?_⟩
  obtain ⟨v, hv, hTv⟩ := Module.End.hasEigenvalue_iff_exists.mp hev
  have h0 : -v 1 = γ * v 0 := congrFun hTv 0
  have h1 : v 0 = γ * v 1 := congrFun hTv 1
  have h2 : -v 3 = γ * v 2 := congrFun hTv 2
  have h3 : v 2 = γ * v 3 := congrFun hTv 3
  have e0 : (1 + γ ^ 2) * v 0 = 0 := by linear_combination h1 - γ * h0
  have e1 : (1 + γ ^ 2) * v 1 = 0 := by linear_combination -h0 - γ * h1
  have e2 : (1 + γ ^ 2) * v 2 = 0 := by linear_combination h3 - γ * h2
  have e3 : (1 + γ ^ 2) * v 3 = 0 := by linear_combination -h2 - γ * h3
  have hpos : (0 : ℝ) < 1 + γ ^ 2 := by positivity
  apply hv
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp e0).resolve_left (ne_of_gt hpos)
  · exact (mul_eq_zero.mp e1).resolve_left (ne_of_gt hpos)
  · exact (mul_eq_zero.mp e2).resolve_left (ne_of_gt hpos)
  · exact (mul_eq_zero.mp e3).resolve_left (ne_of_gt hpos)

/-- 5A.15 -/
theorem exercise_5A_15 [Finite F V] (T : V →ₗ[F] V) (γ : F) :
    HasEigenvalue T γ ↔ HasEigenvalue T.dualMap γ := by
  -- lam is eigen iff T - lam I is injective
  -- iff (T - lam I).dual is surjective (theorem in 3F)
  -- iff T' - lam I' is surjective
  -- I' = I for dual space, so T' - lam I' = T' - lam I_dual
  -- lam is eigenvalue of T.dualMap
  have hdual : (T - γ • LinearMap.id).dualMap
      = T.dualMap - γ • LinearMap.id := by
    ext φ v; simp only [LinearMap.dualMap_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, map_sub, map_smul, smul_eq_mul]
  -- `γ` eigen for `T` ↔ `T − γI` not injective ↔ `(T − γI)'` not surjective
  -- ↔ `T' − γI` not surjective ↔ `γ` eigen for `T'`.
  rw [show HasEigenvalue T γ ↔ _ from (tfae_isEigenvalue T γ).out 0 1,
    show HasEigenvalue T.dualMap γ ↔ _ from (tfae_isEigenvalue T.dualMap γ).out 0 2,
    LADR.Section_3F.injective_iff_dualMap_surjective (T - γ • LinearMap.id), hdual]

/-- 5A.16 -/
theorem exercise_5A_16 {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (hn : 0 < n) {v : Fin n → V} (hv : IsBasis ℂ v) (T : V →ₗ[ℂ] V)
    (γ : ℂ) (hγ : HasEigenvalue T γ) :
    ‖γ‖ ≤ n * Finset.univ.sup' ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
      (fun jk : Fin n × Fin n => ‖LADR.Section_3C.matrixOf hv hv T jk.1 jk.2‖) := by
  -- take an eigenvector corresponding to `γ`
  -- take the maximum absolute value coordinate of the eigenvector - say v_j
  -- it is > 0, otherwise whole vector is zero
  -- M0j * v_0 + ... = γ * v_j
  -- |M0j| * |v_0| + ... = |γ| * |v_j|
  -- |γ| ≤  |M0j| * |v_0| / |v_j| + ... <= |M0j| + ... <= n * M
  classical
  obtain ⟨x, hx0, hTx⟩ := Module.End.hasEigenvalue_iff_exists.mp hγ
  set b := hv.toModuleBasis with hb
  set c : Fin n → ℂ := fun j => b.repr x j with hc
  -- Coordinate form of `T x = γ x`: `∑ₖ A_{j k} cₖ = γ cⱼ` for every `j`.
  have hmv : ∀ j, ∑ k, LADR.Section_3C.matrixOf hv hv T j k * c k = γ * c j := by
    intro j
    have h := congrFun (LinearMap.toMatrix_mulVec_repr b b T x) j
    rw [hTx, map_smul] at h
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h
    -- `h : ((toMatrix b b) T).mulVec (b.repr x) j = γ * (b.repr x) j`, and the
    -- `mulVec` is definitionally the row sum `∑ k, A j k * (b.repr x) k`.
    simpa only [LADR.Section_3C.matrixOf, hc] using h
  -- The eigenvector is nonzero, so some coordinate is nonzero.
  have hcne : ∃ j, c j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    refine hx0 (b.repr.injective ?_)
    rw [map_zero]
    exact Finsupp.ext fun j => by simpa [hc] using hcon j
  -- Pick a coordinate `j₀` of largest modulus; it is strictly positive.
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max (fun j => ‖c j‖)
  have hpos : 0 < ‖c j₀‖ := by
    obtain ⟨j, hj⟩ := hcne
    exact lt_of_lt_of_le (norm_pos_iff.mpr hj) (hj₀ j)
  set S := Finset.univ.sup' (⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩ :
      (Finset.univ : Finset (Fin n × Fin n)).Nonempty)
      (fun jk : Fin n × Fin n => ‖LADR.Section_3C.matrixOf hv hv T jk.1 jk.2‖) with hS
  have hS0 : 0 ≤ S :=
    le_trans (norm_nonneg _)
      (Finset.le_sup' (fun jk : Fin n × Fin n =>
        ‖LADR.Section_3C.matrixOf hv hv T jk.1 jk.2‖) (Finset.mem_univ (j₀, j₀)))
  -- `|γ| · |c_{j₀}| = |∑ₖ A_{j₀ k} cₖ| ≤ ∑ₖ |A_{j₀ k}| |cₖ| ≤ ∑ₖ S · |c_{j₀}| = nS · |c_{j₀}|`.
  have key : ‖γ‖ * ‖c j₀‖ ≤ (n : ℝ) * S * ‖c j₀‖ := by
    calc ‖γ‖ * ‖c j₀‖
        = ‖γ * c j₀‖ := (norm_mul _ _).symm
      _ = ‖∑ k, LADR.Section_3C.matrixOf hv hv T j₀ k * c k‖ := by rw [hmv j₀]
      _ ≤ ∑ k, ‖LADR.Section_3C.matrixOf hv hv T j₀ k * c k‖ := norm_sum_le _ _
      _ = ∑ k, ‖LADR.Section_3C.matrixOf hv hv T j₀ k‖ * ‖c k‖ :=
            Finset.sum_congr rfl fun k _ => norm_mul _ _
      _ ≤ ∑ _k : Fin n, S * ‖c j₀‖ :=
            Finset.sum_le_sum fun k _ =>
              mul_le_mul
                (Finset.le_sup' (fun jk : Fin n × Fin n =>
                  ‖LADR.Section_3C.matrixOf hv hv T jk.1 jk.2‖)
                  (Finset.mem_univ (j₀, k)))
                (hj₀ k) (norm_nonneg _) hS0
      _ = (n : ℝ) * S * ‖c j₀‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
  exact le_of_mul_le_mul_right key hpos

open LADR.Section_1B (Complexification exercise_1B_8) in
open LADR.Section_3B (complexification_map) in
/-- 5A.17 -/
theorem exercise_5A_17 {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (γ : ℝ) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    (HasEigenvalue T γ ↔
      HasEigenvalue (complexification_map T) (γ : ℂ)) := by
  -- using the T v = lam v
  -- and definition smul c x := (c.re • x.1 - c.im • x.2, c.re • x.2 + c.im • x.1)
  -- since lambda is real -> T - lam I, turns into (T - γ • I, T - γ • I)
  -- just repeated twice, the dual map is injective iff T - γ • I is injective
  letI : Module ℂ (Complexification V) := exercise_1B_8 V
  rw [Module.End.hasEigenvalue_iff_exists, Module.End.hasEigenvalue_iff_exists]
  constructor
  · rintro ⟨v, hv, hTv⟩
    refine ⟨(v, 0), fun h => hv (congrArg Prod.fst h), Prod.ext ?_ ?_⟩
    · show T v = γ • v - (0 : ℝ) • (0 : V)
      rw [hTv]; simp
    · show T 0 = γ • (0 : V) + (0 : ℝ) • v
      simp
  · rintro ⟨⟨v₁, v₂⟩, hv, hTv⟩
    have h1 : T v₁ = γ • v₁ - (0 : ℝ) • v₂ := congrArg Prod.fst hTv
    have h2 : T v₂ = γ • v₂ + (0 : ℝ) • v₁ := congrArg Prod.snd hTv
    simp only [zero_smul, sub_zero, add_zero] at h1 h2
    rcases eq_or_ne v₁ 0 with hv₁ | hv₁
    · refine ⟨v₂, ?_, h2⟩
      rintro rfl
      exact hv (by simp [hv₁])
    · exact ⟨v₁, hv₁, h1⟩

open scoped ComplexConjugate in
open LADR.Section_1B (Complexification exercise_1B_8) in
open LADR.Section_3B (complexification_map) in
/-- 5A.18 -/
theorem exercise_5A_18 {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) (lam : ℂ) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    (HasEigenvalue (complexification_map T) lam ↔
      HasEigenvalue (complexification_map T) (conj lam)) := by
  -- same as 17, after expanding
  -- T v = lam v, we have (T v1, T v2) = (lam.re • v1 - lam.im • v2, lam.re • v2 + lam.im • v1)
  -- now if we use (-v1, v2), in (T -v1, T v2) =
  -- (lam.re • (-v1) - lam.im • v2, lam.re • v2 + lam.im • (-v1)) =
  -- (-(lam.re • v1 + lam.im • v2), lam.re • v2 - lam.im • v1) =
  -- (conj lam) • (-v1, v2)
  letI : Module ℂ (Complexification V) := exercise_1B_8 V
  -- If `(v₁, v₂)` is an eigenvector for `μ`, then `(v₁, -v₂)` is one for `conj μ`.
  have key : ∀ μ : ℂ,
      (∃ v : Complexification V, v ≠ 0 ∧ (complexification_map T) v = μ • v) →
      ∃ v : Complexification V, v ≠ 0 ∧ (complexification_map T) v = (conj μ) • v := by
    rintro μ ⟨⟨v₁, v₂⟩, hv, hTv⟩
    have h1 : T v₁ = μ.re • v₁ - μ.im • v₂ := congrArg Prod.fst hTv
    have h2 : T v₂ = μ.re • v₂ + μ.im • v₁ := congrArg Prod.snd hTv
    refine ⟨(v₁, -v₂), ?_, Prod.ext ?_ ?_⟩
    · intro h
      obtain ⟨e1, e2⟩ := Prod.mk_eq_zero.mp h
      exact hv (Prod.mk_eq_zero.mpr ⟨e1, neg_eq_zero.mp e2⟩)
    · show T v₁ = (conj μ).re • v₁ - (conj μ).im • (-v₂)
      simp only [Complex.conj_re, Complex.conj_im, neg_smul, smul_neg, neg_neg]
      rw [h1]
    · show T (-v₂) = (conj μ).re • (-v₂) + (conj μ).im • v₁
      rw [map_neg]
      simp only [Complex.conj_re, Complex.conj_im, neg_smul, smul_neg]
      rw [h2]; abel
  rw [Module.End.hasEigenvalue_iff_exists, Module.End.hasEigenvalue_iff_exists]
  constructor
  · exact key lam
  · intro h
    simpa using key (conj lam) h

/-- 5A.19 -/
def forwardShift : (ℕ → F) →ₗ[F] (ℕ → F) where
  toFun x := fun i => match i with
    | 0 => 0
    | n + 1 => x n
  map_add' x y := by
    funext i
    cases i <;> simp
  map_smul' a x := by
    funext i
    cases i <;> simp

theorem exercise_5A_19 : ∀ γ : F, ¬ HasEigenvalue (forwardShift (F := F)) γ := by
  -- assume it does T v = lam v -> lam (v i) = v (i - 1), and lam v 0 = 0
  -- assume lam = 0 -> v i = 0 for all i, contradiction
  -- so v 0 = 0 - base case
  -- use induction on i to show that v i = 0 for all i, contradicting v ≠ 0
  intro γ hev
  rw [Module.End.hasEigenvalue_iff_exists] at hev
  obtain ⟨x, hx, hTx⟩ := hev
  -- Coordinate 0 of `forwardShift x = γ • x` gives `γ * x 0 = 0`.
  have h0 : γ * x 0 = 0 := by have := congrFun hTx 0; simpa [forwardShift] using this.symm
  -- Coordinate `n + 1` gives the recurrence `x n = γ * x (n + 1)`.
  have hrec : ∀ n, x n = γ * x (n + 1) := by
    intro n; have := congrFun hTx (n + 1); simpa [forwardShift] using this
  -- Either way every coordinate vanishes, contradicting `x ≠ 0`.
  have hall : ∀ i, x i = 0 := by
    rcases eq_or_ne γ 0 with hγ | hγ
    · intro i; rw [hrec i, hγ, zero_mul]
    · intro i
      induction i with
      | zero => exact (mul_eq_zero.mp h0).resolve_left hγ
      | succ n ih =>
          have hn : γ * x (n + 1) = 0 := by rw [← hrec n]; exact ih
          exact (mul_eq_zero.mp hn).resolve_left hγ
  exact hx (funext hall)

open LADR.Section_3A (backwardShift) in
/-- 5A.20 -/
theorem exercise_5A_20a : ∀ γ : F, HasEigenvalue (backwardShift (F := F)) γ := by
  -- use v = fun i => γ ^ i
  intro γ
  rw [Module.End.hasEigenvalue_iff_exists]
  refine ⟨fun i => γ ^ i, ?_, ?_⟩
  · intro h; have := congrFun h 0; simp at this
  · funext i
    simp only [backwardShift, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
    ring

/-- The eigenvectors of the backward shift for an eigenvalue {lit}`γ` — to be
determined. -/
def eigenvectors_5A_20 (F : Type*) [Field F] (γ : F) : Set (ℕ → F) :=
  -- expanding per coordinate - v (i + 1) = λ • v i, so v i = λ^i • v 0
  {x | x ≠ 0 ∧ ∀ i, x i = γ ^ i * x 0}

open LADR.Section_3A (backwardShift) in
/-- 5A.20 (b) Find all eigenvectors of the backward shift. -/
theorem exercise_5A_20b (γ : F) (x : ℕ → F) :
    HasEigenvector (backwardShift (F := F)) γ x ↔ x ∈ eigenvectors_5A_20 F γ := by
  rw [Module.End.hasEigenvector_iff_and, eigenvectors_5A_20, Set.mem_setOf_eq]
  -- The recurrence `x (i+1) = γ * x i` is equivalent to `x i = γ ^ i * x 0`.
  have hbs_iff : backwardShift x = γ • x ↔ ∀ i, x (i + 1) = γ * x i := by
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    simp [backwardShift, Pi.smul_apply, smul_eq_mul]
  refine and_congr_right fun _ => ?_
  rw [hbs_iff]
  constructor
  · intro h i
    induction i with
    | zero => simp
    | succ n ih => rw [h n, ih]; ring
  · intro h i
    rw [h (i + 1), h i]; ring

/-- 5A.21 (a) -/
theorem exercise_5A_21a (T : V →ₗ[F] V) (hT : IsInvertible T) (γ : F)
    (hγ : γ ≠ 0) :
    HasEigenvalue T γ ↔ HasEigenvalue hT.inv γ⁻¹ := by
  -- by def T v = lam v ↔ Tinv T v = Tinv lam v ↔ v = lam Tinv v \iff (1/lam) v = Tinv v
  rw [Module.End.hasEigenvalue_iff_exists, Module.End.hasEigenvalue_iff_exists]
  have hTinv : ∀ v, hT.inv (T v) = v := fun v => LinearMap.congr_fun hT.inv_comp v
  have hinvT : ∀ v, T (hT.inv v) = v := fun v => LinearMap.congr_fun hT.comp_inv v
  constructor
  · rintro ⟨v, hv, hTv⟩
    refine ⟨v, hv, ?_⟩
    have h : v = γ • hT.inv v := by
      have h2 := congrArg hT.inv hTv
      rwa [hTinv, map_smul] at h2
    calc hT.inv v = (γ⁻¹ * γ) • hT.inv v := by rw [inv_mul_cancel₀ hγ, one_smul]
      _ = γ⁻¹ • (γ • hT.inv v) := by rw [mul_smul]
      _ = γ⁻¹ • v := by rw [← h]
  · rintro ⟨v, hv, hTv⟩
    refine ⟨v, hv, ?_⟩
    have h : v = γ⁻¹ • T v := by
      have h2 := congrArg T hTv
      rwa [hinvT, map_smul] at h2
    calc T v = (γ * γ⁻¹) • T v := by rw [mul_inv_cancel₀ hγ, one_smul]
      _ = γ • (γ⁻¹ • T v) := by rw [mul_smul]
      _ = γ • v := by rw [← h]

/-- 5A.21 (b) {lit}`T` and {lit}`T⁻¹` have the same eigenvectors. -/
theorem exercise_5A_21b (T : V →ₗ[F] V) (hT : IsInvertible T) (v : V) :
    (∃ γ, HasEigenvector T γ v) ↔ (∃ γ, HasEigenvector hT.inv γ v) := by
  -- same as a)
  have hTinv : ∀ w, hT.inv (T w) = w := fun w => LinearMap.congr_fun hT.inv_comp w
  have hinvT : ∀ w, T (hT.inv w) = w := fun w => LinearMap.congr_fun hT.comp_inv w
  constructor
  · rintro ⟨γ, hev⟩
    rw [Module.End.hasEigenvector_iff_and] at hev
    obtain ⟨hv, hTv⟩ := hev
    have hγ : γ ≠ 0 := by
      rintro rfl
      exact hv (by rw [← hTinv v, hTv, zero_smul, map_zero])
    refine ⟨γ⁻¹, Module.End.hasEigenvector_iff_and.mpr ⟨hv, ?_⟩⟩
    have h : v = γ • hT.inv v := by
      have h2 := congrArg hT.inv hTv
      rwa [hTinv, map_smul] at h2
    calc hT.inv v = (γ⁻¹ * γ) • hT.inv v := by rw [inv_mul_cancel₀ hγ, one_smul]
      _ = γ⁻¹ • (γ • hT.inv v) := by rw [mul_smul]
      _ = γ⁻¹ • v := by rw [← h]
  · rintro ⟨γ, hev⟩
    rw [Module.End.hasEigenvector_iff_and] at hev
    obtain ⟨hv, hTv⟩ := hev
    have hγ : γ ≠ 0 := by
      rintro rfl
      exact hv (by rw [← hinvT v, hTv, zero_smul, map_zero])
    refine ⟨γ⁻¹, Module.End.hasEigenvector_iff_and.mpr ⟨hv, ?_⟩⟩
    have h : v = γ • T v := by
      have h2 := congrArg T hTv
      rwa [hinvT, map_smul] at h2
    calc T v = (γ⁻¹ * γ) • T v := by rw [inv_mul_cancel₀ hγ, one_smul]
      _ = γ⁻¹ • (γ • T v) := by rw [mul_smul]
      _ = γ⁻¹ • v := by rw [← h]

/-- 5A.22 -/
theorem exercise_5A_22 (T : V →ₗ[F] V) (u w : V) (hu : u ≠ 0) (_ : w ≠ 0)
    (huw : T u = 3 • w) (hwu : T w = 3 • u) :
    HasEigenvalue T 3 ∨ HasEigenvalue T (-3) := by
  -- consider u + w, T (u + w) = 3 (u + w), so 3 is an eigenvalue
  -- unless u + w = 0, but then u = -w , so T u = -3 u, so -3 is eigenvalue
  -- so we proved both are eigenvaludes
  by_cases h : u + w = 0
  · -- `u + w = 0`, so `w = -u` and `T u = 3 • (-u) = (-3) • u`.
    right
    rw [Module.End.hasEigenvalue_iff_exists]
    refine ⟨u, hu, ?_⟩
    have hwu' : w = -u := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    -- `3` in the hypotheses is `ℕ`-smul while the eigenvalue is `F`-smul; `module` bridges them.
    rw [huw, hwu']; module
  · -- `u + w ≠ 0` is an eigenvector for `3`.
    left
    rw [Module.End.hasEigenvalue_iff_exists]
    refine ⟨u + w, h, ?_⟩
    rw [map_add, huw, hwu]; module

/-- 5A.23 -/
theorem exercise_5A_23 [Finite F V] (S T : V →ₗ[F] V) (γ : F) :
    HasEigenvalue (S ∘ₗ T) γ ↔ HasEigenvalue (T ∘ₗ S) γ := by
  -- assume S T v = lam v, then T S T v = T (lam v) = lam (T v)
  -- so lam is eigenvalue, by symmetry the other direction (is there a tactic for that)
  -- special care if T v = 0, then S T = 0, so lam = 0, which is still an eigenvalue.
  -- by finite assumption since T is not a bijection, neither is T S, and thus
  -- zero is an eigenvalue.
  -- Prove one implication generally and apply it with `S`, `T` swapped.
  suffices h : ∀ S T : V →ₗ[F] V,
      HasEigenvalue (S ∘ₗ T) γ → HasEigenvalue (T ∘ₗ S) γ from ⟨h S T, h T S⟩
  intro S T hev
  rw [Module.End.hasEigenvalue_iff_exists] at hev
  obtain ⟨v, hv, hTv⟩ := hev
  by_cases hTv0 : T v = 0
  · -- `T v = 0` forces `γ = 0`; then `T` is not injective, so neither is `T ∘ₗ S`.
    have hTninj : ¬ Function.Injective T := fun hinj => hv (hinj (by rw [hTv0, map_zero]))
    have hTnsurj : ¬ Function.Surjective T :=
      (not_congr (LADR.Section_3D.injective_iff_surjective rfl T)).mp hTninj
    have hγ0 : γ = 0 := by
      have h0 : γ • v = 0 := by
        have he := hTv
        rw [LinearMap.comp_apply, hTv0, map_zero] at he
        exact he.symm
      exact (smul_eq_zero.mp h0).resolve_right hv
    subst hγ0
    rw [show HasEigenvalue (T ∘ₗ S) (0 : F) ↔ _ from (tfae_isEigenvalue (T ∘ₗ S) 0).out 0 2,
      zero_smul, sub_zero]
    intro hTScomp
    rw [LinearMap.coe_comp] at hTScomp
    exact hTnsurj hTScomp.of_comp
  · -- `T v ≠ 0`: it is an eigenvector of `T ∘ₗ S` for `γ`.
    rw [Module.End.hasEigenvalue_iff_exists]
    refine ⟨T v, hTv0, ?_⟩
    rw [LinearMap.comp_apply]
    have hStv : S (T v) = γ • v := hTv
    rw [hStv, map_smul]

open LADR.Section_3A (fromFnToFm) in
/-- 5A.24 (a) -/
theorem exercise_5A_24a {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → F)
    (h : ∀ i, ∑ j, A i j = 1) :
    HasEigenvalue (fromFnToFm A) 1 := by
  -- expand the definition ot T v for v = (1, 1, ...) = ∑ j, A i j • 1 = ∑ j, A i j = 1
  -- thus
  rw [Module.End.hasEigenvalue_iff_exists]
  refine ⟨1, ?_, ?_⟩
  · -- the all-ones vector is nonzero since `n > 0`
    intro hcon
    exact one_ne_zero (α := F) (by simpa using congrFun hcon ⟨0, hn⟩)
  · funext i
    simp only [fromFnToFm, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, mul_one,
      Pi.smul_apply, smul_eq_mul]
    exact h i

open LADR.Section_3A (fromFnToFm) in
set_option maxHeartbeats 800000 in
/-- 5A.24 (b) -/
theorem exercise_5A_24b {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → F)
    (h : ∀ j, ∑ i, A i j = 1) :
    HasEigenvalue (fromFnToFm A) 1 := by
  -- use previous proof that A.dual has same eigenvalues and then apply part (a) to A.dual
  -- matrix of dual is A.transopose and col becomes rows
  classical
  set B := Pi.basisFun F (Fin n) with hB
  -- `fromFnToFm M` is `M` viewed as an operator in the standard basis.
  have hToLin : ∀ M : Matrix (Fin n) (Fin n) F, Matrix.toLin B B M = fromFnToFm M := by
    intro M
    refine LinearMap.ext fun v => ?_
    show Matrix.toLin B B M v = fromFnToFm M v
    ext j
    rw [Matrix.toLin_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, fromFnToFm, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single j] <;> simp_all [eq_comm]
  -- Eigenvalues are preserved under conjugation by a linear equivalence (across spaces).
  have hev_conj : ∀ {M₁ M₂ : Type _} [AddCommGroup M₁] [Module F M₁] [AddCommGroup M₂]
      [Module F M₂] (e : M₁ ≃ₗ[F] M₂) (f : M₁ →ₗ[F] M₁),
      HasEigenvalue (e.conj f) 1 ↔ HasEigenvalue f 1 := by
    intro M₁ M₂ _ _ _ _ e f
    rw [Module.End.hasEigenvalue_iff_exists, Module.End.hasEigenvalue_iff_exists]
    constructor
    · rintro ⟨w, hw, hfw⟩
      refine ⟨e.symm w, by simpa using hw, ?_⟩
      rw [LinearEquiv.conj_apply_apply] at hfw
      exact e.injective (by rw [map_smul]; simpa using hfw)
    · rintro ⟨v, hv, hfv⟩
      exact ⟨e v, by simpa using hv, by
        rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hfv, map_smul]⟩
  -- Two bases of (possibly different) spaces give conjugate `toLin`s of the same matrix.
  have hconj : ∀ {M₁ M₂ : Type _} [AddCommGroup M₁] [Module F M₁] [AddCommGroup M₂] [Module F M₂]
      (c : Module.Basis (Fin n) F M₁) (d : Module.Basis (Fin n) F M₂)
      (M : Matrix (Fin n) (Fin n) F),
      (c.equiv d (Equiv.refl _)).conj (Matrix.toLin c c M) = Matrix.toLin d d M := by
    intro M₁ M₂ _ _ _ _ c d M
    refine d.ext fun j => ?_
    rw [LinearEquiv.conj_apply_apply]
    have hsymm : (c.equiv d (Equiv.refl (Fin n))).symm (d j) = c j := by
      rw [Module.Basis.equiv_symm, Module.Basis.equiv_apply]; rfl
    rw [hsymm, Matrix.toLin_self, map_sum, Matrix.toLin_self]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Module.Basis.equiv_apply]; rfl
  -- Part (a) applied to `Aᵀ`: its rows are the columns of `A`, which sum to `1`.
  have hAT : HasEigenvalue (fromFnToFm (Matrix.transpose A)) 1 :=
    exercise_5A_24a hn (Matrix.transpose A) fun i => by
      simp only [Matrix.transpose_apply]; exact h i
  -- `1 ∈ eigenvalues (A)  ⟺  ∈ eigenvalues (A.dualMap)  ⟺  ∈ eigenvalues (Aᵀ, in dual basis)`,
  -- the middle step being 3.132 (`Matrix.toLin_transpose`, `M(T') = Aᵀ`).
  rw [exercise_5A_15 (fromFnToFm A) 1, ← hToLin, LinearMap.dualMap_def,
    ← Matrix.toLin_transpose, ← hconj B B.dualBasis (Matrix.transpose A), hev_conj, hToLin]
  exact hAT

/-- 5A.25 -/
theorem exercise_5A_25 (T : V →ₗ[F] V) (u w : V) (a b : F)
    (hu : HasEigenvector T a u) (hw : HasEigenvector T b w)
    (huw : ∃ c, HasEigenvector T c (u + w)) : a = b := by
  -- T u = a u, T w = b w, T (u + w) = c (u + w)
  -- T (u + w) = a u + b w = c u + c w
  -- if u and w are lin dep, then u = d w, and subbing in eigen eq, we get a = b
  -- if independent we have to have a = c and b = c, to make the equation work
  rw [Module.End.hasEigenvector_iff_and] at hu hw
  obtain ⟨hu0, hTu⟩ := hu
  obtain ⟨hw0, hTw⟩ := hw
  obtain ⟨c, hc⟩ := huw
  rw [Module.End.hasEigenvector_iff_and] at hc
  obtain ⟨-, hTuw⟩ := hc
  -- `T (u + w) = c (u + w)` combined with `T u = a u`, `T w = b w` gives
  -- `(a − c) • u + (b − c) • w = 0`.
  have e0 : (a - c) • u + (b - c) • w = 0 := by
    have hsum : a • u + b • w = c • u + c • w := by
      have := hTuw; rw [map_add, hTu, hTw, smul_add] at this; exact this
    linear_combination (norm := module) hsum
  by_cases hdep : ∃ d : F, u = d • w
  · -- `u` and `w` are linearly dependent: `u = d • w` with `d ≠ 0`.  Then
    -- `T u = a • u` and `T u = d • T w = b • u`, so `a = b`.
    obtain ⟨d, hd⟩ := hdep
    have hd0 : d ≠ 0 := fun h => hu0 (by rw [hd, h, zero_smul])
    have h2 : a • u = (d * b) • w := by rw [← hTu, hd, map_smul, hTw, smul_smul]
    have h3 : (a * d) • w = (d * b) • w := by rw [← smul_smul, ← hd]; exact h2
    have h4 : a * d - d * b = 0 :=
      (smul_eq_zero.mp (by rw [sub_smul, h3, sub_self])).resolve_right hw0
    exact mul_right_cancel₀ hd0 (by rw [sub_eq_zero.mp h4, mul_comm])
  · -- `u` and `w` are linearly independent (`u` is no multiple of `w`).  Then in
    -- `(a − c) • u + (b − c) • w = 0` both coefficients vanish, so `a = c = b`.
    have hac : a - c = 0 := by
      by_contra hne
      refine hdep ⟨(a - c)⁻¹ * (c - b), ?_⟩
      have hrel : (a - c) • u = (c - b) • w := by linear_combination (norm := module) e0
      rw [mul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hac, zero_smul, zero_add] at e0
    have hbc : b - c = 0 := (smul_eq_zero.mp e0).resolve_right hw0
    exact (sub_eq_zero.mp hac).trans (sub_eq_zero.mp hbc).symm

/-- 5A.26 -/
theorem exercise_5A_26 (T : V →ₗ[F] V)
    (h : ∀ v : V, v ≠ 0 → ∃ γ : F, HasEigenvector T γ v) :
    ∃ c : F, T = c • LinearMap.id := by
  sorry

/-- 5A.27 -/
theorem exercise_5A_27 [Finite F V] (T : V →ₗ[F] V) (k : ℕ+)
    (hk' : k ≤ finrank F V - 1)
    (h : ∀ U : Submodule F V, finrank F U = k → InvariantUnder T U) :
    ∃ c : F, T = c • LinearMap.id := by
  sorry

/-- 5A.28 -/
theorem exercise_5A_28 [Finite F V] (T : V →ₗ[F] V) {m : ℕ}
    (γ : Fin m → F) (hγ : Function.Injective γ)
    (hev : ∀ k, HasEigenvalue T (γ k)) :
    m ≤ 1 + finrank F (range T) := by
  sorry

/-- 5A.29 -/
theorem exercise_5A_29 (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (h4 : HasEigenvalue T (-4)) (h5 : HasEigenvalue T 5)
    (h7 : HasEigenvalue T (Real.sqrt 7)) :
    ∃ x : Fin 3 → ℝ, T x - 9 • x = ![-4, 5, Real.sqrt 7] := by
  sorry

/-- 5A.30 -/
theorem exercise_5A_30 (T : V →ₗ[F] V)
    (h : (T - 2 • LinearMap.id) ∘ₗ (T - 3 • LinearMap.id) ∘ₗ
      (T - 4 • LinearMap.id) = 0)
    (γ : F) (hγ : HasEigenvalue T γ) :
    γ = 2 ∨ γ = 3 ∨ γ = 4 := by
  sorry

/-- 5A.31 -/
theorem exercise_5A_31 :
    ∃ T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), T ^ 4 = -LinearMap.id := by
  sorry

/-- 5A.32 -/
theorem exercise_5A_32 (T : V →ₗ[F] V)
    (h : ∀ γ : F, ¬ HasEigenvalue T γ) (h4 : T ^ 4 = LinearMap.id) :
    T ^ 2 = -LinearMap.id := by
  sorry

/-- 5A.33 (a) -/
theorem exercise_5A_33a (T : V →ₗ[F] V) (m : ℕ+) :
    Function.Injective T ↔ Function.Injective (T ^ m.val) := by
  sorry

/-- 5A.33 (b) -/
theorem exercise_5A_33b (T : V →ₗ[F] V) (m : ℕ+) :
    Function.Surjective T ↔ Function.Surjective (T ^ m.val) := by
  sorry

/-- 5A.34 -/
theorem exercise_5A_34 [Finite F V] {m : ℕ} (v : Fin m → V) :
    LinearIndependent F v ↔
      ∃ (T : V →ₗ[F] V) (γ : Fin m → F), Function.Injective γ ∧
        ∀ k, HasEigenvector T (γ k) (v k) := by
  sorry

/-- 5A.35 -/
theorem exercise_5A_35 {n : ℕ} (γ : Fin n → ℝ)
    (hγ : Function.Injective γ) :
    LinearIndependent ℝ (fun k => fun x : ℝ => Real.exp (γ k * x)) := by
  sorry

/-- 5A.36  -/
theorem exercise_5A_36 {n : ℕ} (γ : Fin n → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ k, 0 < γ k) :
    LinearIndependent ℝ (fun k => fun x : ℝ => Real.cos (γ k * x)) := by
  sorry

/-- 5A.37 -/
theorem exercise_5A_37 [Finite F V] (T : V →ₗ[F] V) (γ : F) :
    HasEigenvalue (LinearMap.mulLeft F T : (V →ₗ[F] V) →ₗ[F] (V →ₗ[F] V)) γ ↔
      HasEigenvalue T γ := by
  sorry

/-- 5A.38 (a) -/
def exercise_5A_38_quotient_op (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) : V ⧸ U →ₗ[F] V ⧸ U :=
  Submodule.mapQ U U T (by sorry)

-- The defining property from Axler.
example (T : V →ₗ[F] V) (U : Submodule F V) (hU : InvariantUnder T U)
    (v : V) :
    exercise_5A_38_quotient_op T U hU (U.mkQ v) = U.mkQ (T v) := by
  simp [exercise_5A_38_quotient_op, Submodule.mapQ_apply]

/-- 5A.38 (b) -/
theorem exercise_5A_38b [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) (γ : F)
    (h : HasEigenvalue (exercise_5A_38_quotient_op T U hU) γ) :
    HasEigenvalue T γ := by
  sorry

/-- 5A.39 -/
theorem exercise_5A_39 [Finite F V] (T : V →ₗ[F] V) :
    (∃ γ : F, HasEigenvalue T γ) ↔
      ∃ U : Submodule F V, InvariantUnder T U ∧
        finrank F U = finrank F V - 1 := by
  sorry

/-- 5A.40 -/
theorem exercise_5A_40 (S T : V →ₗ[F] V) (hS : IsInvertible S)
    (p : Polynomial F) :
    aeval (S ∘ₗ T ∘ₗ hS.inv) p = S ∘ₗ aeval T p ∘ₗ hS.inv := by
  sorry

/-- 5A.41 -/
theorem exercise_5A_41 (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) (p : Polynomial F) :
    InvariantUnder (aeval T p) U := by
  sorry

/-- 5A.42 {lit}`T(x₁, …, xₙ) = (x₁, 2x₂, 3x₃, …, nxₙ)` on {lit}`ℝⁿ`. -/
def T_ex_5A_42 (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun v := fun j => ((j : ℕ) + 1) * v j
  map_add' x y := by
    funext j
    simp [mul_add]
  map_smul' a x := by
    funext j
    simp
    ring

/-- (a) The set of eigenvalues of {lit}`T_ex_5A_42 n` — to be determined. -/
def eigenvalues_5A_42 (n : ℕ) : Set ℝ := sorry

/-- The eigenvectors of {lit}`T_ex_5A_42 n` for a scalar {lit}`γ` — to be
determined (empty when {lit}`γ` is not an eigenvalue). -/
def eigenvectors_5A_42 (n : ℕ) (γ : ℝ) : Set (Fin n → ℝ) := sorry

theorem exercise_5A_42a (n : ℕ) :
    (∀ γ : ℝ,
      HasEigenvalue (T_ex_5A_42 n) γ ↔ γ ∈ eigenvalues_5A_42 n) ∧
    (∀ (γ : ℝ) (v : Fin n → ℝ),
      HasEigenvector (T_ex_5A_42 n) γ v ↔ v ∈ eigenvectors_5A_42 n γ) := by
  sorry

/-- The invariant subspaces of {lit}`T_ex_5A_42 n` — to be determined. -/
def invariantSubspaces_5A_42 (n : ℕ) : Set (Submodule ℝ (Fin n → ℝ)) := sorry

/-- 5A.42 (b) Find all invariant subspaces of {lit}`T`. -/
theorem exercise_5A_42b (n : ℕ) (U : Submodule ℝ (Fin n → ℝ)) :
    InvariantUnder (T_ex_5A_42 n) U ↔ U ∈ invariantSubspaces_5A_42 n := by
  sorry

/-- 5A.43 -/
theorem exercise_5A_43 [Finite F V] (hV : 1 < finrank F V)
    (T : V →ₗ[F] V) :
    ∃ S : V →ₗ[F] V, ∀ p : Polynomial F, aeval T p ≠ S := by
  sorry

end LADR.Section_5A
