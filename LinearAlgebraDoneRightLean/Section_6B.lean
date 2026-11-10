import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import LinearAlgebraDoneRightLean.Section_5C
import LinearAlgebraDoneRightLean.Section_6A
import LinearAlgebraDoneRightLean.L2Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 6B: Orthonormal Bases
-/

namespace LADR.Section_6B

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-! # Orthonormal Lists and the Gram–Schmidt Procedure -/

/-! 6.22 Definition: orthonormal

A list {lit}`e₁, …, eₘ` is *orthonormal* if each vector has norm 1 and distinct
vectors are orthogonal, i.e. {lit}`⟨eⱼ, eₖ⟩ = 1` if {lit}`j = k` and {lit}`0`
otherwise. This is mathlib's {name}`Orthonormal` (indexing the list by a type
{lit}`ι`; for a length-{lit}`m` list take {lit}`ι = Fin m`). -/

recall orthonormal_iff_ite {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {ι : Type*} [DecidableEq ι]
    {v : ι → E} :
    Orthonormal 𝕜 v ↔ ∀ i j, ⟪v i, v j⟫_𝕜 = if i = j then (1 : 𝕜) else (0 : 𝕜)

/-! 6.23 Example: orthonormal lists.

(a) The standard basis of {lit}`𝔽ⁿ` is orthonormal. -/

example {n : ℕ} : Orthonormal 𝕜 (EuclideanSpace.basisFun (Fin n) 𝕜) :=
  (EuclideanSpace.basisFun (Fin n) 𝕜).orthonormal

/-! (b) {lit}`(1/√3, 1/√3, 1/√3), (−1/√2, 1/√2, 0)` is an orthonormal list in
{lit}`𝔽³`. -/

example : Orthonormal 𝕜
    (![!₂[(Real.sqrt 3)⁻¹, (Real.sqrt 3)⁻¹, (Real.sqrt 3)⁻¹],
       !₂[-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0]] :
      Fin 2 → EuclideanSpace 𝕜 (Fin 3)) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
      Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      RCLike.conj_ofReal, map_inv₀, map_neg, map_zero, mul_zero, zero_mul, add_zero,
      Fin.isValue, Fin.reduceEq, reduceIte] <;>
    norm_cast <;>
    field_simp <;>
    nlinarith [h2, h3]

/-! (c) {lit}`(1/√3, 1/√3, 1/√3), (−1/√2, 1/√2, 0), (1/√6, 1/√6, −2/√6)` is an
orthonormal list in {lit}`𝔽³`. -/

example : Orthonormal 𝕜
    (![!₂[(Real.sqrt 3)⁻¹, (Real.sqrt 3)⁻¹, (Real.sqrt 3)⁻¹],
       !₂[-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 0],
       !₂[(Real.sqrt 6)⁻¹, (Real.sqrt 6)⁻¹, -(2 * (Real.sqrt 6)⁻¹)]] :
      Fin 3 → EuclideanSpace 𝕜 (Fin 3)) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  have h6' : Real.sqrt 6 ≠ 0 := by positivity
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
      Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      RCLike.conj_ofReal, map_inv₀, map_neg, map_mul, map_ofNat, map_zero, mul_zero,
      zero_mul, add_zero, Fin.isValue, Fin.reduceEq, reduceIte] <;>
    norm_cast <;>
    field_simp <;>
    nlinarith [h2, h3, h6]

/-! (d) For each positive integer {lit}`n`, the {lit}`2n + 1` functions
{lit}`1/√(2π)` and {lit}`(cos kx)/√π, (sin kx)/√π` for {lit}`k = 1, …, n` form an
orthonormal list in {lit}`C[-π, π]` with {lit}`⟨f, g⟩ = ∫_{-π}^{π} fg`. The book leaves
this to Exercise 4; see {lit}`exercise_6B_4` below.

(e) Dividing the standard basis {lit}`1, x, x²` of {lit}`𝒫₂(ℝ)` (with
{lit}`⟨p, q⟩ = ∫_{-1}^{1} pq`) by norms gives {lit}`1/√2, √(3/2)·x, √(5/2)·x²`; this
is *not* orthonormal, since the first and third vectors are not orthogonal:
{lit}`⟨1/√2, √(5/2)·x²⟩ = √5/3 ≠ 0`. We model {lit}`𝒫₂(ℝ)` inside {lit}`C[-1,1]` with
the {lit}`L²` inner product from the skippable {lit}`L2Interval.lean` infrastructure. -/

section L2Bridge

open MeasureTheory

/-- Bridge for computing the `L²` inner product on {lit}`C[a,b]`: for continuous
{lit}`f, g` on {lit}`ℝ`, the inner product of their restrictions to {lit}`[a,b]` is the
ordinary interval integral {lit}`∫ₐᵇ f g`. -/
theorem L2C_inner_restrict {a b : ℝ} [Fact (a < b)] (f g : C(ℝ, ℝ)) :
    ⟪(show L2C a b from f.restrict _), (show L2C a b from g.restrict _)⟫_ℝ
      = ∫ x in a..b, f x * g x := by
  have hab : a ≤ b := le_of_lt Fact.out
  calc _ = ∫ x : ↥(Set.Icc a b), (fun y => f y * g y) (x : ℝ) := rfl
    _ = ∫ x in Set.Icc a b, f x * g x :=
        integral_subtype_comap measurableSet_Icc (fun y => f y * g y)
    _ = ∫ x in a..b, f x * g x := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- The same bridge for functions that are only continuous on {lit}`[a,b]`. -/
theorem L2C_inner_of_continuousOn {a b : ℝ} [Fact (a < b)] (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b)) :
    ⟪(show L2C a b from (⟨(Set.Icc a b).restrict f, hf.restrict⟩ : C(Set.Icc a b, ℝ))),
      (show L2C a b from (⟨(Set.Icc a b).restrict g, hg.restrict⟩ : C(Set.Icc a b, ℝ)))⟫_ℝ
      = ∫ x in a..b, f x * g x := by
  have hab : a ≤ b := le_of_lt Fact.out
  calc _ = ∫ x : ↥(Set.Icc a b), (fun y => f y * g y) (x : ℝ) := rfl
    _ = ∫ x in Set.Icc a b, f x * g x :=
        integral_subtype_comap measurableSet_Icc (fun y => f y * g y)
    _ = ∫ x in a..b, f x * g x := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

end L2Bridge

/-- The interval {lit}`[-1,1]` is nondegenerate, so {lit}`C[-1,1]` carries the `L²` inner
product (see `L2Interval.lean`). -/
instance : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩

/-- 6.23(e): {lit}`⟨1/√2, √(5/2)·x²⟩ = ∫₋₁¹ (√5/2)x² = √5/3` in {lit}`C[-1,1]`. -/
theorem example_6_23e_inner :
    ⟪(show L2C (-1) 1 from (ContinuousMap.const ℝ (Real.sqrt 2)⁻¹).restrict _),
      (show L2C (-1) 1 from
        (⟨fun x => Real.sqrt (5 / 2) * x ^ 2, by fun_prop⟩ : C(ℝ, ℝ)).restrict _)⟫_ℝ
      = Real.sqrt 5 / 3 := by
  rw [L2C_inner_restrict]
  simp only [ContinuousMap.const_apply, ContinuousMap.coe_mk]
  simp_rw [← mul_assoc]
  rw [intervalIntegral.integral_const_mul, integral_pow,
    Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  norm_num

/-- 6.23(e): hence the normalized list {lit}`1/√2, √(3/2)·x, √(5/2)·x²` is not
orthonormal. -/
theorem example_6_23e : ¬ Orthonormal ℝ
    ![(show L2C (-1) 1 from (ContinuousMap.const ℝ (Real.sqrt 2)⁻¹).restrict _),
      (show L2C (-1) 1 from
        (⟨fun x => Real.sqrt (3 / 2) * x, by fun_prop⟩ : C(ℝ, ℝ)).restrict _),
      (show L2C (-1) 1 from
        (⟨fun x => Real.sqrt (5 / 2) * x ^ 2, by fun_prop⟩ : C(ℝ, ℝ)).restrict _)] := by
  intro h
  have h02 := h.2 (show (0 : Fin 3) ≠ 2 by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at h02
  rw [example_6_23e_inner] at h02
  have : 0 < Real.sqrt 5 := by positivity
  linarith

/-! 6.24 Norm of an orthonormal linear combination

If {lit}`e₁, …, eₘ` is orthonormal, then
{lit}`‖a₁e₁ + ⋯ + aₘeₘ‖² = |a₁|² + ⋯ + |aₘ|²`. -/

/-- 6.24 for a linear combination over any finite set {lit}`s` of indices. As in
the book, apply the Pythagorean theorem (6.12) repeatedly: adding one more term
{lit}`aⱼeⱼ`, it is orthogonal to the earlier ones, so the squared norms add. -/
@[avoiding Orthonormal.inner_sum]
theorem norm_sq_sum_orthonormal_finset {ι : Type*} {e : ι → V}
    (he : Orthonormal 𝕜 e) (a : ι → 𝕜) (s : Finset ι) :
    ‖∑ i ∈ s, a i • e i‖ ^ 2 = ∑ i ∈ s, ‖a i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    -- `aⱼeⱼ` is orthogonal to `∑_{i ∈ s} aᵢeᵢ`
    have horth : LADR.Section_6A.Orthogonal (𝕜 := 𝕜) (a j • e j) (∑ i ∈ s, a i • e i) := by
      unfold LADR.Section_6A.Orthogonal
      rw [inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [inner_smul_left, inner_smul_right, he.2 (fun h : j = i => hj (h ▸ hi)), mul_zero, mul_zero]
    rw [LADR.Section_6A.pythagorean _ _ horth, ih, norm_smul, he.1 j, mul_one]

theorem norm_sq_sum_orthonormal {ι : Type*} [Fintype ι] {e : ι → V}
    (he : Orthonormal 𝕜 e) (a : ι → 𝕜) :
    ‖∑ i, a i • e i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 :=
  norm_sq_sum_orthonormal_finset he a Finset.univ

/-! 6.25 Orthonormal lists are linearly independent

If {lit}`a₁e₁ + ⋯ + aₘeₘ = 0`, then {lit}`|a₁|² + ⋯ + |aₘ|² = 0` by 6.24, so
every {lit}`aₖ = 0`. -/

@[avoiding Orthonormal.linearIndependent]
theorem orthonormal_linearIndependent {ι : Type*} {e : ι → V}
    (he : Orthonormal 𝕜 e) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff']
  intro s a hsum i hi
  have h := norm_sq_sum_orthonormal_finset he a s
  rw [hsum, norm_zero, sq, zero_mul, eq_comm,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)] at h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (h i hi))

/-! 6.26 Bessel's inequality

If {lit}`e₁, …, eₘ` is orthonormal and {lit}`v ∈ V`, then
{lit}`|⟨v, e₁⟩|² + ⋯ + |⟨v, eₘ⟩|² ≤ ‖v‖²` (recall {lit}`⟨v, eₖ⟩` is mathlib's
{lit}`⟪eₖ, v⟫`).

Axler's proof: write {lit}`v = u + w` with
{lit}`u = ⟨v, e₁⟩e₁ + ⋯ + ⟨v, eₘ⟩eₘ` and {lit}`w = v − u`. Then
{lit}`⟨w, eₖ⟩ = ⟨v, eₖ⟩ − ⟨v, eₖ⟩ = 0` for each {lit}`k`, so {lit}`w` is
orthogonal to {lit}`u`, and the Pythagorean theorem with 6.24 gives
{lit}`‖v‖² = ‖u‖² + ‖w‖² ≥ ‖u‖² = |⟨v, e₁⟩|² + ⋯ + |⟨v, eₘ⟩|²`. -/

@[avoiding Orthonormal.sum_inner_products_le]
theorem bessel {ι : Type*} {e : ι → V} (he : Orthonormal 𝕜 e) (v : V)
    (s : Finset ι) : ∑ i ∈ s, ‖⟪e i, v⟫_𝕜‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  set u := ∑ i ∈ s, ⟪e i, v⟫_𝕜 • e i with hu
  -- `w = v − u` is orthogonal to each `eₖ`, hence to `u`
  have hwe : ∀ k ∈ s, ⟪e k, v - u⟫_𝕜 = 0 := by
    intro k hk
    rw [inner_sub_right, hu, he.inner_right_sum _ hk, sub_self]
  have horth : LADR.Section_6A.Orthogonal (𝕜 := 𝕜) u (v - u) := by
    unfold LADR.Section_6A.Orthogonal
    rw [hu, sum_inner]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [inner_smul_left, hwe k hk, mul_zero]
  have hpyth := LADR.Section_6A.pythagorean _ _ horth
  rw [add_sub_cancel, hu, norm_sq_sum_orthonormal_finset he] at hpyth
  rw [hpyth]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-! # Orthonormal bases -/

/-! 6.27 Definition: orthonormal basis

An orthonormal basis is an orthonormal list that is also a basis; this is
mathlib's {name}`OrthonormalBasis`. The standard basis is an orthonormal basis
of {lit}`𝔽ⁿ`. -/

noncomputable example {n : ℕ} : OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  EuclideanSpace.basisFun (Fin n) 𝕜

/-! 6.28 Orthonormal lists of the right length are orthonormal bases

If {lit}`V` is finite-dimensional, every orthonormal list of length {lit}`dim V`
is an orthonormal basis: by 6.25 it is linearly independent, and a linearly
independent list of length {lit}`dim V` is a basis (2.38). -/

@[avoiding Orthonormal.exists_orthonormalBasis_extension_of_card_eq]
theorem orthonormalBasis_of_length [FiniteDimensional 𝕜 V] {n : ℕ}
    (e : Fin n → V) (he : Orthonormal 𝕜 e) (hn : n = finrank 𝕜 V) :
    ∃ b : OrthonormalBasis (Fin n) 𝕜 V, ∀ i, b i = e i := by
  have hbasis : LADR.Section_2B.IsBasis 𝕜 e :=
    LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq e
      (orthonormal_linearIndependent he) hn
  have he' : Orthonormal 𝕜 hbasis.toModuleBasis := by
    convert he
    exact funext (LADR.Section_2B.IsBasis.toModuleBasis_apply hbasis)
  exact ⟨hbasis.toModuleBasis.toOrthonormalBasis he', fun i => by simp⟩

/-! 6.29 Example: an orthonormal basis of {lit}`𝔽⁴`. Besides the standard basis,
the list
{lit}`(½, ½, ½, ½), (½, ½, −½, −½), (½, −½, −½, ½), (−½, ½, −½, ½)`
is orthonormal; being an orthonormal list of length {lit}`4 = dim 𝔽⁴`, it is an
orthonormal basis of {lit}`𝔽⁴` by 6.28. -/

/-- The list of 6.29 in {lit}`𝔽⁴`. -/
noncomputable def list_6_29 : Fin 4 → EuclideanSpace 𝕜 (Fin 4) :=
  ![!₂[1/2, 1/2, 1/2, 1/2],
    !₂[1/2, 1/2, -1/2, -1/2],
    !₂[1/2, -1/2, -1/2, 1/2],
    !₂[-1/2, 1/2, -1/2, 1/2]]

/-- 6.29: the list is orthonormal (each vector has norm 1, distinct ones are orthogonal). -/
theorem orthonormal_6_29 :Orthonormal 𝕜 (list_6_29 (𝕜 := 𝕜)) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [list_6_29, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_four,
      Matrix.cons_val, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_div₀, map_one, map_neg, map_ofNat, Fin.isValue, Fin.reduceEq, reduceIte] <;>
    norm_num

/-- 6.29: the list is an orthonormal basis of {lit}`𝔽⁴`, by 6.28. -/
theorem orthonormalBasis_6_29 :
    ∃ b : OrthonormalBasis (Fin 4) 𝕜 (EuclideanSpace 𝕜 (Fin 4)), ∀ i, b i = list_6_29 i :=
  orthonormalBasis_of_length _ orthonormal_6_29 (by simp)

/-! 6.30 Writing a vector as a linear combination of an orthonormal basis

Suppose {lit}`e₁, …, eₙ` is an orthonormal basis and {lit}`u, v ∈ V`. Then
(a) {lit}`v = ⟨v, e₁⟩e₁ + ⋯ + ⟨v, eₙ⟩eₙ`;
(b) {lit}`‖v‖² = |⟨v, e₁⟩|² + ⋯ + |⟨v, eₙ⟩|²` (Parseval's identity);
(c) {lit}`⟨u, v⟩ = ⟨u, e₁⟩⟨v, e₁⟩‾ + ⋯ + ⟨u, eₙ⟩⟨v, eₙ⟩‾`. Reading Axler's
{lit}`⟨·, ·⟩` as mathlib's with the slots swapped, this is
{lit}`⟪u, v⟫ = ∑ₖ ⟪u, eₖ⟫ ⟪eₖ, v⟫`.

Axler's proof of (a): since {lit}`e₁, …, eₙ` is a basis,
{lit}`v = a₁e₁ + ⋯ + aₙeₙ` for some scalars; taking the inner product with
{lit}`eₖ` gives {lit}`⟨v, eₖ⟩ = aₖ`. Then (b) is 6.24 applied to (a), and (c)
follows by taking the inner product of {lit}`u` with (a). -/

@[avoiding OrthonormalBasis.sum_repr']
theorem orthonormalBasis_repr {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 V)
    (v : V) : v = ∑ i, ⟪b i, v⟫_𝕜 • b i := by
  -- `v = ∑ aᵢ eᵢ` because `e` is a basis
  set a := b.toBasis.repr v
  have hv : v = ∑ i, a i • b i := by
    conv_lhs => rw [← b.toBasis.sum_repr v]
    simp only [OrthonormalBasis.coe_toBasis, a]
  -- and `⟨v, eₖ⟩ = aₖ`
  have ha : ∀ k, ⟪b k, v⟫_𝕜 = a k := by
    intro k
    rw [hv, b.orthonormal.inner_right_fintype]
  simp_rw [ha]
  exact hv

@[avoiding OrthonormalBasis.sum_sq_norm_inner_right]
theorem parseval {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 V) (v : V) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪b i, v⟫_𝕜‖ ^ 2 := by
  conv_lhs => rw [orthonormalBasis_repr b v]
  exact norm_sq_sum_orthonormal b.orthonormal _

@[avoiding OrthonormalBasis.sum_inner_mul_inner]
theorem inner_eq_sum_inner_mul_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 V) (u v : V) :
    ⟪u, v⟫_𝕜 = ∑ i, ⟪u, b i⟫_𝕜 * ⟪b i, v⟫_𝕜 := by
  conv_lhs => rw [orthonormalBasis_repr b v]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, mul_comm]

/-! 6.31 Example: finding coefficients for a linear combination.

To write {lit}`(1, 2, 4, 7) ∈ 𝔽⁴` in the orthonormal basis of 6.29, we need not
solve a linear system: by 6.30(a) the coefficients are the inner products with the
basis vectors, giving {lit}`(1, 2, 4, 7) = 7e₁ − 4e₂ + e₃ + 2e₄`. -/

example : (!₂[1, 2, 4, 7] : EuclideanSpace 𝕜 (Fin 4)) =
    (7 : 𝕜) • list_6_29 0 + (-4 : 𝕜) • list_6_29 1 + (1 : 𝕜) • list_6_29 2
      + (2 : 𝕜) • list_6_29 3 := by
  ext i
  fin_cases i <;>
    simp [list_6_29, PiLp.add_apply, PiLp.smul_apply, Matrix.cons_val, Fin.reduceFinMk] <;>
    norm_num

/-! 6.32 Gram–Schmidt procedure

Given a linearly independent list {lit}`v₁, …, vₘ`, the Gram–Schmidt procedure
produces an orthonormal list {lit}`e₁, …, eₘ` with the same span at each stage.
mathlib's {name}`InnerProductSpace.gramSchmidtNormed` are the {lit}`eₖ`; they are
orthonormal and preserve every initial span {lit}`span(v₁, …, vₖ)`.

mathlib's {name}`InnerProductSpace.gramSchmidt` is the book's recursion before
normalizing: {lit}`fₖ = vₖ − ∑_{j<k} P_{span(fⱼ)} vₖ` (6.56 computes each
projection as {lit}`(⟨vₖ, fⱼ⟩/‖fⱼ‖²) fⱼ`), and {lit}`eₖ = fₖ/‖fₖ‖`. We take only
that recursion ({name}`InnerProductSpace.gramSchmidt_def`) from mathlib and prove
the properties by Axler's induction on {lit}`k`. -/

section GramSchmidt

open InnerProductSpace Submodule

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [IsWellOrder ι (· < ·)]

/-- Each {lit}`fₖ` is orthogonal to the earlier {lit}`fⱼ`: taking the inner
product of {lit}`fⱼ` with the recursion, every projection term except the
{lit}`j`-th vanishes by induction, and the {lit}`j`-th cancels {lit}`⟨fⱼ, vₖ⟩`. -/
@[avoiding gramSchmidt_orthogonal]
theorem gramSchmidt_orthogonal_of_lt (f : ι → V) {a b : ι} (h : a < b) :
    ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫_𝕜 = 0 := by
  induction b using WellFoundedLT.induction generalizing a with | ind b ih
  rw [gramSchmidt_def 𝕜 f b, inner_sub_right, inner_sum,
    Finset.sum_eq_single_of_mem a (Finset.mem_Iio.mpr h)]
  · -- the `a`-th projection term is `⟨fₐ, vᵦ⟩`
    by_cases h0 : gramSchmidt 𝕜 f a = 0
    · rw [h0, inner_zero_left, inner_zero_left, sub_zero]
    · rw [starProjection_singleton, inner_smul_right, RCLike.ofReal_pow,
        ← inner_self_eq_norm_sq_to_K, div_mul_cancel₀ _ (inner_self_ne_zero.mpr h0), sub_self]
  · -- the others vanish by the induction hypothesis
    intro i hi hia
    rw [starProjection_singleton, inner_smul_right]
    rcases hia.lt_or_gt with hlt | hgt
    · rw [inner_eq_zero_symm.mp (ih a h hlt), mul_zero]
    · rw [ih i (Finset.mem_Iio.mp hi) hgt, mul_zero]

/-- {lit}`vᵢ ∈ span(f₁, …, fⱼ)` for {lit}`i ≤ j`: rearrange the recursion as
{lit}`vᵢ = fᵢ + ∑_{l<i} (multiple of fₗ)`. -/
@[avoiding mem_span_gramSchmidt]
theorem mem_span_gramSchmidt_of_le (f : ι → V) {i j : ι} (hij : i ≤ j) :
    f i ∈ span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j) := by
  rw [gramSchmidt_def' 𝕜 f i]
  refine add_mem (subset_span ⟨i, hij, rfl⟩) (sum_mem fun l hl => ?_)
  rw [starProjection_singleton]
  exact smul_mem _ _ (subset_span ⟨l, ((Finset.mem_Iio.mp hl).le.trans hij), rfl⟩)

/-- {lit}`fᵢ ∈ span(v₁, …, vⱼ)` for {lit}`i ≤ j`, by induction on {lit}`i`: the
recursion writes {lit}`fᵢ` as {lit}`vᵢ` minus multiples of earlier {lit}`fₗ`. -/
@[avoiding gramSchmidt_mem_span]
theorem gramSchmidt_mem_span_of_le (f : ι → V) {i j : ι} (hij : i ≤ j) :
    gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' Set.Iic j) := by
  induction i using WellFoundedLT.induction generalizing j with | ind i ih
  rw [gramSchmidt_def 𝕜 f i]
  refine sub_mem (subset_span ⟨i, hij, rfl⟩) (sum_mem fun l hl => ?_)
  rw [starProjection_singleton]
  have hl : l < i := Finset.mem_Iio.mp hl
  exact smul_mem _ _ (ih l hl (hl.le.trans hij))

/-- If {lit}`v₁, …, vₖ` is linearly independent then {lit}`fₖ ≠ 0`: otherwise
{lit}`vₖ` would lie in {lit}`span(f₁, …, fₖ₋₁) ⊆ span(v₁, …, vₖ₋₁)`. -/
@[avoiding gramSchmidt_ne_zero]
theorem gramSchmidt_ne_zero_of_linearIndependent {f : ι → V}
    (hf : LinearIndependent 𝕜 f) (n : ι) : gramSchmidt 𝕜 f n ≠ 0 := by
  intro h0
  apply hf.notMem_span_image (s := Set.Iio n) Set.self_notMem_Iio
  rw [gramSchmidt_def' 𝕜 f n, h0, zero_add]
  refine sum_mem fun l hl => ?_
  rw [starProjection_singleton]
  have hl : l < n := Finset.mem_Iio.mp hl
  exact smul_mem _ _ (span_mono (Set.image_mono (Set.Iic_subset_Iio.mpr hl))
    (gramSchmidt_mem_span_of_le f le_rfl))

/-- 6.32: normalizing, {lit}`eₖ = fₖ/‖fₖ‖` is an orthonormal list. -/
@[avoiding gramSchmidtNormed_orthonormal]
theorem gram_schmidt_orthonormal {f : ι → V}
    (hf : LinearIndependent 𝕜 f) : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · unfold gramSchmidtNormed
    rw [norm_smul_inv_norm (gramSchmidt_ne_zero_of_linearIndependent hf i)]
  · show ⟪gramSchmidtNormed 𝕜 f i, gramSchmidtNormed 𝕜 f j⟫_𝕜 = 0
    unfold gramSchmidtNormed
    rw [inner_smul_left, inner_smul_right]
    rcases hij.lt_or_gt with hlt | hgt
    · rw [gramSchmidt_orthogonal_of_lt f hlt, mul_zero, mul_zero]
    · rw [inner_eq_zero_symm.mp (gramSchmidt_orthogonal_of_lt f hgt), mul_zero, mul_zero]

/-- The Gram–Schmidt vectors span each initial segment of the original list. -/
@[avoiding span_gramSchmidt_Iic]
theorem span_gram_schmidt_initial (f : ι → V) (k : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic k) = span 𝕜 (f '' Set.Iic k) :=
  le_antisymm
    (span_le.mpr (Set.image_subset_iff.mpr fun _ hi => gramSchmidt_mem_span_of_le f hi))
    (span_le.mpr (Set.image_subset_iff.mpr fun _ hi => mem_span_gramSchmidt_of_le f hi))

/-- 6.32: {lit}`span(e₁, …, eₖ) = span(v₁, …, vₖ)`. Each {lit}`eᵢ = fᵢ/‖fᵢ‖` is a multiple
of {lit}`fᵢ`, and conversely {lit}`fᵢ = ‖fᵢ‖eᵢ` (or {lit}`fᵢ = 0`), so the {lit}`e`'s and
{lit}`f`'s have the same initial spans. -/
@[avoiding span_gramSchmidtNormed]
theorem span_gramSchmidtNormed_initial (f : ι → V) (k : ι) :
    span 𝕜 (gramSchmidtNormed 𝕜 f '' Set.Iic k) = span 𝕜 (f '' Set.Iic k) := by
  rw [← span_gram_schmidt_initial f k]
  apply le_antisymm <;> rw [span_le]
  · rintro _ ⟨i, hi, rfl⟩
    exact smul_mem _ _ (subset_span ⟨i, hi, rfl⟩)
  · rintro _ ⟨i, hi, rfl⟩
    by_cases h0 : gramSchmidt 𝕜 f i = 0
    · rw [SetLike.mem_coe, h0]; exact zero_mem _
    · have : gramSchmidt 𝕜 f i = (‖gramSchmidt 𝕜 f i‖ : 𝕜) • gramSchmidtNormed 𝕜 f i := by
        rw [gramSchmidtNormed, smul_smul, mul_inv_cancel₀
          (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)), one_smul]
      rw [SetLike.mem_coe, this]
      exact smul_mem _ _ (subset_span ⟨i, hi, rfl⟩)

/-- Gram–Schmidt leaves an orthogonal initial segment alone: if
{lit}`v₁, …, vₖ` are pairwise orthogonal then {lit}`fₖ = vₖ`, since by induction
every earlier {lit}`fⱼ = vⱼ` is orthogonal to {lit}`vₖ` and so every projection
term vanishes. -/
@[avoiding gramSchmidt_of_orthogonal]
theorem gramSchmidt_eq_self_of_orthogonal (f : ι → V) (k : ι)
    (horth : ∀ i j, i ≤ k → j ≤ k → i ≠ j → ⟪f i, f j⟫_𝕜 = 0) :
    gramSchmidt 𝕜 f k = f k := by
  induction k using WellFoundedLT.induction with | ind k ih
  rw [gramSchmidt_def 𝕜 f k, sub_eq_self]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hl : l < k := Finset.mem_Iio.mp hl
  rw [ih l hl fun i j hi hj => horth i j (hi.trans hl.le) (hj.trans hl.le),
    starProjection_singleton, horth l k hl.le le_rfl hl.ne, zero_div, zero_smul]

/-- …so if {lit}`v₁, …, vₖ` is orthonormal, also {lit}`eₖ = vₖ`. -/
theorem gramSchmidtNormed_eq_self_of_orthonormal (f : ι → V) (k : ι)
    (horth : ∀ i j, i ≤ k → j ≤ k → i ≠ j → ⟪f i, f j⟫_𝕜 = 0) (hk : ‖f k‖ = 1) :
    gramSchmidtNormed 𝕜 f k = f k := by
  unfold gramSchmidtNormed
  rw [gramSchmidt_eq_self_of_orthogonal f k horth, hk, RCLike.ofReal_one, inv_one, one_smul]

end GramSchmidt

/-! 6.34 Example: an orthonormal basis of {lit}`𝒫₂(ℝ)`. Applying Gram–Schmidt
(6.32) to {lit}`1, x, x²` under {lit}`⟨p, q⟩ = ∫₋₁¹ pq` yields the (unnormalized)
Legendre polynomials {lit}`1, x, x² − ⅓`. This uses the {lit}`L²` inner product on
{lit}`C[-1,1]` from the skippable {lit}`L2Interval.lean` infrastructure. Each inner
product reduces to a concrete interval integral via {name}`L2C_inner_restrict`: the
three are pairwise orthogonal, with {lit}`‖f₁‖² = 2`, {lit}`‖f₂‖² = 2/3`,
{lit}`‖f₃‖² = 8/45`, so dividing by the norms gives the orthonormal list
{lit}`√(1/2), √(3/2)·x, √(45/8)·(x² − ⅓)`. Being of length {lit}`3 = dim 𝒫₂(ℝ)` it is
an orthonormal basis of {lit}`𝒫₂(ℝ)` (6.28); we model {lit}`𝒫₂(ℝ)` inside
{lit}`C[-1,1]` and do not formalize that span. The analogous Gram–Schmidt over
{lit}`∫₀¹` is Exercise 6B.8. -/

section Example_6_34

open MeasureTheory

/-- The first Legendre polynomial {lit}`1` as an element of {lit}`C[-1,1]`. -/
noncomputable def legendre0 : L2C (-1) 1 := (ContinuousMap.const ℝ 1).restrict _
/-- The second Legendre polynomial {lit}`x`. -/
noncomputable def legendre1 : L2C (-1) 1 := (ContinuousMap.id ℝ).restrict _
/-- The third Legendre polynomial `x² − ⅓`. -/
noncomputable def legendre2 : L2C (-1) 1 :=
  (⟨fun x => x ^ 2 - 1 / 3, by fun_prop⟩ : C(ℝ, ℝ)).restrict _

/-- `⟨1, x⟩ = ∫₋₁¹ x = 0`. -/
theorem legendre_inner_01 : ⟪legendre0, legendre1⟫_ℝ = 0 := by
  rw [legendre0, legendre1, L2C_inner_restrict]
  simp

/-- `⟨1, x² − ⅓⟩ = ∫₋₁¹ (x² − ⅓) = 0`. -/
theorem legendre_inner_02 : ⟪legendre0, legendre2⟫_ℝ = 0 := by
  rw [legendre0, legendre2, L2C_inner_restrict]
  simp only [ContinuousMap.const_apply, ContinuousMap.coe_mk, one_mul]
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have h2 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 3) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_sub h1 h2, integral_pow, intervalIntegral.integral_const]
  norm_num

/-- `⟨x, x² − ⅓⟩ = ∫₋₁¹ (x³ − x/3) = 0`. -/
theorem legendre_inner_12 : ⟪legendre1, legendre2⟫_ℝ = 0 := by
  rw [legendre1, legendre2, L2C_inner_restrict]
  simp only [ContinuousMap.id_apply, ContinuousMap.coe_mk]
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ 3) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have h2 : IntervalIntegrable (fun x : ℝ => x / 3) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_congr (g := fun x => x ^ 3 - x / 3) (fun x _ => by ring),
    intervalIntegral.integral_sub h1 h2, integral_pow, intervalIntegral.integral_div, integral_id]
  norm_num

/-- `‖1‖² = ∫₋₁¹ 1 = 2`. -/
theorem legendre_inner_00 : ⟪legendre0, legendre0⟫_ℝ = 2 := by
  rw [legendre0, L2C_inner_restrict]
  norm_num

/-- `‖x‖² = ∫₋₁¹ x² = 2/3`. -/
theorem legendre_inner_11 : ⟪legendre1, legendre1⟫_ℝ = 2 / 3 := by
  rw [legendre1, L2C_inner_restrict]
  simp only [ContinuousMap.id_apply]
  simp_rw [← sq]
  rw [integral_pow]
  norm_num

/-- `‖x² − ⅓‖² = ∫₋₁¹ (x⁴ − ⅔x² + ⅑) = 8/45`. -/
theorem legendre_inner_22 : ⟪legendre2, legendre2⟫_ℝ = 8 / 45 := by
  rw [legendre2, L2C_inner_restrict]
  simp only [ContinuousMap.coe_mk]
  have h4 : IntervalIntegrable (fun x : ℝ => x ^ 4) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have h2 : IntervalIntegrable (fun x : ℝ => 2 / 3 * x ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have h0 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 9) volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_congr (g := fun x => x ^ 4 - 2 / 3 * x ^ 2 + 1 / 9)
      (fun x _ => by ring),
    intervalIntegral.integral_add (h4.sub h2) h0, intervalIntegral.integral_sub h4 h2,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow,
    intervalIntegral.integral_const]
  norm_num

/-- 6.34: dividing by the norms gives the orthonormal list
{lit}`√(1/2), √(3/2)·x, √(45/8)·(x² − ⅓)`. -/
theorem legendre_orthonormal : Orthonormal ℝ
    ![(Real.sqrt 2)⁻¹ • legendre0, Real.sqrt (3 / 2) • legendre1,
      Real.sqrt (45 / 8) • legendre2] := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s32 : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have s458 : Real.sqrt (45 / 8) ^ 2 = 45 / 8 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have h10 : ⟪legendre1, legendre0⟫_ℝ = 0 := by rw [real_inner_comm]; exact legendre_inner_01
  have h20 : ⟪legendre2, legendre0⟫_ℝ = 0 := by rw [real_inner_comm]; exact legendre_inner_02
  have h21 : ⟪legendre2, legendre1⟫_ℝ = 0 := by rw [real_inner_comm]; exact legendre_inner_12
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
      reduceIte, Fin.reduceEq] <;>
    rw [real_inner_smul_left, real_inner_smul_right] <;>
    simp only [legendre_inner_00, legendre_inner_11, legendre_inner_22, legendre_inner_01,
      legendre_inner_02, legendre_inner_12, h10, h20, h21, mul_zero]
  · field_simp; linarith
  · rw [← mul_assoc, ← sq, s32]; norm_num
  · rw [← mul_assoc, ← sq, s458]; norm_num

end Example_6_34

/-! 6.35 Existence of an orthonormal basis

Every finite-dimensional inner product space has an orthonormal basis. Axler's
proof: apply Gram–Schmidt (6.32) to a basis of {lit}`V`; the result is an
orthonormal list of length {lit}`dim V`, hence an orthonormal basis by 6.28. -/

@[avoiding stdOrthonormalBasis]
theorem exists_orthonormalBasis [FiniteDimensional 𝕜 V] :
    Nonempty (OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V) := by
  let v := Module.finBasis 𝕜 V
  obtain ⟨b, -⟩ := orthonormalBasis_of_length (InnerProductSpace.gramSchmidtNormed 𝕜 v)
    (gram_schmidt_orthonormal v.linearIndependent) rfl
  exact ⟨b⟩

/-! 6.36 Every orthonormal list extends to an orthonormal basis

If {lit}`V` is finite-dimensional, every orthonormal list can be extended to an
orthonormal basis.

Axler's proof: the orthonormal list {lit}`e₁, …, eₘ` is linearly independent
(6.25), so it extends to a basis {lit}`e₁, …, eₘ, v₁, …, vₙ` of {lit}`V` (2.32).
Apply Gram–Schmidt (6.32) to that basis: the first {lit}`m` vectors are already
orthonormal, so they are left unchanged, and the output is an orthonormal list
of length {lit}`dim V`, hence an orthonormal basis (6.28). -/

@[avoiding Orthonormal.exists_orthonormalBasis_extension]
theorem orthonormal_extends [FiniteDimensional 𝕜 V] {s : Set V}
    (hs : Orthonormal 𝕜 ((↑) : s → V)) :
    ∃ (u : Finset V) (b : OrthonormalBasis u 𝕜 V), s ⊆ u ∧ ⇑b = ((↑) : u → V) := by
  classical
  -- list the (finitely many, by 6.25) vectors of `s` as `e₁, …, eₘ`
  have hli := orthonormal_linearIndependent hs
  haveI : Fintype s := @Fintype.ofFinite s hli.finite
  set σ := Fintype.equivFin s
  set e : Fin (Fintype.card s) → V := fun i => (σ.symm i : V) with he_def
  have he : Orthonormal 𝕜 e := hs.comp _ σ.symm.injective
  -- extend to a basis `w` (2.32), and apply Gram–Schmidt
  obtain ⟨n, w, hmn, hw, hprefix⟩ :=
    LADR.Section_2B.exists_basis_extending e (orthonormal_linearIndependent he)
  set g := InnerProductSpace.gramSchmidtNormed 𝕜 w
  have hg : Orthonormal 𝕜 g := gram_schmidt_orthonormal hw.1
  obtain ⟨b', hb'⟩ := orthonormalBasis_of_length g hg
    (LADR.Section_2C.isBasis_card_eq_finrank w hw)
  -- the first `m` vectors are unchanged
  have hfix : ∀ i, g (Fin.castLE hmn i) = e i := by
    intro i
    rw [← hprefix i]
    have hlt : ∀ j : Fin n, j ≤ Fin.castLE hmn i → (j : ℕ) < Fintype.card s :=
      fun j hj => lt_of_le_of_lt hj i.2
    have hw_eq : ∀ j (hj : j ≤ Fin.castLE hmn i), w j = e ⟨j, hlt j hj⟩ := fun j hj => by
      rw [← hprefix]; rfl
    refine gramSchmidtNormed_eq_self_of_orthonormal w _ (fun j j' hj hj' hne => ?_) ?_
    · rw [hw_eq j hj, hw_eq j' hj']
      exact he.2 fun h => hne (Fin.ext (by simpa using congrArg Fin.val h))
    · rw [hprefix]; exact he.1 i
  -- `u` = the vectors of the Gram–Schmidt output
  refine ⟨Finset.univ.image g, OrthonormalBasis.mk (v := ((↑) : Finset.univ.image g → V))
    ?_ ?_, ?_, OrthonormalBasis.coe_mk _ _⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨x, hx⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hg.1 i
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact hg.2 fun h => hxy (by subst h; rfl)
  · -- it spans `V`, being the orthonormal basis `b'`
    have hrange : Set.range ((↑) : Finset.univ.image g → V) = Set.range g := by
      rw [Subtype.range_coe_subtype]; ext x; simp
    rw [hrange, ← funext hb', ← b'.coe_toBasis, b'.toBasis.span_eq]
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨Fin.castLE hmn (σ ⟨x, hx⟩), Finset.mem_univ _, ?_⟩
    rw [hfix, he_def]
    simp

/-! 6.37 / 6.38 Upper-triangular matrix with respect to an orthonormal basis,
and Schur's theorem.

An operator is *upper-triangular* with respect to an orthonormal basis
{lit}`e₀, …, eₙ₋₁` when {lit}`T eₖ ∈ span(e₀, …, eₖ)` for each {lit}`k`. Gram–
Schmidt turns any triangularizing basis (from 5.44 in
{module -checked}`LinearAlgebraDoneRightLean.Section_5C`) into an orthonormal one
with the same flag, which stays upper-triangular. -/

section Schur

open Submodule Set InnerProductSpace
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf)
open LADR.Section_5C

variable [FiniteDimensional 𝕜 V]

/-- Gram–Schmidt turns a basis into an orthonormal basis with the same flag:
{lit}`span(e₀, …, eₖ) = span(v₀, …, vₖ)` for every {lit}`k`. -/
theorem exists_gramSchmidt_flag {n : ℕ} (v : Fin n → V) (hli : LinearIndependent 𝕜 v)
    (hcard : Module.finrank 𝕜 V = Fintype.card (Fin n)) :
    ∃ e : OrthonormalBasis (Fin n) 𝕜 V,
      ∀ k, span 𝕜 (e '' {i | i ≤ k}) = span 𝕜 (v '' {i | i ≤ k}) := by
  -- mathlib packages the orthonormal Gram–Schmidt list as an `OrthonormalBasis`
  have he : ⇑(gramSchmidtOrthonormalBasis hcard v) = gramSchmidtNormed 𝕜 v :=
    funext fun i => gramSchmidtOrthonormalBasis_apply hcard
      ((gram_schmidt_orthonormal hli).ne_zero i)
  exact ⟨gramSchmidtOrthonormalBasis hcard v, fun k => by
    rw [he]; exact span_gramSchmidtNormed_initial v k⟩

omit [FiniteDimensional 𝕜 V] in
/-- A flag {lit}`span(v₀, …, vₖ)` on which {lit}`T` acts triangularly is
{lit}`T`-invariant. -/
theorem flag_invariant {n : ℕ} (v : Fin n → V) (T : V →ₗ[𝕜] V)
    (hflag : ∀ k, T (v k) ∈ span 𝕜 (v '' {i | i ≤ k})) (k : Fin n) :
    ∀ x ∈ span 𝕜 (v '' {i | i ≤ k}), T x ∈ span 𝕜 (v '' {i | i ≤ k}) := by
  have hle : span 𝕜 (v '' {i | i ≤ k}) ≤ (span 𝕜 (v '' {i | i ≤ k})).comap T := by
    rw [span_le]
    rintro _ ⟨j, hjk, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    have hsub : (v '' {i : Fin n | i ≤ j}) ⊆ (v '' {i | i ≤ k}) :=
      Set.image_mono fun i (hi : i ≤ j) => le_trans hi hjk
    exact Submodule.span_mono hsub (hflag j)
  exact fun x hx => hle hx

/-- The key step of 6.37, for all operators at once: Gram–Schmidt turns a basis
{lit}`v₁, …, vₙ` into an orthonormal basis {lit}`e₁, …, eₙ` with
{lit}`span(e₁, …, eₖ) = span(v₁, …, vₖ)` (6.32). If {lit}`T` is upper-triangular with
respect to {lit}`v`, each {lit}`span(v₁, …, vₖ)` is {lit}`T`-invariant (5.39), so
{lit}`T` is upper-triangular with respect to {lit}`e`. The basis {lit}`e` depends only
on {lit}`v`, not on {lit}`T`. -/
theorem exists_orthonormal_upperTriangular_of_basis {n : ℕ} {v : Fin n → V}
    (hv : IsBasis 𝕜 v) :
    ∃ (e : OrthonormalBasis (Fin n) 𝕜 V) (he : IsBasis 𝕜 (⇑e)),
      ∀ T : V →ₗ[𝕜] V, IsUpperTriangular (matrixOf hv hv T) →
        IsUpperTriangular (matrixOf he he T) := by
  classical
  have hcoe : (⇑hv.toModuleBasis) = v := funext (IsBasis.toModuleBasis_apply hv)
  have hli : LinearIndependent 𝕜 v := hcoe ▸ hv.toModuleBasis.linearIndependent
  have hcard : Module.finrank 𝕜 V = Fintype.card (Fin n) := by
    rw [Module.finrank_eq_card_basis hv.toModuleBasis, Fintype.card_fin]
  obtain ⟨e, hspan_gs⟩ := exists_gramSchmidt_flag v hli hcard
  have hek_mem : ∀ (k : Fin n), e k ∈ span 𝕜 (v '' {i | i ≤ k}) := by
    intro k; rw [← hspan_gs k]; exact subset_span ⟨k, le_refl k, rfl⟩
  have he : IsBasis 𝕜 (⇑e) :=
    LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq _
      e.orthonormal.linearIndependent (by rw [hcard, Fintype.card_fin])
  refine ⟨e, he, fun T hA => ?_⟩
  have hflag : ∀ k, T (v k) ∈ span 𝕜 (v '' {i | i ≤ k}) :=
    ((tfae_upperTriangular hv T).out 0 2).mp hA
  have hflag_e : ∀ k, T (e k) ∈ span 𝕜 (e '' {i | i ≤ k}) := by
    intro k; rw [hspan_gs k]; exact flag_invariant v T hflag k (e k) (hek_mem k)
  exact ((tfae_upperTriangular he T).out 2 0).mp hflag_e

/-- 6.37, one operator: if {lit}`T` is upper-triangular with respect to some basis, it
is upper-triangular with respect to some orthonormal basis. -/
theorem exists_orthonormal_upperTriangular (T : V →ₗ[𝕜] V)
    (h : ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis 𝕜 v), IsUpperTriangular (matrixOf hv hv T)) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V) (he : IsBasis 𝕜 (⇑e)),
      IsUpperTriangular (matrixOf he he T) := by
  obtain ⟨n, v, hv, hA⟩ := h
  obtain ⟨e, he, hT⟩ := exists_orthonormal_upperTriangular_of_basis hv
  exact ⟨n, e, he, hT T hA⟩

/-- 6.37: {lit}`T` is upper-triangular with respect to some orthonormal basis iff
{lit}`minpoly 𝕜 T = (z − λ₁)⋯(z − λₘ)`. By 5.44 the right side is equivalent to
{lit}`T` being upper-triangular with respect to some basis; an orthonormal basis is
a basis, and conversely {name}`exists_orthonormal_upperTriangular` upgrades a basis to
an orthonormal one. -/
theorem exists_orthonormal_upperTriangular_iff_minpoly (T : V →ₗ[𝕜] V) :
    (∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V) (he : IsBasis 𝕜 (⇑e)),
      IsUpperTriangular (matrixOf he he T)) ↔
    ∃ (m : ℕ) (γ : Fin m → 𝕜), minpoly 𝕜 T = ∏ k, (Polynomial.X - Polynomial.C (γ k)) := by
  rw [← exists_upperTriangular_iff_minpoly_eq_prod T]
  constructor
  · rintro ⟨n, e, he, hT⟩
    exact ⟨n, e, he, hT⟩
  · exact exists_orthonormal_upperTriangular T

end Schur

/-- 6.38 (Schur's theorem) Every operator on a finite-dimensional complex inner
product space is upper-triangular with respect to some orthonormal basis. Axler's
proof: by the fundamental theorem of algebra (4.13) the minimal polynomial splits
into linear factors, so 6.37 applies. -/
theorem exists_orthonormal_upperTriangular_complex {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V)
      (he : LADR.Section_2B.IsBasis ℂ (⇑e)),
      LADR.Section_5C.IsUpperTriangular (LADR.Section_3C.matrixOf he he T) := by
  rw [exists_orthonormal_upperTriangular_iff_minpoly]
  obtain ⟨m, γ, hfact, -⟩ := LADR.Section_5C.monic_splits_eq_prod_fin
    (minpoly.monic (Algebra.IsIntegral.isIntegral T)) (IsAlgClosed.splits (k := ℂ) _)
  exact ⟨m, γ, hfact⟩

/-! # Linear Functionals on Inner Product Spaces -/

/-! 6.39 Definition: linear functional, dual space

A linear functional on {lit}`V` is a linear map {lit}`V → 𝕜`; the dual space is
{lit}`V →ₗ[𝕜] 𝕜` (see {module -checked}`LinearAlgebraDoneRightLean.Section_3F`). -/

/-! 6.40 Example: a linear functional such as {lit}`φ(z₁, z₂, z₃) = 2z₁ − 5z₂ + z₃`
on {lit}`𝔽³` can be written in the form {lit}`φ(z) = ⟨z, w⟩` (here {lit}`w =
(2, −5, 1)`). More generally, for any fixed {lit}`w ∈ V` the map {lit}`z ↦ ⟨w, z⟩`
is a (continuous) linear functional — mathlib's {name}`innerSL`. -/

noncomputable example (w : V) : V →L[𝕜] 𝕜 := innerSL 𝕜 w

example (w z : V) : innerSL 𝕜 w z = ⟪w, z⟫_𝕜 := rfl

/-- Concretely, {lit}`φ(z₁, z₂, z₃) = 2z₁ − 5z₂ + z₃` is {lit}`z ↦ ⟨z, w⟩` for
{lit}`w = (2, −5, 1)`; with Axler's {lit}`⟨z, w⟩` read as mathlib's {lit}`⟪w, z⟫`,
that is {lit}`⟪(2, −5, 1), z⟫`. -/
example (z : EuclideanSpace 𝕜 (Fin 3)) :
    ⟪(!₂[2, -5, 1] : EuclideanSpace 𝕜 (Fin 3)), z⟫_𝕜 = 2 * z 0 - 5 * z 1 + z 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three, Matrix.cons_val,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_ofNat, map_neg, map_one, Fin.isValue]
  ring

/-! 6.41 Example: a linear functional on {lit}`𝒫₅(ℝ)`. The map
{lit}`φ(p) = ∫₋₁¹ p(t) cos(πt) dt` is a linear functional on {lit}`𝒫₅(ℝ)`, using the
{lit}`L²` integral pairing (see 6.34). In the `L²` model it is the inner product
against `cos(π·)`, so it is a linear functional by construction; the closely
related Riesz computation on {lit}`𝒫₂(ℝ)` is 6.44. -/

section Example_6_41

/-- The weight `cos(π·)` of the functional {lit}`φ`, as an element of {lit}`C[-1,1]`. -/
noncomputable def cosWeight : L2C (-1) 1 :=
  (⟨fun x => Real.cos (Real.pi * x), by fun_prop⟩ : C(ℝ, ℝ)).restrict _

/-- 6.41: `φ(p) = ∫₋₁¹ p(t) cos(πt) dt = ⟨cos(π·), p⟩` is a linear functional. Its
type {lit}`L2C (-1) 1 →ₗ[ℝ] ℝ` records that it is linear. -/
noncomputable def phi_6_41 : L2C (-1) 1 →ₗ[ℝ] ℝ where
  toFun p := ⟪cosWeight, p⟫_ℝ
  map_add' p q := inner_add_right cosWeight p q
  map_smul' c p := by simp [real_inner_smul_right]

theorem phi_6_41_apply (p : L2C (-1) 1) : phi_6_41 p = ⟪cosWeight, p⟫_ℝ := rfl

end Example_6_41

/-! 6.42 Riesz representation theorem

If {lit}`V` is finite-dimensional and {lit}`φ` is a linear functional on
{lit}`V`, then there is a unique {lit}`v ∈ V` with {lit}`φ(u) = ⟨u, v⟩` for all
{lit}`u`. Reading Axler's {lit}`⟨u, v⟩` as mathlib's {lit}`⟪v, u⟫` (the slot in
which the inner product is genuinely linear — {lit}`u ↦ ⟪u, v⟫` would be
conjugate-linear, not a linear functional), this is mathlib's conjugate-linear
isometric isomorphism {name}`InnerProductSpace.toDual` between {lit}`V` and its
(continuous) dual. -/

/-- Axler's first proof. Existence: pick an orthonormal basis {lit}`e₁, …, eₙ`
(6.35); by 6.30(a),
{lit}`φ(u) = φ(⟨u, e₁⟩e₁ + ⋯ + ⟨u, eₙ⟩eₙ) = ⟨u, e₁⟩φ(e₁) + ⋯ + ⟨u, eₙ⟩φ(eₙ)
= ⟨u, φ(e₁)‾e₁ + ⋯ + φ(eₙ)‾eₙ⟩`, so {lit}`v = φ(e₁)‾e₁ + ⋯ + φ(eₙ)‾eₙ` works.
Uniqueness: if {lit}`⟨u, v₁⟩ = ⟨u, v₂⟩` for all {lit}`u`, then
{lit}`⟨u, v₁ − v₂⟩ = 0` for all {lit}`u`; take {lit}`u = v₁ − v₂`. -/
@[avoiding InnerProductSpace.toDual]
theorem riesz_representation [FiniteDimensional 𝕜 V] (φ : V →ₗ[𝕜] 𝕜) :
    ∃! v : V, ∀ u : V, φ u = ⟪v, u⟫_𝕜 := by
  obtain ⟨e⟩ := exists_orthonormalBasis (𝕜 := 𝕜) (V := V)
  set v := ∑ k, conj (φ (e k)) • e k
  -- expand `u` in the orthonormal basis
  have hv : ∀ u : V, φ u = ⟪v, u⟫_𝕜 := by
    intro u
    conv_lhs => rw [orthonormalBasis_repr e u]
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, inner_smul_left, RCLike.conj_conj, mul_comm]
  refine ⟨v, hv, fun w hw => ?_⟩
  -- `⟨w − v, w − v⟩ = 0`
  have hzero : ⟪w - v, w - v⟫_𝕜 = 0 := by
    rw [inner_sub_left, ← hw, ← hv, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)

/-! 6.44 Example: computation illustrating the Riesz representation theorem.

Make {lit}`𝒫₂(ℝ)` an inner product space with {lit}`⟨p, q⟩ = ∫₋₁¹ pq`, and let
{lit}`φ(p) = ∫₋₁¹ p(t)cos(πt) dt`. The Riesz vector representing {lit}`φ` is
{lit}`q(x) = 15/(2π²)(1 − 3x²)`: for every {lit}`p ∈ 𝒫₂(ℝ)` (written
{lit}`p(t) = a + bt + ct²`) we have {lit}`∫₋₁¹ p(t)cos(πt) dt = ∫₋₁¹ p q`. Both
sides reduce, by linearity, to the moments against {lit}`1, t, t²`; the only
nonzero one is the {lit}`t²` moment, where {lit}`∫₋₁¹ t²cos(πt) dt = −4/π²` matches
{lit}`∫₋₁¹ t² q(t) dt`. -/

section Riesz644
open MeasureTheory

/-- {lit}`∫₋₁¹ cos(πt) dt = 0`. -/
theorem integral_cos_pi : (∫ t in (-1:ℝ)..1, Real.cos (Real.pi * t)) = 0 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t => Real.sin (Real.pi * t) / Real.pi) (Real.cos (Real.pi * t)) t := by
    intro t
    have hlin : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
      simpa using (hasDerivAt_id t).const_mul Real.pi
    have hs : HasDerivAt (fun t => Real.sin (Real.pi * t)) (Real.cos (Real.pi * t) * Real.pi) t :=
      (Real.hasDerivAt_sin (Real.pi * t)).comp t hlin
    have := hs.div_const Real.pi
    rwa [mul_div_assoc, div_self hπ, mul_one] at this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  rw [mul_one, mul_neg_one]
  simp [Real.sin_pi]

/-- {lit}`∫₋₁¹ t cos(πt) dt = 0`. -/
theorem integral_id_mul_cos_pi : (∫ t in (-1:ℝ)..1, t * Real.cos (Real.pi * t)) = 0 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  set F : ℝ → ℝ := fun t => t / Real.pi * Real.sin (Real.pi * t)
    + 1 / Real.pi ^ 2 * Real.cos (Real.pi * t) with hF
  have hderiv : ∀ t : ℝ, HasDerivAt F (t * Real.cos (Real.pi * t)) t := by
    intro t
    have hlin : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
      simpa using (hasDerivAt_id t).const_mul Real.pi
    have hsin := (Real.hasDerivAt_sin (Real.pi * t)).comp t hlin
    have hcos := (Real.hasDerivAt_cos (Real.pi * t)).comp t hlin
    have e1 := ((hasDerivAt_id t).div_const Real.pi).mul hsin
    have e2 := (hasDerivAt_const t (1 / Real.pi ^ 2)).mul hcos
    have hsum := e1.add e2
    convert hsum using 1
    simp only [Function.comp_apply, id_eq]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => t * Real.cos (Real.pi * t)).intervalIntegrable _ _)]
  simp only [hF, mul_one, mul_neg_one, Real.sin_neg, Real.cos_neg, Real.sin_pi, Real.cos_pi]
  field_simp
  ring

/-- {lit}`∫₋₁¹ t² cos(πt) dt = −4/π²`. -/
theorem integral_sq_mul_cos_pi :
    (∫ t in (-1:ℝ)..1, t ^ 2 * Real.cos (Real.pi * t)) = -4 / Real.pi ^ 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  set F : ℝ → ℝ := fun t => t ^ 2 / Real.pi * Real.sin (Real.pi * t)
    + 2 * t / Real.pi ^ 2 * Real.cos (Real.pi * t)
    + -(2 / Real.pi ^ 3) * Real.sin (Real.pi * t) with hF
  have hderiv : ∀ t : ℝ, HasDerivAt F (t ^ 2 * Real.cos (Real.pi * t)) t := by
    intro t
    have hlin : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
      simpa using (hasDerivAt_id t).const_mul Real.pi
    have hsin := (Real.hasDerivAt_sin (Real.pi * t)).comp t hlin
    have hcos := (Real.hasDerivAt_cos (Real.pi * t)).comp t hlin
    have e1 := ((hasDerivAt_pow 2 t).div_const Real.pi).mul hsin
    have e2 := (((hasDerivAt_id t).const_mul 2).div_const (Real.pi ^ 2)).mul hcos
    have e3 := (hasDerivAt_const t (-(2 / Real.pi ^ 3))).mul hsin
    have hsum := (e1.add e2).add e3
    convert hsum using 1
    simp only [Function.comp_apply, id_eq]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by fun_prop : Continuous fun t : ℝ => t ^ 2 * Real.cos (Real.pi * t)).intervalIntegrable _ _)]
  simp only [hF, mul_one, mul_neg_one, Real.sin_neg, Real.cos_neg, Real.sin_pi, Real.cos_pi]
  field_simp
  ring

/-- {lit}`∫₋₁¹ q = 0` for {lit}`q(t) = 15/(2π²)(1 − 3t²)`. -/
theorem integral_q644 : (∫ t in (-1:ℝ)..1, 15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2)) = 0 := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t => 15 / (2 * Real.pi ^ 2) * (t - t ^ 3))
      (15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2)) t := by
    intro t
    have := ((hasDerivAt_id t).sub (hasDerivAt_pow 3 t)).const_mul (15 / (2 * Real.pi ^ 2))
    convert this using 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t)
    ((by fun_prop : Continuous fun t : ℝ =>
      15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2)).intervalIntegrable _ _)]
  norm_num

/-- {lit}`∫₋₁¹ t q = 0` for {lit}`q(t) = 15/(2π²)(1 − 3t²)`. -/
theorem integral_id_mul_q644 :
    (∫ t in (-1:ℝ)..1, t * (15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2))) = 0 := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t => 15 / (2 * Real.pi ^ 2) * (t ^ 2 / 2 - 3 * t ^ 4 / 4))
      (t * (15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2))) t := by
    intro t
    have := ((((hasDerivAt_pow 2 t).div_const 2)).sub
      (((hasDerivAt_pow 4 t).const_mul (3 : ℝ)).div_const 4)).const_mul (15 / (2 * Real.pi ^ 2))
    convert this using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t)
    ((by fun_prop : Continuous fun t : ℝ =>
      t * (15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2))).intervalIntegrable _ _)]
  norm_num

/-- {lit}`∫₋₁¹ t² q = −4/π²` for {lit}`q(t) = 15/(2π²)(1 − 3t²)`. -/
theorem integral_sq_mul_q644 :
    (∫ t in (-1:ℝ)..1, t ^ 2 * (15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2))) = -4 / Real.pi ^ 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hg : ∀ t : ℝ, HasDerivAt (fun t => 15 / (2 * Real.pi ^ 2) * (t ^ 3 / 3 - 3 * t ^ 5 / 5))
      (t ^ 2 * (15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2))) t := by
    intro t
    have := ((((hasDerivAt_pow 3 t).div_const 3)).sub
      (((hasDerivAt_pow 5 t).const_mul (3 : ℝ)).div_const 5)).const_mul (15 / (2 * Real.pi ^ 2))
    convert this using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t)
    ((by fun_prop : Continuous fun t : ℝ =>
      t ^ 2 * (15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2))).intervalIntegrable _ _)]
  norm_num
  field_simp
  ring

/-- 6.44 The Riesz vector for {lit}`φ(p) = ∫₋₁¹ p(t)cos(πt) dt` on {lit}`𝒫₂(ℝ)` is
{lit}`q(x) = 15/(2π²)(1 − 3x²)`: for every quadratic {lit}`p(t) = a + bt + ct²`,
{lit}`∫₋₁¹ p(t)cos(πt) dt = ∫₋₁¹ p(t) q(t) dt`. -/
theorem riesz_computation_644 (a b c : ℝ) :
    (∫ t in (-1:ℝ)..1, (a + b * t + c * t ^ 2) * Real.cos (Real.pi * t))
      = ∫ t in (-1:ℝ)..1, (a + b * t + c * t ^ 2)
          * (15 / (2 * Real.pi ^ 2) * (1 - 3 * t ^ 2)) := by
  have moment_split : ∀ (g : ℝ → ℝ), Continuous g →
      (∫ t in (-1:ℝ)..1, (a + b * t + c * t ^ 2) * g t)
      = a * (∫ t in (-1:ℝ)..1, g t) + b * (∫ t in (-1:ℝ)..1, t * g t)
        + c * (∫ t in (-1:ℝ)..1, t ^ 2 * g t) := by
    intro g hg
    have c0 : IntervalIntegrable g MeasureTheory.volume (-1) 1 := hg.intervalIntegrable (-1) 1
    have c1 : IntervalIntegrable (fun t => t * g t) MeasureTheory.volume (-1) 1 :=
      (continuous_id.mul hg).intervalIntegrable (-1) 1
    have c2 : IntervalIntegrable (fun t => t ^ 2 * g t) MeasureTheory.volume (-1) 1 :=
      ((continuous_pow 2).mul hg).intervalIntegrable (-1) 1
    rw [intervalIntegral.integral_congr
          (g := fun t => a * g t + b * (t * g t) + c * (t ^ 2 * g t)) (fun t _ => by ring),
      intervalIntegral.integral_add ((c0.const_mul a).add (c1.const_mul b)) (c2.const_mul c),
      intervalIntegral.integral_add (c0.const_mul a) (c1.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [moment_split _ (by fun_prop), moment_split _ (by fun_prop),
    integral_cos_pi, integral_id_mul_cos_pi, integral_sq_mul_cos_pi,
    integral_q644, integral_id_mul_q644, integral_sq_mul_q644]

end Riesz644

/-! # Exercises 6B -/

/-- 6B.1 Converse to 6.24: if {lit}`‖a₁e₁ + ⋯ + aₘeₘ‖² = |a₁|² + ⋯ + |aₘ|²` for
all scalars, then {lit}`e₁, …, eₘ` is orthonormal. -/
theorem exercise_6B_1 {m : ℕ} (e : Fin m → V)
    (h : ∀ a : Fin m → 𝕜, ‖∑ i, a i • e i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2) :
    Orthonormal 𝕜 e := by
  sorry

/-- 6B.2 (a) For {lit}`θ ∈ ℝ`, both {lit}`(cos θ, sin θ), (−sin θ, cos θ)` and
{lit}`(cos θ, sin θ), (sin θ, −cos θ)` are orthonormal bases of {lit}`ℝ²`. Stated as
orthonormality; each list then has length {lit}`2 = dim ℝ²`, so it is an orthonormal
basis by 6.28 ({name}`orthonormalBasis_of_length`). -/
theorem exercise_6B_2a (θ : ℝ) :
    Orthonormal ℝ ![!₂[Real.cos θ, Real.sin θ], !₂[-Real.sin θ, Real.cos θ]] ∧
      Orthonormal ℝ ![!₂[Real.cos θ, Real.sin θ], !₂[Real.sin θ, -Real.cos θ]] := by sorry

/-- 6B.2 (b) Every orthonormal basis of {lit}`ℝ²` (here: every orthonormal list
{lit}`v` of two vectors, automatically a basis) has one of the two forms in (a):
some {lit}`θ` with {lit}`v = (cos θ, sin θ), (−sin θ, cos θ)` or
{lit}`v = (cos θ, sin θ), (sin θ, −cos θ)`. -/
theorem exercise_6B_2b (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) (hv : Orthonormal ℝ v) :
    ∃ θ : ℝ, v = ![!₂[Real.cos θ, Real.sin θ], !₂[-Real.sin θ, Real.cos θ]] ∨
      v = ![!₂[Real.cos θ, Real.sin θ], !₂[Real.sin θ, -Real.cos θ]] := by sorry

/-- 6B.3 An orthonormal list {lit}`e₁, …, eₘ` satisfies Parseval's equality for a
vector {lit}`v` iff {lit}`v ∈ span(e₁, …, eₘ)`. -/
theorem exercise_6B_3 {m : ℕ} (e : Fin m → V) (he : Orthonormal 𝕜 e) (v : V) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪e i, v⟫_𝕜‖ ^ 2 ↔
      v ∈ Submodule.span 𝕜 (Set.range e) := by
  sorry

section Fourier6B
open MeasureTheory Real

/-- The {lit}`2n + 1` trigonometric functions of 6B.4, indexed by {lit}`Fin (2n+1)`:
index {lit}`0` is the constant {lit}`1/√(2π)`, indices {lit}`1, …, n` are the cosines
{lit}`(cos kx)/√π`, and {lit}`n+1, …, 2n` are the sines {lit}`(sin kx)/√π`. -/
noncomputable def fourierList (n : ℕ) : Fin (2 * n + 1) → C(ℝ, ℝ) := fun i =>
  if (i : ℕ) = 0 then ContinuousMap.const ℝ (1 / sqrt (2 * π))
  else if (i : ℕ) ≤ n then ⟨fun x => cos ((i : ℕ) * x) / sqrt π, by fun_prop⟩
  else ⟨fun x => sin (((i : ℕ) - n : ℕ) * x) / sqrt π, by fun_prop⟩

/-- The interval {lit}`[-π, π]` is nondegenerate, so {lit}`C[-π, π]` carries the `L²`
inner product (see `L2Interval.lean`). -/
instance : Fact (-π < π) := ⟨by linarith [pi_pos]⟩

/-- The functions {name}`fourierList` as elements of {lit}`C[-π, π]`. -/
noncomputable def fourierL2 (n : ℕ) (i : Fin (2 * n + 1)) : L2C (-π) π :=
  (fourierList n i).restrict _

/-- 6B.4 For a positive integer {lit}`n`, the functions {name}`fourierL2` form an
orthonormal list in {lit}`C[-π, π]` with {lit}`⟨f, g⟩ = ∫₋π^π fg`. Each inner product
reduces to {lit}`∫₋π^π` of a product of the functions ({name}`L2C_inner_restrict`); the
book's hint is the product-to-sum formulas. -/
theorem exercise_6B_4 (n : ℕ) : Orthonormal ℝ (fourierL2 n) := by
  sorry

/-- The {lit}`k`-th Fourier cosine coefficient {lit}`(1/√π)∫₋π^π f(x)cos(kx) dx`. -/
noncomputable def fourierCosCoeff (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (1 / sqrt π) * ∫ x in (-π)..π, f x * cos (k * x)

/-- The {lit}`k`-th Fourier sine coefficient {lit}`(1/√π)∫₋π^π f(x)sin(kx) dx`. -/
noncomputable def fourierSinCoeff (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  (1 / sqrt π) * ∫ x in (-π)..π, f x * sin (k * x)

/-- 6B.5 (Bessel's inequality for Fourier coefficients) For continuous
{lit}`f : [-π, π] → ℝ`, every partial sum of the Fourier coefficients satisfies
{lit}`a₀²/2 + ∑_{k=1}^N (aₖ² + bₖ²) ≤ ∫₋π^π f²` (the book's infinite-sum form is the
{lit}`N → ∞` limit). It is Bessel's inequality (6.26) for the list of 6B.4. -/
theorem exercise_6B_5 (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (-π) π)) (N : ℕ) :
    fourierCosCoeff f 0 ^ 2 / 2
      + ∑ k ∈ Finset.Icc 1 N, (fourierCosCoeff f k ^ 2 + fourierSinCoeff f k ^ 2)
      ≤ ∫ x in (-π)..π, (f x) ^ 2 := by
  sorry

end Fourier6B

/-- 6B.6 (a) If {lit}`e₁, …, eₙ` is an orthonormal basis and
{lit}`‖eₖ − vₖ‖ < 1/√n` for each {lit}`k`, then {lit}`v₁, …, vₙ` is a basis. -/
theorem exercise_6B_6a [FiniteDimensional 𝕜 V] {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 V) (v : Fin n → V)
    (h : ∀ k, ‖b k - v k‖ < 1 / Real.sqrt n) :
    LinearIndependent 𝕜 v := by
  sorry

/-- 6B.6 (b) The bound {lit}`1/√n` in (a) is sharp: there exist {lit}`v₁, …, vₙ`
with {lit}`‖eₖ − vₖ‖ ≤ 1/√n` for each {lit}`k` that are *not* linearly independent. -/
theorem exercise_6B_6b [FiniteDimensional 𝕜 V] {n : ℕ}
    (hpos : 0 < n) (b : OrthonormalBasis (Fin n) 𝕜 V) :
    ∃ v : Fin n → V, (∀ k, ‖b k - v k‖ ≤ 1 / Real.sqrt n) ∧ ¬ LinearIndependent 𝕜 v := by
  sorry

/-- The basis {lit}`(1,0,0), (1,1,1), (1,1,2)` of {lit}`ℝ³` from 6B.7. -/
noncomputable def basis6B7 : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[1, 0, 0], !₂[1, 1, 1], !₂[1, 1, 2]]

/-- The Gram–Schmidt orthonormal basis of {lit}`basis6B7` from 6B.7. -/
noncomputable def onb6B7 : Fin 3 → EuclideanSpace ℝ (Fin 3) := sorry

/-- The Gram–Schmidt list {name}`onb6B7` is a basis of {lit}`ℝ³` (needed to form its
matrix in 6B.7). -/
theorem exercise_6B_7_onb6B7_is_basis : LADR.Section_2B.IsBasis ℝ onb6B7 := by sorry

section UpperTri6B7
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf)
open LADR.Section_5C (IsUpperTriangular)

/-- 6B.7 If {lit}`T ∈ ℒ(ℝ³)` is upper-triangular with respect to {name}`basis6B7`,
then {name}`onb6B7` is an *orthonormal* basis with respect to which {lit}`T` is
upper-triangular (stated with the matrix definition {name}`IsUpperTriangular`;
{lit}`hb` witnesses that {name}`basis6B7` is a basis). -/
theorem exercise_6B_7 (T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hb : IsBasis ℝ basis6B7)
    (hT : IsUpperTriangular (matrixOf hb hb T)) :
    Orthonormal ℝ onb6B7 ∧
      IsUpperTriangular (matrixOf exercise_6B_7_onb6B7_is_basis exercise_6B_7_onb6B7_is_basis T) := by
  sorry

end UpperTri6B7

section GramSchmidt6B8
open MeasureTheory
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf)
open LADR.Section_5C (IsUpperTriangular)

/-- The orthonormal basis of {lit}`𝒫₂(ℝ) = Polynomial.degreeLT ℝ 3` (with
{lit}`⟨p, q⟩ = ∫₀¹ pq`) to find in 6B.8, by Gram–Schmidt on {lit}`1, x, x²`. -/
noncomputable def legendreBasis01 (i : Fin 3) : Polynomial.degreeLT ℝ 3 := sorry

/-- The differentiation operator {lit}`p ↦ p′` as a linear operator on
{lit}`𝒫₂(ℝ) = Polynomial.degreeLT ℝ 3` (differentiation lowers degree, so it maps
{lit}`𝒫₂` into itself). -/
noncomputable def diffP2 : Polynomial.degreeLT ℝ 3 →ₗ[ℝ] Polynomial.degreeLT ℝ 3 :=
  LinearMap.codRestrict (Polynomial.degreeLT ℝ 3)
    (Polynomial.derivative.comp (Polynomial.degreeLT ℝ 3).subtype) <| by
    intro p
    rw [Polynomial.mem_degreeLT]
    by_cases hd : (p.val.derivative : Polynomial ℝ) = 0
    · show (p.val.derivative).degree < (3 : ℕ)
      rw [hd, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · have hp : (p : Polynomial ℝ) ≠ 0 := by rintro h0; apply hd; simp [h0]
      have hpnd : (p : Polynomial ℝ).natDegree ≠ 0 := by
        intro h; apply hd
        show (p : Polynomial ℝ).derivative = 0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.derivative_C]
      have h2 : (p : Polynomial ℝ).natDegree < 3 :=
        (Polynomial.natDegree_lt_iff_degree_lt hp).mpr (Polynomial.mem_degreeLT.mp p.2)
      have h3 : (p : Polynomial ℝ).derivative.natDegree < 3 := by
        have h1 := Polynomial.natDegree_derivative_lt hpnd; omega
      exact (Polynomial.natDegree_lt_iff_degree_lt hd).mp h3

/-- 6B.8 (a) On {lit}`𝒫₂(ℝ)` with {lit}`⟨p, q⟩ = ∫₀¹ pq`, applying Gram–Schmidt to
{lit}`1, x, x²` produces {name}`legendreBasis01`. Stated as the three properties that
characterize the Gram–Schmidt output (6.32 and Exercise 10): it is orthonormal
({lit}`∫₀¹ eᵢeⱼ = δᵢⱼ`), {lit}`span(e₀, …, eₖ) = span(1, …, xᵏ)` for each {lit}`k`, and
{lit}`⟨xᵏ, eₖ⟩ = ∫₀¹ xᵏeₖ > 0` for each {lit}`k`. -/
theorem exercise_6B_8a :
    (∀ i j, (∫ x in (0:ℝ)..1,
        (legendreBasis01 i : Polynomial ℝ).eval x * (legendreBasis01 j : Polynomial ℝ).eval x)
      = if i = j then 1 else 0) ∧
    (∀ k : Fin 3,
      Submodule.span ℝ ((fun i => (legendreBasis01 i : Polynomial ℝ)) '' {i | i ≤ k}) =
        Submodule.span ℝ ((fun i : Fin 3 => Polynomial.X ^ (i : ℕ)) '' {i | i ≤ k})) ∧
    (∀ k : Fin 3,
      0 < ∫ x in (0:ℝ)..1, x ^ (k : ℕ) * (legendreBasis01 k : Polynomial ℝ).eval x) := by
  sorry

/-- {name}`legendreBasis01` is a basis of {lit}`𝒫₂(ℝ)` (needed to form its matrix in
6B.8(b)). -/
theorem legendreBasis01_isBasis : IsBasis ℝ legendreBasis01 := sorry

/-- The matrix of {name}`diffP2` with respect to {name}`legendreBasis01` to find in
6B.8(b). -/
noncomputable def diffMatrix6B8 : Matrix (Fin 3) (Fin 3) ℝ := sorry

/-- 6B.8 (b) The matrix of the differentiation operator {name}`diffP2` on {lit}`𝒫₂(ℝ)`
with respect to the orthonormal basis {name}`legendreBasis01` is
{name}`diffMatrix6B8`, and this matrix is upper triangular (as expected from the
proof of 6.37). -/
theorem exercise_6B_8b :
    matrixOf legendreBasis01_isBasis legendreBasis01_isBasis diffP2 = diffMatrix6B8 ∧
      IsUpperTriangular diffMatrix6B8 := by
  sorry

end GramSchmidt6B8

open scoped ComplexOrder in
/-- 6B.9 If {lit}`e₁, …, eₘ` results from Gram–Schmidt applied to a linearly
independent list {lit}`v₁, …, vₘ`, then {lit}`⟨vₖ, eₖ⟩ > 0` for each {lit}`k`: the
book's {lit}`⟨vₖ, eₖ⟩` is mathlib's {lit}`⟪eₖ, vₖ⟫`, and {lit}`0 < ·` is the
{lit}`ComplexOrder` order on {lit}`𝕜`, i.e. "is a positive real" ({name}`RCLike.pos_iff`). -/
theorem exercise_6B_9 {m : ℕ} (v : Fin m → V) (hv : LinearIndependent 𝕜 v) (k : Fin m) :
    0 < ⟪InnerProductSpace.gramSchmidtNormed 𝕜 v k, v k⟫_𝕜 := by
  sorry

open scoped ComplexOrder in
/-- 6B.10 The orthonormal list produced by Gram–Schmidt (6.32) is the *unique*
orthonormal list {lit}`e₁, …, eₘ` such that {lit}`⟨vₖ, eₖ⟩ > 0` (a positive real, as in
6B.9) and {lit}`span(v₁, …, vₖ) = span(e₁, …, eₖ)` for each {lit}`k`. -/
theorem exercise_6B_10 {m : ℕ} (v : Fin m → V) (hv : LinearIndependent 𝕜 v)
    (e : Fin m → V) (he : Orthonormal 𝕜 e)
    (hpos : ∀ k, 0 < ⟪e k, v k⟫_𝕜)
    (hspan : ∀ k, Submodule.span 𝕜 (e '' {i | i ≤ k}) =
      Submodule.span 𝕜 (v '' {i | i ≤ k})) :
    e = InnerProductSpace.gramSchmidtNormed 𝕜 v := by
  sorry

section Riesz6B
open MeasureTheory

/-- The quadratic {lit}`q ∈ 𝒫₂(ℝ)` to find in 6B.11 (Riesz vector representing point
evaluation {lit}`p ↦ p(½)` for {lit}`⟨p, q⟩ = ∫₀¹ pq`). -/
noncomputable def q6B11 : Polynomial.degreeLT ℝ 3 := sorry

/-- 6B.11 The polynomial {name}`q6B11` satisfies {lit}`p(½) = ∫₀¹ pq` for every
{lit}`p ∈ 𝒫₂(ℝ)` (written {lit}`p = a + bx + cx²`). (Analytic function-space exercise, stated
as an integral identity.) -/
theorem exercise_6B_11 : ∀ a b c : ℝ,
    (a + b * (1 / 2) + c * (1 / 2) ^ 2)
      = ∫ x in (0:ℝ)..1, (a + b * x + c * x ^ 2) * (q6B11 : Polynomial ℝ).eval x := by
  sorry

/-- The quadratic {lit}`q ∈ 𝒫₂(ℝ)` to find in 6B.12 (the analogue of 6.44 on
{lit}`[0, 1]`, representing {lit}`p ↦ ∫₀¹ p(x)cos(πx) dx`). -/
noncomputable def q6B12 : Polynomial.degreeLT ℝ 3 := sorry

/-- 6B.12 The polynomial {name}`q6B12` satisfies {lit}`∫₀¹ p(x)cos(πx) dx = ∫₀¹ pq`
for every {lit}`p ∈ 𝒫₂(ℝ)` (written {lit}`p = a + bx + cx²`). The answer must lie in
{lit}`𝒫₂(ℝ)`; otherwise {lit}`q(x) = cos(πx)` would trivially work. (Analytic
function-space exercise, stated as an integral identity.) -/
theorem exercise_6B_12 : ∀ a b c : ℝ,
    (∫ x in (0:ℝ)..1, (a + b * x + c * x ^ 2) * Real.cos (Real.pi * x))
      = ∫ x in (0:ℝ)..1, (a + b * x + c * x ^ 2) * (q6B12 : Polynomial ℝ).eval x := by
  sorry

end Riesz6B

/-- 6B.13 A list {lit}`v₁, …, vₘ` is linearly dependent iff Gram–Schmidt produces
{lit}`fₖ = 0` for some {lit}`k`. -/
theorem exercise_6B_13 {m : ℕ} (v : Fin m → V) :
    ¬ LinearIndependent 𝕜 v ↔ ∃ k, InnerProductSpace.gramSchmidt 𝕜 v k = 0 := by
  sorry

/-- 6B.14 In a *real* inner product space, a linearly independent list
{lit}`v₁, …, vₘ` admits exactly {lit}`2ᵐ` orthonormal lists {lit}`e₁, …, eₘ` with
{lit}`span(v₁, …, vₖ) = span(e₁, …, eₖ)` for all {lit}`k` (the sign choices at each
Gram–Schmidt step). -/
theorem exercise_6B_14 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (v : Fin m → V) (hv : LinearIndependent ℝ v) :
    {e : Fin m → V | Orthonormal ℝ e ∧
      ∀ k, Submodule.span ℝ (v '' {i | i ≤ k}) =
        Submodule.span ℝ (e '' {i | i ≤ k})}.ncard = 2 ^ m := by
  sorry

/-- 6B.15 If {lit}`⟨·, ·⟩₁` and {lit}`⟨·, ·⟩₂` are inner products with the same
orthogonal pairs, then one is a positive scalar multiple of the other. (Stated
for two inner-product structures {lit}`i₁, i₂` on the same space.) -/
theorem exercise_6B_15 {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (i₁ i₂ : InnerProductSpace.Core 𝕜 V)
    (h : ∀ u w : V, i₁.inner u w = 0 ↔ i₂.inner u w = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ u w : V, i₁.inner u w = (c : 𝕜) * i₂.inner u w := by
  sorry

/-- 6B.16 On a finite-dimensional space any two inner-product norms are equivalent:
there is {lit}`c > 0` with {lit}`‖v‖₁ ≤ c‖v‖₂` for all {lit}`v` (norms
{lit}`‖v‖ᵢ = √⟨v, v⟩ᵢ`). -/
theorem exercise_6B_16 {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module.Finite 𝕜 V]
    (i₁ i₂ : InnerProductSpace.Core 𝕜 V) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V,
      Real.sqrt (RCLike.re (i₁.inner v v)) ≤ c * Real.sqrt (RCLike.re (i₂.inner v v)) := by
  sorry

/-- 6B.17 Over {lit}`ℂ`, if {lit}`1` is the only eigenvalue of {lit}`T` and
{lit}`‖Tv‖ ≤ ‖v‖` for all {lit}`v`, then {lit}`T` is the identity operator. -/
theorem exercise_6B_17 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V)
    (h1 : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → μ = 1)
    (h2 : ∀ v : V, ‖T v‖ ≤ ‖v‖) :
    T = LinearMap.id := by
  sorry

/-- 6B.18 If {lit}`u₁, …, uₘ` is linearly independent, there exists {lit}`v` with
{lit}`⟨uₖ, v⟩ = 1` for all {lit}`k`. -/
theorem exercise_6B_18 {m : ℕ} (u : Fin m → V) (hu : LinearIndependent 𝕜 u) :
    ∃ v : V, ∀ k, ⟪u k, v⟫_𝕜 = 1 := by
  sorry

/-- 6B.19 If {lit}`v₁, …, vₙ` is a basis of {lit}`V`, there is a basis
{lit}`u₁, …, uₙ` with {lit}`⟨vⱼ, uₖ⟩ = δⱼₖ` (a dual/biorthogonal basis). -/
theorem exercise_6B_19 [FiniteDimensional 𝕜 V] {n : ℕ}
    (v : Module.Basis (Fin n) 𝕜 V) :
    ∃ u : Module.Basis (Fin n) 𝕜 V, ∀ j k, ⟪v j, u k⟫_𝕜 = if j = k then 1 else 0 := by
  sorry

section UpperTri6B20
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf)
open LADR.Section_5C (IsUpperTriangular)

/-- 6B.20 Over {lit}`ℂ`, a commuting family {lit}`ℰ ⊆ ℒ(V)` on a finite-dimensional
space has a common orthonormal basis {lit}`e` (with basis witness {lit}`he`) with
respect to which every {lit}`T ∈ ℰ` is upper-triangular (stated with the matrix
definition {name}`IsUpperTriangular`). Strengthens the simultaneous-triangularization
exercise 5E.9(b) to an *orthonormal* basis. -/
theorem exercise_6B_20 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ℰ : Set (V →ₗ[ℂ] V))
    (hcomm : ∀ S ∈ ℰ, ∀ T ∈ ℰ, Commute S T) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V) (he : IsBasis ℂ (⇑e)),
      ∀ T ∈ ℰ, IsUpperTriangular (matrixOf he he T) := by
  sorry

end UpperTri6B20

/-- 6B.21 Over {lit}`ℂ`, if all eigenvalues of {lit}`T` have absolute value less
than 1, then for every {lit}`ε > 0` there is a positive integer {lit}`m` with
{lit}`‖Tᵐv‖ ≤ ε‖v‖` for all {lit}`v`. -/
theorem exercise_6B_21 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → ‖μ‖ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ v : V, ‖(T ^ m) v‖ ≤ ε * ‖v‖ := by
  sorry

section Riesz22
open MeasureTheory

/-- 6B.22 On {lit}`C[-1, 1]` with {lit}`⟨f, g⟩ = ∫₋₁¹ fg`, the evaluation functional
{lit}`φ(f) = f(0)` is *not* of the form {lit}`f ↦ ⟨f, g⟩`: there is no
{lit}`g ∈ C[-1, 1]` with {lit}`f(0) = ⟨f, g⟩` for every {lit}`f ∈ C[-1, 1]`. This shows the
Riesz representation theorem (6.42) can fail in infinite dimensions. -/
theorem exercise_6B_22 :
    ¬ ∃ g : L2C (-1) 1, ∀ f : L2C (-1) 1,
      L2C.toCont f ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ = ⟪f, g⟫_ℝ := by
  sorry

end Riesz22

/-- 6B.23 The norm makes {lit}`V` a metric space via {lit}`d(u, v) = ‖u − v‖`.
(a) {lit}`d` is a metric: it is nonnegative, vanishes exactly on the diagonal, is
symmetric, and satisfies the triangle inequality. (In mathlib this {lit}`d` is the
ambient {name}`NormedAddCommGroup` distance {lit}`dist`, so the four axioms are the
metric-space axioms; the point is to derive them from the norm rather than invoke the
prebuilt metric.) -/
@[avoiding dist_nonneg, dist_comm, dist_triangle, dist_eq_zero]
theorem exercise_6B_23a :
    (∀ u v : V, 0 ≤ ‖u - v‖) ∧
      (∀ u v : V, ‖u - v‖ = 0 ↔ u = v) ∧
      (∀ u v : V, ‖u - v‖ = ‖v - u‖) ∧
      (∀ u v w : V, ‖u - w‖ ≤ ‖u - v‖ + ‖v - w‖) := by sorry

/-- 6B.23 (b) If {lit}`V` is finite-dimensional then the metric is complete (every
Cauchy sequence converges): {lit}`V` is a {name}`CompleteSpace`. -/
theorem exercise_6B_23b [FiniteDimensional 𝕜 V] : CompleteSpace V := by
  sorry

/-- 6B.23 (c) Every finite-dimensional subspace {lit}`U ≤ V` is closed in {lit}`V`. -/
theorem exercise_6B_23c (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    IsClosed (U : Set V) := by
  sorry

end LADR.Section_6B
