module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import LinearAlgebraDoneRightLean.Section_5C
public import LinearAlgebraDoneRightLean.Section_5E
public import LinearAlgebraDoneRightLean.Section_6A
public import LinearAlgebraDoneRightLean.L2Interval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linter.Style
public import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 6B: Orthonormal Bases
-/

@[expose] public section

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
    ⟪(show L2C a b from (⟨(Set.Icc a b).domRestrict f, hf.domRestrict⟩ : C(Set.Icc a b, ℝ))),
      (show L2C a b from (⟨(Set.Icc a b).domRestrict g, hg.domRestrict⟩ : C(Set.Icc a b, ℝ)))⟫_ℝ
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
  have h02 : Real.sqrt 5 / 3 = 0 :=
    example_6_23e_inner.symm.trans (h.2 (show (0 : Fin 3) ≠ 2 by decide))
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

omit [IsWellOrder ι (· < ·)] in
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
  have : Fintype s := @Fintype.ofFinite s hli.finite
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
    ((tfae_upperTriangular hv T).out 1 3).mp hA
  have hflag_e : ∀ k, T (e k) ∈ span 𝕜 (e '' {i | i ≤ k}) := by
    intro k; rw [hspan_gs k]; exact flag_invariant v T hflag k (e k) (hek_mem k)
  exact ((tfae_upperTriangular he T).out 3 1).mp hflag_e

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
    refine hsum.congr_deriv ?_
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
    refine hsum.congr_deriv ?_
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
    refine this.congr_deriv ?_
    norm_num
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
  -- the hypothesis for `a` supported on one index, or on two indices `i ≠ j`
  have one : ∀ i (x : 𝕜), ‖x • e i‖ ^ 2 = ‖x‖ ^ 2 := by
    intro i x
    have := h (fun k => if k = i then x else 0)
    rwa [Fintype.sum_eq_single i (fun k hk => by simp [hk]),
      Fintype.sum_eq_single i (fun k hk => by simp [hk]), ite_eq_left rfl] at this
  have two : ∀ i j, i ≠ j → ∀ x y : 𝕜, ‖x • e i + y • e j‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    intro i j hij x y
    have := h (fun k => if k = i then x else if k = j then y else 0)
    rwa [Fintype.sum_eq_add i j hij (fun k hk => by simp [hk.1, hk.2]),
      Fintype.sum_eq_add i j hij (fun k hk => by simp [hk.1, hk.2]),
      ite_eq_left rfl, ite_eq_right hij.symm, ite_eq_left rfl] at this
  -- to show ‖ei‖ = 1, plug in a = 1 at i and 0 elsewhere
  have hnorm : ∀ i, ‖e i‖ = 1 := by
    intro i
    have := one i 1
    rw [one_smul, norm_one, one_pow] at this
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by rw [this, one_pow])
  refine ⟨hnorm, fun i j hij => ?_⟩
  -- observe ‖ei + ej‖² = ‖ei‖² + ‖ej‖² for i ≠ j, which gives Re ⟪ei, ej⟫ = 0
  have hre : RCLike.re ⟪e i, e j⟫_𝕜 = 0 := by
    have := two i j hij 1 1
    rw [one_smul, one_smul, norm_add_sq (𝕜 := 𝕜), hnorm i, hnorm j, norm_one] at this
    linarith
  -- consider ‖ei + i * ej‖² = ‖ei‖² + ‖ej‖² for i ≠ j, which gives Im ⟪ei, ej⟫ = 0
  have him : RCLike.im ⟪e i, e j⟫_𝕜 = 0 := by
    have := two i j hij 1 RCLike.I
    rw [one_smul, norm_add_sq (𝕜 := 𝕜), inner_smul_right, RCLike.I_mul_re, norm_smul,
      hnorm i, hnorm j, norm_one] at this
    linarith
  exact RCLike.ext (by simp [hre]) (by simp [him])

/-- 6B.2 (a) For {lit}`θ ∈ ℝ`, both {lit}`(cos θ, sin θ), (−sin θ, cos θ)` and
{lit}`(cos θ, sin θ), (sin θ, −cos θ)` are orthonormal bases of {lit}`ℝ²`. Stated as
orthonormality; each list then has length {lit}`2 = dim ℝ²`, so it is an orthonormal
basis by 6.28 ({name}`orthonormalBasis_of_length`). -/
theorem exercise_6B_2a (θ : ℝ) :
    Orthonormal ℝ ![!₂[Real.cos θ, Real.sin θ], !₂[-Real.sin θ, Real.cos θ]] ∧
      Orthonormal ℝ ![!₂[Real.cos θ, Real.sin θ], !₂[Real.sin θ, -Real.cos θ]] := by
  -- direct computation using cos^2 + sin^2 = 1
  have hθ := Real.cos_sq_add_sin_sq θ
  have hr : ∀ x y : ℝ, ⟪x, y⟫_ℝ = x * y := fun x y =>
    (RCLike.inner_apply (𝕜 := ℝ) x y).trans (by simp [mul_comm])
  constructor <;> rw [orthonormal_iff_ite] <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp only [PiLp.inner_apply, hr, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue, Fin.zero_eta, Fin.mk_one, reduceIte,
      Fin.reduceEq] <;> nlinarith [hθ]

/-- 6B.2 (b) Every orthonormal basis of {lit}`ℝ²` (here: every orthonormal list
{lit}`v` of two vectors, automatically a basis) has one of the two forms in (a):
some {lit}`θ` with {lit}`v = (cos θ, sin θ), (−sin θ, cos θ)` or
{lit}`v = (cos θ, sin θ), (sin θ, −cos θ)`. -/
theorem exercise_6B_2b (v : Fin 2 → EuclideanSpace ℝ (Fin 2)) (hv : Orthonormal ℝ v) :
    ∃ θ : ℝ, v = ![!₂[Real.cos θ, Real.sin θ], !₂[-Real.sin θ, Real.cos θ]] ∨
      v = ![!₂[Real.cos θ, Real.sin θ], !₂[Real.sin θ, -Real.cos θ]] := by
  have hr : ∀ x y : ℝ, ⟪x, y⟫_ℝ = x * y := fun x y =>
    (RCLike.inner_apply (𝕜 := ℝ) x y).trans (by simp [mul_comm])
  -- take v 0 = (a, b), notice ‖v0‖^2 = 1 so a² + b² = 1 thus -1 ≤ a, b ≤ 1
  have hunit : ∀ k, v k 0 ^ 2 + v k 1 ^ 2 = 1 := by
    intro k
    have h2 := EuclideanSpace.norm_sq_eq (v k)
    rw [hv.1 k, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      one_pow] at h2
    exact h2.symm
  -- there exist θ ∈ (-π, π] s.t. cos θ = a, then b = sin θ
  have hangle : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → ∃ θ, Real.cos θ = a ∧ Real.sin θ = b := by
    intro a b hab
    -- θ is the argument of `a + bi`, which lies in `(-π, π]`
    have hz : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
      rw [Complex.norm_def, Complex.normSq_mk, ← sq, ← sq, hab, Real.sqrt_one]
    have hz0 : (⟨a, b⟩ : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hz; exact zero_ne_one hz
    exact ⟨Complex.arg ⟨a, b⟩, by rw [Complex.cos_arg hz0, hz, div_one],
      by rw [Complex.sin_arg, hz, div_one]⟩
  obtain ⟨θ, hc, hs⟩ := hangle _ _ (hunit 0)
  -- similarly for v 1 = (c, d), there exists φ ∈ (-π, π] s.t. cos φ = c, then d = sin φ
  obtain ⟨φ, hc', hs'⟩ := hangle _ _ (hunit 1)
  -- finally ⟨v0, v1⟩ = 0 gives
  have horth : v 0 0 * v 1 0 + v 0 1 * v 1 1 = 0 := by
    have : ⟪v 0, v 1⟫_ℝ = 0 := hv.2 (show (0 : Fin 2) ≠ 1 by decide)
    rwa [PiLp.inner_apply, Fin.sum_univ_two, hr, hr] at this
  -- cos θ cos φ + sin θ sin φ = 0, which gives φ = θ + π/2 or φ = θ - π/2
  -- (that is, cos(φ - θ) = 0, so sin(φ - θ) = ±1)
  have hcos : Real.cos (φ - θ) = 0 := by
    rw [Real.cos_sub, hc, hc', hs, hs']; linarith
  have hsin : Real.sin (φ - θ) = 1 ∨ Real.sin (φ - θ) = -1 := by
    apply eq_or_eq_neg_of_sq_eq_sq
    have := Real.sin_sq_add_cos_sq (φ - θ)
    rw [hcos] at this
    linarith
  -- thus v1 must be either (−sin θ, cos θ) or (sin θ, −cos θ) up to the choice of θ
  have hφ : φ = θ + (φ - θ) := by ring
  have hcφ : v 1 0 = -Real.sin θ * Real.sin (φ - θ) := by
    rw [← hc']; conv_lhs => rw [hφ]
    rw [Real.cos_add, hcos]; ring
  have hsφ : v 1 1 = Real.cos θ * Real.sin (φ - θ) := by
    rw [← hs']; conv_lhs => rw [hφ]
    rw [Real.sin_add, hcos]; ring
  refine ⟨θ, ?_⟩
  rcases hsin with h1 | h1
  · left
    funext k; fin_cases k <;> ext i <;> fin_cases i <;> simp [hc, hs, hcφ, hsφ, h1]
  · right
    funext k; fin_cases k <;> ext i <;> fin_cases i <;> simp [hc, hs, hcφ, hsφ, h1]

/-- 6B.3 An orthonormal list {lit}`e₁, …, eₘ` satisfies Parseval's equality for a
vector {lit}`v` iff {lit}`v ∈ span(e₁, …, eₘ)`. -/
theorem exercise_6B_3 {m : ℕ} (e : Fin m → V) (he : Orthonormal 𝕜 e) (v : V) :
    ‖v‖ ^ 2 = ∑ i, ‖⟪e i, v⟫_𝕜‖ ^ 2 ↔
      v ∈ Submodule.span 𝕜 (Set.range e) := by
  constructor
  · -- => decompose v as u = ∑ ⟨ei, v⟩ei and w = v - u. we can show u and v are orthogonal
    -- so ‖v‖^2 = ‖u‖^2 + ‖w‖^2, and by hypothesis ‖w‖ = 0, so v = u ∈ span(e i | i : Fin m)
    intro hpars
    set u := ∑ i, ⟪e i, v⟫_𝕜 • e i with hu
    have hwe : ∀ k, ⟪e k, v - u⟫_𝕜 = 0 := by
      intro k
      rw [inner_sub_right, hu, he.inner_right_fintype, sub_self]
    have horth : LADR.Section_6A.Orthogonal (𝕜 := 𝕜) u (v - u) := by
      unfold LADR.Section_6A.Orthogonal
      rw [hu, sum_inner]
      exact Finset.sum_eq_zero fun k _ => by rw [inner_smul_left, hwe k, mul_zero]
    have hpyth := LADR.Section_6A.pythagorean _ _ horth
    rw [add_sub_cancel, hu, norm_sq_sum_orthonormal he, ← hpars] at hpyth
    have hw : ‖v - u‖ ^ 2 = 0 := by rw [← hu] at hpyth; linarith
    have hvu : v = u :=
      sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hw))
    rw [hvu]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · -- <= just the parseval equality on U = span(e i | i : Fin m), where ei is orthonormal basis
    intro hv
    set U := Submodule.span 𝕜 (Set.range e)
    let e' : Fin m → U := fun i => ⟨e i, Submodule.subset_span ⟨i, rfl⟩⟩
    have he' : Orthonormal 𝕜 e' :=
      ⟨fun i => by simpa [e'] using he.1 i,
        fun i j hij => by simpa [e', Submodule.coe_inner] using he.2 hij⟩
    have hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range e') := by
      rintro ⟨x, hx⟩ -
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hx
      have hx' : (⟨∑ i, c i • e i, hx⟩ : U) = ∑ i, c i • e' i := Subtype.ext (by simp [e'])
      rw [hx']
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have := parseval (OrthonormalBasis.mk he' hsp) ⟨v, hv⟩
    simpa [e', Submodule.coe_inner] using this

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

/-- {lit}`∫₋π^π cos(mx) dx` is {lit}`2π` for {lit}`m = 0` and {lit}`0` for any other integer
{lit}`m`. -/
theorem integral_cos_int_mul (m : ℤ) :
    ∫ x in (-π)..π, cos (m * x) = if m = 0 then 2 * π else 0 := by
  split_ifs with hm
  · simp [hm]; ring
  · have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hm', integral_cos,
      mul_neg, sin_neg, sin_int_mul_pi]
    simp

/-- {lit}`∫₋π^π sin(mx) dx = 0` for every integer {lit}`m`. -/
theorem integral_sin_int_mul (m : ℤ) : ∫ x in (-π)..π, sin (m * x) = 0 := by
  by_cases hm : m = 0
  · simp [hm]
  · have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => sin x) hm', integral_sin,
      mul_neg, cos_neg]
    simp

/-- {lit}`∫₋π^π cos(jx)cos(kx) dx = π·[j = k]` for positive integers {lit}`j, k`, by
{lit}`cos x cos y = (cos(x − y) + cos(x + y))/2`. -/
theorem integral_cos_mul_cos (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    ∫ x in (-π)..π, cos (j * x) * cos (k * x) = if j = k then π else 0 := by
  rw [intervalIntegral.integral_congr (g := fun x =>
      (cos (((j - k : ℤ) : ℝ) * x) + cos (((j + k : ℤ) : ℝ) * x)) / 2)
      (fun x _ => by push_cast; rw [sub_mul, add_mul, cos_sub, cos_add]; ring),
    intervalIntegral.integral_div,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul, integral_cos_int_mul]
  have hjk : (j + k : ℤ) ≠ 0 := by omega
  rw [ite_eq_right hjk]
  by_cases h : j = k
  · rw [ite_eq_left (by omega), ite_eq_left h]; ring
  · rw [ite_eq_right (by omega), ite_eq_right h]; ring

/-- {lit}`∫₋π^π sin(jx)sin(kx) dx = π·[j = k]` for positive integers {lit}`j, k`, by
{lit}`sin x sin y = (cos(x − y) − cos(x + y))/2`. -/
theorem integral_sin_mul_sin (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    ∫ x in (-π)..π, sin (j * x) * sin (k * x) = if j = k then π else 0 := by
  rw [intervalIntegral.integral_congr (g := fun x =>
      (cos (((j - k : ℤ) : ℝ) * x) - cos (((j + k : ℤ) : ℝ) * x)) / 2)
      (fun x _ => by push_cast; rw [sub_mul, add_mul, cos_sub, cos_add]; ring),
    intervalIntegral.integral_div,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul, integral_cos_int_mul]
  have hjk : (j + k : ℤ) ≠ 0 := by omega
  rw [ite_eq_right hjk]
  by_cases h : j = k
  · rw [ite_eq_left (by omega), ite_eq_left h]; ring
  · rw [ite_eq_right (by omega), ite_eq_right h]; ring

/-- {lit}`∫₋π^π sin(jx)cos(kx) dx = 0` for all integers, by
{lit}`sin x cos y = (sin(x + y) + sin(x − y))/2`. -/
theorem integral_sin_mul_cos (j k : ℕ) :
    ∫ x in (-π)..π, sin (j * x) * cos (k * x) = 0 := by
  rw [intervalIntegral.integral_congr (g := fun x =>
      (sin (((j + k : ℤ) : ℝ) * x) + sin (((j - k : ℤ) : ℝ) * x)) / 2)
      (fun x _ => by push_cast; rw [sub_mul, add_mul, sin_sub, sin_add]; ring),
    intervalIntegral.integral_div,
    intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    integral_sin_int_mul, integral_sin_int_mul]
  ring

/-- {lit}`∫₋π^π cos(kx) dx = 0` for a positive integer {lit}`k`. -/
theorem integral_cos_nat_mul (k : ℕ) (hk : 0 < k) : ∫ x in (-π)..π, cos (k * x) = 0 := by
  have := integral_cos_int_mul k
  rw [ite_eq_right (by omega)] at this
  exact_mod_cast this

/-- {lit}`∫₋π^π sin(kx) dx = 0` for every natural {lit}`k`. -/
theorem integral_sin_nat_mul (k : ℕ) : ∫ x in (-π)..π, sin (k * x) = 0 := by
  exact_mod_cast integral_sin_int_mul k

/-- Pulling the normalizing constants out: {lit}`∫ (f/a)(g/b) = (∫ fg)/(ab)`. -/
theorem integral_div_mul_div (f g : ℝ → ℝ) (a b : ℝ) :
    ∫ x in (-π)..π, f x / a * (g x / b) = (∫ x in (-π)..π, f x * g x) / (a * b) := by
  rw [← intervalIntegral.integral_div]
  congr 1; ext x; ring

/-- The functions {name}`fourierList` as elements of {lit}`C[-π, π]`. -/
noncomputable def fourierL2 (n : ℕ) (i : Fin (2 * n + 1)) : L2C (-π) π :=
  (fourierList n i).restrict _

/-- 6B.4 For a positive integer {lit}`n`, the functions {name}`fourierL2` form an
orthonormal list in {lit}`C[-π, π]` with {lit}`⟨f, g⟩ = ∫₋π^π fg`. Each inner product
reduces to {lit}`∫₋π^π` of a product of the functions ({name}`L2C_inner_restrict`); the
book's hint is the product-to-sum formulas. -/
theorem exercise_6B_4 (n : ℕ) : Orthonormal ℝ (fourierL2 n) := by
  -- to show the inner product then i ≠ j, use the
  -- cos x sin y = sin (x - y) + sin (x + y) / 2, etc. identities
  -- all integrals become sums of cos nx or sin nx for some n over [-π, π]
  -- which are zero when integrated over [-π, π].
  -- to show norm is 1
  -- integrate cos^2 ix for some i or sin^2 ix for some i over [-π, π]
  -- similarly use the identies but now we get a 1/2 term, which itegrates to π
  rw [orthonormal_iff_ite]
  intro i j
  rw [fourierL2, fourierL2, L2C_inner_restrict]
  simp only [fourierList]
  have hπ : sqrt π * sqrt π = π := mul_self_sqrt pi_pos.le
  have h2π : sqrt (2 * π) * sqrt (2 * π) = 2 * π := mul_self_sqrt (by positivity)
  have hπ0 : π ≠ 0 := pi_ne_zero
  split_ifs
  -- the cases `i = j` with `i`, `j` of different kinds (or `i ≠ j` both constant) are impossible
  all_goals try (subst_vars; omega)
  all_goals simp only [ContinuousMap.const_apply, ContinuousMap.coe_mk]
  all_goals rw [integral_div_mul_div]
  · -- the constant: `∫₋π^π 1 = 2π`
    simp only [mul_one]
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, h2π]
    field_simp; ring
  -- the constant against a cosine or sine: `∫₋π^π cos(kx) = ∫₋π^π sin(kx) = 0`
  · simp only [one_mul]
    rw [integral_cos_nat_mul (j : ℕ) (by omega), zero_div]
  · simp only [one_mul]
    rw [integral_sin_nat_mul, zero_div]
  · simp only [mul_one]
    rw [integral_cos_nat_mul (i : ℕ) (by omega), zero_div]
  -- two cosines, two sines, or a cosine and a sine: the product-to-sum identities
  · subst_vars
    rw [integral_cos_mul_cos _ _ (by omega) (by omega), ite_eq_left rfl, hπ, div_self hπ0]
  · rw [integral_cos_mul_cos _ _ (by omega) (by omega),
      ite_eq_right (fun h => ‹¬i = j› (Fin.ext h)), zero_div]
  · simp_rw [mul_comm (cos _) (sin _)]
    rw [integral_sin_mul_cos, zero_div]
  · simp only [mul_one]
    rw [integral_sin_nat_mul, zero_div]
  · rw [integral_sin_mul_cos, zero_div]
  · subst_vars
    rw [integral_sin_mul_sin _ _ (by omega) (by omega), ite_eq_left rfl, hπ, div_self hπ0]
  · rw [integral_sin_mul_sin _ _ (by omega) (by omega),
      ite_eq_right (fun h => ‹¬i = j› (Fin.ext (by omega))), zero_div]

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
  -- apply the bassels' inequality for the orthonormal set from exercise_6B_4
  -- `f` as an element of `C[-π, π]`, and the inner products with the list of 6B.4
  set F : L2C (-π) π := (⟨(Set.Icc (-π) π).domRestrict f, hf.domRestrict⟩ : C(Set.Icc (-π) π, ℝ))
  have hinner : ∀ i, ⟪fourierL2 (N + 1) i, F⟫_ℝ = ∫ x in (-π)..π, fourierList (N + 1) i x * f x :=
    fun i => L2C_inner_of_continuousOn _ f (fourierList (N + 1) i).continuous.continuousOn hf
  have hπ : 0 < π := pi_pos
  -- the list 6B.4 with `n = N + 1`, restricted to the indices `0`, `cos kx` and `sin kx` for
  -- `k = 1, …, N` (this also covers `N = 0`, where 6B.4 itself needs `n > 0`)
  let idx : Unit ⊕ (Finset.Icc 1 N) ⊕ (Finset.Icc 1 N) → Fin (2 * (N + 1) + 1)
    | .inl _ => ⟨0, by omega⟩
    | .inr (.inl k) => ⟨k, by have := Finset.mem_Icc.mp k.2; omega⟩
    | .inr (.inr k) => ⟨N + 1 + k, by have := Finset.mem_Icc.mp k.2; omega⟩
  have hidx : Function.Injective idx := by
    rintro (_ | ⟨k⟩ | ⟨k⟩) (_ | ⟨l⟩ | ⟨l⟩) h <;>
      simp only [idx, Fin.mk.injEq] at h <;>
      first
        | rfl
        | (have := Finset.mem_Icc.mp k.2; omega)
        | (have := Finset.mem_Icc.mp l.2; omega)
        | (congr 2; exact Subtype.ext (by omega))
  have hbes := bessel ((exercise_6B_4 (N + 1)).comp idx hidx) F Finset.univ
  -- compute the three kinds of inner products
  have h0 : ⟪fourierL2 (N + 1) (idx (.inl ())), F⟫_ℝ = (1 / sqrt (2 * π)) * ∫ x in (-π)..π, f x := by
    rw [hinner, ← intervalIntegral.integral_const_mul]
    simp [idx, fourierList]
  have hc : ∀ k : Finset.Icc 1 N, ⟪fourierL2 (N + 1) (idx (.inr (.inl k))), F⟫_ℝ =
      fourierCosCoeff f k := by
    intro k
    have := Finset.mem_Icc.mp k.2
    rw [hinner, fourierCosCoeff, ← intervalIntegral.integral_const_mul]
    simp only [idx, fourierList, ite_eq_right (show ¬(k : ℕ) = 0 by omega),
      ite_eq_left (show (k : ℕ) ≤ N + 1 by omega), ContinuousMap.coe_mk]
    congr 1; ext x; ring
  have hs : ∀ k : Finset.Icc 1 N, ⟪fourierL2 (N + 1) (idx (.inr (.inr k))), F⟫_ℝ =
      fourierSinCoeff f k := by
    intro k
    have := Finset.mem_Icc.mp k.2
    rw [hinner, fourierSinCoeff, ← intervalIntegral.integral_const_mul]
    simp only [idx, fourierList, ite_eq_right (show ¬(N + 1 + (k : ℕ)) = 0 by omega),
      ite_eq_right (show ¬(N + 1 + (k : ℕ)) ≤ N + 1 by omega), Nat.add_sub_cancel_left,
      ContinuousMap.coe_mk]
    congr 1; ext x; ring
  -- `‖f‖² = ∫ f²`
  have hF : ‖F‖ ^ 2 = ∫ x in (-π)..π, f x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2C_inner_of_continuousOn f f hf hf]
    simp only [sq]
  -- the constant term: `⟨f, 1/√(2π)⟩² = a₀²/2`
  have ha0 : fourierCosCoeff f 0 ^ 2 / 2 = ((1 / sqrt (2 * π)) * ∫ x in (-π)..π, f x) ^ 2 := by
    simp only [fourierCosCoeff, Nat.cast_zero, zero_mul, cos_zero, mul_one]
    rw [mul_pow, mul_pow, div_pow, div_pow, sq_sqrt hπ.le, sq_sqrt (by positivity)]
    field_simp
  simp only [Function.comp_apply, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, Real.norm_eq_abs, sq_abs, h0, hc, hs, hF] at hbes
  rw [ha0, Finset.sum_add_distrib]
  rw [← Finset.sum_coe_sort (Finset.Icc 1 N), ← Finset.sum_coe_sort (Finset.Icc 1 N)]
  linarith

end Fourier6B

/-- 6B.6 (a) If {lit}`e₁, …, eₙ` is an orthonormal basis and
{lit}`‖eₖ − vₖ‖ < 1/√n` for each {lit}`k`, then {lit}`v₁, …, vₙ` is a basis. -/
theorem exercise_6B_6a [FiniteDimensional 𝕜 V] {n : ℕ}
    (b : OrthonormalBasis (Fin n) 𝕜 V) (v : Fin n → V)
    (h : ∀ k, ‖b k - v k‖ < 1 / Real.sqrt n) :
    LinearIndependent 𝕜 v := by
  -- Suppose ∑ ai vi = 0. We want to show all ai = 0 to prove linear independence, which is enough for basis by dimension
  rw [Fintype.linearIndependent_iff]
  intro a ha
  by_contra hne
  push Not at hne
  obtain ⟨j, hj⟩ := hne
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Fin.pos j
  -- rewrite 0 = ∑ ai vi = ∑ ai ei + ∑ ai (vi - ei)
  have hsum : ∑ i, a i • b i = -∑ i, a i • (v i - b i) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ha, zero_sub, neg_neg]
  -- thus ‖∑ ai ei‖^2 = ‖ ∑ ai (vi - ei)‖^2 will work on each side separately
  -- LHS ‖∑ ai ei‖^2 = ∑ |ai|^2 by orthonormality of ei (earlier theorem)
  have hL : ‖∑ i, a i • b i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := norm_sq_sum_orthonormal b.orthonormal a
  -- RHS ‖ ∑ ai (vi - ei)‖^2 ≤ (∑ |ai| ‖vi - ei‖)^2 (triangle inequality)
  have hT : ‖∑ i, a i • (v i - b i)‖ ≤ ∑ i, ‖a i‖ * ‖v i - b i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp only [norm_smul]))
  -- < (∑ |ai| * 1/√n)^2 by assumption (if ∑|ai| ≠ 0)
  have hS : ∑ i, ‖a i‖ * ‖v i - b i‖ < ∑ i, ‖a i‖ * (1 / Real.sqrt n) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (by rw [norm_sub_rev]; exact (h i).le) (norm_nonneg _)
    · exact ⟨j, Finset.mem_univ _,
        mul_lt_mul_of_pos_left (by rw [norm_sub_rev]; exact h j) (norm_pos_iff.mpr hj)⟩
  -- = 1/n (∑ |ai|)^2
  have hR : ∑ i, ‖a i‖ ^ 2 < 1 / n * (∑ i, ‖a i‖) ^ 2 := by
    rw [← hL, hsum, norm_neg]
    calc ‖∑ i, a i • (v i - b i)‖ ^ 2 ≤ (∑ i, ‖a i‖ * ‖v i - b i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hT 2
      _ < (∑ i, ‖a i‖ * (1 / Real.sqrt n)) ^ 2 :=
          pow_lt_pow_left₀ hS (Finset.sum_nonneg fun i _ => by positivity) two_ne_zero
      _ = 1 / n * (∑ i, ‖a i‖) ^ 2 := by
          rw [← Finset.sum_mul, mul_pow, div_pow, Real.sq_sqrt hn0.le, one_pow]; ring
  -- using Cauchy–Schwarz inequality: (∑ |ai|)^2 ≤ n ∑ |ai|^2 from 6A16 (with xi = |ai| and y = 1 for each i)
  have hCS := LADR.Section_6A.sum_mul_sq_le (fun i => ‖a i‖) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hCS
  -- we get a contradiction.
  -- so only possible solution is if we made the sum ∑|ai| = 0, which implies all ai = 0.
  have : 1 / n * (∑ i, ‖a i‖) ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn0]
    linarith
  linarith

/-- 6B.6 (b) The bound {lit}`1/√n` in (a) is sharp: there exist {lit}`v₁, …, vₙ`
with {lit}`‖eₖ − vₖ‖ ≤ 1/√n` for each {lit}`k` that are *not* linearly independent. -/
theorem exercise_6B_6b [FiniteDimensional 𝕜 V] {n : ℕ}
    (hpos : 0 < n) (b : OrthonormalBasis (Fin n) 𝕜 V) :
    ∃ v : Fin n → V, (∀ k, ‖b k - v k‖ ≤ 1 / Real.sqrt n) ∧ ¬ LinearIndependent 𝕜 v := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
  -- take vi = ei - ∑ ei / n
  set s := ∑ j, b j with hs
  refine ⟨fun i => b i - (n : 𝕜)⁻¹ • s, fun k => ?_, ?_⟩
  · -- ‖vi - ei‖ = ‖- ∑ ej / n‖ = 1/n ‖∑ ej‖
    -- notice that ‖∑ej‖^2 = ∑ 1^2 = n, since the ej form an orthonormal basis, by theorem
    have hs2 : ‖s‖ ^ 2 = n := by
      have := norm_sq_sum_orthonormal b.orthonormal (fun _ => (1 : 𝕜))
      simpa only [one_smul, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] using this
    -- so ‖vi - ei‖ = 1/n * √n = 1/√n exactly.
    rw [sub_sub_cancel, norm_smul, norm_inv, RCLike.norm_natCast,
      ← Real.sqrt_sq (norm_nonneg s), hs2]
    have hsq : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    apply le_of_eq
    rw [eq_div_iff hsq, mul_assoc, Real.mul_self_sqrt hn0.le, inv_mul_cancel₀ hn0.ne']
  · -- but ∑ vi = ∑ ei - n ∑ ei /n = 0, while ai = 1 and non-zero, thus not LI.
    rw [Fintype.linearIndependent_iff]
    push Not
    refine ⟨fun _ => 1, ?_, ⟨0, hpos⟩, one_ne_zero⟩
    simp only [one_smul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← hs]
    rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hpos.ne'),
      one_smul, sub_self]

/-- The basis {lit}`(1,0,0), (1,1,1), (1,1,2)` of {lit}`ℝ³` from 6B.7. -/
noncomputable def basis6B7 : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[1, 0, 0], !₂[1, 1, 1], !₂[1, 1, 2]]

/-- The Gram–Schmidt orthonormal basis of {lit}`basis6B7` from 6B.7.
  v0 = (1, 0, 0) already norm 1
  v1 = (1, 1, 1) - 1 (1,0,0) = (0, 1, 1)
  v2 = (1, 1, 2) - 1  (1,0,0) - 3/2 (0, 1, 1) = (0, -1/2, 1/2)
  normalize to get the final orthonormal vectors
  v0 = (1, 0, 0)
  v1 = (0, 1/√2, 1/√2)
  v2 = (0, -1/√2, 1/√2)
-/
noncomputable def onb6B7 : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[1, 0, 0], !₂[0, (√2)⁻¹, (√2)⁻¹], !₂[0, -(√2)⁻¹, (√2)⁻¹]]

/-- {name}`onb6B7` is orthonormal (direct computation). -/
theorem onb6B7_orthonormal : Orthonormal ℝ onb6B7 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2' : √2 ≠ 0 := by positivity
  have hr : ∀ x y : ℝ, ⟪x, y⟫_ℝ = x * y := fun x y =>
    (RCLike.inner_apply (𝕜 := ℝ) x y).trans (by simp [mul_comm])
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [onb6B7, PiLp.inner_apply, hr, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, reduceIte, Fin.reduceEq] <;>
    field_simp <;> linarith

/-- The Gram–Schmidt list {name}`onb6B7` is a basis of {lit}`ℝ³` (needed to form its
matrix in 6B.7). -/
theorem exercise_6B_7_onb6B7_is_basis : LADR.Section_2B.IsBasis ℝ onb6B7 :=
  LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq _
    onb6B7_orthonormal.linearIndependent (by simp)

/-- Two lists with each vector in the other's initial spans have the same initial spans
{lit}`span(e₀, …, eₖ) = span(v₀, …, vₖ)`. -/
theorem span_initial_eq_of_mem {M : Type*} [AddCommGroup M] [Module ℝ M] {n : ℕ}
    (e v : Fin n → M) (hev : ∀ k, e k ∈ Submodule.span ℝ (v '' {i | i ≤ k}))
    (hve : ∀ k, v k ∈ Submodule.span ℝ (e '' {i | i ≤ k})) (k : Fin n) :
    Submodule.span ℝ (e '' {i | i ≤ k}) = Submodule.span ℝ (v '' {i | i ≤ k}) := by
  apply le_antisymm <;> rw [Submodule.span_le]
  · rintro _ ⟨j, hj, rfl⟩
    exact Submodule.span_mono (Set.image_mono fun i (hi : i ≤ j) => hi.trans hj) (hev j)
  · rintro _ ⟨j, hj, rfl⟩
    exact Submodule.span_mono (Set.image_mono fun i (hi : i ≤ j) => hi.trans hj) (hve j)

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
  -- gram-schmit process preserves wi in span of {v0, ..., vi}
  refine ⟨onb6B7_orthonormal, ?_⟩
  set v := basis6B7
  set e := onb6B7
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h2' : √2 ≠ 0 := by positivity
  have mem : ∀ (w : Fin 3 → EuclideanSpace ℝ (Fin 3)) (k i : Fin 3), i ≤ k →
      w i ∈ Submodule.span ℝ (w '' {i | i ≤ k}) := fun w k i hi =>
    Submodule.subset_span ⟨i, hi, rfl⟩
  -- each `eₖ` is a combination of `v₀, …, vₖ`, and vice versa
  have he1 : e 1 = (√2)⁻¹ • (v 1 - v 0) := by
    ext i; fin_cases i <;> simp [e, v, onb6B7, basis6B7]
  have he2 : e 2 = (√2)⁻¹ • (v 0 - (3 : ℝ) • v 1 + (2 : ℝ) • v 2) := by
    ext i; fin_cases i <;> simp [e, v, onb6B7, basis6B7] <;> ring
  have hv1 : v 1 = e 0 + √2 • e 1 := by
    ext i; fin_cases i <;> simp [e, v, onb6B7, basis6B7, h2']
  have hv2 : v 2 = e 0 + (3 / √2) • e 1 + (√2)⁻¹ • e 2 := by
    ext i; fin_cases i <;> simp [e, v, onb6B7, basis6B7] <;> field_simp <;> linarith
  have hev : ∀ k, e k ∈ Submodule.span ℝ (v '' {i | i ≤ k}) := by
    intro k; fin_cases k <;> dsimp only
    · exact (show e 0 = v 0 by ext i; fin_cases i <;> simp [e, v, onb6B7, basis6B7]) ▸
        mem v 0 0 le_rfl
    · show e 1 ∈ Submodule.span ℝ (v '' {i | i ≤ 1})
      rw [he1]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mem v 1 1 le_rfl) (mem v 1 0 (by decide)))
    · show e 2 ∈ Submodule.span ℝ (v '' {i | i ≤ 2})
      rw [he2]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.sub_mem _
        (mem v 2 0 (by decide)) (Submodule.smul_mem _ _ (mem v 2 1 (by decide))))
        (Submodule.smul_mem _ _ (mem v 2 2 le_rfl)))
  have hve : ∀ k, v k ∈ Submodule.span ℝ (e '' {i | i ≤ k}) := by
    intro k; fin_cases k <;> dsimp only
    · exact (show v 0 = e 0 by ext i; fin_cases i <;> simp [e, v, onb6B7, basis6B7]) ▸
        mem e 0 0 le_rfl
    · show v 1 ∈ Submodule.span ℝ (e '' {i | i ≤ 1})
      rw [hv1]
      exact Submodule.add_mem _ (mem e 1 0 (by decide)) (Submodule.smul_mem _ _ (mem e 1 1 le_rfl))
    · show v 2 ∈ Submodule.span ℝ (e '' {i | i ≤ 2})
      rw [hv2]
      exact Submodule.add_mem _ (Submodule.add_mem _ (mem e 2 0 (by decide))
        (Submodule.smul_mem _ _ (mem e 2 1 (by decide)))) (Submodule.smul_mem _ _ (mem e 2 2 le_rfl))
  -- so the flags agree, and `T` keeps each `span(e₀, …, eₖ)` invariant
  have hflag := ((LADR.Section_5C.tfae_upperTriangular hb T).out 1 3).mp hT
  have hflag_e : ∀ k, T (e k) ∈ Submodule.span ℝ (e '' {i | i ≤ k}) := by
    intro k
    rw [span_initial_eq_of_mem e v hev hve k]
    exact flag_invariant v T hflag k (e k) (hev k)
  exact ((LADR.Section_5C.tfae_upperTriangular _ T).out 3 1).mp hflag_e

end UpperTri6B7

section GramSchmidt6B8
open MeasureTheory
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf)
open LADR.Section_5C (IsUpperTriangular)

/-- The orthonormal basis of {lit}`𝒫₂(ℝ) = Polynomial.degreeLT ℝ 3` (with
{lit}`⟨p, q⟩ = ∫₀¹ pq`) to find in 6B.8, by Gram–Schmidt on {lit}`1, x, x²`.

by computation explicitly using the Gram–Schmidt process on `1, x, x²`

v0 = 1
v1 = √12 (x - 1/2)
v2 = (√180) (x² - x + 1/6)
-/
noncomputable def legendrePoly01 : Fin 3 → Polynomial ℝ :=
  ![Polynomial.C 1, Polynomial.C √12 * (Polynomial.X - Polynomial.C (1 / 2)),
    Polynomial.C √180 * (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (1 / 6))]

theorem legendrePoly01_natDegree (i : Fin 3) : (legendrePoly01 i).natDegree < 3 := by
  fin_cases i <;> simp only [legendrePoly01] <;>
    exact Nat.lt_succ_of_le (by simp <;> compute_degree!)

noncomputable def legendreBasis01 (i : Fin 3) : Polynomial.degreeLT ℝ 3 :=
  ⟨legendrePoly01 i, Polynomial.mem_degreeLT.mpr (Polynomial.degree_le_natDegree.trans_lt
    (by exact_mod_cast legendrePoly01_natDegree i))⟩

/-- {lit}`∫₀¹ pq` for polynomials of degree {lit}`< 3`, from their coefficients:
{lit}`∫₀¹ xⁱ⁺ʲ = 1/(i + j + 1)`. -/
theorem integral01_eval_mul_eval (p q : Polynomial ℝ) (hp : p.natDegree < 3)
    (hq : q.natDegree < 3) :
    ∫ x in (0:ℝ)..1, p.eval x * q.eval x =
      ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        p.coeff i * q.coeff j / ((i : ℝ) + j + 1) := by
  simp_rw [Polynomial.eval_eq_sum_range' hp, Polynomial.eval_eq_sum_range' hq,
    Finset.sum_mul_sum]
  rw [intervalIntegral.integral_finsetSum fun i _ => by
    apply Continuous.intervalIntegrable; fun_prop]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => by
    apply Continuous.intervalIntegrable; fun_prop]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_congr (g := fun x => p.coeff i * q.coeff j * x ^ (i + j))
      (fun x _ => by simp only; rw [pow_add]; ring),
    intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  field_simp
  ring

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
  have h12 : √12 * √12 = 12 := Real.mul_self_sqrt (by norm_num)
  have h180 : √180 * √180 = 180 := Real.mul_self_sqrt (by norm_num)
  refine ⟨fun i j => ?_, fun k => ?_, fun k => ?_⟩
  · show ∫ x in (0:ℝ)..1, (legendrePoly01 i).eval x * (legendrePoly01 j).eval x = _
    rw [integral01_eval_mul_eval _ _ (legendrePoly01_natDegree i) (legendrePoly01_natDegree j)]
    fin_cases i <;> fin_cases j <;>
      simp [legendrePoly01, Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_C,
        Polynomial.coeff_X_pow, Polynomial.coeff_one] <;>
      ring_nf <;> nlinarith [h12, h180]
  · -- each `eₖ` is a combination of `1, …, xᵏ`, and vice versa
    have h12' : √12 ≠ 0 := by positivity
    have h180' : √180 ≠ 0 := by positivity
    set e : Fin 3 → Polynomial ℝ := legendrePoly01
    set v : Fin 3 → Polynomial ℝ := fun i => Polynomial.X ^ (i : ℕ)
    have mem : ∀ (w : Fin 3 → Polynomial ℝ) (k i : Fin 3), i ≤ k →
        w i ∈ Submodule.span ℝ (w '' {i | i ≤ k}) := fun w k i hi =>
      Submodule.subset_span ⟨i, hi, rfl⟩
    have he0 : e 0 = v 0 := by simp [e, v, legendrePoly01]
    have he1 : e 1 = √12 • v 1 - (√12 / 2) • v 0 := by
      ext n; rcases n with _ | _ | n <;>
        (simp [e, v, legendrePoly01, Polynomial.coeff_X, Polynomial.coeff_C,
          Polynomial.coeff_one]; try ring)
    have he2 : e 2 = √180 • v 2 - √180 • v 1 + (√180 / 6) • v 0 := by
      ext n; rcases n with _ | _ | _ | n <;>
        (simp [e, v, legendrePoly01, Polynomial.coeff_X, Polynomial.coeff_C,
          Polynomial.coeff_X_pow, Polynomial.coeff_one]; try ring)
    have hv1 : v 1 = (√12)⁻¹ • e 1 + (1 / 2 : ℝ) • e 0 := by
      ext n; rcases n with _ | _ | n <;>
        simp [e, v, legendrePoly01, Polynomial.coeff_X, Polynomial.coeff_C,
          Polynomial.coeff_one]
    have hv2 : v 2 = (√180)⁻¹ • e 2 + (√12)⁻¹ • e 1 + (1 / 3 : ℝ) • e 0 := by
      ext n; rcases n with _ | _ | _ | n <;>
        (simp [e, v, legendrePoly01, Polynomial.coeff_X, Polynomial.coeff_C,
          Polynomial.coeff_X_pow, Polynomial.coeff_one]; try (field_simp; ring))
    have hev : ∀ k, e k ∈ Submodule.span ℝ (v '' {i | i ≤ k}) := by
      intro k; fin_cases k <;> dsimp only
      · exact he0 ▸ mem v 0 0 le_rfl
      · show e 1 ∈ Submodule.span ℝ (v '' {i | i ≤ 1})
        rw [he1]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (mem v 1 1 le_rfl))
          (Submodule.smul_mem _ _ (mem v 1 0 (by decide)))
      · show e 2 ∈ Submodule.span ℝ (v '' {i | i ≤ 2})
        rw [he2]
        exact Submodule.add_mem _ (Submodule.sub_mem _
          (Submodule.smul_mem _ _ (mem v 2 2 le_rfl)) (Submodule.smul_mem _ _ (mem v 2 1 (by decide))))
          (Submodule.smul_mem _ _ (mem v 2 0 (by decide)))
    have hve : ∀ k, v k ∈ Submodule.span ℝ (e '' {i | i ≤ k}) := by
      intro k; fin_cases k <;> dsimp only
      · exact he0 ▸ mem e 0 0 le_rfl
      · show v 1 ∈ Submodule.span ℝ (e '' {i | i ≤ 1})
        rw [hv1]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ (mem e 1 1 le_rfl))
          (Submodule.smul_mem _ _ (mem e 1 0 (by decide)))
      · show v 2 ∈ Submodule.span ℝ (e '' {i | i ≤ 2})
        rw [hv2]
        exact Submodule.add_mem _ (Submodule.add_mem _
          (Submodule.smul_mem _ _ (mem e 2 2 le_rfl)) (Submodule.smul_mem _ _ (mem e 2 1 (by decide))))
          (Submodule.smul_mem _ _ (mem e 2 0 (by decide)))
    exact span_initial_eq_of_mem e v hev hve k
  · -- `⟨xᵏ, eₖ⟩` from the coefficients
    have hpos12 : 0 < √12 := by positivity
    have hpos180 : 0 < √180 := by positivity
    have hX : ∀ k : Fin 3, (Polynomial.X ^ (k : ℕ) : Polynomial ℝ).natDegree < 3 := by
      intro k; rw [Polynomial.natDegree_X_pow]; exact k.2
    have := integral01_eval_mul_eval _ _ (hX k) (legendrePoly01_natDegree k)
    simp only [Polynomial.eval_pow, Polynomial.eval_X] at this
    show 0 < ∫ x in (0:ℝ)..1, x ^ (k : ℕ) * (legendrePoly01 k).eval x
    rw [this]
    fin_cases k <;>
      simp [legendrePoly01, Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_C,
        Polynomial.coeff_X_pow, Polynomial.coeff_one] <;>
      ring_nf <;> nlinarith

/-- {name}`legendreBasis01` is a basis of {lit}`𝒫₂(ℝ)` (needed to form its matrix in
6B.8(b)). -/
theorem legendreBasis01_isBasis : IsBasis ℝ legendreBasis01 := by
  have : Module.Finite ℝ (Polynomial.degreeLT ℝ 3) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℝ 3).symm
  refine LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq _ ?_
    ((Polynomial.degreeLTEquiv ℝ 3).finrank_eq.trans (Module.finrank_fin_fun ℝ)).symm
  -- an orthonormal list is linearly independent: pair `∑ gⱼeⱼ = 0` with each `eᵢ`
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := congrArg (fun p : Polynomial.degreeLT ℝ 3 =>
    ∫ x in (0:ℝ)..1, (p : Polynomial ℝ).eval x * (legendreBasis01 i : Polynomial ℝ).eval x) hg
  simp only [Submodule.coe_sum, Submodule.coe_smul, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul, Finset.sum_mul, ZeroMemClass.coe_zero,
    Polynomial.eval_zero, zero_mul, intervalIntegral.integral_zero] at h
  rw [intervalIntegral.integral_finsetSum fun j _ => by
    apply Continuous.intervalIntegrable; fun_prop] at h
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, exercise_6B_8a.1] at h
  simpa using h

/-- The matrix of {name}`diffP2` with respect to {name}`legendreBasis01` to find in
6B.8(b). -/
noncomputable def diffMatrix6B8 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, √12, 0; 0, 0, 2 * √15; 0, 0, 0]

/-- 6B.8 (b) The matrix of the differentiation operator {name}`diffP2` on {lit}`𝒫₂(ℝ)`
with respect to the orthonormal basis {name}`legendreBasis01` is
{name}`diffMatrix6B8`, and this matrix is upper triangular (as expected from the
proof of 6.37). -/
theorem exercise_6B_8b :
    matrixOf legendreBasis01_isBasis legendreBasis01_isBasis diffP2 = diffMatrix6B8 ∧
      IsUpperTriangular diffMatrix6B8 := by
  -- the answer is
  -- e2' = 2√15 e1
  -- e1' = √12 e0
  -- so the matrix is zeros with A01 = √12 and A12 = 2√15
  refine ⟨?_, fun j k hkj => by fin_cases j <;> fin_cases k <;> simp_all [diffMatrix6B8]⟩
  ext j k
  rw [LADR.Section_3C.matrixOf_apply]
  set b := legendreBasis01_isBasis.toModuleBasis
  have hb : ∀ i, b i = legendreBasis01 i := LADR.Section_2B.IsBasis.toModuleBasis_apply _
  have hD : ∀ p : Polynomial.degreeLT ℝ 3, (diffP2 p : Polynomial ℝ) = (p : Polynomial ℝ).derivative :=
    fun p => rfl
  have h15 : √15 * √12 = √180 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hD0 : diffP2 (legendreBasis01 0) = 0 := by
    apply Subtype.ext; rw [hD]; simp [legendreBasis01, legendrePoly01]
  have hD1 : diffP2 (legendreBasis01 1) = √12 • b 0 := by
    apply Subtype.ext; rw [hD, hb]
    simp [legendreBasis01, legendrePoly01, Polynomial.smul_eq_C_mul]
  have hD2 : diffP2 (legendreBasis01 2) = (2 * √15) • b 1 := by
    apply Subtype.ext; rw [hD, hb]
    ext n; rcases n with _ | _ | n <;>
      simp [legendreBasis01, legendrePoly01, Polynomial.coeff_X, Polynomial.coeff_C,
        Polynomial.coeff_one] <;>
      nlinarith [h15]
  clear_value b
  fin_cases j <;> fin_cases k <;>
    simp [hD0, hD1, hD2, diffMatrix6B8, Module.Basis.repr_self]

end GramSchmidt6B8

open scoped ComplexOrder in
/-- 6B.9 If {lit}`e₁, …, eₘ` results from Gram–Schmidt applied to a linearly
independent list {lit}`v₁, …, vₘ`, then {lit}`⟨vₖ, eₖ⟩ > 0` for each {lit}`k`: the
book's {lit}`⟨vₖ, eₖ⟩` is mathlib's {lit}`⟪eₖ, vₖ⟫`, and {lit}`0 < ·` is the
{lit}`ComplexOrder` order on {lit}`𝕜`, i.e. "is a positive real" ({name}`RCLike.pos_iff`). -/
theorem exercise_6B_9 {m : ℕ} (v : Fin m → V) (hv : LinearIndependent 𝕜 v) (k : Fin m) :
    0 < ⟪InnerProductSpace.gramSchmidtNormed 𝕜 v k, v k⟫_𝕜 := by
  -- ei is normalization of vi - proj{vi, e1} - proj{vi, e2} - ... - proj{vi, e_{i-1}}
  -- ⟨vk, ek⟩ will eliminate all projections so it equals ‖vi‖, divided by some normalization
  -- this it is real and positive.
  set f := InnerProductSpace.gramSchmidt 𝕜 v k with hf
  have hf0 : f ≠ 0 := gramSchmidt_ne_zero_of_linearIndependent hv k
  -- `vₖ = fₖ + ∑_{j<k} (multiple of fⱼ)`, and each `fⱼ` is orthogonal to `fₖ`
  have hfv : ⟪f, v k⟫_𝕜 = ⟪f, f⟫_𝕜 := by
    rw [InnerProductSpace.gramSchmidt_def' 𝕜 v k, ← hf, inner_add_right, inner_sum,
      Finset.sum_eq_zero, add_zero]
    intro j hj
    rw [Submodule.starProjection_singleton, inner_smul_right,
      inner_eq_zero_symm.mp (gramSchmidt_orthogonal_of_lt v (Finset.mem_Iio.mp hj)), mul_zero]
  -- so `⟨vₖ, eₖ⟩ = ‖fₖ‖²/‖fₖ‖ = ‖fₖ‖ > 0`
  rw [InnerProductSpace.gramSchmidtNormed, ← hf, inner_smul_left, hfv,
    inner_self_eq_norm_sq_to_K, map_inv₀, RCLike.conj_ofReal]
  have hpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have : ((‖f‖ : 𝕜))⁻¹ * (‖f‖ : 𝕜) ^ 2 = ((‖f‖⁻¹ * ‖f‖ ^ 2 : ℝ) : 𝕜) := by push_cast; ring
  rw [this, RCLike.ofReal_pos]
  positivity

/-- The common step of 6B.10 and 6B.14: if {lit}`e` has the same initial spans as {lit}`v`, and
{lit}`eₖ` and {lit}`fₖ` are both orthogonal to {lit}`e₁, …, eₖ₋₁`, then {lit}`eₖ` is a multiple
of {lit}`fₖ`. Write {lit}`W = span(e₁, …, eₖ₋₁)`, {lit}`vₖ = fₖ + w` and {lit}`eₖ = a vₖ + u` with
{lit}`u, w ∈ W`: then {lit}`eₖ - a fₖ = a w + u` is in {lit}`W` and also orthogonal to {lit}`W`. -/
theorem exists_eq_smul_gramSchmidt {m : ℕ} (v e : Fin m → V)
    (hspan : ∀ k, Submodule.span 𝕜 (e '' {i | i ≤ k}) = Submodule.span 𝕜 (v '' {i | i ≤ k}))
    (k : Fin m)
    (hfe : ∀ i, i < k → ⟪e i, InnerProductSpace.gramSchmidt 𝕜 v k⟫_𝕜 = 0)
    (hee : ∀ i, i < k → ⟪e i, e k⟫_𝕜 = 0) :
    ∃ a : 𝕜, e k = a • InnerProductSpace.gramSchmidt 𝕜 v k := by
  set f := InnerProductSpace.gramSchmidt 𝕜 v k with hf
  set W := Submodule.span 𝕜 (e '' Set.Iio k) with hW
  -- anything orthogonal to `e₁, …, eₖ₋₁` is orthogonal to their span `W`
  have hperp : ∀ y, (∀ i, i < k → ⟪e i, y⟫_𝕜 = 0) → ∀ x ∈ W, ⟪x, y⟫_𝕜 = 0 := by
    intro y hy x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact hy i hi
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
    | smul c _ _ h => rw [inner_smul_left, h, mul_zero]
  have hfW : ∀ x ∈ W, ⟪x, f⟫_𝕜 = 0 := hperp f hfe
  have heW : ∀ x ∈ W, ⟪x, e k⟫_𝕜 = 0 := hperp (e k) hee
  have hsub : ∀ i, i < k → Submodule.span 𝕜 (v '' {j | j ≤ i}) ≤ W := fun i hi => by
    rw [← hspan i]
    exact Submodule.span_mono (Set.image_mono fun j hj => lt_of_le_of_lt hj hi)
  -- `vₖ = fₖ + w` with `w ∈ W`
  obtain ⟨w, hwW, hvf⟩ : ∃ w ∈ W, v k = f + w := by
    refine ⟨_, Submodule.sum_mem _ fun j hj => ?_, InnerProductSpace.gramSchmidt_def' 𝕜 v k⟩
    rw [Submodule.starProjection_singleton]
    exact Submodule.smul_mem _ _
      (hsub j (Finset.mem_Iio.mp hj) (gramSchmidt_mem_span_of_le v le_rfl))
  -- `eₖ = a vₖ + u` with `u ∈ W`
  have hek : e k ∈ Submodule.span 𝕜 (insert (v k) (v '' Set.Iio k)) := by
    have h : e k ∈ Submodule.span 𝕜 (v '' {i | i ≤ k}) :=
      hspan k ▸ Submodule.subset_span ⟨k, le_refl k, rfl⟩
    rwa [← Set.image_insert_eq, Set.Iio_insert]
  obtain ⟨a, u, hu, hau⟩ := Submodule.mem_span_insert.mp hek
  have huW : u ∈ W := by
    refine Submodule.span_le.mpr ?_ hu
    rintro _ ⟨i, hi, rfl⟩
    exact hsub i hi (Submodule.subset_span ⟨i, le_refl i, rfl⟩)
  -- the part of `eₖ - a fₖ` in `W` is also orthogonal to `W`, so `eₖ = a fₖ`
  have hr : a • w + u = 0 := by
    have hrW : a • w + u ∈ W := add_mem (Submodule.smul_mem _ _ hwW) huW
    have hrr : e k - a • f = a • w + u := by rw [hau, hvf, smul_add]; abel
    rw [← inner_self_eq_zero (𝕜 := 𝕜)]
    nth_rw 2 [← hrr]
    rw [inner_sub_right, inner_smul_right, heW _ hrW, hfW _ hrW, mul_zero, sub_zero]
  exact ⟨a, by rw [hau, hvf, smul_add, add_assoc, hr, add_zero]⟩

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
  -- we will proceed by induction
  -- assume ei = gram-schmidt for all i < k
  -- enough to show that there is a unique choice for ek under the conditions
  -- 1. ek is in span(v₁, …, vₖ) = span(e₁, …, eₖ₋₁, vk)
  -- 2. ek is orthogonal to e₁, …, eₖ₋₁
  -- 3. ⟨vk, ek⟩ > 0
  -- 4. ‖ek‖ = 1
  -- let W = span(e₁, …, eₖ₋₁); by 2, ek ⟂ W, and by induction (ei = fi/‖fi‖) also fk ⟂ W
  -- the Gram-Schmidt recursion gives vk = fk + w with w ∈ W
  -- by 1, ek = a vk + u with u ∈ W, so ek - a fk = a w + u
  -- this is in W and also orthogonal to W, so it is 0, i.e. ek = a fk
  -- vk = fk + w and fk ⟂ w give ⟨vk, fk⟩ = ‖fk‖², and fk ≠ 0 by linear independence of vi
  -- by 3, 0 < ⟨vk, ek⟩ = ā ‖fk‖², so a is Real and positive, which fixes the phase of a
  -- by 4, 1 = ‖ek‖ = a ‖fk‖, so a = 1/‖fk‖
  funext k
  induction k using WellFoundedLT.induction with | ind k ih
  set f := InnerProductSpace.gramSchmidt 𝕜 v k with hf
  have hf0 : f ≠ 0 := gramSchmidt_ne_zero_of_linearIndependent hv k
  obtain ⟨a, hea⟩ : ∃ a : 𝕜, e k = a • f := exists_eq_smul_gramSchmidt v e hspan k
    (fun i hi => by
      rw [ih i hi, InnerProductSpace.gramSchmidtNormed, inner_smul_left,
        gramSchmidt_orthogonal_of_lt v hi, mul_zero])
    (fun i hi => he.2 hi.ne)
  -- `⟨vₖ, fₖ⟩ = ‖fₖ‖²`, so positivity of `⟨vₖ, eₖ⟩` says `a` is a positive real `t`
  have hfv : ⟪f, v k⟫_𝕜 = ((‖f‖ ^ 2 : ℝ) : 𝕜) := by
    rw [InnerProductSpace.gramSchmidt_def' 𝕜 v k, ← hf, inner_add_right, inner_sum,
      Finset.sum_eq_zero, add_zero, inner_self_eq_norm_sq_to_K]
    · push_cast; rfl
    · intro j hj
      rw [Submodule.starProjection_singleton, inner_smul_right,
        inner_eq_zero_symm.mp (gramSchmidt_orthogonal_of_lt v (Finset.mem_Iio.mp hj)), mul_zero]
  have hnf : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have hp := hpos k
  rw [hea, inner_smul_left, hfv] at hp
  obtain ⟨x, hx, hxa⟩ := RCLike.pos_iff_exists_ofReal.mp hp
  have hta : a = ((x / ‖f‖ ^ 2 : ℝ) : 𝕜) := by
    have hc : (starRingEnd 𝕜) a = ((x / ‖f‖ ^ 2 : ℝ) : 𝕜) := by
      have hne : ((‖f‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (by positivity)
      rw [RCLike.ofReal_div, hxa, mul_div_cancel_right₀ _ hne]
    rw [← RCLike.conj_conj a, hc, RCLike.conj_ofReal]
  set t := x / ‖f‖ ^ 2 with ht
  have htpos : 0 < t := by positivity
  -- `‖eₖ‖ = 1` gives `t = 1/‖fₖ‖`
  have hnorm : t * ‖f‖ = 1 := by
    have h1 := he.1 k
    rw [hea, norm_smul, hta, RCLike.norm_ofReal, abs_of_pos htpos] at h1
    exact h1
  have htf : t = ‖f‖⁻¹ := eq_inv_of_mul_eq_one_left hnorm
  rw [hea, hta, htf, InnerProductSpace.gramSchmidtNormed, RCLike.ofReal_inv]

section Riesz6B
open MeasureTheory

theorem legendreBasis01_eval_zero (x : ℝ) : (legendreBasis01 0 : Polynomial ℝ).eval x = 1 := by
  simp [legendreBasis01, legendrePoly01]

theorem legendreBasis01_eval_one (x : ℝ) :
    (legendreBasis01 1 : Polynomial ℝ).eval x = √12 * (x - 1 / 2) := by
  simp [legendreBasis01, legendrePoly01]

theorem legendreBasis01_eval_two (x : ℝ) :
    (legendreBasis01 2 : Polynomial ℝ).eval x = √180 * (x ^ 2 - x + 1 / 6) := by
  simp [legendreBasis01, legendrePoly01]

/-- The formula from the proof of the Riesz representation theorem (6.42) on {lit}`𝒫₂(ℝ)` with
{lit}`⟨p, q⟩ = ∫₀¹ pq`: every linear functional {lit}`φ` is {lit}`⟨·, q⟩` for
{lit}`q = ∑ⱼ φ(eⱼ) eⱼ`, where {lit}`eⱼ` is the orthonormal basis of 6B.8. We cannot apply
{name}`riesz_representation` directly: it needs an inner product instance on
{lit}`𝒫₂(ℝ)`, and it only asserts that some {lit}`q` exists. -/
theorem riesz_P2 (φ : Polynomial.degreeLT ℝ 3 →ₗ[ℝ] ℝ) (p : Polynomial.degreeLT ℝ 3) :
    φ p = ∫ x in (0:ℝ)..1, (p : Polynomial ℝ).eval x *
      ∑ j, φ (legendreBasis01 j) * (legendreBasis01 j : Polynomial ℝ).eval x := by
  -- on a basis vector, orthonormality leaves only the `i`-th term
  have key : ∀ i, φ (legendreBasis01 i) = ∫ x in (0:ℝ)..1,
      (legendreBasis01 i : Polynomial ℝ).eval x *
        ∑ j, φ (legendreBasis01 j) * (legendreBasis01 j : Polynomial ℝ).eval x := by
    intro i
    have hexp : ∀ x : ℝ, (legendreBasis01 i : Polynomial ℝ).eval x *
        ∑ j, φ (legendreBasis01 j) * (legendreBasis01 j : Polynomial ℝ).eval x =
        ∑ j, φ (legendreBasis01 j) * ((legendreBasis01 i : Polynomial ℝ).eval x *
          (legendreBasis01 j : Polynomial ℝ).eval x) := by
      intro x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum fun j _ => by
      apply Continuous.intervalIntegrable; fun_prop]
    simp_rw [intervalIntegral.integral_const_mul, exercise_6B_8a.1]
    simp
  -- expand `p` in the basis and use linearity of both sides
  obtain ⟨c, rfl⟩ : ∃ c : Fin 3 → ℝ, p = ∑ i, c i • legendreBasis01 i := by
    refine ⟨fun i => legendreBasis01_isBasis.toModuleBasis.repr p i, ?_⟩
    have h := legendreBasis01_isBasis.toModuleBasis.sum_repr p
    simp only [LADR.Section_2B.IsBasis.toModuleBasis_apply] at h
    exact h.symm
  have hev : ∀ x : ℝ, ((∑ i, c i • legendreBasis01 i : Polynomial.degreeLT ℝ 3) :
      Polynomial ℝ).eval x = ∑ i, c i * (legendreBasis01 i : Polynomial ℝ).eval x := by
    intro x
    simp [Polynomial.eval_finsetSum]
  simp_rw [hev, Finset.sum_mul, mul_assoc]
  rw [map_sum, intervalIntegral.integral_finsetSum fun i _ => by
    apply Continuous.intervalIntegrable; fun_prop]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, intervalIntegral.integral_const_mul, ← key]

/-- The quadratic {lit}`a + bx + cx²` as an element of {lit}`𝒫₂(ℝ)`. -/
noncomputable def quad6B (a b c : ℝ) : Polynomial.degreeLT ℝ 3 := by
  refine ⟨Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2, ?_⟩
  refine Polynomial.mem_degreeLT.mpr (Polynomial.degree_le_natDegree.trans_lt ?_)
  exact_mod_cast Nat.lt_succ_of_le (by compute_degree!)

theorem quad6B_eval (a b c x : ℝ) :
    (quad6B a b c : Polynomial ℝ).eval x = a + b * x + c * x ^ 2 := by
  simp [quad6B]

/-- The functional {lit}`φ(p) = p(½)` of 6B.11. -/
noncomputable def evalHalf : Polynomial.degreeLT ℝ 3 →ₗ[ℝ] ℝ where
  toFun p := (p : Polynomial ℝ).eval (1 / 2)
  map_add' p q := by simp
  map_smul' c p := by simp

/-- The quadratic {lit}`q ∈ 𝒫₂(ℝ)` to find in 6B.11 (Riesz vector representing point
evaluation {lit}`p ↦ p(½)` for {lit}`⟨p, q⟩ = ∫₀¹ pq`). -/
noncomputable def q6B11 : Polynomial.degreeLT ℝ 3 := by
  -- φ(p) = ⟨p, q⟩, where q = φ(ei) ei for an orthonormal basis {ei} of 𝒫₂(ℝ)
  -- we know the basis is:
  -- v0 = 1
  -- v1 = √12 (x - 1/2)
  -- v2 = (√180) (x² - x + 1/6)
  -- so eval at 1/2 is equivalent to ⟨p, q⟩ for q = 1 - 15 (x² - x + 1/6)
  refine ⟨Polynomial.C 1 - Polynomial.C 15 *
    (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (1 / 6)), ?_⟩
  refine Polynomial.mem_degreeLT.mpr (Polynomial.degree_le_natDegree.trans_lt ?_)
  exact_mod_cast Nat.lt_succ_of_le (by compute_degree!)

/-- 6B.11 The polynomial {name}`q6B11` satisfies {lit}`p(½) = ∫₀¹ pq` for every
{lit}`p ∈ 𝒫₂(ℝ)` (written {lit}`p = a + bx + cx²`). (Analytic function-space exercise, stated
as an integral identity.) -/
theorem exercise_6B_11 : ∀ a b c : ℝ,
    (a + b * (1 / 2) + c * (1 / 2) ^ 2)
      = ∫ x in (0:ℝ)..1, (a + b * x + c * x ^ 2) * (q6B11 : Polynomial ℝ).eval x := by
  -- by Riesz, `q = ∑ⱼ φ(eⱼ) eⱼ`, with `φ(e₀) = 1`, `φ(e₁) = 0`, `φ(e₂) = -√180/12`
  intro a b c
  have h0 : evalHalf (legendreBasis01 0) = 1 := legendreBasis01_eval_zero _
  have h1 : evalHalf (legendreBasis01 1) = 0 := by
    show (legendreBasis01 1 : Polynomial ℝ).eval (1 / 2) = 0
    rw [legendreBasis01_eval_one]
    ring
  have h2 : evalHalf (legendreBasis01 2) = -√180 / 12 := by
    show (legendreBasis01 2 : Polynomial ℝ).eval (1 / 2) = -√180 / 12
    rw [legendreBasis01_eval_two]
    ring
  have hq : ∀ x : ℝ, ∑ j, evalHalf (legendreBasis01 j) * (legendreBasis01 j : Polynomial ℝ).eval x
      = (q6B11 : Polynomial ℝ).eval x := by
    intro x
    have hs : √180 * √180 = 180 := Real.mul_self_sqrt (by norm_num)
    have hev : (q6B11 : Polynomial ℝ).eval x = 1 - 15 * (x ^ 2 - x + 1 / 6) := by
      simp [q6B11]
    rw [Fin.sum_univ_three, h0, h1, h2, legendreBasis01_eval_zero, legendreBasis01_eval_one,
      legendreBasis01_eval_two, hev]
    linear_combination (-(x ^ 2 - x + 1 / 6) / 12) * hs
  have hφ := riesz_P2 evalHalf (quad6B a b c)
  simp_rw [hq, quad6B_eval] at hφ
  rw [← hφ]
  exact (quad6B_eval a b c (1 / 2)).symm

/-- {lit}`∫₀¹ (a + bx + cx²) cos(πx) dx = -2(b + c)/π²`, integrating by parts as in 6.44. -/
theorem integral01_quad_mul_cos_pi (a b c : ℝ) :
    (∫ x in (0:ℝ)..1, (a + b * x + c * x ^ 2) * Real.cos (Real.pi * x))
      = -2 * (b + c) / Real.pi ^ 2 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  set F : ℝ → ℝ := fun t => a * (Real.sin (Real.pi * t) / Real.pi)
    + b * (t / Real.pi * Real.sin (Real.pi * t) + 1 / Real.pi ^ 2 * Real.cos (Real.pi * t))
    + c * (t ^ 2 / Real.pi * Real.sin (Real.pi * t)
      + 2 * t / Real.pi ^ 2 * Real.cos (Real.pi * t)
      + -(2 / Real.pi ^ 3) * Real.sin (Real.pi * t)) with hF
  have hderiv : ∀ t : ℝ, HasDerivAt F ((a + b * t + c * t ^ 2) * Real.cos (Real.pi * t)) t := by
    intro t
    have hlin : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
      simpa using (hasDerivAt_id t).const_mul Real.pi
    have hsin := (Real.hasDerivAt_sin (Real.pi * t)).comp t hlin
    have hcos := (Real.hasDerivAt_cos (Real.pi * t)).comp t hlin
    have e0 := hsin.div_const Real.pi
    have e1 := ((hasDerivAt_id t).div_const Real.pi).mul hsin
    have e2 := (hasDerivAt_const t (1 / Real.pi ^ 2)).mul hcos
    have e3 := ((hasDerivAt_pow 2 t).div_const Real.pi).mul hsin
    have e4 := (((hasDerivAt_id t).const_mul 2).div_const (Real.pi ^ 2)).mul hcos
    have e5 := (hasDerivAt_const t (-(2 / Real.pi ^ 3))).mul hsin
    have hsum := ((e0.const_mul a).add ((e1.add e2).const_mul b)).add
      (((e3.add e4).add e5).const_mul c)
    refine hsum.congr_deriv ?_
    simp only [Function.comp_apply, id_eq]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [hF, mul_one, mul_zero, Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero]
  field_simp
  ring

/-- The functional {lit}`φ(p) = ∫₀¹ p(x)cos(πx) dx` of 6B.12. -/
noncomputable def integralCosPi : Polynomial.degreeLT ℝ 3 →ₗ[ℝ] ℝ where
  toFun p := ∫ x in (0:ℝ)..1, (p : Polynomial ℝ).eval x * Real.cos (Real.pi * x)
  map_add' p q := by
    simp only [Submodule.coe_add, Polynomial.eval_add, add_mul]
    exact intervalIntegral.integral_add
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
  map_smul' c p := by
    simp only [Submodule.coe_smul, Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact intervalIntegral.integral_const_mul _ _

/-- The quadratic {lit}`q ∈ 𝒫₂(ℝ)` to find in 6B.12 (the analogue of 6.44 on
{lit}`[0, 1]`, representing {lit}`p ↦ ∫₀¹ p(x)cos(πx) dx`). -/
noncomputable def q6B12 : Polynomial.degreeLT ℝ 3 := by
  -- again using the basis of 𝒫₂(ℝ) and solving for the coefficients
  -- φ(p) = ∫₀¹ p(x) cos(πx) dx = (∫₀¹ p0 cos(πx) dx)p0 + (∫₀¹ p1 cos(πx) dx)p1 + (∫₀¹ p2 cos(πx) dx)p2
  -- where p0, p1, p2 are the orthonormal basis
  -- 1, √12 (x - 1/2), √180 (x^2 - x + 1/6)
  -- = -24/π² (x - 1/2)
  refine ⟨Polynomial.C (-(24 / Real.pi ^ 2)) * (Polynomial.X - Polynomial.C (1 / 2)), ?_⟩
  refine Polynomial.mem_degreeLT.mpr (Polynomial.degree_le_natDegree.trans_lt ?_)
  exact_mod_cast Nat.lt_succ_of_le (by compute_degree!)

/-- 6B.12 The polynomial {name}`q6B12` satisfies {lit}`∫₀¹ p(x)cos(πx) dx = ∫₀¹ pq`
for every {lit}`p ∈ 𝒫₂(ℝ)` (written {lit}`p = a + bx + cx²`). The answer must lie in
{lit}`𝒫₂(ℝ)`; otherwise {lit}`q(x) = cos(πx)` would trivially work. (Analytic
function-space exercise, stated as an integral identity.) -/
theorem exercise_6B_12 : ∀ a b c : ℝ,
    (∫ x in (0:ℝ)..1, (a + b * x + c * x ^ 2) * Real.cos (Real.pi * x))
      = ∫ x in (0:ℝ)..1, (a + b * x + c * x ^ 2) * (q6B12 : Polynomial ℝ).eval x := by
  -- by Riesz, `q = ∑ⱼ φ(eⱼ) eⱼ`, with `φ(e₀) = 0`, `φ(e₁) = -2√12/π²`, `φ(e₂) = 0`
  intro a b c
  have hφq : ∀ (p : Polynomial.degreeLT ℝ 3) (A B C : ℝ),
      (∀ x : ℝ, (p : Polynomial ℝ).eval x = A + B * x + C * x ^ 2) →
      integralCosPi p = -2 * (B + C) / Real.pi ^ 2 := by
    intro p A B C h
    show (∫ x in (0:ℝ)..1, (p : Polynomial ℝ).eval x * Real.cos (Real.pi * x)) = _
    simp_rw [h]
    exact integral01_quad_mul_cos_pi A B C
  have h0 : integralCosPi (legendreBasis01 0) = 0 := by
    rw [hφq _ 1 0 0 fun x => by rw [legendreBasis01_eval_zero]; ring]
    ring
  have h1 : integralCosPi (legendreBasis01 1) = -2 * √12 / Real.pi ^ 2 := by
    rw [hφq _ (-√12 / 2) √12 0 fun x => by rw [legendreBasis01_eval_one]; ring]
    ring
  have h2 : integralCosPi (legendreBasis01 2) = 0 := by
    rw [hφq _ (√180 / 6) (-√180) √180 fun x => by rw [legendreBasis01_eval_two]; ring]
    ring
  have hq : ∀ x : ℝ,
      ∑ j, integralCosPi (legendreBasis01 j) * (legendreBasis01 j : Polynomial ℝ).eval x
        = (q6B12 : Polynomial ℝ).eval x := by
    intro x
    have hs : √12 * √12 = 12 := Real.mul_self_sqrt (by norm_num)
    have hev : (q6B12 : Polynomial ℝ).eval x = -(24 / Real.pi ^ 2) * (x - 1 / 2) := by
      simp [q6B12]
    rw [Fin.sum_univ_three, h0, h1, h2, legendreBasis01_eval_one, hev]
    linear_combination (-2 / Real.pi ^ 2 * (x - 1 / 2)) * hs
  have hφ := riesz_P2 integralCosPi (quad6B a b c)
  simp_rw [hq, quad6B_eval] at hφ
  rw [← hφ]
  show _ = ∫ x in (0:ℝ)..1, (quad6B a b c : Polynomial ℝ).eval x * Real.cos (Real.pi * x)
  simp_rw [quad6B_eval]

end Riesz6B

/-- 6B.13 A list {lit}`v₁, …, vₘ` is linearly dependent iff Gram–Schmidt produces
{lit}`fₖ = 0` for some {lit}`k`. -/
theorem exercise_6B_13 {m : ℕ} (v : Fin m → V) :
    ¬ LinearIndependent 𝕜 v ↔ ∃ k, InnerProductSpace.gramSchmidt 𝕜 v k = 0 := by
  -- <= trivial the equation f k = 0 is a linear dependence relation
  -- => ∑ ai vi = 0 for some nontrivial coefficients ai
  -- take the biggest k for which ak ≠ 0
  -- so vk is a linear combination of the previous f's
  -- fk = vk - ∑ ⟨vk, fi⟩/‖fi‖² fi, so fk is also in span(f₁, …, fₖ₋₁)
  -- but fk is orthogonal to span(f₁, …, fₖ₋₁), so it is orthogonal to itself
  -- so fk = 0, which is what we wanted to show
  constructor
  · intro h
    obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp h
    -- the biggest `k` with `g k ≠ 0`
    set s := Finset.univ.filter fun i => g i ≠ 0 with hs
    have hne : s.Nonempty := ⟨i₀, by simp [hs, hi₀]⟩
    set k := s.max' hne with hkdef
    have hk : g k ≠ 0 := (Finset.mem_filter.mp (s.max'_mem hne)).2
    have hgt : ∀ i, k < i → g i = 0 := by
      intro i hi
      by_contra hgi
      exact absurd (s.le_max' i (by simp [hs, hgi])) (not_le.mpr hi)
    refine ⟨k, ?_⟩
    set W := Submodule.span 𝕜 (InnerProductSpace.gramSchmidt 𝕜 v '' Set.Iio k) with hW
    have hv : ∀ i, i < k → v i ∈ W := fun i hi =>
      Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.mpr hi))
        (mem_span_gramSchmidt_of_le v le_rfl)
    -- `vₖ` is a combination of the earlier `vᵢ`, so it lies in `span(f₁, …, fₖ₋₁)`
    have hvk : v k ∈ W := by
      have hsplit : g k • v k = -∑ i ∈ Finset.univ.erase k, g i • v i :=
        eq_neg_of_add_eq_zero_left
          ((Finset.add_sum_erase _ (fun i => g i • v i) (Finset.mem_univ k)).trans hg)
      rw [← inv_smul_smul₀ hk (v k), hsplit]
      refine Submodule.smul_mem _ _ (neg_mem (Submodule.sum_mem _ fun i hi => ?_))
      rcases (Finset.ne_of_mem_erase hi).lt_or_gt with hlt | hgt'
      · exact Submodule.smul_mem _ _ (hv i hlt)
      · rw [hgt i hgt', zero_smul]
        exact zero_mem _
    -- so `fₖ = vₖ - ∑ (multiples of earlier fᵢ)` lies in that span too
    have hfW : InnerProductSpace.gramSchmidt 𝕜 v k ∈ W := by
      rw [InnerProductSpace.gramSchmidt_def 𝕜 v k]
      refine sub_mem hvk (Submodule.sum_mem _ fun j hj => ?_)
      rw [Submodule.starProjection_singleton]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, Finset.mem_Iio.mp hj, rfl⟩)
    -- but `fₖ` is orthogonal to that span, hence to itself
    have hperp : ∀ x ∈ W, ⟪x, InnerProductSpace.gramSchmidt 𝕜 v k⟫_𝕜 = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        exact gramSchmidt_orthogonal_of_lt v hi
      | zero => simp
      | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
      | smul c _ _ h => rw [inner_smul_left, h, mul_zero]
    exact inner_self_eq_zero.mp (hperp _ hfW)
  · rintro ⟨k, hk⟩ hli
    exact gramSchmidt_ne_zero_of_linearIndependent hli k hk

/-- 6B.14 In a *real* inner product space, a linearly independent list
{lit}`v₁, …, vₘ` admits exactly {lit}`2ᵐ` orthonormal lists {lit}`e₁, …, eₘ` with
{lit}`span(v₁, …, vₖ) = span(e₁, …, eₖ)` for all {lit}`k` (the sign choices at each
Gram–Schmidt step). -/
theorem exercise_6B_14 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (v : Fin m → V) (hv : LinearIndependent ℝ v) :
    {e : Fin m → V | Orthonormal ℝ e ∧
      ∀ k, Submodule.span ℝ (v '' {i | i ≤ k}) =
        Submodule.span ℝ (e '' {i | i ≤ k})}.ncard = 2 ^ m := by
  -- variation on the proof for ex10.
  -- again induction, in the last step we obtain |am| = 1
  -- and since real space, and not given > 0, the are two choice + and -1
  -- so the lists are exactly ±e₁, …, ±eₘ for the Gram-Schmidt eᵢ, one for each choice of signs
  set G := InnerProductSpace.gramSchmidtNormed ℝ v with hG
  have hGo : Orthonormal ℝ G := gram_schmidt_orthonormal hv
  obtain ⟨sgn, hsT, hsF⟩ : ∃ sgn : Bool → ℝ, sgn true = 1 ∧ sgn false = -1 :=
    ⟨fun b => if b then 1 else -1, by simp⟩
  have hsq : ∀ b, sgn b * sgn b = 1 := by
    intro b
    cases b <;> simp [hsT, hsF]
  have habs : ∀ b, |sgn b| = 1 := by
    intro b
    cases b <;> simp [hsT, hsF]
  have hsinj : Function.Injective sgn := by
    intro x y h
    cases x <;> cases y <;> first
      | rfl
      | (exfalso; rw [hsT, hsF] at h; norm_num at h)
  set F : (Fin m → Bool) → Fin m → V := fun σ k => sgn (σ k) • G k with hF
  have hFinj : Function.Injective F := by
    intro σ τ h
    funext k
    exact hsinj (smul_left_injective ℝ (hGo.ne_zero k) (congrFun h k))
  -- every choice of signs gives such a list
  have hmem : ∀ σ, Orthonormal ℝ (F σ) ∧ ∀ k, Submodule.span ℝ (v '' {i | i ≤ k}) =
      Submodule.span ℝ (F σ '' {i | i ≤ k}) := by
    intro σ
    refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, fun k => ?_⟩
    · show ‖sgn (σ i) • G i‖ = 1
      rw [norm_smul, hGo.1 i, mul_one, Real.norm_eq_abs, habs]
    · show ⟪sgn (σ i) • G i, sgn (σ j) • G j⟫_ℝ = 0
      rw [real_inner_smul_left, real_inner_smul_right, hGo.2 hij, mul_zero, mul_zero]
    · have h : Submodule.span ℝ (v '' {i | i ≤ k}) = Submodule.span ℝ (G '' {i | i ≤ k}) :=
        (span_gramSchmidtNormed_initial (𝕜 := ℝ) v k).symm
      rw [h]
      apply le_antisymm <;> rw [Submodule.span_le] <;> rintro _ ⟨i, hi, rfl⟩
      · have hGi : G i = sgn (σ i) • F σ i := by
          simp only [hF, smul_smul, hsq, one_smul]
        rw [SetLike.mem_coe, hGi]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  -- every such list comes from a choice of signs, by induction
  have hsurj : ∀ e : Fin m → V, Orthonormal ℝ e → (∀ k, Submodule.span ℝ (v '' {i | i ≤ k}) =
      Submodule.span ℝ (e '' {i | i ≤ k})) → ∃ σ, F σ = e := by
    intro e he hspan
    have key : ∀ k, ∃ b, e k = sgn b • G k := by
      intro k
      induction k using WellFoundedLT.induction with | ind k ih
      set f := InnerProductSpace.gramSchmidt ℝ v k with hf
      have hf0 : f ≠ 0 := gramSchmidt_ne_zero_of_linearIndependent hv k
      obtain ⟨a, ha⟩ : ∃ a : ℝ, e k = a • f :=
        exists_eq_smul_gramSchmidt v e (fun k => (hspan k).symm) k
          (fun i hi => by
            obtain ⟨b, hb⟩ := ih i hi
            rw [hb, real_inner_smul_left, hG, InnerProductSpace.gramSchmidtNormed,
              real_inner_smul_left, gramSchmidt_orthogonal_of_lt v hi, mul_zero, mul_zero])
          (fun i hi => he.2 hi.ne)
      have hnf : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf0
      -- `‖eₖ‖ = 1` gives `|a| ‖fₖ‖ = 1`, which leaves two signs
      have hnorm : |a * ‖f‖| = 1 := by
        have h := he.1 k
        rw [ha, norm_smul, Real.norm_eq_abs] at h
        rw [abs_mul, abs_norm, h]
      have hGk : G k = ‖f‖⁻¹ • f := rfl
      have hak : e k = (a * ‖f‖) • G k := by
        rw [ha, hGk, smul_smul, mul_assoc, mul_inv_cancel₀ hnf, mul_one]
      rcases eq_or_eq_neg_of_abs_eq hnorm with h | h
      · exact ⟨true, by rw [hsT, ← h]; exact hak⟩
      · exact ⟨false, by rw [hsF, ← h]; exact hak⟩
    choose σ hσ using key
    exact ⟨σ, funext fun k => (hσ k).symm⟩
  have hS : {e : Fin m → V | Orthonormal ℝ e ∧
      ∀ k, Submodule.span ℝ (v '' {i | i ≤ k}) =
        Submodule.span ℝ (e '' {i | i ≤ k})} = Set.range F := by
    ext e
    constructor
    · rintro ⟨he, hspan⟩
      exact hsurj e he hspan
    · rintro ⟨σ, rfl⟩
      exact hmem σ
  rw [hS, ← Set.image_univ, Set.ncard_image_of_injective _ hFinj, Set.ncard_univ]
  simp [Nat.card_eq_fintype_card]

/-- 6B.15 If {lit}`⟨·, ·⟩₁` and {lit}`⟨·, ·⟩₂` are inner products with the same
orthogonal pairs, then one is a positive scalar multiple of the other. (Stated
for two inner-product structures {lit}`i₁, i₂` on the same space.) -/
theorem exercise_6B_15 {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    (i₁ i₂ : InnerProductSpace.Core 𝕜 V)
    (h : ∀ u w : V, i₁.inner u w = 0 ↔ i₂.inner u w = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ u w : V, i₁.inner u w = (c : 𝕜) * i₂.inner u w := by
  -- pick u and v non-zero and non-orthogonal vectors
  -- let w = v - ⟪v, u⟫₁ / ⟪u, u⟫₁ * u
  -- we know ⟪w, u⟫₁ = 0, thus ⟪w, u⟫₂ = 0 by the hypothesis
  -- so ⟪v, u⟫₂ - ⟪v, u⟫₁ * ‖u‖₂² / ‖u‖₁² = 0
  -- thus ⟪v, u⟫₂ / ⟪v, u⟫₁ = ‖u‖₂² / ‖u‖₁² = c_u
  -- note it is a positive real number
  -- but c_v = ⟪u, v⟫₂ / ⟪u, v⟫₁ = conj ⟪v, u⟫₂ / conj ⟪v, u⟫₁ = conj c_u
  -- but c_u is a positive real number, so conj c_u = c_u
  -- so c_u = c_v = c for all non-orthogonal u, v
  -- finally if u and v are orthogonal, pick a non-orthogonal w to both, e.g. w = u + v
  -- and use transitivity
  have hreal : ∀ (i : InnerProductSpace.Core 𝕜 V) (u : V),
      ((RCLike.re (i.inner u u) : ℝ) : 𝕜) = i.inner u u :=
    fun i u => RCLike.conj_eq_iff_re.mp (i.conj_inner_symm u u)
  have hpos : ∀ (i : InnerProductSpace.Core 𝕜 V) (u : V), u ≠ 0 → 0 < RCLike.re (i.inner u u) :=
    fun i u hu => lt_of_le_of_ne (i.re_inner_nonneg u) fun h0 => hu (i.definite u (by
      rw [← hreal i u, ← h0]
      simp))
  have hzl : ∀ (i : InnerProductSpace.Core 𝕜 V) (x : V), i.inner 0 x = 0 := by
    intro i x
    simpa using i.smul_left 0 x 0
  have hzr : ∀ (i : InnerProductSpace.Core 𝕜 V) (x : V), i.inner x 0 = 0 := by
    intro i x
    rw [← i.conj_inner_symm, hzl, map_zero]
  -- `c_u = ‖u‖₁² / ‖u‖₂²` (the statement has `⟨·, ·⟩₁ = c ⟨·, ·⟩₂`, the inverse of the sketch)
  obtain ⟨c, hc⟩ : ∃ c : V → ℝ, ∀ u, c u = RCLike.re (i₁.inner u u) / RCLike.re (i₂.inner u u) :=
    ⟨_, fun _ => rfl⟩
  have hcpos : ∀ u, u ≠ 0 → 0 < c u := fun u hu => by
    rw [hc]
    exact div_pos (hpos i₁ u hu) (hpos i₂ u hu)
  -- for `u ≠ 0`: `w = v - a u` with `a = ⟨v, u⟩₂ / ⟨u, u⟩₂` is `⟂₂ u`, hence `⟂₁ u`
  have hA : ∀ u, u ≠ 0 → ∀ v, i₁.inner v u = (c u : 𝕜) * i₂.inner v u := by
    intro u hu v
    have hu2 : i₂.inner u u ≠ 0 := fun h0 => hu (i₂.definite u h0)
    have hw2 : i₂.inner (v + (-(conj (i₂.inner v u / i₂.inner u u))) • u) u = 0 := by
      rw [i₂.add_left, i₂.smul_left, map_neg, RCLike.conj_conj, neg_mul,
        div_mul_cancel₀ _ hu2, add_neg_cancel]
    have hw1 := (h _ _).mpr hw2
    rw [i₁.add_left, i₁.smul_left, map_neg, RCLike.conj_conj, neg_mul,
      add_neg_eq_zero] at hw1
    rw [hw1, hc]
    push_cast
    rw [hreal i₁ u, hreal i₂ u]
    ring
  -- if `⟨v, u⟩₂ ≠ 0`, compare `⟨v, u⟩₁` with the conjugate of `⟨u, v⟩₁`
  have hcase : ∀ u v, u ≠ 0 → v ≠ 0 → i₂.inner v u ≠ 0 → c u = c v := by
    intro u v hu hv hvu
    have h1 := hA u hu v
    have h3 : i₁.inner v u = (c v : 𝕜) * i₂.inner v u := by
      rw [← i₁.conj_inner_symm, hA v hv u, map_mul, RCLike.conj_ofReal, i₂.conj_inner_symm]
    have h0 : ((c u : 𝕜) - c v) * i₂.inner v u = 0 := by
      rw [sub_mul, ← h1, ← h3, sub_self]
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact_mod_cast sub_eq_zero.mp h'
    · exact absurd h' hvu
  -- otherwise go through `u + v`
  have hconst : ∀ u v, u ≠ 0 → v ≠ 0 → c u = c v := by
    intro u v hu hv
    by_cases hvu : i₂.inner v u = 0
    · have huv : i₂.inner u v = 0 := by rw [← i₂.conj_inner_symm, hvu, map_zero]
      have hs : u + v ≠ 0 := by
        intro hs
        rw [eq_neg_of_add_eq_zero_right hs, ← neg_one_smul 𝕜 u, i₂.smul_left] at hvu
        exact hu (i₂.definite u (by simpa using hvu))
      have e1 : c u = c (u + v) := hcase u (u + v) hu hs (by
        rw [i₂.add_left, hvu, add_zero]
        exact fun h0 => hu (i₂.definite u h0))
      have e2 : c v = c (u + v) := hcase v (u + v) hv hs (by
        rw [i₂.add_left, huv, zero_add]
        exact fun h0 => hv (i₂.definite v h0))
      rw [e1, e2]
    · exact hcase u v hu hv hvu
  by_cases hex : ∃ u₀ : V, u₀ ≠ 0
  · obtain ⟨u₀, hu₀⟩ := hex
    refine ⟨c u₀, hcpos u₀ hu₀, fun u w => ?_⟩
    by_cases hw : w = 0
    · rw [hw, hzr, hzr, mul_zero]
    · rw [hA w hw u, hconst w u₀ hw hu₀]
  · push Not at hex
    refine ⟨1, one_pos, fun u w => ?_⟩
    rw [hex w, hzr, hzr, mul_zero]

/-- 6B.16 On a finite-dimensional space any two inner-product norms are equivalent:
there is {lit}`c > 0` with {lit}`‖v‖₁ ≤ c‖v‖₂` for all {lit}`v` (norms
{lit}`‖v‖ᵢ = √⟨v, v⟩ᵢ`). -/
theorem exercise_6B_16 {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module.Finite 𝕜 V]
    (i₁ i₂ : InnerProductSpace.Core 𝕜 V) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V,
      Real.sqrt (RCLike.re (i₁.inner v v)) ≤ c * Real.sqrt (RCLike.re (i₂.inner v v)) := by
  -- take an orthonormal basis e₁, …, eₙ with respect to ⟪,⟫₂ (Gram–Schmidt, 6.35)
  -- (there is no relation between the two inner products, so it need not be ⟪,⟫₁-orthogonal)
  -- then take v = ∑ aᵢ eᵢ, so ‖v‖₂² = ∑ |aᵢ|² = S (6.24)
  -- ‖v‖₁² = ∑ᵢ ∑ⱼ conj aᵢ aⱼ ⟪eᵢ, eⱼ⟫₁ (expanding by sesquilinearity)
  -- ≤ |∑ᵢ ∑ⱼ conj aᵢ aⱼ ⟪eᵢ, eⱼ⟫₁| (a real number is at most its absolute value)
  -- ≤ ∑ᵢ ∑ⱼ |aᵢ| |aⱼ| |⟪eᵢ, eⱼ⟫₁| (triangle inequality, |xyz| = |x||y||z|, |conj x| = |x|)
  -- ≤ S ∑ᵢ ∑ⱼ |⟪eᵢ, eⱼ⟫₁| = K S (each |aᵢ|² ≤ S, so |aᵢ| |aⱼ| ≤ √S · √S = S)
  -- where K = ∑ᵢ ∑ⱼ |⟪eᵢ, eⱼ⟫₁|
  -- so ‖v‖₁ ≤ √K ‖v‖₂, and c = √K + 1 > 0 works (the + 1 covers K = 0)
  -- sesquilinearity of ⟪,⟫₁, from the axioms of `InnerProductSpace.Core`
  have hzl : ∀ x : V, i₁.inner 0 x = 0 := fun x => by simpa using i₁.smul_left 0 x 0
  have hsumL : ∀ {ι : Type} (s : Finset ι) (f : ι → V) (y : V),
      i₁.inner (∑ k ∈ s, f k) y = ∑ k ∈ s, i₁.inner (f k) y := by
    intro ι s f y
    classical
    refine Finset.induction_on s (by simp [hzl]) ?_
    intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, i₁.add_left, ih]
  have hsumR : ∀ {ι : Type} (s : Finset ι) (f : ι → V) (y : V),
      i₁.inner y (∑ k ∈ s, f k) = ∑ k ∈ s, i₁.inner y (f k) := by
    intro ι s f y
    rw [← i₁.conj_inner_symm, hsumL, map_sum]
    exact Finset.sum_congr rfl fun k _ => i₁.conj_inner_symm _ _
  have hsmulR : ∀ (x y : V) (r : 𝕜), i₁.inner x (r • y) = r * i₁.inner x y := by
    intro x y r
    rw [← i₁.conj_inner_symm, i₁.smul_left, map_mul, RCLike.conj_conj, i₁.conj_inner_symm]
  -- make `⟪,⟫₂` the inner product of `V`, and take an orthonormal basis for it
  let : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 V _ _ _ i₂
  let : InnerProductSpace 𝕜 V := InnerProductSpace.ofCore i₂.toCore
  set b := stdOrthonormalBasis 𝕜 V
  set K := ∑ i, ∑ j, ‖i₁.inner (b i) (b j)‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hbound : ∀ v : V, RCLike.re (i₁.inner v v) ≤ K * RCLike.re (i₂.inner v v) := by
    intro v
    set a := b.repr v
    have hv : v = ∑ i, a i • b i := (b.sum_repr v).symm
    -- `‖v‖₂² = ∑ |aᵢ|²`
    have hS : RCLike.re (i₂.inner v v) = ∑ i, ‖a i‖ ^ 2 := by
      have h1 : ‖v‖ ^ 2 = RCLike.re (i₂.inner v v) := norm_sq_eq_re_inner (𝕜 := 𝕜) v
      rw [← h1, ← b.repr.norm_map v, EuclideanSpace.norm_sq_eq]
    rw [hS]
    set S := ∑ i, ‖a i‖ ^ 2
    have hab : ∀ i j, ‖a i‖ * ‖a j‖ ≤ S := by
      intro i j
      have hi : ‖a i‖ ^ 2 ≤ S := Finset.single_le_sum (f := fun k => ‖a k‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      have hj : ‖a j‖ ^ 2 ≤ S := Finset.single_le_sum (f := fun k => ‖a k‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      nlinarith [norm_nonneg (a i), norm_nonneg (a j), sq_nonneg (‖a i‖ - ‖a j‖)]
    -- expand `‖v‖₁²` in the basis
    have hexp : i₁.inner v v = ∑ i, ∑ j, conj (a i) * a j * i₁.inner (b i) (b j) := by
      conv_lhs => rw [hv]
      rw [hsumL]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [i₁.smul_left, hsumR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hsmulR]
      ring
    rw [hexp]
    calc RCLike.re (∑ i, ∑ j, conj (a i) * a j * i₁.inner (b i) (b j))
        ≤ ‖∑ i, ∑ j, conj (a i) * a j * i₁.inner (b i) (b j)‖ := RCLike.re_le_norm _
      _ ≤ ∑ i, ‖∑ j, conj (a i) * a j * i₁.inner (b i) (b j)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖conj (a i) * a j * i₁.inner (b i) (b j)‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ = ∑ i, ∑ j, ‖a i‖ * ‖a j‖ * ‖i₁.inner (b i) (b j)‖ := by
          simp_rw [norm_mul, RCLike.norm_conj]
      _ ≤ ∑ i, ∑ j, S * ‖i₁.inner (b i) (b j)‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (hab i j) (norm_nonneg _)
      _ = K * S := by
          rw [hK, mul_comm, Finset.mul_sum]
          simp_rw [Finset.mul_sum]
  refine ⟨√K + 1, by positivity, fun v => ?_⟩
  calc √(RCLike.re (i₁.inner v v)) ≤ √(K * RCLike.re (i₂.inner v v)) :=
        Real.sqrt_le_sqrt (hbound v)
    _ = √K * √(RCLike.re (i₂.inner v v)) := Real.sqrt_mul hK0 _
    _ ≤ (√K + 1) * √(RCLike.re (i₂.inner v v)) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)

/-- 6B.17 Over {lit}`ℂ`, if {lit}`1` is the only eigenvalue of {lit}`T` and
{lit}`‖Tv‖ ≤ ‖v‖` for all {lit}`v`, then {lit}`T` is the identity operator. -/
theorem exercise_6B_17 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V)
    (h1 : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → μ = 1)
    (h2 : ∀ v : V, ‖T v‖ ≤ ‖v‖) :
    T = LinearMap.id := by
  -- by theorem exists orthonomal basis s.t. T has an upper triagular matrix
  -- by eigenvalues =1 -> diagonals are 1 too
  -- take v = ei, ‖T ei‖ = ‖column i of the upper triangular matrix‖ ≤ ‖ei‖ = 1 (by 6.24)
  -- 1 + squares || of column i non-diag entries ≤ 1, thus those etries are 0 for all i
  -- thus T is the identity operator, since diag matrix with basis ei, with 1 on the diag.
  obtain ⟨n, e, he, hA⟩ := exists_orthonormal_upperTriangular_complex T
  set A := LADR.Section_3C.matrixOf he he T with hAdef
  -- the diagonal entries are eigenvalues (5.41), so they are all 1
  have hdiag : ∀ k, A k k = 1 := fun k =>
    h1 _ ((LADR.Section_5C.isEigenvalue_iff_diag he T hA _).mpr ⟨k, rfl⟩)
  -- column `k`: `‖T eₖ‖² = ∑ⱼ |Aⱼₖ|² ≤ ‖eₖ‖² = 1`
  have hcol : ∀ k, ∑ j, ‖A j k‖ ^ 2 ≤ 1 := by
    intro k
    have hk := h2 (e k)
    rw [LADR.Section_3C.matrixOf_spec he he T k, e.orthonormal.1 k] at hk
    rw [← norm_sq_sum_orthonormal e.orthonormal (fun j => A j k)]
    exact pow_le_one₀ (norm_nonneg _) hk
  -- the diagonal term already contributes 1, so the off-diagonal entries vanish
  have hoff : ∀ j k, j ≠ k → A j k = 0 := by
    intro j k hjk
    have hk := hcol k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hdiag k, norm_one, one_pow] at hk
    have hsum0 : ∑ i ∈ Finset.univ.erase k, ‖A i k‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum0 j
      (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩)
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hj)
  -- so `T eₖ = eₖ` for each basis vector
  have hTe : ∀ k, T (e k) = e k := by
    intro k
    rw [LADR.Section_3C.matrixOf_spec he he T k,
      Finset.sum_eq_single k (fun j _ hj => by rw [← hAdef, hoff j k hj, zero_smul])
        (by simp), ← hAdef, hdiag k, one_smul]
  exact he.toModuleBasis.ext fun k => by
    rw [LADR.Section_2B.IsBasis.toModuleBasis_apply, hTe, LinearMap.id_apply]

/-- 6B.18 helper: for linearly independent {lit}`u₁, …, uₘ`, the map
{lit}`φ(w) = (⟨u₁, w⟩, …, ⟨uₘ, w⟩)` on {lit}`span(u₁, …, uₘ)` is surjective, so
every {lit}`c ∈ 𝕜ᵐ` is {lit}`(⟨u₁, v⟩, …, ⟨uₘ, v⟩)` for some {lit}`v`. -/
theorem exists_inner_eq_of_linearIndependent {m : ℕ} (u : Fin m → V)
    (hu : LinearIndependent 𝕜 u) (c : Fin m → 𝕜) :
    ∃ v : V, ∀ k, ⟪u k, v⟫_𝕜 = c k := by
  set U := Submodule.span 𝕜 (Set.range u) with hU
  let φ : U →ₗ[𝕜] (Fin m → 𝕜) := LinearMap.pi fun k => (innerₛₗ 𝕜 (u k)).comp U.subtype
  have hφ : ∀ w k, φ w k = ⟪u k, (w : V)⟫_𝕜 := fun _ _ => rfl
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : ∀ k, ⟪u k, (w : V)⟫_𝕜 = 0 := fun k => by rw [← hφ, hw]; rfl
    -- by linearity, ⟪x, w⟫ = 0 for every x ∈ U
    have hall : ∀ x ∈ U, ⟪x, (w : V)⟫_𝕜 = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h0 k
      | zero => exact inner_zero_left _
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
    -- in particular for x = w, so w = 0
    exact Subtype.ext (inner_self_eq_zero.mp (hall w w.2))
  have hdim : Module.finrank 𝕜 U = Module.finrank 𝕜 (Fin m → 𝕜) := by
    rw [finrank_span_eq_card hu, Module.finrank_fin_fun, Fintype.card_fin]
  have : FiniteDimensional 𝕜 U := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range u)
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  obtain ⟨w, hw⟩ := hsurj c
  exact ⟨w, fun k => by rw [← hφ, hw]⟩

/-- 6B.18 If {lit}`u₁, …, uₘ` is linearly independent, there exists {lit}`v` with
{lit}`⟨uₖ, v⟩ = 1` for all {lit}`k`. -/
theorem exercise_6B_18 {m : ℕ} (u : Fin m → V) (hu : LinearIndependent 𝕜 u) :
    ∃ v : V, ∀ k, ⟪u k, v⟫_𝕜 = 1 := by
  -- consider U span by u, by lin ind it is of dim m
  -- let φ : U → k^n by v → (⟪u 0, v⟫, …, ⟪u (n-1), v⟫)
  -- φ is linear map between fin dim spaces, if surjective we are done
  -- since 1 has a preimage, but that is same as showing injective
  -- assume ⟨u i, v⟩ = 0, but then by linearity ⟨u, v⟩ = 0 for all u, including v
  -- thus ‖v‖ = 0, so v = 0, showing injectivity of φ.
  exact exists_inner_eq_of_linearIndependent u hu fun _ => 1

/-- 6B.19 If {lit}`v₁, …, vₙ` is a basis of {lit}`V`, there is a basis
{lit}`u₁, …, uₙ` with {lit}`⟨vⱼ, uₖ⟩ = δⱼₖ` (a dual/biorthogonal basis). -/
theorem exercise_6B_19 [FiniteDimensional 𝕜 V] {n : ℕ}
    (v : Module.Basis (Fin n) 𝕜 V) :
    ∃ u : Module.Basis (Fin n) 𝕜 V, ∀ j k, ⟪v j, u k⟫_𝕜 = if j = k then 1 else 0 := by
  -- using same proof as 18, we can find preimages under φ for all eᵢ
  -- which give the desired ui, the only thing left to show is that they are basis
  -- it is enough to show that they are LI, since they have the right dimension - equaling the other basis
  -- assume ∑ aᵢ uᵢ = 0, take ⟪vⱼ, _⟫ of both sides to get aⱼ = 0 for all j.
  choose w hw using fun k =>
    exists_inner_eq_of_linearIndependent v v.linearIndependent (Pi.single k 1)
  have hδ : ∀ j k, ⟪v j, w k⟫_𝕜 = if j = k then 1 else 0 := fun j k => by
    rw [hw k j, Pi.single_apply]
  have hli : LinearIndependent 𝕜 w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha j
    have h := congrArg (fun x => ⟪v j, x⟫_𝕜) ha
    simp only [inner_sum, inner_smul_right, hδ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, inner_zero_right] at h
    exact h
  have hcard : Fintype.card (Fin n) = Module.finrank 𝕜 V := by
    rw [Module.finrank_eq_card_basis v]
  refine ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge,
    fun j k => ?_⟩
  rw [Module.Basis.mk_apply, hδ]

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
  -- this is just the result from 5E and then using Gram-Schmidt to
  -- orthonormalize the basis obtained from 5E using Gram-Schmidt
  -- this preserves upper-triangular form as shown in the Gram-Schmidt section of the notes
  obtain ⟨n, v, hv, hA⟩ := LADR.Section_5E.exercise_5E_9b ℰ hcomm
  obtain ⟨e, he, hT⟩ := exists_orthonormal_upperTriangular_of_basis hv
  exact ⟨n, e, he, fun T hTℰ => hT T (hA T hTℰ)⟩

end UpperTri6B20

/-- 6B.21 helper (the recursion lemma): if {lit}`aₘ₊₁ ≤ r aₘ + bₘ` with
{lit}`0 ≤ r < 1`, {lit}`aₘ ≥ 0` and {lit}`bₘ → 0`, then {lit}`aₘ → 0`.
From some {lit}`N` on {lit}`bₘ ≤ δ`, and unrolling gives
{lit}`a_{N+k} ≤ rᵏ a_N + δ / (1 - r)`. -/
theorem tendsto_zero_of_le_mul_add {a b : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ha : ∀ M, 0 ≤ a M) (hb : Filter.Tendsto b Filter.atTop (nhds 0))
    (hrec : ∀ M, a (M + 1) ≤ r * a M + b M) :
    Filter.Tendsto a Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1r : 0 < 1 - r := by linarith
  set δ := ε * (1 - r) / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hδr : δ / (1 - r) = ε / 2 := by rw [hδ]; field_simp
  -- from some N on, bₘ ≤ δ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hb δ hδpos
  have hbN : ∀ M ≥ N, b M ≤ δ := fun M hM => by
    have := hN M hM
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  -- unrolling: a (N + k) ≤ rᵏ a N + δ / (1 - r)
  have hunroll : ∀ k, a (N + k) ≤ r ^ k * a N + δ / (1 - r) := by
    intro k
    induction k with
    | zero => rw [add_zero, pow_zero, one_mul]; linarith [div_pos hδpos h1r]
    | succ k ih =>
      calc a (N + (k + 1)) = a (N + k + 1) := by rw [add_assoc]
        _ ≤ r * a (N + k) + b (N + k) := hrec _
        _ ≤ r * (r ^ k * a N + δ / (1 - r)) + δ :=
            add_le_add (mul_le_mul_of_nonneg_left ih hr0) (hbN _ (Nat.le_add_right _ _))
        _ = r ^ (k + 1) * a N + δ / (1 - r) := by field_simp; ring
  -- rᵏ a N → 0, so from some K on it is < ε / 2
  have hpow : Filter.Tendsto (fun k => r ^ k * a N) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (a N)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hpow.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N + K, fun M hM => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right N K) hM)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha _)]
  have := hK k (by omega)
  linarith [hunroll k]

/-- 6B.21 helper (the induction over columns): if {lit}`T eₖ - μₖ eₖ ∈ span(e_i : i < k)`
for each {lit}`k` (an upper-triangular flag) and every {lit}`|μₖ| < 1`, then
{lit}`Tᴹ eₖ → 0` for each {lit}`k`. Writing {lit}`T eₖ = μₖ eₖ + wₖ`,
{lit}`xᴹ = Tᴹ eₖ` satisfies {lit}`xᴹ⁺¹ = μₖ xᴹ + Tᴹ wₖ`, and {lit}`Tᴹ wₖ → 0` by induction. -/
theorem tendsto_pow_apply_of_flag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} (T : E →ₗ[ℂ] E) (e : Fin n → E) (μ : Fin n → ℂ) (hμ : ∀ k, ‖μ k‖ < 1)
    (hflag : ∀ k, T (e k) - μ k • e k ∈ Submodule.span ℂ (e '' {i | i < k})) (k : Fin n) :
    Filter.Tendsto (fun M : ℕ => (T ^ M) (e k)) Filter.atTop (nhds 0) := by
  induction k using WellFoundedLT.induction with | ind k ih
  -- by linearity, Tᴹ x → 0 for every x ∈ span(e_i : i < k)
  have hspan : ∀ x ∈ Submodule.span ℂ (e '' {i | i < k}),
      Filter.Tendsto (fun M : ℕ => (T ^ M) x) Filter.atTop (nhds 0) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact ih i hi
    | zero => simp
    | add x y _ _ hx hy => simpa using hx.add hy
    | smul c x _ hx => simpa using hx.const_smul c
  -- T eₖ = μₖ eₖ + w with Tᴹ w → 0
  set w := T (e k) - μ k • e k with hwdef
  have hw := hspan w (hflag k)
  have hTe : T (e k) = μ k • e k + w := by rw [hwdef, add_sub_cancel]
  -- xᴹ⁺¹ = μₖ xᴹ + Tᴹ w
  have hrec : ∀ M : ℕ, (T ^ (M + 1)) (e k) = μ k • (T ^ M) (e k) + (T ^ M) w := by
    intro M
    rw [pow_succ, Module.End.mul_apply, hTe, map_add, map_smul]
  -- so ‖xᴹ⁺¹‖ ≤ |μₖ| ‖xᴹ‖ + ‖Tᴹ w‖, and the recursion lemma applies
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_zero_of_le_mul_add (norm_nonneg _) (hμ k) (fun _ => norm_nonneg _)
    (tendsto_zero_iff_norm_tendsto_zero.mp hw) fun M => ?_
  rw [hrec M, ← norm_smul]
  exact norm_add_le _ _

/-- 6B.21 Over {lit}`ℂ`, if all eigenvalues of {lit}`T` have absolute value less
than 1, then for every {lit}`ε > 0` there is a positive integer {lit}`m` with
{lit}`‖Tᵐv‖ ≤ ε‖v‖` for all {lit}`v`. -/
theorem exercise_6B_21 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V)
    (h : ∀ μ : ℂ, Module.End.HasEigenvalue T μ → ‖μ‖ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ v : V, ‖(T ^ m) v‖ ≤ ε * ‖v‖ := by
  -- pick an othronormal basis ei s.t. T has an upper triangular matrix with < 1 on diag
  -- 1) first show ‖T^M ei‖ → 0 as M → ∞ for each basis vector ei
  -- T^M e_i is the i-th column of T^M
  --   - base case: first column it is just the first diagonal entry raised to the M-th power times e_1
  --     which goes to 0 since |μ_1| < 1
  --   - induction step: T eᵢ = μᵢ eᵢ + wᵢ with wᵢ ∈ span(e₁, …, eᵢ₋₁) (upper triangular)
  --     so xᴹ := T^M eᵢ satisfies xᴹ = μᵢ xᴹ⁻¹ + T^{M-1} wᵢ
  --     T^{M-1} wᵢ → 0 by induction (wᵢ is a fixed combination of e₁, …, eᵢ₋₁)
  --     recursion lemma: aᴹ⁺¹ ≤ r aᴹ + bᴹ with 0 ≤ r < 1 and bᴹ → 0 implies aᴹ → 0
  --     (for M ≥ N with bᴹ ≤ δ: a_{N+k} ≤ rᵏ a_N + δ / (1 - r)), applied to aᴹ = ‖xᴹ‖
  --     (this is `tendsto_pow_apply_of_flag` and `tendsto_zero_of_le_mul_add`)
  -- 2) write v = ∑ a_i e_i with a_i = ⟪e_i, v⟫ (6.30), then
  --    ‖T^M v‖ = ‖∑ a_i T^M e_i‖ ≤ ∑ |a_i| ‖T^M e_i‖ (by triangle inequality)
  --    ≤ ‖v‖ ∑ ‖T^M e_i‖ (Cauchy–Schwarz: |a_i| = |⟪e_i, v⟫| ≤ ‖e_i‖ ‖v‖ = ‖v‖)
  --    ∑ ‖T^M e_i‖ → 0 as a finite sum of terms → 0 by 1), so for all large M it is ≤ ε;
  --    take such an M > 0, giving ‖T^M v‖ ≤ ε‖v‖ for every v
  obtain ⟨n, e, he, hA⟩ := exists_orthonormal_upperTriangular_complex T
  set A := LADR.Section_3C.matrixOf he he T with hAdef
  -- the diagonal entries are the eigenvalues (5.41), so |Aₖₖ| < 1
  have hdiag : ∀ k, ‖A k k‖ < 1 := fun k =>
    h _ ((LADR.Section_5C.isEigenvalue_iff_diag he T hA _).mpr ⟨k, rfl⟩)
  -- upper triangular: T eₖ - Aₖₖ eₖ ∈ span(e_i : i < k)
  have hflag : ∀ k, T (e k) - A k k • e k ∈ Submodule.span ℂ (e '' {i | i < k}) := by
    intro k
    rw [LADR.Section_3C.matrixOf_spec he he T k, ← hAdef,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_left]
    refine Submodule.sum_mem _ fun j hj => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hjk | hjk
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hjk, rfl⟩)
    · rw [hA j k hjk, zero_smul]; exact Submodule.zero_mem _
  -- 1) ‖Tᴹ eᵢ‖ → 0 for each i
  have hlim := tendsto_pow_apply_of_flag T e (fun k => A k k) hdiag hflag
  -- 2) so ∑ᵢ ‖Tᴹ eᵢ‖ → 0, and it is ≤ ε for some M > 0
  have hS : Filter.Tendsto (fun M : ℕ => ∑ i, ‖(T ^ M) (e i)‖) Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ =>
      tendsto_zero_iff_norm_tendsto_zero.mp (hlim i)
  obtain ⟨M, hM, hpos⟩ :=
    ((hS.eventually (ge_mem_nhds hε)).and (Filter.eventually_gt_atTop 0)).exists
  refine ⟨M, hpos, fun v => ?_⟩
  -- v = ∑ ⟪eᵢ, v⟫ eᵢ with |⟪eᵢ, v⟫| ≤ ‖v‖
  calc ‖(T ^ M) v‖ = ‖∑ i, ⟪e i, v⟫_ℂ • (T ^ M) (e i)‖ := by
        conv_lhs => rw [← e.sum_repr' v]
        rw [map_sum]; simp_rw [map_smul]
    _ ≤ ∑ i, ‖⟪e i, v⟫_ℂ‖ * ‖(T ^ M) (e i)‖ :=
        (norm_sum_le _ _).trans_eq (by simp only [norm_smul])
    _ ≤ ∑ i, ‖v‖ * ‖(T ^ M) (e i)‖ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right
          (by simpa [e.orthonormal.1 i] using norm_inner_le_norm (𝕜 := ℂ) (e i) v)
          (norm_nonneg _)
    _ = ‖v‖ * ∑ i, ‖(T ^ M) (e i)‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖v‖ * ε := mul_le_mul_of_nonneg_left hM (norm_nonneg _)
    _ = ε * ‖v‖ := mul_comm _ _

section Riesz22
open MeasureTheory

/-- 6B.22 On {lit}`C[-1, 1]` with {lit}`⟨f, g⟩ = ∫₋₁¹ fg`, the evaluation functional
{lit}`φ(f) = f(0)` is *not* of the form {lit}`f ↦ ⟨f, g⟩`: there is no
{lit}`g ∈ C[-1, 1]` with {lit}`f(0) = ⟨f, g⟩` for every {lit}`f ∈ C[-1, 1]`. This shows the
Riesz representation theorem (6.42) can fail in infinite dimensions. -/
theorem exercise_6B_22 :
    ¬ ∃ g : L2C (-1) 1, ∀ f : L2C (-1) 1,
      L2C.toCont f ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ = ⟪f, g⟫_ℝ := by
  -- work by contradiction
  -- we will first show that g is zero at every c ≠ 0 in [-1, 1]
  -- we need an f with f(0) = 0 that has the same sign as g (where g ≠ 0):
  -- (a bump around c works, but f(x) = x² g(x) does it for all c at once)
  -- then 0 = f(0) = ∫ f g = ∫ x² g(x)², with a nonnegative continuous integrand,
  -- so x² g(x)² = 0 for all x, i.e. g(c) = 0 for every c ≠ 0.
  -- now since g is zero at every c ≠ 0, by continuity g must also be zero at 0.
  -- thus f(0) is also 0, but that is wrong for f = 1.
  rintro ⟨g, hg⟩
  set p0 : Set.Icc (-1 : ℝ) 1 := ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ with hp0
  set G := L2C.toCont g with hG
  -- the inner product is ∫₋₁¹ f g
  have hinner : ∀ f : L2C (-1) 1, ⟪f, g⟫_ℝ = ∫ x, L2C.toCont f x * G x := fun _ => rfl
  -- 1) g(c) = 0 for c ≠ 0: instead of a bump around c, test against f(x) = x² g(x),
  -- which has the sign of g everywhere and f(0) = 0, so ∫ x² g² = 0
  let f : L2C (-1) 1 := (⟨fun x => (x : ℝ) ^ 2 * G x, by fun_prop⟩ : C(Set.Icc (-1 : ℝ) 1, ℝ))
  have hint : ∫ x, L2C.toCont f x * G x = 0 := by
    rw [← hinner, ← hg f]
    show ((0 : ℝ)) ^ 2 * G p0 = 0
    rw [zero_pow two_ne_zero, zero_mul]
  have hnn : 0 ≤ fun x => L2C.toCont f x * G x := fun x => by
    show 0 ≤ (x : ℝ) ^ 2 * G x * G x
    nlinarith [sq_nonneg ((x : ℝ) * G x)]
  have hae := (integral_eq_zero_iff_of_nonneg hnn (L2C.integrable_toCont_mul f g)).mp hint
  -- a continuous function that is 0 a.e. is 0 everywhere
  have hzero : (fun x => L2C.toCont f x * G x) = 0 :=
    (Continuous.ae_eq_iff_eq volume ((L2C.toCont f).continuous.mul G.continuous)
      continuous_zero).mp hae
  have hxg : ∀ x : Set.Icc (-1 : ℝ) 1, (x : ℝ) * G x = 0 := fun x => by
    have h := congrFun hzero x
    change (x : ℝ) ^ 2 * G x * G x = 0 at h
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [← h]; ring)
  -- 2) g(0) = 0 by continuity: g(1/(n+1)) = 0 and 1/(n+1) → 0
  have hs : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ∈ Set.Icc (-1 : ℝ) 1 := fun n => by
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    exact ⟨by linarith, hle⟩
  let s : ℕ → Set.Icc (-1 : ℝ) 1 := fun n => ⟨1 / ((n : ℝ) + 1), hs n⟩
  have hs0 : Filter.Tendsto s Filter.atTop (nhds p0) := by
    rw [hp0, tendsto_subtype_rng]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hGs : ∀ n, G (s n) = 0 := fun n =>
    (mul_eq_zero.mp (hxg (s n))).resolve_left
      (by show 1 / ((n : ℝ) + 1) ≠ 0; positivity)
  have h0 : G p0 = 0 :=
    tendsto_nhds_unique ((G.continuous.tendsto _).comp hs0)
      (by simp only [Function.comp_def, hGs]; exact tendsto_const_nhds)
  -- so g = 0
  have hGall : ∀ x, G x = 0 := fun x => by
    by_cases hx : (x : ℝ) = 0
    · rw [show x = p0 from Subtype.ext hx, h0]
    · exact (mul_eq_zero.mp (hxg x)).resolve_left hx
  have hg0 : g = 0 := ContinuousMap.ext hGall
  -- 3) but then f(0) = ⟪f, 0⟫ = 0 for every f, which fails for f = 1
  let one : L2C (-1) 1 := (ContinuousMap.const _ (1 : ℝ) : C(Set.Icc (-1 : ℝ) 1, ℝ))
  have h1 := hg one
  rw [hg0, inner_zero_right] at h1
  exact one_ne_zero (α := ℝ) h1

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
      (∀ u v w : V, ‖u - w‖ ≤ ‖u - v‖ + ‖v - w‖) := by
  -- 1) positivity - directly from ‖.‖
  -- 2) definiteness - ‖u - v‖ = 0 ↔ u - v = 0 ↔ u = v
  -- 3) symmetry - ‖u - v‖ = ‖-(v - u)‖ = |-1|‖v - u‖ = ‖v - u‖
  -- 4) triangle - ‖u - w‖ = ‖(u - v) + (v - w)‖ ≤ ‖u - v‖ + ‖v - w‖ by the triangle inequality for the norm
  refine ⟨fun u v => norm_nonneg _, fun u v => ?_, fun u v => ?_, fun u v w => ?_⟩
  · rw [norm_eq_zero, sub_eq_zero]
  · rw [← neg_sub, norm_neg]
  · calc ‖u - w‖ = ‖(u - v) + (v - w)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖u - v‖ + ‖v - w‖ := norm_add_le _ _

/-- 6B.23 (b) If {lit}`V` is finite-dimensional then the metric is complete (every
Cauchy sequence converges): {lit}`V` is a {name}`CompleteSpace`. -/
theorem exercise_6B_23b [FiniteDimensional 𝕜 V] : CompleteSpace V := by
  -- assume vᵢ is a Cauchy sequence in V, so ‖vᵢ - vⱼ‖ → 0 as i, j → ∞
  -- by finite-dimensionality, pick an orthonormal basis e₁, …, eₙ of V
  -- let aᵢₖ = ⟪eₖ, vᵢ⟫ be the coordinates of vᵢ, so vᵢ = ∑ₖ aᵢₖ eₖ (6.30)
  -- then ‖vᵢ - vⱼ‖² = ∑ₖ |aᵢₖ - aⱼₖ|² (6.30 applied to vᵢ - vⱼ)
  -- so for each fixed k, |aᵢₖ - aⱼₖ| ≤ ‖vᵢ - vⱼ‖, and (aᵢₖ)ᵢ is Cauchy in 𝕜
  -- 𝕜 (ℝ or ℂ) is complete, so aᵢₖ → bₖ as i → ∞; let b = ∑ₖ bₖ eₖ
  -- finally ‖vᵢ - b‖² = ∑ₖ |aᵢₖ - bₖ|², a finite sum of n terms each → 0,
  -- so vᵢ → b
  obtain ⟨e⟩ := exists_orthonormalBasis (𝕜 := 𝕜) (V := V)
  refine UniformSpace.complete_of_cauchySeq_tendsto fun v hv => ?_
  set a : ℕ → Fin (finrank 𝕜 V) → 𝕜 := fun i k => ⟪e k, v i⟫_𝕜 with hadef
  -- |aᵢₖ - aⱼₖ| ≤ ‖vᵢ - vⱼ‖: one term of the sum ∑ₖ |aᵢₖ - aⱼₖ|² = ‖vᵢ - vⱼ‖²
  have hcoord : ∀ i j k, ‖a i k - a j k‖ ≤ ‖v i - v j‖ := by
    intro i j k
    have hterm : ‖⟪e k, v i - v j⟫_𝕜‖ ^ 2 ≤ ‖v i - v j‖ ^ 2 := by
      rw [parseval e (v i - v j)]
      exact Finset.single_le_sum (f := fun k => ‖⟪e k, v i - v j⟫_𝕜‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ k)
    rw [inner_sub_right] at hterm
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hterm
  -- so each coordinate sequence is Cauchy in 𝕜
  have hcauchy : ∀ k, CauchySeq fun i => a i k := by
    intro k
    rw [Metric.cauchySeq_iff'] at hv ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hv ε hε
    refine ⟨N, fun i hi => ?_⟩
    rw [dist_eq_norm]
    exact (hcoord i N k).trans_lt (by rw [← dist_eq_norm]; exact hN i hi)
  -- 𝕜 is complete: aᵢₖ → bₖ
  choose b hb using fun k => cauchySeq_tendsto_of_complete (hcauchy k)
  refine ⟨∑ k, b k • e k, ?_⟩
  -- ‖vᵢ - b‖² = ∑ₖ |aᵢₖ - bₖ|²
  have hdist : ∀ i, ‖v i - ∑ k, b k • e k‖ ^ 2 = ∑ k, ‖a i k - b k‖ ^ 2 := by
    intro i
    rw [parseval e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_sub_right, e.orthonormal.inner_right_fintype]
  -- a finite sum of terms → 0 tends to 0
  have hsq : Filter.Tendsto (fun i => ∑ k, ‖a i k - b k‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ fun k _ =>
      (tendsto_iff_norm_sub_tendsto_zero.mp (hb k)).pow 2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun i => ?_
  rw [Function.comp_apply, ← hdist i, Real.sqrt_sq (norm_nonneg _)]

/-- 6B.23 (c) Every finite-dimensional subspace {lit}`U ≤ V` is closed in {lit}`V`. -/
theorem exercise_6B_23c (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    IsClosed (U : Set V) := by
  -- U is a finite-dimensional inner product space, so it is complete by 6B.23(b) applied to U
  -- a complete subset of a metric space is closed (standard topology: a sequence in U
  -- converging to v ∈ V is Cauchy, so it converges in U, and limits are unique, so v ∈ U)
  have : CompleteSpace U := exercise_6B_23b (𝕜 := 𝕜) (V := U)
  exact (completeSpace_coe_iff_isComplete.mp this).isClosed

end LADR.Section_6B
