import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Real.Lemmas
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 2A: Span and Linear Independence
-/

namespace LADR.Section_2A

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! 2.1 Notation: list of vectors

Following 1A (1.8), a *list of {lit}`m` vectors in {lit}`V`* is rendered here as
{lit}`Fin m → V`, with the length encoded in the type. -/

/-! 2.2 Definition: linear combination

A *linear combination* of {lit}`v₁, …, vₘ` is any vector of the form
{lit}`a₁ v₁ + ⋯ + aₘ vₘ`. In Lean, with {lit}`v : Fin m → V` and
{lit}`a : Fin m → F`, that's {lit}`∑ i, a i • v i`. -/

example {m : ℕ} (v : Fin m → V) (a : Fin m → F) : V := ∑ i, a i • v i

/-! 2.3 Example: linear combinations in {lit}`ℝ³`

{lit}`(17, -4, 2) = 6 (2, 1, -3) + 5 (1, -2, 4)`, so it *is* a linear
combination of {lit}`(2, 1, -3), (1, -2, 4)`. -/

example : (![17, -4, 2] : Fin 3 → ℝ) =
    (6 : ℝ) • ![2, 1, -3] + (5 : ℝ) • ![1, -2, 4] := by
  funext i; fin_cases i <;> simp <;> ring

/-! Conversely, {lit}`(17, -4, 5)` is *not* a linear combination of
{lit}`(2, 1, -3), (1, -2, 4)`: the linear system has no solution. -/

example : ¬ ∃ a b : ℝ,
    (![17, -4, 5] : Fin 3 → ℝ) =
      a • ![2, 1, -3] + b • ![1, -2, 4] := by
  rintro ⟨a, b, h⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp at h0 h1 h2
  linarith

/-! 2.4 Definition: span

The *span* of {lit}`v₁, …, vₘ` is the set of all linear combinations. In
mathlib this is {name}`Submodule.span` applied to the range of {lit}`v`,
which gives back a {name}`Submodule` (so its subspace structure is automatic). -/

example {m : ℕ} (v : Fin m → V) : Submodule F V := Submodule.span F (Set.range v)

/-! Membership recovers Axler's definition: {lit}`u ∈ span(v₁, …, vₘ)` iff
{lit}`u = a₁ v₁ + ⋯ + aₘ vₘ` for some scalars. -/

example {m : ℕ} (v : Fin m → V) (u : V) :
    u ∈ Submodule.span F (Set.range v) ↔ ∃ a : Fin m → F, ∑ i, a i • v i = u :=
  Submodule.mem_span_range_iff_exists_fun F

/-! The span of the empty list is {lit}`{0}`, which is denoted as ⊥ in mathlib. -/

example : Submodule.span F (Set.range (![] : Fin 0 → V)) = ⊥ := by
  simp

/-! 2.5 Example: span -/

example : (![17, -4, 2] : Fin 3 → ℝ) ∈
    Submodule.span ℝ (Set.range (![![2, 1, -3], ![1, -2, 4]] : Fin 2 → Fin 3 → ℝ)) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact ⟨![6, 5], by funext i; fin_cases i <;> simp <;> ring⟩

example : (![17, -4, 5] : Fin 3 → ℝ) ∉
    Submodule.span ℝ (Set.range (![![2, 1, -3], ![1, -2, 4]] : Fin 2 → Fin 3 → ℝ)) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  rintro ⟨a, ha⟩
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  simp [Fin.sum_univ_two] at h0 h1 h2
  linarith

/-! 2.6 Span is the smallest containing subspace. mathlib's
{name}`Submodule.span` already returns a {name}`Submodule`, and the universal
property is encoded by {name}`Submodule.span_le`. -/

example {m : ℕ} (v : Fin m → V) (k : Fin m) :
    v k ∈ Submodule.span F (Set.range v) :=
  Submodule.subset_span ⟨k, rfl⟩

example {m : ℕ} (v : Fin m → V) (U : Submodule F V) (h : ∀ k, v k ∈ U) :
    Submodule.span F (Set.range v) ≤ U :=
  Submodule.span_le.mpr (Set.range_subset_iff.mpr h)

/-! 2.7 Definition: spans

A list *spans* {lit}`V` if its span is all of {lit}`V`. {lit}`F` is taken
explicitly so call sites read {lit}`Spans F v` and Lean doesn't have to guess
the scalar field from {lit}`v` alone. -/

def Spans (F : Type*) {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {m : ℕ} (v : Fin m → V) : Prop :=
  Submodule.span F (Set.range v) = ⊤

/-! 2.8 Example: a list that spans {lit}`Fⁿ`

The standard basis {lit}`(1, 0, …, 0), (0, 1, …, 0), …, (0, …, 0, 1)` spans
{lit}`Fⁿ`. -/

example (n : ℕ) :
    Spans F (fun k : Fin n => (Pi.single k 1 : Fin n → F)) := by
  rw [Spans, eq_top_iff]
  intro v _
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨v, ?_⟩
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    show v i • (Pi.single i (1 : F) : Fin n → F) j = 0
    simp [hij.symm]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! 2.9 Definition: finite-dimensional vector space

A vector space is *finite-dimensional* if some list spans it. mathlib's
{name}`Module.Finite` says equivalently that the top submodule is *finitely
generated* — i.e. spanned by some finite set. -/

/-! From a spanning list to {name}`Module.Finite`: package the (finite) range
of {lit}`v` as the witnessing finset. -/

example : (∃ (m : ℕ) (v : Fin m → V), Spans F v) ↔ Module.Finite F V := by
  constructor
  . rintro ⟨_, v, h⟩
    classical
    refine ⟨(Set.range v).toFinset, ?_⟩
    rw [Spans] at h
    rw [Set.coe_toFinset]; exact h
  . intro hfin
    classical
    obtain ⟨S, hS⟩ := hfin.fg_top
    refine ⟨S.card, fun i => S.equivFin.symm i, ?_⟩
    rw [Spans, ← hS]
    congr 1
    ext x
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (S.equivFin.symm i).2,
      fun hx => ⟨S.equivFin ⟨x, hx⟩, by simp⟩⟩

example (n : ℕ) : Module.Finite F (Fin n → F) := inferInstance

/-! 2.10 Definition: polynomial, {lit}`P(F)`

A polynomial is a function {lit}`p : F → F` of the form
{lit}`p(z) = a₀ + a₁ z + ⋯ + aₘ zᵐ`. In mathlib, polynomials are formal
algebraic objects of type {name}`Polynomial`; the function {lit}`F → F` is
recovered by {name}`Polynomial.eval` (often abbreviated {lit}`p.eval`). -/

example (p : Polynomial F) : F → F := p.eval

/-! {name}`Polynomial` is a vector space over {lit}`F`. -/

noncomputable example : Module F (Polynomial F) := inferInstance

/-! Taking the span of the image of {name}`Polynomial.eval` realizes
"polynomials as functions" as a subspace of {lit}`F → F`. Over Axler's
fields ({lit}`F = ℝ` or {lit}`ℂ`, both infinite) the map {lit}`p ↦ p.eval`
is injective — distinct polynomials yield distinct functions — so polynomials
as formal objects and polynomials as functions coincide. -/

noncomputable example : Submodule F (F → F) :=
  Submodule.span F (Set.range (fun p : Polynomial F => p.eval))

/-! 2.11 Definition: degree of a polynomial

mathlib's {name}`Polynomial.degree` lives in {lit}`WithBot ℕ`, where {lit}`⊥`
plays the role of Axler's {lit}`-∞` (so the zero polynomial has degree
{lit}`⊥`). -/

example (p : Polynomial F) : WithBot ℕ := p.degree

example : (0 : Polynomial F).degree = ⊥ := Polynomial.degree_zero

/-! Two polynomials are equal if and only if all their coefficients are equal. -/
example (p q : Polynomial F) : p = q ↔ ∀ n, p.coeff n = q.coeff n :=
  Polynomial.ext_iff

/-! Axler reads off {lit}`degree p = m` from the coefficients: the {lit}`m`-th
coefficient is nonzero, and every higher coefficient vanishes. mathlib's
{name}`Polynomial.coeff` (returning {lit}`p.coeff n : F`) is the same
"{lit}`n`-th coefficient" map, and this characterization holds. -/

example (p : Polynomial F) (m : ℕ) :
    p.degree = (m : ℕ) ↔ p.coeff m ≠ 0 ∧ ∀ n > m, p.coeff n = 0 := by
  refine ⟨fun hdeg => ?_, fun ⟨hm, hgt⟩ => ?_⟩
  · -- {lit}`degree p = m` forces {lit}`p ≠ 0`, hence {lit}`natDegree p = m`.
    have hp0 : p ≠ 0 := fun h => by simp [h] at hdeg
    have hnat : p.natDegree = m := by
      have := Polynomial.degree_eq_natDegree hp0
      rw [hdeg] at this; exact_mod_cast this.symm
    refine ⟨?_, fun n hn => ?_⟩
    · rw [← hnat, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hp0
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hnat ▸ hn)
  · -- Conversely, {lit}`hm` rules out {lit}`p = 0`; {lit}`hgt` plus
    -- {lit}`p.coeff m ≠ 0` pin {lit}`natDegree p = m`.
    have hp0 : p ≠ 0 := fun h => hm (by simp [h])
    have hle : p.natDegree ≤ m := by
      by_contra h
      push Not at h
      have hne : p.coeff p.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hp0
      exact hne (hgt _ h)
    have hge : m ≤ p.natDegree := by
      by_contra h
      push Not at h
      exact hm (Polynomial.coeff_eq_zero_of_natDegree_lt h)
    have hnat : p.natDegree = m := le_antisymm hle hge
    rw [Polynomial.degree_eq_natDegree hp0, hnat]

/-! 2.12 Notation: {lit}`Pₘ(F)`

{lit}`Pₘ(F)` is the subspace of polynomials of degree at most {lit}`m`. In
mathlib this is {name}`Polynomial.degreeLT`, which collects polynomials of
degree *strictly less than* {lit}`n`; Axler's {lit}`Pₘ(F)` is therefore
{lit}`Polynomial.degreeLT F (m+1)`. -/

noncomputable example (m : ℕ) : Submodule F (Polynomial F) :=
  Polynomial.degreeLT F (m + 1)

example (m : ℕ) (p : Polynomial F) :
    p ∈ Polynomial.degreeLT F (m + 1) ↔ p.degree < (m + 1 : ℕ) :=
  Polynomial.mem_degreeLT

/-! {lit}`Pₘ(F)` is finite-dimensional: the linear equivalence
{name}`Polynomial.degreeLTEquiv` to {lit}`Fin (m+1) → F` makes this immediate. -/

example (m : ℕ) : Module.Finite F (Polynomial.degreeLT F (m + 1)) :=
  Module.Finite.equiv (Polynomial.degreeLTEquiv F (m + 1)).symm

/-! 2.13 Definition: infinite-dimensional vector space

A vector space is *infinite-dimensional* if it is not finite-dimensional. -/

example : Prop := ¬ Module.Finite F V

/-! 2.14 Example: {lit}`P(F)` is infinite-dimensional. -/

theorem polynomial_infiniteDimensional [Infinite F] :
    ¬ Module.Finite F (Polynomial F) := by
  -- Suppose, for contradiction, that {lit}`P(F)` is finite-dimensional.
  -- Then some finite list spans it; let {lit}`m` be the largest degree
  -- appearing in the list. Every linear combination has degree ≤ m, so
  -- {lit}`X^(m+1)` cannot be in the span. But the span is all of {lit}`P(F)`.
  intro hfin
  obtain ⟨S, hS⟩ := hfin.fg_top
  set m := S.sup Polynomial.natDegree with hm_def
  have hbound : Submodule.span F (S : Set (Polynomial F)) ≤
      Polynomial.degreeLT F (m + 1) := by
    rw [Submodule.span_le]
    intro p hp
    rw [SetLike.mem_coe, Polynomial.mem_degreeLT]
    have hp_deg : p.degree ≤ (m : WithBot ℕ) := by
      by_cases hp0 : p = 0
      · simp [hp0]
      · rw [Polynomial.degree_eq_natDegree hp0]
        exact_mod_cast Finset.le_sup hp
    exact lt_of_le_of_lt hp_deg (by exact_mod_cast Nat.lt_succ_self m)
  rw [hS] at hbound
  have hX : (Polynomial.X : Polynomial F) ^ (m + 1) ∈
      Polynomial.degreeLT F (m + 1) := hbound trivial
  rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow] at hX
  exact_mod_cast lt_irrefl _ hX

/-! 2.15 Definition: linearly independent

A list {lit}`v₁, …, vₘ` is *linearly independent* if the only choice of
scalars making {lit}`a₁ v₁ + ⋯ + aₘ vₘ = 0` is {lit}`a₁ = ⋯ = aₘ = 0`. mathlib's
{name}`LinearIndependent` packages this as injectivity of the linear-combination
map; for finite index types {name}`Fintype.linearIndependent_iff` recovers the
textbook formulation. -/

example {m : ℕ} (v : Fin m → V) :
    LinearIndependent F v ↔ ∀ a : Fin m → F, ∑ i, a i • v i = 0 → ∀ i, a i = 0 :=
  Fintype.linearIndependent_iff

/-! The empty list is linearly independent. -/

example : LinearIndependent F (![] : Fin 0 → V) :=
  linearIndependent_empty_type

/-! 2.16 Example: linearly independent lists -/

/-! (a) The standard list {lit}`(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0)` is
linearly independent in {lit}`F⁴`. -/

example : LinearIndependent F
    (![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0]] : Fin 3 → Fin 4 → F) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  simp [Fin.sum_univ_three] at h0 h1 h2
  intro i; fin_cases i <;> assumption

/-! (b) {lit}`1, z, …, zᵐ` is linearly independent in {lit}`P(F)`. -/

example (m : ℕ) :
    LinearIndependent F (fun i : Fin (m + 1) => (Polynomial.X (R := F)) ^ (i : ℕ)) := by
  -- Suppose {lit}`a₀ • 1 + a₁ • X + ⋯ + aₘ • Xᵐ = 0`. Reading off the coefficient
  -- of {lit}`Xⁱ` on the left forces {lit}`aᵢ = 0`.
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  have hi := congrArg (fun p : Polynomial F => p.coeff (i : ℕ)) ha
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hi
  rw [Finset.sum_eq_single i] at hi
  · simpa using hi
  · intro j _ hji
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! (c) A length-1 list {lit}`v` is linearly independent iff {lit}`v ≠ 0`.
Stated here; proved as {lit}`exercise_2A_4a` below.

(d) A length-2 list is linearly independent iff neither vector is a scalar
multiple of the other. Stated here; proved as {lit}`exercise_2A_4b` below. -/

/-! 2.17 Definition: linearly dependent

A list is *linearly dependent* if it is not linearly independent. -/

example {m : ℕ} (v : Fin m → V) : Prop := ¬ LinearIndependent F v

/-! Concretely: there exist scalars not all zero summing to {lit}`0`. -/

example {m : ℕ} (v : Fin m → V) :
    ¬ LinearIndependent F v ↔ ∃ a : Fin m → F, (∑ i, a i • v i = 0) ∧ ∃ i, a i ≠ 0 := by
  rw [Fintype.linearIndependent_iff]
  push Not
  rfl

/-! 2.18 Example: linearly dependent lists -/

example :
    ¬ LinearIndependent ℝ (![![2, 3, 1], ![1, -1, 2], ![7, 3, 8]] : Fin 3 → Fin 3 → ℝ) := by
  rw [Fintype.linearIndependent_iff]; push Not
  refine ⟨![2, 3, -1], ?_, 0, by simp⟩
  funext i; fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

/-! {lit}`(2, 3, 1), (1, -1, 2), (7, 3, c)` is linearly dependent in {lit}`F³`
iff {lit}`c = 8`. (Axler: "as you should verify"; the field is assumed
{name}`CharZero` so the witnessing coefficients {lit}`2, 3, -1` are nonzero.
Appears as {lit}`exercise_2A_6` below.) -/

example [CharZero F] (c : F) :
    ¬ LinearIndependent F (![![2, 3, 1], ![1, -1, 2], ![7, 3, c]] : Fin 3 → Fin 3 → F) ↔
      c = 8 := by
  constructor
  · rw [Fintype.linearIndependent_iff]; push Not
    rintro ⟨a, ha, j, hj⟩
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    have h2 := congrFun ha 2
    simp [Fin.sum_univ_three] at h0 h1 h2
    -- {lit}`h0 + h1` ⟹ {lit}`5 a 0 + 10 a 2 = 0`, so {lit}`a 0 = -2 a 2`.
    have ha0 : a 0 = -(2 * a 2) := by linear_combination (1 / 5 : F) * h0 + (1 / 5) * h1
    -- {lit}`3 h0 - 2 h1` ⟹ {lit}`5 a 1 + 15 a 2 = 0`, so {lit}`a 1 = -3 a 2`.
    have ha1 : a 1 = -(3 * a 2) := by linear_combination (3 / 5 : F) * h0 - (2 / 5) * h1
    -- Substituting into {lit}`h2`: {lit}`(c - 8) * a 2 = 0`.
    have hkey : (c - 8) * a 2 = 0 := by linear_combination h2 - ha0 - 2 * ha1
    rcases mul_eq_zero.mp hkey with hc | h2zero
    · linear_combination hc
    · -- {lit}`a 2 = 0` forces {lit}`a 0 = a 1 = 0` too, contradicting {lit}`hj`.
      exfalso; apply hj
      fin_cases j <;> simp_all
  · rintro rfl
    rw [Fintype.linearIndependent_iff]; push Not
    refine ⟨![2, 3, -1], ?_, 0, by norm_num⟩
    funext i; fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

/-! If some vector in a list is a linear combination of the others, the list
is linearly dependent: write {lit}`v_k = ∑_{i ≠ k} a_i v_i` and move
{lit}`v_k` to the other side with coefficient {lit}`-1`. -/

example {m : ℕ} (v : Fin m → V) (k : Fin m) (a : Fin m → F)
    (hk : v k = ∑ i ∈ Finset.univ.erase k, a i • v i) :
    ¬ LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff]; push Not
  -- Coefficients: {lit}`-1` at index {lit}`k`, {lit}`a i` elsewhere.
  refine ⟨Function.update a k (-1), ?_, k, by simp⟩
  -- Split off the {lit}`k`-th term: {lit}`-1 • v k + ∑_{i ≠ k} a i • v i = 0`.
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  rw [Function.update_self, neg_one_smul]
  rw [Finset.sum_congr rfl (g := fun i => a i • v i) ?_]
  · rw [← hk, neg_add_cancel]
  · intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-! Any list containing the zero vector is linearly dependent. -/

example {m : ℕ} (v : Fin m → V) (k : Fin m) (hk : v k = 0) :
    ¬ LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff]; push Not
  refine ⟨Pi.single k (1 : F), ?_, k, by simp⟩
  rw [Finset.sum_eq_single k]
  · simp [hk]
  · intro i _ hik; simp [Pi.single_eq_of_ne hik]
  · intro h; exact absurd (Finset.mem_univ k) h

/-! 2.19 Linear dependence lemma

If {lit}`v₁, …, vₘ` is linearly dependent, then some {lit}`v_k` lies in the
span of the previous ones; furthermore the span is unchanged when {lit}`v_k`
is removed. -/

theorem linearDependence_lemma {m : ℕ} (v : Fin m → V) (h : ¬ LinearIndependent F v) :
    ∃ k : Fin m, v k ∈ Submodule.span F (v '' {i | i < k}) ∧
      Submodule.span F (Set.range v) =
        Submodule.span F (v '' {i | i ≠ k}) := by
  classical
  rw [Fintype.linearIndependent_iff] at h
  push Not at h
  obtain ⟨a, hsum, j, haj⟩ := h
  -- Let {lit}`k` be the largest index with {lit}`a k ≠ 0`.
  let S : Finset (Fin m) := Finset.univ.filter (fun i => a i ≠ 0)
  have hSne : S.Nonempty :=
    ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, haj⟩⟩
  let k := S.max' hSne
  have hak : a k ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hSne)).2
  have hkmax : ∀ i : Fin m, k < i → a i = 0 := by
    intro i hki
    by_contra hai
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩
    exact absurd hki (not_lt.mpr (S.le_max' i hiS))
  set M : Submodule F V := Submodule.span F (v '' {i : Fin m | i < k}) with hM_def
  have hdisj : Disjoint
      (Finset.univ.filter (· < k : Fin m → Prop))
      (Finset.univ.filter (k < ·)) := by
    rw [Finset.disjoint_filter]
    intros i _ hi hki; exact lt_asymm hki hi
  have hgt_zero : ∑ i ∈ Finset.univ.filter (k < ·), a i • v i = 0 := by
    apply Finset.sum_eq_zero
    intros i hi
    rw [Finset.mem_filter] at hi
    rw [hkmax i hi.2, zero_smul]
  have hfilter_split : (Finset.univ : Finset (Fin m)).erase k =
      (Finset.univ.filter (· < k)) ∪ (Finset.univ.filter (k < ·)) := by
    ext i
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt (fun h => (ne_of_lt h).symm)⟩
  have hsum_split : a k • v k +
      ∑ i ∈ Finset.univ.filter (· < k : Fin m → Prop), a i • v i = 0 := by
    have h1 := Finset.add_sum_erase Finset.univ (fun i => a i • v i) (Finset.mem_univ k)
    rw [hsum] at h1
    rw [hfilter_split, Finset.sum_union hdisj, hgt_zero, add_zero] at h1
    exact h1
  have hsmall_in_M : ∑ i ∈ Finset.univ.filter (· < k : Fin m → Prop),
      a i • v i ∈ M := by
    refine Submodule.sum_mem _ ?_
    intro i hi
    rw [Finset.mem_filter] at hi
    exact M.smul_mem _ (Submodule.subset_span ⟨i, hi.2, rfl⟩)
  have hak_vk : a k • v k ∈ M := by
    have heq : a k • v k =
        -(∑ i ∈ Finset.univ.filter (· < k : Fin m → Prop), a i • v i) :=
      eq_neg_of_add_eq_zero_left hsum_split
    rw [heq]; exact M.neg_mem hsmall_in_M
  have hvk : v k ∈ M := by
    have : v k = (a k)⁻¹ • (a k • v k) := by
      rw [smul_smul, inv_mul_cancel₀ hak, one_smul]
    rw [this]; exact M.smul_mem _ hak_vk
  refine ⟨k, hvk, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    by_cases hik : i = k
    · subst hik
      have hsub : v '' {i : Fin m | i < k} ⊆ v '' {i : Fin m | i ≠ k} :=
        Set.image_mono fun _ hi => ne_of_lt hi
      exact Submodule.span_mono hsub hvk
    · exact Submodule.subset_span ⟨i, hik, rfl⟩
  · exact Submodule.span_mono (Set.image_subset_range _ _)

/-! 2.21 Example: smallest k in linear dependence lemma

For {lit}`(1, 2, 3), (6, 5, 4), (15, 16, 17), (8, 9, 7)` in {lit}`ℝ³`, the
smallest {lit}`k` that works is {lit}`k = 3` (the third vector lies in the
span of the first two), since the second vector is *not* a scalar multiple of
the first. -/

/-- For the 4-list {lit}`v = (1,2,3), (6,5,4), (15,16,17), (8,9,7)` in
{lit}`ℝ³`, the smallest {lit}`k` from the linear-dependence lemma is
{lit}`k = 2`: {lit}`v 2 = (15,16,17) ∈ span (v 0, v 1)` (witness:
{lit}`3 (1,2,3) + 2 (6,5,4)`), while {lit}`v 1 = (6,5,4)` is *not* a scalar
multiple of {lit}`v 0 = (1,2,3)`, so {lit}`k = 1` doesn't work. -/
example :
    let v : Fin 4 → Fin 3 → ℝ := ![![1, 2, 3], ![6, 5, 4], ![15, 16, 17], ![8, 9, 7]]
    v 2 ∈ Submodule.span ℝ (v '' {i | i < 2}) ∧
      v 1 ∉ Submodule.span ℝ (v '' {i | i < 1}) := by
  constructor
  · -- {lit}`(15,16,17) = 3 (1,2,3) + 2 (6,5,4)`.
    rw [show ({i : Fin 4 | i < 2} : Set _) = {0, 1} by
          ext i; fin_cases i <;> simp]
    rw [Set.image_pair]
    rw [Submodule.mem_span_pair]
    refine ⟨3, 2, ?_⟩
    funext i; fin_cases i <;> simp <;> ring
  · rw [show ({i : Fin 4 | i < 1} : Set _) = {0} by ext i; fin_cases i <;> simp]
    rw [Set.image_singleton]
    rw [Submodule.mem_span_singleton]
    rintro ⟨a, ha⟩
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp at h0 h1
    linarith

/-! 2.22 Length of linearly independent list ≤ length of spanning list

In a finite-dimensional vector space, the length of every linearly independent
list of vectors is at most the length of every spanning list. -/

theorem linearIndependent_le_spanning {m n : ℕ} (u : Fin m → V) (w : Fin n → V)
    (hu : LinearIndependent F u) (hw : Spans F w) : m ≤ n := by
  -- TODO: review this more carefully, it is a bit more involved than I expected.
  classical
  suffices H : ∀ k, k ≤ m → ∃ T : Finset (Fin n),
      T.card + k = n ∧
      Submodule.span F ((u '' {i : Fin m | i.val < k}) ∪
        (w '' (T : Set (Fin n)))) = ⊤ by
    obtain ⟨T, hTc, _⟩ := H m le_rfl
    omega
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Finset.univ, by simp, ?_⟩
    have hempty : {i : Fin m | i.val < 0} = ∅ := by ext; simp
    rw [hempty, Set.image_empty, Set.empty_union, Finset.coe_univ, Set.image_univ]
    exact hw
  | succ k ih =>
    intro hk1m
    have hkm : k < m := hk1m
    obtain ⟨T, hTcard, hTspan⟩ := ih (Nat.le_of_succ_le hk1m)
    have hkn : k ≤ n := by omega
    -- Enumerator of {lit}`T` in order, and the list
    -- {lit}`L = (u 0, …, u k, w_{j_1}, …, w_{j_{T.card}})` of length {lit}`n+1`.
    let r : Fin T.card ↪o Fin n := T.orderEmbOfFin rfl
    have hr_range : Set.range ⇑r = (↑T : Set (Fin n)) :=
      Finset.range_orderEmbOfFin T rfl
    let L : Fin (n + 1) → V := fun i =>
      if hi : (i : ℕ) ≤ k then u ⟨i, by have := i.isLt; omega⟩
      else w (r ⟨i - (k + 1), by have := i.isLt; omega⟩)
    have hLu : ∀ (i : ℕ) (hi : i < n + 1) (hi' : i ≤ k),
        L ⟨i, hi⟩ = u ⟨i, by omega⟩ := by
      intros i _ hi'; exact dif_pos hi'
    have hLw : ∀ (i : ℕ) (hi : i < n + 1) (hi' : k + 1 ≤ i),
        L ⟨i, hi⟩ = w (r ⟨i - (k + 1), by omega⟩) := by
      intros i _ hi'
      have hnot : ¬ i ≤ k := by omega
      exact dif_neg hnot
    -- {lit}`u_k` sits at position {lit}`k` of {lit}`L`.
    let pos_k : Fin (n + 1) := ⟨k, by omega⟩
    let pos_k_m : Fin m := ⟨k, hkm⟩
    have hL_pos_k : L pos_k = u pos_k_m := hLu k (by omega) le_rfl
    -- Inclusion: the IH spanning set lies inside {lit}`L`'s image off
    -- position {lit}`pos_k`.
    have hWk_sub : (u '' {i : Fin m | i.val < k}) ∪ (w '' (T : Set (Fin n))) ⊆
        L '' ({pos_k}ᶜ : Set (Fin (n + 1))) := by
      rintro x (⟨i, hi, rfl⟩ | ⟨j, hjT, rfl⟩)
      · -- {lit}`x = u i` with {lit}`i.val < k`
        have hik : i.val < k := hi
        refine ⟨⟨i.val, by omega⟩, ?_, ?_⟩
        · intro h
          have : i.val = k := by simpa [pos_k] using congrArg Fin.val h
          omega
        · rw [hLu i.val (by omega) (by omega)]
      · -- {lit}`x = w j` with {lit}`j ∈ T`
        have hj_range : j ∈ Set.range ⇑r := by rw [hr_range]; exact hjT
        obtain ⟨idx, hidx⟩ := hj_range
        have hidxLt : idx.val < T.card := idx.isLt
        refine ⟨⟨k + 1 + idx.val, by omega⟩, ?_, ?_⟩
        · intro h
          have : k + 1 + idx.val = k := by simpa [pos_k] using congrArg Fin.val h
          omega
        · rw [hLw _ (by omega) (by omega)]
          have hreduce : (⟨k + 1 + idx.val - (k + 1), by omega⟩ : Fin T.card) = idx := by
            apply Fin.ext; show k + 1 + idx.val - (k + 1) = idx.val; omega
          rw [hreduce, hidx]
    -- {lit}`u_k = L pos_k` is in {lit}`span(L '' {pos_k}ᶜ)`.
    have hL_pos_k_in : L pos_k ∈ Submodule.span F (L '' ({pos_k}ᶜ)) := by
      rw [hL_pos_k]
      have : u pos_k_m ∈ (⊤ : Submodule F V) := trivial
      rw [← hTspan] at this
      exact (Submodule.span_mono hWk_sub) this
    -- {lit}`L` is linearly dependent.
    have hLdep : ¬ LinearIndependent F L := fun hLind =>
      hLind.notMem_span pos_k hL_pos_k_in
    -- 2.19 applied to {lit}`L`.
    obtain ⟨p, hp_in_span, hL_span_eq⟩ := linearDependence_lemma L hLdep
    -- {lit}`p > k`: a {lit}`u`-position would force {lit}`u_p ∈ span(u_{<p})`,
    -- contradicting linear independence of {lit}`u`.
    have hp_gt : k < p.val := by
      by_contra hpk
      push Not at hpk
      let p_m : Fin m := ⟨p.val, by omega⟩
      have hL_p : L p = u p_m := hLu p.val p.isLt hpk
      have h_lt_sub : L '' {q : Fin (n + 1) | q < p} ⊆ u '' ({p_m}ᶜ) := by
        rintro x ⟨q, hq, rfl⟩
        have hqp : q.val < p.val := hq
        rw [hLu q.val q.isLt (by omega)]
        refine ⟨⟨q.val, by omega⟩, ?_, rfl⟩
        intro h
        have : q.val = p.val := by simpa [p_m] using congrArg Fin.val h
        omega
      have hu_p_in : u p_m ∈ Submodule.span F (u '' ({p_m}ᶜ)) := by
        rw [← hL_p]; exact (Submodule.span_mono h_lt_sub) hp_in_span
      exact hu.notMem_span p_m hu_p_in
    -- {lit}`p ≥ k+1`, so {lit}`L p = w j` for the {lit}`p-(k+1)`-th element of {lit}`T`.
    have hp_lower : k + 1 ≤ p.val := hp_gt
    let q : Fin T.card := ⟨p.val - (k + 1), by have := p.isLt; omega⟩
    let j : Fin n := r q
    have hL_p_eq : L p = w j := hLw p.val p.isLt hp_lower
    have hj_in_T : j ∈ T := by
      have : j ∈ Set.range ⇑r := ⟨q, rfl⟩
      rw [hr_range] at this; exact this
    -- New finset: drop {lit}`j`.
    let T' : Finset (Fin n) := T.erase j
    refine ⟨T', ?_, ?_⟩
    · simp only [T']; rw [Finset.card_erase_of_mem hj_in_T]; omega
    -- {lit}`L '' {p}ᶜ = (u '' {<k+1}) ∪ (w '' T')`.
    have h_pre_eq : L '' ({p}ᶜ : Set (Fin (n + 1))) =
        (u '' {i : Fin m | i.val < k + 1}) ∪
          (w '' (T' : Set (Fin n))) := by
      ext x
      constructor
      · rintro ⟨i, hi_ne, rfl⟩
        by_cases hi_le : i.val ≤ k
        · -- {lit}`u`-position
          left
          rw [hLu i.val i.isLt hi_le]
          exact ⟨⟨i.val, by omega⟩, by simpa, rfl⟩
        · -- {lit}`w`-position; show the resulting {lit}`w`-index lies in {lit}`T'`.
          push Not at hi_le
          right
          rw [hLw i.val i.isLt hi_le]
          refine ⟨_, ?_, rfl⟩
          simp only [T', Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff]
          refine ⟨?_, ?_⟩
          · have : r ⟨i.val - (k + 1), by have := i.isLt; omega⟩ ∈ Set.range ⇑r :=
              ⟨_, rfl⟩
            rwa [hr_range] at this
          · intro hrj
            apply hi_ne
            have hidx_eq : (⟨i.val - (k + 1), by have := i.isLt; omega⟩ : Fin T.card) = q :=
              r.injective hrj
            have h_val : i.val - (k + 1) = q.val := congrArg Fin.val hidx_eq
            have h_q : q.val = p.val - (k + 1) := rfl
            apply Fin.ext
            show i.val = p.val
            omega
      · rintro (⟨i, hi, rfl⟩ | ⟨j', hj'T', rfl⟩)
        · have hi_lt : i.val < k + 1 := hi
          refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_, ?_⟩
          · intro h
            have : i.val = p.val := by simpa using congrArg Fin.val h
            omega
          · rw [hLu i.val (by have := i.isLt; omega) (by omega)]
        · -- {lit}`j' ∈ T'` so {lit}`j' ∈ T` and {lit}`j' ≠ j`.
          simp only [T', Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff] at hj'T'
          obtain ⟨hj'_T, hj'_ne⟩ := hj'T'
          have h_range : j' ∈ Set.range ⇑r := by rw [hr_range]; exact hj'_T
          obtain ⟨idx', hidx'⟩ := h_range
          have hidxLt : idx'.val < T.card := idx'.isLt
          refine ⟨⟨k + 1 + idx'.val, by omega⟩, ?_, ?_⟩
          · intro h
            apply hj'_ne
            have hsum_eq : k + 1 + idx'.val = p.val := by
              simpa using congrArg Fin.val h
            have hidx_q : idx' = q := by
              apply Fin.ext
              show idx'.val = p.val - (k + 1)
              omega
            rw [← hidx', hidx_q]
          · rw [hLw (k + 1 + idx'.val) (by omega) (by omega)]
            have hreduce : (⟨k + 1 + idx'.val - (k + 1), by omega⟩ : Fin T.card) = idx' := by
              apply Fin.ext; show k + 1 + idx'.val - (k + 1) = idx'.val; omega
            rw [hreduce, hidx']
    -- {lit}`range L` spans {lit}`V` (it contains the IH spanning set).
    have h_range_top : Submodule.span F (Set.range L) = ⊤ := by
      rw [eq_top_iff, ← hTspan]
      apply Submodule.span_mono
      rintro x (⟨i, hi, rfl⟩ | ⟨j', hj'T, rfl⟩)
      · have hik : i.val < k := hi
        refine ⟨⟨i.val, by have := i.isLt; omega⟩, ?_⟩
        rw [hLu i.val (by have := i.isLt; omega) (by omega)]
      · have h_range : j' ∈ Set.range ⇑r := by rw [hr_range]; exact hj'T
        obtain ⟨idx', hidx'⟩ := h_range
        have hidxLt : idx'.val < T.card := idx'.isLt
        refine ⟨⟨k + 1 + idx'.val, by omega⟩, ?_⟩
        rw [hLw (k + 1 + idx'.val) (by omega) (by omega)]
        have hreduce : (⟨k + 1 + idx'.val - (k + 1), by omega⟩ : Fin T.card) = idx' := by
          apply Fin.ext; show k + 1 + idx'.val - (k + 1) = idx'.val; omega
        rw [hreduce, hidx']
    -- Combine: {lit}`L '' {q | q ≠ p} = L '' {p}ᶜ` (defeq), then
    -- 2.19 turns {lit}`span(L '' {p}ᶜ) = span(range L) = ⊤`.
    have h_compl : ({q : Fin (n + 1) | q ≠ p} : Set _) = ({p}ᶜ : Set _) := rfl
    rw [← h_pre_eq, ← h_compl, ← hL_span_eq, h_range_top]

/-! 2.23 Example: no list of length 4 is linearly independent in {lit}`ℝ³` -/

example : ¬ LinearIndependent ℝ
    (![![1, 2, 3], ![4, 5, 8], ![9, 6, 7], ![-3, 2, 8]] : Fin 4 → Fin 3 → ℝ) := by
  intro h
  have hspan : Spans ℝ (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] : Fin 3 → Fin 3 → ℝ) := by
    rw [Spans, eq_top_iff]
    intro v _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨v, ?_⟩
    funext i; fin_cases i <;> simp [Fin.sum_univ_three]
  exact absurd (linearIndependent_le_spanning _ _ h hspan) (by decide)

/-! 2.24 Example: no list of length 3 spans {lit}`ℝ⁴` -/

example : ¬ Spans ℝ
    (![![1, 2, 3, -5], ![4, 5, 8, 3], ![9, 6, 7, -1]] : Fin 3 → Fin 4 → ℝ) := by
  intro h
  have hli : LinearIndependent ℝ
      (![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]
        : Fin 4 → Fin 4 → ℝ) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    have h2 := congrFun ha 2
    have h3 := congrFun ha 3
    simp [Fin.sum_univ_four] at h0 h1 h2 h3
    intro i; fin_cases i <;> assumption
  exact absurd (linearIndependent_le_spanning _ _ hli h) (by decide)

/-! 2.25 Finite-dimensional subspaces

Every subspace of a finite-dimensional vector space is finite-dimensional.
mathlib provides this directly as an instance — -/

example (U : Submodule F V) [Module.Finite F V] : Module.Finite F U :=
  inferInstance

/-! — but Axler proves it by hand. Build an LI list {lit}`u₁, …, uₙ` in
{lit}`U` greedily: at each step, if the current list does not span {lit}`U`,
pick a vector in {lit}`U` outside its span, which by 2.13 extends LI. By 2.22,
the length is bounded by the length of any spanning list of {lit}`V`, so the
process terminates; maximality then forces the final list to span {lit}`U`. -/

example (U : Submodule F V) [Module.Finite F V] : Module.Finite F U := by
  classical
  -- Get a spanning list {lit}`w` of {lit}`V` of length {lit}`n` (any
  -- finite-generating set, packaged via {name}`Module.Finite.exists_fin`).
  obtain ⟨n, w, hw⟩ := Module.Finite.exists_fin (R := F) (M := V)
  have hw_spans : Spans F w := hw
  -- {lit}`S`: lengths of LI lists in {lit}`U`. Nonempty ({lit}`0 ∈ S`) and
  -- bounded above by {lit}`n` via 2.22 (push LI to {lit}`V`, compare to
  -- {lit}`w`).
  let S : Set ℕ := {k | ∃ u : Fin k → U, LinearIndependent F u}
  have hS0 : (0 : ℕ) ∈ S := ⟨Fin.elim0, linearIndependent_empty_type⟩
  have hSbdd : BddAbove S := by
    refine ⟨n, ?_⟩
    rintro k ⟨u, hu⟩
    have hu' : LinearIndependent F (fun i => (u i : V)) :=
      hu.map' U.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
    exact linearIndependent_le_spanning _ _ hu' hw_spans
  -- Pick {lit}`m = sSup S`. Then {lit}`m ∈ S` (witness {lit}`u`) and
  -- {lit}`m` bounds every length in {lit}`S`.
  set m := sSup S with hm_def
  obtain ⟨u, hu⟩ : m ∈ S := Nat.sSup_mem ⟨0, hS0⟩ hSbdd
  have hmax : ∀ k ∈ S, k ≤ m := fun _ hk => le_csSup hSbdd hk
  -- {lit}`u` spans {lit}`U`: if some {lit}`⟨y, hyU⟩ : U` were outside
  -- {lit}`span (range u)`, 2.13 would extend {lit}`u` by it to an LI list of
  -- length {lit}`m + 1 ∈ S`, contradicting maximality of {lit}`m`.
  have hspan_U : Submodule.span F (Set.range u) = ⊤ := by
    by_contra hne
    have hlt : Submodule.span F (Set.range u) < ⊤ := lt_top_iff_ne_top.mpr hne
    obtain ⟨y, _, hy_not⟩ := SetLike.exists_of_lt hlt
    have hsnoc_LI : LinearIndependent F (Fin.snoc u y : Fin (m + 1) → U) := by
      -- In a relation on the extended list, the coefficient {lit}`A` of {lit}`y` must
      -- vanish: otherwise {lit}`y = -A⁻¹ (∑ gᵢ uᵢ)` would lie in {lit}`span (range u)`.
      -- With {lit}`A = 0` the relation is one among the {lit}`u`'s, so {lit}`hu` finishes.
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_castSucc] at hg
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
      set A := g (Fin.last m) with hA
      have hlast : A = 0 := by
        by_contra hA0
        refine hy_not ?_
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨fun i => -A⁻¹ * g i.castSucc, ?_⟩
        have hneg : ∑ i, g i.castSucc • u i = -(A • y) := by
          rw [eq_neg_iff_add_eq_zero]; exact hg
        calc ∑ i, (-A⁻¹ * g i.castSucc) • u i
            = (-A⁻¹) • ∑ i, g i.castSucc • u i := by
              rw [Finset.smul_sum]
              exact Finset.sum_congr rfl fun i _ => (smul_smul _ _ _).symm
          _ = (-A⁻¹) • (-(A • y)) := by rw [hneg]
          _ = y := by
              rw [smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hA0, neg_one_smul, neg_neg]
      rw [hlast, zero_smul, add_zero] at hg
      exact Fin.lastCases hlast (Fintype.linearIndependent_iff.mp hu (fun i => g i.castSucc) hg)
    have : m + 1 ≤ m := hmax (m + 1) ⟨_, hsnoc_LI⟩
    omega
  -- {lit}`u : Fin m → U` spans {lit}`U`, so its finite image
  -- ({lit}`Finset.univ.image u`) finitely generates the submodule {lit}`U`.
  refine ⟨Finset.univ.image u, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact hspan_U

/-! # Exercises -/

/-- 2A.1 -/
theorem exercise_2A_1 :
    ∃ v : Fin 4 → (Fin 3 → F),
      Function.Injective v ∧
      (Submodule.span F (Set.range v) : Set (Fin 3 → F)) = {x | x 0 + x 1 + x 2 = 0} := by
  -- (-1,1,0), (1,0,-1), (0,1,-1), (0,0,0) -- the dim is two, so first two are enough
  -- (x,y,z) = (-z)(-1,1,0) + (x-z)(1,0,-1) + (-x)(0,1,-1) (when x+y+z=0)
  refine ⟨![![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], 0], ?_, ?_⟩
  · intro i j hij
    have h0 := congrFun hij 0
    have h1 := congrFun hij 1
    have h2 := congrFun hij 2
    fin_cases i <;> fin_cases j <;> simp_all [funext_iff, Fin.forall_fin_succ]
  · ext x
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · intro hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        fin_cases i <;> simp
      | zero => simp
      | add a b _ _ ha hb => simpa using by linear_combination ha + hb
      | smul c a _ ha => simpa [mul_add] using by linear_combination c * ha
    · intro hx
      -- {lit}`(x,y,z) = -z(-1,1,0) + (x-z)(1,0,-1) - x(0,1,-1)` when {lit}`x + y + z = 0`.
      refine (Submodule.mem_span_range_iff_exists_fun F).mpr
        ⟨![-(x 2), x 0 - x 2, -(x 0), 0], ?_⟩
      funext i
      fin_cases i
      · simp [Fin.sum_univ_four]
      · simp [Fin.sum_univ_four]; linear_combination -hx
      · simp [Fin.sum_univ_four]

/-- 2A.2 -/
def exercise_2A_2 (v : Fin 4 → V) : Decidable (Spans F v →
    Spans F (![v 0 - v 1, v 1 - v 2, v 2 - v 3, v 3] : Fin 4 → V)) := by
  apply isTrue
  -- since v i spans w = a 0 v 0 + a 1 v 1 + a 2 v 2 + a 3 v 3
  -- a rewrite shows w = a 0 (v 0 - v 1) + (a 0 + a 1) (v 1 - v 2) + (a 0 + a 1 + a 2) (v 2 - v 3) + (a 0 + a 1 + a 2 + a 3) v 3
  intro h
  set U := Submodule.span F (Set.range (![v 0 - v 1, v 1 - v 2, v 2 - v 3, v 3] : Fin 4 → V))
    with hU
  -- Each difference, and {lit}`v 3`, lies in {lit}`U`; telescoping recovers the {lit}`v i`.
  have m0 : v 0 - v 1 ∈ U := Submodule.subset_span ⟨0, by simp⟩
  have m1 : v 1 - v 2 ∈ U := Submodule.subset_span ⟨1, by simp⟩
  have m2 : v 2 - v 3 ∈ U := Submodule.subset_span ⟨2, by simp⟩
  have h3 : v 3 ∈ U := Submodule.subset_span ⟨3, by simp⟩
  have h2 : v 2 ∈ U := by simpa using add_mem m2 h3
  have h1 : v 1 ∈ U := by simpa using add_mem m1 h2
  have h0 : v 0 ∈ U := by simpa using add_mem m0 h1
  rw [Spans, eq_top_iff, ← h, Submodule.span_le, Set.range_subset_iff]
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

/-- 2A.3 -/
theorem exercise_2A_3 {m : ℕ} (v : Fin m → V) :
    Submodule.span F (Set.range v) =
      Submodule.span F (Set.range (fun k : Fin m => ∑ i : Fin (k + 1), v ⟨i, by omega⟩)) := by
  -- enough to show that each v k is in the span w i
  -- and each w k is in the span v i
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    -- subtract w k - w (k-1) = v k is in the span of v i
    have mem : ∀ (j : ℕ) (hj : j < m),
        (∑ i : Fin (j + 1), v ⟨i, by omega⟩) ∈
          Submodule.span F (Set.range (fun k : Fin m => ∑ i : Fin (k + 1), v ⟨i, by omega⟩)) :=
      fun j hj => Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨n, hn⟩ := k
    cases n with
    | zero => simpa using mem 0 hn
    | succ n =>
      have key : (∑ i : Fin (n + 1 + 1), v ⟨i, by omega⟩)
          = (∑ i : Fin (n + 1), v ⟨i, by omega⟩) + v ⟨n + 1, hn⟩ :=
        Fin.sum_univ_castSucc _
      have hsub := sub_mem (mem (n + 1) hn) (mem n (by omega))
      rw [key] at hsub
      simpa using hsub
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    -- w k = v 0 + … + v k is in the span of v i
    exact sum_mem fun i _ => Submodule.subset_span ⟨_, rfl⟩

/-- 2A.4(a) -/
theorem exercise_2A_4a (v : V) : LinearIndependent F (![v] : Fin 1 → V) ↔ v ≠ 0 := by
  -- ∑ i, a i • v = 0 is a 0 v 0 = 0, so if v = 0, then a 0 can be nonzero
  -- and if v ≠ 0, then a 0 must be zero
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h hv
    have := h ![1] (by simp [hv]) 0
    simp at this
  · intro hv a ha i
    fin_cases i
    have h0 := ha
    simp at h0
    rcases h0 with h | h
    · exact h
    · exact absurd h hv

/-- 2A.4(b) -/
theorem exercise_2A_4b (v w : V) : LinearIndependent F (![v, w] : Fin 2 → V) ↔
    (∀ a : F, w ≠ a • v) ∧ (∀ b : F, v ≠ b • w) := by
  -- => a v + b w = 0 implies a = b = 0
  -- if w = a v, then b = -1 implies sum = 0, but b ≠ 0, so not LI
  -- if v = b w, then a = -1 implies sum = 0, but a ≠ 0, so not LI
  -- <= assume a v + b w = 0, want to prove a = b = 0
  -- if both v = w = 0 we have contra, so assume by symmetr v ≠ 0
  -- if b = 0, then a v = 0, so a = 0, contra
  -- so -a / b v = w, contra
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hLI
    refine ⟨fun a hwa => ?_, fun b hvb => ?_⟩
    · have hsum : ∑ i, ![a, -1] i • (![v, w] : Fin 2 → V) i = 0 := by
        rw [Fin.sum_univ_two]; simp [hwa]
      have := hLI _ hsum 1
      simp at this
    · have hsum : ∑ i, ![-1, b] i • (![v, w] : Fin 2 → V) i = 0 := by
        rw [Fin.sum_univ_two]; simp [hvb]
      have := hLI _ hsum 0
      simp at this
  · rintro ⟨hwv, hvw⟩ a hsum
    rw [Fin.sum_univ_two] at hsum
    simp at hsum
    by_cases hb : a 1 = 0
    · rw [hb, zero_smul, add_zero] at hsum
      by_cases ha : a 0 = 0
      · intro i; fin_cases i <;> assumption
      · exfalso
        apply hvw 0
        have : v = (a 0)⁻¹ • (a 0 • v) := by
          rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
        rw [this, hsum, smul_zero, zero_smul]
    · exfalso
      apply hwv (-(a 1)⁻¹ * a 0)
      have hwexpr : a 1 • w = -(a 0 • v) := eq_neg_of_add_eq_zero_right hsum
      have hw : w = (a 1)⁻¹ • (a 1 • w) := by
        rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      rw [hw, hwexpr, smul_neg, smul_smul, neg_mul, neg_smul]

/-- 2A.5 Find {lit}`t ∈ ℝ` such that the list is *not* linearly independent. -/
theorem exercise_2A_5 :
    ∃ t : ℝ, ¬ LinearIndependent ℝ
      (![![3, 1, 4], ![2, -3, 5], ![5, 9, t]] : Fin 3 → Fin 3 → ℝ) := by
  -- 3 v 0 - 2 v 1 = v 2, so t = 3*4 - 2*5 = 2 would make the list linearly dependent
  refine ⟨2, ?_⟩
  rw [Fintype.linearIndependent_iff]; push Not
  refine ⟨![3, -2, -1], ?_, 0, by norm_num⟩
  funext i
  fin_cases i <;> simp [Fin.sum_univ_three] <;> norm_num

/-- 2A.6 The field is assumed {name}`CharZero`: the {lit}`3 × 3` determinant is
{lit}`-5 (c - 8)`, so in characteristic {lit}`5` the list is dependent for every
{lit}`c` and the equivalence fails. -/
theorem exercise_2A_6 [CharZero F] (c : F) :
    ¬ LinearIndependent F (![![2, 3, 1], ![1, -1, 2], ![7, 3, c]] : Fin 3 → Fin 3 → F) ↔
      c = 8 := by
  -- if c = 8, then 2 v 0 + 3 v 1 - v 2 = 0, so the list is linearly dependent,
  -- any other value still forces 2 and 3 to first two params, so c must be 8 to make the list linearly dependent
  constructor
  · rw [Fintype.linearIndependent_iff]; push Not
    rintro ⟨a, ha, j, hj⟩
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    have h2 := congrFun ha 2
    simp [Fin.sum_univ_three] at h0 h1 h2
    -- the first two coordinates force {lit}`a 0 = -2 a 2` and {lit}`a 1 = -3 a 2`
    have ha0 : a 0 = -(2 * a 2) := by linear_combination (1 / 5 : F) * h0 + (1 / 5) * h1
    have ha1 : a 1 = -(3 * a 2) := by linear_combination (3 / 5 : F) * h0 - (2 / 5) * h1
    -- and then the third gives {lit}`(c - 8) * a 2 = 0`
    have hkey : (c - 8) * a 2 = 0 := by linear_combination h2 - ha0 - 2 * ha1
    rcases mul_eq_zero.mp hkey with hc | h2zero
    · linear_combination hc
    · -- {lit}`a 2 = 0` would force {lit}`a 0 = a 1 = 0` too, contradicting {lit}`hj`
      exfalso; apply hj
      fin_cases j <;> simp_all
  · rintro rfl
    rw [Fintype.linearIndependent_iff]; push Not
    refine ⟨![2, 3, -1], ?_, 0, by norm_num⟩
    funext i; fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

/-- 2A.7(a) Over {lit}`ℝ`, the list {lit}`1+i, 1-i` is linearly independent in
{lit}`ℂ` (viewed as an {lit}`ℝ`-vector space). -/
theorem exercise_2A_7a :
    LinearIndependent ℝ (![(1 + Complex.I), (1 - Complex.I)] : Fin 2 → ℂ) := by
  -- a (1 + i) + b (1 - i) = 0 over R, means a + b = 0 and a - b = 0, so a = b , 2 a = 0, so a = b = 0
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_two] at hg
  -- the {lit}`ℝ`-scalar action on {lit}`ℂ` is multiplication by the coercion
  have hg' : (g 0 : ℂ) * (1 + Complex.I) + (g 1 : ℂ) * (1 - Complex.I) = 0 := hg
  simp [Complex.ext_iff] at hg'
  fin_cases i <;> simp <;> linarith [hg'.1, hg'.2]

/-- 2A.7(b) Over {lit}`ℂ`, the same list is linearly dependent. -/
theorem exercise_2A_7b :
    ¬ LinearIndependent ℂ (![(1 + Complex.I), (1 - Complex.I)] : Fin 2 → ℂ) := by
  -- over C - i (1 + i) = i - i ^2 = i - 1 = -1 * (1 - i), so i (1 + i) + 1 (1 - i) = 0, so the list is linearly dependent
  rw [Fintype.linearIndependent_iff]; push Not
  refine ⟨![Complex.I, 1], ?_, 0, by simp⟩
  rw [Fin.sum_univ_two]
  simp [Complex.ext_iff]

/-- 2A.8 -/
theorem exercise_2A_8 (v : Fin 4 → V) (h : LinearIndependent F v) :
    LinearIndependent F (![v 0 - v 1, v 1 - v 2, v 2 - v 3, v 3] : Fin 4 → V) := by
  -- assume a (v 0 - v 1) + b (v 1 - v 2) + c (v 2 - v 3) + d v 3 = 0, then
  -- a v 0 + (b - a) v 1 + (c - b) v 2 + (d - c) v 3 = 0, so by LI, a = b - a = c - b = d - c = 0, so a = b = c = d = 0
  -- replace one by one and get a = b = c = d = 0
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro a ha
  rw [Fin.sum_univ_four] at ha
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at ha
  have key : ∀ j, (![a 0, a 1 - a 0, a 2 - a 1, a 3 - a 2] : Fin 4 → F) j = 0 := by
    refine h _ ?_
    rw [Fin.sum_univ_four, ← ha]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, sub_smul, smul_sub]
    abel
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have k3 := key 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at k0 k1 k2 k3
  intro i
  fin_cases i
  · exact k0
  · show a 1 = 0
    linear_combination k1 + k0
  · show a 2 = 0
    linear_combination k2 + k1 + k0
  · show a 3 = 0
    linear_combination k3 + k2 + k1 + k0

/-- 2A.9 The field is assumed {name}`CharZero`: in characteristic {lit}`5` one has
{lit}`5 • v 0 - 4 • v 1 = v 1`, so for {lit}`m ≥ 1` the updated list repeats
{lit}`v 1` and is dependent. -/
def exercise_2A_9 [CharZero F] :
    Decidable (∀ {m : ℕ} (v : Fin (m + 1) → V) (_ : LinearIndependent F v),
      LinearIndependent F (Function.update v 0 ((5 : F) • v 0 - (4 : F) • v 1))) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  -- assume a (5 v 0 - 4 v 1) + b v 1 + ... = 0
  -- then a 5 v 0 + (b - a 4) v 1 + ... = 0, so by LI, a = b - a 4 = ... = 0, so a = b = ... = 0
  intro m v hv
  cases m with
  | zero =>
    -- in {lit}`Fin 1` the index {lit}`1` *is* {lit}`0`, so the update is the identity
    have h10 : (1 : Fin 1) = 0 := Subsingleton.elim _ _
    have hupd : (5 : F) • v 0 - (4 : F) • v 1 = v 0 := by
      rw [h10, ← sub_smul]; norm_num
    rw [hupd, Function.update_eq_self]
    exact hv
  | succ n =>
    -- updating at {lit}`0` is consing onto the tail
    have hcons : Function.update v 0 ((5 : F) • v 0 - (4 : F) • v 1)
        = Fin.cons ((5 : F) • v 0 - (4 : F) • v 1) (Fin.tail v) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
    have hv' : LinearIndependent F (Fin.cons (v 0) (Fin.tail v)) := by
      rw [Fin.cons_self_tail]; exact hv
    obtain ⟨htail, hnot⟩ := linearIndependent_finCons.mp hv'
    rw [hcons, linearIndependent_finCons]
    refine ⟨htail, fun hmem => hnot ?_⟩
    -- {lit}`v 1` is in the tail's span, so {lit}`5 • v 0` would be too, hence {lit}`v 0`
    have hv1 : v 1 ∈ Submodule.span F (Set.range (Fin.tail v)) :=
      Submodule.subset_span ⟨0, by simp [Fin.tail]⟩
    have h5 : ((5 : F) • v 0) ∈ Submodule.span F (Set.range (Fin.tail v)) := by
      simpa using add_mem hmem (Submodule.smul_mem _ (4 : F) hv1)
    have h5ne : (5 : F) ≠ 0 := by norm_num
    have := Submodule.smul_mem _ ((5 : F)⁻¹) h5
    rwa [smul_smul, inv_mul_cancel₀ h5ne, one_smul] at this

/-- 2A.10 -/
def exercise_2A_10 :
    Decidable (∀ {m : ℕ} (v : Fin m → V) (γ : F) (_ : γ ≠ 0)
      (_ : LinearIndependent F v), LinearIndependent F (fun i => γ • v i)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  -- assume λ v 0 + ... = 0, then γ (λ v 0 + ...) = 0, so
  -- λ v 0 + ... = 0, so by LI, λ = ... = 0, so the new list is LI too
  apply isTrue
  intro m v γ hγ hv
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro a ha i
  have hsum : ∑ j, (a j * γ) • v j = 0 := by simpa [smul_smul] using ha
  exact (mul_eq_zero.mp (hv _ hsum i)).resolve_right hγ

/-- 2A.11 *Prove or counterexample.* If {lit}`v₁, …, vₘ` and {lit}`w₁, …, wₘ`
are linearly independent, is {lit}`v₁ + w₁, …, vₘ + wₘ` linearly independent?
The ambient space is taken to be {lit}`F²`: over a *zero* vector space the claim
would be vacuously true (a linearly independent list there must be empty), so a
counterexample has to name a space. -/
def exercise_2A_11 :
    Decidable (∀ {m : ℕ} (v w : Fin m → (Fin 2 → F)),
      LinearIndependent F v → LinearIndependent F w →
      LinearIndependent F (fun i => v i + w i)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- use V = F^2 and take v1,v2 = e1,e2 and w1,w2 = e2,e1, then v1+w1 = e1+e2, v2+w2 = e1+e2
  -- the list is clearly not LI, as 1 * (e1+e2) + -1 * (e1+e2) = 0, but the first two lists are LI
  intro hcon
  have hv : LinearIndependent F (![![1, 0], ![0, 1]] : Fin 2 → Fin 2 → F) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp [Fin.sum_univ_two] at h0 h1
    fin_cases i <;> simp_all
  have hw : LinearIndependent F (![![0, 1], ![1, 0]] : Fin 2 → Fin 2 → F) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp [Fin.sum_univ_two] at h0 h1
    fin_cases i <;> simp_all
  have hdep := hcon _ _ hv hw
  rw [Fintype.linearIndependent_iff] at hdep
  have hone := hdep ![1, -1] (by funext i; fin_cases i <;> simp [Fin.sum_univ_two]) 0
  simp at hone

/-- 2A.12 -/
theorem exercise_2A_12 {m : ℕ} (v : Fin m → V) (w : V)
    (hv : LinearIndependent F v)
    (hvw : ¬ LinearIndependent F (fun i => v i + w)) :
    w ∈ Submodule.span F (Set.range v) := by
  -- assumed a(v0 + w) + b(v1 + w) + ... = 0, s.t. not all a, b, ... are zero, then
  -- a v0 + b v1 + ... + (a + b + ...) w = 0, let (a + b + ...) = A,
  -- w = -1/A (a v0 + b v1 + ...), so w is in the span of v i, unless A = 0,
  -- but if A = 0, then a v0 + b v1 + ... = 0, so by LI, a = b = ... = 0, contradiction.
  rw [Fintype.linearIndependent_iff] at hv hvw
  push Not at hvw
  obtain ⟨a, ha, j, hj⟩ := hvw
  have hsplit : ∑ i, a i • v i + (∑ i, a i) • w = 0 := by
    rw [← ha, Finset.sum_smul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (smul_add _ _ _).symm
  set A := ∑ i, a i with hA
  by_cases hA0 : A = 0
  · -- `A = 0` would make `v` itself dependent
    exact absurd (hv a (by rwa [hA0, zero_smul, add_zero] at hsplit) j) hj
  · -- otherwise divide by `A`: `w = -A⁻¹ (a v₀ + b v₁ + ⋯)`
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => -A⁻¹ * a i, ?_⟩
    have hneg : ∑ i, a i • v i = -(A • w) := by
      rw [eq_neg_iff_add_eq_zero]; exact hsplit
    calc ∑ i, (-A⁻¹ * a i) • v i
        = (-A⁻¹) • ∑ i, a i • v i := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => (smul_smul _ _ _).symm
      _ = (-A⁻¹) • (-(A • w)) := by rw [hneg]
      _ = w := by
          rw [smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hA0, neg_one_smul, neg_neg]

/-- 2A.13 -/
theorem exercise_2A_13 {m : ℕ} (v : Fin m → V) (w : V) (hv : LinearIndependent F v) :
    LinearIndependent F (Fin.snoc v w : Fin (m + 1) → V) ↔
      w ∉ Submodule.span F (Set.range v) := by
  -- => by contra assume w = a v0 + b v1 + ..., s.t. not all a, b, ... are zero, then
  -- then a v0 +  ... -1 w = 0, without all zero, so list is dependent.
  -- <= assume a v0 + b v1 + ... + z w = 0, then
  -- a v0 + b v1 + ... = - z w,
  -- since w is not in th span of v i, we must have z = 0, so a v0 + b v1 + ... = 0, so by LI, a = b = ... = 0, so the list is LI.
  -- but then by v i independent, we must have a = b = ... = 0, so the list is LI.
  constructor
  · -- if `w = a v₀ + b v₁ + ⋯`, then `a v₀ + ⋯ + (-1) w = 0` is a nontrivial relation
    intro hLI hmem
    rw [Fintype.linearIndependent_iff] at hLI
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hrel : ∑ i, (Fin.snoc c (-1 : F) : Fin (m + 1) → F) i •
        (Fin.snoc v w : Fin (m + 1) → V) i = 0 := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hc]
      simp
    have hlast := hLI _ hrel (Fin.last m)
    rw [Fin.snoc_last] at hlast
    norm_num at hlast
  · -- conversely, in a relation `∑ g i • v i + A • w = 0` the coefficient `A` of `w`
    -- must vanish (else `w = -A⁻¹ (∑ g i • v i)` lies in the span), and then `v` is
    -- linearly independent, so all the other coefficients vanish too
    intro hw
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_castSucc] at hg
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
    set A := g (Fin.last m) with hA
    have hlast : A = 0 := by
      by_contra hA0
      refine hw ?_
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => -A⁻¹ * g i.castSucc, ?_⟩
      have hneg : ∑ i, g i.castSucc • v i = -(A • w) := by
        rw [eq_neg_iff_add_eq_zero]; exact hg
      calc ∑ i, (-A⁻¹ * g i.castSucc) • v i
          = (-A⁻¹) • ∑ i, g i.castSucc • v i := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ => (smul_smul _ _ _).symm
        _ = (-A⁻¹) • (-(A • w)) := by rw [hneg]
        _ = w := by
            rw [smul_neg, smul_smul, neg_mul, inv_mul_cancel₀ hA0, neg_one_smul, neg_neg]
    rw [hlast, zero_smul, add_zero] at hg
    have hzero := (Fintype.linearIndependent_iff.mp hv) (fun i => g i.castSucc) hg
    exact Fin.lastCases hlast hzero

/-- 2A.14 -/
theorem exercise_2A_14 {m : ℕ} (v : Fin m → V) :
    LinearIndependent F v ↔
      LinearIndependent F (fun k : Fin m => ∑ i : Fin (k + 1), v ⟨i, by omega⟩) := by
  -- => assum a v0 + b (v0 + v1) + c (v0 + v1 + v2) + ... = 0, then
  -- (a + b + c + ...) v0 + (b + c + ...) v1 + (c + ...) v2 + ... = 0, so by LI,
  -- each is zero, working quickly down the list gives a = b = c = ... = 0, so the new list is LI.
  -- <= conversely, assume a v0 + b v1 + c v2 + ... = 0, then
  -- a v0 + (b - a) (v0 + v1) + (c - b) (v0 + v1 + v2) + ... = 0,
  -- so by LI, a = b - a = c - b = ... = 0, so then a = b = c = ... = 0, so the original list is LI.
  -- `w k` is the sum of the `v i` over all indices `i ≤ k`
  have hw : ∀ k : Fin m, (∑ i : Fin (k + 1), v ⟨i, by omega⟩) = ∑ i ∈ Finset.Iic k, v i := by
    intro k
    refine Finset.sum_bij (fun (i : Fin (k + 1)) _ => (⟨i.1, by omega⟩ : Fin m)) ?_ ?_ ?_ ?_
    · intro a _
      simp only [Finset.mem_Iic, Fin.le_def]
      omega
    · intro a _ b _ hab
      simpa [Fin.ext_iff] using hab
    · intro c hc
      rw [Finset.mem_Iic] at hc
      have hc' : (c : ℕ) ≤ (k : ℕ) := hc
      exact ⟨⟨c.1, by omega⟩, Finset.mem_univ _, by simp⟩
    · intro a _
      rfl
  -- exchanging the order of summation turns `∑ a k • w k` into `∑ (a k + a (k+1) + ⋯) • v i`
  have key : ∀ a : Fin m → F,
      ∑ k, a k • (∑ i : Fin (k + 1), v ⟨i, by omega⟩)
        = ∑ i, (∑ k ∈ Finset.Ici i, a k) • v i := by
    intro a
    simp_rw [hw, Finset.smul_sum, Finset.sum_smul]
    exact Finset.sum_comm' (by intro x y; simp [Finset.mem_Iic, Finset.mem_Ici])
  -- those suffix sums vanish only for the zero coefficients: read them off from the top down
  have hker : ∀ a : Fin m → F, (∀ i, ∑ k ∈ Finset.Ici i, a k = 0) → ∀ k, a k = 0 := by
    cases m with
    | zero => exact fun a _ k => absurd k.2 (by omega)
    | succ n =>
      intro a h
      refine Fin.lastCases ?_ ?_
      · have hlast : Finset.Ici (Fin.last n) = {Fin.last n} := by
          ext x
          simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_def, Fin.ext_iff, Fin.val_last]
          omega
        have hl := h (Fin.last n)
        rwa [hlast, Finset.sum_singleton] at hl
      · intro i
        have hsplit : Finset.Ici i.castSucc = insert i.castSucc (Finset.Ici i.succ) := by
          ext x
          simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff,
            Fin.val_succ, Fin.val_castSucc]
          omega
        have hnotmem : i.castSucc ∉ Finset.Ici i.succ := by
          simp only [Finset.mem_Ici, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega
        have h1 := h i.castSucc
        rwa [hsplit, Finset.sum_insert hnotmem, h i.succ, add_zero] at h1
  -- conversely every prescription of suffix sums is realized, by `a k = b k - b (k+1)`
  have hsurj : ∀ b : Fin m → F, ∃ a : Fin m → F, ∀ i, ∑ k ∈ Finset.Ici i, a k = b i := by
    cases m with
    | zero => exact fun b => ⟨b, fun i => absurd i.2 (by omega)⟩
    | succ n =>
      intro b
      refine ⟨fun k => b k - (if h : (k : ℕ) + 1 < n + 1 then b ⟨k + 1, h⟩ else 0), ?_⟩
      refine Fin.reverseInduction ?_ ?_
      · have hlast : Finset.Ici (Fin.last n) = {Fin.last n} := by
          ext x
          simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.le_def, Fin.ext_iff, Fin.val_last]
          omega
        rw [hlast, Finset.sum_singleton]
        simp [Fin.val_last]
      · intro i hi
        have hsplit : Finset.Ici i.castSucc = insert i.castSucc (Finset.Ici i.succ) := by
          ext x
          simp only [Finset.mem_Ici, Finset.mem_insert, Fin.le_def, Fin.ext_iff,
            Fin.val_succ, Fin.val_castSucc]
          omega
        have hnotmem : i.castSucc ∉ Finset.Ici i.succ := by
          simp only [Finset.mem_Ici, Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega
        have hlt : (i.castSucc : ℕ) + 1 < n + 1 := by
          simp only [Fin.val_castSucc]; omega
        have hsucc : (⟨(i.castSucc : ℕ) + 1, hlt⟩ : Fin (n + 1)) = i.succ := by
          simp [Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
        rw [hsplit, Finset.sum_insert hnotmem, hi, dif_pos hlt, hsucc]
        ring
  constructor
  · intro hv
    rw [Fintype.linearIndependent_iff] at hv ⊢
    intro a ha
    rw [key a] at ha
    exact hker a (hv _ ha)
  · intro hwLI
    rw [Fintype.linearIndependent_iff] at hwLI ⊢
    intro b hb
    obtain ⟨a, hab⟩ := hsurj b
    have hzero : ∀ k, a k = 0 := by
      refine hwLI a ?_
      rw [key a]
      simp_rw [hab]
      exact hb
    intro i
    rw [← hab i]
    exact Finset.sum_eq_zero fun k _ => hzero k

/-! The list {lit}`1, z, …, z^(n-1)` in {lit}`degreeLT F n`, obtained by pulling the
standard list {lit}`(1,0,…,0), …, (0,…,0,1)` of {lit}`Fⁿ` back along
{name}`Polynomial.degreeLTEquiv` (a polynomial of degree {lit}`< n` corresponds to its
coefficient vector). It is linearly independent and spans, which is all that 2A.15,
2A.16 and 2A.20 need. -/

noncomputable def degreeLT_monomials (n : ℕ) : Fin n → Polynomial.degreeLT F n :=
  fun i => (Polynomial.degreeLTEquiv F n).symm (Pi.single i 1)

theorem degreeLT_monomials_linearIndependent (n : ℕ) :
    LinearIndependent F (degreeLT_monomials (F := F) n) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  -- push the relation through the (injective) coefficient map
  have h0 : (Polynomial.degreeLTEquiv F n).symm
      (∑ i, a i • (Pi.single i 1 : Fin n → F)) = 0 := by
    rw [map_sum]
    simpa [degreeLT_monomials] using ha
  have h1 : ∑ i, a i • (Pi.single i 1 : Fin n → F) = 0 := by
    simpa using congrArg (Polynomial.degreeLTEquiv F n) h0
  simpa [Finset.sum_apply, Pi.single_apply] using congrFun h1 j

theorem degreeLT_monomials_spans (n : ℕ) : Spans F (degreeLT_monomials (F := F) n) := by
  rw [Spans, eq_top_iff]
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  -- the coefficients of {lit}`x` are the scalars that rebuild it
  refine ⟨fun i => (Polynomial.degreeLTEquiv F n) x i, ?_⟩
  have hpi : ∑ i, ((Polynomial.degreeLTEquiv F n) x i) • (Pi.single i 1 : Fin n → F)
      = (Polynomial.degreeLTEquiv F n) x := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc ∑ i, ((Polynomial.degreeLTEquiv F n) x i) • degreeLT_monomials (F := F) n i
      = (Polynomial.degreeLTEquiv F n).symm
          (∑ i, ((Polynomial.degreeLTEquiv F n) x i) • (Pi.single i 1 : Fin n → F)) := by
        rw [map_sum]
        simp [degreeLT_monomials]
    _ = x := by rw [hpi]; simp

/-- 2A.15 -/
theorem exercise_2A_15 :
    ¬ ∃ v : Fin 6 → Polynomial.degreeLT ℝ 5, LinearIndependent ℝ v := by
  -- there is list of 5 poly that spans so any list of 6 poly is dependent
  rintro ⟨v, hv⟩
  exact absurd (linearIndependent_le_spanning _ _ hv (degreeLT_monomials_spans (F := ℝ) 5)) (by decide)

/-- 2A.16 -/
theorem exercise_2A_16 :
    ¬ ∃ v : Fin 4 → Polynomial.degreeLT ℝ 5,
      Spans ℝ v := by
  -- 5 poly basis is LI, so any span has tp be 5 or more
  rintro ⟨v, hv⟩
  exact absurd (linearIndependent_le_spanning _ _ (degreeLT_monomials_linearIndependent (F := ℝ) 5) hv)
    (by decide)

/-- 2A.17 -/
theorem exercise_2A_17 :
    ¬ Module.Finite F V ↔
      ∃ v : ℕ → V, ∀ m : ℕ, LinearIndependent F (fun i : Fin m => v i) := by
  -- => assume v is not finite, take a vector v i
  -- if it spans V, we contradict, so it does not span V,
  -- this means there is at least one outside its space
  -- add it to the list ,and thus the list is LI,
  -- repeat this process to get an infinite list of LI vectors

  -- <=, assume v is finite, so there is a list that spans V
  -- take m bigger than the length of the list
  -- then v i is LI of length bigger than span list, contradiction
  constructor
  · intro hfin
    classical
    -- no finite set spans, so from any finite list we can step outside its span
    have key : ∀ t : Finset V, ∃ x : V, x ∉ Submodule.span F (t : Set V) := by
      intro t
      by_contra hcon
      push Not at hcon
      exact hfin ⟨t, eq_top_iff.mpr fun x _ => hcon x⟩
    choose f hf using key
    -- collect the chosen vectors: `T n = {v 0, …, v (n-1)}` and `v n = f (T n)`
    set T : ℕ → Finset V := fun n => Nat.rec (∅ : Finset V) (fun _ t => insert (f t) t) n with hTdef
    set v : ℕ → V := fun n => f (T n) with hvdef
    have hTsucc : ∀ n, T (n + 1) = insert (v n) (T n) := fun _ => rfl
    have hmemT : ∀ n, ∀ i < n, v i ∈ T n := by
      intro n
      induction n with
      | zero => omega
      | succ n ih =>
        intro i hi
        rw [hTsucc]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact Finset.mem_insert_of_mem (ih i h)
        · exact h ▸ Finset.mem_insert_self _ _
    refine ⟨v, fun m => ?_⟩
    induction m with
    | zero => exact linearIndependent_empty_type
    | succ n ih =>
      have hsnoc : (fun i : Fin (n + 1) => v i) = Fin.snoc (fun i : Fin n => v i) (v n) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hsnoc, exercise_2A_13 _ _ ih]
      intro hmem
      -- the span of `v 0, …, v (n-1)` sits inside the span of `T n`, which misses `v n`
      refine hf (T n) (Submodule.span_mono ?_ hmem)
      rintro _ ⟨i, rfl⟩
      exact hmemT n i i.isLt
  · rintro ⟨v, hv⟩ hfin
    obtain ⟨n, w, hw⟩ := Module.Finite.exists_fin (R := F) (M := V)
    have hle := linearIndependent_le_spanning _ w (hv (n + 1)) (hw : Spans F w)
    omega

/-- 2A.18 {lit}`F^∞` is infinite-dimensional. -/
theorem exercise_2A_18 : ¬ Module.Finite F (ℕ → F) := by
  -- take e i vectors,
  -- show their finite subsets 0, ..., n are LI
  -- if sum ai ei = 0, then each ai = 0, so the list is LI
  -- by 2A.17, the space is infinite-dimensional
  rw [exercise_2A_17]
  refine ⟨fun n => Pi.single n 1, fun m => ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  simpa [Finset.sum_apply, Pi.single_apply, Fin.val_inj, Finset.sum_ite_eq]
    using congrFun ha (j : ℕ)

/-- 2A.19 The real vector space of all continuous real-valued functions on
{lit}`[0, 1]` is infinite-dimensional. We follow the convention of 1.35(b)
and use {lit}`C(ℝ, ℝ)` (continuous functions on all of {lit}`ℝ`); the same
argument works on {lit}`C(Set.Icc 0 1, ℝ)`. -/
theorem exercise_2A_19 :
    ¬ Module.Finite ℝ C(ℝ, ℝ) := by
  -- take the functions f n (x) = x ^ n, show that any finite subset is LI
  -- already proved for polynomials, so the list is LI
  -- by 2A.17, the space is infinite-dimensional
  rw [exercise_2A_17]
  refine ⟨fun n => ⟨fun x => x ^ n, continuous_pow n⟩, fun m => ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha j
  -- the polynomial `∑ a i Xⁱ` vanishes at every real, so it is the zero polynomial
  have hp : (∑ i : Fin m, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) = 0 := by
    refine Polynomial.funext fun x => ?_
    simpa [Polynomial.eval_finset_sum] using DFunLike.congr_fun ha x
  simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Fin.val_inj, Finset.sum_ite_eq] using congrArg (fun p : Polynomial ℝ => p.coeff (j : ℕ)) hp

/-- 2A.20 -/
theorem exercise_2A_20 (m : ℕ) (p : Fin (m + 1) → Polynomial.degreeLT F (m + 1))
    (h : ∀ k, ((p k : Polynomial F).eval 2) = 0) :
    ¬ LinearIndependent F p := by
  -- by contra, assume LI, then they have to span all of V, because
  -- the list of 1, X, …, X^m span V and same length.
  -- thus the constant 1 is a linear combination of the p k, so 1 = ∑ a k p k, but then
  -- evaluating at 2 gives 1 = ∑ a k p k (2), but the right-hand side is zero, contradiction.
  intro hp
  -- "same length ⟹ spans": otherwise 2A.13 extends `p` to an LI list of length `m + 2`,
  -- beating the spanning list of `m + 1` monomials, which 2.22 forbids
  have hspan : Submodule.span F (Set.range p) = ⊤ := by
    by_contra hne
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    have hLI : LinearIndependent F (Fin.snoc p x) := (exercise_2A_13 _ _ hp).mpr hx
    have hle := linearIndependent_le_spanning _ _ hLI (degreeLT_monomials_spans (F := F) (m + 1))
    omega
  have hone : (1 : Polynomial F) ∈ Polynomial.degreeLT F (m + 1) := by
    rw [Polynomial.mem_degreeLT, Polynomial.degree_one]
    exact_mod_cast Nat.succ_pos m
  have hmem : (⟨1, hone⟩ : Polynomial.degreeLT F (m + 1)) ∈ Submodule.span F (Set.range p) := by
    rw [hspan]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hval := congrArg (fun q : Polynomial.degreeLT F (m + 1) => ((q : Polynomial F).eval 2)) hc
  simp [Polynomial.eval_finset_sum, Polynomial.smul_eq_C_mul, h] at hval

end LADR.Section_2A
