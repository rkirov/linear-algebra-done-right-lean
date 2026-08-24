import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
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

example (m : ℕ) [Infinite F] :
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
process terminates; maximality then forces the final list to span {lit}`U`.

The translation uses {name}`linearIndependent_le_spanning` (our 2.22) for the
bound; the LI-extension step — appending a vector outside the span of a linearly
independent list keeps it linearly independent, which Axler gets from the linear
dependence lemma {name}`linearDependence_lemma` (2.19) — is proved inline below,
so this example depends on no exercise. -/

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
  sorry

/-- 2A.2 *Prove or counterexample.* If {lit}`v₁, v₂, v₃, v₄` spans {lit}`V`, does
{lit}`v₁ - v₂, v₂ - v₃, v₃ - v₄, v₄` span {lit}`V`? -/
def exercise_2A_2 (v : Fin 4 → V) : Decidable (Spans F v →
    Spans F (![v 0 - v 1, v 1 - v 2, v 2 - v 3, v 3] : Fin 4 → V)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 2A.3 -/
theorem exercise_2A_3 {m : ℕ} (v : Fin m → V) :
    Submodule.span F (Set.range v) =
      Submodule.span F (Set.range (fun k : Fin m => ∑ i : Fin (k + 1), v ⟨i, by omega⟩)) := by
  sorry

/-- 2A.4(a) -/
theorem exercise_2A_4a (v : V) : LinearIndependent F (![v] : Fin 1 → V) ↔ v ≠ 0 := by
  sorry

/-- 2A.4(b) -/
theorem exercise_2A_4b (v w : V) : LinearIndependent F (![v, w] : Fin 2 → V) ↔
    (∀ a : F, w ≠ a • v) ∧ (∀ b : F, v ≠ b • w) := by
  sorry

/-- 2A.5 Find {lit}`t ∈ ℝ` such that the list is *not* linearly independent. -/
theorem exercise_2A_5 :
    ∃ t : ℝ, ¬ LinearIndependent ℝ
      (![![3, 1, 4], ![2, -3, 5], ![5, 9, t]] : Fin 3 → Fin 3 → ℝ) := by
  sorry

/-- 2A.6 The field is assumed {name}`CharZero`: the {lit}`3 × 3` determinant is
{lit}`-5 (c - 8)`, so in characteristic {lit}`5` the list is dependent for every
{lit}`c` and the equivalence fails. -/
theorem exercise_2A_6 [CharZero F] (c : F) :
    ¬ LinearIndependent F (![![2, 3, 1], ![1, -1, 2], ![7, 3, c]] : Fin 3 → Fin 3 → F) ↔
      c = 8 := by
  sorry

/-- 2A.7(a) Over {lit}`ℝ`, the list {lit}`1+i, 1-i` is linearly independent in
{lit}`ℂ` (viewed as an {lit}`ℝ`-vector space). -/
theorem exercise_2A_7a :
    LinearIndependent ℝ (![(1 + Complex.I), (1 - Complex.I)] : Fin 2 → ℂ) := by
  sorry

/-- 2A.7(b) Over {lit}`ℂ`, the same list is linearly dependent. -/
theorem exercise_2A_7b :
    ¬ LinearIndependent ℂ (![(1 + Complex.I), (1 - Complex.I)] : Fin 2 → ℂ) := by
  sorry

/-- 2A.8 -/
theorem exercise_2A_8 (v : Fin 4 → V) (h : LinearIndependent F v) :
    LinearIndependent F (![v 0 - v 1, v 1 - v 2, v 2 - v 3, v 3] : Fin 4 → V) := by
  sorry

/-- 2A.9 The field is assumed {name}`CharZero`: in characteristic {lit}`5` one has
{lit}`5 • v 0 - 4 • v 1 = v 1`, so for {lit}`m ≥ 1` the updated list repeats
{lit}`v 1` and is dependent. -/
def exercise_2A_9 [CharZero F] :
    Decidable (∀ {m : ℕ} (v : Fin (m + 1) → V) (_ : LinearIndependent F v),
      LinearIndependent F (Function.update v 0 ((5 : F) • v 0 - (4 : F) • v 1))) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 2A.10 -/
def exercise_2A_10 :
    Decidable (∀ {m : ℕ} (v : Fin m → V) (γ : F) (_ : γ ≠ 0)
      (_ : LinearIndependent F v), LinearIndependent F (fun i => γ • v i)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

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
  sorry

/-- 2A.12 -/
theorem exercise_2A_12 {m : ℕ} (v : Fin m → V) (w : V)
    (hv : LinearIndependent F v)
    (hvw : ¬ LinearIndependent F (fun i => v i + w)) :
    w ∈ Submodule.span F (Set.range v) := by
  sorry

/-- 2A.13 -/
theorem exercise_2A_13 {m : ℕ} (v : Fin m → V) (w : V) (hv : LinearIndependent F v) :
    LinearIndependent F (Fin.snoc v w : Fin (m + 1) → V) ↔
      w ∉ Submodule.span F (Set.range v) := by
  sorry

/-- 2A.14 -/
theorem exercise_2A_14 {m : ℕ} (v : Fin m → V) :
    LinearIndependent F v ↔
      LinearIndependent F (fun k : Fin m => ∑ i : Fin (k + 1), v ⟨i, by omega⟩) := by
  sorry

/-- 2A.15 -/
theorem exercise_2A_15 :
    ¬ ∃ v : Fin 6 → Polynomial.degreeLT ℝ 5, LinearIndependent ℝ v := by
  sorry

/-- 2A.16 -/
theorem exercise_2A_16 :
    ¬ ∃ v : Fin 4 → Polynomial.degreeLT ℝ 5,
      Spans ℝ v := by
  sorry

/-- 2A.17 -/
theorem exercise_2A_17 :
    ¬ Module.Finite F V ↔
      ∃ v : ℕ → V, ∀ m : ℕ, LinearIndependent F (fun i : Fin m => v i) := by
  sorry

/-- 2A.18 {lit}`F^∞` is infinite-dimensional. -/
theorem exercise_2A_18 : ¬ Module.Finite F (ℕ → F) := by
  sorry

/-- 2A.19 The real vector space of all continuous real-valued functions on
{lit}`[0, 1]` is infinite-dimensional. We follow the convention of 1.35(b)
and use {lit}`C(ℝ, ℝ)` (continuous functions on all of {lit}`ℝ`); the same
argument works on {lit}`C(Set.Icc 0 1, ℝ)`. -/
theorem exercise_2A_19 :
    ¬ Module.Finite ℝ C(ℝ, ℝ) := by
  sorry

/-- 2A.20 -/
theorem exercise_2A_20 (m : ℕ) (p : Fin (m + 1) → Polynomial.degreeLT F (m + 1))
    (h : ∀ k, ((p k : Polynomial F).eval 2) = 0) :
    ¬ LinearIndependent F p := by
  sorry

end LADR.Section_2A
