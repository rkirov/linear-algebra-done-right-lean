import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_1C
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3B: Null Spaces and Ranges
-/

namespace LADR.Section_3B

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open LADR.Section_1C (IsDirectSum)
open Module (Finite finrank)
open LinearMap (ker range)

variable {F : Type*} [Field F]
  {U V W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]

/-! 3.11 Definition: null space, {lit}`null T`

For {lit}`T ∈ ℒ(V, W)`, the null space is {lit}`{v ∈ V : T v = 0}`. In
mathlib this is {name}`LinearMap.ker`, which is a {name}`Submodule`. -/

example (T : V →ₗ[F] W) : Submodule F V := ker T

example (T : V →ₗ[F] W) (v : V) : v ∈ ker T ↔ T v = 0 :=
  LinearMap.mem_ker

/-! 3.12 Example: null space -/

/-! (a) For the zero map {lit}`V → W`, {lit}`null 0 = V`. -/
example : ker (0 : V →ₗ[F] W) = ⊤ := LinearMap.ker_zero

/-- (b) {lit}`φ ∈ ℒ(ℂ³, ℂ)` with {lit}`φ(z₁, z₂, z₃) = z₁ + 2z₂ + 3z₃`. -/
def phi_3_12 : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun z := z 0 + 2 * z 1 + 3 * z 2
  map_add' x y := by
    simp only [Pi.add_apply]; ring
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The null space of {lit}`φ` consists of triples {lit}`(z₁, z₂, z₃)` with
{lit}`z₁ + 2z₂ + 3z₃ = 0`. -/
example (z : Fin 3 → ℂ) :
    z ∈ ker phi_3_12 ↔ z 0 + 2 * z 1 + 3 * z 2 = 0 :=
  LinearMap.mem_ker

/-! (c) {lit}`D ∈ ℒ(𝒫(ℝ))` differentiation. {lit}`null D` = constants. We
record this membership statement (the full {lit}`ker = degreeLT ℝ 1`
equality is an exercise). -/

example (c : ℝ) :
    (Polynomial.C c : Polynomial ℝ) ∈ ker
      (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ) := by
  rw [LinearMap.mem_ker]; simp

/-! (d) Multiplication by {lit}`X²` has {lit}`null = {0}`. -/

example : ker LADR.Section_3A.multByXSq = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro p hp
  rw [LinearMap.mem_ker] at hp
  -- hp : multByXSq p = 0, i.e. X² * p = 0
  have hX2 : (Polynomial.X ^ 2 : Polynomial ℝ) * p = 0 := hp
  have hX : (Polynomial.X ^ 2 : Polynomial ℝ) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.coeff · 2) h
    simp [Polynomial.coeff_X_pow] at this
  exact (mul_eq_zero.mp hX2).resolve_left hX

/-! (e) Backward shift on {lit}`F^∞ = ℕ → F`: {lit}`null T = {x : ∀ i ≥ 1, x i = 0}`. -/

example (x : ℕ → F) :
    x ∈ ker (LADR.Section_3A.backwardShift (F := F)) ↔
    ∀ i, 1 ≤ i → x i = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h i hi
    have := congrFun h (i - 1)
    show x i = 0
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact this
  · intro h
    funext i
    show x (i + 1) = 0
    exact h (i + 1) (by omega)

/-! 3.13 The null space is a subspace

In mathlib, {name}`LinearMap.ker` already returns a {name}`Submodule`. -/

example (T : V →ₗ[F] W) : Submodule F V := ker T

/-- For illustration, here is the same fact built by hand: we exhibit
{lit}`{v : V | T v = 0}` as a {name}`Submodule` by checking the three subspace
axioms — closure under {lit}`0`, addition, and scalar multiplication. -/
example (T : V →ₗ[F] W) : Submodule F V where
  carrier := {v : V | T v = 0}
  zero_mem' := T.map_zero
  add_mem' := by
    intro a b ha hb
    show T (a + b) = 0
    rw [T.map_add, ha, hb, add_zero]
  smul_mem' := by
    intro c v hv
    show T (c • v) = 0
    rw [T.map_smul, hv, smul_zero]

/-! 3.14 Definition: injective -/

example (T : V → W) : Prop := Function.Injective T

omit [AddCommGroup V] [AddCommGroup W] in
/-- Axler's definition: {lit}`T` is injective when {lit}`T x = T y` implies
{lit}`x = y`. This is definitionally mathlib's {name}`Function.Injective`. -/
theorem injective_iff_axler (T : V → W) :
    Function.Injective T ↔ ∀ x y, T x = T y → x = y := Iff.rfl

/-! 3.15 {lit}`T` injective iff {lit}`null T = {0}` -/

@[avoiding LinearMap.ker_eq_bot]
theorem injective_iff_ker_eq_bot (T : V →ₗ[F] W) :
    Function.Injective T ↔ ker T = ⊥ := by
  constructor
  · intro hT
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have : T v = T 0 := by rw [hv, T.map_zero]
    exact hT this
  · intro hker u v huv
    have h : u - v ∈ ker T := by
      rw [LinearMap.mem_ker, T.map_sub, huv, sub_self]
    rw [hker, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h

/-! 3.16 Definition: range, {lit}`range T` -/

example (T : V →ₗ[F] W) : Submodule F W := range T

example (T : V →ₗ[F] W) (w : W) :
    w ∈ range T ↔ ∃ v : V, T v = w := LinearMap.mem_range

/-! 3.17 Example: range -/

/-! (a) Range of zero map. -/
example : range (0 : V →ₗ[F] W) = ⊥ := LinearMap.range_zero

/-- (b) {lit}`T ∈ ℒ(ℝ², ℝ³)` with {lit}`T(x, y) = (2x, 5y, x + y)`. -/
def T_3_17 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![2 * v 0, 5 * v 1, v 0 + v 1]
  map_add' x y := by
    funext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  map_smul' a x := by
    funext i; fin_cases i <;>
      simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-! Helpers shared between (c) below and the {lit}`𝒫₅ → 𝒫₄` example in 3.20. -/

/-- The antiderivative {lit}`∑ q.coeff k / (k+1) * X^(k+1)` of a real polynomial. -/
private noncomputable def antiderivative (q : Polynomial ℝ) : Polynomial ℝ :=
  q.sum (fun n a => Polynomial.C (a / (n + 1)) * Polynomial.X ^ (n + 1))

private lemma derivative_antiderivative (q : Polynomial ℝ) :
    Polynomial.derivative (antiderivative q) = q := by
  rw [antiderivative, Polynomial.sum_def, Polynomial.derivative_sum]
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq q, Polynomial.sum_def]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Polynomial.derivative_C_mul_X_pow]
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  congr 1
  rw [Polynomial.C_inj]
  field_simp

/-- Differentiation drops the degree by at least one: if {lit}`p.degree < m + 1`
then {lit}`(D p).degree < m`. -/
private lemma degree_derivative_lt_of_degree_lt {p : Polynomial ℝ} {m : ℕ}
    (hp : p.degree < (m + 1 : ℕ)) : (Polynomial.derivative p).degree < (m : ℕ) := by
  by_cases hp_const : p.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hp_const, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  by_cases hdp0 : Polynomial.derivative p = 0
  · rw [hdp0, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  have hp0 : p ≠ 0 := fun h => hp_const (by rw [h]; simp)
  have hp_lt : p.natDegree < m + 1 :=
    (Polynomial.natDegree_lt_iff_degree_lt (n := m + 1) hp0).mpr hp
  have hdp_lt : (Polynomial.derivative p).natDegree < p.natDegree :=
    Polynomial.natDegree_derivative_lt hp_const
  exact (Polynomial.natDegree_lt_iff_degree_lt (n := m) hdp0).mp (by omega)

/-- Antiderivative raises the degree-LT bound by one: if {lit}`q.degree < m`
then {lit}`antiderivative q ∈ degreeLT ℝ (m + 1)`. -/
private lemma antiderivative_mem_degreeLT (q : Polynomial ℝ) {m : ℕ}
    (hq : q.degree < (m : ℕ)) :
    antiderivative q ∈ Polynomial.degreeLT ℝ (m + 1) := by
  rw [antiderivative, Polynomial.sum_def]
  refine Submodule.sum_mem _ (fun k hk => ?_)
  rw [Polynomial.mem_degreeLT]
  have hk_q : (k : WithBot ℕ) ≤ q.degree := Polynomial.le_degree_of_mem_supp k hk
  have hk_lt : (k : ℕ) < m := by exact_mod_cast lt_of_le_of_lt hk_q hq
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast (by omega : (k + 1 : ℕ) < m + 1)

/-! (c) Range of differentiation on {lit}`𝒫(ℝ)` is all of {lit}`𝒫(ℝ)`. -/

example : range
    (Polynomial.derivative : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ) = ⊤ := by
  rw [LinearMap.range_eq_top]
  exact fun q => ⟨antiderivative q, derivative_antiderivative q⟩

/-! 3.18 The range is a subspace (mathlib's {name}`LinearMap.range` is a
{name}`Submodule`). -/

example (T : V →ₗ[F] W) : Submodule F W := range T

/-- For illustration, here is the same fact built by hand: {lit}`{w : W | ∃ v, T v = w}`
is a {name}`Submodule` by the three subspace axioms. -/
example (T : V →ₗ[F] W) : Submodule F W where
  carrier := {w : W | ∃ v : V, T v = w}
  zero_mem' := ⟨0, T.map_zero⟩
  add_mem' := by
    rintro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x + y, by rw [T.map_add, hx, hy]⟩
  smul_mem' := by
    rintro c w ⟨v, hv⟩
    exact ⟨c • v, by rw [T.map_smul, hv]⟩

/-! 3.19 Definition: surjective -/

example (T : V → W) : Prop := Function.Surjective T

omit [AddCommGroup V] [AddCommGroup W] in
/-- Axler's definition: {lit}`T` is surjective when every {lit}`w` has a
preimage. This is definitionally mathlib's {name}`Function.Surjective`. -/
theorem surjective_iff_axler (T : V → W) :
    Function.Surjective T ↔ ∀ w, ∃ v, T v = w := Iff.rfl

@[avoiding LinearMap.range_eq_top]
theorem surjective_iff_range_eq_top (T : V →ₗ[F] W) :
    Function.Surjective T ↔ range T = ⊤ := by
  constructor
  · intro hT
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, hv⟩ := hT w
    exact ⟨v, hv⟩
  · intro hT w
    have hw : w ∈ range T := by rw [hT]; exact Submodule.mem_top
    exact hw

/-! 3.20 Example: surjectivity depends on the target space.

We represent {lit}`𝒫ₘ(ℝ)` as {name}`Polynomial.degreeLT` {lit}`ℝ (m+1)` and
contrast {lit}`D : 𝒫₅(ℝ) → 𝒫₅(ℝ)` (not surjective) with
{lit}`D : 𝒫₅(ℝ) → 𝒫₄(ℝ)` (surjective). -/

/-- {lit}`D : 𝒫₅(ℝ) → 𝒫₅(ℝ)`, polynomial differentiation viewed as a map
from degree-{lit}`≤ 5` polynomials to themselves. -/
noncomputable def D55 :
    Polynomial.degreeLT ℝ 6 →ₗ[ℝ] Polynomial.degreeLT ℝ 6 :=
  LinearMap.codRestrict (Polynomial.degreeLT ℝ 6)
    (Polynomial.derivative.comp (Polynomial.degreeLT ℝ 6).subtype) (by
      rintro ⟨p, hp⟩
      rw [Polynomial.mem_degreeLT] at hp ⊢
      exact lt_trans (degree_derivative_lt_of_degree_lt hp)
        (by exact_mod_cast (by norm_num : (5 : ℕ) < 6)))

/-- {lit}`D : 𝒫₅(ℝ) → 𝒫₅(ℝ)` is not surjective. The polynomial {lit}`X⁵` lies
in {lit}`𝒫₅(ℝ)` but is not in the range: any preimage {lit}`p` has
{lit}`degree p < 6`, so {lit}`degree (D p) < 5`, but {lit}`X⁵` has degree
{lit}`5`. -/
example : ¬ Function.Surjective D55 := by
  intro hsurj
  let q : Polynomial.degreeLT ℝ 6 :=
    ⟨Polynomial.X ^ 5, by
      rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]
      exact_mod_cast (by norm_num : (5 : ℕ) < 6)⟩
  obtain ⟨p, hp⟩ := hsurj q
  have hp' : Polynomial.derivative (p : Polynomial ℝ) = Polynomial.X ^ 5 :=
    congrArg Subtype.val hp
  have hp_mem : (p : Polynomial ℝ).degree < (6 : ℕ) := by
    rw [← Polynomial.mem_degreeLT]; exact p.property
  have hdrop := degree_derivative_lt_of_degree_lt hp_mem
  rw [hp', Polynomial.degree_X_pow] at hdrop
  exact_mod_cast (lt_irrefl (5 : WithBot ℕ)) hdrop

/-- {lit}`D : 𝒫₅(ℝ) → 𝒫₄(ℝ)`, the same differentiation but with the codomain
restricted to {lit}`𝒫₄(ℝ)`. -/
noncomputable def D54 :
    Polynomial.degreeLT ℝ 6 →ₗ[ℝ] Polynomial.degreeLT ℝ 5 :=
  LinearMap.codRestrict (Polynomial.degreeLT ℝ 5)
    (Polynomial.derivative.comp (Polynomial.degreeLT ℝ 6).subtype) (by
      rintro ⟨p, hp⟩
      rw [Polynomial.mem_degreeLT] at hp ⊢
      exact degree_derivative_lt_of_degree_lt hp)

/-- {lit}`D : 𝒫₅(ℝ) → 𝒫₄(ℝ)` is surjective. Given {lit}`q ∈ 𝒫₄(ℝ)`, the
antiderivative lies in {lit}`𝒫₅(ℝ)` and maps to {lit}`q`. -/
example : Function.Surjective D54 := by
  rintro ⟨q, hq⟩
  rw [Polynomial.mem_degreeLT] at hq
  refine ⟨⟨antiderivative q, antiderivative_mem_degreeLT q hq⟩, ?_⟩
  exact Subtype.ext (derivative_antiderivative q)

/-! 3.21 Fundamental theorem of linear maps -/

@[avoiding LinearMap.finrank_range_add_finrank_ker]
theorem finrank_ker_add_finrank_range [Finite F V] (T : V →ₗ[F] W) :
    finrank F (ker T) + finrank F (range T) = finrank F V := by
  classical
  -- Basis u of null T.
  obtain ⟨m, u, hu_basis⟩ :=
    LADR.Section_2B.exists_basis (F := F) (V := ker T)
  have hm_ker : m = finrank F (ker T) :=
    LADR.Section_2C.isBasis_card_eq_finrank u hu_basis
  -- Lift u into V and extend to a basis of V.
  let uV : Fin m → V := fun i => (u i : V)
  have hu_li_V : LinearIndependent F uV :=
    hu_basis.1.map' (ker T).subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  obtain ⟨N, w, hmN, hw_basis, hw_prefix⟩ :=
    LADR.Section_2B.exists_basis_extending uV hu_li_V
  obtain ⟨n, rfl⟩ : ∃ n, N = m + n := ⟨N - m, by omega⟩
  have hmn_V : m + n = finrank F V :=
    LADR.Section_2C.isBasis_card_eq_finrank w hw_basis
  -- The extension piece v₁, …, v_n inside V.
  let vT : Fin n → V := fun j => w (Fin.natAdd m j)
  -- T v_j as an element of range T.
  let TvT : Fin n → range T :=
    fun j => ⟨T (vT j), LinearMap.mem_range_self T (vT j)⟩
  -- Prefix equality of w with uV.
  have hw_prefix_V : ∀ i : Fin m, (w (Fin.castAdd n i) : V) = uV i := by
    intro i
    have h := hw_prefix i
    have hfin : (Fin.castAdd n i : Fin (m + n)) = Fin.castLE hmN i := rfl
    rw [hfin, h]
  -- T u_i = 0 since u_i ∈ ker T.
  have hT_u : ∀ i, T (uV i) = 0 := by
    intro i
    have : uV i ∈ ker T := (u i).property
    rwa [LinearMap.mem_ker] at this
  -- (1) TvT spans range T.
  have hTvT_span : Spans F TvT := by
    rw [Spans, eq_top_iff]
    rintro ⟨y, hy⟩ _
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, hxy⟩ := hy
    -- Expand x in basis w.
    have hx_in : x ∈ Submodule.span F (Set.range w) := by
      rw [(hw_basis.2 : _ = ⊤)]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx_in
    obtain ⟨a, ha⟩ := hx_in
    -- Take aTail = a on the v-block.
    let aTail : Fin n → F := fun j => a (Fin.natAdd m j)
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨aTail, ?_⟩
    apply Subtype.ext
    show ((∑ j, aTail j • TvT j : range T) : W) = y
    rw [Submodule.coe_sum]
    show (∑ j, ((aTail j • TvT j : range T) : W)) = y
    have hcast : (∑ j, ((aTail j • TvT j : range T) : W)) =
        ∑ j, aTail j • T (vT j) :=
      Finset.sum_congr rfl (fun _ _ => rfl)
    rw [hcast, ← hxy, ← ha, map_sum]
    simp only [LinearMap.map_smul]
    rw [Fin.sum_univ_add (f := fun k => a k • T (w k))]
    -- u-block in T (a • w) sums to 0 because T u_i = 0.
    have h_uzero : ∑ i : Fin m,
        a (Fin.castAdd n i) • T (w (Fin.castAdd n i)) = (0 : W) := by
      apply Finset.sum_eq_zero
      intro i _
      rw [show (w (Fin.castAdd n i) : V) = uV i from hw_prefix_V i, hT_u i, smul_zero]
    rw [h_uzero, zero_add]
  -- (2) TvT is linearly independent.
  have hTvT_li : LinearIndependent F TvT := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    -- Lift the vanishing combination from range T to W.
    have hc_W : ∑ j, c j • T (vT j) = (0 : W) := by
      have hcv := congrArg Subtype.val hc
      rw [Submodule.coe_sum] at hcv
      have hsum : ∑ j, ((c j • TvT j : range T) : W) =
          ∑ j, c j • T (vT j) := Finset.sum_congr rfl (fun _ _ => rfl)
      rw [hsum] at hcv
      exact hcv
    -- So ∑ c j • v_j ∈ ker T.
    have hker : ∑ j, c j • vT j ∈ ker T := by
      rw [LinearMap.mem_ker, map_sum]
      simp only [LinearMap.map_smul]
      exact hc_W
    -- Express it in basis u of ker T.
    have hu_span : Submodule.span F (Set.range u) = ⊤ := hu_basis.2
    have hmem : (⟨∑ j, c j • vT j, hker⟩ : ker T) ∈
        Submodule.span F (Set.range u) := by
      rw [hu_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨d, hd⟩ := hmem
    -- Project hd into V.
    have hd_V : ∑ i, d i • uV i = ∑ j, c j • vT j := by
      have hd' := congrArg Subtype.val hd
      rw [Submodule.coe_sum] at hd'
      have hsum : ∑ i, ((d i • u i : ker T) : V) =
          ∑ i, d i • uV i := Finset.sum_congr rfl (fun _ _ => rfl)
      rw [hsum] at hd'
      exact hd'
    -- Build the combination cw of w which sums to 0.
    let cw : Fin (m + n) → F := Fin.append (-d) c
    have hcw_sum : ∑ k, cw k • w k = 0 := by
      rw [Fin.sum_univ_add (f := fun k => cw k • w k)]
      have hprefix : ∑ i : Fin m, cw (Fin.castAdd n i) • w (Fin.castAdd n i) =
          ∑ i, (-d i) • uV i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show cw (Fin.castAdd n i) = -d i from Fin.append_left _ _ _,
            show (w (Fin.castAdd n i) : V) = uV i from hw_prefix_V i]
      have htail : ∑ j : Fin n, cw (Fin.natAdd m j) • w (Fin.natAdd m j) =
          ∑ j, c j • vT j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show cw (Fin.natAdd m j) = c j from Fin.append_right _ _ _]
      rw [hprefix, htail]
      rw [show ∑ i, (-d i) • uV i = -∑ i, d i • uV i from by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by rw [neg_smul])]
      rw [hd_V, neg_add_cancel]
    -- LI of w kills all coefficients of cw.
    have hcw_zero := (Fintype.linearIndependent_iff.mp hw_basis.1) cw hcw_sum
    have hcw_j : c j = cw (Fin.natAdd m j) := (Fin.append_right (-d) c j).symm
    rw [hcw_j]
    exact hcw_zero _
  -- Conclude.
  have hn_range : n = finrank F (range T) :=
    LADR.Section_2C.isBasis_card_eq_finrank TvT ⟨hTvT_li, hTvT_span⟩
  omega

/-! 3.22 Linear map to a lower-dimensional space is not injective -/

@[avoiding LinearMap.exists_ne_zero_of_finrank_lt_of_finrank_lt]
theorem not_injective_of_finrank_lt [Finite F V] [Finite F W]
    (hWV : finrank F W < finrank F V) (T : V →ₗ[F] W) :
    ¬ Function.Injective T := by
  intro hinj
  rw [injective_iff_ker_eq_bot] at hinj
  have hker : finrank F (ker T) = 0 := by rw [hinj]; simp
  have hrange_le : finrank F (range T) ≤ finrank F W :=
    LADR.Section_2C.finrank_submodule_le (range T)
  have := finrank_ker_add_finrank_range T
  omega

/-! 3.23 Example: a linear map {lit}`F⁴ → F³` is not injective. -/

example (T : (Fin 4 → F) →ₗ[F] (Fin 3 → F)) : ¬ Function.Injective T :=
  not_injective_of_finrank_lt (by simp) T

/-! 3.24 Linear map to a higher-dimensional space is not surjective -/

theorem not_surjective_of_finrank_lt [Finite F V] [Finite F W]
    (hVW : finrank F V < finrank F W) (T : V →ₗ[F] W) :
    ¬ Function.Surjective T := by
  intro hsurj
  rw [surjective_iff_range_eq_top] at hsurj
  have hrange : finrank F (range T) = finrank F W := by
    rw [hsurj]
    exact Submodule.topEquiv.finrank_eq
  have hker_le : 0 ≤ finrank F (ker T) := Nat.zero_le _
  have := finrank_ker_add_finrank_range T
  omega

/-! 3.25/3.26 Homogeneous system of linear equations with more variables than
equations has nonzero solutions.

Axler devotes considerable space (3.25, 3.26, and surrounding discussion) to
turning a matrix {lit}`A` into the linear map {lit}`x ↦ (∑ k, A j k * x k)ⱼ`
and arguing that its kernel encodes solutions of the homogeneous system. We
already did that translation once in {name}`LADR.Section_3A.fromFnToFm`, so
both 3.25/3.26 and 3.27/3.28 below just apply the abstract finrank theorems
to that map. -/

theorem homogeneous_system_nonzero_solution {m n : ℕ} (hmn : m < n)
    (A : Fin m → Fin n → F) :
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ j : Fin m, ∑ k, A j k * x k = 0 := by
  let T : (Fin n → F) →ₗ[F] (Fin m → F) := LADR.Section_3A.fromFnToFm A
  have hT : ¬ Function.Injective T :=
    not_injective_of_finrank_lt (by simpa using hmn) T
  rw [injective_iff_ker_eq_bot] at hT
  have hne : ker T ≠ ⊥ := hT
  obtain ⟨x, hx_ker, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨x, hx_ne, ?_⟩
  intro j
  have hTx : T x = 0 := hx_ker
  have := congrFun hTx j
  show ∑ k, A j k * x k = 0
  exact this

/-! 3.27/3.28 A system of linear equations with more equations than variables
has no solution for some choice of constant terms. -/

theorem more_equations_no_solution {m n : ℕ} (hmn : n < m) (A : Fin m → Fin n → F) :
    ∃ c : Fin m → F, ¬ ∃ x : Fin n → F, ∀ j : Fin m, ∑ k, A j k * x k = c j := by
  let T : (Fin n → F) →ₗ[F] (Fin m → F) := LADR.Section_3A.fromFnToFm A
  have hT : ¬ Function.Surjective T :=
    not_surjective_of_finrank_lt (by simpa using hmn) T
  rw [Function.Surjective] at hT
  push Not at hT
  obtain ⟨c, hc⟩ := hT
  refine ⟨c, ?_⟩
  rintro ⟨x, hx⟩
  exact hc x (funext hx)

/-! # Exercises -/

/-- 3B.1 -/
theorem exercise_3B_1 :
    ∃ (V W : Type) (_ : AddCommGroup V) (_ : Module ℝ V)
      (_ : AddCommGroup W) (_ : Module ℝ W) (T : V →ₗ[ℝ] W),
      finrank ℝ (ker T) = 3 ∧ finrank ℝ (range T) = 2 := by
  sorry

/-- 3B.2 -/
theorem exercise_3B_2 (S T : V →ₗ[F] V)
    (h : range S ≤ ker T) :
    (S ∘ₗ T) ∘ₗ (S ∘ₗ T) = 0 := by
  sorry

/-- 3B.3 The linear map {lit}`T(z₁, …, zₘ) = z₁ v₁ + ⋯ + zₘ vₘ`. -/
def exercise_3B_3_T {m : ℕ} (v : Fin m → V) : (Fin m → F) →ₗ[F] V where
  toFun z := ∑ i, z i • v i
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by rw [Pi.add_apply, add_smul])
  map_smul' a x := by
    show ∑ i, (a • x) i • v i = a • ∑ i, x i • v i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- 3B.3 (a) {lit}`v` spans {lit}`V` iff the corresponding {lit}`T` is
surjective. Needs a proof. -/
theorem exercise_3B_3a {m : ℕ} (v : Fin m → V) :
    Spans F v ↔ Function.Surjective (exercise_3B_3_T (F := F) v) := by
  sorry

/-- 3B.3 (b) {lit}`v` is linearly independent iff the corresponding {lit}`T`
is injective. Needs a proof. -/
theorem exercise_3B_3b {m : ℕ} (v : Fin m → V) :
    LinearIndependent F v ↔ Function.Injective (exercise_3B_3_T (F := F) v) := by
  sorry

/-- 3B.4 -/
theorem exercise_3B_4 :
    ¬ ∃ (U : Submodule ℝ ((Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))),
      ∀ T : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ),
        T ∈ U ↔ 2 < finrank ℝ (ker T) := by
  sorry

/-- 3B.5 -/
theorem exercise_3B_5 :
    ∃ T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ), range T = ker T := by
  sorry

/-- 3B.6 -/
theorem exercise_3B_6 :
    ¬ ∃ T : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ), range T = ker T := by
  sorry

/-- 3B.7 -/
theorem exercise_3B_7 [Finite F V] [Finite F W]
    (hVW : 2 ≤ finrank F V) (hWV : finrank F V ≤ finrank F W) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] W)),
      ∀ T : V →ₗ[F] W, T ∈ U ↔ ¬ Function.Injective T := by
  sorry

/-- 3B.8 -/
theorem exercise_3B_8 [Finite F V] [Finite F W]
    (hVW : finrank F V ≥ finrank F W) (hW : 2 ≤ finrank F W) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] W)),
      ∀ T : V →ₗ[F] W, T ∈ U ↔ ¬ Function.Surjective T := by
  sorry

/-- 3B.9 -/
theorem exercise_3B_9 (T : V →ₗ[F] W) (hT : Function.Injective T)
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent F v) :
    LinearIndependent F (fun i => T (v i)) := by
  sorry

/-- 3B.10 -/
theorem exercise_3B_10 {n : ℕ} (v : Fin n → V) (hv : Spans F v)
    (T : V →ₗ[F] W) :
    Submodule.span F (Set.range (fun i => T (v i))) = range T := by
  sorry

/-- 3B.11

{lit}`Submodule.map T U` is the image of the submodule {lit}`U ⊆ V` under
{lit}`T`, packaged as a submodule of {lit}`W` (mathlib bundles the
closure-under-{lit}`+`/{lit}`•` proofs into the definition, so it is
automatically a submodule). Underlying set: {lit}`T '' U = {T u | u ∈ U}`. -/
theorem exercise_3B_11 [Finite F V] (T : V →ₗ[F] W) :
    ∃ U : Submodule F V, U ⊓ ker T = ⊥ ∧
      range T = Submodule.map T U := by
  sorry

/-- 3B.12 -/
theorem exercise_3B_12 (T : (Fin 4 → F) →ₗ[F] (Fin 2 → F))
    (h : ∀ x : Fin 4 → F,
      x ∈ ker T ↔ x 0 = 5 * x 1 ∧ x 2 = 7 * x 3) :
    Function.Surjective T := by
  sorry

/-- 3B.13 -/
theorem exercise_3B_13 (U : Submodule ℝ (Fin 8 → ℝ)) (hU : finrank ℝ U = 3)
    (T : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ)) (hker : ker T = U) :
    Function.Surjective T := by
  sorry

/-- 3B.14 -/
theorem exercise_3B_14 :
    ¬ ∃ T : (Fin 5 → F) →ₗ[F] (Fin 2 → F), ∀ x : Fin 5 → F,
      x ∈ ker T ↔ x 0 = 3 * x 1 ∧ x 2 = x 3 ∧ x 3 = x 4 := by
  sorry

/-- 3B.15 -/
theorem exercise_3B_15 (T : V →ₗ[F] V)
    (hker : Finite F (ker T)) (hrange : Finite F (range T)) :
    Finite F V := by
  sorry

/-- 3B.16 -/
theorem exercise_3B_16 [Finite F V] [Finite F W] :
    (∃ T : V →ₗ[F] W, Function.Injective T) ↔ finrank F V ≤ finrank F W := by
  sorry

/-- 3B.17 -/
theorem exercise_3B_17 [Finite F V] [Finite F W] :
    (∃ T : V →ₗ[F] W, Function.Surjective T) ↔ finrank F V ≥ finrank F W := by
  sorry

/-- 3B.18 -/
theorem exercise_3B_18 [Finite F V] [Finite F W] (U : Submodule F V) :
    (∃ T : V →ₗ[F] W, ker T = U) ↔
      finrank F V - finrank F W ≤ finrank F U := by
  sorry

/-- 3B.19 -/
theorem exercise_3B_19 [Finite F W] (T : V →ₗ[F] W) :
    Function.Injective T ↔
      ∃ S : W →ₗ[F] V, S ∘ₗ T = LinearMap.id := by
  sorry

/-- 3B.20 -/
theorem exercise_3B_20 [Finite F W] (T : V →ₗ[F] W) :
    Function.Surjective T ↔
      ∃ S : W →ₗ[F] V, T ∘ₗ S = LinearMap.id := by
  sorry

/-- 3B.21.a — preimage of a subspace is a subspace.

Axler states 3.21 assuming the preimage {lit}`{v ∈ V | T v ∈ U}` is a
subspace. Mathlib bundles this fact into {lit}`Submodule.comap T U`, whose
underlying set is exactly that preimage. This exercise asks for the proof
of the closure properties without appealing to {lit}`Submodule.comap`. -/
theorem exercise_3B_21_a (T : V →ₗ[F] W) (Usub : Submodule F W) :
    (0 : V) ∈ {v : V | T v ∈ Usub} ∧
    (∀ u v : V, u ∈ {v : V | T v ∈ Usub} → v ∈ {v : V | T v ∈ Usub} →
      u + v ∈ {v : V | T v ∈ Usub}) ∧
    (∀ (c : F) (v : V), v ∈ {v : V | T v ∈ Usub} →
      c • v ∈ {v : V | T v ∈ Usub}) := by
  sorry

/-- 3B.21.b

{lit}`Submodule.comap T Usub` is the preimage {lit}`{v ∈ V | T v ∈ Usub}`
bundled as a submodule of {lit}`V` (mathlib packages the closure proofs
from 3B.21.a into the definition). -/
theorem exercise_3B_21_b [Finite F V] (T : V →ₗ[F] W) (Usub : Submodule F W) :
    finrank F (Submodule.comap T Usub) =
      finrank F (ker T) +
        finrank F ((Usub ⊓ range T : Submodule F W)) := by
  sorry

/-- 3B.22 -/
theorem exercise_3B_22 [Finite F U] [Finite F V]
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    finrank F (ker (S ∘ₗ T)) ≤
      finrank F (ker S) + finrank F (ker T) := by
  sorry

/-- 3B.23 -/
theorem exercise_3B_23 [Finite F U] [Finite F V]
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    finrank F (range (S ∘ₗ T)) ≤ min (finrank F (range S))
      (finrank F (range T)) := by
  sorry

/-- 3B.24 (a) -/
theorem exercise_3B_24a [Finite F V] (hV : finrank F V = 5)
    (S T : V →ₗ[F] V) (hST : S ∘ₗ T = 0) :
    finrank F (range (T ∘ₗ S)) ≤ 2 := by
  sorry

/-- 3B.24 (b) -/
theorem exercise_3B_24b :
    ∃ S T : (Fin 5 → F) →ₗ[F] (Fin 5 → F),
      S ∘ₗ T = 0 ∧ finrank F (range (T ∘ₗ S)) = 2 := by
  sorry

/-- 3B.25 -/
theorem exercise_3B_25 [Finite F W] (S T : V →ₗ[F] W) :
    ker S ≤ ker T ↔
      ∃ E : W →ₗ[F] W, T = E ∘ₗ S := by
  sorry

/-- 3B.26 -/
theorem exercise_3B_26 [Finite F V] (S T : V →ₗ[F] W) :
    range S ≤ range T ↔
      ∃ E : V →ₗ[F] V, S = T ∘ₗ E := by
  sorry

/-- 3B.27 -/
theorem exercise_3B_27 (P : V →ₗ[F] V) (hP : P ∘ₗ P = P) :
    IsCompl (ker P) (range P) := by
  sorry

/-- 3B.28 — Axler's "nonconstant" condition is {lit}`0 < p.degree`, and
{lit}`deg (D p) = deg p - 1` is written as {lit}`(D p).degree + 1 = p.degree`
since {lit}`WithBot ℕ` has no subtraction. We use {name}`Polynomial.degree`
(with {lit}`deg 0 = ⊥`, so {lit}`⊥ + 1 = ⊥`) rather than
{name}`Polynomial.natDegree`: with {lit}`natDegree`, the hypothesis would allow
{lit}`D p = 0` for {lit}`deg p = 1` (both sides {lit}`0`), and then
{lit}`D 1 = D X = 0`, {lit}`D Xᵏ = Xᵏ⁻¹` for {lit}`k ≥ 2` satisfies it but
misses the constants, so the statement would be false. -/
theorem exercise_3B_28 (D : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
    (hD : ∀ p : Polynomial ℝ, 0 < p.degree →
      (D p).degree + 1 = p.degree) :
    Function.Surjective D := by
  sorry

/-- 3B.29 -/
theorem exercise_3B_29 (p : Polynomial ℝ) :
    ∃ q : Polynomial ℝ,
      (5 : ℝ) • q.derivative.derivative + (3 : ℝ) • q.derivative = p := by
  sorry

/-- 3B.30 -/
theorem exercise_3B_30 (φ : V →ₗ[F] F) (_hφ : φ ≠ 0) (u : V)
    (hu : φ u ≠ 0) :
    IsCompl (ker φ)
      (Submodule.span F ({u} : Set V)) := by
  sorry

/-- 3B.31 — the book assumes {lit}`Y` is a finite-dimensional subspace of
{lit}`W`; without {lit}`[Finite F Y]` the statement is false (for {lit}`X = V`
and {lit}`Y` infinite-dimensional, {lit}`finrank F Y = 0` makes the equation
hold, but {lit}`ker T = V` forces {lit}`range T = 0 ≠ Y`). -/
theorem exercise_3B_31 [Finite F V] (X : Submodule F V) (Y : Submodule F W) [Finite F Y] :
    (∃ T : V →ₗ[F] W,
      ker T = X ∧ range T = Y) ↔
    finrank F X + finrank F Y = finrank F V := by
  sorry

/-- 3B.32 -/
theorem exercise_3B_32 [Finite F V] (hV : 1 < finrank F V)
    (φ : (V →ₗ[F] V) →ₗ[F] F)
    (hφ : ∀ S T : V →ₗ[F] V, φ (S ∘ₗ T) = φ S * φ T) :
    φ = 0 := by
  sorry

open LADR.Section_1B (Complexification exercise_1B_8) in
/-- 3B.33.a — complexification of a real linear map, the map itself. -/
noncomputable def complexification_map {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : V →ₗ[ℝ] W) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    letI : Module ℂ (Complexification W) := exercise_1B_8 W
    Complexification V →ₗ[ℂ] Complexification W :=
  letI : Module ℂ (Complexification V) := exercise_1B_8 V
  letI : Module ℂ (Complexification W) := exercise_1B_8 W
  { toFun := fun p => (T p.1, T p.2)
    map_add' := by sorry
    map_smul' := by sorry }

open LADR.Section_1B (Complexification exercise_1B_8) in
/-- 3B.33.b — the complexification is injective iff {lit}`T` is. -/
theorem exercise_3B_33_b {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] W) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    letI : Module ℂ (Complexification W) := exercise_1B_8 W
    Function.Injective (complexification_map T) ↔ Function.Injective T := by
  sorry

open LADR.Section_1B (Complexification exercise_1B_8) in
/-- 3B.33.c — the complexification is surjective iff {lit}`T` is. -/
theorem exercise_3B_33_c {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] W) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    letI : Module ℂ (Complexification W) := exercise_1B_8 W
    Function.Surjective (complexification_map T) ↔ Function.Surjective T := by
  sorry

end LADR.Section_3B
