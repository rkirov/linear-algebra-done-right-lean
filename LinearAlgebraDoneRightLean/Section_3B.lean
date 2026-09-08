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
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
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
  refine ⟨Fin 5 → ℝ, Fin 2 → ℝ, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  -- T (x₀, …, x₄) = (x₀, x₁)
  let T : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun v => ![v 0, v 1]
      map_add' := fun x y => by funext i; fin_cases i <;> simp
      map_smul' := fun a x => by funext i; fin_cases i <;> simp }
  have hrange : range T = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro w
    refine ⟨![w 0, w 1, 0, 0, 0], ?_⟩
    funext i; fin_cases i <;> rfl
  have hr : finrank ℝ (range T) = 2 := by
    rw [hrange, finrank_top, Module.finrank_fin_fun]
  -- rank–nullity gives dim null T = 5 - 2 = 3
  have h := LinearMap.finrank_range_add_finrank_ker T
  rw [hr, Module.finrank_fin_fun] at h
  exact ⟨T, by omega, hr⟩

/-- 3B.2 -/
theorem exercise_3B_2 (S T : V →ₗ[F] V)
    (h : range S ≤ ker T) :
    (S ∘ₗ T) ∘ₗ (S ∘ₗ T) = 0 := by
  -- (ST)² = S (TS) T and TS = 0
  suffices h' : T ∘ₗ S = 0 by
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc T, h', LinearMap.zero_comp,
      LinearMap.comp_zero]
  ext x
  exact LinearMap.mem_ker.mp (h (LinearMap.mem_range_self S x))

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
surjective. -/
theorem exercise_3B_3a {m : ℕ} (v : Fin m → V) :
    Spans F v ↔ Function.Surjective (exercise_3B_3_T (F := F) v) := by
  constructor
  · -- ⇒ every w is ∑ aᵢ vᵢ = T a, so T is surjective
    intro hspan w
    have hw : w ∈ Submodule.span F (Set.range v) := hspan ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hw
    exact ⟨a, ha⟩
  · -- ⇐ every w is some T a = ∑ aᵢ vᵢ, so v spans V
    intro hsurj
    rw [Spans, eq_top_iff]
    intro w _
    obtain ⟨a, rfl⟩ := hsurj w
    exact (Submodule.mem_span_range_iff_exists_fun F).mpr ⟨a, rfl⟩

/-- 3B.3 (b) {lit}`v` is linearly independent iff the corresponding {lit}`T`
is injective. -/
theorem exercise_3B_3b {m : ℕ} (v : Fin m → V) :
    LinearIndependent F v ↔ Function.Injective (exercise_3B_3_T (F := F) v) := by
  -- both sides say: ∑ aᵢ vᵢ = 0 → a = 0
  rw [Fintype.linearIndependent_iff, injective_iff_map_eq_zero]
  constructor
  · intro hli a ha
    funext i
    exact hli a ha i
  · intro hinj a ha i
    rw [hinj a ha]
    rfl

/-- 3B.4 -/
theorem exercise_3B_4 :
    ¬ ∃ (U : Submodule ℝ ((Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))),
      ∀ T : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ),
        T ∈ U ↔ 2 < finrank ℝ (ker T) := by
  rintro ⟨U, hU⟩
  -- T x = (x₀, x₁, 0, 0) and S x = (0, 0, x₃, x₄); both have 3-dimensional null
  -- space, but T + S is surjective, so null (T + S) is 1-dimensional.
  -- Each is written as (embed into ℝ⁴) ∘ (surjection onto ℝ²).
  let P : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.funLeft ℝ ℝ (Fin.castLE (by norm_num))
  let P' : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := LinearMap.funLeft ℝ ℝ (Fin.natAdd 3)
  let ι : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) := LinearMap.pi ![LinearMap.proj 0, LinearMap.proj 1, 0, 0]
  let ι' : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) := LinearMap.pi ![0, 0, LinearMap.proj 0, LinearMap.proj 1]
  have hker : ∀ Q : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), Function.Surjective Q →
      finrank ℝ (ker Q) = 3 := by
    intro Q hQ
    have h := LinearMap.finrank_range_add_finrank_ker Q
    rw [LinearMap.range_eq_top.mpr hQ, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h
    omega
  have hP : finrank ℝ (ker P) = 3 :=
    hker P (LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective _))
  have hP' : finrank ℝ (ker P') = 3 :=
    hker P' (LinearMap.funLeft_surjective_of_injective _ _ _ fun a b h =>
      Fin.ext (by simpa using congrArg Fin.val h))
  have hT : ι ∘ₗ P ∈ U := (hU _).mpr (by
    have := Submodule.finrank_mono (LinearMap.ker_le_ker_comp P ι); omega)
  have hS : ι' ∘ₗ P' ∈ U := (hU _).mpr (by
    have := Submodule.finrank_mono (LinearMap.ker_le_ker_comp P' ι'); omega)
  have hTS := (hU _).mp (U.add_mem hT hS)
  have hsurj : Function.Surjective (ι ∘ₗ P + ι' ∘ₗ P') := by
    intro w
    refine ⟨![w 0, w 1, 0, w 2, w 3], ?_⟩
    funext i
    fin_cases i <;> simp [ι, ι', P, P', LinearMap.funLeft_apply, Fin.natAdd]
  have h := LinearMap.finrank_range_add_finrank_ker (ι ∘ₗ P + ι' ∘ₗ P')
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at h
  omega

/-- 3B.5 -/
theorem exercise_3B_5 :
    ∃ T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ), range T = ker T := by
  -- T (x₀, x₁, x₂, x₃) = (x₂, x₃, 0, 0); range and null space are both
  -- {(a, b, 0, 0)}
  refine ⟨LinearMap.pi ![LinearMap.proj 2, LinearMap.proj 3, 0, 0], ?_⟩
  ext x
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    funext i
    fin_cases i <;> simp
  · intro hx
    have h2 : x 2 = 0 := by simpa using congrFun hx 0
    have h3 : x 3 = 0 := by simpa using congrFun hx 1
    refine ⟨![0, 0, x 0, x 1], ?_⟩
    funext i
    fin_cases i <;> simp [h2, h3]

/-- 3B.6 -/
theorem exercise_3B_6 :
    ¬ ∃ T : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ), range T = ker T := by
  -- rank–nullity: dim range T + dim null T = 5, so 2 · dim null T = 5
  rintro ⟨T, hT⟩
  have h := LinearMap.finrank_range_add_finrank_ker T
  rw [hT, Module.finrank_fin_fun] at h
  omega

/-- 3B.7 -/
theorem exercise_3B_7 [Finite F V] [Finite F W]
    (hVW : 2 ≤ finrank F V) (hWV : finrank F V ≤ finrank F W) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] W)),
      ∀ T : V →ₗ[F] W, T ∈ U ↔ ¬ Function.Injective T := by
  rintro ⟨U, hU⟩
  -- Pick bases b of V and c of W and an injective ι : V → W sending bᵢ ↦ cᵢ.
  -- Use Q₀ (v i) = 0 if i ≠ 0 and Q₀ (v 0) = v 0
  -- Use Q₁ (v i) = ι (v i) if i ≠ 0 and Q₁ (v 0) = 0
  -- Q₁ + Q₀ (v i) = ι (v i) for all i, so Q₁ + Q₀ = ι is injective.
  let b := Module.finBasis F V
  let c := Module.finBasis F W
  let w : Fin (finrank F V) → W := fun i => c (Fin.castLE hWV i)
  have hw : LinearIndependent F w := c.linearIndependent.comp _ (Fin.castLE_injective hWV)
  let ι : V →ₗ[F] W := b.constr F w
  have hι : Function.Injective ι := by
    have : ι = Fintype.linearCombination F w ∘ₗ b.equivFun.toLinearMap := by
      ext x
      simp [ι, Module.Basis.constr_apply_fintype, Fintype.linearCombination_apply]
    rw [this]
    exact hw.fintypeLinearCombination_injective.comp b.equivFun.injective
  let i0 : Fin (finrank F V) := ⟨0, by omega⟩
  let i1 : Fin (finrank F V) := ⟨1, by omega⟩
  let Q₀ : V →ₗ[F] W := b.constr F fun i => if i = i0 then ι (b i) else 0
  let Q₁ : V →ₗ[F] W := b.constr F fun i => if i = i0 then 0 else ι (b i)
  have hQ₀ : Q₀ ∈ U := by
    -- Q₀ (b 1) = 0 = Q₀ 0, but b 1 ≠ 0
    rw [hU]
    intro hinj
    apply b.ne_zero i1
    apply hinj
    simp only [Q₀, Module.Basis.constr_basis, map_zero]
    simp [i0, i1]
  have hQ₁ : Q₁ ∈ U := by
    -- Q₁ (b 0) = 0 = Q₁ 0, but b 0 ≠ 0
    rw [hU]
    intro hinj
    apply b.ne_zero i0
    apply hinj
    simp only [Q₁, Module.Basis.constr_basis, map_zero]
    simp
  have hsum : Q₁ + Q₀ = ι := by
    apply b.ext
    intro i
    simp only [LinearMap.add_apply, Q₀, Q₁, Module.Basis.constr_basis]
    split_ifs <;> simp
  exact (hU _).mp (U.add_mem hQ₁ hQ₀) (hsum ▸ hι)

/-- 3B.8 -/
theorem exercise_3B_8 [Finite F V] [Finite F W]
    (hVW : finrank F V ≥ finrank F W) (hW : 2 ≤ finrank F W) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] W)),
      ∀ T : V →ₗ[F] W, T ∈ U ↔ ¬ Function.Surjective T := by
  rintro ⟨U, hU⟩
  -- Pick bases b of V and c of W and an surjective π : V → W sending bᵢ ↦ cᵢ.
  -- Use Q₀ (v i) = 0 if i ≠ 0 and Q₀ (v 0) = v 0
  -- Use Q₁ (v i) = ι (v i) if i ≠ 0 and Q₁ (v 0) = 0
  -- Q₁ + Q₀ (v i) = ι (v i) for all π (i.e., for all basis vectors), so Q₁ + Q₀ = ι is surjective.
  let b := Module.finBasis F V
  let c := Module.finBasis F W
  let m := finrank F W
  -- π bᵢ = cᵢ for i < dim W and π bᵢ = 0 otherwise
  let π : V →ₗ[F] W := b.constr F fun i => if h : i.val < m then c ⟨i, h⟩ else 0
  have hπb : ∀ j : Fin m, π (b (Fin.castLE hVW j)) = c j := by
    intro j
    simp only [π, Module.Basis.constr_basis]
    simp
    exact fun h => absurd j.isLt (not_lt.mpr h)
  have hπ : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← c.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨b (Fin.castLE hVW j), hπb j⟩
  let i0 : Fin (finrank F V) := ⟨0, by omega⟩
  let j0 : Fin m := ⟨0, by omega⟩
  let j1 : Fin m := ⟨1, by omega⟩
  let Q₀ : V →ₗ[F] W := b.constr F fun i => if i = i0 then π (b i) else 0
  let Q₁ : V →ₗ[F] W := b.constr F fun i => if i = i0 then 0 else π (b i)
  have hQ₀ : Q₀ ∈ U := by
    -- range Q₀ ⊆ span {c₀}, so c₁ is not hit: apply the c₁-coordinate
    rw [hU]
    intro hsurj
    obtain ⟨v, hv⟩ := hsurj (c j1)
    have := congrArg (c.coord j1) hv
    have h0 : π (b i0) = c j0 := hπb j0
    simp [Q₀, Module.Basis.constr_apply_fintype, smul_ite, h0, j0, j1,
      Module.Basis.coord_apply, Module.Basis.repr_self] at this
  have hQ₁ : Q₁ ∈ U := by
    -- range Q₁ ⊆ span {cᵢ : i ≠ 0}, so c₀ is not hit: apply the c₀-coordinate
    rw [hU]
    intro hsurj
    obtain ⟨v, hv⟩ := hsurj (c j0)
    have h1 : c.coord j0 (c j0) = 1 := by simp
    have h0 : c.coord j0 (Q₁ v) = 0 := by
      simp only [Q₁, Module.Basis.constr_apply_fintype, map_sum, map_smul]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with h
      · simp
      · simp only [π, Module.Basis.constr_basis]
        split_ifs with h'
        · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg,
            smul_zero]
          intro h''
          apply h
          ext
          simpa [j0, i0] using congrArg Fin.val h''
        · simp
    rw [hv, h1] at h0
    exact one_ne_zero h0
  have hsum : Q₁ + Q₀ = π := by
    apply b.ext
    intro i
    simp only [LinearMap.add_apply, Q₀, Q₁, Module.Basis.constr_basis]
    split_ifs <;> simp
  exact (hU _).mp (U.add_mem hQ₁ hQ₀) (hsum ▸ hπ)

/-- 3B.9 -/
theorem exercise_3B_9 (T : V →ₗ[F] W) (hT : Function.Injective T)
    {n : ℕ} (v : Fin n → V) (hv : LinearIndependent F v) :
    LinearIndependent F (fun i => T (v i)) := by
  -- ∑ aᵢ T vᵢ = 0 ⇒ T (∑ aᵢ vᵢ) = 0 ⇒ ∑ aᵢ vᵢ = 0 ⇒ a = 0
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro a ha
  apply hv
  apply hT
  rw [map_sum, map_zero]
  simpa only [map_smul] using ha

/-- 3B.10 -/
theorem exercise_3B_10 {n : ℕ} (v : Fin n → V) (hv : Spans F v)
    (T : V →ₗ[F] W) :
    Submodule.span F (Set.range (fun i => T (v i))) = range T := by
  apply le_antisymm
  · -- each T vᵢ lies in range T
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_range_self T (v i)
  · -- w = T u with u = ∑ aᵢ vᵢ, so w = ∑ aᵢ T vᵢ
    rintro w ⟨u, rfl⟩
    have hu : u ∈ Submodule.span F (Set.range v) := hv ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hu
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- 3B.11

{lit}`Submodule.map T U` is the image of the submodule {lit}`U ⊆ V` under
{lit}`T`, packaged as a submodule of {lit}`W` (mathlib bundles the
closure-under-{lit}`+`/{lit}`•` proofs into the definition, so it is
automatically a submodule). Underlying set: {lit}`T '' U = {T u | u ∈ U}`. -/
private lemma sum_prefix_tail {m n : ℕ} (hmn : m ≤ n) {M : Type*} [AddCommMonoid M]
    (f : Fin n → M) :
    ∑ k : Fin n, f k =
      (∑ i : Fin m, f (Fin.castLE hmn i)) +
      (∑ j : Fin (n - m), f ⟨m + j.val, by have := j.isLt; omega⟩) := by
  have heq : m + (n - m) = n := by omega
  rw [← Equiv.sum_comp (finCongr heq) f, Fin.sum_univ_add]
  congr 1

theorem exercise_3B_11 [Finite F V] (T : V →ₗ[F] W) :
    ∃ U : Submodule F V, U ⊓ ker T = ⊥ ∧
      range T = Submodule.map T U := by
  -- take a basis for ker T, say v i, extend to basis of V, new vectors w i
  -- then U = span {w i}, need to show
  -- 1) U ⊓ ker T = ⊥ -- by construction, if ∑ ai wi in ker (with somenonzero ai) =>
  -- ∑ ai wi = ∑ bi vi with some non-zero bi, which gives a linear dependence of basis, contra
  -- 2) range T = Submodule.map T U --
  -- take v in V, write v = ∑ ai vi + ∑ bi wi, then T v = ∑ ai T vi + ∑ bi T wi = ∑ bi T wi
  -- so T v is spanned by wi for all v, thus range T = U.
  -- basis v of ker T (2.31), viewed as vectors of V
  obtain ⟨m, v, hv_basis⟩ := LADR.Section_2B.exists_basis (F := F) (V := ker T)
  let vV : Fin m → V := fun i => (v i : V)
  have hv_li : LinearIndependent F vV :=
    hv_basis.1.map' (ker T).subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  -- extend to a basis w of V (2.32); w₀, …, w_{m-1} are the vᵢ and the new
  -- vectors are the tail w_m, …, w_{n-1}
  obtain ⟨n, w, hmn, hw_basis, hw_prefix⟩ :=
    LADR.Section_2B.exists_basis_extending vV hv_li
  let tail : Fin (n - m) → V := fun j => w ⟨m + j.val, by have := j.isLt; omega⟩
  have hw_span : Submodule.span F (Set.range w) = ⊤ := hw_basis.2
  refine ⟨Submodule.span F (Set.range tail), ?_, ?_⟩
  · -- 1) x in both: x = ∑ aᵢ vᵢ (basis of ker T) and x = ∑ bⱼ tailⱼ, so
    -- ∑ aᵢ vᵢ - ∑ bⱼ tailⱼ = 0 is a relation on the basis w, so all aᵢ = 0
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxU, hxK⟩ := hx
    have hv_span : Submodule.span F (Set.range v) = ⊤ := hv_basis.2
    have hx_v : (⟨x, hxK⟩ : ker T) ∈ Submodule.span F (Set.range v) := by
      rw [hv_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx_v
    obtain ⟨a, ha⟩ := hx_v
    have ha' : ∑ i, a i • vV i = x := by
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at this
      exact this
    rw [Submodule.mem_span_range_iff_exists_fun] at hxU
    obtain ⟨b, hb⟩ := hxU
    -- coefficients on the full basis w: a on the prefix, -b on the tail
    let c : Fin n → F := fun k =>
      if h : k.val < m then a ⟨k.val, h⟩
      else -b ⟨k.val - m, by have := k.isLt; omega⟩
    have hc_prefix : ∀ i : Fin m, c (Fin.castLE hmn i) = a i := by
      intro i
      show (if h : (Fin.castLE hmn i).val < m then a ⟨_, h⟩ else _) = a i
      rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
      congr 1
    have hc_tail : ∀ j : Fin (n - m),
        c ⟨m + j.val, by have := j.isLt; omega⟩ = -b j := by
      intro j
      show (if h : m + j.val < m then _ else -b ⟨m + j.val - m, _⟩) = -b j
      rw [dif_neg (by omega)]
      congr
      show m + j.val - m = j.val
      omega
    have hsum_zero : ∑ k, c k • w k = 0 := by
      rw [sum_prefix_tail hmn (fun k => c k • w k)]
      have hsum1 : ∑ i : Fin m, c (Fin.castLE hmn i) • w (Fin.castLE hmn i) = x := by
        rw [← ha']
        exact Finset.sum_congr rfl fun i _ => by rw [hc_prefix i, hw_prefix i]
      have hsum2 : ∑ j : Fin (n - m),
          c ⟨m + j.val, by have := j.isLt; omega⟩ • tail j = -x := by
        rw [← hb, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [hc_tail j, neg_smul]
      rw [hsum1, hsum2, add_neg_cancel]
    have hc_zero : ∀ k, c k = 0 := by
      have hli := hw_basis.1
      rw [Fintype.linearIndependent_iff] at hli
      exact hli c hsum_zero
    rw [← ha']
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hc_prefix i, hc_zero, zero_smul]
  · -- 2) T x = T (prefix part) + T (tail part) = T (tail part) ∈ T '' U
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ Submodule.span F (Set.range w) := by
        rw [hw_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, hc⟩ := hx
      rw [← hc, sum_prefix_tail hmn (fun k => c k • w k), map_add]
      have hpre : T (∑ i : Fin m, c (Fin.castLE hmn i) • w (Fin.castLE hmn i)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        have hvi : T (vV i) = 0 := LinearMap.mem_ker.mp (v i).2
        rw [hw_prefix i, map_smul, hvi, smul_zero]
      rw [hpre, zero_add]
      refine ⟨_, ?_, rfl⟩
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · exact LinearMap.map_le_range

/-- 3B.12 -/
theorem exercise_3B_12 (T : (Fin 4 → F) →ₗ[F] (Fin 2 → F))
    (h : ∀ x : Fin 4 → F,
      x ∈ ker T ↔ x 0 = 5 * x 1 ∧ x 2 = 7 * x 3) :
    Function.Surjective T := by
  -- by dimension, enough to show null dim is 2.
  -- two lin ind that span it is - (5, 1, 0, 0) and (0, 0, 7, 1)
  -- (only dim null T ≤ 2 is needed: then dim range T ≥ 4 - 2 = 2 = dim F²)
  have hle : ker T ≤ Submodule.span F
      (Set.range ![(![5, 1, 0, 0] : Fin 4 → F), ![0, 0, 7, 1]]) := by
    intro x hx
    obtain ⟨h1, h2⟩ := (h x).mp hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![x 1, x 3], ?_⟩
    funext i
    fin_cases i <;> simp [Fin.sum_univ_two, h1, h2] <;> ring
  have h2 := finrank_range_le_card (R := F) ![(![5, 1, 0, 0] : Fin 4 → F), ![0, 0, 7, 1]]
  rw [Set.finrank, Fintype.card_fin] at h2
  have hk : finrank F (ker T) ≤ 2 := (Submodule.finrank_mono hle).trans h2
  have hr := LinearMap.finrank_range_add_finrank_ker T
  rw [Module.finrank_fin_fun] at hr
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at this
  omega

/-- 3B.13 -/
theorem exercise_3B_13 (U : Submodule ℝ (Fin 8 → ℝ)) (hU : finrank ℝ U = 3)
    (T : (Fin 8 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ)) (hker : ker T = U) :
    Function.Surjective T := by
  -- by dim formula, dim range T = dim V - dim ker T = 8 - 3 = 5, so T is surjective.
  have hr := LinearMap.finrank_range_add_finrank_ker T
  rw [hker, hU, Module.finrank_fin_fun] at hr
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have := Submodule.finrank_lt hne
  rw [Module.finrank_fin_fun] at this
  omega

/-- 3B.14 -/
theorem exercise_3B_14 :
    ¬ ∃ T : (Fin 5 → F) →ₗ[F] (Fin 2 → F), ∀ x : Fin 5 → F,
      x ∈ ker T ↔ x 0 = 3 * x 1 ∧ x 2 = x 3 ∧ x 3 = x 4 := by
  -- by contra assume exists
  -- will show dim ker T = 2, but dim V = 5, so dim range T = 3 > 2, impossible
  -- a basis for ker T is (3, 1, 0, 0, 0) and (0, 0, 1, 1, 1)
  -- (only dim null T ≤ 2 is needed: then dim range T ≥ 3 > 2 = dim F²)
  rintro ⟨T, h⟩
  have hle : ker T ≤ Submodule.span F
      (Set.range ![(![3, 1, 0, 0, 0] : Fin 5 → F), ![0, 0, 1, 1, 1]]) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := (h x).mp hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![x 1, x 2], ?_⟩
    funext i
    (fin_cases i <;> simp [Fin.sum_univ_two, h1, h2, h3]); ring
  have h2 := finrank_range_le_card (R := F) ![(![3, 1, 0, 0, 0] : Fin 5 → F), ![0, 0, 1, 1, 1]]
  rw [Set.finrank, Fintype.card_fin] at h2
  have hk : finrank F (ker T) ≤ 2 := (Submodule.finrank_mono hle).trans h2
  have hr := LinearMap.finrank_range_add_finrank_ker T
  rw [Module.finrank_fin_fun] at hr
  have hle2 := Submodule.finrank_le (range T)
  rw [Module.finrank_fin_fun] at hle2
  omega

/-- 3B.15 -/
theorem exercise_3B_15 (T : V →ₗ[F] V)
    (hker : Finite F (ker T)) (hrange : Finite F (range T)) :
    Finite F V := by
  -- take a basis for ker T = v i, and take a basis for range T = w i,
  -- w' i are the preimages of w i under T.
  -- take random v in V and will show that it is in span of {w' i, v i}
  -- thus basis is finite.
  -- T v = ∑ a i w i , by construction
  -- then v - ∑ a i w' i ∈ ker T, so it is in the span of {v i} = ∑ b i v i
  -- so v. = ∑ a i w' i + ∑ b i v i as desired (with the right some non zero conditions)
  obtain ⟨m, v, hv_basis⟩ := LADR.Section_2B.exists_basis (F := F) (V := ker T)
  obtain ⟨n, w, hw_basis⟩ := LADR.Section_2B.exists_basis (F := F) (V := range T)
  have hv_span : Submodule.span F (Set.range v) = ⊤ := hv_basis.2
  have hw_span : Submodule.span F (Set.range w) = ⊤ := hw_basis.2
  -- preimages w'ⱼ of the wⱼ
  have hpre : ∀ j, ∃ w' : V, T w' = w j := fun j => LinearMap.mem_range.mp (w j).2
  choose w' hw' using hpre
  -- V is finite-dimensional iff some finite set spans it
  let S : Set V := Set.range (fun i => (v i : V)) ∪ Set.range w'
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨S, (Set.finite_range _).union (Set.finite_range _), ?_⟩
  rw [eq_top_iff]
  intro x _
  -- T x ∈ range T, so T x = ∑ aⱼ wⱼ; let u = ∑ aⱼ w'ⱼ, so T u = T x
  have hTx : (⟨T x, LinearMap.mem_range_self T x⟩ : range T) ∈
      Submodule.span F (Set.range w) := by
    rw [hw_span]; exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hTx
  obtain ⟨a, ha⟩ := hTx
  let u : V := ∑ j, a j • w' j
  have hu : T u = T x := by
    have := congrArg Subtype.val ha
    rw [Submodule.coe_sum] at this
    simp only [Submodule.coe_smul] at this
    simp only [u, map_sum, map_smul, hw']
    exact this
  -- x - u ∈ ker T, so x - u = ∑ bᵢ vᵢ
  have hxu : x - u ∈ ker T := by rw [LinearMap.mem_ker, map_sub, hu, sub_self]
  have hxu_v : (⟨x - u, hxu⟩ : ker T) ∈ Submodule.span F (Set.range v) := by
    rw [hv_span]; exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hxu_v
  obtain ⟨b, hb⟩ := hxu_v
  have hb' : ∑ i, b i • (v i : V) = x - u := by
    have := congrArg Subtype.val hb
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this
  -- x = u + (x - u), and both pieces lie in span S
  have hu_mem : u ∈ Submodule.span F S :=
    Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_union_right _ ⟨j, rfl⟩))
  have hxu_mem : x - u ∈ Submodule.span F S := by
    rw [← hb']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩))
  have := Submodule.add_mem _ hu_mem hxu_mem
  rwa [add_sub_cancel] at this

/-- 3B.16 -/
theorem exercise_3B_16 [Finite F V] [Finite F W] :
    (∃ T : V →ₗ[F] W, Function.Injective T) ↔ finrank F V ≤ finrank F W := by
  -- => by rank-nullity theorem, inj => dim ker = 0 -> dim V = rank T <= dim W
  -- <= take a basis vi of V and basis wi of W, map vi to wi (possible by rank), extend linearly.
  -- need to show this is injective, for linear same as ker = {0}
  -- assume T v = 0, T ∑ ai vi = 0 -> ∑ ai wi = 0, but wi LI so ai = 0, thus v = 0
  constructor
  · rintro ⟨T, hT⟩
    have h := finrank_ker_add_finrank_range T
    rw [(injective_iff_ker_eq_bot T).mp hT, finrank_bot, zero_add] at h
    rw [← h]
    exact LADR.Section_2C.finrank_submodule_le (range T)
  · intro hVW
    obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
    obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
    have hn : n = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v hv
    have hm : m = finrank F W := LADR.Section_2C.isBasis_card_eq_finrank w hw
    have hnm : n ≤ m := by omega
    -- T vᵢ = wᵢ, extended linearly
    let b := hv.toModuleBasis
    let T : V →ₗ[F] W := b.constr F fun i => w (Fin.castLE hnm i)
    refine ⟨T, ?_⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    -- x = ∑ aᵢ vᵢ with aᵢ the coordinates of x, so T x = ∑ aᵢ wᵢ = 0
    rw [Module.Basis.constr_apply_fintype] at hx
    have hli : LinearIndependent F fun i => w (Fin.castLE hnm i) :=
      hw.1.comp _ (Fin.castLE_injective hnm)
    rw [Fintype.linearIndependent_iff] at hli
    have ha : b.equivFun x = 0 := funext (hli _ hx)
    exact b.equivFun.map_eq_zero_iff.mp ha

/-- 3B.17 -/
theorem exercise_3B_17 [Finite F V] [Finite F W] :
    (∃ T : V →ₗ[F] W, Function.Surjective T) ↔ finrank F V ≥ finrank F W := by
  -- => surj => rank T = dim W, by rank nullity theorem, dim V = rank T + dim ker T >= dim W
  -- <= take a basis wi of W and a basis vi of V, map some of vi to all wi injectively (possible by ranks)
  -- take w = ∑ ai wi, its preimage is ∑ ai vi, which exists by construction, thus surjective.
  constructor
  · rintro ⟨T, hT⟩
    have h := finrank_ker_add_finrank_range T
    rw [(surjective_iff_range_eq_top T).mp hT, finrank_top] at h
    omega
  · intro hVW
    obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
    obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
    have hn : n = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v hv
    have hm : m = finrank F W := LADR.Section_2C.isBasis_card_eq_finrank w hw
    have hmn : m ≤ n := by omega
    -- T vᵢ = wᵢ for i < m and T vᵢ = 0 otherwise
    let b := hv.toModuleBasis
    let T : V →ₗ[F] W := b.constr F fun i => if h : i.val < m then w ⟨i, h⟩ else 0
    have hT : ∀ j : Fin m, T (v (Fin.castLE hmn j)) = w j := by
      intro j
      have : v (Fin.castLE hmn j) = b (Fin.castLE hmn j) := (hv.toModuleBasis_apply _).symm
      rw [this]
      simp only [T, Module.Basis.constr_basis]
      rw [dif_pos (by rw [Fin.val_castLE]; exact j.isLt)]
      congr 1
    refine ⟨T, ?_⟩
    intro y
    have hw_span : Submodule.span F (Set.range w) = ⊤ := hw.2
    have hy : y ∈ Submodule.span F (Set.range w) := by rw [hw_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨a, ha⟩ := hy
    refine ⟨∑ j, a j • v (Fin.castLE hmn j), ?_⟩
    rw [map_sum, ← ha]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hT j]

/-- 3B.18 -/
theorem exercise_3B_18 [Finite F V] [Finite F W] (U : Submodule F V) :
    (∃ T : V →ₗ[F] W, ker T = U) ↔
      finrank F V - finrank F W ≤ finrank F U := by
  -- => by rank-nullity, dim V = dim range T + dim U, so dim U = dim V - dim range T
  -- but dim range T <= dim W, so dim U = dim V - dim range T >= dim V - dim W
  -- <= take basis of U and extend to basis of V, take basis wi of W,
  -- since dim V - dim U ≤ dim W, the extended basis vectors of V/U are fewer than wi
  -- map those injectively to wi, and send basis of U to 0.
  -- this gives a linear map T, need to show that ker T = U.
  -- U ⊆ ker T by construction,
  -- to show ker T ⊆ U, take v ∈ ker T
  -- write v as LI of V, v = u + ∑ ai vi, where u ∈ U and vi are the extended basis vectors
  -- then T v = 0 + ∑ ai T vi = ∑ ai wi, but wi are LI, thus all ai = 0, and v = u ∈ U.
  constructor
  · rintro ⟨T, rfl⟩
    have h := finrank_ker_add_finrank_range T
    have := LADR.Section_2C.finrank_submodule_le (range T)
    omega
  · intro hdim
    -- basis u of U (2.31), viewed in V, extended (2.32) to a basis v of V
    obtain ⟨k, u, hu⟩ := LADR.Section_2B.exists_basis (F := F) (V := U)
    let uV : Fin k → V := fun i => (u i : V)
    have hu_li : LinearIndependent F uV :=
      hu.1.map' U.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
    obtain ⟨n, v, hkn, hv, hv_prefix⟩ := LADR.Section_2B.exists_basis_extending uV hu_li
    obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
    have hk : k = finrank F U := LADR.Section_2C.isBasis_card_eq_finrank u hu
    have hn : n = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v hv
    have hm : m = finrank F W := LADR.Section_2C.isBasis_card_eq_finrank w hw
    -- the n - k new basis vectors are at most m in number
    have hnkm : n - k ≤ m := by omega
    -- T vᵢ = 0 for i < k (the basis of U) and T v_{k+j} = wⱼ
    let b := hv.toModuleBasis
    let T : V →ₗ[F] W := b.constr F fun i =>
      if h : i.val < k then 0 else w ⟨i.val - k, by have := i.isLt; omega⟩
    have hT_prefix : ∀ i : Fin k, T (uV i) = 0 := by
      intro i
      have : uV i = b (Fin.castLE hkn i) := by rw [hv.toModuleBasis_apply, hv_prefix i]
      rw [this]
      simp only [T, Module.Basis.constr_basis]
      rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
    have hT_tail : ∀ j : Fin (n - k),
        T (v ⟨k + j.val, by have := j.isLt; omega⟩) = w (Fin.castLE hnkm j) := by
      intro j
      have : v ⟨k + j.val, by have := j.isLt; omega⟩ =
          b ⟨k + j.val, by have := j.isLt; omega⟩ := (hv.toModuleBasis_apply _).symm
      rw [this]
      simp only [T, Module.Basis.constr_basis]
      rw [dif_neg (by omega)]
      congr 1
      ext
      show k + j.val - k = j.val
      omega
    refine ⟨T, le_antisymm ?_ ?_⟩
    · -- ker T ⊆ U: x = ∑ cᵢ vᵢ; T x = ∑ over the tail of c_{k+j} wⱼ = 0 forces the
      -- tail coefficients to vanish, leaving x = ∑ cᵢ uᵢ ∈ U
      intro x hx
      have hv_span : Submodule.span F (Set.range v) = ⊤ := hv.2
      have hxv : x ∈ Submodule.span F (Set.range v) := by rw [hv_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxv
      obtain ⟨c, hc⟩ := hxv
      rw [LinearMap.mem_ker, ← hc, sum_prefix_tail hkn (fun i => c i • v i), map_add, map_sum,
        map_sum] at hx
      have hpre : ∑ i : Fin k, T (c (Fin.castLE hkn i) • v (Fin.castLE hkn i)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [map_smul, hv_prefix i, hT_prefix i, smul_zero]
      rw [hpre, zero_add] at hx
      have htail : ∑ j : Fin (n - k),
          c ⟨k + j.val, by have := j.isLt; omega⟩ • w (Fin.castLE hnkm j) = 0 := by
        rw [← hx]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hT_tail j]
      have hli : LinearIndependent F fun j => w (Fin.castLE hnkm j) :=
        hw.1.comp _ (Fin.castLE_injective hnkm)
      rw [Fintype.linearIndependent_iff] at hli
      have hc_tail := hli _ htail
      rw [← hc, sum_prefix_tail hkn (fun i => c i • v i)]
      refine U.add_mem ?_ ?_
      · exact Submodule.sum_mem _ fun i _ => by rw [hv_prefix i]; exact U.smul_mem _ (u i).2
      · exact Submodule.sum_mem _ fun j _ => by rw [hc_tail j, zero_smul]; exact U.zero_mem
    · -- U ⊆ ker T: x ∈ U is ∑ aᵢ uᵢ and T uᵢ = 0
      intro x hx
      have hu_span : Submodule.span F (Set.range u) = ⊤ := hu.2
      have hxu : (⟨x, hx⟩ : U) ∈ Submodule.span F (Set.range u) := by
        rw [hu_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxu
      obtain ⟨a, ha⟩ := hxu
      have ha' : ∑ i, a i • uV i = x := by
        have := congrArg Subtype.val ha
        rw [Submodule.coe_sum] at this
        exact this
      rw [LinearMap.mem_ker, ← ha', map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hT_prefix i, smul_zero]

/-- 3B.19 -/
theorem exercise_3B_19 [Finite F W] (T : V →ₗ[F] W) :
    Function.Injective T ↔
      ∃ S : W →ₗ[F] V, S ∘ₗ T = LinearMap.id := by
  -- => first V is also fin.dim as injected into fin. dim W
  -- take a basis vi of V, by ex 9, T vi are LI too, so we can extend them ot a W basis
  -- make S by sending T vi back to vi, and wi to 0.
  -- now S T v i = vi, as desired. and thus S T = id (by linearity)
  -- <= assume S T = id, and not inj, i.e. exist v ≠ 0 such that T v = 0.
  -- then S T v = S 0 = 0, contradicting S T = id since v ≠ 0.
  constructor
  · intro hT
    -- V is finite-dimensional since T embeds it into W
    haveI : Finite F V := FiniteDimensional.of_injective T hT
    obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
    have hTv : LinearIndependent F fun i => T (v i) := exercise_3B_9 T hT v hv.1
    obtain ⟨m, w, hnm, hw, hw_prefix⟩ := LADR.Section_2B.exists_basis_extending _ hTv
    -- S (T vᵢ) = vᵢ and S wⱼ = 0 for the added wⱼ
    let c := hw.toModuleBasis
    let S : W →ₗ[F] V := c.constr F fun j => if h : j.val < n then v ⟨j, h⟩ else 0
    refine ⟨S, hv.toModuleBasis.ext fun i => ?_⟩
    rw [hv.toModuleBasis_apply, LinearMap.comp_apply, LinearMap.id_apply]
    have : T (v i) = c (Fin.castLE hnm i) := by rw [hw.toModuleBasis_apply, hw_prefix i]
    rw [this]
    simp only [S, Module.Basis.constr_basis]
    rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
    congr 1
  · rintro ⟨S, hS⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    have := LinearMap.congr_fun hS x
    rw [LinearMap.comp_apply, hx, map_zero, LinearMap.id_apply] at this
    exact this.symm

/-- 3B.20 -/
theorem exercise_3B_20 [Finite F W] (T : V →ₗ[F] W) :
    Function.Surjective T ↔
      ∃ S : W →ₗ[F] V, T ∘ₗ S = LinearMap.id := by
  -- => take a basis wi of W, by surj, exists vi in V such that T vi = wi.
  -- define S wi = vi, since wi are basis, this is well-defined linear op.
  -- now T S wi = T vi = wi, so T S = id (by linearity) on the extended basis of W.
  constructor
  · intro hT
    obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
    choose v hv using fun j => hT (w j)
    let c := hw.toModuleBasis
    let S : W →ₗ[F] V := c.constr F v
    refine ⟨S, c.ext fun j => ?_⟩
    rw [LinearMap.comp_apply, LinearMap.id_apply]
    simp only [S, Module.Basis.constr_basis]
    rw [hv j, hw.toModuleBasis_apply]
  · rintro ⟨S, hS⟩
    intro y
    exact ⟨S y, by simpa using LinearMap.congr_fun hS y⟩

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
  constructor
  · simp only [Set.mem_setOf_eq, map_zero, zero_mem]
  · constructor
    · intros u v hu hv
      simp at hu hv ⊢
      exact (Submodule.add_mem_iff_right Usub hu).mpr hv
    · intros c v hv
      simp at hv ⊢
      exact Submodule.smul_mem Usub c hv

/-- 3B.21.b

{lit}`Submodule.comap T Usub` is the preimage {lit}`{v ∈ V | T v ∈ Usub}`
bundled as a submodule of {lit}`V` (mathlib packages the closure proofs
from 3B.21.a into the definition). -/
theorem exercise_3B_21_b [Finite F V] (T : V →ₗ[F] W) (Usub : Submodule F W) :
    finrank F (Submodule.comap T Usub) =
      finrank F (ker T) +
        finrank F ((Usub ⊓ range T : Submodule F W)) := by
  -- restrict T to U, T|U
  -- rank-nullity of T|U says finrank U = finrank (ker (T|U)) + finrank (range (T|U))
  -- so we need to show
  -- 1) ker T|U = ker T , since 0 in U, every v in ker T is also in U.
  -- 2) range (T|U) = Usub ⊓ range T, this is the definition of the restricted map.
  let U' := Submodule.comap T Usub
  have h := finrank_ker_add_finrank_range (T.domRestrict U')
  -- 1) ker (T|U') is ker T viewed inside U', and ker T ⊆ U' since T v = 0 ∈ Usub
  have hker : finrank F (ker (T.domRestrict U')) = finrank F (ker T) := by
    rw [LinearMap.ker_domRestrict]
    refine (Submodule.comapSubtypeEquivOfLe fun v hv => ?_).finrank_eq
    show T v ∈ Usub
    rw [LinearMap.mem_ker.mp hv]
    exact Usub.zero_mem
  -- 2) range (T|U') = T '' U' = Usub ⊓ range T
  have hrange : finrank F (range (T.domRestrict U')) =
      finrank F ((Usub ⊓ range T : Submodule F W)) := by
    rw [LinearMap.range_domRestrict, Submodule.map_comap_eq, inf_comm]
  rw [← h, hker, hrange]

/-- 3B.22 -/
theorem exercise_3B_22 [Finite F U] [Finite F V]
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    finrank F (ker (S ∘ₗ T)) ≤
      finrank F (ker S) + finrank F (ker T) := by
    -- apply ex21 to ker S as subspace of V.
    -- dim comap T (ker S) = dim null T + dim (ker S ∩ range T) ≤ dim ker T + dim ker S
    -- finally, v in comap T ker S, means T v ∈ ker S, so S T v = 0, i.e. v ∈ ker (S ∘ₗ T),
    -- so comap T (ker S) = ker (S ∘ₗ T)
  have hcomap : ker (S ∘ₗ T) = Submodule.comap T (ker S) := by
    ext v
    rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.comp_apply]
  rw [hcomap, exercise_3B_21_b T (ker S)]
  have := Submodule.finrank_mono (inf_le_left : ker S ⊓ range T ≤ ker S)
  omega

/-- 3B.23 -/
theorem exercise_3B_23 [Finite F U] [Finite F V]
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    finrank F (range (S ∘ₗ T)) ≤ min (finrank F (range S))
      (finrank F (range T)) := by
  -- by rank-nullity
  -- 1) show dim range S T ≤ dim range S -- trivially as range (S ∘ₗ T) ⊆ range S.
  -- 2) show dim range S T ≤ dim range T
  -- consider S|range T, range ST = range (S|range T), so dim range ST ≤ dim range T too.
  refine le_min ?_ ?_
  · refine Submodule.finrank_mono ?_
    rintro _ ⟨u, rfl⟩
    exact ⟨T u, rfl⟩
  · have hrange : range (S ∘ₗ T) = range (S.domRestrict (range T)) := by
      rw [LinearMap.range_domRestrict, LinearMap.range_comp]
    have h := finrank_ker_add_finrank_range (S.domRestrict (range T))
    rw [hrange]
    omega

/-- 3B.24 (a) -/
theorem exercise_3B_24a [Finite F V] (hV : finrank F V = 5)
    (S T : V →ₗ[F] V) (hST : S ∘ₗ T = 0) :
    finrank F (range (T ∘ₗ S)) ≤ 2 := by
  -- combine 22 and 23, ST = 0 -> dim ker ST = 5, so ker S + ker T ≥ 5
  -- thus either S or T has rank at most 2, by 23, rank TS ≤ 2 too.
  have h22 := exercise_3B_22 S T
  rw [hST, LinearMap.ker_zero, finrank_top, hV] at h22
  have h23 := exercise_3B_23 T S
  have hS := finrank_ker_add_finrank_range S
  have hT := finrank_ker_add_finrank_range T
  rw [hV] at hS hT
  omega

/-- 3B.24 (b) -/
theorem exercise_3B_24b :
    ∃ S T : (Fin 5 → F) →ₗ[F] (Fin 5 → F),
      S ∘ₗ T = 0 ∧ finrank F (range (T ∘ₗ S)) = 2 := by
  -- S (x1, x2, x3, x4, x5) = (x4, x5, x5, x5, x5)
  -- T (x1, x2, x3, x4, x5) = (x1, x2, 0, 0, 0)
  -- then S T = 0, but T S = (x4, x5, 0, 0, 0)
  let S : (Fin 5 → F) →ₗ[F] (Fin 5 → F) :=
    LinearMap.pi ![LinearMap.proj 3, LinearMap.proj 4, LinearMap.proj 4, LinearMap.proj 4,
      LinearMap.proj 4]
  let T : (Fin 5 → F) →ₗ[F] (Fin 5 → F) :=
    LinearMap.pi ![LinearMap.proj 0, LinearMap.proj 1, 0, 0, 0]
  refine ⟨S, T, ?_, ?_⟩
  · ext x i
    fin_cases i <;> simp [S, T]
  · -- T S = ι ∘ P with P x = (x4, x5) onto F² and ι (y1, y2) = (y1, y2, 0, 0, 0) injective,
    -- so null (T S) = null P has dimension 5 - 2 = 3 and rank (T S) = 5 - 3 = 2
    let P : (Fin 5 → F) →ₗ[F] (Fin 2 → F) := LinearMap.funLeft F F (Fin.natAdd 3)
    let ι : (Fin 2 → F) →ₗ[F] (Fin 5 → F) :=
      LinearMap.pi ![LinearMap.proj 0, LinearMap.proj 1, 0, 0, 0]
    have hTS : T ∘ₗ S = ι ∘ₗ P := by
      ext x i
      fin_cases i <;> simp [S, T, ι, P, LinearMap.funLeft_apply, Fin.natAdd]
    have hP : Function.Surjective P :=
      LinearMap.funLeft_surjective_of_injective _ _ _ fun a b h =>
        Fin.ext (by simpa using congrArg Fin.val h)
    have hι : ker ι = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro y hy
      have h0 := congrFun hy 0
      have h1 := congrFun hy 1
      simp [ι] at h0 h1
      funext j
      fin_cases j <;> simp [h0, h1]
    have hkerP := finrank_ker_add_finrank_range P
    rw [(surjective_iff_range_eq_top P).mp hP, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at hkerP
    have h := finrank_ker_add_finrank_range (T ∘ₗ S)
    rw [hTS, LinearMap.ker_comp_of_ker_eq_bot P hι, Module.finrank_fin_fun] at h
    rw [hTS]
    omega

/-- 3B.25 -/
theorem exercise_3B_25 [Finite F W] (S T : V →ₗ[F] W) :
    ker S ≤ ker T ↔
      ∃ E : W →ₗ[F] W, T = E ∘ₗ S := by
  -- <= trivially, if S x = 0, then T x = E (S x) = E 0 = 0 too.
  -- => will construct E as follows
  -- 1) take a basis wi of range S and pick one preimage xi of each, S xi = wi.
  -- define E on the wi by E wi = T xi (the choice of xi is arbitrary).
  -- 2) extend E to the whole of W by sending the rest of a basis of W to 0.
  -- now we need to show T v = E (S v) for every v in V. the xi together with
  -- ker S span V: S v = ∑ ai wi = S (∑ ai xi), so v - ∑ ai xi ∈ ker S.
  -- so it is enough to check on those:
  -- if v = xi, then E (S xi) = E wi = T xi by construction.
  -- if v ∈ ker S, then E (S v) = E 0 = 0, and T v = 0 too since ker S ⊆ ker T.
  constructor
  · intro hST
    -- 1) basis wᵢ of range S, preimages xᵢ with S xᵢ = wᵢ
    obtain ⟨n, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := range S)
    let wW : Fin n → W := fun i => (w i : W)
    have hw_li : LinearIndependent F wW :=
      hw.1.map' (range S).subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
    choose x hx using fun i => LinearMap.mem_range.mp (w i).2
    have hx' : ∀ i, S (x i) = wW i := hx
    -- 2) extend the wᵢ to a basis of W (2.32); E (wᵢ) = T xᵢ, E = 0 on the rest
    obtain ⟨m, c, hnm, hc, hc_prefix⟩ := LADR.Section_2B.exists_basis_extending wW hw_li
    let cb := hc.toModuleBasis
    let E : W →ₗ[F] W := cb.constr F fun j => if h : j.val < n then T (x ⟨j, h⟩) else 0
    have hE : ∀ i, E (wW i) = T (x i) := by
      intro i
      have : wW i = cb (Fin.castLE hnm i) := by rw [hc.toModuleBasis_apply, hc_prefix i]
      rw [this]
      simp only [E, Module.Basis.constr_basis]
      rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
      congr 1
    refine ⟨E, ?_⟩
    ext v
    rw [LinearMap.comp_apply]
    -- S v = ∑ aᵢ wᵢ = S (∑ aᵢ xᵢ), so v - ∑ aᵢ xᵢ ∈ null S ⊆ null T
    have hw_span : Submodule.span F (Set.range w) = ⊤ := hw.2
    have hSv : (⟨S v, LinearMap.mem_range_self S v⟩ : range S) ∈
        Submodule.span F (Set.range w) := by
      rw [hw_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hSv
    obtain ⟨a, ha⟩ := hSv
    have ha' : ∑ i, a i • wW i = S v := by
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at this
      exact this
    let u : V := ∑ i, a i • x i
    have hSu : S u = S v := by
      rw [← ha']
      simp only [u, map_sum, map_smul, hx']
    have hvu : v - u ∈ ker T := hST (by rw [LinearMap.mem_ker, map_sub, hSu, sub_self])
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hvu
    -- hence T v = T (∑ aᵢ xᵢ) = ∑ aᵢ E wᵢ = E (S v)
    rw [hvu, ← ha', map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hE i]
  · rintro ⟨E, rfl⟩
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [LinearMap.comp_apply, hv, map_zero]

/-- 3B.26 -/
theorem exercise_3B_26 [Finite F V] (S T : V →ₗ[F] W) :
    range S ≤ range T ↔
      ∃ E : V →ₗ[F] V, S = T ∘ₗ E := by
  -- <= trivially, if S = T ∘ₗ E, then range S ≤ range T
  -- => will construct E as follows, take v i as a basis of V
  -- for each vi, Svi is in range T, so there exists ti such that T ti = S vi
  -- define E vi = ti for one such ti
  constructor
  · intro hST
    obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
    choose t ht using fun i => LinearMap.mem_range.mp (hST (LinearMap.mem_range_self S (v i)))
    let b := hv.toModuleBasis
    refine ⟨b.constr F t, b.ext fun i => ?_⟩
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, ht i, hv.toModuleBasis_apply]
  · rintro ⟨E, rfl⟩
    rintro _ ⟨v, rfl⟩
    exact ⟨E v, rfl⟩

/-- 3B.27 -/
theorem exercise_3B_27 (P : V →ₗ[F] V) (hP : P ∘ₗ P = P) :
    IsCompl (ker P) (range P) := by
  -- first show independence assume exists v ≠ 0, st. P v = 0, and exist w st. P w = v.
  -- but then P P w = P v = 0, but PP = P, so P w = v = 0, contradiction.
  -- finally show span - v = P v + (v - P v), with P v in range
  -- (v - P v) in ker, because P (v - P v) = P v - P (P v) = 0
  have hPP : ∀ v, P (P v) = P v := fun v => LinearMap.congr_fun hP v
  refine ⟨?_, ?_⟩
  · -- ker P ⊓ range P = 0
    rw [Submodule.disjoint_def]
    rintro v hv ⟨w, rfl⟩
    rw [LinearMap.mem_ker] at hv
    rw [← hPP w, hv]
  · -- ker P ⊔ range P = V: v = (v - P v) + P v
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [← sub_add_cancel v (P v)]
    refine Submodule.add_mem_sup ?_ (LinearMap.mem_range_self P v)
    rw [LinearMap.mem_ker, map_sub, hPP, sub_self]

open Polynomial in
/-- 3B.28 — Axler's "nonconstant" condition is {lit}`0 < p.degree`, and
{lit}`deg (D p) = deg p - 1` is written as {lit}`(D p).degree + 1 = p.degree`
since {lit}`WithBot ℕ` has no subtraction. -/
theorem exercise_3B_28 (D : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
    (hD : ∀ p : Polynomial ℝ, 0 < p.degree →
      (D p).degree + 1 = p.degree) :
    Function.Surjective D := by
  -- we will prove by induction on degree
  -- base case: degree -inf, D 0 = 0, so surjective onto degree -inf, trivially.
  -- then for a poly of deg n = a X^n + lower terms, with a ≠ 0
  -- first take D X ^ (n + 1) = b X^n + lower terms, with b ≠ 0
  -- if we now take a/b X^(n + 1) + p(X), D will map it to a X^n + lower terms,
  -- and by strong induction we can find the right p(X) to match the desired lower terms.
  -- D X^(n+1) is nonzero of degree n
  have hDX : ∀ n : ℕ, D (X ^ (n + 1)) ≠ 0 ∧ (D (X ^ (n + 1))).natDegree = n := by
    intro n
    have h := hD (X ^ (n + 1)) (by rw [degree_X_pow]; exact_mod_cast Nat.succ_pos n)
    rw [degree_X_pow] at h
    have hne : D (X ^ (n + 1)) ≠ 0 := by
      intro h0
      rw [h0, degree_zero, WithBot.bot_add] at h
      exact WithBot.bot_ne_coe h
    refine ⟨hne, ?_⟩
    rw [degree_eq_natDegree hne] at h
    have : (D (X ^ (n + 1))).natDegree + 1 = n + 1 := by exact_mod_cast h
    omega
  intro q
  obtain ⟨n, hn⟩ : ∃ n, q.natDegree = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing q with
  | _ n ih => ?_
  by_cases hq : q = 0
  · exact ⟨0, by rw [map_zero, hq]⟩
  obtain ⟨hne, hdeg⟩ := hDX n
  -- a = leading coefficient of q, b = leading coefficient of D X^(n+1)
  have hb : (D (X ^ (n + 1))).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have hab : q.leadingCoeff / (D (X ^ (n + 1))).leadingCoeff ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.mpr hq) hb
  -- r = q - (a/b) D X^(n+1) has degree < n
  have hr : (q - C (q.leadingCoeff / (D (X ^ (n + 1))).leadingCoeff) * D (X ^ (n + 1))).degree <
      q.degree := by
    refine degree_sub_lt ?_ hq ?_
    · rw [degree_C_mul hab, degree_eq_natDegree hq, degree_eq_natDegree hne, hn, hdeg]
    · rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hab), div_mul_cancel₀ _ hb]
  -- the answer is (a/b) X^(n+1) + p with D p = r
  by_cases hr0 : q - C (q.leadingCoeff / (D (X ^ (n + 1))).leadingCoeff) * D (X ^ (n + 1)) = 0
  · refine ⟨C (q.leadingCoeff / (D (X ^ (n + 1))).leadingCoeff) * X ^ (n + 1), ?_⟩
    rw [← smul_eq_C_mul, map_smul, smul_eq_C_mul]
    exact (sub_eq_zero.mp hr0).symm
  obtain ⟨p, hp⟩ := ih _ (by rw [← hn]; exact natDegree_lt_natDegree hr0 hr) _ rfl
  refine ⟨C (q.leadingCoeff / (D (X ^ (n + 1))).leadingCoeff) * X ^ (n + 1) + p, ?_⟩
  rw [map_add, hp, ← smul_eq_C_mul, map_smul, smul_eq_C_mul, add_sub_cancel]

open Polynomial in
/-- 3B.29 -/
theorem exercise_3B_29 (p : Polynomial ℝ) :
    ∃ q : Polynomial ℝ,
      (5 : ℝ) • q.derivative.derivative + (3 : ℝ) • q.derivative = p := by
  -- apply 28 to D = 5 D₀² + 3 D₀ itself,
  -- which lowers degree by exactly one since 3 D₀ p has degree deg p - 1 and
  -- 5 D₀² p has smaller degree.
  let D : ℝ[X] →ₗ[ℝ] ℝ[X] :=
    (5 : ℝ) • (derivative ∘ₗ derivative) + (3 : ℝ) • derivative
  have hD : ∀ p : ℝ[X], 0 < p.degree → (D p).degree + 1 = p.degree := by
    intro p hp
    have hp0 : 0 < p.natDegree := natDegree_pos_iff_degree_pos.mpr hp
    have h1 : (derivative p).degree = (p.natDegree - 1 : ℕ) := degree_derivative_eq p hp0
    have h1' : derivative p ≠ 0 := by
      intro h
      rw [h, degree_zero] at h1
      exact WithBot.bot_ne_coe h1
    have h3 : ((5 : ℝ) • derivative (derivative p)).degree < ((3 : ℝ) • derivative p).degree := by
      calc ((5 : ℝ) • derivative (derivative p)).degree
          ≤ (derivative (derivative p)).degree := degree_smul_le _ _
        _ < (derivative p).degree := degree_derivative_lt h1'
        _ = ((3 : ℝ) • derivative p).degree := by
          rw [smul_eq_C_mul, degree_C_mul (by norm_num)]
    show ((5 : ℝ) • derivative (derivative p) + (3 : ℝ) • derivative p).degree + 1 = p.degree
    rw [degree_add_eq_right_of_degree_lt h3, smul_eq_C_mul, degree_C_mul (by norm_num), h1,
      degree_eq_natDegree (ne_zero_of_natDegree_gt hp0)]
    norm_cast
    omega
  obtain ⟨q, hq⟩ := exercise_3B_28 D hD p
  exact ⟨q, hq⟩

/-- 3B.30 -/
theorem exercise_3B_30 (φ : V →ₗ[F] F) (_hφ : φ ≠ 0) (u : V)
    (hu : φ u ≠ 0) :
    IsCompl (ker φ)
      (Submodule.span F ({u} : Set V)) := by
  -- by rank nullity, image is dim 0, so has to be dim 1
  -- so ker φ has dim = dim V - 1, thus dimensions null φ and span {u} add up to dim V
  -- finally their intersction is trivial, as seen my applying T.
  -- (V is not assumed finite-dimensional here, so instead of counting dimensions
  -- write v = (v - (φ v / φ u) u) + (φ v / φ u) u directly; the first summand is
  -- in null φ.)
  refine ⟨?_, ?_⟩
  · -- null φ ⊓ span {u} = 0: c • u ∈ null φ gives c * φ u = 0, so c = 0
    rw [Submodule.disjoint_def]
    intro v hv hvu
    rw [Submodule.mem_span_singleton] at hvu
    obtain ⟨c, rfl⟩ := hvu
    rw [LinearMap.mem_ker, map_smul, smul_eq_mul] at hv
    rw [(mul_eq_zero.mp hv).resolve_right hu, zero_smul]
  · -- null φ ⊔ span {u} = V
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [← sub_add_cancel v ((φ v / φ u) • u)]
    refine Submodule.add_mem_sup ?_
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu, sub_self]

/-- 3B.31 -/
theorem exercise_3B_31 [Finite F V] (X : Submodule F V) (Y : Submodule F W) [Finite F Y] :
    (∃ T : V →ₗ[F] W,
      ker T = X ∧ range T = Y) ↔
    finrank F X + finrank F Y = finrank F V := by
  -- => by rank nullity - rank X = rank ker T = rank V - rank range T = finrank F V - finrank F Y,
  -- so finrank F X + finrank F Y = finrank F V
  -- <= take a basis vi of X and wi of Y, extend vi to basis of V
  -- construct by matching T vi = wi for all i of wi, and T vi = 0 for rest.
  -- we can only do that if #vis = #wis to hit + #rest, which is the condition.
  constructor
  · rintro ⟨T, rfl, rfl⟩
    exact finrank_ker_add_finrank_range T
  · intro hdim
    -- basis u of X (2.31), extended (2.32) to a basis v of V; basis w of Y
    obtain ⟨k, u, hu⟩ := LADR.Section_2B.exists_basis (F := F) (V := X)
    let uV : Fin k → V := fun i => (u i : V)
    have hu_li : LinearIndependent F uV :=
      hu.1.map' X.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
    obtain ⟨n, v, hkn, hv, hv_prefix⟩ := LADR.Section_2B.exists_basis_extending uV hu_li
    obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := Y)
    let wW : Fin m → W := fun j => (w j : W)
    have hw_li : LinearIndependent F wW :=
      hw.1.map' Y.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
    have hk : k = finrank F X := LADR.Section_2C.isBasis_card_eq_finrank u hu
    have hn : n = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v hv
    have hm : m = finrank F Y := LADR.Section_2C.isBasis_card_eq_finrank w hw
    -- the n - k added basis vectors are exactly as many as the wⱼ
    have hnkm : n - k = m := by omega
    -- T vᵢ = 0 for i < k (the basis of X) and T v_{k+j} = wⱼ
    let b := hv.toModuleBasis
    let T : V →ₗ[F] W := b.constr F fun i =>
      if h : i.val < k then 0 else wW ⟨i.val - k, by have := i.isLt; omega⟩
    have hT_prefix : ∀ i : Fin k, T (uV i) = 0 := by
      intro i
      have : uV i = b (Fin.castLE hkn i) := by rw [hv.toModuleBasis_apply, hv_prefix i]
      rw [this]
      simp only [T, Module.Basis.constr_basis]
      rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
    have hT_tail : ∀ (j : ℕ) (hj : j < m), T (v ⟨k + j, by omega⟩) = wW ⟨j, hj⟩ := by
      intro j hj
      have : v ⟨k + j, by omega⟩ = b ⟨k + j, by omega⟩ := (hv.toModuleBasis_apply _).symm
      rw [this]
      simp only [T, Module.Basis.constr_basis]
      rw [dif_neg (by omega)]
      congr 1
      ext
      show k + j - k = j
      omega
    have hTv : ∀ i, T (v i) ∈ Y := by
      intro i
      have : v i = b i := (hv.toModuleBasis_apply i).symm
      rw [this]
      simp only [T, Module.Basis.constr_basis]
      split_ifs
      · exact Y.zero_mem
      · exact (w _).2
    have hv_span : Submodule.span F (Set.range v) = ⊤ := hv.2
    refine ⟨T, le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
    · -- ker T ⊆ X: x = ∑ cᵢ vᵢ, T x = ∑ (tail coefficients) wⱼ = 0 forces the
      -- tail coefficients to vanish, so x = ∑ cᵢ uᵢ ∈ X
      intro x hx
      have hxv : x ∈ Submodule.span F (Set.range v) := by rw [hv_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxv
      obtain ⟨c, hc⟩ := hxv
      rw [LinearMap.mem_ker, ← hc, sum_prefix_tail hkn (fun i => c i • v i), map_add, map_sum,
        map_sum] at hx
      have hpre : ∑ i : Fin k, T (c (Fin.castLE hkn i) • v (Fin.castLE hkn i)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [map_smul, hv_prefix i, hT_prefix i, smul_zero]
      rw [hpre, zero_add] at hx
      have htail : ∑ j : Fin (n - k),
          c ⟨k + j.val, by have := j.isLt; omega⟩ • wW (Fin.cast hnkm j) = 0 := by
        rw [← hx]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hT_tail j.val (by omega)]; rfl
      have hli : LinearIndependent F fun j : Fin (n - k) => wW (Fin.cast hnkm j) :=
        hw_li.comp _ (Fin.cast_injective _)
      rw [Fintype.linearIndependent_iff] at hli
      have hc_tail := hli _ htail
      rw [← hc, sum_prefix_tail hkn (fun i => c i • v i)]
      refine X.add_mem ?_ ?_
      · exact Submodule.sum_mem _ fun i _ => by rw [hv_prefix i]; exact X.smul_mem _ (u i).2
      · exact Submodule.sum_mem _ fun j _ => by rw [hc_tail j, zero_smul]; exact X.zero_mem
    · -- X ⊆ ker T: x ∈ X is ∑ aᵢ uᵢ and T uᵢ = 0
      intro x hx
      have hu_span : Submodule.span F (Set.range u) = ⊤ := hu.2
      have hxu : (⟨x, hx⟩ : X) ∈ Submodule.span F (Set.range u) := by
        rw [hu_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxu
      obtain ⟨a, ha⟩ := hxu
      have ha' : ∑ i, a i • uV i = x := by
        have := congrArg Subtype.val ha
        rw [Submodule.coe_sum] at this
        exact this
      rw [LinearMap.mem_ker, ← ha', map_sum]
      exact Finset.sum_eq_zero fun i _ => by rw [map_smul, hT_prefix i, smul_zero]
    · -- range T ⊆ Y: every T vᵢ is in Y
      rintro _ ⟨x, rfl⟩
      have hxv : x ∈ Submodule.span F (Set.range v) := by rw [hv_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxv
      obtain ⟨c, hc⟩ := hxv
      rw [← hc, map_sum]
      exact Submodule.sum_mem _ fun i _ => by rw [map_smul]; exact Y.smul_mem _ (hTv i)
    · -- Y ⊆ range T: y = ∑ aⱼ wⱼ = T (∑ aⱼ v_{k+j})
      intro y hy
      have hw_span : Submodule.span F (Set.range w) = ⊤ := hw.2
      have hyw : (⟨y, hy⟩ : Y) ∈ Submodule.span F (Set.range w) := by
        rw [hw_span]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hyw
      obtain ⟨a, ha⟩ := hyw
      have ha' : ∑ j, a j • wW j = y := by
        have := congrArg Subtype.val ha
        rw [Submodule.coe_sum] at this
        exact this
      refine ⟨∑ j : Fin m, a j • v ⟨k + j.val, by have := j.isLt; omega⟩, ?_⟩
      rw [map_sum, ← ha']
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hT_tail j.val j.isLt]

/-- 3B.32 -/
theorem exercise_3B_32 [Finite F V] (hV : 1 < finrank F V)
    (φ : (V →ₗ[F] V) →ₗ[F] F)
    (hφ : ∀ S T : V →ₗ[F] V, φ (S ∘ₗ T) = φ S * φ T) :
    φ = 0 := by
  -- the ker of this map is a two-sided ideal
  -- if φ S is in ker, then φ S T = φ S * φ T = 0, so φ S T is also in ker
  -- if φ T is in ker, then φ S T = φ S * φ T = 0, so φ S T is also in ker
  -- but two sided ideals are either {0} or all of V by 3A exercise
  -- assume not V (otherwise done), so ker only 0,
  -- but now dimensions don't work, dim L(V) ≥ 4, and range dim is at most 1,
  -- so ker has to be all of V.
  have hL : ∀ T : V →ₗ[F] V, ∀ S ∈ ker φ, T ∘ₗ S ∈ ker φ := by
    intro T S hS
    rw [LinearMap.mem_ker] at hS ⊢
    rw [hφ, hS, mul_zero]
  have hR : ∀ T : V →ₗ[F] V, ∀ S ∈ ker φ, S ∘ₗ T ∈ ker φ := by
    intro T S hS
    rw [LinearMap.mem_ker] at hS ⊢
    rw [hφ, hS, zero_mul]
  rcases LADR.Section_3A.exercise_3A_17 (ker φ) hL hR with h | h
  · -- ker φ = 0: φ is injective, so dim L(V) ≤ dim F = 1, but dim L(V) = (dim V)² ≥ 4
    exfalso
    have h1 := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h)
    rw [Module.finrank_self, Module.finrank_linearMap] at h1
    nlinarith
  · exact LinearMap.ker_eq_top.mp h

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
    map_add' := by
      intro x y
      simp only [Prod.fst_add, map_add, Prod.snd_add, Prod.mk_add_mk]
    map_smul' := by
      intro c x
      simp only [Section_1B.complexSMul_apply, map_sub, map_smul, map_add, RingHom.id_apply] }

open LADR.Section_1B (Complexification exercise_1B_8) in
/-- 3B.33.b — the complexification is injective iff {lit}`T` is. -/
theorem exercise_3B_33_b {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] W) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    letI : Module ℂ (Complexification W) := exercise_1B_8 W
    Function.Injective (complexification_map T) ↔ Function.Injective T := by
  -- inj iff T v = 0 → v = 0, so enough to show Tc (u + i v) = 0 ↔ T v = 0 and T u = 0
  -- but this is just definition of complex 0
  rw [injective_iff_map_eq_zero, injective_iff_map_eq_zero]
  constructor
  · -- T v = 0 gives Tc (v + i 0) = (T v, T 0) = 0, so v + i 0 = 0, so v = 0
    intro h v hv
    have h0 := h (v, 0) (by show (T v, T 0) = (0, 0); rw [hv, map_zero])
    exact congrArg Prod.fst h0
  · -- Tc (u + i v) = (T u, T v) = 0 gives T u = 0 and T v = 0, so u = v = 0
    intro h p hp
    have h1 : T p.1 = 0 := congrArg Prod.fst hp
    have h2 : T p.2 = 0 := congrArg Prod.snd hp
    exact Prod.ext (h _ h1) (h _ h2)

open LADR.Section_1B (Complexification exercise_1B_8) in
/-- 3B.33.c — the complexification is surjective iff {lit}`T` is. -/
theorem exercise_3B_33_c {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] W) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    letI : Module ℂ (Complexification W) := exercise_1B_8 W
    Function.Surjective (complexification_map T) ↔ Function.Surjective T := by
  -- => find the preimage of Tc which gives the two components for the partial preimages
  -- <= find the two preimages on real and im, and combine to find one preimage
  constructor
  · -- w = Tc (u + i v) = (T u, T v), so u is a preimage of w
    intro h w
    obtain ⟨p, hp⟩ := h (w, 0)
    exact ⟨p.1, congrArg Prod.fst hp⟩
  · -- preimages u of w₁ and v of w₂ give Tc (u + i v) = (w₁, w₂)
    intro h q
    obtain ⟨u, hu⟩ := h q.1
    obtain ⟨v, hv⟩ := h q.2
    exact ⟨(u, v), Prod.ext hu hv⟩

end LADR.Section_3B
