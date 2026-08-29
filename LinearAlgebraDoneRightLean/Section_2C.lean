import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
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
import LinearAlgebraDoneRightLean.Section_1C
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 2C: Dimension
-/

namespace LADR.Section_2C

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open LADR.Section_1C (IsDirectSum)
open Module (finrank Finite)

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! 2.34 Basis length does not depend on basis -/

theorem basis_card_eq {m n : ℕ} (v : Fin m → V) (w : Fin n → V)
    (hv : IsBasis F v) (hw : IsBasis F w) : m = n := by
  obtain ⟨hv_li, hv_span⟩ := hv
  obtain ⟨hw_li, hw_span⟩ := hw
  have h1 : m ≤ n :=
    LADR.Section_2A.linearIndependent_le_spanning v w hv_li hw_span
  have h2 : n ≤ m :=
    LADR.Section_2A.linearIndependent_le_spanning w v hw_li hv_span
  omega

/-! 2.35 Definition: dimension, dim V

The *dimension* of a finite-dimensional vector space is the length of any
basis. mathlib's {name}`finrank` is exactly this, so we use it
directly throughout (no custom {lit}`dim` abbreviation). Note that
{name}`finrank` has no finite-dimensionality hypothesis: mathlib
just assigns the garbage value {lean}`0` when {lean}`V` is
infinite-dimensional. -/

/-! Bridging: the length of any basis equals {lit}`finrank F V`. -/

theorem isBasis_card_eq_finrank [Finite F V] {m : ℕ} (v : Fin m → V)
    (hv : IsBasis F v) : m = finrank F V := by
  obtain ⟨hv_li, hv_span⟩ := hv
  rw [Spans] at hv_span
  let b : Module.Basis (Fin m) F V :=
    Module.Basis.mk hv_li (by rw [hv_span])
  simp [Module.finrank_eq_card_basis b]

/-! 2.36 Example: dimensions -/

example (n : ℕ) : finrank F (Fin n → F) = n := by simp

example (m : ℕ) : finrank F (Polynomial.degreeLT F (m + 1)) = m + 1 := by
  simp only [(Polynomial.degreeLTEquiv F (m + 1)).finrank_eq,
    Module.finrank_pi, Fintype.card_fin]

example : finrank F (LADR.Section_2B.U_27e F) = 2 := by
  obtain ⟨hli, hspan⟩ := LADR.Section_2B.isBasis_basisVec_27e (F := F)
  rw [Spans] at hspan
  let b : Module.Basis (Fin 2) F (LADR.Section_2B.U_27e F) :=
    Module.Basis.mk hli (by rw [hspan])
  simp [Module.finrank_eq_card_basis b]

example : finrank F (LADR.Section_2B.U_27f F) = 2 := by
  obtain ⟨hli, hspan⟩ := LADR.Section_2B.isBasis_basisVec_27f (F := F)
  rw [Spans] at hspan
  let b : Module.Basis (Fin 2) F (LADR.Section_2B.U_27f F) :=
    Module.Basis.mk hli (by rw [hspan])
  simp [Module.finrank_eq_card_basis b]

/-! 2.37 Dimension of a subspace -/

@[avoiding Submodule.finrank_le]
theorem finrank_submodule_le [Finite F V] (U : Submodule F V) :
    finrank F U ≤ finrank F V := by
  classical
  obtain ⟨m, u, hu_basis⟩ :=
    LADR.Section_2B.exists_basis (F := F) (V := U)
  obtain ⟨n, w, hw_basis⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
  let uV : Fin m → V := fun i => (u i : V)
  have hu_li_V : LinearIndependent F uV :=
    hu_basis.1.map' U.subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hmn : m ≤ n :=
    LADR.Section_2A.linearIndependent_le_spanning uV w hu_li_V hw_basis.2
  have hm : m = finrank F U := isBasis_card_eq_finrank u hu_basis
  have hn : n = finrank F V := isBasis_card_eq_finrank w hw_basis
  omega

/-! 2.38 Linearly independent list of the right length is a basis -/

@[avoiding LinearIndependent.span_eq_top_of_card_eq_finrank']
theorem isBasis_of_linearIndependent_of_card_eq [Finite F V] {m : ℕ}
    (v : Fin m → V) (hv : LinearIndependent F v) (hm : m = finrank F V) :
    IsBasis F v := by
  obtain ⟨n, w, hmn, hw_basis, hw_prefix⟩ := LADR.Section_2B.exists_basis_extending v hv
  have hn : n = finrank F V := isBasis_card_eq_finrank w hw_basis
  have hmn_eq : m = n := by omega
  subst hmn_eq
  have hv_eq : v = w := by
    funext i
    have := hw_prefix i
    simpa [Fin.castLE] using this.symm
  rw [hv_eq]; exact hw_basis

/-! 2.39 Subspace of full dimension equals the whole space -/

@[avoiding Submodule.eq_top_of_finrank_eq]
theorem subspace_eq_top_of_finrank_eq [Finite F V] (U : Submodule F V)
    (h : finrank F U = finrank F V) : U = ⊤ := by
  classical
  obtain ⟨m, u, hu_basis⟩ :=
    LADR.Section_2B.exists_basis (F := F) (V := U)
  let uV : Fin m → V := fun i => (u i : V)
  have hu_li_V : LinearIndependent F uV :=
    hu_basis.1.map' U.subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hm_U : m = finrank F U := isBasis_card_eq_finrank u hu_basis
  have hm_V : m = finrank F V := hm_U.trans h
  have huV_basis : IsBasis F uV :=
    isBasis_of_linearIndependent_of_card_eq uV hu_li_V hm_V
  have hspan : Submodule.span F (Set.range uV) = ⊤ := huV_basis.2
  rw [eq_top_iff, ← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (u i).property

/-! 2.40 Example: a basis of {lit}`F²` -/
example [CharZero F] : IsBasis F (![![5, 7], ![4, 3]] : Fin 2 → Fin 2 → F) := by
  apply isBasis_of_linearIndependent_of_card_eq
  · rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : 5 * a 0 + 4 * a 1 = 0 := by
      have := congrFun ha 0
      simpa [Fin.sum_univ_two, Matrix.cons_val_zero, smul_eq_mul,
        mul_comm] using this
    have h1 : 7 * a 0 + 3 * a 1 = 0 := by
      have := congrFun ha 1
      simpa [Fin.sum_univ_two, Matrix.cons_val_one, Matrix.head_cons,
        smul_eq_mul, mul_comm] using this
    have ha0 : a 0 = 0 := by
      have h13 : (-13 : F) * a 0 = 0 := by linear_combination 3 * h0 - 4 * h1
      have h13ne : (-13 : F) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h13).resolve_left h13ne
    have ha1 : a 1 = 0 := by
      have h4 : (4 : F) * a 1 = 0 := by linear_combination h0 - 5 * ha0
      have h4ne : (4 : F) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h4).resolve_left h4ne
    intro i
    fin_cases i <;> simp [ha0, ha1]
  · simp

/-! 2.41 Example: a basis of a subspace of {lit}`P₃(ℝ)` -/

/-- The subspace of {lit}`P₃(ℝ)` cut out by {lit}`p'(5) = 0`. -/
noncomputable def U_2_41 : Submodule ℝ (Polynomial.degreeLT ℝ 4) where
  carrier := {p | (p.val.derivative.eval 5 : ℝ) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    show (p.val + q.val).derivative.eval 5 = 0
    rw [Polynomial.derivative_add, Polynomial.eval_add, hp, hq, add_zero]
  smul_mem' := by
    intro a p hp
    show (a • p.val).derivative.eval 5 = 0
    rw [Polynomial.derivative_smul, Polynomial.eval_smul, hp, smul_zero]

/-- {lit}`(X - 5)^k` has degree {lit}`k`, hence lives in {lit}`degreeLT ℝ 4`
when {lit}`k < 4`. -/
private lemma xSub5_pow_mem_degreeLT (k : ℕ) (hk : k < 4) :
    (Polynomial.X - Polynomial.C (5 : ℝ)) ^ k ∈ Polynomial.degreeLT ℝ 4 := by
  rw [Polynomial.mem_degreeLT]
  rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
  simp only [nsmul_eq_mul, mul_one, Nat.cast_lt]
  exact_mod_cast hk

/-- The derivative of {lit}`(X - 5)^k` evaluated at {lit}`5` is {lit}`0` for
{lit}`k ≥ 2`. -/
private lemma xSub5_pow_derivative_eval (k : ℕ) (hk : 2 ≤ k) :
    ((Polynomial.X - Polynomial.C (5 : ℝ)) ^ k).derivative.eval 5 = 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp [Polynomial.derivative_pow, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C]
  have hk' : 1 ≤ k' := by omega
  obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
  simp

/-- The list {lit}`1, (x-5)², (x-5)³` inside {lit}`U_2_41`. -/
noncomputable def basisVec_2_41 : Fin 3 → U_2_41 :=
  ![⟨⟨(1 : Polynomial ℝ), by rw [Polynomial.mem_degreeLT]; simp⟩,
      by show (1 : Polynomial ℝ).derivative.eval 5 = 0; simp⟩,
    ⟨⟨(Polynomial.X - Polynomial.C 5) ^ 2,
        xSub5_pow_mem_degreeLT 2 (by decide)⟩,
      xSub5_pow_derivative_eval 2 (by decide)⟩,
    ⟨⟨(Polynomial.X - Polynomial.C 5) ^ 3,
        xSub5_pow_mem_degreeLT 3 (by decide)⟩,
      xSub5_pow_derivative_eval 3 (by decide)⟩]

/-- The underlying polynomial of {lit}`basisVec_2_41 i`. -/
private noncomputable def basisVec_2_41_poly : Fin 3 → Polynomial ℝ :=
  ![1, (Polynomial.X - Polynomial.C 5) ^ 2, (Polynomial.X - Polynomial.C 5) ^ 3]

private lemma basisVec_2_41_coe (i : Fin 3) :
    ((basisVec_2_41 i : Polynomial.degreeLT ℝ 4) : Polynomial ℝ)
      = basisVec_2_41_poly i := by
  fin_cases i <;> rfl

/-- Linear independence of the underlying polynomial list
{lit}`1, (X-5)², (X-5)³`, by repeatedly differentiating the vanishing
combination and evaluating at {lit}`5`. -/
private theorem linearIndependent_basisVec_2_41_poly :
    LinearIndependent ℝ basisVec_2_41_poly := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  -- The vanishing combination: {lit}`a₀ + a₁(X-5)² + a₂(X-5)³ = 0`.
  have ha_poly : a 0 • (1 : Polynomial ℝ)
      + a 1 • (Polynomial.X - Polynomial.C 5) ^ 2
      + a 2 • (Polynomial.X - Polynomial.C 5) ^ 3 = 0 := by
    have := ha
    rw [Fin.sum_univ_three] at this
    simpa [basisVec_2_41_poly] using this
  -- Evaluate at 5: only {lit}`a₀` survives.
  have ha0 : a 0 = 0 := by
    have h := congrArg (Polynomial.eval 5) ha_poly
    simp [Polynomial.eval_smul, smul_eq_mul] at h
    linarith
  rw [ha0, zero_smul, zero_add] at ha_poly
  -- 2nd derivative at 5: {lit}`((X-5)²)''(5) = 2`, {lit}`((X-5)³)''(5) = 0`,
  -- so eval at 5 gives {lit}`2 a₁ = 0`.
  have ha1 : a 1 = 0 := by
    have h := congrArg
      (fun p => (Polynomial.derivative (Polynomial.derivative p)).eval 5)
      ha_poly
    simp only [map_add, map_smul, Polynomial.eval_add, Polynomial.eval_smul,
      smul_eq_mul] at h
    have h2 : (Polynomial.derivative (Polynomial.derivative
        ((Polynomial.X - Polynomial.C (5 : ℝ)) ^ 2))).eval 5 = 2 := by
      simp [Polynomial.derivative_pow, Polynomial.derivative_sub,
        Polynomial.derivative_X, Polynomial.derivative_C]
    have h3 : (Polynomial.derivative (Polynomial.derivative
        ((Polynomial.X - Polynomial.C (5 : ℝ)) ^ 3))).eval 5 = 0 := by
      simp [Polynomial.derivative_pow, Polynomial.derivative_sub,
        Polynomial.derivative_X, Polynomial.derivative_C]
    rw [h2, h3] at h
    simp at h
    linarith
  rw [ha1, zero_smul, zero_add] at ha_poly
  -- {lit}`a₂ · (X-5)³ = 0`, but {lit}`(X-5)³ ≠ 0`, so {lit}`a₂ = 0`.
  have ha2 : a 2 = 0 := by
    rw [smul_eq_zero] at ha_poly
    rcases ha_poly with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 5))
  intro i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2

/-- The linear map {lit}`U_2_41 → Polynomial ℝ`. -/
private noncomputable def U_2_41_toPoly : U_2_41 →ₗ[ℝ] Polynomial ℝ :=
  (Polynomial.degreeLT ℝ 4).subtype ∘ₗ U_2_41.subtype

private lemma U_2_41_toPoly_basisVec :
    U_2_41_toPoly ∘ basisVec_2_41 = basisVec_2_41_poly := by
  funext i
  fin_cases i <;> rfl

private theorem linearIndependent_basisVec_2_41 :
    LinearIndependent ℝ basisVec_2_41 := by
  apply LinearIndependent.of_comp U_2_41_toPoly
  rw [U_2_41_toPoly_basisVec]
  exact linearIndependent_basisVec_2_41_poly

/-- {lit}`X ∉ U_2_41` because {lit}`X.derivative.eval 5 = 1 ≠ 0`. -/
private lemma X_not_mem_U_2_41 :
    (⟨Polynomial.X, by
        rw [Polynomial.mem_degreeLT, Polynomial.degree_X]
        decide⟩ : Polynomial.degreeLT ℝ 4) ∉ U_2_41 := by
  intro h
  have : (Polynomial.X : Polynomial ℝ).derivative.eval 5 = 0 := h
  simp at this

/-- {lit}`U_2_41` is finite-dimensional (as a submodule of a fin-dim space). -/
instance : Finite ℝ U_2_41 := by
  have : Finite ℝ (Polynomial.degreeLT ℝ 4) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℝ 4).symm
  exact Module.Finite.of_injective U_2_41.subtype Subtype.val_injective

/-- {lit}`dim U_2_41 = 3`. -/
private theorem finrank_U_2_41 : finrank ℝ U_2_41 = 3 := by
  -- Lower bound: the 3-vector LI list lives in {lit}`U_2_41`, so
  -- {lit}`3 ≤ dim U_2_41`.
  have hLI := linearIndependent_basisVec_2_41
  have hP : Finite ℝ (Polynomial.degreeLT ℝ 4) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℝ 4).symm
  have hge : 3 ≤ finrank ℝ U_2_41 := by
    haveI : FiniteDimensional ℝ U_2_41 := inferInstance
    have := hLI.fintype_card_le_finrank
    simpa using this
  -- Upper bound: {lit}`dim U_2_41 ≤ dim P₃(ℝ) = 4`. We exclude {lit}`= 4`
  -- because {lit}`X ∉ U_2_41`, so {lit}`U_2_41 ≠ ⊤`; by 2.39 this forces
  -- {lit}`dim U_2_41 ≠ 4`, hence {lit}`≤ 3`.
  have hdimP : finrank ℝ (Polynomial.degreeLT ℝ 4) = 4 := by
    simp only [(Polynomial.degreeLTEquiv ℝ 4).finrank_eq,
      Module.finrank_pi, Fintype.card_fin]
  have hle_4 : finrank ℝ U_2_41 ≤ 4 := by
    have := finrank_submodule_le U_2_41
    rw [hdimP] at this; exact this
  have hne_top : U_2_41 ≠ ⊤ := fun h => X_not_mem_U_2_41 (by rw [h]; trivial)
  have hne_4 : finrank ℝ U_2_41 ≠ 4 := by
    intro heq
    apply hne_top
    apply subspace_eq_top_of_finrank_eq
    rw [heq, hdimP]
  omega

theorem isBasis_basisVec_2_41 : IsBasis ℝ basisVec_2_41 :=
  isBasis_of_linearIndependent_of_card_eq basisVec_2_41
    linearIndependent_basisVec_2_41 (by rw [finrank_U_2_41])

/-! 2.42 Spanning list of the right length is a basis -/
@[avoiding linearIndependent_of_top_le_span_of_card_eq_finrank]
theorem isBasis_of_spans_of_card_eq [Finite F V] {m : ℕ}
    (v : Fin m → V) (hv : Spans F v) (hm : m = finrank F V) :
    IsBasis F v := by
  refine ⟨?_, hv⟩
  by_contra hdep
  obtain ⟨k, _, hspan_eq⟩ :=
    LADR.Section_2A.linearDependence_lemma v hdep
  have hm_pos : m ≠ 0 := fun h => (h ▸ k).elim0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  let w : Fin m' → V := v ∘ k.succAbove
  have hw_range : Set.range w = v '' {i | i ≠ k} := by
    show Set.range (v ∘ k.succAbove) = v '' {i | i ≠ k}
    rw [Set.range_comp, Fin.range_succAbove]; rfl
  have hw_spans : Spans F w := by
    show Submodule.span F (Set.range w) = ⊤
    rw [hw_range, ← hspan_eq]; exact hv
  obtain ⟨n, u, hu_basis⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
  have hn : n = finrank F V := isBasis_card_eq_finrank u hu_basis
  have hle : n ≤ m' :=
    LADR.Section_2A.linearIndependent_le_spanning u w hu_basis.1 hw_spans
  omega

/-! 2.43 Dimension of a sum

Axler's argument: pick a basis {lit}`u₁, …, u_m` of {lit}`V₁ ⊓ V₂`; extend
it to a basis {lit}`u₁, …, u_m, v₁, …, v_j` of {lit}`V₁` and to a basis
{lit}`u₁, …, u_m, w₁, …, w_k` of {lit}`V₂` (2.32). The concatenated list
{lit}`u₁, …, u_m, v₁, …, v_j, w₁, …, w_k` is a basis of {lit}`V₁ + V₂`,
hence {lit}`dim(V₁+V₂) = m + j + k = (m+j) + (m+k) - m = dim V₁ + dim V₂
- dim(V₁⊓V₂)`. -/

section dim_sum

variable [Finite F V] (V₁ V₂ : Submodule F V)

@[avoiding Submodule.finrank_sup_add_finrank_inf_eq]
theorem finrank_sup_add_finrank_inf_eq :
    finrank F ↥(V₁ ⊔ V₂) + finrank F ↥(V₁ ⊓ V₂) =
      finrank F V₁ + finrank F V₂ := by
  classical
  obtain ⟨m, u, hu_basis⟩ :=
    LADR.Section_2B.exists_basis (F := F) (V := ↥(V₁ ⊓ V₂))
  have hm_inf : m = finrank F ↥(V₁ ⊓ V₂) :=
    isBasis_card_eq_finrank u hu_basis
  let uV1 : Fin m → ↥V₁ := fun i => ⟨(u i : V), (u i).property.1⟩
  let uV2 : Fin m → ↥V₂ := fun i => ⟨(u i : V), (u i).property.2⟩
  have huV1_li : LinearIndependent F uV1 :=
    hu_basis.1.map' (Submodule.inclusion (inf_le_left (b := V₂)))
      (LinearMap.ker_eq_bot_of_injective
        (Submodule.inclusion_injective (inf_le_left (b := V₂))))
  have huV2_li : LinearIndependent F uV2 :=
    hu_basis.1.map' (Submodule.inclusion (inf_le_right (a := V₁)))
      (LinearMap.ker_eq_bot_of_injective
        (Submodule.inclusion_injective (inf_le_right (a := V₁))))
  obtain ⟨n1, v, hmn1, hv_basis, hv_prefix⟩ :=
    LADR.Section_2B.exists_basis_extending uV1 huV1_li
  obtain ⟨j, rfl⟩ : ∃ j, n1 = m + j := ⟨n1 - m, by omega⟩
  have hv_len : m + j = finrank F ↥V₁ :=
    isBasis_card_eq_finrank v hv_basis
  obtain ⟨n2, w, hmn2, hw_basis, hw_prefix⟩ :=
    LADR.Section_2B.exists_basis_extending uV2 huV2_li
  obtain ⟨k, rfl⟩ : ∃ k, n2 = m + k := ⟨n2 - m, by omega⟩
  have hw_len : m + k = finrank F ↥V₂ :=
    isBasis_card_eq_finrank w hw_basis
  let vV : Fin (m + j) → V := fun p => (v p : V)
  let wTail : Fin k → V := fun q => (w (Fin.natAdd m q) : V)
  let joint : Fin ((m + j) + k) → V := Fin.append vV wTail
  have hv_prefix_V : ∀ i : Fin m, vV (Fin.castAdd j i) = (u i : V) := by
    intro i
    have h := hv_prefix i
    have hfin : (Fin.castAdd j i : Fin (m + j)) = Fin.castLE hmn1 i := rfl
    show (v (Fin.castAdd j i) : V) = (u i : V)
    rw [hfin, h]
  have hw_prefix_V : ∀ i : Fin m, (w (Fin.castAdd k i) : V) = (u i : V) := by
    intro i
    have h := hw_prefix i
    have hfin : (Fin.castAdd k i : Fin (m + k)) = Fin.castLE hmn2 i := rfl
    rw [hfin, h]
  have hjoint_mem : ∀ r, joint r ∈ V₁ ⊔ V₂ := by
    refine Fin.addCases (fun p => ?_) (fun q => ?_)
    · rw [show joint (Fin.castAdd k p) = vV p from Fin.append_left _ _ _]
      exact (le_sup_left : V₁ ≤ V₁ ⊔ V₂) (v p).property
    · rw [show joint (Fin.natAdd (m + j) q) = wTail q from Fin.append_right _ _ _]
      exact (le_sup_right : V₂ ≤ V₁ ⊔ V₂) (w (Fin.natAdd m q)).property
  let jointS : Fin ((m + j) + k) → ↥(V₁ ⊔ V₂) := fun r => ⟨joint r, hjoint_mem r⟩
  have hjointS_spans : Spans F jointS := by
    show Submodule.span F (Set.range jointS) = ⊤
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ _
    rw [Submodule.mem_sup] at hx
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
    have hv_span : Submodule.span F (Set.range v) = ⊤ := hv_basis.2
    have hx₁_in : (⟨x₁, hx₁⟩ : ↥V₁) ∈ Submodule.span F (Set.range v) := by
      rw [hv_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx₁_in
    obtain ⟨a, ha⟩ := hx₁_in
    have hw_span : Submodule.span F (Set.range w) = ⊤ := hw_basis.2
    have hx₂_in : (⟨x₂, hx₂⟩ : ↥V₂) ∈ Submodule.span F (Set.range w) := by
      rw [hw_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx₂_in
    obtain ⟨b, hb⟩ := hx₂_in
    -- Joint coefficients via nested Fin.append: at the u-block (first m
    -- positions of vV) put aLift + bLift; at the v-tail put aTail; at the
    -- w-tail put bTail. Each block lookup is then a Fin.append_left/right.
    let aLift : Fin m → F := fun i => a (Fin.castAdd j i)
    let bLift : Fin m → F := fun i => b (Fin.castAdd k i)
    let aTail : Fin j → F := fun q => a (Fin.natAdd m q)
    let bTail : Fin k → F := fun q => b (Fin.natAdd m q)
    let cTop : Fin (m + j) → F := Fin.append (aLift + bLift) aTail
    let c : Fin (m + j + k) → F := Fin.append cTop bTail
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, ?_⟩
    apply Subtype.ext
    rw [Submodule.coe_sum]
    show ∑ r, (c r • jointS r : V) = x₁ + x₂
    have hsum_coe : ∑ r, (c r • jointS r : V) = ∑ r, c r • (joint r : V) :=
      Finset.sum_congr rfl (fun r _ => rfl)
    rw [hsum_coe, Fin.sum_univ_add (f := fun r => c r • (joint r : V)),
        Fin.sum_univ_add (f := fun p => c (Fin.castAdd k p) • (joint (Fin.castAdd k p) : V))]
    -- u-block: cTop's prefix is aLift + bLift, joint reduces to u via vV-prefix.
    have hu_block : ∑ i : Fin m,
        c (Fin.castAdd k (Fin.castAdd j i)) • (joint (Fin.castAdd k (Fin.castAdd j i)) : V) =
        (∑ i, aLift i • (u i : V)) + ∑ i, bLift i • (u i : V) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have hc : c (Fin.castAdd k (Fin.castAdd j i)) = aLift i + bLift i := by
        show Fin.append cTop bTail (Fin.castAdd k _) = _
        rw [Fin.append_left]
        exact Fin.append_left (aLift + bLift) aTail i
      have hj : (joint (Fin.castAdd k (Fin.castAdd j i)) : V) = (u i : V) := by
        show (Fin.append vV wTail (Fin.castAdd k _) : V) = _
        rw [Fin.append_left]; exact hv_prefix_V i
      rw [hc, hj, add_smul]
    -- v-tail block: cTop's tail is aTail.
    have hv_block : ∑ q : Fin j,
        c (Fin.castAdd k (Fin.natAdd m q)) • (joint (Fin.castAdd k (Fin.natAdd m q)) : V) =
        ∑ q : Fin j, aTail q • (v (Fin.natAdd m q) : V) := by
      apply Finset.sum_congr rfl
      intro q _
      have hc : c (Fin.castAdd k (Fin.natAdd m q)) = aTail q := by
        show Fin.append cTop bTail (Fin.castAdd k _) = _
        rw [Fin.append_left]
        exact Fin.append_right (aLift + bLift) aTail q
      have hj : (joint (Fin.castAdd k (Fin.natAdd m q)) : V) = (v (Fin.natAdd m q) : V) := by
        show (Fin.append vV wTail (Fin.castAdd k _) : V) = _
        rw [Fin.append_left]
      rw [hc, hj]
    -- w-tail block.
    have hw_block : ∑ q : Fin k,
        c (Fin.natAdd (m + j) q) • (joint (Fin.natAdd (m + j) q) : V) =
        ∑ q : Fin k, bTail q • (w (Fin.natAdd m q) : V) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [show c (Fin.natAdd (m + j) q) = bTail q from Fin.append_right _ _ _,
          show (joint (Fin.natAdd (m + j) q) : V) = (w (Fin.natAdd m q) : V) from
            Fin.append_right _ _ _]
    rw [hu_block, hv_block, hw_block]
    -- Express x₁, x₂ in the same split-sum form.
    have hx₁_split : x₁ = (∑ i, aLift i • (u i : V)) +
        ∑ q, aTail q • (v (Fin.natAdd m q) : V) := by
      have hsum_V : ∑ p, a p • (v p : V) = x₁ := by
        have h := congrArg (Subtype.val (p := fun x => x ∈ V₁)) ha
        rw [Submodule.coe_sum] at h
        convert h using 1
      rw [← hsum_V, Fin.sum_univ_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show (v (Fin.castAdd j i) : V) = (u i : V) from hv_prefix_V i]
    have hx₂_split : x₂ = (∑ i, bLift i • (u i : V)) +
        ∑ q, bTail q • (w (Fin.natAdd m q) : V) := by
      have hsum_V : ∑ p, b p • (w p : V) = x₂ := by
        have h := congrArg (Subtype.val (p := fun x => x ∈ V₂)) hb
        rw [Submodule.coe_sum] at h
        convert h using 1
      rw [← hsum_V, Fin.sum_univ_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show (w (Fin.castAdd k i) : V) = (u i : V) from hw_prefix_V i]
    rw [hx₁_split, hx₂_split]
    abel
  have hjointS_li : LinearIndependent F jointS := by
    rw [Fintype.linearIndependent_iff]
    intro c hc r
    have hc_V : ∑ r, c r • (joint r : V) = 0 := by
      have := congrArg (Subtype.val (p := fun x => x ∈ V₁ ⊔ V₂)) hc
      rw [Submodule.coe_sum] at this
      rw [show (0 : ↥(V₁ ⊔ V₂)).val = (0 : V) from rfl] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro r _; rfl
    rw [Fin.sum_univ_add (f := fun r => c r • (joint r : V)),
        Fin.sum_univ_add (f := fun p => c (Fin.castAdd k p) • (joint (Fin.castAdd k p) : V))]
        at hc_V
    let aF : Fin m → F := fun i => c (Fin.castAdd k (Fin.castAdd j i))
    let bF : Fin j → F := fun q => c (Fin.castAdd k (Fin.natAdd m q))
    let dF : Fin k → F := fun q => c (Fin.natAdd (m + j) q)
    have hSumA : ∑ i : Fin m,
        c (Fin.castAdd k (Fin.castAdd j i)) • (joint (Fin.castAdd k (Fin.castAdd j i)) : V) =
        ∑ i, aF i • (u i : V) := by
      apply Finset.sum_congr rfl
      intro i _
      show _ = aF i • (u i : V)
      rw [show (joint (Fin.castAdd k (Fin.castAdd j i)) : V) = (u i : V) by
            show (Fin.append vV wTail (Fin.castAdd k _) : V) = _
            rw [Fin.append_left]; exact hv_prefix_V i]
    have hSumB : ∑ q : Fin j,
        c (Fin.castAdd k (Fin.natAdd m q)) • (joint (Fin.castAdd k (Fin.natAdd m q)) : V) =
        ∑ q, bF q • (v (Fin.natAdd m q) : V) := by
      apply Finset.sum_congr rfl
      intro q _
      show _ = bF q • _
      rw [show (joint (Fin.castAdd k (Fin.natAdd m q)) : V) = (v (Fin.natAdd m q) : V) by
            show (Fin.append vV wTail (Fin.castAdd k _) : V) = _
            rw [Fin.append_left]]
    have hSumD : ∑ q : Fin k,
        c (Fin.natAdd (m + j) q) • (joint (Fin.natAdd (m + j) q) : V) =
        ∑ q, dF q • (w (Fin.natAdd m q) : V) := by
      apply Finset.sum_congr rfl
      intro q _
      show _ = dF q • _
      rw [show (joint (Fin.natAdd (m + j) q) : V) = (w (Fin.natAdd m q) : V) by
            show (Fin.append vV wTail (Fin.natAdd (m + j) _) : V) = _
            rw [Fin.append_right]]
    rw [hSumA, hSumB, hSumD] at hc_V
    -- Axler's central move: the w-tail sum y lies in V₂ by construction and
    -- in V₁ because it equals -(u-block + v-tail-block), hence in V₁ ⊓ V₂,
    -- so it expands in basis u; then LI of w in V₂ kills the w-tail
    -- coefficients, after which LI of v in V₁ kills the rest.
    set y : V := ∑ q : Fin k, dF q • (w (Fin.natAdd m q) : V) with hy_def
    have hy_eq_neg :
        y = - ((∑ i, aF i • (u i : V))
              + ∑ q, bF q • (v (Fin.natAdd m q) : V)) := by
      have h : (∑ i, aF i • (u i : V))
        + ∑ q, bF q • (v (Fin.natAdd m q) : V) + y = 0 := hc_V
      exact eq_neg_of_add_eq_zero_left (add_comm _ y ▸ h)
    have hy_in_V2 : y ∈ V₂ := by
      rw [hy_def]
      apply Submodule.sum_mem; intro q _
      exact V₂.smul_mem _ (w (Fin.natAdd m q)).property
    have hy_in_V1 : y ∈ V₁ := by
      rw [hy_eq_neg]
      apply Submodule.neg_mem; apply Submodule.add_mem
      · apply Submodule.sum_mem; intro i _; exact V₁.smul_mem _ (u i).property.1
      · apply Submodule.sum_mem; intro q _; exact V₁.smul_mem _ (v (Fin.natAdd m q)).property
    have hy_in_inf : y ∈ V₁ ⊓ V₂ := ⟨hy_in_V1, hy_in_V2⟩
    have hu_span : Submodule.span F (Set.range u) = ⊤ := hu_basis.2
    have : (⟨y, hy_in_inf⟩ : ↥(V₁ ⊓ V₂)) ∈ Submodule.span F (Set.range u) := by
      rw [hu_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at this
    obtain ⟨e, he⟩ := this
    have he_V : ∑ i : Fin m, e i • (u i : V) = y := by
      have h := congrArg
        (Subtype.val (p := fun x => x ∈ V₁ ⊓ V₂)) he
      rw [Submodule.coe_sum] at h
      convert h using 1
    have hw_li := hw_basis.1
    rw [Fintype.linearIndependent_iff] at hw_li
    -- Build cw : Fin (m+k) → F via Fin.append, so its value at each block
    -- is given by Fin.append_left / Fin.append_right.
    let cw : Fin (m + k) → F := Fin.append e (-dF)
    have hcw_sum : ∑ p, cw p • w p = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul_of_tower]
      rw [Fin.sum_univ_add (f := fun p => cw p • (w p : V))]
      have hprefix : ∑ i : Fin m, cw (Fin.castAdd k i) • (w (Fin.castAdd k i) : V) =
          ∑ i : Fin m, e i • (u i : V) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show cw (Fin.castAdd k i) = e i from Fin.append_left _ _ _, hw_prefix_V i]
      have htail : ∑ q : Fin k, cw (Fin.natAdd m q) • (w (Fin.natAdd m q) : V) =
          -∑ q : Fin k, dF q • (w (Fin.natAdd m q) : V) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro q _
        rw [show cw (Fin.natAdd m q) = -dF q from Fin.append_right _ _ _, neg_smul]
      rw [hprefix, htail, he_V, ← hy_def, add_neg_cancel]
    have hcw_zero := hw_li cw hcw_sum
    have hdF_zero : ∀ q : Fin k, dF q = 0 := by
      intro q
      have hcw_tail : cw (Fin.natAdd m q) = 0 := hcw_zero _
      have hcw_eq : cw (Fin.natAdd m q) = -dF q := Fin.append_right _ _ _
      exact neg_eq_zero.mp (hcw_eq ▸ hcw_tail)
    have hy_zero : y = 0 := by
      rw [hy_def]
      apply Finset.sum_eq_zero
      intro q _
      rw [hdF_zero q, zero_smul]
    have hABzero : (∑ i, aF i • (u i : V))
        + ∑ q, bF q • (v (Fin.natAdd m q) : V) = 0 := by
      have h := hy_eq_neg
      rw [hy_zero] at h
      exact neg_eq_zero.mp (h.symm)
    have hv_li := hv_basis.1
    rw [Fintype.linearIndependent_iff] at hv_li
    let cv : Fin (m + j) → F := Fin.append aF bF
    have hcv_sum : ∑ p, cv p • v p = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul_of_tower]
      rw [Fin.sum_univ_add (f := fun p => cv p • (v p : V))]
      have hprefix : ∑ i : Fin m, cv (Fin.castAdd j i) • (v (Fin.castAdd j i) : V) =
          ∑ i, aF i • (u i : V) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show cv (Fin.castAdd j i) = aF i from Fin.append_left _ _ _,
            show (v (Fin.castAdd j i) : V) = (u i : V) from hv_prefix_V i]
      have htail : ∑ q : Fin j, cv (Fin.natAdd m q) • (v (Fin.natAdd m q) : V) =
          ∑ q, bF q • (v (Fin.natAdd m q) : V) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [show cv (Fin.natAdd m q) = bF q from Fin.append_right _ _ _]
      rw [hprefix, htail]; exact hABzero
    have hcv_zero := hv_li cv hcv_sum
    -- Split r : Fin (m+j+k) into the joint's two blocks via Fin.addCases;
    -- in each block c r reduces to aF / bF / dF, all zero by the LI lemmas.
    refine r.addCases (fun p => ?_) (fun q => ?_)
    · refine p.addCases (fun i => ?_) (fun q => ?_)
      · show aF i = 0
        rw [show aF i = cv (Fin.castAdd j i) from (Fin.append_left _ _ _).symm]
        exact hcv_zero _
      · show bF q = 0
        rw [show bF q = cv (Fin.natAdd m q) from (Fin.append_right _ _ _).symm]
        exact hcv_zero _
    · show dF q = 0
      exact hdF_zero q
  have hjointS_basis : IsBasis F jointS := ⟨hjointS_li, hjointS_spans⟩
  have hsup_len : m + j + k = finrank F ↥(V₁ ⊔ V₂) :=
    isBasis_card_eq_finrank jointS hjointS_basis
  omega

end dim_sum

/-! # Exercises -/

/-- 2C.1 (we replace lines containing 0 with subspaces of rank 1) -/
theorem exercise_2C_1 (U : Submodule ℝ (Fin 2 → ℝ)) :
    U = ⊥ ∨ finrank ℝ U = 1 ∨ U = ⊤ := by
  sorry

/-- 2C.2 (we replace lines containing 0 with subspaces of rank 1, and
planes through the origin with subspaces of rank 2) -/
theorem exercise_2C_2 (U : Submodule ℝ (Fin 3 → ℝ)) :
    U = ⊥ ∨ finrank ℝ U = 1 ∨ finrank ℝ U = 2 ∨ U = ⊤ := by
  sorry

/-! 2C.3 -/

def U_2C_3 (F : Type*) [Field F] : Submodule F (Polynomial.degreeLT F 5) where
  carrier := {p | (p.val.eval 6 : F) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    show (p.val + q.val).eval 6 = 0
    rw [Polynomial.eval_add, hp, hq, add_zero]
  smul_mem' := by
    intro a p hp
    show (a • p.val).eval 6 = 0
    rw [Polynomial.eval_smul, hp, smul_zero]

/-- 2C.3 (a): find a list for a basis of {lit}`U_2C_3`. -/
noncomputable def U_2C_3_basis (F : Type*) [Field F] : Fin sorry → U_2C_3 F := sorry
theorem exercise_2C_3a : IsBasis F (U_2C_3_basis F) := by
  sorry

/-- (b) Extension of the {lit}`U_2C_3` basis to a basis of {lit}`P₄(F)`. -/
noncomputable def U_2C_3_extension (F : Type*) [Field F] :
    Fin sorry → Polynomial.degreeLT F 5 := sorry
theorem exercise_2C_3b :
    IsBasis F (Fin.append (fun i => ((U_2C_3_basis F i : Polynomial.degreeLT F 5)))
      (U_2C_3_extension F)) := by
  sorry

noncomputable def W_2C_3 (F : Type*) [Field F] :
    Submodule F (Polynomial.degreeLT F 5) := sorry
theorem exercise_2C_3c : IsCompl (U_2C_3 F) (W_2C_3 F) := by
  sorry

/-! 2C.4 -/
noncomputable def U_2C_4 : Submodule ℝ (Polynomial.degreeLT ℝ 5) where
  carrier := {p | (p.val.derivative.derivative.eval 6 : ℝ) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    show (p.val + q.val).derivative.derivative.eval 6 = 0
    rw [Polynomial.derivative_add, Polynomial.derivative_add,
      Polynomial.eval_add, hp, hq, add_zero]
  smul_mem' := by
    intro a p hp
    show (a • p.val).derivative.derivative.eval 6 = 0
    rw [Polynomial.derivative_smul, Polynomial.derivative_smul,
      Polynomial.eval_smul, hp, smul_zero]

/-- (a) A basis of {lit}`U_2C_4`. -/
noncomputable def U_2C_4_basis : Fin sorry → U_2C_4 := sorry

/-- 2C.4 (a): the chosen list is a basis of {lit}`U_2C_4`. -/
theorem exercise_2C_4a : IsBasis ℝ U_2C_4_basis := by
  sorry

/-- (b) Extension of the {lit}`U_2C_4` basis to a basis of {lit}`P₄(ℝ)`. -/
noncomputable def U_2C_4_extension : Fin sorry → Polynomial.degreeLT ℝ 5 := sorry

/-- 2C.4 (b): appending the extension to the basis of {lit}`U_2C_4` gives a
basis of {lit}`P₄(ℝ)`. -/
theorem exercise_2C_4b :
    IsBasis ℝ (Fin.append (fun i => ((U_2C_4_basis i : Polynomial.degreeLT ℝ 5)))
      U_2C_4_extension) := by
  sorry

/-- (c) Complement of {lit}`U_2C_4` inside {lit}`P₄(ℝ)`. -/
noncomputable def W_2C_4 : Submodule ℝ (Polynomial.degreeLT ℝ 5) := sorry

/-- 2C.4 (c): {lit}`U_2C_4` and {lit}`W_2C_4` are complementary. -/
theorem exercise_2C_4c : IsCompl U_2C_4 W_2C_4 := by
  sorry

/-! 2C.5 -/

def U_2C_5 (F : Type*) [Field F] : Submodule F (Polynomial.degreeLT F 5) where
  carrier := {p | (p.val.eval 2 : F) = p.val.eval 5}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    show (p.val + q.val).eval 2 = (p.val + q.val).eval 5
    rw [Polynomial.eval_add, Polynomial.eval_add, hp, hq]
  smul_mem' := by
    intro a p hp
    show (a • p.val).eval 2 = (a • p.val).eval 5
    rw [Polynomial.eval_smul, Polynomial.eval_smul, hp]

/-- (a) A basis of {lit}`U_2C_5`. -/
noncomputable def U_2C_5_basis (F : Type*) [Field F] : Fin sorry → U_2C_5 F := sorry

/-- 2C.5 (a): the chosen list is a basis of {lit}`U_2C_5`. -/
theorem exercise_2C_5a [CharZero F] : IsBasis F (U_2C_5_basis F) := by
  sorry

/-- (b) Extension of the {lit}`U_2C_5` basis to a basis of {lit}`P₄(F)`. -/
noncomputable def U_2C_5_extension (F : Type*) [Field F] :
    Fin sorry → Polynomial.degreeLT F 5 := sorry

/-- 2C.5 (b): appending the extension to the basis of {lit}`U_2C_5` gives a
basis of {lit}`P₄(F)`. -/
theorem exercise_2C_5b :
    IsBasis F (Fin.append (fun i => ((U_2C_5_basis F i : Polynomial.degreeLT F 5)))
      (U_2C_5_extension F)) := by
  sorry

/-- (c) Complement of {lit}`U_2C_5` inside {lit}`P₄(F)`. -/
noncomputable def W_2C_5 (F : Type*) [Field F] :
    Submodule F (Polynomial.degreeLT F 5) := sorry

/-- 2C.5 (c): {lit}`U_2C_5` and {lit}`W_2C_5` are complementary. -/
theorem exercise_2C_5c [CharZero F] : IsCompl (U_2C_5 F) (W_2C_5 F) := by
  sorry

/-! 2C.6 -/

/-- {lit}`{p ∈ P₄(F) : p(2) = p(5) = p(6)}`. -/
def U_2C_6 (F : Type*) [Field F] : Submodule F (Polynomial.degreeLT F 5) where
  carrier := {p | (p.val.eval 2 : F) = p.val.eval 5 ∧ p.val.eval 5 = p.val.eval 6}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    refine ⟨?_, ?_⟩
    · show (p.val + q.val).eval 2 = (p.val + q.val).eval 5
      rw [Polynomial.eval_add, Polynomial.eval_add, hp.1, hq.1]
    · show (p.val + q.val).eval 5 = (p.val + q.val).eval 6
      rw [Polynomial.eval_add, Polynomial.eval_add, hp.2, hq.2]
  smul_mem' := by
    intro a p hp
    refine ⟨?_, ?_⟩
    · show (a • p.val).eval 2 = (a • p.val).eval 5
      rw [Polynomial.eval_smul, Polynomial.eval_smul, hp.1]
    · show (a • p.val).eval 5 = (a • p.val).eval 6
      rw [Polynomial.eval_smul, Polynomial.eval_smul, hp.2]

/-- (a) A basis of {lit}`U_2C_6`. -/
noncomputable def U_2C_6_basis (F : Type*) [Field F] : Fin sorry → U_2C_6 F := sorry

/-- 2C.6 (a): the chosen list is a basis of {lit}`U_2C_6`. -/
theorem exercise_2C_6a [CharZero F] : IsBasis F (U_2C_6_basis F) := by
  sorry

/-- (b) Extension of the {lit}`U_2C_6` basis to a basis of {lit}`P₄(F)`. -/
noncomputable def U_2C_6_extension (F : Type*) [Field F] :
    Fin sorry → Polynomial.degreeLT F 5 := sorry

/-- 2C.6 (b): appending the extension to the basis of {lit}`U_2C_6` gives a
basis of {lit}`P₄(F)`. -/
theorem exercise_2C_6b [CharZero F] :
    IsBasis F (Fin.append (fun i => ((U_2C_6_basis F i : Polynomial.degreeLT F 5)))
      (U_2C_6_extension F)) := by
  sorry

/-- (c) Complement of {lit}`U_2C_6` inside {lit}`P₄(F)`. -/
noncomputable def W_2C_6 (F : Type*) [Field F] :
    Submodule F (Polynomial.degreeLT F 5) := sorry

/-- 2C.6 (c): {lit}`U_2C_6` and {lit}`W_2C_6` are complementary. -/
theorem exercise_2C_6c [CharZero F] : IsCompl (U_2C_6 F) (W_2C_6 F) := by
  sorry

/-! 2C.7 Let {lit}`U = {p ∈ P₄(ℝ) : ∫₋₁¹ p = 0}`. We encode the integral
algebraically: for {lit}`p = ∑ cᵢ Xⁱ` of degree {lit}`< 5`,
{lit}`∫₋₁¹ p = ∑ᵢ cᵢ · (1 - (-1)^(i+1))/(i+1) = 2 c₀ + (2/3) c₂ + (2/5) c₄`.
Vanishing of this linear form on coefficients is what we use. -/

/-- {lit}`{p ∈ P₄(ℝ) : ∫₋₁¹ p = 0}`, encoded via the closed-form integral
{lit}`2 c₀ + (2/3) c₂ + (2/5) c₄ = 0` on coefficients. -/
noncomputable def U_2C_7 : Submodule ℝ (Polynomial.degreeLT ℝ 5) where
  carrier := {p | (2 * p.val.coeff 0 + (2 / 3) * p.val.coeff 2
                   + (2 / 5) * p.val.coeff 4 : ℝ) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    show 2 * (p.val + q.val).coeff 0 + (2 / 3) * (p.val + q.val).coeff 2
         + (2 / 5) * (p.val + q.val).coeff 4 = 0
    simp only [Polynomial.coeff_add]
    have hp' : 2 * p.val.coeff 0 + (2 / 3) * p.val.coeff 2
               + (2 / 5) * p.val.coeff 4 = 0 := hp
    have hq' : 2 * q.val.coeff 0 + (2 / 3) * q.val.coeff 2
               + (2 / 5) * q.val.coeff 4 = 0 := hq
    linarith
  smul_mem' := by
    intro a p hp
    show 2 * (a • p.val).coeff 0 + (2 / 3) * (a • p.val).coeff 2
         + (2 / 5) * (a • p.val).coeff 4 = 0
    simp only [Polynomial.coeff_smul, smul_eq_mul]
    have hp' : 2 * p.val.coeff 0 + (2 / 3) * p.val.coeff 2
               + (2 / 5) * p.val.coeff 4 = 0 := hp
    linear_combination a * hp'

/-- (a) A basis of {lit}`U_2C_7`. -/
noncomputable def U_2C_7_basis : Fin sorry → U_2C_7 := sorry

/-- 2C.7 (a): the chosen list is a basis of {lit}`U_2C_7`. -/
theorem exercise_2C_7a : IsBasis ℝ U_2C_7_basis := by
  sorry

/-- (b) Extension of the {lit}`U_2C_7` basis to a basis of {lit}`P₄(ℝ)`. -/
noncomputable def U_2C_7_extension : Fin sorry → Polynomial.degreeLT ℝ 5 := sorry

/-- 2C.7 (b): appending the extension to the basis of {lit}`U_2C_7` gives a
basis of {lit}`P₄(ℝ)`. -/
theorem exercise_2C_7b :
    IsBasis ℝ (Fin.append (fun i => ((U_2C_7_basis i : Polynomial.degreeLT ℝ 5)))
      U_2C_7_extension) := by
  sorry

/-- (c) Complement of {lit}`U_2C_7` inside {lit}`P₄(ℝ)`. -/
noncomputable def W_2C_7 : Submodule ℝ (Polynomial.degreeLT ℝ 5) := sorry

/-- 2C.7 (c): {lit}`U_2C_7` and {lit}`W_2C_7` are complementary. -/
theorem exercise_2C_7c : IsCompl U_2C_7 W_2C_7 := by
  sorry

/-- 2C.8 -/
theorem exercise_2C_8 {m : ℕ} (v : Fin m → V) (hv : LinearIndependent F v)
    (w : V) :
    m - 1 ≤ finrank F
      (Submodule.span F (Set.range (fun i : Fin m => v i + w))) := by
  sorry

/-- 2C.9 -/
theorem exercise_2C_9 [Infinite F] (m : ℕ) (hm : 1 ≤ m)
    (p : Fin (m + 1) → Polynomial.degreeLT F (m + 1))
    (hp : ∀ k : Fin (m + 1), (p k : Polynomial F).degree = (k : ℕ)) :
    IsBasis F p := by
  sorry

/-- {lit}`X^a (1 - X)^b` lies in {lit}`degreeLT F (a + b + 1)`: its
{lit}`natDegree` is at most {lit}`a + b`. -/
private lemma X_pow_one_sub_X_pow_mem_degreeLT (a b : ℕ) :
    (Polynomial.X ^ a * (1 - Polynomial.X) ^ b : Polynomial F)
      ∈ Polynomial.degreeLT F (a + b + 1) := by
  rw [Polynomial.mem_degreeLT]
  calc (Polynomial.X ^ a * (1 - Polynomial.X) ^ b : Polynomial F).degree
      ≤ (Polynomial.X ^ a : Polynomial F).degree
          + ((1 - Polynomial.X) ^ b : Polynomial F).degree :=
        Polynomial.degree_mul_le _ _
    _ ≤ (a : WithBot ℕ) + b := by
        gcongr
        · simp only [Polynomial.degree_X_pow_le (R := F) a]
        · have hdeg : (1 - Polynomial.X : Polynomial F).degree ≤ 1 := by
            calc (1 - Polynomial.X : Polynomial F).degree
                ≤ max (1 : Polynomial F).degree (-Polynomial.X : Polynomial F).degree := by
                  rw [sub_eq_add_neg]; exact Polynomial.degree_add_le _ _
              _ ≤ 1 := by simp [Polynomial.degree_one, Polynomial.degree_neg,
                  Polynomial.degree_X]
          calc ((1 - Polynomial.X) ^ b : Polynomial F).degree
              ≤ b • (1 - Polynomial.X : Polynomial F).degree :=
                Polynomial.degree_pow_le _ _
            _ ≤ b • (1 : WithBot ℕ) := by gcongr
            _ = b := by simp
    _ < (a + b + 1 : ℕ) := by push_cast; exact_mod_cast Nat.lt_succ_self _

/-- 2C.10 -/
theorem exercise_2C_10 [Infinite F] (m : ℕ) (hm : 1 ≤ m) :
    IsBasis F (fun k : Fin (m + 1) =>
      (⟨Polynomial.X ^ (k : ℕ) * (1 - Polynomial.X) ^ (m - (k : ℕ)), by
        have hk : (k : ℕ) + (m - (k : ℕ)) = m := by have := k.isLt; omega
        have := X_pow_one_sub_X_pow_mem_degreeLT (F := F) (k : ℕ) (m - (k : ℕ))
        rwa [hk] at this⟩ : Polynomial.degreeLT F (m + 1))) := by
  sorry

/-- 2C.11 -/
theorem exercise_2C_11 (U W : Submodule ℂ (Fin 6 → ℂ))
    (hU : finrank ℂ U = 4) (hW : finrank ℂ W = 4) :
    ∃ x y : (U ⊓ W : Submodule ℂ (Fin 6 → ℂ)),
      (∀ a : ℂ, x ≠ a • y) ∧ (∀ b : ℂ, y ≠ b • x) := by
  sorry

/-- 2C.12 -/
theorem exercise_2C_12 (U W : Submodule ℝ (Fin 8 → ℝ))
    (hU : finrank ℝ U = 3) (hW : finrank ℝ W = 5)
    (hUW : U ⊔ W = ⊤) : IsCompl U W := by
  sorry

/-- 2C.13 -/
theorem exercise_2C_13 (U W : Submodule ℝ (Fin 9 → ℝ))
    (hU : finrank ℝ U = 5) (hW : finrank ℝ W = 5) :
    U ⊓ W ≠ ⊥ := by
  sorry

/-- 2C.14 -/
theorem exercise_2C_14 [Finite F V] (hV : finrank F V = 10)
    (V₁ V₂ V₃ : Submodule F V)
    (hV₁ : finrank F V₁ = 7) (hV₂ : finrank F V₂ = 7)
    (hV₃ : finrank F V₃ = 7) :
    V₁ ⊓ V₂ ⊓ V₃ ≠ ⊥ := by
  sorry

/-- 2C.15 -/
theorem exercise_2C_15 [Finite F V] (V₁ V₂ V₃ : Submodule F V)
    (hsum : finrank F V₁ + finrank F V₂ + finrank F V₃ >
      2 * finrank F V) :
    V₁ ⊓ V₂ ⊓ V₃ ≠ ⊥ := by
  sorry

/-- 2C.16 -/
theorem exercise_2C_16 [Finite F V] (U : Submodule F V) (hU : U ≠ ⊤) :
    ∃ (W : Fin (finrank F V - finrank F U) → Submodule F V),
      (∀ i, finrank F (W i) = finrank F V - 1) ∧
      ⨅ i, W i = U := by
  sorry

/-- 2C.17 -/
theorem exercise_2C_17 {m : ℕ} (W : Fin m → Submodule F V)
    (hW : ∀ i, Finite F (W i)) :
    Finite F ↥(⨆ i, W i) ∧
      finrank F ↥(⨆ i, W i) ≤ ∑ i, finrank F (W i) := by
  sorry

/-- 2C.18 -/
theorem exercise_2C_18 [Finite F V] (hV : 1 ≤ finrank F V) :
    ∃ (W : Fin (finrank F V) → Submodule F V),
      (∀ i, finrank F (W i) = 1) ∧ IsDirectSum W ∧ ⨆ i, W i = ⊤ := by
  sorry

universe u in
/-- 2C.19 — the space is quantified (with the section's fixed {lit}`V` the claim
would hold vacuously whenever {lit}`V` is trivial), and the field shares its
universe so that a counterexample in {lit}`K²` can instantiate it. -/
def exercise_2C_19 {K : Type u} [Field K] :
    Decidable (∀ (W : Type u) [AddCommGroup W] [Module K W] [Finite K W]
      (V₁ V₂ V₃ : Submodule K W),
      finrank K ↥(V₁ ⊔ V₂ ⊔ V₃) =
        finrank K V₁ + finrank K V₂ + finrank K V₃ -
        finrank K ↥(V₁ ⊓ V₂) - finrank K ↥(V₁ ⊓ V₃) - finrank K ↥(V₂ ⊓ V₃) +
        finrank K ↥(V₁ ⊓ V₂ ⊓ V₃)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 2C.20 The {lit}`/3` makes this a rational identity in general; we encode it by
clearing the denominator, i.e. multiplying both sides by 3 so we can stay in ℕ. -/
theorem exercise_2C_20 :
    ∀ (V₁ V₂ V₃ : Submodule F V) [Finite F V],
      3 * finrank F ↥(V₁ ⊔ V₂ ⊔ V₃) =
      3 * (finrank F V₁ + finrank F V₂ + finrank F V₃)
        - (finrank F ↥(V₁ ⊓ V₂) + finrank F ↥(V₁ ⊓ V₃) + finrank F ↥(V₂ ⊓ V₃))
        - (finrank F ↥((V₁ ⊔ V₂) ⊓ V₃) + finrank F ↥((V₁ ⊔ V₃) ⊓ V₂)
          + finrank F ↥((V₂ ⊔ V₃) ⊓ V₁)) := by
  sorry

end LADR.Section_2C
