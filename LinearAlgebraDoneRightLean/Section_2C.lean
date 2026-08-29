import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Basis
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
  -- by cases on {lit}`dim U ∈ {0, 1, 2}`
  have hdim : finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  have hle : finrank ℝ U ≤ 2 := by
    have := finrank_submodule_le (F := ℝ) (V := Fin 2 → ℝ) U
    rwa [hdim] at this
  have hcases : finrank ℝ U = 0 ∨ finrank ℝ U = 1 ∨ finrank ℝ U = 2 := by omega
  rcases hcases with h | h | h
  · exact Or.inl (Submodule.finrank_eq_zero.mp h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (subspace_eq_top_of_finrank_eq U (by rw [h, hdim])))

/-- 2C.2 (we replace lines containing 0 with subspaces of rank 1, and
planes through the origin with subspaces of rank 2) -/
theorem exercise_2C_2 (U : Submodule ℝ (Fin 3 → ℝ)) :
    U = ⊥ ∨ finrank ℝ U = 1 ∨ finrank ℝ U = 2 ∨ U = ⊤ := by
  -- by cases on {lit}`dim U ∈ {0, 1, 2, 3}`
  have hdim : finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  have hle : finrank ℝ U ≤ 3 := by
    have := finrank_submodule_le (F := ℝ) (V := Fin 3 → ℝ) U
    rwa [hdim] at this
  have hcases : finrank ℝ U = 0 ∨ finrank ℝ U = 1 ∨ finrank ℝ U = 2
      ∨ finrank ℝ U = 3 := by omega
  rcases hcases with h | h | h | h
  · exact Or.inl (Submodule.finrank_eq_zero.mp h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr
      (subspace_eq_top_of_finrank_eq U (by rw [h, hdim]))))

/-! Shifted-power toolkit, used by the {lit}`P₄(F)` exercises below. -/

/-- {lit}`(X - c)^k` has degree {lit}`k`, hence lies in {lit}`degreeLT F 5`
when {lit}`k < 5`. -/
private lemma xSubC_pow_mem_degreeLT (c : F) (k : ℕ) (hk : k < 5) :
    (Polynomial.X - Polynomial.C c) ^ k ∈ Polynomial.degreeLT F 5 := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_pow, Polynomial.degree_X_sub_C]
  simp only [nsmul_eq_mul, mul_one, Nat.cast_lt]
  exact_mod_cast hk

/-- {lit}`(X - c)^k` vanishes at {lit}`c` whenever {lit}`k ≥ 1`. -/
private lemma xSubC_pow_eval (c : F) (k : ℕ) (hk : 1 ≤ k) :
    ((Polynomial.X - Polynomial.C c) ^ k).eval c = 0 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp

/-- The second derivative of {lit}`(X - c)^k` vanishes at {lit}`c` unless
{lit}`k = 2`. -/
private lemma xSubC_pow_deriv2_eval (c : F) (k : ℕ) (hk : k ≠ 2) :
    (((Polynomial.X - Polynomial.C c) ^ k).derivative.derivative).eval c = 0 := by
  rcases k with _ | _ | _ | k
  · simp
  · simp
  · exact absurd rfl hk
  · rw [Polynomial.derivative_X_sub_C_pow, Polynomial.derivative_C_mul,
      Polynomial.derivative_X_sub_C_pow]
    simp

/-- Powers {lit}`(X - c)^(e i)` with pairwise distinct exponents are linearly
independent: the substitution {lit}`X ↦ X + c` turns them into distinct
monomials. -/
private lemma linearIndependent_xSubC_pow (c : F) {n : ℕ} (e : Fin n → ℕ)
    (he : Function.Injective e) :
    LinearIndependent F (fun i => (Polynomial.X - Polynomial.C c) ^ e i) := by
  have hmon : LinearIndependent F (fun i => (Polynomial.X : Polynomial F) ^ e i) := by
    have := (Polynomial.basisMonomials F).linearIndependent.comp e he
    simpa [Function.comp_def, Polynomial.X_pow_eq_monomial] using this
  apply LinearIndependent.of_comp
    (Polynomial.aeval (R := F) (Polynomial.X + Polynomial.C c)).toLinearMap
  have hcomp :
      ((Polynomial.aeval (R := F) (Polynomial.X + Polynomial.C c)).toLinearMap ∘
        fun i => (Polynomial.X - Polynomial.C c) ^ e i)
        = fun i => (Polynomial.X : Polynomial F) ^ e i := by
    funext i
    simp
  rw [hcomp]
  exact hmon

/-- A list of nonzero polynomials with pairwise distinct degrees is linearly
independent: in a vanishing combination, look at the coefficient of the largest
degree that actually occurs. -/
private lemma linearIndependent_of_natDegree_injective {n : ℕ}
    (v : Fin n → Polynomial F) (hv : ∀ i, v i ≠ 0)
    (hdeg : Function.Injective fun i => (v i).natDegree) :
    LinearIndependent F v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  by_contra hi
  obtain ⟨j, hjmem, hjmax⟩ :=
    Finset.exists_max_image (Finset.univ.filter fun k => a k ≠ 0)
      (fun k => (v k).natDegree) ⟨i, by simp [hi]⟩
  have hja : a j ≠ 0 := by simpa using hjmem
  have hcoeff := congrArg (fun p => Polynomial.coeff p (v j).natDegree) ha
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_zero] at hcoeff
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ≠ j →
      a k * (v k).coeff ((v j).natDegree) = 0 := by
    intro k _ hkj
    rcases eq_or_ne (a k) 0 with hk | hk
    · rw [hk, zero_mul]
    · have hle : (v k).natDegree ≤ (v j).natDegree := hjmax k (by simp [hk])
      have hne : (v k).natDegree ≠ (v j).natDegree := fun h => hkj (hdeg h)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hle hne), mul_zero]
  rw [Finset.sum_eq_single j hterm (fun h => absurd (Finset.mem_univ j) h),
    Polynomial.coeff_natDegree] at hcoeff
  exact mul_ne_zero hja (Polynomial.leadingCoeff_ne_zero.mpr (hv j)) hcoeff

/-- Dual form of {name}`linearIndependent_of_natDegree_injective`: nonzero
polynomials with pairwise distinct *trailing* degrees are linearly independent —
look at the coefficient of the smallest trailing degree that occurs. -/
private lemma linearIndependent_of_natTrailingDegree_injective {n : ℕ}
    (v : Fin n → Polynomial F) (hv : ∀ i, v i ≠ 0)
    (hdeg : Function.Injective fun i => (v i).natTrailingDegree) :
    LinearIndependent F v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  by_contra hi
  obtain ⟨j, hjmem, hjmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter fun k => a k ≠ 0)
      (fun k => (v k).natTrailingDegree) ⟨i, by simp [hi]⟩
  have hja : a j ≠ 0 := by simpa using hjmem
  have hcoeff := congrArg (fun p => Polynomial.coeff p (v j).natTrailingDegree) ha
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_zero] at hcoeff
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ≠ j →
      a k * (v k).coeff ((v j).natTrailingDegree) = 0 := by
    intro k _ hkj
    rcases eq_or_ne (a k) 0 with hk | hk
    · rw [hk, zero_mul]
    · have hle : (v j).natTrailingDegree ≤ (v k).natTrailingDegree :=
        hjmin k (by simp [hk])
      have hne : (v k).natTrailingDegree ≠ (v j).natTrailingDegree := fun h => hkj (hdeg h)
      rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
        (lt_of_le_of_ne hle (Ne.symm hne)), mul_zero]
  rw [Finset.sum_eq_single j hterm (fun h => absurd (Finset.mem_univ j) h)] at hcoeff
  have hj0 : (v j).coeff ((v j).natTrailingDegree) ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (hv j)
  exact mul_ne_zero hja hj0 hcoeff

/-- {lit}`P₄(F)` is finite-dimensional. -/
instance instFiniteDegreeLT5 : Finite F (Polynomial.degreeLT F 5) :=
  Module.Finite.equiv (Polynomial.degreeLTEquiv F 5).symm

private lemma finrank_degreeLT5 : finrank F (Polynomial.degreeLT F 5) = 5 := by
  simp only [(Polynomial.degreeLTEquiv F 5).finrank_eq,
    Module.finrank_pi, Fintype.card_fin]

/-- The constant polynomial {lit}`1`, viewed inside {lit}`P₄(F)`. -/
noncomputable def one_degreeLT5 (F : Type*) [Field F] : Polynomial.degreeLT F 5 :=
  ⟨1, by rw [Polynomial.mem_degreeLT]; simp⟩

/-- {lit}`x`, viewed inside {lit}`P₄(F)`. -/
noncomputable def x_degreeLT5 (F : Type*) [Field F] : Polynomial.degreeLT F 5 :=
  ⟨Polynomial.X, by rw [Polynomial.mem_degreeLT, Polynomial.degree_X]; decide⟩

/-- {lit}`x²`, viewed inside {lit}`P₄(F)`. -/
noncomputable def xSq_degreeLT5 (F : Type*) [Field F] : Polynomial.degreeLT F 5 :=
  ⟨Polynomial.X ^ 2, by rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]; decide⟩

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
-- (x - 6) ^ i for i = 1, 2, 3, 4 is a basis of U_2C_3.
noncomputable def U_2C_3_basis (F : Type*) [Field F] : Fin 4 → U_2C_3 F :=
  fun i => ⟨⟨(Polynomial.X - Polynomial.C (6 : F)) ^ ((i : ℕ) + 1),
      xSubC_pow_mem_degreeLT 6 _ (by have := i.isLt; omega)⟩,
    xSubC_pow_eval 6 _ (by omega)⟩

/-- The linear map {lit}`U_2C_3 F → F[X]`. -/
private noncomputable def U_2C_3_toPoly (F : Type*) [Field F] :
    U_2C_3 F →ₗ[F] Polynomial F :=
  (Polynomial.degreeLT F 5).subtype ∘ₗ (U_2C_3 F).subtype

private theorem linearIndependent_U_2C_3_basis :
    LinearIndependent F (U_2C_3_basis F) := by
  apply LinearIndependent.of_comp (U_2C_3_toPoly F)
  have hcomp : (U_2C_3_toPoly F) ∘ (U_2C_3_basis F)
      = fun i : Fin 4 => (Polynomial.X - Polynomial.C (6 : F)) ^ ((i : ℕ) + 1) := rfl
  rw [hcomp]
  exact linearIndependent_xSubC_pow 6 (fun i : Fin 4 => (i : ℕ) + 1)
    (fun a b h => by
      have h' : (a : ℕ) + 1 = (b : ℕ) + 1 := h
      exact Fin.ext (by omega))

instance : Finite F (U_2C_3 F) :=
  Module.Finite.of_injective (U_2C_3 F).subtype Subtype.val_injective

/-- {lit}`1 ∉ U_2C_3 F`, so {lit}`U_2C_3 F` is a proper subspace. -/
private lemma one_not_mem_U_2C_3 : one_degreeLT5 F ∉ U_2C_3 F := by
  intro h
  have h1 : (1 : Polynomial F).eval 6 = 0 := h
  simp at h1

private theorem finrank_U_2C_3 : finrank F (U_2C_3 F) = 4 := by
  -- Lower bound: the four listed vectors are linearly independent.
  have hge : 4 ≤ finrank F (U_2C_3 F) := by
    have := (linearIndependent_U_2C_3_basis (F := F)).fintype_card_le_finrank
    simpa using this
  -- Upper bound: {lit}`dim ≤ 5`, and {lit}`= 5` would force {lit}`U = P₄(F)`,
  -- contradicted by {lit}`1 ∉ U`.
  have hle : finrank F (U_2C_3 F) ≤ 5 := by
    have := finrank_submodule_le (U_2C_3 F)
    rwa [finrank_degreeLT5] at this
  have hne_top : U_2C_3 F ≠ ⊤ := fun h =>
    one_not_mem_U_2C_3 (F := F) (by rw [h]; trivial)
  have hne_5 : finrank F (U_2C_3 F) ≠ 5 := fun heq =>
    hne_top (subspace_eq_top_of_finrank_eq _ (by rw [heq, finrank_degreeLT5]))
  omega

theorem exercise_2C_3a : IsBasis F (U_2C_3_basis F) := by
  -- show lin ind by degree
  exact isBasis_of_linearIndependent_of_card_eq _ linearIndependent_U_2C_3_basis
    finrank_U_2C_3.symm

/-- (b) Extension of the {lit}`U_2C_3` basis to a basis of {lit}`P₄(F)`. -/
-- add 1
noncomputable def U_2C_3_extension (F : Type*) [Field F] :
    Fin 1 → Polynomial.degreeLT F 5 := fun _ => one_degreeLT5 F

/-- The exponents appearing in the extended list {lit}`(x-6), …, (x-6)⁴, 1`. -/
private def U_2C_3_full_exponents : Fin (4 + 1) → ℕ := ![1, 2, 3, 4, 0]

private lemma U_2C_3_append_coe (j : Fin (4 + 1)) :
    ((Fin.append (fun i => ((U_2C_3_basis F i : Polynomial.degreeLT F 5)))
        (U_2C_3_extension F) j : Polynomial.degreeLT F 5) : Polynomial F)
      = (Polynomial.X - Polynomial.C (6 : F)) ^ U_2C_3_full_exponents j := by
  fin_cases j <;>
    simp [U_2C_3_full_exponents, U_2C_3_basis, U_2C_3_extension, one_degreeLT5,
      Fin.append, Fin.addCases]

theorem exercise_2C_3b :
    IsBasis F (Fin.append (fun i => ((U_2C_3_basis F i : Polynomial.degreeLT F 5)))
      (U_2C_3_extension F)) := by
  refine isBasis_of_linearIndependent_of_card_eq _ ?_ (by rw [finrank_degreeLT5])
  apply LinearIndependent.of_comp (Polynomial.degreeLT F 5).subtype
  have hcomp : ((Polynomial.degreeLT F 5).subtype ∘
      Fin.append (fun i => ((U_2C_3_basis F i : Polynomial.degreeLT F 5)))
        (U_2C_3_extension F))
      = fun j => (Polynomial.X - Polynomial.C (6 : F)) ^ U_2C_3_full_exponents j := by
    funext j; exact U_2C_3_append_coe j
  rw [hcomp]
  exact linearIndependent_xSubC_pow 6 U_2C_3_full_exponents (by decide)

-- the subspace of constant polynomials is a complement of U_2C_3
noncomputable def W_2C_3 (F : Type*) [Field F] :
    Submodule F (Polynomial.degreeLT F 5) :=
  Submodule.span F {one_degreeLT5 F}

theorem exercise_2C_3c : IsCompl (U_2C_3 F) (W_2C_3 F) := by
  constructor
  · -- a constant vanishing at {lit}`6` is {lit}`0`
    rw [Submodule.disjoint_def]
    intro x hxU hxW
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxW
    have hxval : (x : Polynomial F) = a • (1 : Polynomial F) := by rw [← ha]; rfl
    have hx6 : ((x : Polynomial F)).eval 6 = 0 := hxU
    rw [hxval] at hx6
    simp only [Polynomial.eval_smul, Polynomial.eval_one, smul_eq_mul,
      mul_one] at hx6
    exact Subtype.ext (by simp [hxval, hx6])
  · -- {lit}`p = (p - p(6)) + p(6)` splits any {lit}`p ∈ P₄(F)`
    rw [codisjoint_iff, eq_top_iff]
    intro p _
    have hmemU : p - ((p : Polynomial F).eval 6) • one_degreeLT5 F ∈ U_2C_3 F := by
      show ((p : Polynomial F)
        - ((p : Polynomial F).eval 6) • (1 : Polynomial F)).eval 6 = 0
      simp
    have hmemW : ((p : Polynomial F).eval 6) • one_degreeLT5 F ∈ W_2C_3 F :=
      Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
    have hsum := Submodule.add_mem_sup hmemU hmemW
    have heq : (p - ((p : Polynomial F).eval 6) • one_degreeLT5 F)
        + ((p : Polynomial F).eval 6) • one_degreeLT5 F = p := by abel
    rwa [heq] at hsum

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

/-- {lit}`(x-6)²`, viewed inside {lit}`P₄(ℝ)`. -/
noncomputable def xSub6_sq_2C_4 : Polynomial.degreeLT ℝ 5 :=
  ⟨(Polynomial.X - Polynomial.C (6 : ℝ)) ^ 2, xSubC_pow_mem_degreeLT 6 2 (by norm_num)⟩

private lemma xSub6_sq_deriv2_eval :
    (((Polynomial.X - Polynomial.C (6 : ℝ)) ^ 2).derivative.derivative).eval 6 = 2 := by
  rw [Polynomial.derivative_X_sub_C_pow, Polynomial.derivative_C_mul,
    Polynomial.derivative_X_sub_C_pow]
  simp

/-- (a) A basis of {lit}`U_2C_4`. -/
-- 1, x - 6, (x - 6) ^ 3, (x - 6) ^ 4: the second derivative of {lit}`(x-6)^k`
-- vanishes at 6 except for k = 2.
private def U_2C_4_exponents : Fin 4 → ℕ := ![0, 1, 3, 4]

private lemma U_2C_4_exponents_lt (i : Fin 4) : U_2C_4_exponents i < 5 := by
  fin_cases i <;> decide

private lemma U_2C_4_exponents_ne_two (i : Fin 4) : U_2C_4_exponents i ≠ 2 := by
  fin_cases i <;> decide

noncomputable def U_2C_4_basis : Fin 4 → U_2C_4 :=
  fun i => ⟨⟨(Polynomial.X - Polynomial.C (6 : ℝ)) ^ U_2C_4_exponents i,
      xSubC_pow_mem_degreeLT 6 _ (U_2C_4_exponents_lt i)⟩,
    xSubC_pow_deriv2_eval 6 _ (U_2C_4_exponents_ne_two i)⟩

/-- The linear map {lit}`U_2C_4 → ℝ[X]`. -/
private noncomputable def U_2C_4_toPoly : U_2C_4 →ₗ[ℝ] Polynomial ℝ :=
  (Polynomial.degreeLT ℝ 5).subtype ∘ₗ U_2C_4.subtype

private theorem linearIndependent_U_2C_4_basis :
    LinearIndependent ℝ U_2C_4_basis := by
  apply LinearIndependent.of_comp U_2C_4_toPoly
  have hcomp : U_2C_4_toPoly ∘ U_2C_4_basis
      = fun i => (Polynomial.X - Polynomial.C (6 : ℝ)) ^ U_2C_4_exponents i := rfl
  rw [hcomp]
  exact linearIndependent_xSubC_pow 6 U_2C_4_exponents (by decide)

instance : Finite ℝ U_2C_4 :=
  Module.Finite.of_injective U_2C_4.subtype Subtype.val_injective

/-- {lit}`(x-6)² ∉ U_2C_4`, so {lit}`U_2C_4` is a proper subspace. -/
private lemma xSub6_sq_not_mem_U_2C_4 : xSub6_sq_2C_4 ∉ U_2C_4 := by
  intro h
  have h2 : (((Polynomial.X - Polynomial.C (6 : ℝ)) ^ 2).derivative.derivative).eval 6
      = 0 := h
  rw [xSub6_sq_deriv2_eval] at h2
  norm_num at h2

private theorem finrank_U_2C_4 : finrank ℝ U_2C_4 = 4 := by
  -- Lower bound: the four listed vectors are linearly independent.
  have hge : 4 ≤ finrank ℝ U_2C_4 := by
    have := linearIndependent_U_2C_4_basis.fintype_card_le_finrank
    simpa using this
  -- Upper bound: {lit}`dim ≤ 5`, and {lit}`= 5` would force {lit}`U = P₄(ℝ)`,
  -- contradicted by {lit}`(x-6)² ∉ U`.
  have hle : finrank ℝ U_2C_4 ≤ 5 := by
    have := finrank_submodule_le U_2C_4
    rwa [finrank_degreeLT5] at this
  have hne_top : U_2C_4 ≠ ⊤ := fun h =>
    xSub6_sq_not_mem_U_2C_4 (by rw [h]; trivial)
  have hne_5 : finrank ℝ U_2C_4 ≠ 5 := fun heq =>
    hne_top (subspace_eq_top_of_finrank_eq _ (by rw [heq, finrank_degreeLT5]))
  omega

/-- 2C.4 (a): the chosen list is a basis of {lit}`U_2C_4`. -/
theorem exercise_2C_4a : IsBasis ℝ U_2C_4_basis :=
  isBasis_of_linearIndependent_of_card_eq _ linearIndependent_U_2C_4_basis
    finrank_U_2C_4.symm

/-- (b) Extension of the {lit}`U_2C_4` basis to a basis of {lit}`P₄(ℝ)`. -/
-- add (x - 6) ^ 2
noncomputable def U_2C_4_extension : Fin 1 → Polynomial.degreeLT ℝ 5 :=
  fun _ => xSub6_sq_2C_4

/-- The exponents of the extended list {lit}`1, x-6, (x-6)³, (x-6)⁴, (x-6)²`. -/
private def U_2C_4_full_exponents : Fin (4 + 1) → ℕ := ![0, 1, 3, 4, 2]

private lemma U_2C_4_append_coe (j : Fin (4 + 1)) :
    ((Fin.append (fun i => ((U_2C_4_basis i : Polynomial.degreeLT ℝ 5)))
        U_2C_4_extension j : Polynomial.degreeLT ℝ 5) : Polynomial ℝ)
      = (Polynomial.X - Polynomial.C (6 : ℝ)) ^ U_2C_4_full_exponents j := by
  fin_cases j <;>
    simp [U_2C_4_full_exponents, U_2C_4_exponents, U_2C_4_basis, U_2C_4_extension,
      xSub6_sq_2C_4, Fin.append, Fin.addCases]

/-- 2C.4 (b): appending the extension to the basis of {lit}`U_2C_4` gives a
basis of {lit}`P₄(ℝ)`. -/
theorem exercise_2C_4b :
    IsBasis ℝ (Fin.append (fun i => ((U_2C_4_basis i : Polynomial.degreeLT ℝ 5)))
      U_2C_4_extension) := by
  refine isBasis_of_linearIndependent_of_card_eq _ ?_ (by rw [finrank_degreeLT5])
  apply LinearIndependent.of_comp (Polynomial.degreeLT ℝ 5).subtype
  have hcomp : ((Polynomial.degreeLT ℝ 5).subtype ∘
      Fin.append (fun i => ((U_2C_4_basis i : Polynomial.degreeLT ℝ 5)))
        U_2C_4_extension)
      = fun j => (Polynomial.X - Polynomial.C (6 : ℝ)) ^ U_2C_4_full_exponents j := by
    funext j; exact U_2C_4_append_coe j
  rw [hcomp]
  exact linearIndependent_xSubC_pow 6 U_2C_4_full_exponents (by decide)

/-- (c) Complement of {lit}`U_2C_4` inside {lit}`P₄(ℝ)`. -/
-- the multiples of (x - 6) ^ 2
noncomputable def W_2C_4 : Submodule ℝ (Polynomial.degreeLT ℝ 5) :=
  Submodule.span ℝ {xSub6_sq_2C_4}

/-- 2C.4 (c): {lit}`U_2C_4` and {lit}`W_2C_4` are complementary. -/
theorem exercise_2C_4c : IsCompl U_2C_4 W_2C_4 := by
  constructor
  · -- a multiple of {lit}`(x-6)²` whose second derivative vanishes at 6 is 0
    rw [Submodule.disjoint_def]
    intro x hxU hxW
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxW
    have hxval : (x : Polynomial ℝ)
        = a • ((Polynomial.X - Polynomial.C (6 : ℝ)) ^ 2) := by rw [← ha]; rfl
    have hx : ((x : Polynomial ℝ)).derivative.derivative.eval 6 = 0 := hxU
    rw [hxval, Polynomial.derivative_smul, Polynomial.derivative_smul,
      Polynomial.eval_smul, xSub6_sq_deriv2_eval, smul_eq_mul] at hx
    have ha0 : a = 0 := by linarith
    exact Subtype.ext (by simp [hxval, ha0])
  · -- {lit}`p = (p - (p''(6)/2)·(x-6)²) + (p''(6)/2)·(x-6)²`
    rw [codisjoint_iff, eq_top_iff]
    intro p _
    have hmemU : p - (((p : Polynomial ℝ).derivative.derivative.eval 6) / 2)
        • xSub6_sq_2C_4 ∈ U_2C_4 := by
      show ((p : Polynomial ℝ) - (((p : Polynomial ℝ).derivative.derivative.eval 6) / 2)
        • ((Polynomial.X - Polynomial.C (6 : ℝ)) ^ 2)).derivative.derivative.eval 6 = 0
      rw [Polynomial.derivative_sub, Polynomial.derivative_sub, Polynomial.eval_sub,
        Polynomial.derivative_smul, Polynomial.derivative_smul, Polynomial.eval_smul,
        xSub6_sq_deriv2_eval, smul_eq_mul]
      ring
    have hmemW : (((p : Polynomial ℝ).derivative.derivative.eval 6) / 2)
        • xSub6_sq_2C_4 ∈ W_2C_4 := Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
    have hsum := Submodule.add_mem_sup hmemU hmemW
    have heq : (p - (((p : Polynomial ℝ).derivative.derivative.eval 6) / 2)
          • xSub6_sq_2C_4)
        + (((p : Polynomial ℝ).derivative.derivative.eval 6) / 2) • xSub6_sq_2C_4
        = p := by abel
    rwa [heq] at hsum

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

/-- {lit}`(x-2)(x-5)`, the polynomial cutting out the condition of 2C.5. -/
private noncomputable def q_2C_5 (F : Type*) [Field F] : Polynomial F :=
  (Polynomial.X - Polynomial.C 2) * (Polynomial.X - Polynomial.C 5)

private lemma q_2C_5_ne_zero : q_2C_5 F ≠ 0 :=
  mul_ne_zero (Polynomial.X_sub_C_ne_zero 2) (Polynomial.X_sub_C_ne_zero 5)

private lemma q_2C_5_natDegree : (q_2C_5 F).natDegree = 2 := by
  rw [q_2C_5, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero 2)
      (Polynomial.X_sub_C_ne_zero 5), Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_X_sub_C]

/-- (a) A basis of {lit}`U_2C_5`. -/
-- 1, x ^ i * (x - 2) * (x - 5) for x = 0, 1, 2
private noncomputable def poly_2C_5 (F : Type*) [Field F] : Fin 4 → Polynomial F :=
  ![1, q_2C_5 F, Polynomial.X * q_2C_5 F, Polynomial.X ^ 2 * q_2C_5 F]

private lemma poly_2C_5_ne_zero (i : Fin 4) : poly_2C_5 F i ≠ 0 := by
  fin_cases i
  · show (1 : Polynomial F) ≠ 0
    exact one_ne_zero
  · exact q_2C_5_ne_zero
  · exact mul_ne_zero Polynomial.X_ne_zero q_2C_5_ne_zero
  · exact mul_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero) q_2C_5_ne_zero

private lemma poly_2C_5_natDegree (i : Fin 4) :
    (poly_2C_5 F i).natDegree = ![0, 2, 3, 4] i := by
  fin_cases i
  · show (1 : Polynomial F).natDegree = 0
    simp
  · exact q_2C_5_natDegree
  · show ((Polynomial.X : Polynomial F) * q_2C_5 F).natDegree = 3
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero q_2C_5_ne_zero,
      Polynomial.natDegree_X, q_2C_5_natDegree]
  · show ((Polynomial.X : Polynomial F) ^ 2 * q_2C_5 F).natDegree = 4
    rw [Polynomial.natDegree_mul (pow_ne_zero 2 Polynomial.X_ne_zero) q_2C_5_ne_zero,
      Polynomial.natDegree_X_pow, q_2C_5_natDegree]

private lemma poly_2C_5_eval (i : Fin 4) :
    (poly_2C_5 F i).eval 2 = (poly_2C_5 F i).eval 5 := by
  fin_cases i
  · show (1 : Polynomial F).eval 2 = (1 : Polynomial F).eval 5
    simp
  · show (q_2C_5 F).eval 2 = (q_2C_5 F).eval 5
    simp [q_2C_5]
  · show ((Polynomial.X : Polynomial F) * q_2C_5 F).eval 2
      = ((Polynomial.X : Polynomial F) * q_2C_5 F).eval 5
    simp [q_2C_5]
  · show ((Polynomial.X : Polynomial F) ^ 2 * q_2C_5 F).eval 2
      = ((Polynomial.X : Polynomial F) ^ 2 * q_2C_5 F).eval 5
    simp [q_2C_5]

private lemma poly_2C_5_mem (i : Fin 4) : poly_2C_5 F i ∈ Polynomial.degreeLT F 5 := by
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.natDegree_lt_iff_degree_lt (poly_2C_5_ne_zero i)).mp ?_
  rw [poly_2C_5_natDegree i]
  fin_cases i <;> decide

noncomputable def U_2C_5_basis (F : Type*) [Field F] : Fin 4 → U_2C_5 F :=
  fun i => ⟨⟨poly_2C_5 F i, poly_2C_5_mem i⟩, poly_2C_5_eval i⟩

/-- The linear map {lit}`U_2C_5 F → F[X]`. -/
private noncomputable def U_2C_5_toPoly (F : Type*) [Field F] :
    U_2C_5 F →ₗ[F] Polynomial F :=
  (Polynomial.degreeLT F 5).subtype ∘ₗ (U_2C_5 F).subtype

private theorem linearIndependent_U_2C_5_basis :
    LinearIndependent F (U_2C_5_basis F) := by
  apply LinearIndependent.of_comp (U_2C_5_toPoly F)
  have hcomp : (U_2C_5_toPoly F) ∘ (U_2C_5_basis F) = poly_2C_5 F := rfl
  rw [hcomp]
  refine linearIndependent_of_natDegree_injective _ poly_2C_5_ne_zero ?_
  have hd : (fun i => (poly_2C_5 F i).natDegree) = ![0, 2, 3, 4] :=
    funext poly_2C_5_natDegree
  rw [hd]
  decide

instance : Finite F (U_2C_5 F) :=
  Module.Finite.of_injective (U_2C_5 F).subtype Subtype.val_injective

/-- {lit}`x ∉ U_2C_5 F`, since {lit}`2 ≠ 5`. -/
private lemma x_not_mem_U_2C_5 [CharZero F] : x_degreeLT5 F ∉ U_2C_5 F := by
  intro h
  have h1 : (Polynomial.X : Polynomial F).eval 2
      = (Polynomial.X : Polynomial F).eval 5 := h
  simp only [Polynomial.eval_X] at h1
  norm_num at h1

private theorem finrank_U_2C_5 [CharZero F] : finrank F (U_2C_5 F) = 4 := by
  -- Lower bound: the four listed vectors are linearly independent.
  have hge : 4 ≤ finrank F (U_2C_5 F) := by
    have := (linearIndependent_U_2C_5_basis (F := F)).fintype_card_le_finrank
    simpa using this
  -- Upper bound: {lit}`dim ≤ 5`, and {lit}`= 5` would force {lit}`U = P₄(F)`,
  -- contradicted by {lit}`x ∉ U`.
  have hle : finrank F (U_2C_5 F) ≤ 5 := by
    have := finrank_submodule_le (U_2C_5 F)
    rwa [finrank_degreeLT5] at this
  have hne_top : U_2C_5 F ≠ ⊤ := fun h =>
    x_not_mem_U_2C_5 (F := F) (by rw [h]; trivial)
  have hne_5 : finrank F (U_2C_5 F) ≠ 5 := fun heq =>
    hne_top (subspace_eq_top_of_finrank_eq _ (by rw [heq, finrank_degreeLT5]))
  omega

/-- 2C.5 (a): the chosen list is a basis of {lit}`U_2C_5`. -/
theorem exercise_2C_5a [CharZero F] : IsBasis F (U_2C_5_basis F) :=
  isBasis_of_linearIndependent_of_card_eq _ linearIndependent_U_2C_5_basis
    finrank_U_2C_5.symm

/-- (b) Extension of the {lit}`U_2C_5` basis to a basis of {lit}`P₄(F)`. -/
-- add x
noncomputable def U_2C_5_extension (F : Type*) [Field F] :
    Fin 1 → Polynomial.degreeLT F 5 := fun _ => x_degreeLT5 F

/-- The underlying polynomials of the extended list. -/
private noncomputable def poly_2C_5_full (F : Type*) [Field F] :
    Fin (4 + 1) → Polynomial F :=
  ![1, q_2C_5 F, Polynomial.X * q_2C_5 F, Polynomial.X ^ 2 * q_2C_5 F, Polynomial.X]

private lemma poly_2C_5_full_ne_zero (j : Fin (4 + 1)) : poly_2C_5_full F j ≠ 0 := by
  fin_cases j
  · show (1 : Polynomial F) ≠ 0
    exact one_ne_zero
  · exact q_2C_5_ne_zero
  · exact mul_ne_zero Polynomial.X_ne_zero q_2C_5_ne_zero
  · exact mul_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero) q_2C_5_ne_zero
  · exact Polynomial.X_ne_zero

private lemma poly_2C_5_full_natDegree (j : Fin (4 + 1)) :
    (poly_2C_5_full F j).natDegree = ![0, 2, 3, 4, 1] j := by
  fin_cases j
  · show (1 : Polynomial F).natDegree = 0
    simp
  · exact q_2C_5_natDegree
  · show ((Polynomial.X : Polynomial F) * q_2C_5 F).natDegree = 3
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero q_2C_5_ne_zero,
      Polynomial.natDegree_X, q_2C_5_natDegree]
  · show ((Polynomial.X : Polynomial F) ^ 2 * q_2C_5 F).natDegree = 4
    rw [Polynomial.natDegree_mul (pow_ne_zero 2 Polynomial.X_ne_zero) q_2C_5_ne_zero,
      Polynomial.natDegree_X_pow, q_2C_5_natDegree]
  · show (Polynomial.X : Polynomial F).natDegree = 1
    simp

private lemma U_2C_5_append_coe (j : Fin (4 + 1)) :
    ((Fin.append (fun i => ((U_2C_5_basis F i : Polynomial.degreeLT F 5)))
        (U_2C_5_extension F) j : Polynomial.degreeLT F 5) : Polynomial F)
      = poly_2C_5_full F j := by
  fin_cases j <;> rfl

/-- 2C.5 (b): appending the extension to the basis of {lit}`U_2C_5` gives a
basis of {lit}`P₄(F)`. -/
theorem exercise_2C_5b :
    IsBasis F (Fin.append (fun i => ((U_2C_5_basis F i : Polynomial.degreeLT F 5)))
      (U_2C_5_extension F)) := by
  refine isBasis_of_linearIndependent_of_card_eq _ ?_ (by rw [finrank_degreeLT5])
  apply LinearIndependent.of_comp (Polynomial.degreeLT F 5).subtype
  have hcomp : ((Polynomial.degreeLT F 5).subtype ∘
      Fin.append (fun i => ((U_2C_5_basis F i : Polynomial.degreeLT F 5)))
        (U_2C_5_extension F)) = poly_2C_5_full F := by
    funext j; exact U_2C_5_append_coe j
  rw [hcomp]
  refine linearIndependent_of_natDegree_injective _ poly_2C_5_full_ne_zero ?_
  have hd : (fun j => (poly_2C_5_full F j).natDegree) = ![0, 2, 3, 4, 1] :=
    funext poly_2C_5_full_natDegree
  rw [hd]
  decide

/-- (c) Complement of {lit}`U_2C_5` inside {lit}`P₄(F)`. -/
-- use {c x}
noncomputable def W_2C_5 (F : Type*) [Field F] :
    Submodule F (Polynomial.degreeLT F 5) :=
  Submodule.span F {x_degreeLT5 F}

/-- 2C.5 (c): {lit}`U_2C_5` and {lit}`W_2C_5` are complementary. -/
theorem exercise_2C_5c [CharZero F] : IsCompl (U_2C_5 F) (W_2C_5 F) := by
  have h3 : (3 : F) ≠ 0 := by norm_num
  constructor
  · -- {lit}`a·x` takes the same value at 2 and 5 only when {lit}`3a = 0`
    rw [Submodule.disjoint_def]
    intro x hxU hxW
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxW
    have hxval : (x : Polynomial F) = a • (Polynomial.X : Polynomial F) := by
      rw [← ha]; rfl
    have hx : ((x : Polynomial F)).eval 2 = ((x : Polynomial F)).eval 5 := hxU
    rw [hxval] at hx
    simp only [Polynomial.eval_smul, Polynomial.eval_X, smul_eq_mul] at hx
    have ha3 : a * 3 = 0 := by linear_combination -hx
    have ha0 : a = 0 := (mul_eq_zero.mp ha3).resolve_right h3
    exact Subtype.ext (by simp [hxval, ha0])
  · -- {lit}`p = (p - c·x) + c·x` with {lit}`c = (p(5) - p(2))/3`
    rw [codisjoint_iff, eq_top_iff]
    intro p _
    have hmemU : p - ((((p : Polynomial F)).eval 5 - ((p : Polynomial F)).eval 2) / 3)
        • x_degreeLT5 F ∈ U_2C_5 F := by
      show ((p : Polynomial F) - ((((p : Polynomial F)).eval 5
          - ((p : Polynomial F)).eval 2) / 3) • (Polynomial.X : Polynomial F)).eval 2
        = ((p : Polynomial F) - ((((p : Polynomial F)).eval 5
          - ((p : Polynomial F)).eval 2) / 3) • (Polynomial.X : Polynomial F)).eval 5
      simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_X,
        smul_eq_mul]
      field_simp
      ring
    have hmemW : ((((p : Polynomial F)).eval 5 - ((p : Polynomial F)).eval 2) / 3)
        • x_degreeLT5 F ∈ W_2C_5 F := Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
    have hsum := Submodule.add_mem_sup hmemU hmemW
    have heq : (p - ((((p : Polynomial F)).eval 5 - ((p : Polynomial F)).eval 2) / 3)
          • x_degreeLT5 F)
        + ((((p : Polynomial F)).eval 5 - ((p : Polynomial F)).eval 2) / 3) • x_degreeLT5 F
        = p := by abel
    rwa [heq] at hsum

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

/-- {lit}`(x-2)(x-5)(x-6)`, the polynomial cutting out the conditions of 2C.6. -/
private noncomputable def q_2C_6 (F : Type*) [Field F] : Polynomial F :=
  q_2C_5 F * (Polynomial.X - Polynomial.C 6)

private lemma q_2C_6_ne_zero : q_2C_6 F ≠ 0 :=
  mul_ne_zero q_2C_5_ne_zero (Polynomial.X_sub_C_ne_zero 6)

private lemma q_2C_6_natDegree : (q_2C_6 F).natDegree = 3 := by
  rw [q_2C_6, Polynomial.natDegree_mul q_2C_5_ne_zero (Polynomial.X_sub_C_ne_zero 6),
    q_2C_5_natDegree, Polynomial.natDegree_X_sub_C]

/-- (a) A basis of {lit}`U_2C_6`. -/
-- 1, x ^ i * (x - 2)(x - 5)(x - 6) for i = 0, 1
private noncomputable def poly_2C_6 (F : Type*) [Field F] : Fin 3 → Polynomial F :=
  ![1, q_2C_6 F, Polynomial.X * q_2C_6 F]

private lemma poly_2C_6_ne_zero (i : Fin 3) : poly_2C_6 F i ≠ 0 := by
  fin_cases i
  · show (1 : Polynomial F) ≠ 0
    exact one_ne_zero
  · exact q_2C_6_ne_zero
  · exact mul_ne_zero Polynomial.X_ne_zero q_2C_6_ne_zero

private lemma poly_2C_6_natDegree (i : Fin 3) :
    (poly_2C_6 F i).natDegree = ![0, 3, 4] i := by
  fin_cases i
  · show (1 : Polynomial F).natDegree = 0
    simp
  · exact q_2C_6_natDegree
  · show ((Polynomial.X : Polynomial F) * q_2C_6 F).natDegree = 4
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero q_2C_6_ne_zero,
      Polynomial.natDegree_X, q_2C_6_natDegree]

private lemma poly_2C_6_eval (i : Fin 3) :
    (poly_2C_6 F i).eval 2 = (poly_2C_6 F i).eval 5
      ∧ (poly_2C_6 F i).eval 5 = (poly_2C_6 F i).eval 6 := by
  fin_cases i <;> refine ⟨?_, ?_⟩ <;> simp [poly_2C_6, q_2C_6, q_2C_5]

private lemma poly_2C_6_mem (i : Fin 3) : poly_2C_6 F i ∈ Polynomial.degreeLT F 5 := by
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.natDegree_lt_iff_degree_lt (poly_2C_6_ne_zero i)).mp ?_
  rw [poly_2C_6_natDegree i]
  fin_cases i <;> decide

noncomputable def U_2C_6_basis (F : Type*) [Field F] : Fin 3 → U_2C_6 F :=
  fun i => ⟨⟨poly_2C_6 F i, poly_2C_6_mem i⟩, poly_2C_6_eval i⟩

/-- The linear map {lit}`U_2C_6 F → F[X]`. -/
private noncomputable def U_2C_6_toPoly (F : Type*) [Field F] :
    U_2C_6 F →ₗ[F] Polynomial F :=
  (Polynomial.degreeLT F 5).subtype ∘ₗ (U_2C_6 F).subtype

private theorem linearIndependent_U_2C_6_basis :
    LinearIndependent F (U_2C_6_basis F) := by
  apply LinearIndependent.of_comp (U_2C_6_toPoly F)
  have hcomp : (U_2C_6_toPoly F) ∘ (U_2C_6_basis F) = poly_2C_6 F := rfl
  rw [hcomp]
  refine linearIndependent_of_natDegree_injective _ poly_2C_6_ne_zero ?_
  have hd : (fun i => (poly_2C_6 F i).natDegree) = ![0, 3, 4] :=
    funext poly_2C_6_natDegree
  rw [hd]
  decide

instance : Finite F (U_2C_6 F) :=
  Module.Finite.of_injective (U_2C_6 F).subtype Subtype.val_injective

/-- (b) Extension of the {lit}`U_2C_6` basis to a basis of {lit}`P₄(F)`. -/
-- add x and x ^ 2
noncomputable def U_2C_6_extension (F : Type*) [Field F] :
    Fin 2 → Polynomial.degreeLT F 5 := ![x_degreeLT5 F, xSq_degreeLT5 F]

/-- (c) Complement of {lit}`U_2C_6` inside {lit}`P₄(F)`: the span of the two
vectors added in (b). It is introduced here because the dimension of
{lit}`U_2C_6` is read off from the complement (2.43). -/
noncomputable def W_2C_6 (F : Type*) [Field F] :
    Submodule F (Polynomial.degreeLT F 5) :=
  Submodule.span F (Set.range (U_2C_6_extension F))

private noncomputable def poly_2C_6_ext (F : Type*) [Field F] : Fin 2 → Polynomial F :=
  ![Polynomial.X, Polynomial.X ^ 2]

private lemma linearIndependent_U_2C_6_extension :
    LinearIndependent F (U_2C_6_extension F) := by
  apply LinearIndependent.of_comp (Polynomial.degreeLT F 5).subtype
  have hcomp : ((Polynomial.degreeLT F 5).subtype ∘ (U_2C_6_extension F))
      = poly_2C_6_ext F := by
    funext j; fin_cases j <;> rfl
  rw [hcomp]
  refine linearIndependent_of_natDegree_injective _ (fun j => ?_) ?_
  · fin_cases j
    · show (Polynomial.X : Polynomial F) ≠ 0
      exact Polynomial.X_ne_zero
    · show ((Polynomial.X : Polynomial F) ^ 2) ≠ 0
      exact pow_ne_zero 2 Polynomial.X_ne_zero
  · have hd : (fun j => (poly_2C_6_ext F j).natDegree) = ![1, 2] := by
      funext j
      fin_cases j
      · show (Polynomial.X : Polynomial F).natDegree = 1
        simp
      · show ((Polynomial.X : Polynomial F) ^ 2).natDegree = 2
        simp
    rw [hd]
    decide

private lemma finrank_W_2C_6 : finrank F (W_2C_6 F) = 2 := by
  have := finrank_span_eq_card (R := F) linearIndependent_U_2C_6_extension
  simpa [W_2C_6] using this

/-- {lit}`U_2C_6` and its complement: a vector of {lit}`W_2C_6` lying in
{lit}`U_2C_6` must vanish, and every {lit}`p` splits as a member of
{lit}`U_2C_6` plus a combination of {lit}`x` and {lit}`x²`. -/
private theorem isCompl_2C_6 [CharZero F] : IsCompl (U_2C_6 F) (W_2C_6 F) := by
  have h12 : (12 : F) ≠ 0 := by norm_num
  constructor
  · -- {lit}`c₀x + c₁x²` takes the same value at 2, 5, 6 only when {lit}`c = 0`
    rw [Submodule.disjoint_def]
    intro x hxU hxW
    have hxW' : x ∈ Submodule.span F (Set.range (U_2C_6_extension F)) := hxW
    rw [Submodule.mem_span_range_iff_exists_fun] at hxW'
    obtain ⟨c, hc⟩ := hxW'
    have hxval : (x : Polynomial F) = c 0 • (Polynomial.X : Polynomial F)
        + c 1 • (Polynomial.X : Polynomial F) ^ 2 := by
      rw [← hc]
      simp [Fin.sum_univ_two, U_2C_6_extension, x_degreeLT5, xSq_degreeLT5]
    have h1 : ((x : Polynomial F)).eval 2 = ((x : Polynomial F)).eval 5 := hxU.1
    have h2 : ((x : Polynomial F)).eval 5 = ((x : Polynomial F)).eval 6 := hxU.2
    rw [hxval] at h1 h2
    simp only [Polynomial.eval_add, Polynomial.eval_smul, Polynomial.eval_X,
      Polynomial.eval_pow, smul_eq_mul] at h1 h2
    have hc1 : c 1 * 12 = 0 := by linear_combination h1 - 3 * h2
    have hc1z : c 1 = 0 := (mul_eq_zero.mp hc1).resolve_right h12
    have hc0z : c 0 = 0 := by linear_combination -h2 - 11 * hc1z
    exact Subtype.ext (by simp [hxval, hc0z, hc1z])
  · -- solve {lit}`p - c₀x - c₁x² ∈ U_2C_6` for {lit}`c₀, c₁`
    rw [codisjoint_iff, eq_top_iff]
    intro p _
    obtain ⟨A, hA⟩ : ∃ A : F, ((p : Polynomial F)).eval 2 = A := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : F, ((p : Polynomial F)).eval 5 = B := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C : F, ((p : Polynomial F)).eval 6 = C := ⟨_, rfl⟩
    have hmemU : p - (((-11 * A + 32 * B - 21 * C) / 12) • x_degreeLT5 F
        + ((A - 4 * B + 3 * C) / 12) • xSq_degreeLT5 F) ∈ U_2C_6 F := by
      constructor
      · show ((p : Polynomial F) - (((-11 * A + 32 * B - 21 * C) / 12)
              • (Polynomial.X : Polynomial F)
            + ((A - 4 * B + 3 * C) / 12) • (Polynomial.X : Polynomial F) ^ 2)).eval 2
          = ((p : Polynomial F) - (((-11 * A + 32 * B - 21 * C) / 12)
              • (Polynomial.X : Polynomial F)
            + ((A - 4 * B + 3 * C) / 12) • (Polynomial.X : Polynomial F) ^ 2)).eval 5
        simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_smul,
          Polynomial.eval_X, Polynomial.eval_pow, smul_eq_mul]
        rw [hA, hB]
        field_simp
        ring
      · show ((p : Polynomial F) - (((-11 * A + 32 * B - 21 * C) / 12)
              • (Polynomial.X : Polynomial F)
            + ((A - 4 * B + 3 * C) / 12) • (Polynomial.X : Polynomial F) ^ 2)).eval 5
          = ((p : Polynomial F) - (((-11 * A + 32 * B - 21 * C) / 12)
              • (Polynomial.X : Polynomial F)
            + ((A - 4 * B + 3 * C) / 12) • (Polynomial.X : Polynomial F) ^ 2)).eval 6
        simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_smul,
          Polynomial.eval_X, Polynomial.eval_pow, smul_eq_mul]
        rw [hB, hC]
        field_simp
        ring
    have hmemW : (((-11 * A + 32 * B - 21 * C) / 12) • x_degreeLT5 F
        + ((A - 4 * B + 3 * C) / 12) • xSq_degreeLT5 F) ∈ W_2C_6 F := by
      rw [W_2C_6, Submodule.mem_span_range_iff_exists_fun]
      exact ⟨![(-11 * A + 32 * B - 21 * C) / 12, (A - 4 * B + 3 * C) / 12],
        by simp [Fin.sum_univ_two, U_2C_6_extension]⟩
    have hsum := Submodule.add_mem_sup hmemU hmemW
    have heq : (p - (((-11 * A + 32 * B - 21 * C) / 12) • x_degreeLT5 F
          + ((A - 4 * B + 3 * C) / 12) • xSq_degreeLT5 F))
        + (((-11 * A + 32 * B - 21 * C) / 12) • x_degreeLT5 F
          + ((A - 4 * B + 3 * C) / 12) • xSq_degreeLT5 F) = p := by abel
    rwa [heq] at hsum

private theorem finrank_U_2C_6 [CharZero F] : finrank F (U_2C_6 F) = 3 := by
  -- 2.43 applied to the complementary pair {lit}`U_2C_6, W_2C_6`
  have h := finrank_sup_add_finrank_inf_eq (U_2C_6 F) (W_2C_6 F)
  rw [(isCompl_2C_6 (F := F)).sup_eq_top, (isCompl_2C_6 (F := F)).inf_eq_bot,
    finrank_top, finrank_bot, finrank_degreeLT5, finrank_W_2C_6] at h
  omega

/-- 2C.6 (a): the chosen list is a basis of {lit}`U_2C_6`. -/
theorem exercise_2C_6a [CharZero F] : IsBasis F (U_2C_6_basis F) :=
  isBasis_of_linearIndependent_of_card_eq _ linearIndependent_U_2C_6_basis
    finrank_U_2C_6.symm

/-- The underlying polynomials of the extended list. -/
private noncomputable def poly_2C_6_full (F : Type*) [Field F] :
    Fin (3 + 2) → Polynomial F :=
  ![1, q_2C_6 F, Polynomial.X * q_2C_6 F, Polynomial.X, Polynomial.X ^ 2]

private lemma poly_2C_6_full_ne_zero (j : Fin (3 + 2)) : poly_2C_6_full F j ≠ 0 := by
  fin_cases j
  · show (1 : Polynomial F) ≠ 0
    exact one_ne_zero
  · exact q_2C_6_ne_zero
  · exact mul_ne_zero Polynomial.X_ne_zero q_2C_6_ne_zero
  · exact Polynomial.X_ne_zero
  · exact pow_ne_zero 2 Polynomial.X_ne_zero

private lemma poly_2C_6_full_natDegree (j : Fin (3 + 2)) :
    (poly_2C_6_full F j).natDegree = ![0, 3, 4, 1, 2] j := by
  fin_cases j
  · show (1 : Polynomial F).natDegree = 0
    simp
  · exact q_2C_6_natDegree
  · show ((Polynomial.X : Polynomial F) * q_2C_6 F).natDegree = 4
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero q_2C_6_ne_zero,
      Polynomial.natDegree_X, q_2C_6_natDegree]
  · show (Polynomial.X : Polynomial F).natDegree = 1
    simp
  · show ((Polynomial.X : Polynomial F) ^ 2).natDegree = 2
    simp

private lemma U_2C_6_append_coe (j : Fin (3 + 2)) :
    ((Fin.append (fun i => ((U_2C_6_basis F i : Polynomial.degreeLT F 5)))
        (U_2C_6_extension F) j : Polynomial.degreeLT F 5) : Polynomial F)
      = poly_2C_6_full F j := by
  fin_cases j <;> rfl

/-- 2C.6 (b): appending the extension to the basis of {lit}`U_2C_6` gives a
basis of {lit}`P₄(F)`. -/
theorem exercise_2C_6b :
    IsBasis F (Fin.append (fun i => ((U_2C_6_basis F i : Polynomial.degreeLT F 5)))
      (U_2C_6_extension F)) := by
  refine isBasis_of_linearIndependent_of_card_eq _ ?_ (by rw [finrank_degreeLT5])
  apply LinearIndependent.of_comp (Polynomial.degreeLT F 5).subtype
  have hcomp : ((Polynomial.degreeLT F 5).subtype ∘
      Fin.append (fun i => ((U_2C_6_basis F i : Polynomial.degreeLT F 5)))
        (U_2C_6_extension F)) = poly_2C_6_full F := by
    funext j; exact U_2C_6_append_coe j
  rw [hcomp]
  refine linearIndependent_of_natDegree_injective _ poly_2C_6_full_ne_zero ?_
  have hd : (fun j => (poly_2C_6_full F j).natDegree) = ![0, 3, 4, 1, 2] :=
    funext poly_2C_6_full_natDegree
  rw [hd]
  decide

/-- 2C.6 (c): {lit}`U_2C_6` and {lit}`W_2C_6` are complementary. -/
theorem exercise_2C_6c [CharZero F] : IsCompl (U_2C_6 F) (W_2C_6 F) := isCompl_2C_6

/-! 2C.7 Let {lit}`U = {p ∈ P₄(ℝ) : ∫₋₁¹ p = 0}`. We encode the integral
algebraically: for {lit}`p = ∑ cᵢ Xⁱ` of degree {lit}`< 5`,
{lit}`∫₋₁¹ p = ∑ᵢ cᵢ · (1 - (-1)^(i+1))/(i+1) = 2 c₀ + (2/3) c₂ + (2/5) c₄`.
Vanishing of this linear form on coefficients is what we use. -/
-- the basis is then x, x^3, 3 * x^2 - 1, 5 x^4 - 1

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
-- see above: x, x ^ 3, 3x ^ 2 - 1, 5x ^ 4 - 1
private noncomputable def poly_2C_7 : Fin 4 → Polynomial ℝ :=
  ![Polynomial.X, Polynomial.X ^ 3,
    Polynomial.C 3 * Polynomial.X ^ 2 - 1, Polynomial.C 5 * Polynomial.X ^ 4 - 1]

private lemma poly_2C_7_natDegree (i : Fin 4) :
    (poly_2C_7 i).natDegree = ![1, 3, 2, 4] i := by
  fin_cases i
  · show (Polynomial.X : Polynomial ℝ).natDegree = 1
    simp
  · show ((Polynomial.X : Polynomial ℝ) ^ 3).natDegree = 3
    simp
  · show ((Polynomial.C 3 * Polynomial.X ^ 2 - 1 : Polynomial ℝ)).natDegree = 2
    have h2 : ((Polynomial.C 3 * Polynomial.X ^ 2 : Polynomial ℝ)).natDegree = 2 :=
      Polynomial.natDegree_C_mul_X_pow 2 3 (by norm_num)
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      (by rw [Polynomial.natDegree_one, h2]; norm_num), h2]
  · show ((Polynomial.C 5 * Polynomial.X ^ 4 - 1 : Polynomial ℝ)).natDegree = 4
    have h4 : ((Polynomial.C 5 * Polynomial.X ^ 4 : Polynomial ℝ)).natDegree = 4 :=
      Polynomial.natDegree_C_mul_X_pow 4 5 (by norm_num)
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      (by rw [Polynomial.natDegree_one, h4]; norm_num), h4]

private lemma poly_2C_7_ne_zero (i : Fin 4) : poly_2C_7 i ≠ 0 := by
  intro h
  have hd := poly_2C_7_natDegree i
  rw [h, Polynomial.natDegree_zero] at hd
  revert hd
  fin_cases i <;> decide

/-- Each listed polynomial has vanishing integral over {lit}`[-1, 1]`. -/
private lemma poly_2C_7_integral (i : Fin 4) :
    2 * (poly_2C_7 i).coeff 0 + (2 / 3) * (poly_2C_7 i).coeff 2
      + (2 / 5) * (poly_2C_7 i).coeff 4 = 0 := by
  fin_cases i <;>
    simp [poly_2C_7, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_one]

private lemma poly_2C_7_mem (i : Fin 4) : poly_2C_7 i ∈ Polynomial.degreeLT ℝ 5 := by
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.natDegree_lt_iff_degree_lt (poly_2C_7_ne_zero i)).mp ?_
  rw [poly_2C_7_natDegree i]
  fin_cases i <;> decide

noncomputable def U_2C_7_basis : Fin 4 → U_2C_7 :=
  fun i => ⟨⟨poly_2C_7 i, poly_2C_7_mem i⟩, poly_2C_7_integral i⟩

/-- The linear map {lit}`U_2C_7 → ℝ[X]`. -/
private noncomputable def U_2C_7_toPoly : U_2C_7 →ₗ[ℝ] Polynomial ℝ :=
  (Polynomial.degreeLT ℝ 5).subtype ∘ₗ U_2C_7.subtype

private theorem linearIndependent_U_2C_7_basis :
    LinearIndependent ℝ U_2C_7_basis := by
  apply LinearIndependent.of_comp U_2C_7_toPoly
  have hcomp : U_2C_7_toPoly ∘ U_2C_7_basis = poly_2C_7 := rfl
  rw [hcomp]
  refine linearIndependent_of_natDegree_injective _ poly_2C_7_ne_zero ?_
  have hd : (fun i => (poly_2C_7 i).natDegree) = ![1, 3, 2, 4] :=
    funext poly_2C_7_natDegree
  rw [hd]
  decide

instance : Finite ℝ U_2C_7 :=
  Module.Finite.of_injective U_2C_7.subtype Subtype.val_injective

/-- {lit}`1 ∉ U_2C_7`: the constant {lit}`1` has integral {lit}`2`. -/
private lemma one_not_mem_U_2C_7 : one_degreeLT5 ℝ ∉ U_2C_7 := by
  intro h
  have h1 : 2 * (1 : Polynomial ℝ).coeff 0 + (2 / 3) * (1 : Polynomial ℝ).coeff 2
      + (2 / 5) * (1 : Polynomial ℝ).coeff 4 = 0 := h
  simp [Polynomial.coeff_one] at h1

private theorem finrank_U_2C_7 : finrank ℝ U_2C_7 = 4 := by
  -- Lower bound: the four listed vectors are linearly independent.
  have hge : 4 ≤ finrank ℝ U_2C_7 := by
    have := linearIndependent_U_2C_7_basis.fintype_card_le_finrank
    simpa using this
  -- Upper bound: {lit}`dim ≤ 5`, and {lit}`= 5` would force {lit}`U = P₄(ℝ)`,
  -- contradicted by {lit}`1 ∉ U`.
  have hle : finrank ℝ U_2C_7 ≤ 5 := by
    have := finrank_submodule_le U_2C_7
    rwa [finrank_degreeLT5] at this
  have hne_top : U_2C_7 ≠ ⊤ := fun h => one_not_mem_U_2C_7 (by rw [h]; trivial)
  have hne_5 : finrank ℝ U_2C_7 ≠ 5 := fun heq =>
    hne_top (subspace_eq_top_of_finrank_eq _ (by rw [heq, finrank_degreeLT5]))
  omega

/-- 2C.7 (a): the chosen list is a basis of {lit}`U_2C_7`. -/
theorem exercise_2C_7a : IsBasis ℝ U_2C_7_basis :=
  isBasis_of_linearIndependent_of_card_eq _ linearIndependent_U_2C_7_basis
    finrank_U_2C_7.symm

/-- (b) Extension of the {lit}`U_2C_7` basis to a basis of {lit}`P₄(ℝ)`. -/
-- add 1
noncomputable def U_2C_7_extension : Fin 1 → Polynomial.degreeLT ℝ 5 :=
  fun _ => one_degreeLT5 ℝ

/-- The underlying polynomials of the extended list. -/
private noncomputable def poly_2C_7_full : Fin (4 + 1) → Polynomial ℝ :=
  ![Polynomial.X, Polynomial.X ^ 3,
    Polynomial.C 3 * Polynomial.X ^ 2 - 1, Polynomial.C 5 * Polynomial.X ^ 4 - 1, 1]

private lemma poly_2C_7_full_natDegree (j : Fin (4 + 1)) :
    (poly_2C_7_full j).natDegree = ![1, 3, 2, 4, 0] j := by
  fin_cases j
  · exact poly_2C_7_natDegree 0
  · exact poly_2C_7_natDegree 1
  · exact poly_2C_7_natDegree 2
  · exact poly_2C_7_natDegree 3
  · show (1 : Polynomial ℝ).natDegree = 0
    simp

private lemma poly_2C_7_full_ne_zero (j : Fin (4 + 1)) : poly_2C_7_full j ≠ 0 := by
  fin_cases j
  · exact poly_2C_7_ne_zero 0
  · exact poly_2C_7_ne_zero 1
  · exact poly_2C_7_ne_zero 2
  · exact poly_2C_7_ne_zero 3
  · show (1 : Polynomial ℝ) ≠ 0
    exact one_ne_zero

private lemma U_2C_7_append_coe (j : Fin (4 + 1)) :
    ((Fin.append (fun i => ((U_2C_7_basis i : Polynomial.degreeLT ℝ 5)))
        U_2C_7_extension j : Polynomial.degreeLT ℝ 5) : Polynomial ℝ)
      = poly_2C_7_full j := by
  fin_cases j <;> rfl

/-- 2C.7 (b): appending the extension to the basis of {lit}`U_2C_7` gives a
basis of {lit}`P₄(ℝ)`. -/
theorem exercise_2C_7b :
    IsBasis ℝ (Fin.append (fun i => ((U_2C_7_basis i : Polynomial.degreeLT ℝ 5)))
      U_2C_7_extension) := by
  refine isBasis_of_linearIndependent_of_card_eq _ ?_ (by rw [finrank_degreeLT5])
  apply LinearIndependent.of_comp (Polynomial.degreeLT ℝ 5).subtype
  have hcomp : ((Polynomial.degreeLT ℝ 5).subtype ∘
      Fin.append (fun i => ((U_2C_7_basis i : Polynomial.degreeLT ℝ 5)))
        U_2C_7_extension) = poly_2C_7_full := by
    funext j; exact U_2C_7_append_coe j
  rw [hcomp]
  refine linearIndependent_of_natDegree_injective _ poly_2C_7_full_ne_zero ?_
  have hd : (fun j => (poly_2C_7_full j).natDegree) = ![1, 3, 2, 4, 0] :=
    funext poly_2C_7_full_natDegree
  rw [hd]
  decide

/-- (c) Complement of {lit}`U_2C_7` inside {lit}`P₄(ℝ)`. -/
-- span {1}
noncomputable def W_2C_7 : Submodule ℝ (Polynomial.degreeLT ℝ 5) :=
  Submodule.span ℝ {one_degreeLT5 ℝ}

/-- 2C.7 (c): {lit}`U_2C_7` and {lit}`W_2C_7` are complementary. -/
theorem exercise_2C_7c : IsCompl U_2C_7 W_2C_7 := by
  constructor
  · -- a constant with vanishing integral is {lit}`0`
    rw [Submodule.disjoint_def]
    intro x hxU hxW
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxW
    have hxval : (x : Polynomial ℝ) = a • (1 : Polynomial ℝ) := by rw [← ha]; rfl
    have hx : 2 * ((x : Polynomial ℝ)).coeff 0 + (2 / 3) * ((x : Polynomial ℝ)).coeff 2
        + (2 / 5) * ((x : Polynomial ℝ)).coeff 4 = 0 := hxU
    rw [hxval] at hx
    simp [Polynomial.coeff_one] at hx
    exact Subtype.ext (by simp [hxval, hx])
  · -- {lit}`p = (p - (∫p / 2)·1) + (∫p / 2)·1`
    rw [codisjoint_iff, eq_top_iff]
    intro p _
    obtain ⟨L, hL⟩ : ∃ L : ℝ, 2 * ((p : Polynomial ℝ)).coeff 0
        + (2 / 3) * ((p : Polynomial ℝ)).coeff 2
        + (2 / 5) * ((p : Polynomial ℝ)).coeff 4 = L := ⟨_, rfl⟩
    have hmemU : p - (L / 2) • one_degreeLT5 ℝ ∈ U_2C_7 := by
      show 2 * ((p : Polynomial ℝ) - (L / 2) • (1 : Polynomial ℝ)).coeff 0
        + (2 / 3) * ((p : Polynomial ℝ) - (L / 2) • (1 : Polynomial ℝ)).coeff 2
        + (2 / 5) * ((p : Polynomial ℝ) - (L / 2) • (1 : Polynomial ℝ)).coeff 4 = 0
      simp only [Polynomial.coeff_sub, Polynomial.coeff_smul, Polynomial.coeff_one,
        smul_eq_mul]
      norm_num
      linarith [hL]
    have hmemW : (L / 2) • one_degreeLT5 ℝ ∈ W_2C_7 :=
      Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
    have hsum := Submodule.add_mem_sup hmemU hmemW
    have heq : (p - (L / 2) • one_degreeLT5 ℝ) + (L / 2) • one_degreeLT5 ℝ = p := by abel
    rwa [heq] at hsum

/-- 2C.8 -/
-- The differences (v i + w) - (v 0 + w) = v i - v 0 for i ≠ 0 lie in the span
-- and are linearly independent, so the span has dimension at least m - 1.
theorem exercise_2C_8 {m : ℕ} (v : Fin m → V) (hv : LinearIndependent F v)
    (w : V) :
    m - 1 ≤ finrank F
      (Submodule.span F (Set.range (fun i : Fin m => v i + w))) := by
  obtain _ | n := m
  · simp
  have hmem : ∀ i : Fin (n + 1), v i + w ∈
      Submodule.span F (Set.range fun j : Fin (n + 1) => v j + w) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have hd : LinearIndependent F (fun i : Fin n =>
      (⟨v i.succ + w, hmem i.succ⟩ :
          ↥(Submodule.span F (Set.range fun j : Fin (n + 1) => v j + w)))
        - ⟨v 0 + w, hmem 0⟩) := by
    apply LinearIndependent.of_comp
      (Submodule.span F (Set.range fun j : Fin (n + 1) => v j + w)).subtype
    have hcomp :
        ((Submodule.span F (Set.range fun j : Fin (n + 1) => v j + w)).subtype ∘
          fun i : Fin n =>
            (⟨v i.succ + w, hmem i.succ⟩ :
                ↥(Submodule.span F (Set.range fun j : Fin (n + 1) => v j + w)))
              - ⟨v 0 + w, hmem 0⟩)
        = fun i : Fin n => v i.succ - v 0 := by
      funext i
      show (v i.succ + w) - (v 0 + w) = v i.succ - v 0
      abel
    rw [hcomp, Fintype.linearIndependent_iff]
    intro a ha i
    -- {lit}`∑ a i • v i.succ = (∑ a i) • v 0`, so {lit}`-(∑ a i), a` is a
    -- vanishing combination of the linearly independent {lit}`v`.
    have ha' : (∑ i, a i • v i.succ) = (∑ k, a k) • v 0 := by
      rw [← sub_eq_zero]
      simpa [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] using ha
    have hzero : ∑ j : Fin (n + 1),
        (Fin.cons (-(∑ k, a k)) a : Fin (n + 1) → F) j • v j = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, neg_smul]
      rw [ha']
      abel
    have hc := (Fintype.linearIndependent_iff.mp hv) _ hzero i.succ
    simpa using hc
  haveI : FiniteDimensional F
      ↥(Submodule.span F (Set.range fun j : Fin (n + 1) => v j + w)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range _)
  simpa using hd.fintype_card_le_finrank

/-- 2C.9 -/
theorem exercise_2C_9 [Infinite F] (m : ℕ) (_hm : 1 ≤ m)
    (p : Fin (m + 1) → Polynomial.degreeLT F (m + 1))
    (hp : ∀ k : Fin (m + 1), (p k : Polynomial F).degree = (k : ℕ)) :
    IsBasis F p := by
  -- LI is enough, since the list has the right length: the degrees
  -- {lit}`0, 1, …, m` are distinct, so the list is linearly independent.
  haveI : Finite F (Polynomial.degreeLT F (m + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv F (m + 1)).symm
  have hne : ∀ k, ((p k : Polynomial F)) ≠ 0 := by
    intro k h
    have hk := hp k
    rw [h, Polynomial.degree_zero] at hk
    simp at hk
  have hnat : ∀ k, ((p k : Polynomial F)).natDegree = (k : ℕ) := fun k =>
    Polynomial.natDegree_eq_of_degree_eq_some (hp k)
  refine isBasis_of_linearIndependent_of_card_eq _ ?_ ?_
  · apply LinearIndependent.of_comp (Polynomial.degreeLT F (m + 1)).subtype
    refine linearIndependent_of_natDegree_injective _ hne ?_
    intro a b hab
    simp only [Function.comp_apply, Submodule.subtype_apply, hnat] at hab
    exact Fin.ext hab
  · simp only [(Polynomial.degreeLTEquiv F (m + 1)).finrank_eq, Module.finrank_pi,
      Fintype.card_fin]

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

private lemma one_sub_X_ne_zero : (1 - Polynomial.X : Polynomial F) ≠ 0 := by
  intro h
  have h0 := congrArg (fun p => Polynomial.coeff p 0) h
  simp at h0

private lemma natTrailingDegree_one_sub_X_pow (j : ℕ) :
    ((1 - Polynomial.X : Polynomial F) ^ j).natTrailingDegree = 0 := by
  refine Nat.le_zero.mp (Polynomial.natTrailingDegree_le_of_ne_zero ?_)
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp

/-- {lit}`Xᵏ(1-X)ʲ` has trailing degree {lit}`k`. -/
private lemma natTrailingDegree_X_pow_mul_one_sub_X_pow (k j : ℕ) :
    ((Polynomial.X : Polynomial F) ^ k * (1 - Polynomial.X) ^ j).natTrailingDegree = k := by
  rw [Polynomial.natTrailingDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero)
      (pow_ne_zero _ one_sub_X_ne_zero),
    Polynomial.natTrailingDegree_X_pow, natTrailingDegree_one_sub_X_pow, add_zero]

/-- 2C.10 -/
theorem exercise_2C_10 [Infinite F] (m : ℕ) (_hm : 1 ≤ m) :
    IsBasis F (fun k : Fin (m + 1) =>
      (⟨Polynomial.X ^ (k : ℕ) * (1 - Polynomial.X) ^ (m - (k : ℕ)), by
        have hk : (k : ℕ) + (m - (k : ℕ)) = m := by have := k.isLt; omega
        have := X_pow_one_sub_X_pow_mem_degreeLT (F := F) (k : ℕ) (m - (k : ℕ))
        rwa [hk] at this⟩ : Polynomial.degreeLT F (m + 1))) := by
  -- LI is enough by size: {lit}`Xᵏ(1-X)^(m-k)` has trailing degree exactly
  -- {lit}`k`, since {lit}`(1-X)^(m-k)` has nonzero constant term.
  haveI : Finite F (Polynomial.degreeLT F (m + 1)) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv F (m + 1)).symm
  refine isBasis_of_linearIndependent_of_card_eq _ ?_ ?_
  · apply LinearIndependent.of_comp (Polynomial.degreeLT F (m + 1)).subtype
    refine linearIndependent_of_natTrailingDegree_injective _ (fun k => ?_) ?_
    · exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (pow_ne_zero _ one_sub_X_ne_zero)
    · intro a b hab
      simp only [Function.comp_apply, Submodule.subtype_apply,
        natTrailingDegree_X_pow_mul_one_sub_X_pow] at hab
      exact Fin.ext hab
  · simp only [(Polynomial.degreeLTEquiv F (m + 1)).finrank_eq, Module.finrank_pi,
      Fintype.card_fin]

/-- 2C.11 -/
theorem exercise_2C_11 (U W : Submodule ℂ (Fin 6 → ℂ))
    (hU : finrank ℂ U = 4) (hW : finrank ℂ W = 4) :
    ∃ x y : (U ⊓ W : Submodule ℂ (Fin 6 → ℂ)),
      (∀ a : ℂ, x ≠ a • y) ∧ (∀ b : ℂ, y ≠ b • x) := by
  -- 2.43: dim (U ⊓ W) = dim U + dim W - dim (U ⊔ W) ≥ 4 + 4 - 6 = 2, so a basis
  -- of {lit}`U ⊓ W` has two entries, and neither is a multiple of the other.
  have hdim : finrank ℂ (Fin 6 → ℂ) = 6 := by simp
  have hsum := finrank_sup_add_finrank_inf_eq U W
  have hle : finrank ℂ ↥(U ⊔ W) ≤ 6 := by
    have := finrank_submodule_le (U ⊔ W)
    rwa [hdim] at this
  obtain ⟨m, v, hv⟩ := LADR.Section_2B.exists_basis (F := ℂ) (V := ↥(U ⊓ W))
  have hm : m = finrank ℂ ↥(U ⊓ W) := isBasis_card_eq_finrank v hv
  have hm2 : 2 ≤ m := by omega
  obtain ⟨i0, i1, hne⟩ : ∃ i0 i1 : Fin m, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have he : Function.Injective (![i0, i1] : Fin 2 → Fin m) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hli := Fintype.linearIndependent_iff.mp (hv.1.comp _ he)
  refine ⟨v i0, v i1, ?_, ?_⟩
  · intro a hxy
    have hsum0 : ∑ i : Fin 2, (![1, -a] : Fin 2 → ℂ) i • ((v ∘ ![i0, i1]) i) = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Function.comp_apply, one_smul, neg_smul]
      rw [hxy]
      abel
    have h0 := hli _ hsum0 0
    simp at h0
  · intro b hyx
    have hsum0 : ∑ i : Fin 2, (![-b, 1] : Fin 2 → ℂ) i • ((v ∘ ![i0, i1]) i) = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Function.comp_apply, one_smul, neg_smul]
      rw [hyx]
      abel
    have h1 := hli _ hsum0 1
    simp at h1

/-- 2C.12 -/
theorem exercise_2C_12 (U W : Submodule ℝ (Fin 8 → ℝ))
    (hU : finrank ℝ U = 3) (hW : finrank ℝ W = 5)
    (hUW : U ⊔ W = ⊤) : IsCompl U W := by
  -- 2.43: {lit}`8 + dim (U ⊓ W) = 3 + 5`, so {lit}`U ⊓ W = ⊥`; together with the
  -- assumed {lit}`U ⊔ W = ⊤` that is exactly complementarity.
  have hdim : finrank ℝ (Fin 8 → ℝ) = 8 := by simp
  have hsum := finrank_sup_add_finrank_inf_eq U W
  rw [hUW, finrank_top, hdim, hU, hW] at hsum
  have hinf : finrank ℝ ↥(U ⊓ W) = 0 := by omega
  exact ⟨disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf), codisjoint_iff.mpr hUW⟩

/-- Corollary of 2.43: {lit}`dim (A ⊓ B) ≥ dim A + dim B - dim V`, stated
additively to stay inside {lit}`ℕ`. -/
private lemma finrank_le_finrank_inf_add [Finite F V] (A B : Submodule F V) :
    finrank F A + finrank F B ≤ finrank F ↥(A ⊓ B) + finrank F V := by
  have h := finrank_sup_add_finrank_inf_eq A B
  have hle : finrank F ↥(A ⊔ B) ≤ finrank F V := finrank_submodule_le _
  omega

/-- 2C.13 -/
theorem exercise_2C_13 (U W : Submodule ℝ (Fin 9 → ℝ))
    (hU : finrank ℝ U = 5) (hW : finrank ℝ W = 5) :
    U ⊓ W ≠ ⊥ := by
  -- by contra that would give dim (U ⊔ W) = 5 + 5 - 0 = 10, contradicting dim (Fin 9 → ℝ) = 9.
  intro h
  have hdim : finrank ℝ (Fin 9 → ℝ) = 9 := by simp
  have hkey := finrank_le_finrank_inf_add U W
  rw [hdim, hU, hW] at hkey
  have h0 : finrank ℝ ↥(U ⊓ W) = 0 := Submodule.finrank_eq_zero.mpr h
  omega

/-- 2C.14 -/
theorem exercise_2C_14 [Finite F V] (hV : finrank F V = 10)
    (V₁ V₂ V₃ : Submodule F V)
    (hV₁ : finrank F V₁ = 7) (hV₂ : finrank F V₂ = 7)
    (hV₃ : finrank F V₃ = 7) :
    V₁ ⊓ V₂ ⊓ V₃ ≠ ⊥ := by
  -- U = V1 ∩ V2 has to be at least 4 by dim count
  -- U ∩ V3 has to be at least 1 by dim count
  intro h
  have h12 := finrank_le_finrank_inf_add V₁ V₂
  have h123 := finrank_le_finrank_inf_add (V₁ ⊓ V₂) V₃
  rw [hV, hV₁, hV₂] at h12
  rw [hV, hV₃] at h123
  have h0 : finrank F ↥(V₁ ⊓ V₂ ⊓ V₃) = 0 := Submodule.finrank_eq_zero.mpr h
  omega

/-- 2C.15 -/
theorem exercise_2C_15 [Finite F V] (V₁ V₂ V₃ : Submodule F V)
    (hsum : finrank F V₁ + finrank F V₂ + finrank F V₃ >
      2 * finrank F V) :
    V₁ ⊓ V₂ ⊓ V₃ ≠ ⊥ := by
  -- by contra
  -- dim V1 + dim V2 - dim (V1 + V2) = dim (V1 ∩ V2)
  -- dim (V1 ∩ V2) + dim V3 - dim ((V1 ∩ V2) + V3) = dim (V1 ∩ V2 � ∩ V3) = 0
  -- combine to get
  -- dim V1 + dim V2 + dim V3 = dim ((V1 ∩ V2) + V3) + dim (V1 + V2)
  -- 2 * dim V < dim ((V1 ∩ V2) + V3) + dim (V1 + V2)
  -- but two subspaces can't add to twice the sum of the ambient space, so contradiction
  intro h
  have h12 := finrank_le_finrank_inf_add V₁ V₂
  have h123 := finrank_le_finrank_inf_add (V₁ ⊓ V₂) V₃
  have h0 : finrank F ↥(V₁ ⊓ V₂ ⊓ V₃) = 0 := Submodule.finrank_eq_zero.mpr h
  omega

/-- Auxiliary for 2C.16: if a combination of a linearly independent list lies in
the span of all its entries except the {lit}`q`-th, the {lit}`q`-th coefficient
vanishes. -/
private lemma coeff_eq_zero_of_mem_span_succAbove {k : ℕ} (w : Fin (k + 1) → V)
    (hw : LinearIndependent F w) (q : Fin (k + 1)) (c : Fin (k + 1) → F)
    (hx : (∑ i, c i • w i) ∈
      Submodule.span F (Set.range fun t : Fin k => w (q.succAbove t))) :
    c q = 0 := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨d, hd⟩ := hx
  -- {lit}`insertNth q 0 d` is {lit}`d` spread over the indices {lit}`≠ q`
  have hins : (∑ i, (q.insertNth (α := fun _ => F) 0 d) i • w i) = ∑ i, c i • w i := by
    rw [Fin.sum_univ_succAbove (fun i => (q.insertNth (α := fun _ => F) 0 d) i • w i) q]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, zero_smul,
      zero_add]
    exact hd
  have hzero : ∑ i, (c i - (q.insertNth (α := fun _ => F) 0 d) i) • w i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, hins, sub_self]
  have hc := Fintype.linearIndependent_iff.mp hw _ hzero q
  simpa using hc

/-- The index omitted by the {lit}`j`-th hyperplane of 2C.16: the
{lit}`(m + j)`-th basis vector. -/
private def omitIndex {k m : ℕ} (j : Fin (k + 1 - m)) : Fin (k + 1) :=
  ⟨m + j.val, by have := j.isLt; omega⟩

/-- 2C.16 -/
-- take a basis of U and extend to a basis of V; the j-th subspace is the span of
-- all the extended basis vectors except the (m + j)-th one. Each has dimension
-- n - 1, they all contain U, and a vector in every one of them has vanishing
-- coefficient on each added basis vector, so it lies in U.
theorem exercise_2C_16 [Finite F V] (U : Submodule F V) (hU : U ≠ ⊤) :
    ∃ (W : Fin (finrank F V - finrank F U) → Submodule F V),
      (∀ i, finrank F (W i) = finrank F V - 1) ∧
      ⨅ i, W i = U := by
  classical
  obtain ⟨m, u, hu⟩ := LADR.Section_2B.exists_basis (F := F) (V := ↥U)
  have hm : m = finrank F U := isBasis_card_eq_finrank u hu
  have huV : LinearIndependent F (fun i => (u i : V)) :=
    hu.1.map' U.subtype (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  obtain ⟨n, w, hmn, hw, hprefix⟩ :=
    LADR.Section_2B.exists_basis_extending (fun i => (u i : V)) huV
  have hn : n = finrank F V := isBasis_card_eq_finrank w hw
  -- {lit}`m < n`: otherwise {lit}`dim U = dim V`, forcing {lit}`U = ⊤`
  have hmltn : m < n := by
    rcases lt_or_eq_of_le hmn with h | h
    · exact h
    · exact absurd (subspace_eq_top_of_finrank_eq U (by omega)) hU
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [← hm, ← hn]
  refine ⟨fun j => Submodule.span F
    (Set.range fun t : Fin k => w ((omitIndex j).succAbove t)), ?_, ?_⟩
  · -- each is spanned by {lit}`k` of the basis vectors, so has dimension {lit}`k`
    intro j
    have hLI : LinearIndependent F (fun t : Fin k => w ((omitIndex j).succAbove t)) :=
      hw.1.comp _ Fin.succAbove_right_injective
    simpa using finrank_span_eq_card hLI
  · apply le_antisymm
    · -- a vector in every one of them has zero coefficient on each added vector
      intro x hx
      rw [Submodule.mem_iInf] at hx
      have hxtop : x ∈ Submodule.span F (Set.range w) := by
        rw [hw.2]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxtop
      obtain ⟨c, hc⟩ := hxtop
      have hzero : ∀ j : Fin (k + 1 - m), c (omitIndex j) = 0 := by
        intro j
        refine coeff_eq_zero_of_mem_span_succAbove w hw.1 (omitIndex j) c ?_
        rw [hc]
        exact hx j
      rw [← hc]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      by_cases hi : i.val < m
      · have hcast : Fin.castLE hmn ⟨i.val, hi⟩ = i := Fin.ext rfl
        have hwi : w i = (u ⟨i.val, hi⟩ : V) := by
          have hp := hprefix ⟨i.val, hi⟩
          rwa [hcast] at hp
        rw [hwi]
        exact Submodule.smul_mem _ _ (u ⟨i.val, hi⟩).property
      · have hj : i = omitIndex (⟨i.val - m, by have := i.isLt; omega⟩ :
            Fin (k + 1 - m)) := by
          apply Fin.ext
          show i.val = m + (i.val - m)
          omega
        rw [hj, hzero, zero_smul]
        exact Submodule.zero_mem _
    · -- {lit}`U` is spanned by the first {lit}`m` basis vectors, none of which is
      -- omitted
      intro y hy
      rw [Submodule.mem_iInf]
      intro j
      have hy' : (⟨y, hy⟩ : U) ∈ Submodule.span F (Set.range u) := by
        rw [hu.2]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hy'
      obtain ⟨a, ha⟩ := hy'
      have hyval : ∑ i, a i • (u i : V) = y := by
        have hval := congrArg Subtype.val ha
        rw [Submodule.coe_sum] at hval
        convert hval using 1
      rw [← hyval]
      refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
      rw [← hprefix i]
      have hne : Fin.castLE hmn i ≠ omitIndex j := by
        intro h
        have h1 : (Fin.castLE hmn i).val = m + j.val := congrArg Fin.val h
        rw [Fin.val_castLE] at h1
        have := i.isLt
        omega
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hne
      rw [← ht]
      exact Submodule.subset_span ⟨t, rfl⟩

/-- Two bases, appended, viewed inside {lit}`U ⊔ W`. -/
private def appendSup (U W : Submodule F V) {p q : ℕ} (u : Fin p → ↥U)
    (w : Fin q → ↥W) : Fin (p + q) → ↥(U ⊔ W) :=
  Fin.append (fun i => ⟨(u i : V), Submodule.mem_sup_left (u i).property⟩)
    (fun j => ⟨(w j : V), Submodule.mem_sup_right (w j).property⟩)

private lemma appendSup_left (U W : Submodule F V) {p q : ℕ} (u : Fin p → ↥U)
    (w : Fin q → ↥W) (i : Fin p) :
    ((appendSup U W u w (Fin.castAdd q i) : ↥(U ⊔ W)) : V) = (u i : V) := by
  rw [appendSup, Fin.append_left]

private lemma appendSup_right (U W : Submodule F V) {p q : ℕ} (u : Fin p → ↥U)
    (w : Fin q → ↥W) (j : Fin q) :
    ((appendSup U W u w (Fin.natAdd p j) : ↥(U ⊔ W)) : V) = (w j : V) := by
  rw [appendSup, Fin.append_right]

/-- The sum of two finite-dimensional subspaces is finite-dimensional, and
{lit}`dim (U ⊔ W) ≤ dim U + dim W`: bases of {lit}`U` and {lit}`W`, appended,
span {lit}`U ⊔ W`, and by 2.22 no linearly independent list is longer.

Note that 2.43 does not apply here: like the book, it assumes the *ambient*
space is finite-dimensional, whereas 2C.17 assumes only that each summand is —
proving that the sum is finite-dimensional is part of the exercise. -/
private lemma finite_sup_and_finrank_le (U W : Submodule F V)
    (hU : Finite F U) (hW : Finite F W) :
    Finite F ↥(U ⊔ W) ∧ finrank F ↥(U ⊔ W) ≤ finrank F U + finrank F W := by
  classical
  haveI := hU
  haveI := hW
  obtain ⟨p, u, hu⟩ := LADR.Section_2B.exists_basis (F := F) (V := ↥U)
  obtain ⟨q, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := ↥W)
  have hp : p = finrank F U := isBasis_card_eq_finrank u hu
  have hq : q = finrank F W := isBasis_card_eq_finrank w hw
  -- the appended list spans {lit}`U ⊔ W`
  have hz : Submodule.span F (Set.range (appendSup U W u w)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨t, ht⟩ -
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ht
    have hxspan : (⟨x, hx⟩ : ↥U) ∈ Submodule.span F (Set.range u) := by
      rw [hu.2]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hxspan
    obtain ⟨a, ha⟩ := hxspan
    have hyspan : (⟨y, hy⟩ : ↥W) ∈ Submodule.span F (Set.range w) := by
      rw [hw.2]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hyspan
    obtain ⟨b, hb⟩ := hyspan
    have hax : ∑ i, a i • (u i : V) = x := by
      have h := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at h
      convert h using 1
    have hby : ∑ j, b j • (w j : V) = y := by
      have h := congrArg Subtype.val hb
      rw [Submodule.coe_sum] at h
      convert h using 1
    have hL : (∑ i : Fin p, (Fin.append a b) (Fin.castAdd q i) •
        ((appendSup U W u w (Fin.castAdd q i) : ↥(U ⊔ W)) : V)) = x := by
      rw [← hax]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.append_left, appendSup_left]
    have hR : (∑ j : Fin q, (Fin.append a b) (Fin.natAdd p j) •
        ((appendSup U W u w (Fin.natAdd p j) : ↥(U ⊔ W)) : V)) = y := by
      rw [← hby]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.append_right, appendSup_right]
    have hsum : (⟨t, ht⟩ : ↥(U ⊔ W)) = ∑ k, (Fin.append a b) k • appendSup U W u w k := by
      apply Subtype.ext
      show t = ((∑ k, (Fin.append a b) k • appendSup U W u w k : ↥(U ⊔ W)) : V)
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul_of_tower]
      rw [Fin.sum_univ_add, hL, hR, hxy]
    rw [hsum]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  -- a finite spanning list makes {lit}`U ⊔ W` finite-dimensional
  have hfin : Finite F ↥(U ⊔ W) :=
    ⟨⟨Finset.image (appendSup U W u w) Finset.univ, by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hz⟩⟩
  refine ⟨hfin, ?_⟩
  haveI := hfin
  obtain ⟨r, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := ↥(U ⊔ W))
  have hr : r = finrank F ↥(U ⊔ W) := isBasis_card_eq_finrank v hv
  have hle : r ≤ p + q :=
    LADR.Section_2A.linearIndependent_le_spanning v (appendSup U W u w) hv.1 hz
  omega

/-- Peeling off the first subspace of a finite family. -/
private lemma iSup_fin_succ {m : ℕ} (W : Fin (m + 1) → Submodule F V) :
    (⨆ i, W i) = W 0 ⊔ ⨆ j : Fin m, W j.succ := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    induction i using Fin.cases with
    | zero => exact le_sup_left
    | succ j => exact (le_iSup (fun j : Fin m => W j.succ) j).trans le_sup_right
  · exact sup_le (le_iSup W 0) (iSup_le fun j => le_iSup W j.succ)

private lemma finite_iSup_and_finrank_le : ∀ (m : ℕ) (W : Fin m → Submodule F V),
    (∀ i, Finite F (W i)) →
      Finite F ↥(⨆ i, W i) ∧ finrank F ↥(⨆ i, W i) ≤ ∑ i, finrank F (W i) := by
  intro m
  induction m with
  | zero =>
    intro W _
    rw [iSup_of_empty W]
    have hbot : ∀ z : ↥(⊥ : Submodule F V), z = 0 := fun z =>
      Subtype.ext ((Submodule.mem_bot F).mp z.property)
    refine ⟨⟨⟨∅, ?_⟩⟩, by simp⟩
    rw [eq_top_iff]
    intro z _
    rw [hbot z]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro W hW
    obtain ⟨hfin_tail, hle_tail⟩ := ih (fun j => W j.succ) fun j => hW j.succ
    rw [iSup_fin_succ W]
    obtain ⟨hfin, hle⟩ :=
      finite_sup_and_finrank_le (W 0) (⨆ j : Fin n, W j.succ) (hW 0) hfin_tail
    refine ⟨hfin, ?_⟩
    rw [Fin.sum_univ_succ]
    omega

/-- 2C.17 -/
-- we showed V + W is finite if they are, so repeat by induction.
-- dim (V + W) ≤ dim V + dim W, so repeat by induction too
theorem exercise_2C_17 {m : ℕ} (W : Fin m → Submodule F V)
    (hW : ∀ i, Finite F (W i)) :
    Finite F ↥(⨆ i, W i) ∧
      finrank F ↥(⨆ i, W i) ≤ ∑ i, finrank F (W i) :=
  finite_iSup_and_finrank_le m W hW

/-- 2C.18 -/
-- take a basis and set W i as span {b i}: each has dimension 1, the sum is
-- everything since the spans cover the basis, and the direct-sum property is
-- uniqueness of coordinates in a basis.
theorem exercise_2C_18 [Finite F V] (_hV : 1 ≤ finrank F V) :
    ∃ (W : Fin (finrank F V) → Submodule F V),
      (∀ i, finrank F (W i) = 1) ∧ IsDirectSum W ∧ ⨆ i, W i = ⊤ := by
  classical
  obtain ⟨n, b, hb⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
  have hn : n = finrank F V := isBasis_card_eq_finrank b hb
  subst hn
  refine ⟨fun i => F ∙ b i, fun i => finrank_span_singleton (hb.1.ne_zero i), ?_, ?_⟩
  · intro x y hxy
    choose c hc using fun i => Submodule.mem_span_singleton.mp (x i).property
    choose d hd using fun i => Submodule.mem_span_singleton.mp (y i).property
    have hzero : ∑ i, (c i - d i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [Finset.sum_congr rfl fun i _ => hc i, Finset.sum_congr rfl fun i _ => hd i,
        hxy, sub_self]
    have hcd := Fintype.linearIndependent_iff.mp hb.1 _ hzero
    funext i
    exact Subtype.ext (by rw [← hc i, ← hd i, sub_eq_zero.mp (hcd i)])
  · refine le_antisymm le_top ?_
    rw [← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_span_singleton_self _)

/-- Two vectors admitting no nontrivial vanishing combination span lines meeting
only in {lit}`0`. -/
private lemma span_inf_span_eq_bot {a b : V}
    (h : ∀ s t : F, s • a + t • b = 0 → s = 0 ∧ t = 0) :
    (F ∙ a) ⊓ (F ∙ b) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hx.1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx.2
  have hcomb : s • a + (-t) • b = 0 := by rw [neg_smul, hs, ht]; abel
  rw [Submodule.mem_bot, ← hs, (h s (-t) hcomb).1, zero_smul]

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
  apply isFalse
  -- in K², take V1 = span {(1,0)}, V2 = span {(0,1)}, V3 = span {(1,1)}:
  -- dim(V1 + V2 + V3) = 2 but the right-hand side is 1 + 1 + 1 = 3
  intro h
  have hne1 : (![1, 0] : Fin 2 → K) ≠ 0 := by
    intro hz; have h0 := congrFun hz 0; simp at h0
  have hne2 : (![0, 1] : Fin 2 → K) ≠ 0 := by
    intro hz; have h1 := congrFun hz 1; simp at h1
  have hne3 : (![1, 1] : Fin 2 → K) ≠ 0 := by
    intro hz; have h0 := congrFun hz 0; simp at h0
  have h12 : (K ∙ (![1, 0] : Fin 2 → K)) ⊓ (K ∙ (![0, 1] : Fin 2 → K)) = ⊥ := by
    refine span_inf_span_eq_bot fun s t hst => ?_
    have h0 := congrFun hst 0
    have h1 := congrFun hst 1
    simp at h0 h1
    exact ⟨h0, h1⟩
  have h13 : (K ∙ (![1, 0] : Fin 2 → K)) ⊓ (K ∙ (![1, 1] : Fin 2 → K)) = ⊥ := by
    refine span_inf_span_eq_bot fun s t hst => ?_
    have h0 := congrFun hst 0
    have h1 := congrFun hst 1
    simp at h0 h1
    exact ⟨by linear_combination h0 - h1, h1⟩
  have h23 : (K ∙ (![0, 1] : Fin 2 → K)) ⊓ (K ∙ (![1, 1] : Fin 2 → K)) = ⊥ := by
    refine span_inf_span_eq_bot fun s t hst => ?_
    have h0 := congrFun hst 0
    have h1 := congrFun hst 1
    simp at h0 h1
    exact ⟨by linear_combination h1 - h0, h0⟩
  have hsup : (K ∙ (![1, 0] : Fin 2 → K)) ⊔ (K ∙ (![0, 1] : Fin 2 → K)) = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    have hx : x = x 0 • ![1, 0] + x 1 • ![0, 1] := by
      funext j; fin_cases j <;> simp
    rw [hx]
    exact Submodule.add_mem_sup (Submodule.mem_span_singleton.mpr ⟨x 0, rfl⟩)
      (Submodule.mem_span_singleton.mpr ⟨x 1, rfl⟩)
  have hdimsup : finrank K ↥((K ∙ (![1, 0] : Fin 2 → K)) ⊔ (K ∙ (![0, 1] : Fin 2 → K))
      ⊔ (K ∙ (![1, 1] : Fin 2 → K))) = 2 := by
    rw [hsup, top_sup_eq, finrank_top]
    simp
  have hEq := h (Fin 2 → K) (K ∙ ![1, 0]) (K ∙ ![0, 1]) (K ∙ ![1, 1])
  rw [hdimsup, finrank_span_singleton hne1, finrank_span_singleton hne2,
    finrank_span_singleton hne3, h12, h13, h23, bot_inf_eq] at hEq
  simp at hEq

/-- 2C.20 The {lit}`/3` makes this a rational identity in general; we encode it by
clearing the denominator, i.e. multiplying both sides by 3 so we can stay in ℕ. -/
theorem exercise_2C_20 :
    ∀ (V₁ V₂ V₃ : Submodule F V) [Finite F V],
      3 * finrank F ↥(V₁ ⊔ V₂ ⊔ V₃) =
      3 * (finrank F V₁ + finrank F V₂ + finrank F V₃)
        - (finrank F ↥(V₁ ⊓ V₂) + finrank F ↥(V₁ ⊓ V₃) + finrank F ↥(V₂ ⊓ V₃))
        - (finrank F ↥((V₁ ⊔ V₂) ⊓ V₃) + finrank F ↥((V₁ ⊔ V₃) ⊓ V₂)
          + finrank F ↥((V₂ ⊔ V₃) ⊓ V₁)) := by
  -- use the formula above
  -- dim (V1 + V2) = dim V1 + dim V2 - dim (V1 ∩ V2)
  -- dim (V1 + V2 + V3) = dim (V1 + V2) + dim V3 - dim ((V1 + V2) ∩ V3)
  -- so this three times for different permutation of V1, V2, V3 and add them up
  intro V₁ V₂ V₃ _
  have e12 := finrank_sup_add_finrank_inf_eq V₁ V₂
  have e13 := finrank_sup_add_finrank_inf_eq V₁ V₃
  have e23 := finrank_sup_add_finrank_inf_eq V₂ V₃
  have f3 := finrank_sup_add_finrank_inf_eq (V₁ ⊔ V₂) V₃
  have f2 := finrank_sup_add_finrank_inf_eq (V₁ ⊔ V₃) V₂
  have f1 := finrank_sup_add_finrank_inf_eq (V₂ ⊔ V₃) V₁
  -- the three outer sums are the same subspace
  have h2 : (V₁ ⊔ V₃) ⊔ V₂ = V₁ ⊔ V₂ ⊔ V₃ := by
    simp [sup_comm, sup_left_comm]
  have h1 : (V₂ ⊔ V₃) ⊔ V₁ = V₁ ⊔ V₂ ⊔ V₃ := by
    simp [sup_comm, sup_left_comm]
  rw [h2] at f2
  rw [h1] at f1
  omega

end LADR.Section_2C
