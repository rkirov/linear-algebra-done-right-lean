import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import LinearAlgebraDoneRightLean.Section_7C
import LinearAlgebraDoneRightLean.Section_7D
import LinearAlgebraDoneRightLean.Section_7E
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7F: Consequences of Singular Value Decomposition

This section develops three families of consequences of the singular value
decomposition (Section 7E):

* the *norm of a linear map* and its basic properties (7.86–7.91);
* the *polar decomposition* (7.93), the flagship algebraic result: every operator
  factors as an isometry composed with the positive square root of {lit}`T* T`;
* the geometry of *ellipsoids*, *parallelepipeds*, *boxes*, and *volume* (7.95–7.111).

The norm and polar-decomposition results are proved in full, as is the headline
volume theorem 7.111 (proved measure-theoretically in 9C). Only Axler's
deliberately informal box/volume *definitions* 7.108–7.110 and a few set-geometry
image results remain in prose with reasons, as flagged below.
-/

namespace LADR.Section_7F

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate Matrix
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)
open LADR.Section_7C LADR.Section_7D LADR.Section_7E

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! # Norms of Linear Maps -/

/-! 7.86 Definition: norm of a linear map, ‖·‖

Axler defines the *norm* of {lit}`T ∈ ℒ(V, W)` to be
{lit}`‖T‖ = max{‖T v‖ : v ∈ V and ‖v‖ ≤ 1}` (the maximum exists by 7.85, which
identifies it with the largest singular value).

In a finite-dimensional inner product space every linear map is continuous, so we
define {lit}`opNorm T` as the operator norm of the associated continuous linear
map {lit}`T.toContinuousLinearMap`. Mathlib's operator norm is *exactly* the
supremum of {lit}`‖T v‖` over the closed unit ball
({name}`ContinuousLinearMap.sSup_unitClosedBall_eq_norm`), so this coincides with
Axler's definition; see {lit}`opNorm_eq_sSup_closedBall` below. -/
noncomputable def opNorm (T : V →ₗ[𝕜] W) : ℝ := ‖LinearMap.toContinuousLinearMap T‖

omit [FiniteDimensional 𝕜 W] in
/-- {lit}`opNorm T` equals the supremum of {lit}`‖T v‖` over the closed unit ball
{lit}`{v : ‖v‖ ≤ 1}`, which is Axler's definition 7.86 (the maximum in 7.85). -/
theorem opNorm_eq_sSup_closedBall (T : V →ₗ[𝕜] W) :
    opNorm T = sSup ((fun v => ‖T v‖) '' Metric.closedBall (0 : V) 1) := by
  rw [opNorm, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm (LinearMap.toContinuousLinearMap T)]
  simp

/-! 7.82 For {lit}`T ∈ ℒ(V, W)` and {lit}`v ∈ V`, {lit}`‖Tv‖ ≤ s₁‖v‖` with
{lit}`s₁` the largest singular value. Proved below as
{lit}`norm_apply_le_iSup_singularValues`, once the norm and its
singular-value characterization (7.88(a)/7.89) are available. -/

/-! 7.85 The maximum in 7.86 equals the largest singular value; the "≥ each singular
value" half is {lit}`singularValues_le_opNorm` below and the reverse bound is
7.88(a), proved below as {lit}`opNorm_eq_iSup_singularValues`. -/

omit [FiniteDimensional 𝕜 W] in
/-- 7.89 The fundamental inequality {lit}`‖T v‖ ≤ ‖T‖ ‖v‖`. -/
theorem opNorm_apply_le (T : V →ₗ[𝕜] W) (v : V) : ‖T v‖ ≤ opNorm T * ‖v‖ := by
  have := (LinearMap.toContinuousLinearMap T).le_opNorm v
  simpa [opNorm] using this

omit [FiniteDimensional 𝕜 W] in
/-- 7.87(a) {lit}`‖T‖ ≥ 0`. -/
theorem opNorm_nonneg (T : V →ₗ[𝕜] W) : 0 ≤ opNorm T := norm_nonneg _

omit [FiniteDimensional 𝕜 W] in
/-- 7.87(b) {lit}`‖T‖ = 0 ⟺ T = 0`. -/
theorem opNorm_eq_zero {T : V →ₗ[𝕜] W} : opNorm T = 0 ↔ T = 0 := by
  rw [opNorm, norm_eq_zero]
  constructor
  · intro h; ext v
    have : (LinearMap.toContinuousLinearMap T) v = 0 := by rw [h]; rfl
    simpa using this
  · intro h; rw [h]; exact map_zero _

omit [FiniteDimensional 𝕜 W] in
/-- 7.87(c) {lit}`‖λ T‖ = ‖λ‖ ‖T‖` (Axler's {lit}`|λ|` is {lit}`‖λ‖` for the
scalar field). -/
theorem opNorm_smul (c : 𝕜) (T : V →ₗ[𝕜] W) : opNorm (c • T) = ‖c‖ * opNorm T := by
  rw [opNorm, opNorm, map_smul, norm_smul]

omit [FiniteDimensional 𝕜 W] in
/-- 7.87(d) Triangle inequality {lit}`‖S + T‖ ≤ ‖S‖ + ‖T‖`. -/
theorem opNorm_add_le (S T : V →ₗ[𝕜] W) : opNorm (S + T) ≤ opNorm S + opNorm T := by
  rw [opNorm, opNorm, opNorm, map_add]; exact norm_add_le _ _

omit [FiniteDimensional 𝕜 W] in
/-- 7.88(c) {lit}`‖T‖` is the smallest {lit}`c ≥ 0` with {lit}`‖T v‖ ≤ c ‖v‖` for
all {lit}`v`: for {lit}`0 ≤ c`, {lit}`‖T‖ ≤ c ⟺ ∀ v, ‖T v‖ ≤ c ‖v‖`. -/
theorem opNorm_le_iff {T : V →ₗ[𝕜] W} {c : ℝ} (hc : 0 ≤ c) :
    opNorm T ≤ c ↔ ∀ v, ‖T v‖ ≤ c * ‖v‖ := by
  rw [opNorm, ContinuousLinearMap.opNorm_le_iff hc]; simp

/-- Each singular value is at most the norm; this is the easy half of 7.88(a)/7.85
({lit}`‖T eₖ‖ = sₖ` and {lit}`‖eₖ‖ = 1`). -/
theorem singularValues_le_opNorm (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) :
    singularValues T i ≤ opNorm T := by
  have h := opNorm_apply_le T (svdBasis T i)
  rw [norm_image_svdBasis, (svdBasis T).orthonormal.1 i, mul_one] at h
  exact h

/-- 7.88(a) / 7.85: the operator norm {lit}`‖T‖` equals the supremum of the
singular values of {lit}`T` (a supremum, so the {lit}`V = 0` case is handled).

Following Axler: the easy bound {lit}`singularValues_le_opNorm` gives one
inequality; for the reverse, expand {lit}`‖T v‖²` as {lit}`⟨v, T* T v⟩` and use
the eigenbasis of {lit}`T* T` together with Parseval to bound it by
{lit}`(sup s)² ‖v‖²`, then take square roots. -/
theorem opNorm_eq_iSup_singularValues (T : V →ₗ[𝕜] W) :
    opNorm T = ⨆ i, singularValues T i := by
  have hop_nn : 0 ≤ opNorm T := by rw [opNorm]; exact norm_nonneg _
  have hbdd : BddAbove (Set.range (singularValues T)) := (Set.finite_range _).bddAbove
  have hsup_nn : 0 ≤ ⨆ i, singularValues T i := Real.iSup_nonneg (singularValues_nonneg T)
  refine le_antisymm ?_ (Real.iSup_le (singularValues_le_opNorm T) hop_nn)
  rw [opNorm_le_iff hsup_nn]
  intro v
  set e := svdBasis T with he
  set M := ⨆ i, singularValues T i with hM
  have hsym := (adjComp_self_isPositive T).isSymmetric
  have hTvadj : ⟪T v, T v⟫_𝕜 = ⟪v, (LinearMap.adjoint T ∘ₗ T) v⟫_𝕜 :=
    (LinearMap.adjoint_inner_right T v (T v)).symm
  have hq : ⟪v, (LinearMap.adjoint T ∘ₗ T) v⟫_𝕜
      = ∑ i, (((singularValues T i) ^ 2 : ℝ) : 𝕜) * ((‖⟪e i, v⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← e.sum_inner_mul_inner v ((LinearMap.adjoint T ∘ₗ T) v)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h1 : ⟪e i, (LinearMap.adjoint T ∘ₗ T) v⟫_𝕜
        = (((singularValues T i) ^ 2 : ℝ) : 𝕜) * ⟪e i, v⟫_𝕜 := by
      rw [← hsym (e i) v, adjComp_apply_svdBasis, inner_smul_left, RCLike.conj_ofReal]
    rw [h1]
    have h2 : ⟪v, e i⟫_𝕜 * ⟪e i, v⟫_𝕜 = ((‖⟪e i, v⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
      rw [← inner_conj_symm v (e i), RCLike.conj_mul, ← RCLike.ofReal_pow]
    calc ⟪v, e i⟫_𝕜 * ((((singularValues T i) ^ 2 : ℝ) : 𝕜) * ⟪e i, v⟫_𝕜)
        = (((singularValues T i) ^ 2 : ℝ) : 𝕜) * (⟪v, e i⟫_𝕜 * ⟪e i, v⟫_𝕜) := by ring
      _ = (((singularValues T i) ^ 2 : ℝ) : 𝕜) * ((‖⟪e i, v⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by rw [h2]
  have hnormsq : ‖T v‖ ^ 2 = ∑ i, (singularValues T i) ^ 2 * ‖⟪e i, v⟫_𝕜‖ ^ 2 := by
    have hcast : ((‖T v‖ ^ 2 : ℝ) : 𝕜)
        = ((∑ i, (singularValues T i) ^ 2 * ‖⟪e i, v⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
      rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K, hTvadj, hq]; push_cast; ring
    exact_mod_cast hcast
  have hbound : ∑ i, (singularValues T i) ^ 2 * ‖⟪e i, v⟫_𝕜‖ ^ 2 ≤ M ^ 2 * ‖v‖ ^ 2 := by
    rw [← e.sum_sq_norm_inner_right v, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (singularValues_nonneg T i) (le_ciSup hbdd i) 2) (sq_nonneg _)
  have hsq : ‖T v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by rw [hnormsq, mul_pow]; exact hbound
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (mul_nonneg hsup_nn (norm_nonneg _))] at h1

/-- 7.82 For {lit}`T ∈ ℒ(V, W)` and {lit}`v ∈ V`, {lit}`‖T v‖ ≤ s₁ ‖v‖`, where
{lit}`s₁ = ⨆ᵢ sᵢ` is the largest singular value. Immediate from the fundamental
inequality 7.89 ({lit}`opNorm_apply_le`) and the identification of the norm with
the largest singular value 7.88(a) ({lit}`opNorm_eq_iSup_singularValues`). -/
theorem norm_apply_le_iSup_singularValues (T : V →ₗ[𝕜] W) (v : V) :
    ‖T v‖ ≤ (⨆ i, singularValues T i) * ‖v‖ := by
  rw [← opNorm_eq_iSup_singularValues]; exact opNorm_apply_le T v

omit [FiniteDimensional 𝕜 W] in
/-- 7.88(b) {lit}`‖T‖ = max{‖T v‖ : ‖v‖ = 1}`: the norm is the supremum of
{lit}`‖T v‖` over the *unit sphere*, the restriction of 7.86 from the closed unit
ball. This is mathlib's {name}`ContinuousLinearMap.sSup_sphere_eq_norm`. -/
theorem opNorm_eq_sSup_sphere (T : V →ₗ[𝕜] W) :
    opNorm T = sSup ((fun v => ‖T v‖) '' Metric.sphere (0 : V) 1) := by
  rw [opNorm, ← ContinuousLinearMap.sSup_sphere_eq_norm (LinearMap.toContinuousLinearMap T)]
  simp

/-! 7.90 Example: norms

We record the first bullet, {lit}`‖I‖ = 1` (for {lit}`V ≠ 0`). The remaining
bullets (the all-ones matrix on {lit}`𝔽ⁿ`, the eigenvalue-maximum formula, and the
{lit}`5×5` numerical example) are concrete computations illustrating 7.88 and are
omitted from formalization, matching the treatment of numeric examples in
Section 7E. -/

/-- 7.90 (first bullet) The identity operator has norm {lit}`1` (when {lit}`V ≠ 0`). -/
theorem opNorm_id [Nontrivial V] : opNorm (LinearMap.id : V →ₗ[𝕜] V) = 1 := by
  rw [opNorm]
  have h : LinearMap.toContinuousLinearMap (LinearMap.id : V →ₗ[𝕜] V)
      = ContinuousLinearMap.id 𝕜 V := by
    ext v; simp
  rw [h, ContinuousLinearMap.norm_id]

/-- 7.91 A linear map and its adjoint have the same norm: {lit}`‖T*‖ = ‖T‖`. -/
theorem opNorm_adjoint (T : V →ₗ[𝕜] W) : opNorm (LinearMap.adjoint T) = opNorm T := by
  haveI := FiniteDimensional.complete 𝕜 V
  haveI := FiniteDimensional.complete 𝕜 W
  rw [opNorm, opNorm, LinearMap.adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _

/-! # 7.92 Best approximation by a linear map whose range has dimension {lit}`≤ k` -/

omit [FiniteDimensional 𝕜 V] in
/-- Pythagoras for an orthonormal family: {lit}`‖∑ aᵢ gᵢ‖² = ∑ ‖aᵢ‖²`. -/
theorem norm_sum_smul_sq {ι : Type*} [Fintype ι] {g : ι → V} (hg : Orthonormal 𝕜 g)
    (a : ι → 𝕜) : ‖∑ i, a i • g i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  rw [← @inner_self_eq_norm_sq 𝕜, hg.inner_sum a a, map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

omit [FiniteDimensional 𝕜 V] in
/-- Pythagoras when the family is orthonormal on {lit}`{i // p i}` and the coefficients
vanish off it. -/
theorem norm_sum_smul_sq_subtype {ι : Type*} [Fintype ι] {g : ι → V} {p : ι → Prop}
    [DecidablePred p] (hg : Orthonormal 𝕜 (fun i : {i // p i} => g i.1)) {a : ι → 𝕜}
    (ha : ∀ i, ¬ p i → a i = 0) : ‖∑ i, a i • g i‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
  have e1 : (∑ i, a i • g i) = ∑ i : {i // p i}, a i.1 • g i.1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter p) (fun x => by simp) (fun i => a i • g i)]
    exact (Finset.sum_filter_of_ne fun i _ h => by
      by_contra hp; exact h (by rw [ha i hp, zero_smul])).symm
  have e2 : (∑ i, ‖a i‖ ^ 2) = ∑ i : {i // p i}, ‖a i.1‖ ^ 2 := by
    rw [← Finset.sum_subtype (Finset.univ.filter p) (fun x => by simp) (fun i => ‖a i‖ ^ 2)]
    exact (Finset.sum_filter_of_ne fun i _ h => by
      by_contra hp; exact h (by simp [ha i hp])).symm
  rw [e1, e2]; exact norm_sum_smul_sq hg _

/-- The permutation sorting the singular values of {lit}`T` into decreasing order. -/
noncomputable def svSortPerm (T : V →ₗ[𝕜] V) : Equiv.Perm (Fin (finrank 𝕜 V)) :=
  Tuple.sort (fun i => -(singularValues T i))

theorem singularValues_svSortPerm_antitone (T : V →ₗ[𝕜] V) {j k : Fin (finrank 𝕜 V)}
    (hjk : j ≤ k) : singularValues T (svSortPerm T k) ≤ singularValues T (svSortPerm T j) := by
  have h := Tuple.monotone_sort (fun i => -(singularValues T i)) hjk
  simpa only [Function.comp_apply, neg_le_neg_iff] using h

theorem svd_apply_sorted (T : V →ₗ[𝕜] V) (v : V) :
    T v = ∑ j, ((singularValues T (svSortPerm T j) : 𝕜) * ⟪svdBasis T (svSortPerm T j), v⟫_𝕜) •
      svdImage T (svSortPerm T j) := by
  rw [svd_apply T v]
  refine Fintype.sum_equiv (svSortPerm T).symm _ _ (fun i => ?_)
  simp only [Equiv.apply_symm_apply]
  rw [smul_smul]

/-- The truncated SVD keeping the top {lit}`k` singular directions. -/
noncomputable def truncSVD (T : V →ₗ[𝕜] V) (k : ℕ) : V →ₗ[𝕜] V :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (finrank 𝕜 V) => (j : ℕ) < k),
    (singularValues T (svSortPerm T j) : 𝕜) •
      LinearMap.smulRight (innerₛₗ 𝕜 (svdBasis T (svSortPerm T j)))
        (svdImage T (svSortPerm T j))

theorem truncSVD_apply (T : V →ₗ[𝕜] V) (k : ℕ) (v : V) :
    truncSVD T k v = ∑ j ∈ Finset.univ.filter (fun j : Fin (finrank 𝕜 V) => (j : ℕ) < k),
      ((singularValues T (svSortPerm T j) : 𝕜) * ⟪svdBasis T (svSortPerm T j), v⟫_𝕜) •
        svdImage T (svSortPerm T j) := by
  rw [truncSVD, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smulRight_apply, innerₛₗ_apply_apply, smul_smul]

theorem finrank_range_truncSVD_le (T : V →ₗ[𝕜] V) (k : ℕ) :
    finrank 𝕜 (LinearMap.range (truncSVD T k)) ≤ k := by
  classical
  have hsub : LinearMap.range (truncSVD T k) ≤
      Submodule.span 𝕜 ↑((Finset.univ.filter (fun j : Fin (finrank 𝕜 V) => (j : ℕ) < k)).image
        (fun j => svdImage T (svSortPerm T j))) := by
    rintro _ ⟨v, rfl⟩
    rw [truncSVD, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun j hj => ?_
    rw [LinearMap.smul_apply, LinearMap.smulRight_apply]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span (Finset.mem_coe.mpr
      (Finset.mem_image_of_mem (fun j => svdImage T (svSortPerm T j)) hj))
  refine le_trans (le_trans (Submodule.finrank_mono hsub) (finrank_span_finset_le_card _))
    (le_trans Finset.card_image_le ?_)
  have h := Finset.card_le_card_of_injOn
    (s := Finset.univ.filter (fun j : Fin (finrank 𝕜 V) => (j : ℕ) < k))
    (t := Finset.range k) Fin.val
    (fun j hj => by
      simp only [Finset.mem_coe, Finset.mem_filter] at hj
      exact Finset.mem_range.mpr hj.2)
    Fin.val_injective.injOn
  rwa [Finset.card_range] at h

/-- The image vectors reindexed by the sort, orthonormal on positive singular values. -/
theorem svdImage_sorted_orthonormal (T : V →ₗ[𝕜] V) :
    Orthonormal 𝕜 (fun j : {j : Fin (finrank 𝕜 V) // singularValues T (svSortPerm T j) ≠ 0} =>
      svdImage T (svSortPerm T j.1)) :=
  (svdImage_orthonormal T).comp (fun j => ⟨svSortPerm T j.1, j.2⟩)
    (fun _ _ h => Subtype.ext ((svSortPerm T).injective (congrArg Subtype.val h)))

/-- Parseval in the sorted eigenbasis: {lit}`∑ⱼ ‖⟨eⱼ,v⟩‖² = ‖v‖²`. -/
theorem sum_sq_norm_inner_sorted (T : V →ₗ[𝕜] V) (v : V) :
    ∑ j, ‖⟪svdBasis T (svSortPerm T j), v⟫_𝕜‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [Equiv.sum_comp (svSortPerm T) (fun i => ‖⟪svdBasis T i, v⟫_𝕜‖ ^ 2)]
  exact (svdBasis T).sum_sq_norm_inner_right v

/-- The squared norm of a partial SVD sum: {lit}`‖∑ⱼ [P j] sⱼ⟨eⱼ,v⟩ fⱼ‖² = ∑ⱼ [P j] sⱼ²‖⟨eⱼ,v⟩‖²`. -/
theorem partialSVD_normSq (T : V →ₗ[𝕜] V) (v : V) (P : Fin (finrank 𝕜 V) → Prop)
    [DecidablePred P] :
    ‖∑ j, (if P j then (singularValues T (svSortPerm T j) : 𝕜) *
        ⟪svdBasis T (svSortPerm T j), v⟫_𝕜 else 0) • svdImage T (svSortPerm T j)‖ ^ 2
      = ∑ j, if P j then (singularValues T (svSortPerm T j)) ^ 2 *
          ‖⟪svdBasis T (svSortPerm T j), v⟫_𝕜‖ ^ 2 else 0 := by
  rw [norm_sum_smul_sq_subtype (svdImage_sorted_orthonormal T)
    (a := fun j => if P j then (singularValues T (svSortPerm T j) : 𝕜) *
      ⟪svdBasis T (svSortPerm T j), v⟫_𝕜 else 0)
    (fun j hj => by simp only [ne_eq, not_not] at hj; simp [hj])]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hP
  · rw [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  · simp

/-- The operator-norm upper bound from a pointwise bound. -/
theorem opNorm_le_of_forall {T : V →ₗ[𝕜] V} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, ‖T v‖ ≤ c * ‖v‖) : opNorm T ≤ c := by
  rw [opNorm]; exact ContinuousLinearMap.opNorm_le_bound _ hc h

/-- `(T − Tₖ) v = ∑ⱼ [k ≤ j] sⱼ ⟨eⱼ,v⟩ fⱼ` (the tail of the SVD). -/
theorem sub_truncSVD_apply (T : V →ₗ[𝕜] V) (k : ℕ) (v : V) :
    (T - truncSVD T k) v = ∑ j : Fin (finrank 𝕜 V),
      (if k ≤ (j : ℕ) then (singularValues T (svSortPerm T j) : 𝕜) *
        ⟪svdBasis T (svSortPerm T j), v⟫_𝕜 else 0) • svdImage T (svSortPerm T j) := by
  rw [LinearMap.sub_apply, svd_apply_sorted, truncSVD_apply, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) < k
  · rw [if_pos h, if_neg (not_le.mpr h), sub_self, zero_smul]
  · rw [if_neg h, if_pos (not_lt.mp h), sub_zero]

/-- `‖T v‖² = ∑ⱼ sⱼ² ‖⟨eⱼ,v⟩‖²`. -/
theorem normSq_apply (T : V →ₗ[𝕜] V) (v : V) :
    ‖T v‖ ^ 2 = ∑ j, (singularValues T (svSortPerm T j)) ^ 2 *
      ‖⟪svdBasis T (svSortPerm T j), v⟫_𝕜‖ ^ 2 := by
  rw [svd_apply_sorted, norm_sum_smul_sq_subtype (svdImage_sorted_orthonormal T)
    (a := fun j => (singularValues T (svSortPerm T j) : 𝕜) * ⟪svdBasis T (svSortPerm T j), v⟫_𝕜)
    (fun j hj => by simp only [ne_eq, not_not] at hj; simp [hj])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

/-- Upper bound: `opNorm (T − truncSVD T k) ≤ s'_k`. -/
theorem opNorm_sub_truncSVD_le (T : V →ₗ[𝕜] V) {k : ℕ} (hk : k < finrank 𝕜 V) :
    opNorm (T - truncSVD T k) ≤ singularValues T (svSortPerm T ⟨k, hk⟩) := by
  classical
  refine opNorm_le_of_forall (singularValues_nonneg T _) fun v => ?_
  have key : ‖(T - truncSVD T k) v‖ ^ 2
      ≤ (singularValues T (svSortPerm T ⟨k, hk⟩)) ^ 2 * ‖v‖ ^ 2 := by
    rw [sub_truncSVD_apply, partialSVD_normSq]
    calc ∑ j : Fin (finrank 𝕜 V), (if k ≤ (j : ℕ) then (singularValues T (svSortPerm T j)) ^ 2 *
            ‖⟪svdBasis T (svSortPerm T j), v⟫_𝕜‖ ^ 2 else 0)
        ≤ ∑ j, (singularValues T (svSortPerm T ⟨k, hk⟩)) ^ 2 *
            ‖⟪svdBasis T (svSortPerm T j), v⟫_𝕜‖ ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          split_ifs with h
          · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            nlinarith [singularValues_nonneg T (svSortPerm T j),
              singularValues_nonneg T (svSortPerm T ⟨k, hk⟩),
              singularValues_svSortPerm_antitone T
                (show (⟨k, hk⟩ : Fin (finrank 𝕜 V)) ≤ j from h)]
          · positivity
      _ = (singularValues T (svSortPerm T ⟨k, hk⟩)) ^ 2 *
            ∑ j, ‖⟪svdBasis T (svSortPerm T j), v⟫_𝕜‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = (singularValues T (svSortPerm T ⟨k, hk⟩)) ^ 2 * ‖v‖ ^ 2 := by
          rw [sum_sq_norm_inner_sorted]
  have hb := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (singularValues_nonneg T _), Real.sqrt_sq (norm_nonneg _)] at hb

/-- Lower bound (achieved): `s'_k ≤ opNorm (T − truncSVD T k)`, witnessed by {lit}`eₖ`. -/
theorem le_opNorm_sub_truncSVD (T : V →ₗ[𝕜] V) {k : ℕ} (hk : k < finrank 𝕜 V) :
    singularValues T (svSortPerm T ⟨k, hk⟩) ≤ opNorm (T - truncSVD T k) := by
  classical
  have hnorm : ‖(T - truncSVD T k) (svdBasis T (svSortPerm T ⟨k, hk⟩))‖
      = singularValues T (svSortPerm T ⟨k, hk⟩) := by
    rw [sub_truncSVD_apply, Finset.sum_eq_single (⟨k, hk⟩ : Fin (finrank 𝕜 V))]
    · rw [if_pos (le_refl k), orthonormal_iff_ite.mp (svdBasis T).orthonormal, if_pos rfl,
        mul_one, ← svdBasis_image_eq, norm_image_svdBasis]
    · intro j _ hj
      rw [orthonormal_iff_ite.mp (svdBasis T).orthonormal,
        if_neg (fun hh => hj ((svSortPerm T).injective hh)), mul_zero, ite_self, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have happ := opNorm_apply_le (T - truncSVD T k) (svdBasis T (svSortPerm T ⟨k, hk⟩))
  rw [hnorm, (svdBasis T).orthonormal.1 (svSortPerm T ⟨k, hk⟩), mul_one] at happ
  exact happ

/-- Lower bound: any {lit}`S` with {lit}`dim range S ≤ k` has `opNorm (T − S) ≥ s'_k`. On the
{lit}`(k+1)`-dimensional span {lit}`W` of the top eigen-directions, {lit}`ker S ⊓ W ≠ ⊥` (dimensions),
so a nonzero {lit}`v` there has `(T − S) v = T v` with {lit}`‖T v‖ ≥ s'_k ‖v‖`. -/
theorem le_opNorm_sub_of_rank_le (T : V →ₗ[𝕜] V) {k : ℕ} (hk : k < finrank 𝕜 V)
    (S : V →ₗ[𝕜] V) (hrank : finrank 𝕜 (LinearMap.range S) ≤ k) :
    singularValues T (svSortPerm T ⟨k, hk⟩) ≤ opNorm (T - S) := by
  classical
  have hle : k + 1 ≤ finrank 𝕜 V := hk
  set family := fun i : Fin (k + 1) => svdBasis T (svSortPerm T (Fin.castLE hle i)) with hfam
  set W := Submodule.span 𝕜 (Set.range family) with hWdef
  have hWdim : finrank 𝕜 W = k + 1 := by
    have hli : LinearIndependent 𝕜 family :=
      (svdBasis T).orthonormal.linearIndependent.comp _
        ((svSortPerm T).injective.comp (Fin.castLE_injective hle))
    rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hkerdim : finrank 𝕜 V - k ≤ finrank 𝕜 (LinearMap.ker S) := by
    have h := LinearMap.finrank_range_add_finrank_ker S
    omega
  have hinter : LinearMap.ker S ⊓ W ≠ ⊥ := by
    intro hbot
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker S) W
    rw [hbot, finrank_bot, add_zero, hWdim] at hsup
    have hle2 : finrank 𝕜 ((LinearMap.ker S ⊔ W : Submodule 𝕜 V)) ≤ finrank 𝕜 V :=
      Submodule.finrank_le _
    omega
  obtain ⟨v, hvmem, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinter
  have hSv : S v = 0 := LinearMap.mem_ker.mp hvmem.1
  have hvW : v ∈ W := hvmem.2
  have hperp : ∀ j : Fin (finrank 𝕜 V), k + 1 ≤ (j : ℕ) →
      ⟪svdBasis T (svSortPerm T j), v⟫_𝕜 = 0 := by
    intro j hj
    refine Submodule.span_induction (p := fun w _ => ⟪svdBasis T (svSortPerm T j), w⟫_𝕜 = 0)
      ?_ ?_ ?_ ?_ hvW
    · rintro _ ⟨i, rfl⟩
      rw [hfam, orthonormal_iff_ite.mp (svdBasis T).orthonormal]
      refine if_neg (fun h => ?_)
      have hji := (svSortPerm T).injective h
      have hi := i.isLt
      rw [hji] at hj
      simp only [Fin.val_castLE] at hj
      omega
    · exact inner_zero_right _
    · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
    · intro c x _ hx; rw [inner_smul_right, hx, mul_zero]
  have hTvSq : (singularValues T (svSortPerm T ⟨k, hk⟩)) ^ 2 * ‖v‖ ^ 2 ≤ ‖T v‖ ^ 2 := by
    rw [normSq_apply, ← sum_sq_norm_inner_sorted T v, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hjk : (j : ℕ) < k + 1
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      nlinarith [singularValues_nonneg T (svSortPerm T ⟨k, hk⟩),
        singularValues_nonneg T (svSortPerm T j),
        singularValues_svSortPerm_antitone T
          (show (j : Fin (finrank 𝕜 V)) ≤ ⟨k, hk⟩ from Nat.lt_succ_iff.mp hjk)]
    · rw [hperp j (not_lt.mp hjk), norm_zero]; simp
  have hTSv : ‖(T - S) v‖ = ‖T v‖ := by rw [LinearMap.sub_apply, hSv, sub_zero]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have h1 : singularValues T (svSortPerm T ⟨k, hk⟩) * ‖v‖ ≤ ‖T v‖ := by
    rw [← Real.sqrt_sq (mul_nonneg (singularValues_nonneg T _) (norm_nonneg v)),
      ← Real.sqrt_sq (norm_nonneg (T v))]
    apply Real.sqrt_le_sqrt
    rw [mul_pow]; exact hTvSq
  have h2 := opNorm_apply_le (T - S) v
  rw [hTSv] at h2
  exact le_of_mul_le_mul_right (le_trans h1 h2) hvpos

/-- 7.92 The best rank-{lit}`≤ k` approximation of {lit}`T` is the truncated SVD: the minimum
of `‖T − S‖` over operators with {lit}`dim range S ≤ k` is the {lit}`(k+1)`-th largest
singular value. -/
theorem isLeast_opNorm_sub (T : V →ₗ[𝕜] V) {k : ℕ} (hk : k < finrank 𝕜 V) :
    IsLeast {r : ℝ | ∃ S : V →ₗ[𝕜] V, finrank 𝕜 (LinearMap.range S) ≤ k ∧ opNorm (T - S) = r}
      (singularValues T (svSortPerm T ⟨k, hk⟩)) := by
  refine ⟨⟨truncSVD T k, finrank_range_truncSVD_le T k,
    le_antisymm (opNorm_sub_truncSVD_le T hk) (le_opNorm_sub_truncSVD T hk)⟩, ?_⟩
  rintro r ⟨S, hrank, rfl⟩
  exact le_opNorm_sub_of_rank_le T hk S hrank

/-! # Polar Decomposition -/

/-! 7.93 Polar decomposition

Suppose {lit}`T ∈ ℒ(V)`. Then there is an isometry (unitary operator) {lit}`S` and
the positive operator {lit}`R = √(T* T)` (with {lit}`R ∘ R = T* T`) such that
{lit}`T = S ∘ R`.

*Construction.* Let {lit}`e = svdBasis T` and let {lit}`fₖ = svdImage T k` be the
orthonormal image frame (7E). Because {lit}`R eₖ = sₖ eₖ` (the positive square root
acts as {lit}`√(sₖ²)` on the {lit}`T* T`-eigenbasis, 7C {name}`LADR.Section_7C.sqrt_eigenvector`),
we have {lit}`(S ∘ R) eₖ = sₖ S eₖ`. Extending the orthonormal list
{lit}`{fₖ : sₖ ≠ 0}` to a full orthonormal basis {lit}`fFull` of {lit}`V`
({name}`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`) and defining
{lit}`S eₖ = fFull k` makes {lit}`S` an isometry (it maps an orthonormal basis to
an orthonormal basis) with {lit}`(S ∘ R) eₖ = sₖ fₖ = T eₖ`. -/
theorem polarDecomposition (T : V →ₗ[𝕜] V) :
    ∃ S R : V →ₗ[𝕜] V, IsIsometry S ∧ R.IsPositive ∧
      R ∘ₗ R = LinearMap.adjoint T ∘ₗ T ∧ T = S ∘ₗ R := by
  obtain ⟨R, hRpos, hRR⟩ := exists_positive_sqrt (adjComp_self_isPositive T)
  -- `R eₖ = sₖ eₖ`.
  have hRe : ∀ i, R (svdBasis T i) = (singularValues T i : 𝕜) • svdBasis T i := by
    intro i
    have h1 : (R ∘ₗ R) (svdBasis T i)
        = (((singularValues T i) ^ 2 : ℝ) : 𝕜) • svdBasis T i := by
      rw [hRR]; exact adjComp_apply_svdBasis T i
    have h2 := sqrt_eigenvector hRpos (sq_nonneg (singularValues T i)) h1
    rwa [Real.sqrt_sq (singularValues_nonneg T i)] at h2
  -- Extend the orthonormal image frame to a full orthonormal basis `fFull`.
  have hcard : finrank 𝕜 V = Fintype.card (Fin (finrank 𝕜 V)) := (Fintype.card_fin _).symm
  have horth : Orthonormal 𝕜
      (Set.restrict {i | singularValues T i ≠ 0} (svdImage T)) := svdImage_orthonormal T
  obtain ⟨fFull, hfFull⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  -- Define `S eₖ = fFull k`.
  set S := (svdBasis T).toBasis.constr 𝕜 (fun i => fFull i) with hS
  have hSe : ∀ i, S (svdBasis T i) = fFull i := by
    intro i
    have h : S ((svdBasis T).toBasis i) = fFull i := by rw [hS]; simp
    rwa [OrthonormalBasis.coe_toBasis] at h
  have hSiso : IsIsometry S := by
    rw [isometry_iff_orthonormal_image (svdBasis T) S]
    simp only [hSe]
    exact fFull.orthonormal
  refine ⟨S, R, hSiso, hRpos, hRR, ?_⟩
  apply (svdBasis T).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply]
  rw [hRe, map_smul, hSe]
  by_cases h : singularValues T i = 0
  · have hz : T (svdBasis T i) = 0 := by
      have hn : ‖T (svdBasis T i)‖ = 0 := by rw [norm_image_svdBasis, h]
      exact norm_eq_zero.mp hn
    rw [hz, h]; simp
  · rw [hfFull i h]
    exact svdBasis_image_eq T i

/-- 7.93 packaged with the unitary predicate: for {lit}`T ∈ ℒ(V)` there is a
unitary {lit}`S` and positive {lit}`R = √(T* T)` with {lit}`T = S ∘ R`. -/
theorem polarDecomposition_unitary (T : V →ₗ[𝕜] V) :
    ∃ S R : V →ₗ[𝕜] V, IsUnitary S ∧ R.IsPositive ∧
      R ∘ₗ R = LinearMap.adjoint T ∘ₗ T ∧ T = S ∘ₗ R := by
  obtain ⟨S, R, hS, hRpos, hRR, hT⟩ := polarDecomposition T
  exact ⟨S, R, (isUnitary_iff_isometry S).mpr hS, hRpos, hRR, hT⟩

/-! # Operators Applied to Ellipsoids and Parallelepipeds -/

/-! 7.95 Definition: ball, {lit}`B`

The ball {lit}`B` in {lit}`V` of radius {lit}`1` centered at {lit}`0`. -/
def ball : Set V := {v : V | ‖v‖ < 1}

/-! 7.96 Definition: ellipsoid, {lit}`E(s₁ f₁, …, sₙ fₙ)`, principal axes

For an orthonormal basis {lit}`f₁, …, fₙ` of {lit}`V` and positive numbers
{lit}`s₁, …, sₙ`, the ellipsoid with principal axes {lit}`sₖ fₖ`. Recall the slot
convention: Axler's {lit}`⟨v, fₖ⟩` is mathlib's {lit}`⟪fₖ, v⟫`. -/
def ellipsoid {n : ℕ} (f : Fin n → V) (s : Fin n → ℝ) : Set V :=
  {v : V | ∑ i, ‖⟪f i, v⟫_𝕜‖ ^ 2 / (s i) ^ 2 < 1}

/-! 7.97 Example: ellipsoids, and 7.98 Notation {lit}`T(Ω)`.

The examples 7.97 ({lit}`E(2f₁, f₂)` in {lit}`ℝ²`, {lit}`E(4f₁, 3f₂, 2f₃)` in
{lit}`ℝ³`) are pictures illustrating 7.96. The notation {lit}`T(Ω)` (7.98) for the
image of {lit}`Ω ⊆ V` under {lit}`T` is mathlib's set image {lit}`T '' Ω`; in
particular {lit}`T(V) = range T`. We use {lit}`T '' Ω` directly below. -/

/-! 7.99 Invertible operator takes the ball to an ellipsoid.

For invertible {lit}`T` with SVD {lit}`T v = ∑ sₖ ⟨v, eₖ⟩ fₖ`,
{lit}`T(B) = E(s₁ f₁, …, sₙ fₙ)`. The proof rests on the coordinate identity
{lit}`∑ ‖⟨T v, fₖ⟩‖² / sₖ² = ∑ ‖⟨v, eₖ⟩‖² = ‖v‖²` (from {name}`LADR.Section_7E.svd_apply`,
{lit}`⟪fₖ, T v⟫ = sₖ ⟪eₖ, v⟫`, and Parseval), so {lit}`T v` lies in the ellipsoid
exactly when {lit}`‖v‖ < 1`. -/
theorem image_ball_eq_ellipsoid (T : V →ₗ[𝕜] V) (hT : Function.Bijective T) :
    T '' ball = ellipsoid (𝕜 := 𝕜) (LADR.Section_7E.svdImage T) (LADR.Section_7E.singularValues T) := by
  set e := LADR.Section_7E.svdBasis T
  set s := LADR.Section_7E.singularValues T with hs
  set f := LADR.Section_7E.svdImage T with hf
  -- every singular value is nonzero (`T` injective)
  have hspos : ∀ k, s k ≠ 0 := by
    intro k
    rw [hs, ← LADR.Section_7E.norm_image_svdBasis T k, ne_eq, norm_eq_zero]
    intro h
    exact LADR.Section_7E.svdBasis_ne_zero T k (hT.injective (by rw [h, map_zero]))
  -- the `fₖ` are orthonormal (all indices are positive-singular-value indices)
  have hON : ∀ j k, ⟪f j, f k⟫_𝕜 = if j = k then 1 else 0 := by
    intro j k
    have h := orthonormal_iff_ite.mp (LADR.Section_7E.svdImage_orthonormal T)
      ⟨j, hspos j⟩ ⟨k, hspos k⟩
    simpa using h
  -- `⟪fₖ, T v⟫ = sₖ ⟪eₖ, v⟫`
  have hinner : ∀ (v : V) (k), ⟪f k, T v⟫_𝕜 = (s k : 𝕜) * ⟪e k, v⟫_𝕜 := by
    intro v k
    rw [LADR.Section_7E.svd_apply T v, inner_sum, Finset.sum_eq_single k]
    · rw [inner_smul_right, inner_smul_right, hON k k, if_pos rfl, mul_one]
    · intro j _ hjk
      rw [inner_smul_right, inner_smul_right, hON k j, if_neg (Ne.symm hjk), mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  -- the coordinate identity `∑ ‖⟪fₖ, T v⟫‖²/sₖ² = ‖v‖²`
  have hkey : ∀ v : V, ∑ k, ‖⟪f k, T v⟫_𝕜‖ ^ 2 / (s k) ^ 2 = ‖v‖ ^ 2 := by
    intro v
    rw [← (e).sum_sq_norm_inner_right v]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hinner v k, div_eq_iff (pow_ne_zero 2 (hspos k)), norm_mul, mul_pow,
      RCLike.norm_ofReal, sq_abs, mul_comm]
  ext w
  simp only [ball, ellipsoid, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [hkey v]
    exact pow_lt_one₀ (norm_nonneg v) hv two_ne_zero
  · intro hw
    obtain ⟨v, rfl⟩ := hT.surjective w
    rw [hkey v] at hw
    exact ⟨v, by nlinarith [norm_nonneg v], rfl⟩

omit [FiniteDimensional 𝕜 V] in
/-- General principle behind 7.99/7.101: an invertible {lit}`S` acting diagonally on an
orthonormal basis ({lit}`⟨g k, S v⟩ = r k ⟨g k, v⟩`, all {lit}`r k ≠ 0`) carries the ball
onto the ellipsoid `E(r₁ g₁, …, rₙ gₙ)`. -/
theorem image_ball_eq_ellipsoid_of_diag {n : ℕ} (S : V →ₗ[𝕜] V) (hS : Function.Bijective S)
    (g : OrthonormalBasis (Fin n) 𝕜 V) (r : Fin n → ℝ) (hr : ∀ k, r k ≠ 0)
    (hSg : ∀ (v : V) (k), ⟪g k, S v⟫_𝕜 = (r k : 𝕜) * ⟪g k, v⟫_𝕜) :
    S '' ball = ellipsoid (𝕜 := 𝕜) (g ·) r := by
  have hkey : ∀ v : V, ∑ k, ‖⟪g k, S v⟫_𝕜‖ ^ 2 / (r k) ^ 2 = ‖v‖ ^ 2 := by
    intro v
    rw [← g.sum_sq_norm_inner_right v]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hSg v k, div_eq_iff (pow_ne_zero 2 (hr k)), norm_mul, mul_pow,
      RCLike.norm_ofReal, sq_abs, mul_comm]
  ext w
  simp only [ball, ellipsoid, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [hkey v]; exact pow_lt_one₀ (norm_nonneg v) hv two_ne_zero
  · intro hw
    obtain ⟨v, rfl⟩ := hS.surjective w
    rw [hkey v] at hw
    exact ⟨v, by nlinarith [norm_nonneg v], rfl⟩

/-- The diagonal stretch with {lit}`S gₖ = rₖ gₖ`, i.e. `S v = ∑ₖ rₖ ⟨v, gₖ⟩ gₖ`. -/
noncomputable def stretchOp {n : ℕ} (g : OrthonormalBasis (Fin n) 𝕜 V) (r : Fin n → ℝ) :
    V →ₗ[𝕜] V :=
  ∑ k, (r k : 𝕜) • LinearMap.smulRight (innerₛₗ 𝕜 (g k)) (g k)

omit [FiniteDimensional 𝕜 V] in
theorem stretchOp_inner {n : ℕ} (g : OrthonormalBasis (Fin n) 𝕜 V) (r : Fin n → ℝ)
    (v : V) (j : Fin n) : ⟪g j, stretchOp g r v⟫_𝕜 = (r j : 𝕜) * ⟪g j, v⟫_𝕜 := by
  rw [stretchOp]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
    innerₛₗ_apply_apply, smul_smul]
  rw [inner_sum, Finset.sum_eq_single j]
  · rw [inner_smul_right, orthonormal_iff_ite.mp g.orthonormal j j, if_pos rfl, mul_one]
  · intro k _ hkj
    rw [inner_smul_right, orthonormal_iff_ite.mp g.orthonormal j k, if_neg (Ne.symm hkj), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem stretchOp_bijective {n : ℕ} (g : OrthonormalBasis (Fin n) 𝕜 V) (r : Fin n → ℝ)
    (hr : ∀ k, r k ≠ 0) : Function.Bijective (stretchOp g r) := by
  have hinj : Function.Injective (stretchOp g r) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hall : ∀ j, ⟪g j, v⟫_𝕜 = 0 := by
      intro j
      have h := stretchOp_inner g r v j
      rw [hv, inner_zero_right] at h
      rcases mul_eq_zero.mp h.symm with h1 | h1
      · exact absurd (RCLike.ofReal_eq_zero.mp h1) (hr j)
      · exact h1
    conv_lhs => rw [← g.sum_repr' v]
    exact Finset.sum_eq_zero fun j _ => by rw [hall j, zero_smul]
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

theorem stretchOp_image_ball {n : ℕ} (g : OrthonormalBasis (Fin n) 𝕜 V) (r : Fin n → ℝ)
    (hr : ∀ k, r k ≠ 0) : stretchOp g r '' ball = ellipsoid (𝕜 := 𝕜) (g ·) r :=
  image_ball_eq_ellipsoid_of_diag (stretchOp g r) (stretchOp_bijective g r hr) g r hr
    (fun v k => stretchOp_inner g r v k)

/-- 7.101 An invertible operator maps every ellipsoid to an ellipsoid. Axler's
argument: the ellipsoid `E(r₁ g₁, …, rₙ gₙ)` is {lit}`stretchOp '' ball`, so its image
under {lit}`T` is {lit}`(T ∘ stretchOp) '' ball`, which 7.99 identifies as an ellipsoid
(with axes the singular values / image vectors of {lit}`T ∘ stretchOp`). -/
theorem image_ellipsoid_is_ellipsoid {n : ℕ} (T : V →ₗ[𝕜] V) (hT : Function.Bijective T)
    (g : OrthonormalBasis (Fin n) 𝕜 V) (r : Fin n → ℝ) (hr : ∀ k, r k ≠ 0) :
    ∃ (h : Fin (Module.finrank 𝕜 V) → V) (t : Fin (Module.finrank 𝕜 V) → ℝ),
      T '' ellipsoid (𝕜 := 𝕜) (g ·) r = ellipsoid (𝕜 := 𝕜) h t := by
  have hbij : Function.Bijective (T ∘ₗ stretchOp g r) := by
    rw [LinearMap.coe_comp]; exact hT.comp (stretchOp_bijective g r hr)
  refine ⟨LADR.Section_7E.svdImage (T ∘ₗ stretchOp g r),
    LADR.Section_7E.singularValues (T ∘ₗ stretchOp g r), ?_⟩
  rw [← stretchOp_image_ball g r hr, ← Set.image_comp, ← LinearMap.coe_comp]
  exact image_ball_eq_ellipsoid (T ∘ₗ stretchOp g r) hbij

/-! 7.102 Definition: {lit}`P(v₁, …, vₙ)`, parallelepiped

We fold Axler's base point {lit}`u` into the definition, so
{lit}`parallelepiped u v` is Axler's {lit}`u + P(v₁, …, vₙ)` (3.95). The
coefficients {lit}`aₖ ∈ (0,1)` are real numbers acting on {lit}`V` through the
scalar field {lit}`𝕜 ⊇ ℝ`. -/
def parallelepiped {n : ℕ} (u : V) (v : Fin n → V) : Set V :=
  {x : V | ∃ a : Fin n → ℝ, (∀ i, a i ∈ Set.Ioo (0 : ℝ) 1) ∧ x = u + ∑ i, (a i : 𝕜) • v i}

/-! 7.103 Example: parallelepipeds — pictures illustrating 7.102, omitted. -/

omit [FiniteDimensional 𝕜 V] in
/-- 7.104 An invertible operator takes parallelepipeds to parallelepipeds:
{lit}`T(u + P(v₁, …, vₙ)) = T u + P(T v₁, …, T vₙ)`. (The set equality is pure
linearity; invertibility of {lit}`T` is what makes {lit}`T v₁, …, T vₙ` a basis, so
the image is again a genuine parallelepiped.) -/
theorem image_parallelepiped {n : ℕ} (T : V →ₗ[𝕜] V) (u : V) (v : Fin n → V) :
    T '' parallelepiped (𝕜 := 𝕜) u v = parallelepiped (𝕜 := 𝕜) (T u) (fun i => T (v i)) := by
  ext y
  simp only [parallelepiped, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [map_add, map_sum]; simp only [map_smul]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨u + ∑ i, (a i : 𝕜) • v i, ⟨a, ha, rfl⟩, ?_⟩
    rw [map_add, map_sum]; simp only [map_smul]

/-! 7.105 Definition: box

A *box* {lit}`u + P(r₁ e₁, …, rₙ eₙ)` is a parallelepiped whose defining edges are
positive multiples of an orthonormal basis. We express it as
{lit}`parallelepiped u (fun k => (rₖ : 𝕜) • e k)`. (7.106 gives pictures, omitted.) -/
def box {n : ℕ} (u : V) (r : Fin n → ℝ) (e : OrthonormalBasis (Fin n) 𝕜 V) : Set V :=
  parallelepiped (𝕜 := 𝕜) u (fun i => (r i : 𝕜) • e i)

/-- 7.107 Every invertible operator takes some boxes to boxes: {lit}`T` maps the box
{lit}`u + P(r₁ e₁, …, rₙ eₙ)` (with {lit}`e = svdBasis T`) onto the box
{lit}`T u + P(r₁ s₁ f₁, …, rₙ sₙ fₙ)` (with {lit}`fₖ = svdImage T k`). For invertible
{lit}`T` all {lit}`sₖ > 0`, so the image is a genuine box. -/
theorem image_box (T : V →ₗ[𝕜] V) (u : V) (r : Fin (finrank 𝕜 V) → ℝ) :
    T '' box u r (svdBasis T)
      = parallelepiped (𝕜 := 𝕜) (T u)
          (fun i => (r i * singularValues T i : 𝕜) • svdImage T i) := by
  have hedge : (fun i => T ((r i : 𝕜) • svdBasis T i))
      = fun i => (r i * singularValues T i : 𝕜) • svdImage T i := by
    funext i
    rw [map_smul, svdBasis_image_eq T i, smul_smul, ← RCLike.ofReal_mul]
  rw [box, image_parallelepiped, hedge]

/-! # Volume via Singular Values -/

/-! 7.108 Definition: volume of a box, 7.109 Definition: volume, 7.110 Example, and
7.111 volume changes by a factor of the product of the singular values.

Axler takes {lit}`𝐅 = 𝐑` and an intuitive (non-rigorous) notion of volume:
{lit}`volume(u + P(r₁ e₁, …, rₙ eₙ)) = r₁ ⋯ rₙ` (7.108), extended to arbitrary
subsets by approximation with disjoint boxes (7.109). The headline result 7.111
states that for invertible {lit}`T ∈ ℒ(V)` and {lit}`Ω ⊆ V`,
{lit}`volume T(Ω) = (s₁ ⋯ sₙ)(volume Ω)`, where {lit}`s₁ ⋯ sₙ = |det T|` (9.60/9.61).

The definitions 7.108/7.109 (volume of a box, and volume of a general set by box
approximation) and the example 7.110 stay in prose: Axler himself notes these
belong to analysis rather than linear algebra and works only with an intuitive
notion of volume. But the **headline theorem 7.111 is proved**, using measure
theory for {lit}`volume`: on {lit}`ℝⁿ` the additive Haar measure satisfies
{lit}`volume T(Ω) = (s₁ ⋯ sₙ) · volume Ω`, formalized as
{lit}`LADR.Section_9C.volume_image_eq_prod_singularValues` (the Haar
change-of-variables {name}`MeasureTheory.Measure.addHaar_image_linearMap`, 9.61,
with Jacobian {lit}`|det T|` rewritten as {lit}`∏ sᵢ` by 9.60). The linear-algebra
input 7.107 (boxes to boxes) is proved above as {lit}`image_box`. -/

/-! # Properties of an Operator as Determined by Its Eigenvalues

The chapter closes with an (unnumbered) summary table: for a normal operator on a
complex inner product space, each listed property (invertible, self-adjoint, skew,
orthogonal projection, positive, unitary, norm {lit}`< 1`) holds iff all eigenvalues
lie in the indicated subset of {lit}`ℂ`. The last row uses 7.88(a) (norm = largest
singular value) together with Section 7E Exercise 7 (singular values of a normal
operator are the absolute values of its eigenvalues). These equivalences are spread
across Sections 7A–7E; no new numbered result appears, so nothing is formalized
here. -/

/-! # Exercises 7F -/

/-- 7F.1 Reverse triangle inequality: {lit}`| ‖S‖ − ‖T‖ | ≤ ‖S − T‖`. -/
theorem exercise_7F_1 (S T : V →ₗ[𝕜] W) : |opNorm S - opNorm T| ≤ opNorm (S - T) := by
  sorry

/-- 7F.2 For self-adjoint (or complex normal) {lit}`T`,
{lit}`‖T‖ = max{|λ| : λ eigenvalue}`. -/
theorem exercise_7F_2 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) :
    IsGreatest {r : ℝ | ∃ μ : 𝕜, HasEigenvalue T μ ∧ ‖μ‖ = r} (opNorm T) := by
  sorry

/-- 7F.3 {lit}`‖T v‖ = ‖T‖ ‖v‖ ⟺ T* T v = ‖T‖² v`. -/
theorem exercise_7F_3 (T : V →ₗ[𝕜] W) (v : V) :
    ‖T v‖ = opNorm T * ‖v‖ ↔
      (LinearMap.adjoint T ∘ₗ T) v = ((opNorm T ^ 2 : ℝ) : 𝕜) • v := by
  sorry

/-- 7F.4 If {lit}`‖T v‖ = ‖T‖ ‖v‖` and {lit}`⟨u, v⟩ = 0`, then
{lit}`⟨T u, T v⟩ = 0`. -/
theorem exercise_7F_4 (T : V →ₗ[𝕜] W) (v : V) (hv : ‖T v‖ = opNorm T * ‖v‖)
    (u : V) (huv : ⟪u, v⟫_𝕜 = 0) : ⟪T u, T v⟫_𝕜 = 0 := by
  sorry

/-- 7F.5 Submultiplicativity: for {lit}`T ∈ ℒ(V, U)` and {lit}`S ∈ ℒ(U, W)`,
{lit}`‖S T‖ ≤ ‖S‖ ‖T‖`. -/
theorem exercise_7F_5 {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    [FiniteDimensional 𝕜 U] (T : V →ₗ[𝕜] U) (S : U →ₗ[𝕜] W) :
    opNorm (S ∘ₗ T) ≤ opNorm S * opNorm T := by
  sorry

/-- 7F.6 Counterexample: {lit}`‖ST‖ = ‖TS‖` can fail. -/
theorem exercise_7F_6 :
    ¬ ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
      (S T : E →ₗ[𝕜] E), opNorm (S ∘ₗ T) = opNorm (T ∘ₗ S) := by
  sorry

/-- 7F.7 {lit}`d(S, T) = ‖S − T‖` is a metric on {lit}`ℒ(V, W)`. -/
theorem exercise_7F_7 :
    (∀ S T : V →ₗ[𝕜] W, opNorm (S - T) = 0 ↔ S = T) ∧
      (∀ S T : V →ₗ[𝕜] W, opNorm (S - T) = opNorm (T - S)) ∧
      (∀ S T R : V →ₗ[𝕜] W, opNorm (S - R) ≤ opNorm (S - T) + opNorm (T - R)) := by
  sorry

/-- 7F.8(a) If {lit}`‖I − T‖ < 1`, then {lit}`T` is invertible. -/
theorem exercise_7F_8a (T : V →ₗ[𝕜] V) (h : opNorm (1 - T) < 1) :
    Function.Bijective T := by
  sorry

/-- 7F.8(b) If {lit}`S` is invertible and {lit}`‖S − T‖ < 1/‖S⁻¹‖`, then {lit}`T`
is invertible. -/
theorem exercise_7F_8b (S : V ≃ₗ[𝕜] V) (T : V →ₗ[𝕜] V)
    (h : opNorm ((S : V →ₗ[𝕜] V) - T) < 1 / opNorm (S.symm : V →ₗ[𝕜] V)) :
    Function.Bijective T := by
  sorry

/-- 7F.9 Every operator is a limit of invertible operators: for every {lit}`ε > 0`
there is an invertible {lit}`S` with {lit}`0 < ‖T − S‖ < ε`. -/
theorem exercise_7F_9 (T : V →ₗ[𝕜] V) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : V →ₗ[𝕜] V, Function.Bijective S ∧ 0 < opNorm (T - S) ∧ opNorm (T - S) < ε := by
  sorry

/-- 7F.10 If {lit}`dim V > 1` and {lit}`T` is not invertible, {lit}`T` is a limit of
non-invertible operators. -/
theorem exercise_7F_10 (h : 1 < finrank 𝕜 V) (T : V →ₗ[𝕜] V)
    (hni : ¬ Function.Bijective T) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : V →ₗ[𝕜] V, ¬ Function.Bijective S ∧ 0 < opNorm (T - S) ∧ opNorm (T - S) < ε := by
  sorry

/-- 7F.11 Over {lit}`ℂ`, every operator is a limit of diagonalizable operators. -/
theorem exercise_7F_11 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : E →ₗ[ℂ] E,
      (∃ b : Module.Basis (Fin (finrank ℂ E)) ℂ E, ∀ i, ∃ μ : ℂ, S (b i) = μ • b i) ∧
        0 < opNorm (T - S) ∧ opNorm (T - S) < ε := by
  sorry

/-- 7F.12 For a positive operator {lit}`T` with positive square root {lit}`R`,
{lit}`‖R‖ = √‖T‖`. -/
theorem exercise_7F_12 {T R : V →ₗ[𝕜] V} (hT : T.IsPositive) (hR : R.IsPositive)
    (hRT : R ∘ₗ R = T) : opNorm R = Real.sqrt (opNorm T) := by
  sorry

/-- 7F.13 For positive operators {lit}`S, T`,
{lit}`‖S − T‖ ≤ max{‖S‖, ‖T‖} ≤ ‖S + T‖`. -/
theorem exercise_7F_13 {S T : V →ₗ[𝕜] V} (hS : S.IsPositive) (hT : T.IsPositive) :
    opNorm (S - T) ≤ max (opNorm S) (opNorm T) ∧
      max (opNorm S) (opNorm T) ≤ opNorm (S + T) := by
  sorry

/-- 7F.14 If {lit}`‖P_U − P_W‖ < 1`, then {lit}`dim U = dim W`. -/
theorem exercise_7F_14 (U W' : Submodule 𝕜 V)
    (h : opNorm ((U.starProjection : V →ₗ[𝕜] V) - (W'.starProjection : V →ₗ[𝕜] V)) < 1) :
    finrank 𝕜 U = finrank 𝕜 W' := by
  sorry

/-- 7F.15 For {lit}`T(z₁,z₂,z₃) = (z₃, 2z₁, 3z₂)` on {lit}`𝔽³`, there is a unitary
{lit}`S` with {lit}`T = S√(T*T)` (polar decomposition). -/
theorem exercise_7F_15 (T : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3))
    (hT : ∀ z : EuclideanSpace 𝕜 (Fin 3), T z = !₂[z 2, 2 * z 0, 3 * z 1]) :
    ∃ S R : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3),
      IsUnitary S ∧ R.IsPositive ∧ R ∘ₗ R = LinearMap.adjoint T ∘ₗ T ∧ T = S ∘ₗ R := by
  sorry

/-- 7F.16 If {lit}`S` is positive invertible, there is {lit}`δ > 0` such that every
self-adjoint {lit}`T` with {lit}`‖S − T‖ < δ` is positive. -/
theorem exercise_7F_16 (S : V →ₗ[𝕜] V) (hS : S.IsPositive) (hSinv : Function.Bijective S) :
    ∃ δ > 0, ∀ T : V →ₗ[𝕜] V, LinearMap.IsSymmetric T → opNorm (S - T) < δ →
      T.IsPositive := by
  sorry

/-- 7F.17 The Riesz functional {lit}`φ_u(v) = ⟨v, u⟩` has {lit}`‖φ_u‖ = ‖u‖`,
where {lit}`‖φ_u‖` is its norm as a linear map into the scalar field {lit}`𝔽`
viewed as an inner product space over itself. Recall the slot convention: Axler's
{lit}`⟨v, u⟩` is mathlib's {lit}`⟪u, v⟫`, so {lit}`φ_u` is {name}`innerₛₗ` applied
to {lit}`u`. -/
theorem exercise_7F_17 (u : V) : opNorm (innerₛₗ 𝕜 u) = ‖u‖ := by
  sorry

/-- 7F.18(a) For an orthonormal basis {lit}`e`,
{lit}`max ‖Teₖ‖ ≤ ‖T‖ ≤ (∑ ‖Teₖ‖²)^(1/2)`. -/
theorem exercise_7F_18a (T : V →ₗ[𝕜] W) (e : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V) :
    (∀ k, ‖T (e k)‖ ≤ opNorm T) ∧ opNorm T ≤ Real.sqrt (∑ k, ‖T (e k)‖ ^ 2) := by
  sorry

/-- 7F.18(b) {lit}`‖T‖ = (∑ ‖Teₖ‖²)^(1/2)` iff {lit}`dim range T ≤ 1`. -/
theorem exercise_7F_18b (T : V →ₗ[𝕜] W) (e : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V) :
    opNorm T = Real.sqrt (∑ k, ‖T (e k)‖ ^ 2) ↔ finrank 𝕜 (LinearMap.range T) ≤ 1 := by
  sorry

/-- 7F.19 The C-star identity {lit}`‖T* T‖ = ‖T‖²`, the starting point for the
theory of C-star-algebras. -/
@[avoiding ContinuousLinearMap.norm_adjoint_comp_self]
theorem exercise_7F_19 (T : V →ₗ[𝕜] W) :
    opNorm (LinearMap.adjoint T ∘ₗ T) = opNorm T ^ 2 := by
  sorry

/-- 7F.20 For a normal operator {lit}`T` and {lit}`k ≥ 1`, {lit}`‖Tᵏ‖ = ‖T‖ᵏ`. -/
theorem exercise_7F_20 {T : V →ₗ[𝕜] V}
    (hT : LinearMap.adjoint T ∘ₗ T = T ∘ₗ LinearMap.adjoint T) (k : ℕ) (hk : 0 < k) :
    opNorm (T ^ k) = opNorm T ^ k := by
  sorry

/-- 7F.21 If {lit}`dim V, dim W > 1`, the operator norm on {lit}`ℒ(V, W)` does not
come from an inner product. -/
theorem exercise_7F_21 (hV : 1 < finrank 𝕜 V) (hW : 1 < finrank 𝕜 W) :
    ¬ ∃ core : InnerProductSpace.Core 𝕜 (V →ₗ[𝕜] W),
      ∀ T : V →ₗ[𝕜] W, opNorm T = Real.sqrt (RCLike.re (core.inner T T)) := by
  sorry

/-- 7F.22 (Courant–Fischer min-max) With {lit}`s₁ ≥ ⋯ ≥ sₙ` the singular values
of {lit}`T` in decreasing order and {lit}`1 ≤ k ≤ n`,
{lit}`min{‖T|U‖ : dim U = k} = s_{n−k+1}`. The decreasing order is
{name}`svSortPerm`, under which Axler's {lit}`s_{n−k+1}` (1-indexed) is the
{lit}`0`-indexed entry {lit}`n − k`. Stated for an operator on {lit}`V`, since
that is where this file's sorted singular values are defined. -/
theorem exercise_7F_22 (T : V →ₗ[𝕜] V) {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ finrank 𝕜 V) :
    IsLeast {r : ℝ | ∃ U : Submodule 𝕜 V, finrank 𝕜 U = k ∧ opNorm (T ∘ₗ U.subtype) = r}
      (LADR.Section_7E.singularValues T (svSortPerm T ⟨finrank 𝕜 V - k, by omega⟩)) := by
  sorry

/-- 7F.23 Every {lit}`T ∈ ℒ(V, W)` is uniformly continuous. -/
theorem exercise_7F_23 (T : V →ₗ[𝕜] W) : UniformContinuous T := by
  sorry

/-- 7F.24 For invertible {lit}`T`, {lit}`‖T⁻¹‖ = ‖T‖⁻¹` iff {lit}`T/‖T‖` is
unitary. -/
theorem exercise_7F_24 (T : V ≃ₗ[𝕜] V) :
    opNorm (T.symm : V →ₗ[𝕜] V) = (opNorm (T : V →ₗ[𝕜] V))⁻¹ ↔
      IsUnitary (((opNorm (T : V →ₗ[𝕜] V))⁻¹ : 𝕜) • (T : V →ₗ[𝕜] V)) := by
  sorry

/-- 7F.25 For {lit}`T v = ⟨v, u⟩ x` with {lit}`u ≠ 0`,
{lit}`√(T*T) v = (‖x‖/‖u‖) ⟨v, u⟩ u`. -/
theorem exercise_7F_25 (u x : V) (hu : u ≠ 0) (T : V →ₗ[𝕜] V)
    (hT : ∀ v, T v = ⟪u, v⟫_𝕜 • x) (R : V →ₗ[𝕜] V) (hR : R.IsPositive)
    (hRT : R ∘ₗ R = LinearMap.adjoint T ∘ₗ T) (v : V) :
    R v = ((((‖x‖ / ‖u‖ : ℝ) : 𝕜)) * ⟪u, v⟫_𝕜) • u := by
  sorry

/-- 7F.26 {lit}`T` is invertible iff there is a unique unitary {lit}`S` with
{lit}`T = S√(T*T)`. -/
theorem exercise_7F_26 (T : V →ₗ[𝕜] V) :
    Function.Bijective T ↔
      ∃! S : V →ₗ[𝕜] V, IsUnitary S ∧ ∃ R : V →ₗ[𝕜] V, R.IsPositive ∧
        R ∘ₗ R = LinearMap.adjoint T ∘ₗ T ∧ T = S ∘ₗ R := by
  sorry

/-- 7F.27 The unitary {lit}`S v = ∑ ⟨v, eₖ⟩ fₖ` from an SVD of {lit}`T` is unitary
and is a closest unitary operator to {lit}`T`. -/
theorem exercise_7F_27 {n : ℕ} (T : V →ₗ[𝕜] V) (e f : Fin n → V) (s : Fin n → ℝ)
    (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (hT : ∀ v, T v = ∑ k, (s k : 𝕜) • ⟪e k, v⟫_𝕜 • f k)
    (S : V →ₗ[𝕜] V) (hS : ∀ v, S v = ∑ k, ⟪e k, v⟫_𝕜 • f k) :
    IsUnitary S ∧ ∀ E : V →ₗ[𝕜] V, IsUnitary E → opNorm (T - S) ≤ opNorm (T - E) := by
  sorry

/-- 7F.28 A "right" polar decomposition: {lit}`T = √(T T*) ∘ S` for a unitary
{lit}`S`. Here {lit}`R` is the positive square root of {lit}`T T*`. -/
theorem exercise_7F_28 (T : V →ₗ[𝕜] V) :
    ∃ S R : V →ₗ[𝕜] V, IsUnitary S ∧ R.IsPositive ∧
      R ∘ₗ R = T ∘ₗ LinearMap.adjoint T ∧ T = R ∘ₗ S := by
  sorry

/-- 7F.29(a) There is a unitary {lit}`S` with {lit}`T T* = S (T* T) S*`. -/
theorem exercise_7F_29a (T : V →ₗ[𝕜] V) :
    ∃ S : V →ₗ[𝕜] V, IsUnitary S ∧
      T ∘ₗ LinearMap.adjoint T =
        S ∘ₗ (LinearMap.adjoint T ∘ₗ T) ∘ₗ LinearMap.adjoint S := by
  sorry

/-- 7F.29(b) {lit}`T` and {lit}`T*` have the same singular values. -/
theorem exercise_7F_29b (T : V →ₗ[𝕜] V) :
    {r : ℝ | ∃ i, LADR.Section_7E.singularValues T i = r} =
      {r : ℝ | ∃ i, LADR.Section_7E.singularValues (LinearMap.adjoint T) i = r} := by
  sorry

/-- 7F.30 Uniqueness of the positive factor: if {lit}`S` is unitary, {lit}`R` is
positive, and {lit}`T = S R`, then {lit}`R = √(T* T)`, i.e. {lit}`R ∘ R = T* T`. -/
theorem exercise_7F_30 {T S R : V →ₗ[𝕜] V} (hS : IsUnitary S) (hR : R.IsPositive)
    (hT : T = S ∘ₗ R) : R ∘ₗ R = LinearMap.adjoint T ∘ₗ T := by
  sorry

/-- 7F.31 Over {lit}`ℂ`, a normal {lit}`T` has a polar decomposition {lit}`T = SR`
where {lit}`S` and {lit}`R = √(T*T)` are simultaneously diagonalizable. -/
theorem exercise_7F_31 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hN : IsStarNormal T) :
    ∃ (S R : E →ₗ[ℂ] E) (m : ℕ) (b : OrthonormalBasis (Fin m) ℂ E),
      IsUnitary S ∧ R.IsPositive ∧ R ∘ₗ R = LinearMap.adjoint T ∘ₗ T ∧ T = S ∘ₗ R ∧
        (∀ i, ∃ μ : ℂ, S (b i) = μ • b i) ∧ (∀ i, ∃ ν : ℂ, R (b i) = ν • b i) := by
  sorry

/-- 7F.32 For {lit}`T ≠ 0` with positive singular values {lit}`s₁, …, sₘ`, there
is an orthonormal basis {lit}`e₁, …, eₘ` of {lit}`(null T)⟂` for which
{lit}`T(E(e₁/s₁, …, eₘ/sₘ))` is the ball of radius {lit}`1` in {lit}`range T`.
The positive singular values are listed with multiplicity by the equivalence
{lit}`σ`, and {lit}`E(e₁/s₁, …)` is {name}`ellipsoid` with axis lengths
{lit}`1/sⱼ`. -/
theorem exercise_7F_32 (T : V →ₗ[𝕜] W) (hT : T ≠ 0) {m : ℕ}
    (σ : Fin m ≃ {i : Fin (finrank 𝕜 V) // LADR.Section_7E.singularValues T i ≠ 0}) :
    ∃ e : Fin m → ((LinearMap.ker T)ᗮ : Submodule 𝕜 V), Orthonormal 𝕜 e ∧
      (T ∘ₗ (LinearMap.ker T)ᗮ.subtype) ''
          ellipsoid (𝕜 := 𝕜) e (fun j => 1 / LADR.Section_7E.singularValues T (σ j)) =
        {w : W | w ∈ LinearMap.range T ∧ ‖w‖ < 1} := by
  sorry

end LADR.Section_7F
