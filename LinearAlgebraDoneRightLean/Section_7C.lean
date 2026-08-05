import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.FieldTheory.Minpoly.Field
import LinearAlgebraDoneRightLean.Section_6C
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7C: Positive Operators
-/

namespace LADR.Section_7C

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module.End (HasEigenvalue)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-! 7.34 Definition: positive operator

An operator {lit}`T ∈ ℒ(V)` is *positive* if it is self-adjoint and
{lit}`⟨Tv, v⟩ ≥ 0` for all {lit}`v`. This is mathlib's {name}`LinearMap.IsPositive`
(over a complex space the self-adjointness is automatic — 7.14). -/

omit [FiniteDimensional 𝕜 V] in
theorem isPositive_iff_symmetric_nonneg (T : V →ₗ[𝕜] V) :
    T.IsPositive ↔ LinearMap.IsSymmetric T ∧ ∀ v, 0 ≤ RCLike.re ⟪T v, v⟫_𝕜 :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-! 7.35 Example: positive operators. Axler gives three illustrations of
Definition 7.34: (a) the operator on {lit}`𝐅²` with matrix {lit}`!![2,-1;-1,1]`;
(b) an orthogonal projection {lit}`P_U` ("as you should verify"); and (c)
{lit}`T² + bT + cI` when {lit}`T` is self-adjoint and {lit}`b² < 4c` ("as shown by
the proof of 7.26"). We formalize the concrete instance (a): its quadratic form is
{lit}`⟨T(w,z),(w,z)⟩ = 2|w|² - 2 Re(w̄z) + |z|² = |w - z|² + |w|² ≥ 0`. -/
open scoped Matrix ComplexOrder in
/-- 7.35(a): the operator on {lit}`ℂ²` whose matrix in the standard basis is
{lit}`!![2, -1; -1, 1]` is a positive operator, because its quadratic form equals
{lit}`|w - z|² + |w|² ≥ 0`. -/
theorem toEuclideanLin_isPositive :
    (Matrix.toEuclideanLin (!![2, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ)).IsPositive := by
  rw [Matrix.isPositive_toEuclideanLin_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · have hval : star x ⬝ᵥ (!![2, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℂ).mulVec x
        = ((Complex.normSq (x 0 - x 1) + Complex.normSq (x 0) : ℝ) : ℂ) := by
      simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.cons_val_zero,
        Matrix.cons_val_one, Pi.star_apply, RCLike.star_def, Matrix.of_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
      apply Complex.ext <;>
        simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.conj_re, Complex.conj_im] <;> ring
    rw [hval]
    exact_mod_cast add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-! 7.36 Definition: square root

{lit}`R` is a *square root* of {lit}`T` if {lit}`R² = T`. -/

def IsSquareRoot (R T : V →ₗ[𝕜] V) : Prop := R ∘ₗ R = T

/-- The operator {lit}`T(z₁,z₂,z₃) = (z₃,0,0)` on {lit}`ℂ³` (Example 7.37). -/
def T_7_37 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun z := ![z 2, 0, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- The operator {lit}`R(z₁,z₂,z₃) = (z₂,z₃,0)` on {lit}`ℂ³` (Example 7.37). -/
def R_7_37 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun z := ![z 1, z 2, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- 7.37 Example: {lit}`R` is a square root of {lit}`T` — {lit}`R² = T` (the
square-root relation of Definition 7.36, here stated directly since it is purely
algebraic and needs no inner product). -/
theorem R_7_37_sq : R_7_37 ∘ₗ R_7_37 = T_7_37 := by
  ext z i
  fin_cases i <;> simp [R_7_37, T_7_37]

/-! 7.38 Characterizations of positive operators

Among the equivalent conditions, the direction {lit}`T = R* R ⟹ T` positive
(f ⟹ a) has a short direct proof, which we give. -/

/-- {lit}`R* R` is always a positive operator (7.38 (f) ⟹ (a)). -/
theorem adjoint_comp_self_isPositive (R : V →ₗ[𝕜] V) :
    (LinearMap.adjoint R ∘ₗ R).IsPositive := by
  constructor
  · intro x y
    simp only [LinearMap.comp_apply]
    rw [LinearMap.adjoint_inner_left, ← LinearMap.adjoint_inner_right]
  · intro x
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    rw [inner_self_eq_norm_sq_to_K]
    simp

omit [FiniteDimensional 𝕜 V] in
/-- (a) ⟹ (b): every eigenvalue of a positive operator is a nonnegative real. -/
theorem eigenvalue_nonneg {T : V →ₗ[𝕜] V} (hT : T.IsPositive) {μ : 𝕜}
    (hμ : HasEigenvalue T μ) : 0 ≤ RCLike.re μ ∧ conj μ = μ := by
  refine ⟨?_, hT.isSymmetric.conj_eigenvalue_eq_self hμ⟩
  obtain ⟨v, hTv, hv⟩ := hμ.exists_hasEigenvector
  have hmem : T v = μ • v := Module.End.mem_eigenspace_iff.mp hTv
  have hpos : 0 ≤ RCLike.re ⟪T v, v⟫_𝕜 := hT.2 v
  rw [hmem, inner_smul_left, inner_self_eq_norm_sq_to_K,
    hT.isSymmetric.conj_eigenvalue_eq_self hμ, ← RCLike.ofReal_pow, mul_comm,
    RCLike.re_ofReal_mul] at hpos
  have hvnorm : 0 < ‖v‖ ^ 2 := by positivity
  exact (mul_nonneg_iff_of_pos_left hvnorm).mp hpos

/-! 7.38 (b) ⟹ (d) Every positive operator has a positive square root.

We build {lit}`R` acting as {lit}`√λ` on each {lit}`T`-eigenvector (from the
spectral theorem's orthonormal eigenbasis), and check {lit}`R` is positive and
{lit}`R² = T`. -/

theorem exists_positive_sqrt {T : V →ₗ[𝕜] V} (hT : T.IsPositive) :
    ∃ R : V →ₗ[𝕜] V, R.IsPositive ∧ R ∘ₗ R = T := by
  set n := Module.finrank 𝕜 V
  set hs := hT.isSymmetric
  set b := hs.eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) with hb
  set μ := hs.eigenvalues (rfl : Module.finrank 𝕜 V = n) with hμ
  have hμnn : ∀ i, 0 ≤ μ i := by
    intro i
    have hev : HasEigenvalue T ((μ i : ℝ) : 𝕜) :=
      hs.hasEigenvalue_eigenvalues (rfl : Module.finrank 𝕜 V = n) i
    have := (eigenvalue_nonneg hT hev).1
    rwa [RCLike.ofReal_re] at this
  set R := b.toBasis.constr 𝕜 (fun i => (Real.sqrt (μ i) : 𝕜) • b i) with hR
  have hRb : ∀ i, R (b i) = (Real.sqrt (μ i) : 𝕜) • b i := by
    intro i
    have h1 : R (b.toBasis i) = (Real.sqrt (μ i) : 𝕜) • b i := by
      rw [hR]; simp only [Module.Basis.constr_basis]
    rwa [OrthonormalBasis.coe_toBasis] at h1
  have hRsym : LinearMap.IsSymmetric R := by
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, isSelfAdjoint_iff, LinearMap.star_eq_adjoint,
      eq_comm, LinearMap.eq_adjoint_iff_basis b.toBasis b.toBasis]
    intro i j
    simp only [OrthonormalBasis.coe_toBasis, hRb, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal]
    rcases eq_or_ne i j with h | h
    · subst h; rfl
    · rw [b.orthonormal.2 h]; ring
  refine ⟨R, ⟨hRsym, ?_⟩, ?_⟩
  · intro x
    have hRx : R x = ∑ i, (⟪b i, x⟫_𝕜 * (Real.sqrt (μ i) : 𝕜)) • b i := by
      conv_lhs => rw [← b.sum_repr' x]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hRb, smul_smul]
    rw [hRx, sum_inner, map_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have hterm : ⟪(⟪b i, x⟫_𝕜 * (Real.sqrt (μ i) : 𝕜)) • b i, x⟫_𝕜
        = ((Real.sqrt (μ i) * ‖⟪b i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
      rw [inner_smul_left,
        show conj (⟪b i, x⟫_𝕜 * (Real.sqrt (μ i) : 𝕜)) = conj ⟪b i, x⟫_𝕜 * (Real.sqrt (μ i) : 𝕜) by
          rw [map_mul, RCLike.conj_ofReal],
        mul_right_comm, RCLike.conj_mul]
      push_cast; ring
    rw [hterm, RCLike.ofReal_re]
    positivity
  · apply b.toBasis.ext
    intro i
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
    rw [hRb, map_smul, hRb, smul_smul]
    rw [show (Real.sqrt (μ i) : 𝕜) * (Real.sqrt (μ i) : 𝕜) = ((μ i : ℝ) : 𝕜) by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hμnn i)]]
    rw [← hs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i]

/-! 7.39 Each positive operator has a *unique* positive square root.

Key step: a positive square root {lit}`S` of {lit}`T` sends each
{lit}`c`-eigenvector {lit}`w` of {lit}`T` to {lit}`√c · w`, because writing
{lit}`w` in {lit}`S`'s orthonormal eigenbasis forces every contributing
{lit}`S`-eigenvalue {lit}`σ` to satisfy {lit}`σ² = c`. -/

theorem sqrt_eigenvector {S : V →ₗ[𝕜] V} (hS : S.IsPositive) {w : V} {c : ℝ} (_hc : 0 ≤ c)
    (hw : (S ∘ₗ S) w = (c : 𝕜) • w) : S w = (Real.sqrt c : 𝕜) • w := by
  set n := Module.finrank 𝕜 V
  set hSs := hS.isSymmetric
  set e := hSs.eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) with he
  set σ := hSs.eigenvalues (rfl : Module.finrank 𝕜 V = n) with hσ
  have hσnn : ∀ i, 0 ≤ σ i := by
    intro i
    have hev : HasEigenvalue S ((σ i : ℝ) : 𝕜) :=
      hSs.hasEigenvalue_eigenvalues (rfl : Module.finrank 𝕜 V = n) i
    have := (eigenvalue_nonneg hS hev).1
    rwa [RCLike.ofReal_re] at this
  have hSe : ∀ i, S (e i) = (σ i : 𝕜) • e i :=
    fun i => hSs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i
  apply e.repr.injective
  ext i
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hSw : ⟪e i, S w⟫_𝕜 = (σ i : 𝕜) * ⟪e i, w⟫_𝕜 := by
    rw [← hSs (e i) w, hSe, inner_smul_left, RCLike.conj_ofReal]
  have hSSw : (σ i : 𝕜) ^ 2 * ⟪e i, w⟫_𝕜 = (c : 𝕜) * ⟪e i, w⟫_𝕜 := by
    have h1 : ⟪e i, (S ∘ₗ S) w⟫_𝕜 = (σ i : 𝕜) ^ 2 * ⟪e i, w⟫_𝕜 := by
      rw [LinearMap.comp_apply, ← hSs (e i) (S w), hSe, inner_smul_left, RCLike.conj_ofReal, hSw]
      ring
    rw [hw, inner_smul_right] at h1
    linear_combination -h1
  have hcoef : (σ i : 𝕜) * ⟪e i, w⟫_𝕜 = (Real.sqrt c : 𝕜) * ⟪e i, w⟫_𝕜 := by
    rcases eq_or_ne (⟪e i, w⟫_𝕜) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    · have hsq : (σ i) ^ 2 = c := by
        have hz : ((σ i : 𝕜) ^ 2 - (c : 𝕜)) * ⟪e i, w⟫_𝕜 = 0 := by
          rw [sub_mul]; linear_combination hSSw
        rcases mul_eq_zero.mp hz with h | h
        · have : ((σ i) ^ 2 : 𝕜) = (c : 𝕜) := by linear_combination h
          exact_mod_cast this
        · exact absurd h h0
      rw [show Real.sqrt c = σ i by rw [← hsq, Real.sqrt_sq (hσnn i)]]
  rw [hSw, inner_smul_right, hcoef]

theorem positive_sqrt_unique {T R S : V →ₗ[𝕜] V} (hR : R.IsPositive) (hRT : R ∘ₗ R = T)
    (hS : S.IsPositive) (hST : S ∘ₗ S = T) : R = S := by
  have hTs : T.IsSymmetric := by
    rw [← hRT]; intro x y
    simp only [LinearMap.comp_apply]
    rw [hR.isSymmetric, hR.isSymmetric]
  have hTpos : T.IsPositive := by
    rw [← hRT]
    refine ⟨?_, fun x => ?_⟩
    · intro x y; simp only [LinearMap.comp_apply]; rw [hR.isSymmetric, hR.isSymmetric]
    · simp only [LinearMap.comp_apply]
      rw [hR.isSymmetric (R x) x, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
      positivity
  set n := Module.finrank 𝕜 V
  set b := hTs.eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) with hb
  set μ := hTs.eigenvalues (rfl : Module.finrank 𝕜 V = n) with hμ
  have hμnn : ∀ i, 0 ≤ μ i := by
    intro i
    have hev : HasEigenvalue T ((μ i : ℝ) : 𝕜) :=
      hTs.hasEigenvalue_eigenvalues (rfl : Module.finrank 𝕜 V = n) i
    have := (eigenvalue_nonneg hTpos hev).1
    rwa [RCLike.ofReal_re] at this
  apply b.toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis]
  have hwR : (R ∘ₗ R) (b i) = ((μ i : ℝ) : 𝕜) • b i := by
    rw [hRT]; exact hTs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i
  have hwS : (S ∘ₗ S) (b i) = ((μ i : ℝ) : 𝕜) • b i := by
    rw [hST]; exact hTs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i
  rw [sqrt_eigenvector hR (hμnn i) hwR, sqrt_eigenvector hS (hμnn i) hwS]

/-- The (positive) operator {lit}`S(x,y) = (x, 2y)` on {lit}`ℝ²` (Example 7.41). -/
def S_7_41 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun p := ![p 0, 2 * p 1]
  map_add' x y := by funext i; fin_cases i <;> simp; ring
  map_smul' a x := by funext i; fin_cases i <;> simp; ring

/-- Its positive square root {lit}`√S(x,y) = (x, √2·y)` (Example 7.41). -/
noncomputable def sqrtS_7_41 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun p := ![p 0, Real.sqrt 2 * p 1]
  map_add' x y := by funext i; fin_cases i <;> simp; ring
  map_smul' a x := by funext i; fin_cases i <;> simp; ring

/-- 7.41 Example: {lit}`√S` is a square root of {lit}`S`, i.e. {lit}`(√S)² = S`
(using {lit}`√2 · √2 = 2`). -/
theorem sqrtS_7_41_sq : sqrtS_7_41 ∘ₗ sqrtS_7_41 = S_7_41 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply LinearMap.ext; intro p; funext i
  fin_cases i
  · show sqrtS_7_41 (sqrtS_7_41 p) 0 = S_7_41 p 0
    simp [sqrtS_7_41, S_7_41]
  · show sqrtS_7_41 (sqrtS_7_41 p) 1 = S_7_41 p 1
    simp only [sqrtS_7_41, S_7_41, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [← mul_assoc, h2]

/-- 7.43 If {lit}`T` is a positive operator and {lit}`⟨Tv, v⟩ = 0`, then {lit}`Tv = 0`.
Writing {lit}`T = R²` with {lit}`R` a positive (hence self-adjoint) square root
(7.36), {lit}`0 = ⟨Tv, v⟩ = ⟨R(Rv), v⟩ = ⟨Rv, Rv⟩ = ‖Rv‖²`, so {lit}`Rv = 0` and
thus {lit}`Tv = R(Rv) = 0`. -/
theorem apply_eq_zero_of_isPositive_of_inner_eq_zero {T : V →ₗ[𝕜] V} (hT : T.IsPositive)
    {v : V} (hv : ⟪T v, v⟫_𝕜 = 0) : T v = 0 := by
  obtain ⟨R, hRpos, hRT⟩ := exists_positive_sqrt hT
  have hRR : ⟪R v, R v⟫_𝕜 = 0 := by
    rw [← hv, ← hRT, LinearMap.comp_apply]; exact (hRpos.1 (R v) v).symm
  have hRv : R v = 0 := inner_self_eq_zero.mp hRR
  rw [← hRT, LinearMap.comp_apply, hRv, map_zero]

/-! # Exercises 7C -/

/-- 7C.1 If both {lit}`T` and {lit}`−T` are positive, then {lit}`T = 0`. -/
theorem exercise_7C_1 (T : V →ₗ[𝕜] V) (hT : T.IsPositive) (hnT : (-T).IsPositive) :
    T = 0 := by
  sorry

/-- 7C.2 The tridiagonal operator on {lit}`𝔽⁴` with matrix
{lit}`[[2,−1,0,0],[−1,2,−1,0],[0,−1,2,−1],[0,0,−1,2]]` is an invertible positive
operator (its matrix is positive definite). -/
theorem exercise_7C_2 :
    (Matrix.of ![![2, -1, 0, 0], ![-1, 2, -1, 0], ![0, -1, 2, -1], ![0, 0, -1, 2]] :
      Matrix (Fin 4) (Fin 4) ℝ).PosDef := by
  sorry

/-- 7C.3 The operator on {lit}`𝔽ⁿ` whose matrix is all {lit}`1`s is a positive
operator (its matrix is positive semidefinite). -/
theorem exercise_7C_3 {n : ℕ} :
    (Matrix.of (fun _ _ => 1) : Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
  sorry

/-- 7C.4 For {lit}`n > 1` there is an {lit}`n×n` Hermitian matrix with all entries
positive whose operator is not positive. -/
theorem exercise_7C_4 {n : ℕ} (hn : 1 < n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 < A i j) ∧ A.IsHermitian ∧ ¬ A.PosSemidef := by
  sorry

/-- 7C.5 A self-adjoint {lit}`T` is positive iff for every orthonormal basis, all
diagonal entries {lit}`⟨T eₖ, eₖ⟩` of its matrix are nonnegative. -/
theorem exercise_7C_5 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) :
    T.IsPositive ↔ ∀ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V) (i : Fin n),
      0 ≤ RCLike.re ⟪e i, T (e i)⟫_𝕜 := by
  sorry

/-- 7C.6 The sum of two positive operators is positive. -/
theorem exercise_7C_6 (S T : V →ₗ[𝕜] V) (hS : S.IsPositive) (hT : T.IsPositive) :
    (S + T).IsPositive := by
  sorry

/-- 7C.7 If {lit}`S` is an invertible positive operator and {lit}`T` is positive,
then {lit}`S + T` is invertible. -/
theorem exercise_7C_7 (S T : V →ₗ[𝕜] V) (hS : S.IsPositive) (hSinv : Function.Bijective S)
    (hT : T.IsPositive) : Function.Bijective (S + T) := by
  sorry

/-- 7C.8 {lit}`T` is positive iff its pseudoinverse {lit}`T†` is positive. -/
theorem exercise_7C_8 (T : V →ₗ[𝕜] V) :
    T.IsPositive ↔ (LADR.Section_6C.pinv T).IsPositive := by
  sorry

/-- 7C.9 If {lit}`T` is positive on {lit}`V` and {lit}`S ∈ ℒ(W, V)`, then
{lit}`S* T S` is positive on {lit}`W`. -/
theorem exercise_7C_9 {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 W] (T : V →ₗ[𝕜] V) (hT : T.IsPositive) (S : W →ₗ[𝕜] V) :
    (LinearMap.adjoint S ∘ₗ T ∘ₗ S).IsPositive := by
  sorry

/-- 7C.10 If {lit}`T` is positive, {lit}`Tv = w` and {lit}`Tw = v`, then
{lit}`v = w`. -/
theorem exercise_7C_10 (T : V →ₗ[𝕜] V) (hT : T.IsPositive) (v w : V)
    (h1 : T v = w) (h2 : T w = v) : v = w := by
  sorry

/-- 7C.11 If {lit}`T` is positive and {lit}`U` is invariant, then {lit}`T|U` is
positive. -/
theorem exercise_7C_11 (T : V →ₗ[𝕜] V) (hT : T.IsPositive) (U : Submodule 𝕜 V)
    (hU : ∀ u ∈ U, T u ∈ U) : (T.restrict hU).IsPositive := by
  sorry

/-- 7C.12 If {lit}`T` is positive, then {lit}`Tᵏ` is positive for every positive
integer {lit}`k`. -/
theorem exercise_7C_12 (T : V →ₗ[𝕜] V) (hT : T.IsPositive) (k : ℕ) (hk : 0 < k) :
    (T ^ k).IsPositive := by
  sorry

/-- 7C.13 For self-adjoint {lit}`T` and {lit}`α ∈ ℝ`: (a) {lit}`T − αI` is positive
iff {lit}`α` is ≤ every eigenvalue; (b) {lit}`αI − T` is positive iff {lit}`α` is
≥ every eigenvalue. -/
theorem exercise_7C_13 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (α : ℝ) :
    ((T - (α : 𝕜) • LinearMap.id).IsPositive ↔
        ∀ μ : 𝕜, HasEigenvalue T μ → α ≤ RCLike.re μ) ∧
      (((α : 𝕜) • LinearMap.id - T).IsPositive ↔
        ∀ μ : 𝕜, HasEigenvalue T μ → RCLike.re μ ≤ α) := by
  sorry

/-- 7C.14 If {lit}`T` is positive and {lit}`v₁, …, vₘ ∈ V`, then
{lit}`∑ⱼ ∑ₖ ⟨T vₖ, vⱼ⟩ ≥ 0`. -/
theorem exercise_7C_14 (T : V →ₗ[𝕜] V) (hT : T.IsPositive) {m : ℕ} (v : Fin m → V) :
    0 ≤ RCLike.re (∑ j, ∑ k, ⟪v j, T (v k)⟫_𝕜) := by
  sorry

/-- 7C.15 For self-adjoint {lit}`T` there exist positive {lit}`A, B` with
{lit}`T = A − B`, {lit}`(A + B)² = T*T` (so {lit}`A + B = √(T*T)`), and
{lit}`AB = BA = 0`. -/
theorem exercise_7C_15 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) :
    ∃ A B : V →ₗ[𝕜] V, A.IsPositive ∧ B.IsPositive ∧ T = A - B ∧
      (A + B) ∘ₗ (A + B) = LinearMap.adjoint T ∘ₗ T ∧ A ∘ₗ B = 0 ∧ B ∘ₗ A = 0 := by
  sorry

/-- 7C.16 For positive {lit}`T` with positive square root {lit}`R` ({lit}`R² = T`),
{lit}`null R = null T` and {lit}`range R = range T`. -/
theorem exercise_7C_16 (T R : V →ₗ[𝕜] V) (hT : T.IsPositive) (hR : R.IsPositive)
    (hRT : R ∘ₗ R = T) :
    LinearMap.ker R = LinearMap.ker T ∧ LinearMap.range R = LinearMap.range T := by
  sorry

/-- 7C.17 For positive {lit}`T` with positive square root {lit}`R`, there is a
real-coefficient polynomial {lit}`p` with {lit}`R = p(T)`. -/
theorem exercise_7C_17 (T R : V →ₗ[𝕜] V) (hT : T.IsPositive) (hR : R.IsPositive)
    (hRT : R ∘ₗ R = T) :
    ∃ p : Polynomial ℝ, R = Polynomial.aeval T (p.map (algebraMap ℝ 𝕜)) := by
  sorry

/-- 7C.18 For positive {lit}`S, T`, the product {lit}`ST` is positive iff
{lit}`S` and {lit}`T` commute. -/
theorem exercise_7C_18 (S T : V →ₗ[𝕜] V) (hS : S.IsPositive) (hT : T.IsPositive) :
    (S ∘ₗ T).IsPositive ↔ S ∘ₗ T = T ∘ₗ S := by
  sorry

/-- 7C.19 The identity operator on {lit}`𝔽²` has infinitely many self-adjoint
square roots. -/
theorem exercise_7C_19 :
    {R : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) |
      LinearMap.IsSymmetric R ∧ R ∘ₗ R = LinearMap.id}.Infinite := by
  sorry

/-- 7C.20 {lit}`T` is positive iff there exist {lit}`v₁, …, vₙ` with
{lit}`⟨T eₖ, eⱼ⟩ = ⟨vₖ, vⱼ⟩` for an orthonormal basis {lit}`e` (Gram/Cholesky
characterization). -/
theorem exercise_7C_20 {n : ℕ} (T : V →ₗ[𝕜] V) (e : OrthonormalBasis (Fin n) 𝕜 V) :
    T.IsPositive ↔ ∃ v : Fin n → V, ∀ j k, ⟪e j, T (e k)⟫_𝕜 = ⟪v j, v k⟫_𝕜 := by
  sorry

/-- 7C.21 The {lit}`n×n` Hilbert matrix ({lit}`1/(j+k−1)` entries) gives a positive
invertible operator (its matrix is positive definite). -/
theorem exercise_7C_21 {n : ℕ} (hn : 0 < n) :
    (Matrix.of (fun j k : Fin n => (1 : ℝ) / ((j : ℝ) + (k : ℝ) + 1))).PosDef := by
  sorry

/-- 7C.22 If {lit}`T` is positive, {lit}`‖u‖ = 1`, and {lit}`u` maximizes
{lit}`‖Tv‖` over unit vectors, then {lit}`u` is an eigenvector for the largest
eigenvalue. -/
theorem exercise_7C_22 (T : V →ₗ[𝕜] V) (hT : T.IsPositive) (u : V) (hu : ‖u‖ = 1)
    (hmax : ∀ v, ‖v‖ = 1 → ‖T v‖ ≤ ‖T u‖) :
    ∃ μ : 𝕜, T u = μ • u ∧
      ∀ ν : 𝕜, HasEigenvalue T ν → RCLike.re ν ≤ RCLike.re μ := by
  sorry

/-- 7C.23 (a) {lit}`⟨u, v⟩_T = ⟨T u, v⟩` is an inner product iff {lit}`T` is an
invertible positive operator. -/
theorem exercise_7C_23a (T : V →ₗ[𝕜] V) :
    (∃ core : InnerProductSpace.Core 𝕜 V, ∀ u v : V, core.inner u v = ⟪T u, v⟫_𝕜) ↔
      (T.IsPositive ∧ Function.Bijective T) := by
  sorry

/-- 7C.23 (b) Every inner product on {lit}`V` is of the form
{lit}`⟨u, v⟩_T = ⟨T u, v⟩` for some positive invertible {lit}`T`. -/
theorem exercise_7C_23b (core : InnerProductSpace.Core 𝕜 V) :
    ∃ T : V →ₗ[𝕜] V, T.IsPositive ∧ Function.Bijective T ∧
      ∀ u v : V, core.inner u v = ⟪T u, v⟫_𝕜 := by
  sorry

/-- 7C.24 For positive {lit}`S, T`, {lit}`null(S + T) = null S ∩ null T`. -/
theorem exercise_7C_24 (S T : V →ₗ[𝕜] V) (hS : S.IsPositive) (hT : T.IsPositive) :
    LinearMap.ker (S + T) = LinearMap.ker S ⊓ LinearMap.ker T := by
  sorry

/-! 7C.25 (deferred): for the second-derivative operator {lit}`T` of Exercise
7A.31(b), {lit}`−T` is a positive operator. Depends on the trigonometric
{lit}`L²` function space of 7A.31, which is itself deferred. -/

end LADR.Section_7C
