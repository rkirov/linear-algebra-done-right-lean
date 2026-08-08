import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.FieldTheory.Minpoly.Field
import LinearAlgebraDoneRightLean.Section_6C
import LinearAlgebraDoneRightLean.Section_7B
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7C: Positive Operators
-/

namespace LADR.Section_7C

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module.End (HasEigenvalue)
open LADR.Section_5A (InvariantUnder)

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
the proof of 7.26"). For (a) the quadratic form is
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

omit [FiniteDimensional 𝕜 V] in
/-- 7.35(b): the orthogonal projection {lit}`P_U` is a positive operator —
{lit}`P_U` is self-adjoint (6C.19) and {lit}`⟨P_U v, v⟩ = ⟨P_U v, P_U v⟩ = ‖P_U v‖² ≥ 0`
because {lit}`P_U` is idempotent. -/
theorem starProjection_isPositive (U : Submodule 𝕜 V) [U.HasOrthogonalProjection] :
    (U.starProjection : V →ₗ[𝕜] V).IsPositive := by
  set P : V →ₗ[𝕜] V := (U.starProjection : V →ₗ[𝕜] V) with hP
  have hsymm : P.IsSymmetric := fun x y => U.inner_starProjection_left_eq_right x y
  refine ⟨hsymm, fun v => ?_⟩
  have hidem : P (P v) = P v :=
    Submodule.starProjection_eq_self_iff.mpr (U.starProjection_apply_mem v)
  have hself : ⟪P v, v⟫_𝕜 = ⟪P v, P v⟫_𝕜 := by
    conv_lhs => rw [← hidem]
    exact hsymm (P v) v
  rw [hself, inner_self_eq_norm_sq_to_K]
  simp

omit [FiniteDimensional 𝕜 V] in
/-- 7.35(c): if {lit}`T` is self-adjoint and {lit}`b² < 4c`, then
{lit}`T² + bT + cI` is a positive operator — the positivity of the quadratic form is
exactly the step in the proof of 7.26 ({name}`LADR.Section_7B.quadratic_pos`). -/
theorem quadratic_isPositive (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (b c : ℝ)
    (hbc : b ^ 2 < 4 * c) :
    (T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)).IsPositive := by
  constructor
  · intro x y
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_ofReal, hT _ _]
  · intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (Section_7B.quadratic_pos T hT b c hbc v hv).le

/-! 7.36 Definition: square root

{lit}`R` is a *square root* of {lit}`T` if {lit}`R² = T`. The notion is purely
algebraic — no inner product is involved — so we state it for an operator on any
module, which lets Example 7.37 use it on {lit}`ℂ³` with the plain (non-Euclidean)
module structure. -/

def IsSquareRoot {F : Type*} [Semiring F] {W : Type*} [AddCommMonoid W] [Module F W]
    (R T : W →ₗ[F] W) : Prop := R ∘ₗ R = T

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
theorem R_7_37_sq : IsSquareRoot R_7_37 T_7_37 := by
  ext z i
  fin_cases i <;> simp [R_7_37, T_7_37]

/-! 7.38 Characterizations of positive operators

For {lit}`T ∈ ℒ(V)` the following are equivalent: (a) {lit}`T` is positive;
(b) {lit}`T` is self-adjoint and all eigenvalues of {lit}`T` are nonnegative;
(c) with respect to some orthonormal basis of {lit}`V` the matrix of {lit}`T` is
diagonal with only nonnegative numbers on the diagonal; (d) {lit}`T` has a
positive square root; (e) {lit}`T` has a self-adjoint square root; (f)
{lit}`T = R* R` for some {lit}`R ∈ ℒ(V)`.

Each implication of the cycle (a) ⟹ (b) ⟹ (c) ⟹ (d) ⟹ (e) ⟹ (f) ⟹ (a) is
proved separately below, and {lit}`tfae_isPositive` assembles them into the
equivalence. -/

/-- Condition (c) of 7.38: with respect to some orthonormal basis of {lit}`V`, the
matrix of {lit}`T` is a diagonal matrix with only nonnegative numbers on the
diagonal. -/
def HasNonnegDiagonalMatrix (T : V →ₗ[𝕜] V) : Prop :=
  ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V) (d : Fin n → ℝ), (∀ i, 0 ≤ d i) ∧
    LinearMap.toMatrixOrthonormal e T = Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)

/-- Reading a diagonal matrix as eigenvalue equations: if the matrix of {lit}`T`
with respect to {lit}`e` is {lit}`diagonal d`, then each {lit}`e i` is an
eigenvector with eigenvalue {lit}`d i`. -/
theorem apply_eq_smul_of_toMatrixOrthonormal_eq_diagonal {n : ℕ} {T : V →ₗ[𝕜] V}
    (e : OrthonormalBasis (Fin n) 𝕜 V) {d : Fin n → 𝕜}
    (h : LinearMap.toMatrixOrthonormal e T = Matrix.diagonal d) (i : Fin n) :
    T (e i) = d i • e i := by
  have hentry : ∀ j, ⟪e j, T (e i)⟫_𝕜 = if j = i then d i else 0 := by
    intro j
    rw [← LinearMap.toMatrixOrthonormal_apply_apply e T j i, h, Matrix.diagonal_apply]
    rcases eq_or_ne j i with rfl | hji
    · simp
    · simp [hji]
  conv_lhs => rw [← e.sum_repr' (T (e i))]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [hentry j, if_neg hj, zero_smul])
    (fun hi => absurd (Finset.mem_univ i) hi), hentry i, if_pos rfl]

/-- The converse reading: eigenvalue equations along an orthonormal basis make the
matrix diagonal. -/
theorem toMatrixOrthonormal_eq_diagonal {n : ℕ} {T : V →ₗ[𝕜] V}
    (e : OrthonormalBasis (Fin n) 𝕜 V) {d : Fin n → 𝕜} (h : ∀ i, T (e i) = d i • e i) :
    LinearMap.toMatrixOrthonormal e T = Matrix.diagonal d := by
  ext j i
  rw [LinearMap.toMatrixOrthonormal_apply_apply, h i, inner_smul_right,
    orthonormal_iff_ite.mp e.orthonormal j i, Matrix.diagonal_apply]
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [hji]

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

/-! 7.38 (b) ⟹ (c) The spectral theorem turns "self-adjoint with nonnegative
eigenvalues" into a diagonal matrix with nonnegative diagonal: take mathlib's
orthonormal eigenbasis and read off the eigenvalues. -/

/-- (b) ⟹ (c). -/
theorem hasNonnegDiagonalMatrix_of_eigenvalue_nonneg {T : V →ₗ[𝕜] V}
    (hs : T.IsSymmetric) (hev : ∀ μ : 𝕜, HasEigenvalue T μ → 0 ≤ RCLike.re μ) :
    HasNonnegDiagonalMatrix T := by
  set n := Module.finrank 𝕜 V
  refine ⟨n, hs.eigenvectorBasis (rfl : Module.finrank 𝕜 V = n),
    hs.eigenvalues (rfl : Module.finrank 𝕜 V = n), fun i => ?_,
    toMatrixOrthonormal_eq_diagonal _ fun i =>
      hs.apply_eigenvectorBasis (rfl : Module.finrank 𝕜 V = n) i⟩
  have := hev _ (hs.hasEigenvalue_eigenvalues (rfl : Module.finrank 𝕜 V = n) i)
  rwa [RCLike.ofReal_re] at this

/-! 7.38 (c) ⟹ (d) An operator that is diagonal with nonnegative diagonal
{lit}`λ₁, …, λₙ` in some orthonormal basis has a positive square root: the
operator {lit}`R` acting as {lit}`√λⱼ` on the {lit}`j`-th basis vector. -/

/-- (c) ⟹ (d). -/
theorem exists_positive_sqrt_of_hasNonnegDiagonalMatrix {T : V →ₗ[𝕜] V}
    (h : HasNonnegDiagonalMatrix T) :
    ∃ R : V →ₗ[𝕜] V, R.IsPositive ∧ IsSquareRoot R T := by
  obtain ⟨n, b, μ, hμnn, hdiag⟩ := h
  have hTb : ∀ i, T (b i) = ((μ i : ℝ) : 𝕜) • b i :=
    apply_eq_smul_of_toMatrixOrthonormal_eq_diagonal b hdiag
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
  · show R ∘ₗ R = T
    apply b.toBasis.ext
    intro i
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
    rw [hRb, map_smul, hRb, smul_smul]
    rw [show (Real.sqrt (μ i) : 𝕜) * (Real.sqrt (μ i) : 𝕜) = ((μ i : ℝ) : 𝕜) by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hμnn i)]]
    rw [← hTb i]

/-! 7.38 The remaining two links of the cycle are immediate: a positive operator
is self-adjoint ((d) ⟹ (e)), and a self-adjoint {lit}`R` equals its own adjoint,
so {lit}`R² = R* R` ((e) ⟹ (f)). -/

/-- (e) ⟹ (f): a self-adjoint square root {lit}`R` of {lit}`T` exhibits
{lit}`T = R* R`. -/
theorem adjoint_comp_self_eq_of_isSymmetric_isSquareRoot {T R : V →ₗ[𝕜] V}
    (hR : R.IsSymmetric) (hRT : IsSquareRoot R T) : LinearMap.adjoint R ∘ₗ R = T := by
  have hadj : LinearMap.adjoint R = R := by
    rw [← LinearMap.star_eq_adjoint]
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint R).mp hR
  rw [hadj]
  exact hRT

/-- 7.38 Characterizations of positive operators: for {lit}`T ∈ ℒ(V)` the six
conditions (a)–(f) are equivalent, proved as the cycle
(a) ⟹ (b) ⟹ (c) ⟹ (d) ⟹ (e) ⟹ (f) ⟹ (a). -/
theorem tfae_isPositive (T : V →ₗ[𝕜] V) :
    [T.IsPositive,
      T.IsSymmetric ∧ ∀ μ : 𝕜, HasEigenvalue T μ → 0 ≤ RCLike.re μ ∧ conj μ = μ,
      HasNonnegDiagonalMatrix T,
      ∃ R : V →ₗ[𝕜] V, R.IsPositive ∧ IsSquareRoot R T,
      ∃ R : V →ₗ[𝕜] V, R.IsSymmetric ∧ IsSquareRoot R T,
      ∃ R : V →ₗ[𝕜] V, LinearMap.adjoint R ∘ₗ R = T].TFAE := by
  tfae_have 1 → 2 := fun hT => ⟨hT.isSymmetric, fun _ hμ => eigenvalue_nonneg hT hμ⟩
  tfae_have 2 → 3 := fun h =>
    hasNonnegDiagonalMatrix_of_eigenvalue_nonneg h.1 fun μ hμ => (h.2 μ hμ).1
  tfae_have 3 → 4 := exists_positive_sqrt_of_hasNonnegDiagonalMatrix
  tfae_have 4 → 5 := fun ⟨R, hR, hRT⟩ => ⟨R, hR.isSymmetric, hRT⟩
  tfae_have 5 → 6 := fun ⟨R, hR, hRT⟩ =>
    ⟨R, adjoint_comp_self_eq_of_isSymmetric_isSquareRoot hR hRT⟩
  tfae_have 6 → 1 := fun ⟨R, hRT⟩ => hRT ▸ adjoint_comp_self_isPositive R
  tfae_finish

/-- 7.38 (a) ⟹ (d), the direction usually cited on its own: every positive
operator has a positive square root. -/
theorem exists_positive_sqrt {T : V →ₗ[𝕜] V} (hT : T.IsPositive) :
    ∃ R : V →ₗ[𝕜] V, R.IsPositive ∧ R ∘ₗ R = T :=
  ((tfae_isPositive T).out 0 3).mp hT

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

/-! 7.41 Example: square roots of positive operators

Axler works out two operators on {lit}`𝐑²` with the usual Euclidean inner
product: {lit}`S(x,y) = (x, 2y)` and {lit}`T(x,y) = (x + y, x + y)`. Both are
self-adjoint (7.42: their matrices in the standard basis, {lit}`!![1,0;0,2]` and
{lit}`!![1,1;1,1]`, equal their own transposes) and both have nonnegative
quadratic form ({lit}`x² + 2y²` and {lit}`(x + y)²`), so both are positive. Their
square roots are {lit}`√S(x,y) = (x, √2·y)` and
{lit}`√T(x,y) = ((x+y)/√2, (x+y)/√2)`; each is itself positive, so by 7.39 it
really is *the* square root denoted {lit}`√S`, {lit}`√T` in 7.40. -/

/-- The operator {lit}`S(x,y) = (x, 2y)` on {lit}`𝐑²` (Example 7.41). -/
def S_7_41 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := !₂[p 0, 2 * p 1]
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' a x := by ext i; fin_cases i <;> simp; ring

/-- The operator {lit}`T(x,y) = (x + y, x + y)` on {lit}`𝐑²` (Example 7.41). -/
def T_7_41 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := !₂[p 0 + p 1, p 0 + p 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

/-- {lit}`√S(x,y) = (x, √2·y)` (Example 7.41). -/
noncomputable def sqrtS_7_41 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := !₂[p 0, Real.sqrt 2 * p 1]
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' a x := by ext i; fin_cases i <;> simp; ring

/-- {lit}`√T(x,y) = ((x+y)/√2, (x+y)/√2)` (Example 7.41). -/
noncomputable def sqrtT_7_41 : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := !₂[(p 0 + p 1) / Real.sqrt 2, (p 0 + p 1) / Real.sqrt 2]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

/-- 7.42 The matrices of {lit}`S` and {lit}`T` with respect to the standard basis
of {lit}`𝐑²`: {lit}`!![1,0;0,2]` and {lit}`!![1,1;1,1]`. Each equals its own
transpose, so {lit}`S` and {lit}`T` are self-adjoint. -/
theorem matrix_7_42 :
    Matrix.toEuclideanLin (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ) = S_7_41 ∧
      Matrix.toEuclideanLin (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) ℝ) = T_7_41 := by
  constructor <;>
    (ext p i
     fin_cases i <;>
       simp [S_7_41, T_7_41, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail])

/-- The quadratic form of {lit}`S`: {lit}`⟨S(x,y),(x,y)⟩ = x² + 2y²`. -/
theorem inner_S_7_41 (p : EuclideanSpace ℝ (Fin 2)) :
    ⟪S_7_41 p, p⟫_ℝ = p 0 ^ 2 + 2 * p 1 ^ 2 := by
  simp [S_7_41, PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℝ]
  ring

/-- The quadratic form of {lit}`T`: {lit}`⟨T(x,y),(x,y)⟩ = (x + y)²`. -/
theorem inner_T_7_41 (p : EuclideanSpace ℝ (Fin 2)) :
    ⟪T_7_41 p, p⟫_ℝ = (p 0 + p 1) ^ 2 := by
  simp [T_7_41, PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℝ]
  ring

/-- 7.41: {lit}`S` is a positive operator. -/
theorem S_7_41_isPositive : S_7_41.IsPositive := by
  constructor
  · intro x y
    simp [S_7_41, PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℝ]
    ring
  · intro p
    rw [inner_S_7_41, RCLike.re_to_real]
    positivity

/-- 7.41: {lit}`T` is a positive operator. -/
theorem T_7_41_isPositive : T_7_41.IsPositive := by
  constructor
  · intro x y
    simp [T_7_41, PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℝ]
    ring
  · intro p
    rw [inner_T_7_41, RCLike.re_to_real]
    positivity

/-- 7.41 Example: {lit}`√S` is a square root of {lit}`S`, i.e. {lit}`(√S)² = S`
(using {lit}`√2 · √2 = 2`). -/
theorem sqrtS_7_41_sq : IsSquareRoot sqrtS_7_41 S_7_41 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  show sqrtS_7_41 ∘ₗ sqrtS_7_41 = S_7_41
  ext p i
  fin_cases i <;> simp [sqrtS_7_41, S_7_41, ← mul_assoc, h2]

/-- 7.41 Example: {lit}`√T` is a square root of {lit}`T`, i.e. {lit}`(√T)² = T`. -/
theorem sqrtT_7_41_sq : IsSquareRoot sqrtT_7_41 T_7_41 := by
  show sqrtT_7_41 ∘ₗ sqrtT_7_41 = T_7_41
  ext p i
  fin_cases i <;>
    (simp [sqrtT_7_41, T_7_41]; field_simp; rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring)

/-- The quadratic form of {lit}`√S`: {lit}`⟨√S(x,y),(x,y)⟩ = x² + √2·y²`. -/
theorem inner_sqrtS_7_41 (p : EuclideanSpace ℝ (Fin 2)) :
    ⟪sqrtS_7_41 p, p⟫_ℝ = p 0 ^ 2 + Real.sqrt 2 * p 1 ^ 2 := by
  simp [sqrtS_7_41, PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℝ]
  ring

/-- The quadratic form of {lit}`√T`: {lit}`⟨√T(x,y),(x,y)⟩ = (x + y)²/√2`. -/
theorem inner_sqrtT_7_41 (p : EuclideanSpace ℝ (Fin 2)) :
    ⟪sqrtT_7_41 p, p⟫_ℝ = (p 0 + p 1) ^ 2 / Real.sqrt 2 := by
  simp [sqrtT_7_41, PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℝ]
  ring

/-- 7.41: {lit}`√S` is itself positive, so by 7.39 it is *the* positive square
root of {lit}`S`. -/
theorem sqrtS_7_41_isPositive : sqrtS_7_41.IsPositive := by
  constructor
  · intro x y
    simp [sqrtS_7_41, PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℝ]
    ring
  · intro p
    rw [inner_sqrtS_7_41, RCLike.re_to_real]
    positivity

/-- 7.41: {lit}`√T` is itself positive, so by 7.39 it is *the* positive square
root of {lit}`T`. -/
theorem sqrtT_7_41_isPositive : sqrtT_7_41.IsPositive := by
  constructor
  · intro x y
    simp [sqrtT_7_41, PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_re_inner ℝ]
    ring
  · intro p
    rw [inner_sqrtT_7_41, RCLike.re_to_real]
    positivity

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
    (hU : InvariantUnder T U) : hU.restrict.IsPositive := by
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

open LADR.Section_7A (trigSpan) in
/-- 7C.25 For the second-derivative operator {lit}`T f = f″` of Exercise 7A.31(b),
{lit}`−T` is a positive operator. -/
theorem exercise_7C_25 (n : ℕ) (T : trigSpan n →ₗ[ℝ] trigSpan n)
    (hT : ∀ f : trigSpan n, (T f : ℝ → ℝ) = deriv (deriv (f : ℝ → ℝ))) :
    (-T).IsPositive := by
  sorry

end LADR.Section_7C
