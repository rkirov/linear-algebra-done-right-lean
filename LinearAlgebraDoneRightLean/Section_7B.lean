import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLin
import LinearAlgebraDoneRightLean.Section_7A
import LinearAlgebraDoneRightLean.Section_6B
import LinearAlgebraDoneRightLean.Section_6C
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7B: Spectral Theorem
-/

namespace LADR.Section_7B

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)
open LADR.Section_3D (IsInvertible)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-! # Real Spectral Theorem -/

/-! 7.26 Invertible quadratic expressions

If {lit}`T ∈ ℒ(V)` is self-adjoint and {lit}`b, c ∈ ℝ` satisfy {lit}`b² < 4c`,
then {lit}`T² + bT + cI` is invertible. Axler's proof runs through positivity:
{lit}`⟨(T² + bT + cI)v, v⟩ > 0` for {lit}`v ≠ 0`, which forces injectivity and
hence (in finite dimensions) invertibility. We record the positivity step as
{lit}`quadratic_pos` and the conclusion itself as {lit}`quadratic_isInvertible`. -/

omit [FiniteDimensional 𝕜 V] in
theorem quadratic_pos (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (b c : ℝ)
    (hbc : b ^ 2 < 4 * c) (v : V) (hv : v ≠ 0) :
    0 < RCLike.re ⟪(T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) v,
      v⟫_𝕜 := by
  have hinner : ⟪(T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) v, v⟫_𝕜
      = ((‖T v‖ ^ 2 : ℝ) : 𝕜) + (b : 𝕜) * ⟪T v, v⟫_𝕜 + ((c * ‖v‖ ^ 2 : ℝ) : 𝕜) := by
    rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_left,
      LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_smul_left, inner_smul_left, hT (T v) v, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, RCLike.conj_ofReal, RCLike.conj_ofReal]
    push_cast
    ring
  rw [hinner, map_add, map_add, RCLike.ofReal_re, RCLike.re_ofReal_mul, RCLike.ofReal_re]
  have hcs : RCLike.re ⟪T v, v⟫_𝕜 ^ 2 ≤ ‖T v‖ ^ 2 * ‖v‖ ^ 2 := by
    have h1 : ‖⟪T v, v⟫_𝕜‖ ≤ ‖T v‖ * ‖v‖ := norm_inner_le_norm (T v) v
    have h2 : |RCLike.re ⟪T v, v⟫_𝕜| ≤ ‖T v‖ * ‖v‖ :=
      le_trans (RCLike.abs_re_le_norm _) h1
    nlinarith [sq_abs (RCLike.re ⟪T v, v⟫_𝕜), norm_nonneg (T v), norm_nonneg v,
      abs_nonneg (RCLike.re ⟪T v, v⟫_𝕜)]
  have hs : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith [hcs, hbc, hs, sq_nonneg (‖v‖ ^ 2 * b + 2 * RCLike.re ⟪T v, v⟫_𝕜),
    mul_pos hs hs]

/-- 7.26 If {lit}`T` is self-adjoint and {lit}`b² < 4c`, then {lit}`T² + bT + cI`
is invertible. -/
theorem quadratic_isInvertible (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (b c : ℝ)
    (hbc : b ^ 2 < 4 * c) :
    IsInvertible (T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) := by
  refine (Section_3D.isInvertible_iff_injective rfl _).mpr fun x y hxy => ?_
  by_contra hne
  have hpos := quadratic_pos T hT b c hbc (x - y) (sub_ne_zero.mpr hne)
  rw [map_sub, hxy, sub_self, inner_zero_left, map_zero] at hpos
  exact lt_irrefl 0 hpos

/-! 7.27 The minimal polynomial of a self-adjoint operator (over {lit}`ℝ`) is a
product of the linear factors {lit}`(z − λ₁) ⋯ (z − λₘ)` — i.e. it splits over
{lit}`ℝ`. -/

open Polynomial in
theorem minpoly_symmetric_splits {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V)
    (hT : T.IsSymmetric) :
    (minpoly ℝ T).Splits := by
  set b := hT.eigenvectorBasis (rfl : Module.finrank ℝ V = Module.finrank ℝ V) with hb
  set μ := hT.eigenvalues (rfl : Module.finrank ℝ V = Module.finrank ℝ V) with hμ
  set S := Finset.image μ Finset.univ with hS
  set p := ∏ lam ∈ S, (X - C lam) with hp
  have hp0 : p ≠ 0 := by
    rw [hp]; exact Finset.prod_ne_zero_iff.mpr fun lam _ => X_sub_C_ne_zero lam
  have hpsplit : p.Splits :=
    Polynomial.Splits.prod (fun lam _ => Polynomial.Splits.X_sub_C lam)
  have haeval : (aeval T) p = 0 := by
    apply b.toBasis.ext
    intro i
    simp only [LinearMap.zero_apply]
    have hiS : μ i ∈ S := Finset.mem_image_of_mem μ (Finset.mem_univ i)
    rw [hp, ← Finset.prod_erase_mul S _ hiS, map_mul, Module.End.mul_apply]
    have hkill : (aeval T) (X - C (μ i)) (b.toBasis i) = 0 := by
      simp only [OrthonormalBasis.coe_toBasis]
      simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
      rw [hT.apply_eigenvectorBasis (rfl : Module.finrank ℝ V = Module.finrank ℝ V) i]
      simp [hb, hμ]
    rw [hkill, map_zero]
  exact Polynomial.Splits.of_dvd hpsplit hp0 (minpoly.dvd ℝ T haeval)

/-! 7.29 Real spectral theorem

For {lit}`𝔽 = ℝ`, an operator {lit}`T` is self-adjoint if and only if {lit}`V`
has an orthonormal basis consisting of eigenvectors of {lit}`T` (equivalently,
{lit}`T` has a diagonal matrix with respect to some orthonormal basis).

The substantive direction — every self-adjoint operator is orthonormally
diagonalizable — is mathlib's spectral theorem, available uniformly over
{lit}`ℝ` and {lit}`ℂ` (over {lit}`ℂ` it is the self-adjoint case of the complex
spectral theorem). mathlib packages the eigenbasis as
{name}`LinearMap.IsSymmetric.eigenvectorBasis`. -/

theorem spectral_orthonormal_eigenbasis (T : V →ₗ[𝕜] V)
    (hT : LinearMap.IsSymmetric T) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V, ∀ i, ∃ μ : 𝕜, T (b i) = μ • b i :=
  ⟨hT.eigenvectorBasis rfl,
    fun i => ⟨(hT.eigenvalues rfl i : 𝕜), hT.apply_eigenvectorBasis rfl i⟩⟩

/-- The eigenvalues in the spectral decomposition are real, as expected for a
self-adjoint operator (7.12). -/
theorem spectral_eigenvalues_real (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (i : Fin (finrank 𝕜 V)) :
    T (hT.eigenvectorBasis rfl i) =
      ((hT.eigenvalues rfl i : ℝ) : 𝕜) • hT.eigenvectorBasis rfl i :=
  hT.apply_eigenvectorBasis rfl i

/-! # Complex Spectral Theorem -/

/-! 7.30 Example: an orthonormal basis of eigenvectors (real case). For the
self-adjoint operator on {lit}`ℝ³` with matrix {lit}`!![14,-13,8; -13,14,8; 8,8,-7]`,
the vectors {lit}`(1,-1,0), (1,1,1), (1,1,-2)` (normalized by {lit}`√2, √3, √6`)
form an orthonormal basis of eigenvectors, with eigenvalues {lit}`27, 9, -15`. This
illustrates the real spectral theorem 7.29. We verify each eigenvalue equation and
the pairwise orthogonality and squared norms of the three vectors. -/

section Example_7_30

open scoped Matrix

/-- Real scalar inner product is multiplication (used to compute coordinate inner
products below). -/
private theorem rinner (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by rw [real_inner_comm]; rfl

/-- The self-adjoint matrix of Example 7.30. -/
noncomputable def A_7_30 : Matrix (Fin 3) (Fin 3) ℝ := !![14, -13, 8; -13, 14, 8; 8, 8, -7]

/-- The eigenvector {lit}`(1, -1, 0)` (eigenvalue {lit}`27`). -/
noncomputable def v_7_30_a : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm ![1, -1, 0]
/-- The eigenvector {lit}`(1, 1, 1)` (eigenvalue {lit}`9`). -/
noncomputable def v_7_30_b : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm ![1, 1, 1]
/-- The eigenvector {lit}`(1, 1, -2)` (eigenvalue {lit}`-15`). -/
noncomputable def v_7_30_c : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm ![1, 1, -2]

theorem A_7_30_eigenvalue_27 : Matrix.toEuclideanLin A_7_30 v_7_30_a = (27 : ℝ) • v_7_30_a := by
  ext i; fin_cases i <;> simp [A_7_30, v_7_30_a, Matrix.toEuclideanLin] <;> norm_num
theorem A_7_30_eigenvalue_9 : Matrix.toEuclideanLin A_7_30 v_7_30_b = (9 : ℝ) • v_7_30_b := by
  ext i; fin_cases i <;> simp [A_7_30, v_7_30_b, Matrix.toEuclideanLin] <;> norm_num
theorem A_7_30_eigenvalue_neg15 :
    Matrix.toEuclideanLin A_7_30 v_7_30_c = (-15 : ℝ) • v_7_30_c := by
  ext i; fin_cases i <;> simp [A_7_30, v_7_30_c, Matrix.toEuclideanLin] <;> norm_num

theorem v_7_30_ortho_ab : ⟪v_7_30_a, v_7_30_b⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]; simp [rinner, v_7_30_a, v_7_30_b, Fin.sum_univ_three]
theorem v_7_30_ortho_ac : ⟪v_7_30_a, v_7_30_c⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]; simp [rinner, v_7_30_a, v_7_30_c, Fin.sum_univ_three]
theorem v_7_30_ortho_bc : ⟪v_7_30_b, v_7_30_c⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]; simp [rinner, v_7_30_b, v_7_30_c, Fin.sum_univ_three]; norm_num
theorem v_7_30_normSq_a : ⟪v_7_30_a, v_7_30_a⟫_ℝ = 2 := by
  rw [PiLp.inner_apply]; simp [v_7_30_a, Fin.sum_univ_three]; norm_num
theorem v_7_30_normSq_b : ⟪v_7_30_b, v_7_30_b⟫_ℝ = 3 := by
  rw [PiLp.inner_apply]; simp [v_7_30_b, Fin.sum_univ_three]; norm_num
theorem v_7_30_normSq_c : ⟪v_7_30_c, v_7_30_c⟫_ℝ = 6 := by
  rw [PiLp.inner_apply]; simp [v_7_30_c, Fin.sum_univ_three]; norm_num

end Example_7_30

/-! 7.31 Complex spectral theorem

For {lit}`𝔽 = ℂ`, an operator {lit}`T` is normal if and only if {lit}`V` has an
orthonormal basis consisting of eigenvectors of {lit}`T`. Axler's proof runs
through Schur's theorem (6.38, from
{module -checked}`LinearAlgebraDoneRightLean.Section_6B`): a normal operator that
is upper-triangular with respect to an orthonormal basis is in fact diagonal. -/

/-- A normal operator that is upper-triangular with respect to an orthonormal
basis {lit}`e` is diagonal: each {lit}`eₖ` is an eigenvector. The proof compares
{lit}`‖T eₖ‖² = ∑ᵢ ‖⟨eᵢ, T eₖ⟩‖²` (column {lit}`k`) with
{lit}`‖T* eₖ‖² = ∑ᵢ ‖⟨eₖ, T eᵢ⟩‖²` (row {lit}`k`); equality (7.20) plus an
induction from the top row forces every strictly-upper entry to vanish. -/
theorem normal_ut_diagonal {n : ℕ} (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (e : OrthonormalBasis (Fin n) 𝕜 V)
    (hUT : ∀ k, T (e k) ∈ Submodule.span 𝕜 (e '' {i | i ≤ k})) :
    ∀ k, T (e k) = ⟪e k, T (e k)⟫_𝕜 • e k := by
  set a : Fin n → Fin n → 𝕜 := fun i j => ⟪e i, T (e j)⟫_𝕜 with ha
  have hUTz : ∀ i j : Fin n, j < i → a i j = 0 := by
    intro i j hji
    have hmem : T (e j) ∈ Submodule.span 𝕜 (e '' {l | l ≤ j}) := hUT j
    have horth : e i ∈ (Submodule.span 𝕜 (e '' {l | l ≤ j}))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      have hle : Submodule.span 𝕜 (e '' {l | l ≤ j}) ≤ (𝕜 ∙ e i)ᗮ := by
        rw [Submodule.span_le]
        rintro _ ⟨l, hlj, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
        exact e.orthonormal.2 (fun h => absurd (h ▸ hlj) (not_le.mpr hji))
      have hyi := hle hy
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hyi
      exact hyi
    simp only [ha]
    exact inner_eq_zero_symm.mpr (Submodule.inner_right_of_mem_orthogonal hmem horth)
  have hParsT : ∀ k, ‖T (e k)‖ ^ 2 = ∑ i, ‖a i k‖ ^ 2 := by
    intro k
    simp only [ha]
    exact (OrthonormalBasis.sum_sq_norm_inner_right e (T (e k))).symm
  have hParsA : ∀ k, ‖LinearMap.adjoint T (e k)‖ ^ 2 = ∑ i, ‖a k i‖ ^ 2 := by
    intro k
    rw [← OrthonormalBasis.sum_sq_norm_inner_right e (LinearMap.adjoint T (e k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha]
    rw [LinearMap.adjoint_inner_right]
    congr 1
    exact norm_inner_symm (T (e i)) (e k)
  have hN2 : ∀ v, ‖T v‖ = ‖LinearMap.adjoint T v‖ := (LADR.Section_7A.normal_iff_norm T).mp hN
  have hQaux : ∀ m : ℕ, ∀ k : Fin n, k.val = m → ∀ j : Fin n, k < j → a k j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro k hk j hkj
      have IHk : ∀ i : Fin n, i < k → a i k = 0 := fun i hik =>
        IH i.val (by rw [← hk]; exact Fin.lt_def.mp hik) i rfl k hik
      have hcol : ∑ i, ‖a i k‖ ^ 2 = ‖a k k‖ ^ 2 := by
        rw [Finset.sum_eq_single k]
        · intro i _ hik
          rcases lt_or_gt_of_ne hik with h | h
          · rw [IHk i h, norm_zero]; ring
          · rw [hUTz i k h, norm_zero]; ring
        · intro h; exact absurd (Finset.mem_univ k) h
      have hnorm_eq : ∑ i, ‖a i k‖ ^ 2 = ∑ i, ‖a k i‖ ^ 2 := by
        rw [← hParsT k, ← hParsA k, hN2 (e k)]
      have hsum_eq : ∑ i, ‖a k i‖ ^ 2 = ‖a k k‖ ^ 2 := by rw [← hnorm_eq, hcol]
      have hzero : ∑ i ∈ Finset.univ.erase k, ‖a k i‖ ^ 2 = 0 := by
        have hae := Finset.add_sum_erase Finset.univ (fun i => ‖a k i‖ ^ 2) (Finset.mem_univ k)
        rw [hsum_eq] at hae
        linarith
      have hjmem : j ∈ Finset.univ.erase k :=
        Finset.mem_erase.mpr ⟨(ne_of_lt hkj).symm, Finset.mem_univ j⟩
      have hj0 : ‖a k j‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hzero j hjmem
      have hjn : ‖a k j‖ = 0 := by nlinarith [norm_nonneg (a k j)]
      rwa [norm_eq_zero] at hjn
  have hQ : ∀ k : Fin n, ∀ j : Fin n, k < j → a k j = 0 := fun k => hQaux k.val k rfl
  intro k
  have hexp : T (e k) = ∑ i, a i k • e i := by
    simp only [ha]
    exact (e.sum_repr' (T (e k))).symm
  conv_lhs => rw [hexp]
  rw [Finset.sum_eq_single k (fun i _ hik => by
        rcases lt_or_gt_of_ne hik with h | h
        · rw [hQ i k h, zero_smul]
        · rw [hUTz i k h, zero_smul])
      (fun h => absurd (Finset.mem_univ k) h)]

/-- 7.31 (Complex spectral theorem) Every normal operator on a finite-dimensional
complex inner product space has an orthonormal basis of eigenvectors. -/
theorem complex_spectral {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (hN : IsStarNormal T) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ W),
      ∀ k, T (e k) = ⟪e k, T (e k)⟫_ℂ • e k := by
  obtain ⟨n, e, he, hUT⟩ := LADR.Section_6B.exists_orthonormal_upperTriangular_complex T
  have hflag : ∀ k, T (e k) ∈ Submodule.span ℂ (e '' {i | i ≤ k}) :=
    ((LADR.Section_5C.tfae_upperTriangular he T).out 0 2).mp hUT
  exact ⟨n, e, normal_ut_diagonal T hN e hflag⟩

/-! 7.33 Example: an orthonormal basis of eigenvectors (complex case). For the
normal operator {lit}`T(w, z) = (2w - 3z, 3w + 2z)` on {lit}`ℂ²` (matrix
{lit}`!![2,-3; 3,2]`), the vectors {lit}`(i, 1), (-i, 1)` (normalized by {lit}`√2`)
form an orthonormal basis of eigenvectors, with eigenvalues {lit}`2 + 3i, 2 - 3i`.
This illustrates the complex spectral theorem 7.31. -/

section Example_7_33

open scoped Matrix

/-- The normal matrix of Example 7.33. -/
noncomputable def A_7_33 : Matrix (Fin 2) (Fin 2) ℂ := !![2, -3; 3, 2]

/-- The eigenvector {lit}`(i, 1)` (eigenvalue {lit}`2 + 3i`). -/
noncomputable def v_7_33_a : EuclideanSpace ℂ (Fin 2) := (WithLp.equiv 2 _).symm ![Complex.I, 1]
/-- The eigenvector {lit}`(-i, 1)` (eigenvalue {lit}`2 - 3i`). -/
noncomputable def v_7_33_b : EuclideanSpace ℂ (Fin 2) := (WithLp.equiv 2 _).symm ![-Complex.I, 1]

theorem A_7_33_eigenvalue_add :
    Matrix.toEuclideanLin A_7_33 v_7_33_a = (2 + 3 * Complex.I) • v_7_33_a := by
  ext i; fin_cases i <;> simp [A_7_33, v_7_33_a, Matrix.toEuclideanLin, Complex.ext_iff]
theorem A_7_33_eigenvalue_sub :
    Matrix.toEuclideanLin A_7_33 v_7_33_b = (2 - 3 * Complex.I) • v_7_33_b := by
  ext i; fin_cases i <;> simp [A_7_33, v_7_33_b, Matrix.toEuclideanLin, Complex.ext_iff]

theorem v_7_33_ortho : ⟪v_7_33_a, v_7_33_b⟫_ℂ = 0 := by
  rw [PiLp.inner_apply]; simp [v_7_33_a, v_7_33_b, Fin.sum_univ_two]
theorem v_7_33_normSq_a : ⟪v_7_33_a, v_7_33_a⟫_ℂ = 2 := by
  rw [PiLp.inner_apply]; simp [v_7_33_a, Fin.sum_univ_two, Complex.ext_iff]; norm_num
theorem v_7_33_normSq_b : ⟪v_7_33_b, v_7_33_b⟫_ℂ = 2 := by
  rw [PiLp.inner_apply]; simp [v_7_33_b, Fin.sum_univ_two, Complex.ext_iff]; norm_num

end Example_7_33

/-! # Exercises 7B -/

/-- 7B.1 A normal operator on a complex inner product space is self-adjoint iff
all its eigenvalues are real. -/
theorem exercise_7B_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    LinearMap.IsSymmetric T ↔ ∀ μ : ℂ, HasEigenvalue T μ → conj μ = μ := by
  sorry

/-- 7B.2 A normal operator on a complex inner product space with only one
eigenvalue is a scalar multiple of the identity. -/
theorem exercise_7B_2 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T)
    (μ : ℂ) (hμ : ∀ ν : ℂ, HasEigenvalue T ν ↔ ν = μ) :
    T = μ • LinearMap.id := by
  sorry

/-- 7B.3 For normal {lit}`T` on a complex inner product space, the eigenvalues lie
in {lit}`{0, 1}` iff {lit}`T = P_U` for some subspace {lit}`U`. -/
theorem exercise_7B_3 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    (∀ μ : ℂ, HasEigenvalue T μ → μ = 0 ∨ μ = 1) ↔
      ∃ U : Submodule ℂ V, (U.starProjection : V →ₗ[ℂ] V) = T := by
  sorry

/-- 7B.4 A normal operator on a complex inner product space is skew
({lit}`T* = −T`) iff all its eigenvalues are purely imaginary. -/
theorem exercise_7B_4 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    LinearMap.adjoint T = -T ↔ ∀ μ : ℂ, HasEigenvalue T μ → μ.re = 0 := by
  sorry

/-- 7B.5 Counterexample: a diagonalizable operator on {lit}`ℂ³` need not be
normal with respect to the usual inner product. -/
theorem exercise_7B_5 :
    ¬ ∀ T : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3),
      (∃ b : Module.Basis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)),
        ∀ i, ∃ μ : ℂ, T (b i) = μ • b i) → IsStarNormal T := by
  sorry

/-- 7B.6 If {lit}`T` is normal on a complex inner product space and {lit}`T⁹ = T⁸`,
then {lit}`T` is self-adjoint and {lit}`T² = T`. -/
theorem exercise_7B_6 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) (h : T ^ 9 = T ^ 8) :
    LinearMap.IsSymmetric T ∧ T ^ 2 = T := by
  sorry

/-- 7B.7 There is an operator on a complex vector space with {lit}`T⁹ = T⁸` but
{lit}`T² ≠ T`. -/
theorem exercise_7B_7 :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V)
      (T : V →ₗ[ℂ] V), T ^ 9 = T ^ 8 ∧ T ^ 2 ≠ T := by
  sorry

/-- 7B.8 For {lit}`𝔽 = ℂ`, {lit}`T` is normal iff every eigenvector of {lit}`T` is
also an eigenvector of {lit}`T*`. -/
theorem exercise_7B_8 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔ ∀ (v : V) (μ : ℂ), v ≠ 0 → T v = μ • v →
      ∃ ν : ℂ, LinearMap.adjoint T v = ν • v := by
  sorry

/-- 7B.9 For {lit}`𝔽 = ℂ`, {lit}`T` is normal iff {lit}`T* = p(T)` for some
polynomial {lit}`p ∈ 𝒫(ℂ)`. -/
theorem exercise_7B_9 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔ ∃ p : Polynomial ℂ, LinearMap.adjoint T = Polynomial.aeval T p := by
  sorry

/-- 7B.10 Every normal operator on a complex inner product space has a square
root. -/
theorem exercise_7B_10 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    ∃ S : V →ₗ[ℂ] V, S ^ 2 = T := by
  sorry

/-- 7B.11 Every self-adjoint operator on {lit}`V` has a cube root. -/
theorem exercise_7B_11 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) :
    ∃ S : V →ₗ[𝕜] V, S ^ 3 = T := by
  sorry

/-- 7B.12 (Fuglede) For normal {lit}`T` on a complex inner product space, any
{lit}`S` commuting with {lit}`T` also commutes with {lit}`T*`. -/
theorem exercise_7B_12 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T S : V →ₗ[ℂ] V) (hN : IsStarNormal T)
    (h : S ∘ₗ T = T ∘ₗ S) :
    S ∘ₗ LinearMap.adjoint T = LinearMap.adjoint T ∘ₗ S := by
  sorry

/-- 7B.13 (Via Schur for two commuting operators) Every normal operator on a
complex inner product space has an orthonormal basis of eigenvectors. -/
theorem exercise_7B_13 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V), ∀ k, ∃ μ : ℂ, T (e k) = μ • e k := by
  sorry

/-- 7B.14 For {lit}`𝔽 = ℝ`, {lit}`T` is self-adjoint iff eigenvectors for distinct
eigenvalues are orthogonal and the eigenspaces span {lit}`V`. -/
theorem exercise_7B_14 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) :
    LinearMap.IsSymmetric T ↔
      ((∀ (μ ν : ℝ) (u v : V), μ ≠ ν → T u = μ • u → T v = ν • v → ⟪u, v⟫_ℝ = 0) ∧
        (⨆ μ : ℝ, Module.End.eigenspace T μ) = ⊤) := by
  sorry

/-- 7B.15 For {lit}`𝔽 = ℂ`, {lit}`T` is normal iff eigenvectors for distinct
eigenvalues are orthogonal and the eigenspaces span {lit}`V`. -/
theorem exercise_7B_15 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔
      ((∀ (μ ν : ℂ) (u v : V), μ ≠ ν → T u = μ • u → T v = ν • v → ⟪u, v⟫_ℂ = 0) ∧
        (⨆ μ : ℂ, Module.End.eigenspace T μ) = ⊤) := by
  sorry

/-- 7B.16 For {lit}`𝔽 = ℂ` and {lit}`ℰ ⊆ ℒ(V)`, there is an orthonormal basis
diagonalizing every element of {lit}`ℰ` iff all pairs in {lit}`ℰ` are commuting
normal operators. -/
theorem exercise_7B_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ℰ : Set (V →ₗ[ℂ] V)) :
    (∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V),
        ∀ T ∈ ℰ, ∀ k, ∃ μ : ℂ, T (e k) = μ • e k) ↔
      (∀ S ∈ ℰ, ∀ T ∈ ℰ, IsStarNormal S ∧ IsStarNormal T ∧ S ∘ₗ T = T ∘ₗ S) := by
  sorry

/-- 7B.17 For {lit}`𝔽 = ℝ` and {lit}`ℰ ⊆ ℒ(V)`, there is an orthonormal basis
diagonalizing every element of {lit}`ℰ` iff all pairs in {lit}`ℰ` are commuting
self-adjoint operators. -/
theorem exercise_7B_17 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (ℰ : Set (V →ₗ[ℝ] V)) :
    (∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℝ V),
        ∀ T ∈ ℰ, ∀ k, ∃ μ : ℝ, T (e k) = μ • e k) ↔
      (∀ S ∈ ℰ, ∀ T ∈ ℰ,
        LinearMap.IsSymmetric S ∧ LinearMap.IsSymmetric T ∧ S ∘ₗ T = T ∘ₗ S) := by
  sorry

/-- 7B.18 The self-adjoint hypothesis in 7.26 cannot be dropped: there is a real
inner product space operator {lit}`T` and {lit}`b, c` with {lit}`b² < 4c` making
{lit}`T² + bT + cI` non-invertible. -/
theorem exercise_7B_18 :
    ∃ (T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) (b c : ℝ),
      b ^ 2 < 4 * c ∧
      ¬ Function.Bijective (T ∘ₗ T + b • T +
        c • (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))) := by
  sorry

/-- 7B.19 If {lit}`T` is self-adjoint and {lit}`U` is invariant, then (a) {lit}`U⟂`
is invariant and (b) {lit}`T|U` is self-adjoint. -/
theorem exercise_7B_19 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    (∀ w ∈ Uᗮ, T w ∈ Uᗮ) ∧ LinearMap.IsSymmetric (T.restrict hU) := by
  sorry

/-- 7B.20 If {lit}`T` is normal and {lit}`U` is invariant, then (a) {lit}`U⟂` is
invariant, (b) {lit}`U` is invariant under {lit}`T*`, and (d) {lit}`T|U` is
normal. -/
theorem exercise_7B_20 (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    (∀ w ∈ Uᗮ, T w ∈ Uᗮ) ∧ (∀ u ∈ U, LinearMap.adjoint T u ∈ U) ∧
      IsStarNormal (T.restrict hU) := by
  sorry

/-- 7B.21 If {lit}`T` is self-adjoint with {lit}`2, 3` its only eigenvalues, then
{lit}`T² − 5T + 6I = 0`. -/
theorem exercise_7B_21 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (h : ∀ μ : 𝕜, HasEigenvalue T μ ↔ μ = 2 ∨ μ = 3) :
    T ∘ₗ T - (5 : 𝕜) • T + (6 : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V) = 0 := by
  sorry

/-- 7B.22 There is an operator on {lit}`ℂ³` with {lit}`2, 3` its only eigenvalues
but {lit}`T² − 5T + 6I ≠ 0`. -/
theorem exercise_7B_22 :
    ∃ T : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3),
      (∀ μ : ℂ, HasEigenvalue T μ ↔ μ = 2 ∨ μ = 3) ∧
      T ∘ₗ T - (5 : ℂ) • T +
        (6 : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) ≠ 0 := by
  sorry

/-- 7B.23 If {lit}`T` is self-adjoint and {lit}`‖Tv − λv‖ < ε` for some unit
{lit}`v`, then {lit}`T` has an eigenvalue within {lit}`ε` of {lit}`λ`. -/
theorem exercise_7B_23 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (μ : 𝕜)
    (ε : ℝ) (hε : 0 < ε) (v : V) (hv : ‖v‖ = 1) (hlt : ‖T v - μ • v‖ < ε) :
    ∃ μ' : 𝕜, HasEigenvalue T μ' ∧ ‖μ - μ'‖ < ε := by
  sorry

/-- 7B.24 (a) For {lit}`𝔽 = ℝ`, {lit}`T` is diagonalizable iff some basis gives a
matrix equal to its transpose. -/
theorem exercise_7B_24a {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (T : U →ₗ[ℝ] U) :
    (∃ b : Module.Basis (Fin (finrank ℝ U)) ℝ U, ∀ i, ∃ μ : ℝ, T (b i) = μ • b i) ↔
      ∃ b : Module.Basis (Fin (finrank ℝ U)) ℝ U,
        (LinearMap.toMatrix b b T).transpose = LinearMap.toMatrix b b T := by
  sorry

/-- 7B.24 (b) For {lit}`𝔽 = ℂ`, {lit}`T` is diagonalizable iff some basis gives a
matrix commuting with its conjugate transpose. -/
theorem exercise_7B_24b {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] (T : U →ₗ[ℂ] U) :
    (∃ b : Module.Basis (Fin (finrank ℂ U)) ℂ U, ∀ i, ∃ μ : ℂ, T (b i) = μ • b i) ↔
      ∃ b : Module.Basis (Fin (finrank ℂ U)) ℂ U,
        LinearMap.toMatrix b b T * (LinearMap.toMatrix b b T).conjTranspose =
          (LinearMap.toMatrix b b T).conjTranspose * LinearMap.toMatrix b b T := by
  sorry

/-- 7B.25 For {lit}`T` with orthonormal eigenbasis {lit}`e` and eigenvalues
{lit}`λ`, the pseudoinverse satisfies {lit}`T† eₖ = (1/λₖ) eₖ` if {lit}`λₖ ≠ 0`,
else {lit}`0`. -/
theorem exercise_7B_25 {n : ℕ} (T : V →ₗ[𝕜] V) (e : OrthonormalBasis (Fin n) 𝕜 V)
    (lam : Fin n → 𝕜) (he : ∀ k, T (e k) = lam k • e k) (k : Fin n) :
    LADR.Section_6C.pinv T (e k) = (if lam k = 0 then 0 else (lam k)⁻¹ • e k) := by
  sorry

end LADR.Section_7B
