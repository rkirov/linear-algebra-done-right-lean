import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Notation
import LinearAlgebraDoneRightLean.Section_7B
import LinearAlgebraDoneRightLean.Section_7C
import LinearAlgebraDoneRightLean.Section_7D
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7E: Singular Value Decomposition
-/

namespace LADR.Section_7E

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate Matrix
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! # Singular Values -/

/-! 7.64 Properties of {lit}`T* T`

For {lit}`T ∈ ℒ(V, W)`: (a) {lit}`T* T` is a positive operator on {lit}`V`;
(b) {lit}`null (T* T) = null T`; (c) {lit}`range (T* T) = range T*`;
(d) {lit}`dim range T = dim range T* = dim range (T* T)`. Axler proves this first
because the whole section rests on it — the singular values of 7.65 are defined from the
eigenvalues of {lit}`T* T`, which (a) makes nonnegative.

All four parts are in mathlib, whose own docstrings cite this result by number:
{name}`LinearMap.isPositive_adjoint_comp_self`, {name}`LinearMap.ker_adjoint_comp_self`
(7.64(b)), {name}`LinearMap.range_adjoint_comp_self` (7.64(c)) and
{name}`LinearMap.finrank_range_adjoint` (part of 7.64(d)), so the items below record
Axler's statements in his phrasing. -/

/-- 7.64(a) {lit}`T* T` is a positive operator on {lit}`V`, for any {lit}`T ∈ ℒ(V, W)`.
The endomorphism case is {name}`LADR.Section_7C.adjoint_comp_self_isPositive`. -/
theorem adjComp_self_isPositive (T : V →ₗ[𝕜] W) :
    (LinearMap.adjoint T ∘ₗ T).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self T

/-- 7.64(b) {lit}`null (T* T) = null T`. Axler's proof: {lit}`T* T v = 0` gives
{lit}`‖T v‖² = ⟨T* T v, v⟩ = 0`; the other inclusion is immediate. -/
theorem ker_adjComp_self (T : V →ₗ[𝕜] W) :
    LinearMap.ker (LinearMap.adjoint T ∘ₗ T) = LinearMap.ker T :=
  LinearMap.ker_adjoint_comp_self T

/-- 7.64(c) {lit}`range (T* T) = range T*`. Axler's proof: {lit}`T* T` is self-adjoint by
(a), so {lit}`range (T* T) = (null (T* T))⟂ = (null T)⟂ = range T*` using (b) and 7.6. -/
theorem range_adjComp_self (T : V →ₗ[𝕜] W) :
    LinearMap.range (LinearMap.adjoint T ∘ₗ T) = LinearMap.range (LinearMap.adjoint T) :=
  LinearMap.range_adjoint_comp_self T

/-- 7.64(d) {lit}`dim range T = dim range T* = dim range (T* T)`; the second equality is
(c). -/
theorem finrank_range_adjComp_self (T : V →ₗ[𝕜] W) :
    finrank 𝕜 (LinearMap.range T) = finrank 𝕜 (LinearMap.range (LinearMap.adjoint T)) ∧
      finrank 𝕜 (LinearMap.range (LinearMap.adjoint T)) =
        finrank 𝕜 (LinearMap.range (LinearMap.adjoint T ∘ₗ T)) :=
  ⟨(LinearMap.finrank_range_adjoint T).symm, by rw [range_adjComp_self]⟩

/-! 7.65 Definition: singular values

The *singular values* of {lit}`T ∈ ℒ(V, W)` are the nonnegative square roots of
the eigenvalues of the positive operator {lit}`T* T` (positive by 7.64(a) /
{lit}`adjComp_self_isPositive`), each repeated according to
the dimension of the corresponding eigenspace.

We index the singular values by the orthonormal eigenbasis {lit}`e` of {lit}`T* T`
supplied by the spectral theorem ({name}`LinearMap.IsSymmetric.eigenvectorBasis`),
so {lit}`singularValues T : Fin (finrank 𝕜 V) → ℝ` with
{lit}`singularValues T i = √(λᵢ)` where {lit}`λᵢ` is the eigenvalue of
{lit}`T* T` on {lit}`eᵢ`. This captures the multiset of singular values *with
multiplicity* (one value per basis vector); Axler additionally lists them in
decreasing order, an ordering choice we do not track here as it plays no role in
the results below. -/

/-- The orthonormal eigenbasis of {lit}`T* T` used throughout this section. -/
noncomputable def svdBasis (T : V →ₗ[𝕜] W) :
    OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V :=
  (adjComp_self_isPositive T).isSymmetric.eigenvectorBasis rfl

/-- The singular values of {lit}`T`, indexed by {lit}`svdBasis T`. -/
noncomputable def singularValues (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) : ℝ :=
  Real.sqrt ((adjComp_self_isPositive T).isSymmetric.eigenvalues rfl i)

theorem singularValues_nonneg (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) :
    0 ≤ singularValues T i :=
  Real.sqrt_nonneg _

/-- The eigenvalues of the positive operator {lit}`T* T` are nonnegative (7.64(a)). -/
theorem eigenvalues_nonneg (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) :
    0 ≤ (adjComp_self_isPositive T).isSymmetric.eigenvalues rfl i := by
  have hpos := adjComp_self_isPositive T
  have hev : HasEigenvalue (LinearMap.adjoint T ∘ₗ T)
      ((hpos.isSymmetric.eigenvalues rfl i : ℝ) : 𝕜) :=
    hpos.isSymmetric.hasEigenvalue_eigenvalues rfl i
  have := (LADR.Section_7C.eigenvalue_nonneg hpos hev).1
  rwa [RCLike.ofReal_re] at this

/-- The square of a singular value recovers the eigenvalue of {lit}`T* T`. -/
theorem singularValues_sq (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) :
    (singularValues T i) ^ 2 =
      (adjComp_self_isPositive T).isSymmetric.eigenvalues rfl i :=
  Real.sq_sqrt (eigenvalues_nonneg T i)

/-- The spectral theorem applied to the positive operator {lit}`T* T`: the eigenbasis
vectors satisfy {lit}`T* T eₖ = sₖ² eₖ`. Axler numbers this equation 7.72, inside the proof
of 7.70, but it is available as soon as 7.65's eigenbasis exists and 7.68/7.69 below rest on
it, so it is stated here with the rest of the 7.65 machinery. -/
theorem adjComp_apply_svdBasis (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) :
    (LinearMap.adjoint T ∘ₗ T) (svdBasis T i) =
      (((singularValues T i) ^ 2 : ℝ) : 𝕜) • svdBasis T i := by
  rw [singularValues_sq]
  exact (adjComp_self_isPositive T).isSymmetric.apply_eigenvectorBasis rfl i

theorem svdBasis_ne_zero (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) : svdBasis T i ≠ 0 := by
  intro h
  have := (svdBasis T).orthonormal.1 i
  rw [h, norm_zero] at this
  norm_num at this

/-! The key orthogonality computation, Axler's equation 7.73 in the proof of 7.70.
Writing {lit}`eₖ = svdBasis T k`,
{lit}`⟨T eⱼ, T eₖ⟩ = ⟨eⱼ, T* T eₖ⟩ = sₖ² ⟨eⱼ, eₖ⟩`, which is {lit}`sₖ²` when
{lit}`j = k` and {lit}`0` otherwise. -/
theorem inner_image_svdBasis (T : V →ₗ[𝕜] W) (j k : Fin (finrank 𝕜 V)) :
    ⟪T (svdBasis T j), T (svdBasis T k)⟫_𝕜 =
      if j = k then (((singularValues T k) ^ 2 : ℝ) : 𝕜) else 0 := by
  rw [← LinearMap.adjoint_inner_left, ← LinearMap.comp_apply, adjComp_apply_svdBasis,
    inner_smul_left, RCLike.conj_ofReal,
    orthonormal_iff_ite.mp (svdBasis T).orthonormal j k]
  rcases eq_or_ne j k with h | h
  · subst h; rw [if_pos rfl, if_pos rfl, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- {lit}`‖T eₖ‖ = sₖ`. -/
theorem norm_image_svdBasis (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) :
    ‖T (svdBasis T i)‖ = singularValues T i := by
  have h := inner_image_svdBasis T i i
  rw [if_pos rfl, inner_self_eq_norm_sq_to_K] at h
  have h2 : (‖T (svdBasis T i)‖) ^ 2 = (singularValues T i) ^ 2 := by
    have hre := congrArg RCLike.re h
    rwa [← RCLike.ofReal_pow, RCLike.ofReal_re, RCLike.ofReal_re] at hre
  rw [← Real.sqrt_sq (norm_nonneg (T (svdBasis T i))), h2,
    Real.sqrt_sq (singularValues_nonneg T i)]

/-! 7.66 Example: singular values of an operator on {lit}`𝔽⁴`

For {lit}`T(z₁, z₂, z₃, z₄) = (0, 3z₁, 2z₂, −3z₄)` on {lit}`𝔽⁴`, Axler computes
{lit}`T* T(z₁, z₂, z₃, z₄) = (9z₁, 4z₂, 0, 9z₄)` ("as you should verify"), reads off the
eigenvalues {lit}`9, 4, 0` of {lit}`T* T` with
{lit}`dim E(9, T* T) = 2`, {lit}`dim E(4, T* T) = 1`, {lit}`dim E(0, T* T) = 1`, and
concludes that the singular values of {lit}`T` are {lit}`3, 3, 2, 0`. The point of the
example: the only eigenvalues of {lit}`T` itself are {lit}`−3` and {lit}`0`, so the
eigenvalues miss the {lit}`2` that governs {lit}`T`'s behaviour, while the singular values
see it.

We define {lit}`T` through its matrix in the standard basis, which makes {lit}`T* T` the
matrix product {lit}`Aᴴ A`. -/

/-- The matrix of the operator of Example 7.66 in the standard basis of {lit}`𝔽⁴`: its
columns are {lit}`T e₁ = (0,3,0,0)`, {lit}`T e₂ = (0,0,2,0)`, {lit}`T e₃ = 0` and
{lit}`T e₄ = (0,0,0,−3)`. -/
def A_7_66 : Matrix (Fin 4) (Fin 4) 𝕜 :=
  !![0, 0, 0, 0;
     3, 0, 0, 0;
     0, 2, 0, 0;
     0, 0, 0, -3]

/-- The operator {lit}`T(z₁, z₂, z₃, z₄) = (0, 3z₁, 2z₂, −3z₄)` of Example 7.66. -/
noncomputable def T_7_66 : EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4) :=
  Matrix.toEuclideanLin A_7_66

/-- 7.66 {lit}`T(z₁, z₂, z₃, z₄) = (0, 3z₁, 2z₂, −3z₄)`, coordinate by coordinate. -/
theorem T_7_66_apply (z : EuclideanSpace 𝕜 (Fin 4)) :
    T_7_66 z 0 = 0 ∧ T_7_66 z 1 = 3 * z 0 ∧ T_7_66 z 2 = 2 * z 1 ∧
      T_7_66 z 3 = -3 * z 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [T_7_66, A_7_66, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_four]

/-- 7.66 The matrix form of the computation Axler leaves to the reader:
{lit}`Aᴴ A = diag(9, 4, 0, 9)`. -/
theorem conjTranspose_mul_A_7_66 :
    (A_7_66 (𝕜 := 𝕜))ᴴ * A_7_66 (𝕜 := 𝕜) = Matrix.diagonal ![9, 4, 0, 9] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A_7_66, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_four,
      Matrix.diagonal_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
      Matrix.vecTail, map_ofNat, map_neg, map_zero, map_one]

/-- 7.66 The computation Axler leaves to the reader:
{lit}`T* T(z₁, z₂, z₃, z₄) = (9z₁, 4z₂, 0, 9z₄)`, so the standard basis diagonalizes
{lit}`T* T`. -/
theorem adjComp_T_7_66_apply (z : EuclideanSpace 𝕜 (Fin 4)) :
    (LinearMap.adjoint T_7_66 ∘ₗ T_7_66) z 0 = 9 * z 0 ∧
      (LinearMap.adjoint T_7_66 ∘ₗ T_7_66) z 1 = 4 * z 1 ∧
      (LinearMap.adjoint T_7_66 ∘ₗ T_7_66) z 2 = 0 ∧
      (LinearMap.adjoint T_7_66 ∘ₗ T_7_66) z 3 = 9 * z 3 := by
  have hadj : LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) = Matrix.toEuclideanLin (A_7_66 (𝕜 := 𝕜))ᴴ := by
    rw [T_7_66, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [LinearMap.comp_apply, hadj, T_7_66, Matrix.toLpLin_apply, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, Matrix.mulVec_mulVec, conjTranspose_mul_A_7_66]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- 7.66 {lit}`T* T` *is* the diagonal operator {lit}`diag(9, 4, 0, 9)`: the operator form of
{name}`conjTranspose_mul_A_7_66`, which is what lets the eigenvalues be read off. -/
theorem adjComp_T_7_66_eq :
    LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66 =
      Matrix.toEuclideanLin (Matrix.diagonal ![(9 : 𝕜), 4, 0, 9]) := by
  have hadj : LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) = Matrix.toEuclideanLin (A_7_66 (𝕜 := 𝕜))ᴴ := by
    rw [T_7_66, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hmul : ∀ M P : Matrix (Fin 4) (Fin 4) 𝕜,
      (M * P).toEuclideanLin = M.toEuclideanLin ∘ₗ P.toEuclideanLin := by
    intro M P; ext v
    simp only [LinearMap.comp_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec]
  rw [hadj, T_7_66, ← hmul, conjTranspose_mul_A_7_66]

/-- 7.66 The eigenvalues of {lit}`T* T` are exactly {lit}`9, 4, 0`, read off the diagonal
form {name}`adjComp_T_7_66_eq` via {name}`spectrum_diagonal`. -/
theorem hasEigenvalue_adjComp_T_7_66 (μ : 𝕜) :
    HasEigenvalue (LinearMap.adjoint T_7_66 ∘ₗ T_7_66) μ ↔ μ = 9 ∨ μ = 4 ∨ μ = 0 := by
  rw [adjComp_T_7_66_eq, Module.End.hasEigenvalue_iff_mem_spectrum,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.spectrum_toLin, spectrum_diagonal]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- 7.66 The eigenspace dimensions {lit}`dim E(9, T* T) = 2`, {lit}`dim E(4, T* T) = 1`,
{lit}`dim E(0, T* T) = 1`, which is what turns the eigenvalue *set* into Axler's list
{lit}`3, 3, 2, 0` with multiplicity. -/
theorem finrank_eigenspace_adjComp_T_7_66 :
    finrank 𝕜 (Module.End.eigenspace (LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66) 9) = 2 ∧
      finrank 𝕜
          (Module.End.eigenspace (LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66) 4) = 1 ∧
      finrank 𝕜
          (Module.End.eigenspace (LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66) 0) = 1 := by
  sorry

/-- 7.66 The singular values of {lit}`T` are {lit}`3, 3, 2, 0` — as a multiset, i.e. with
multiplicity, which is how 7.65 lists them. (This pin's
{name}`LinearMap.IsSymmetric.eigenvalues` are sorted decreasingly, so
{name}`singularValues` is in fact already Axler's decreasing list; the multiset form avoids
transporting along {lit}`finrank 𝕜 (EuclideanSpace 𝕜 (Fin 4)) = 4`.) -/
theorem singularValues_T_7_66 :
    Multiset.map (singularValues (T_7_66 (𝕜 := 𝕜))) Finset.univ.val = {3, 3, 2, 0} := by
  sorry

/-! 7.67 Example: singular values of a linear map from {lit}`𝔽⁴` to {lit}`𝔽³`

For the {lit}`T ∈ ℒ(𝔽⁴, 𝔽³)` with matrix {lit}`!![0,0,0,-5; 0,0,0,0; 1,1,0,0]` in the
standard bases, the matrix of {lit}`T* T` is {lit}`!![1,1,0,0; 1,1,0,0; 0,0,0,0; 0,0,0,25]`,
whose eigenvalues are {lit}`25, 2, 0` with {lit}`dim E(25, T* T) = 1`,
{lit}`dim E(2, T* T) = 1` and {lit}`dim E(0, T* T) = 2`; so the singular values of
{lit}`T` are {lit}`5, √2, 0, 0`. -/

/-- The matrix of the map of Example 7.67. -/
def A_7_67 : Matrix (Fin 3) (Fin 4) 𝕜 :=
  !![0, 0, 0, -5;
     0, 0, 0, 0;
     1, 1, 0, 0]

/-- The map {lit}`T ∈ ℒ(𝔽⁴, 𝔽³)` of Example 7.67. -/
noncomputable def T_7_67 : EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3) :=
  Matrix.toEuclideanLin A_7_67

/-- 7.67 The matrix of {lit}`T* T` is {lit}`!![1,1,0,0; 1,1,0,0; 0,0,0,0; 0,0,0,25]`
("you can verify"). -/
theorem conjTranspose_mul_A_7_67 :
    (A_7_67 (𝕜 := 𝕜))ᴴ * A_7_67 (𝕜 := 𝕜) =
      !![1, 1, 0, 0;
         1, 1, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A_7_67, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
      map_ofNat, map_neg, map_zero, map_one]

/-- 7.67 The eigenvalues of {lit}`T* T` are {lit}`25, 2, 0`, with
{lit}`dim E(25, T* T) = 1`, {lit}`dim E(2, T* T) = 1` and {lit}`dim E(0, T* T) = 2`. -/
theorem eigenvalues_adjComp_T_7_67 :
    (∀ μ : 𝕜, HasEigenvalue (LinearMap.adjoint T_7_67 ∘ₗ T_7_67) μ ↔ μ = 25 ∨ μ = 2 ∨ μ = 0) ∧
      finrank 𝕜
          (Module.End.eigenspace (LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) ∘ₗ T_7_67) 25) = 1 ∧
      finrank 𝕜
          (Module.End.eigenspace (LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) ∘ₗ T_7_67) 2) = 1 ∧
      finrank 𝕜
          (Module.End.eigenspace (LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) ∘ₗ T_7_67) 0) = 2 := by
  sorry

/-- 7.67 The singular values of {lit}`T` are {lit}`5, √2, 0, 0`, as a multiset. -/
theorem singularValues_T_7_67 :
    Multiset.map (singularValues (T_7_67 (𝕜 := 𝕜))) Finset.univ.val =
      {5, Real.sqrt 2, 0, 0} := by
  sorry


/-! # Role of Positive Singular Values -/

/-- The pointwise reading of 7.64(b) ({name}`ker_adjComp_self`): {lit}`T* T v = 0 ⟺ T v = 0`.
Convenient in the arguments below. -/
theorem adjComp_eq_zero_iff (T : V →ₗ[𝕜] W) (v : V) :
    (LinearMap.adjoint T ∘ₗ T) v = 0 ↔ T v = 0 := by
  rw [← LinearMap.mem_ker, ← LinearMap.mem_ker, ker_adjComp_self]

/-- If all singular values are nonzero then {lit}`T* T` is injective. -/
theorem adjComp_injective (T : V →ₗ[𝕜] W) (hs : ∀ i, singularValues T i ≠ 0) :
    Function.Injective (LinearMap.adjoint T ∘ₗ T) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have hzero : ∀ i, ⟪svdBasis T i, v⟫_𝕜 = 0 := by
    intro i
    have hsym := (adjComp_self_isPositive T).isSymmetric
    have h1 : ⟪svdBasis T i, (LinearMap.adjoint T ∘ₗ T) v⟫_𝕜
        = (((singularValues T i) ^ 2 : ℝ) : 𝕜) * ⟪svdBasis T i, v⟫_𝕜 := by
      rw [← hsym (svdBasis T i) v, adjComp_apply_svdBasis, inner_smul_left, RCLike.conj_ofReal]
    rw [hv, inner_zero_right] at h1
    have hs2 : (((singularValues T i) ^ 2 : ℝ) : 𝕜) ≠ 0 := by
      have : (singularValues T i) ^ 2 ≠ 0 := pow_ne_zero 2 (hs i)
      exact_mod_cast this
    rcases mul_eq_zero.mp h1.symm with hc | hc
    · exact absurd hc hs2
    · exact hc
  have : v = ∑ i, ⟪svdBasis T i, v⟫_𝕜 • svdBasis T i := ((svdBasis T).sum_repr' v).symm
  rw [this]
  apply Finset.sum_eq_zero
  intro i _
  rw [hzero i, zero_smul]

/-- 7.68(a) {lit}`T` is injective {lit}`⟺` {lit}`0` is not a singular value of
{lit}`T`. -/
theorem injective_iff_singularValues_ne_zero (T : V →ₗ[𝕜] W) :
    Function.Injective T ↔ ∀ i, singularValues T i ≠ 0 := by
  constructor
  · intro hinj i hzero
    have hz : (((singularValues T i) ^ 2 : ℝ) : 𝕜) = 0 := by rw [hzero]; norm_num
    have hzero2 : (LinearMap.adjoint T ∘ₗ T) (svdBasis T i) = 0 := by
      rw [adjComp_apply_svdBasis, hz, zero_smul]
    have hTe : T (svdBasis T i) = 0 := (adjComp_eq_zero_iff T _).mp hzero2
    have hv0 : svdBasis T i = 0 := hinj (by rw [hTe, map_zero])
    exact svdBasis_ne_zero T i hv0
  · intro hs a b hab
    have h0 : T (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h1 : (LinearMap.adjoint T ∘ₗ T) (a - b) = 0 := (adjComp_eq_zero_iff T _).mpr h0
    have h2 : a - b = 0 := adjComp_injective T hs (by rw [h1, map_zero])
    exact sub_eq_zero.mp h2

/-! 7.68 Role of positive singular values, parts (b) and (c)

(b) the number of positive singular values of {lit}`T` equals {lit}`dim range T`;
(c) {lit}`T` is surjective {lit}`⟺` the number of positive singular values equals
{lit}`dim W`.

Part (a) is proved above. For (b) Axler argues through {lit}`T* T` rather than through
the SVD (which comes later): the spectral theorem makes
{lit}`dim range (T* T)` the number of positive eigenvalues of {lit}`T* T`, and 7.64(d)
transports that to {lit}`dim range T`. (c) then follows from (b). -/

/-- 7.68(b) The number of positive singular values of {lit}`T` equals
{lit}`dim range T`. The eigenbasis vectors {lit}`eₖ` with {lit}`sₖ ≠ 0` span
{lit}`range (T* T)` — each is {lit}`(sₖ²)⁻¹ • T* T eₖ`, and conversely {lit}`T* T v`
expands over them by 7.72 — and they are orthonormal, so
{lit}`dim range (T* T)` is their number; 7.64(d) then replaces
{lit}`range (T* T)` by {lit}`range T`. -/
theorem card_pos_singularValues_eq_finrank_range (T : V →ₗ[𝕜] W) :
    Fintype.card {i : Fin (finrank 𝕜 V) // singularValues T i ≠ 0}
      = finrank 𝕜 (LinearMap.range T) := by
  have hindep : LinearIndependent 𝕜
      (fun i : {i : Fin (finrank 𝕜 V) // singularValues T i ≠ 0} => svdBasis T i.1) :=
    ((svdBasis T).orthonormal.comp _ Subtype.val_injective).linearIndependent
  have hsq : ∀ i : Fin (finrank 𝕜 V), singularValues T i ≠ 0 →
      (((singularValues T i) ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    intro i hi
    have : (singularValues T i) ^ 2 ≠ 0 := pow_ne_zero 2 hi
    exact_mod_cast this
  have hspan : Submodule.span 𝕜
      (Set.range fun i : {i : Fin (finrank 𝕜 V) // singularValues T i ≠ 0} => svdBasis T i.1)
      = LinearMap.range (LinearMap.adjoint T ∘ₗ T) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨(((singularValues T i.1) ^ 2 : ℝ) : 𝕜)⁻¹ • svdBasis T i.1, by
        rw [map_smul, adjComp_apply_svdBasis, smul_smul, inv_mul_cancel₀ (hsq i.1 i.2), one_smul]⟩
    · rintro _ ⟨v, rfl⟩
      have hv : (LinearMap.adjoint T ∘ₗ T) v
          = ∑ i, ⟪svdBasis T i, v⟫_𝕜 • (((singularValues T i) ^ 2 : ℝ) : 𝕜) • svdBasis T i := by
        conv_lhs => rw [← (svdBasis T).sum_repr' v]
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul, adjComp_apply_svdBasis]
      rw [hv]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hi : singularValues T i = 0
      · rw [hi]; simp
      · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))
  rw [(finrank_range_adjComp_self T).1.trans (finrank_range_adjComp_self T).2, ← hspan]
  exact (finrank_span_eq_card hindep).symm

/-- 7.68(c) {lit}`T` is surjective iff the number of positive singular values of
{lit}`T` equals {lit}`dim W`. -/
theorem surjective_iff_card_pos_singularValues (T : V →ₗ[𝕜] W) :
    Function.Surjective T ↔
      Fintype.card {i : Fin (finrank 𝕜 V) // singularValues T i ≠ 0} = finrank 𝕜 W := by
  rw [card_pos_singularValues_eq_finrank_range, ← LinearMap.range_eq_top]
  constructor
  · intro h; rw [h]; exact finrank_top 𝕜 W
  · intro h; exact Submodule.eq_top_of_finrank_eq h

/-! 7.69 Isometries characterized by having all singular values equal 1

{lit}`S ∈ ℒ(V, W)` is an isometry {lit}`⟺` all singular values of {lit}`S` equal
{lit}`1`, because {lit}`S` is an isometry {lit}`⟺ S* S = I` (7.49) {lit}`⟺` all
eigenvalues of {lit}`S* S` equal {lit}`1` (spectral theorem). -/
theorem isometry_iff_singularValues_eq_one (S : V →ₗ[𝕜] W) :
    Isometry S ↔ ∀ i, singularValues S i = 1 := by
  rw [LADR.Section_7D.isometry_iff_adjoint_comp]
  constructor
  · intro hS i
    have hself : ⟪svdBasis S i, svdBasis S i⟫_𝕜 = 1 := by
      rw [orthonormal_iff_ite.mp (svdBasis S).orthonormal i i, if_pos rfl]
    have h1 : (((singularValues S i) ^ 2 : ℝ) : 𝕜) * ⟪svdBasis S i, svdBasis S i⟫_𝕜
        = ⟪svdBasis S i, svdBasis S i⟫_𝕜 := by
      rw [← inner_smul_right, ← adjComp_apply_svdBasis, hS, Module.End.one_apply]
    rw [hself, mul_one] at h1
    have hr : (singularValues S i) ^ 2 = 1 := by exact_mod_cast h1
    have : singularValues S i = Real.sqrt ((singularValues S i) ^ 2) :=
      (Real.sqrt_sq (singularValues_nonneg S i)).symm
    rw [this, hr, Real.sqrt_one]
  · intro hS
    apply (svdBasis S).toBasis.ext
    intro i
    rw [OrthonormalBasis.coe_toBasis, Module.End.one_apply, adjComp_apply_svdBasis, hS i]
    norm_num

/-! # Singular Value Decomposition -/

/-- The normalized image vectors {lit}`fₖ = T eₖ / sₖ` (set to {lit}`0` when
{lit}`sₖ = 0`), as in 7.73. -/
noncomputable def svdImage (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) : W :=
  if singularValues T i = 0 then 0 else (singularValues T i : 𝕜)⁻¹ • T (svdBasis T i)

/-- {lit}`T eₖ = sₖ fₖ` for every {lit}`k` (including {lit}`sₖ = 0`, where both
sides vanish because {lit}`T eₖ = 0`). -/
theorem svdBasis_image_eq (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) :
    T (svdBasis T i) = (singularValues T i : 𝕜) • svdImage T i := by
  rw [svdImage]
  by_cases h : singularValues T i = 0
  · rw [if_pos h, smul_zero]
    have : ‖T (svdBasis T i)‖ = 0 := by rw [norm_image_svdBasis, h]
    exact norm_eq_zero.mp this
  · rw [if_neg h, smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast h : (singularValues T i : 𝕜) ≠ 0), one_smul]

/-- 7.73 The vectors {lit}`fₖ = svdImage T k` with {lit}`sₖ ≠ 0` form an
orthonormal list in {lit}`W`. -/
theorem svdImage_orthonormal (T : V →ₗ[𝕜] W) :
    Orthonormal 𝕜 (fun i : {i : Fin (finrank 𝕜 V) // singularValues T i ≠ 0} =>
      svdImage T i.1) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  simp only [svdImage, if_neg hi, if_neg hj]
  rw [inner_smul_left, inner_smul_right, inner_image_svdBasis, map_inv₀, RCLike.conj_ofReal]
  rcases eq_or_ne i j with h | h
  · subst h
    rw [if_pos rfl, if_pos (by rfl : (⟨i, hi⟩ : {i // singularValues T i ≠ 0}) = ⟨i, hj⟩),
      RCLike.ofReal_pow]
    have hne : (singularValues T i : 𝕜) ≠ 0 := by exact_mod_cast hi
    field_simp
  · rw [if_neg h, if_neg (fun hh => h (Subtype.ext_iff.mp hh)), mul_zero, mul_zero]

/-! 7.70 Singular value decomposition

Suppose {lit}`T ∈ ℒ(V, W)`. Then there exist an orthonormal basis
{lit}`e₁, …, eₙ` of {lit}`V` (with {lit}`n = dim V`) and vectors
{lit}`f₁, …, fₙ` in {lit}`W`, orthonormal on the indices with {lit}`sₖ ≠ 0`, such
that {lit}`T eₖ = sₖ fₖ` and
{lit}`T v = s₁ ⟨v, e₁⟩ f₁ + ⋯ + sₙ ⟨v, eₙ⟩ fₙ` for every {lit}`v ∈ V` (7.71).

Recall (slot convention, see Chapter 6 notes) that Axler's {lit}`⟨v, eₖ⟩` is
mathlib's {lit}`⟪eₖ, v⟫`. The terms with {lit}`sₖ = 0` contribute {lit}`0`, so
this full-basis form is equivalent to Axler's list form over the positive singular
values. -/

/-- 7.71 The singular value decomposition formula. -/
theorem svd_apply (T : V →ₗ[𝕜] W) (v : V) :
    T v = ∑ i, (singularValues T i : 𝕜) • ⟪svdBasis T i, v⟫_𝕜 • svdImage T i := by
  conv_lhs => rw [← (svdBasis T).sum_repr' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, svdBasis_image_eq]
  exact smul_comm _ _ _

/-- 7.70 Existence of a singular value decomposition, exactly what Axler asserts:
orthonormal lists {lit}`e` (here an orthonormal basis of {lit}`V`) and {lit}`f`
(orthonormal on the positive-singular-value indices) for which the formula 7.71 holds.
Axler's statement stops there; the construction also gives {lit}`T eₖ = sₖ fₖ`, which is
{name}`svdBasis_image_eq` and is what the later sections use. -/
theorem singularValueDecomposition (T : V →ₗ[𝕜] W) :
    ∃ (e : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V) (f : Fin (finrank 𝕜 V) → W),
      Orthonormal 𝕜 (fun i : {i // singularValues T i ≠ 0} => f i.1) ∧
      ∀ v, T v = ∑ i, (singularValues T i : 𝕜) • ⟪e i, v⟫_𝕜 • f i :=
  ⟨svdBasis T, svdImage T, svdImage_orthonormal T, svd_apply T⟩

/-! Note on the {lit}`e`'s and {lit}`f`'s. The witnesses just supplied are
{lit}`e i = svdBasis T i` and {lit}`f i = svdImage T i`, and everything from here on —
7.75 and its consequences (7.77 for the adjoint, 7.78 for the pseudoinverse), and Section 7F
— is stated with {lit}`svdBasis`/{lit}`svdImage` rather than through this existential. So
when Axler writes "let {lit}`e₁, …, eₙ` and {lit}`f₁, …, fₙ` be as in the singular value
decomposition 7.70", read {lit}`eₖ = svdBasis T k` and {lit}`fₖ = svdImage T k`; the facts
those proofs use about them are {name}`svdBasis_image_eq` ({lit}`T eₖ = sₖ fₖ`),
{name}`svd_apply` (7.71) and the orthonormality of each family. -/

/-! # Diagonal Matrices and the Adjoint -/

/-! 7.74 Definition: diagonal matrix

An {lit}`M`-by-{lit}`N` matrix is *diagonal* if every entry off the main diagonal
is {lit}`0` (mathlib's {lit}`Matrix.IsDiag` requires a square matrix; this is the
rectangular generalization). -/

def IsRectDiagonal {p n : ℕ} (A : Matrix (Fin p) (Fin n) 𝕜) : Prop :=
  ∀ (j : Fin p) (k : Fin n), (j : ℕ) ≠ (k : ℕ) → A j k = 0

/-! 7.75 Singular value decomposition of the adjoint (7.77)

Given a singular value decomposition {lit}`T v = ∑ sₖ ⟨v, eₖ⟩ fₖ`, the adjoint is
obtained by interchanging the roles of the {lit}`e`'s and {lit}`f`'s:
{lit}`T* w = ∑ sₖ ⟨w, fₖ⟩ eₖ`. We verify this by checking
{lit}`⟨v, T* w⟩ = ⟨T v, w⟩` for all {lit}`v` and appealing to
{name}`ext_inner_left`. -/
theorem adjoint_svd_apply (T : V →ₗ[𝕜] W) (w : W) :
    LinearMap.adjoint T w =
      ∑ i, (singularValues T i : 𝕜) • ⟪svdImage T i, w⟫_𝕜 • svdBasis T i := by
  refine ext_inner_left 𝕜 fun v => ?_
  rw [LinearMap.adjoint_inner_right, inner_sum]
  rw [svd_apply T v, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right,
    RCLike.conj_ofReal, inner_conj_symm]
  ring

/-- 7.75 Singular value decomposition of the pseudoinverse (7.78):
{lit}`T† w = ∑ (⟨fₖ, w⟩ / sₖ) eₖ` (summed over all {lit}`k`; the {lit}`sₖ = 0`
terms vanish). Following Axler, write {lit}`S w` for the right-hand side. The key
identity {lit}`T* w = (T* T)(S w)` (both equal {lit}`∑ sₖ ⟨fₖ, w⟩ eₖ` by the SVD
of the adjoint and {lit}`T* T eₖ = sₖ² eₖ`) shows {lit}`w − T(S w) ∈ ker T* =
(range T)ᗮ`, so {lit}`T(S w) = P_(range T) w = T(T† w)` (6.69(b)); since both
{lit}`S w` and {lit}`T† w` lie in {lit}`(ker T)ᗮ`, they are equal. -/
theorem pinv_svd_apply (T : V →ₗ[𝕜] W) (w : W) :
    LADR.Section_6C.pinv T w
      = ∑ i, (singularValues T i : 𝕜)⁻¹ • ⟪svdImage T i, w⟫_𝕜 • svdBasis T i := by
  set S := ∑ i, (singularValues T i : 𝕜)⁻¹ • ⟪svdImage T i, w⟫_𝕜 • svdBasis T i with hSdef
  -- svdBasis T i ∈ (ker T)ᗮ when sᵢ ≠ 0, since eᵢ = sᵢ⁻¹ • T*(fᵢ) ∈ range T*.
  have hTf : ∀ i, singularValues T i ≠ 0 →
      LinearMap.adjoint T (svdImage T i) = (singularValues T i : 𝕜) • svdBasis T i := by
    intro i hi
    rw [svdImage, if_neg hi, map_smul, ← LinearMap.comp_apply, adjComp_apply_svdBasis, smul_smul]
    congr 1
    have hne : (singularValues T i : 𝕜) ≠ 0 := by exact_mod_cast hi
    rw [RCLike.ofReal_pow]; field_simp
  have hei_perp : ∀ i, singularValues T i ≠ 0 → svdBasis T i ∈ (LinearMap.ker T)ᗮ := by
    intro i hi
    have hei : svdBasis T i = (singularValues T i : 𝕜)⁻¹ • LinearMap.adjoint T (svdImage T i) := by
      rw [hTf i hi, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hi), one_smul]
    rw [hei]
    apply Submodule.smul_mem
    rw [Submodule.mem_orthogonal]
    intro x hx
    rw [LinearMap.adjoint_inner_right, LinearMap.mem_ker.mp hx, inner_zero_left]
  have hS_mem : S ∈ (LinearMap.ker T)ᗮ := by
    rw [hSdef]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : singularValues T i = 0
    · rw [hi, RCLike.ofReal_zero, inv_zero, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hei_perp i hi))
  -- Key identity: T* w = (T* T)(S).
  have hkey : LinearMap.adjoint T w = (LinearMap.adjoint T ∘ₗ T) S := by
    rw [adjoint_svd_apply, hSdef, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, adjComp_apply_svdBasis]
    by_cases hi : singularValues T i = 0
    · simp [hi]
    · simp only [smul_smul]
      congr 1
      have hne : (singularValues T i : 𝕜) ≠ 0 := by exact_mod_cast hi
      rw [RCLike.ofReal_pow]; field_simp
  -- Hence T(S) = P_(range T) w.
  have hTS : T S = (LinearMap.range T).starProjection w := by
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self T S)
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    have hadj0 : LinearMap.adjoint T (w - T S) = 0 := by
      rw [map_sub, hkey, LinearMap.comp_apply, sub_self]
    rw [← LinearMap.adjoint_inner_left, hadj0, inner_zero_left]
  -- pinv w and S both lie in (ker T)ᗮ and T maps both to P_(range T) w.
  have hpinv_mem : LADR.Section_6C.pinv T w ∈ (LinearMap.ker T)ᗮ := by
    show ((LADR.Section_6C.restrEquiv T).symm
      ((LinearMap.range T).orthogonalProjection w) : V) ∈ _
    exact SetLike.coe_mem _
  have hTeq : T (LADR.Section_6C.pinv T w) = T S := by
    rw [hTS, ← LinearMap.comp_apply]
    exact LinearMap.congr_fun (LADR.Section_6C.T_comp_pinv T) w
  have hdiff_ker : LADR.Section_6C.pinv T w - S ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker, map_sub, hTeq, sub_self]
  have hdiff_perp : LADR.Section_6C.pinv T w - S ∈ (LinearMap.ker T)ᗮ :=
    Submodule.sub_mem _ hpinv_mem hS_mem
  have hzero : ⟪LADR.Section_6C.pinv T w - S, LADR.Section_6C.pinv T w - S⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal' _ _).mp hdiff_perp _ hdiff_ker
  rw [← sub_eq_zero]
  exact inner_self_eq_zero.mp hzero

/-- The {lit}`(k,l)` entry of {lit}`A` read off the SVD of {lit}`Matrix.toEuclideanLin A`:
`A k l = ∑ᵢ sᵢ conj(eᵢ l) fᵢ k` (the {lit}`sᵢ = 0` terms vanish). -/
theorem toEuclideanLin_entry_eq_svd {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) (k l : Fin N) :
    A k l = ∑ i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin N))),
      (singularValues (Matrix.toEuclideanLin A) i : 𝕜)
      * (starRingEnd 𝕜) (svdBasis (Matrix.toEuclideanLin A) i l)
      * svdImage (Matrix.toEuclideanLin A) i k := by
  set T := Matrix.toEuclideanLin A with hTdef
  have hL := congrArg (⇑(EuclideanSpace.equiv (Fin N) 𝕜))
    (svd_apply T (EuclideanSpace.single l (1 : 𝕜)))
  rw [map_sum] at hL
  simp only [map_smul] at hL
  have hLk := congrFun hL k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hLk
  have hAkl : A k l = (⇑(EuclideanSpace.equiv (Fin N) 𝕜)
      (T (EuclideanSpace.single l (1:𝕜)))) k := by
    rw [hTdef, Matrix.toLpLin_apply]
    simp [EuclideanSpace.single, Matrix.mulVec_single]
  rw [hAkl, hLk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_single_right]
  simp only [show ∀ (w : EuclideanSpace 𝕜 (Fin N)) (m : Fin N),
    ⇑(EuclideanSpace.equiv (Fin N) 𝕜) w m = w m from fun _ _ => rfl, one_mul]
  ring

/-- 7.80 Matrix version of the SVD. A square matrix {lit}`A` factors as {lit}`A = B D Cᴴ`
with {lit}`B`, {lit}`C` having orthonormal columns (`Bᴴ B = Cᴴ C = 1`) and {lit}`D` a diagonal
matrix carrying the positive singular values. Following Axler, the columns of {lit}`B`
are the image vectors {lit}`fₖ`, the columns of {lit}`C` are the eigenbasis vectors {lit}`eₖ`
(both indexed by the positive singular values), and {lit}`D` holds the {lit}`sₖ`. -/
theorem matrix_svd {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜) :
    ∃ (B C : Matrix (Fin N)
        {i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin N)))
          // singularValues (Matrix.toEuclideanLin A) i ≠ 0} 𝕜)
      (D : Matrix {i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin N)))
          // singularValues (Matrix.toEuclideanLin A) i ≠ 0}
        {i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin N)))
          // singularValues (Matrix.toEuclideanLin A) i ≠ 0} 𝕜),
      Bᴴ * B = 1 ∧ Cᴴ * C = 1
        ∧ (∀ i, D i i = (singularValues (Matrix.toEuclideanLin A) i.1 : 𝕜))
        ∧ (∀ i j, i ≠ j → D i j = 0) ∧ A = B * D * Cᴴ := by
  classical
  set T := Matrix.toEuclideanLin A with hTdef
  refine ⟨Matrix.of fun k i => svdImage T i.1 k, Matrix.of fun k i => svdBasis T i.1 k,
    Matrix.diagonal fun i => (singularValues T i.1 : 𝕜), ?_, ?_,
    fun i => Matrix.diagonal_apply_eq _ _, fun i j hij => Matrix.diagonal_apply_ne _ hij, ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply,
      ← orthonormal_iff_ite.mp (svdImage_orthonormal T) i j, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.inner_apply, RCLike.star_def]
    ring
  · ext i j
    rw [Matrix.mul_apply, Matrix.one_apply,
      ← orthonormal_iff_ite.mp
        ((svdBasis T).orthonormal.comp Subtype.val Subtype.val_injective) i j, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.inner_apply, RCLike.star_def,
      Function.comp_apply]
    ring
  · ext k l
    rw [Matrix.mul_assoc, Matrix.mul_apply, toEuclideanLin_entry_eq_svd A k l]
    rw [show (∑ i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin N))),
        (singularValues T i : 𝕜) * (starRingEnd 𝕜) (svdBasis T i l) * svdImage T i k)
        = ∑ i : {x : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin N))) // singularValues T x ≠ 0},
          (singularValues T i.1 : 𝕜) * (starRingEnd 𝕜) (svdBasis T i.1 l) * svdImage T i.1 k
      from ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [Matrix.diagonal_apply_eq, Matrix.of_apply, Matrix.conjTranspose_apply,
          Matrix.of_apply, RCLike.star_def]; ring
      · intro b _ hb; rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [← Finset.sum_subtype (Finset.univ.filter fun i => singularValues T i ≠ 0)
        (fun x => by simp) fun i => (singularValues T i : 𝕜)
          * (starRingEnd 𝕜) (svdBasis T i l) * svdImage T i k]
      exact (Finset.sum_filter_of_ne fun i _ hne => by
        intro hz
        exact hne (by rw [hz, RCLike.ofReal_zero, zero_mul, zero_mul])).symm

/-! # Examples

Examples 7.66 and 7.67 are formalized at their book positions above, following 7.65:
the maps are given by their matrices ({lit}`A_7_66`, {lit}`A_7_67`), and the
{lit}`T* T` computations Axler assigns to the reader are proved
({name}`adjComp_T_7_66_apply`, {name}`conjTranspose_mul_A_7_66`,
{name}`adjComp_T_7_66_eq`, {name}`conjTranspose_mul_A_7_67`), as is the eigenvalue *set*
of 7.66's {lit}`T* T` ({name}`hasEigenvalue_adjComp_T_7_66`, via
{name}`spectrum_diagonal`).

What still carries a {lit}`sorry` is the passage from the eigenvalue set to Axler's list
*with multiplicity*: the eigenspace dimensions ({lit}`finrank_eigenspace_adjComp_T_7_66`,
{lit}`eigenvalues_adjComp_T_7_67`) and the singular-value multisets
({lit}`singularValues_T_7_66`, {lit}`singularValues_T_7_67`). Axler reads these off by
inspection; in Lean they want a lemma computing {lit}`dim E(μ, S)` for an operator diagonal
in a given orthonormal basis — mathlib has this only for its own
{lit}`eigenvectorBasis` ({name}`LinearMap.IsSymmetric.card_filter_eigenvalues_eq`) — plus,
for 7.67, a diagonalization of the non-diagonal {lit}`T* T` (its {lit}`(1,1;1,1)` block has
eigenvectors {lit}`(1,±1,0,0)`).

Example 7.79 ({lit}`T ∈ ℒ(𝔽⁴, 𝔽³)`, the pseudoinverse of the same map) remains
unformalized for the same reason. -/

/-! # Exercises 7E -/

/-- 7E.1 {lit}`T = 0` if and only if all singular values of {lit}`T` are {lit}`0`. -/
theorem exercise_7E_1 (T : V →ₗ[𝕜] W) :
    T = 0 ↔ ∀ i, singularValues T i = 0 := by
  sorry

/-- 7E.2 For {lit}`s > 0`, {lit}`s` is a singular value of {lit}`T` iff there exist
nonzero {lit}`v ∈ V`, {lit}`w ∈ W` with {lit}`T v = s w` and {lit}`T* w = s v`
(a *Schmidt pair*). -/
theorem exercise_7E_2 (T : V →ₗ[𝕜] W) {s : ℝ} (hs : 0 < s) :
    (∃ i, singularValues T i = s) ↔
      ∃ (v : V) (w : W), v ≠ 0 ∧ w ≠ 0 ∧
        T v = (s : 𝕜) • w ∧ LinearMap.adjoint T w = (s : 𝕜) • v := by
  sorry

/-- 7E.3 There is an operator on {lit}`ℂ²` whose only eigenvalue is {lit}`0` but
whose singular values are {lit}`5, 0`. -/
theorem exercise_7E_3 :
    ∃ T : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2),
      (∀ μ : ℂ, HasEigenvalue T μ ↔ μ = 0) ∧
      (∀ s : ℝ, (∃ i, singularValues T i = s) ↔ s = 5 ∨ s = 0) := by
  sorry

/-- 7E.4 With {lit}`s₁` the largest and {lit}`sₙ` the smallest singular value,
{lit}`{‖Tv‖ : ‖v‖ = 1} = [sₙ, s₁]`. -/
theorem exercise_7E_4 (T : V →ₗ[𝕜] W) (s₁ sₙ : ℝ)
    (h1 : IsGreatest (Set.range (singularValues T)) s₁)
    (hn : IsLeast (Set.range (singularValues T)) sₙ) :
    {r : ℝ | ∃ v : V, ‖v‖ = 1 ∧ ‖T v‖ = r} = Set.Icc sₙ s₁ := by
  sorry

/-- 7E.5 The operator {lit}`T(x, y) = (−4y, x)` on {lit}`ℂ²` has singular values
{lit}`4, 1`. -/
theorem exercise_7E_5 (T : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
    (hT : ∀ z : EuclideanSpace ℂ (Fin 2), T z = !₂[-4 * z 1, z 0]) :
    ∀ s : ℝ, (∃ i, singularValues T i = s) ↔ s = 4 ∨ s = 1 := by
  sorry

/-- The singular values of the differentiation operator of 7E.6 — the numbers to
be found by the solver. -/
noncomputable def singularValues_7E_6 : Fin 3 → ℝ := sorry

/-- 7E.6 Find the singular values of the differentiation operator {lit}`D p = p′`
on {lit}`𝒫₂(ℝ)` with the {lit}`L²` inner product {lit}`⟨p, q⟩ = ∫₀¹ pq` of Example
6.34 (the space is {name}`LADR.Section_7A.l2Core_7A14`'s
{lit}`Polynomial.degreeLT ℝ 3`). The answer is {name}`singularValues_7E_6`. -/
theorem exercise_7E_6 (D : Polynomial.degreeLT ℝ 3 →ₗ[ℝ] Polynomial.degreeLT ℝ 3)
    (hD : ∀ p : Polynomial.degreeLT ℝ 3,
      (D p : Polynomial ℝ) = (p : Polynomial ℝ).derivative) (s : ℝ) :
    (∃ i, singularValues D i = s) ↔ ∃ j, singularValues_7E_6 j = s := by
  sorry

/-- 7E.7 For self-adjoint {lit}`T` (or {lit}`𝔽 = ℂ` and {lit}`T` normal), the
singular values are the absolute values of the eigenvalues. -/
theorem exercise_7E_7 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) :
    {s : ℝ | ∃ i, singularValues T i = s} =
      {s : ℝ | ∃ μ : 𝕜, HasEigenvalue T μ ∧ ‖μ‖ = s} := by
  sorry

/-- 7E.8(a) In an SVD, {lit}`f₁, …, fₘ` is an orthonormal basis of {lit}`range T`. -/
theorem exercise_7E_8a {m : ℕ} (T : V →ₗ[𝕜] W) (e : Fin m → V) (f : Fin m → W)
    (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (hT : ∀ v, T v = ∑ i, (s i : 𝕜) • ⟪e i, v⟫_𝕜 • f i) :
    Submodule.span 𝕜 (Set.range f) = LinearMap.range T := by
  sorry

/-- 7E.8(b) In an SVD, {lit}`e₁, …, eₘ` is an orthonormal basis of
{lit}`(null T)⟂`. -/
theorem exercise_7E_8b {m : ℕ} (T : V →ₗ[𝕜] W) (e : Fin m → V) (f : Fin m → W)
    (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (hT : ∀ v, T v = ∑ i, (s i : 𝕜) • ⟪e i, v⟫_𝕜 • f i) :
    Submodule.span 𝕜 (Set.range e) = (LinearMap.ker T)ᗮ := by
  sorry

/-- 7E.8(c) In an SVD, {lit}`s₁, …, sₘ` are the positive singular values of
{lit}`T`. -/
theorem exercise_7E_8c {m : ℕ} (T : V →ₗ[𝕜] W) (e : Fin m → V) (f : Fin m → W)
    (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (hT : ∀ v, T v = ∑ i, (s i : 𝕜) • ⟪e i, v⟫_𝕜 • f i) :
    {r : ℝ | 0 < r ∧ ∃ i, singularValues T i = r} = {r : ℝ | ∃ i, s i = r} := by
  sorry

/-- 7E.8(d) Given a singular value decomposition with orthonormal lists {lit}`e`,
{lit}`f` and positive {lit}`sₖ`, each {lit}`eₖ` is an eigenvector of {lit}`T* T`
with eigenvalue {lit}`sₖ²`. -/
theorem exercise_7E_8d {m : ℕ} (T : V →ₗ[𝕜] W) (e : Fin m → V) (f : Fin m → W)
    (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (hT : ∀ v, T v = ∑ i, (s i : 𝕜) • ⟪e i, v⟫_𝕜 • f i) (k : Fin m) :
    (LinearMap.adjoint T ∘ₗ T) (e k) = ((s k) ^ 2 : 𝕜) • e k := by
  sorry

/-- 7E.8(e) With the same data, {lit}`T T* w = ∑ sₖ² ⟨w, fₖ⟩ fₖ`. -/
theorem exercise_7E_8e {m : ℕ} (T : V →ₗ[𝕜] W) (e : Fin m → V) (f : Fin m → W)
    (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (hT : ∀ v, T v = ∑ i, (s i : 𝕜) • ⟪e i, v⟫_𝕜 • f i) (w : W) :
    T (LinearMap.adjoint T w) = ∑ i, ((s i) ^ 2 : 𝕜) • ⟪f i, w⟫_𝕜 • f i := by
  sorry

/-- 7E.9 {lit}`T` and {lit}`T*` have the same positive singular values. -/
theorem exercise_7E_9 (T : V →ₗ[𝕜] W) :
    {s : ℝ | 0 < s ∧ ∃ i, singularValues T i = s} =
      {s : ℝ | 0 < s ∧ ∃ j, singularValues (LinearMap.adjoint T) j = s} := by
  sorry

/-- 7E.10 If {lit}`T` is invertible, then {lit}`T⁻¹` has singular values the
reciprocals of those of {lit}`T`. -/
theorem exercise_7E_10 (T : V ≃ₗ[𝕜] V) :
    {r : ℝ | ∃ i, singularValues (T.symm : V →ₗ[𝕜] V) i = r} =
      {r : ℝ | ∃ i, singularValues (T : V →ₗ[𝕜] V) i ≠ 0 ∧
        r = (singularValues (T : V →ₗ[𝕜] V) i)⁻¹} := by
  sorry

/-- 7E.11(a) For any orthonormal basis {lit}`c` of {lit}`V`,
{lit}`∑ ‖T cⱼ‖² = ∑ sⱼ²` (the sum of squared singular values is basis
independent). -/
theorem exercise_7E_11a (T : V →ₗ[𝕜] W) (c : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V) :
    ∑ j, ‖T (c j)‖ ^ 2 = ∑ i, (singularValues T i) ^ 2 := by
  sorry

/-- 7E.11(b) If {lit}`W = V` and {lit}`T` is positive, then
{lit}`∑ ⟨T vⱼ, vⱼ⟩ = ∑ sⱼ`. -/
theorem exercise_7E_11b (T : V →ₗ[𝕜] V) (hT : T.IsPositive)
    (c : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V) :
    RCLike.re (∑ j, ⟪c j, T (c j)⟫_𝕜) = ∑ i, singularValues T i := by
  sorry

/-- 7E.12(a) There is an operator whose {lit}`T²` singular values are not the
squares of the singular values of {lit}`T`. -/
theorem exercise_7E_12a :
    ∃ T : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2),
      {r : ℝ | ∃ i, singularValues (T ∘ₗ T) i = r} ≠
        {r : ℝ | ∃ i, singularValues T i ^ 2 = r} := by
  sorry

/-- 7E.12(b) For normal {lit}`T`, the singular values of {lit}`T²` are the squares
of the singular values of {lit}`T`. -/
theorem exercise_7E_12b (T : V →ₗ[𝕜] V) (hN : IsStarNormal T) :
    {r : ℝ | ∃ i, singularValues (T ∘ₗ T) i = r} =
      {r : ℝ | ∃ i, singularValues T i ^ 2 = r} := by
  sorry

/-- 7E.13 {lit}`T₁, T₂` have the same singular values iff {lit}`T₁ = S₁ T₂ S₂` for
unitary {lit}`S₁, S₂`. -/
theorem exercise_7E_13 (T₁ T₂ : V →ₗ[𝕜] V) :
    ({r : ℝ | ∃ i, singularValues T₁ i = r} = {r : ℝ | ∃ i, singularValues T₂ i = r}) ↔
      ∃ S₁ S₂ : V →ₗ[𝕜] V, S₁ ∈ unitary (V →ₗ[𝕜] V) ∧ S₂ ∈ unitary (V →ₗ[𝕜] V) ∧
        T₁ = S₁ ∘ₗ T₂ ∘ₗ S₂ := by
  sorry

/-- 7E.14 With {lit}`sₙ` the smallest singular value, {lit}`sₙ ‖v‖ ≤ ‖Tv‖` for all
{lit}`v`. -/
theorem exercise_7E_14 (T : V →ₗ[𝕜] W) (sₙ : ℝ)
    (hn : IsLeast (Set.range (singularValues T)) sₙ) (v : V) :
    sₙ * ‖v‖ ≤ ‖T v‖ := by
  sorry

/-- 7E.15 If {lit}`λ` is an eigenvalue of {lit}`T` then
{lit}`s₁ ≥ |λ| ≥ sₙ` (largest and smallest singular values). -/
theorem exercise_7E_15 (T : V →ₗ[𝕜] V) (s₁ sₙ : ℝ)
    (h1 : IsGreatest (Set.range (singularValues T)) s₁)
    (hn : IsLeast (Set.range (singularValues T)) sₙ)
    (μ : 𝕜) (hμ : HasEigenvalue T μ) : ‖μ‖ ≤ s₁ ∧ sₙ ≤ ‖μ‖ := by
  sorry

/-- 7E.16 {lit}`(T*)† = (T†)*`. -/
theorem exercise_7E_16 (T : V →ₗ[𝕜] W) :
    LADR.Section_6C.pinv (LinearMap.adjoint T) =
      LinearMap.adjoint (LADR.Section_6C.pinv T) := by
  sorry

/-- 7E.17 {lit}`T` is self-adjoint iff {lit}`T†` is self-adjoint. -/
theorem exercise_7E_17 (T : V →ₗ[𝕜] V) :
    LinearMap.IsSymmetric T ↔ LinearMap.IsSymmetric (LADR.Section_6C.pinv T) := by
  sorry

end LADR.Section_7E
