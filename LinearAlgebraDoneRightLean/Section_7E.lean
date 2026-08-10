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
multiplicity* (one value per basis vector), and it captures Axler's ordering too:
mathlib's {name}`LinearMap.IsSymmetric.eigenvalues` are sorted in decreasing order
({name}`LinearMap.IsSymmetric.eigenvalues_antitone`) and {lit}`√` is monotone, so
{lit}`singularValues T` is already Axler's decreasing list
({lit}`singularValues_antitone` below). -/

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

/-- 7.65 The singular values are listed in decreasing order, as Axler's definition
requires: mathlib sorts the eigenvalues of a self-adjoint operator decreasingly and
{lit}`√` preserves that. -/
theorem singularValues_antitone (T : V →ₗ[𝕜] W) : Antitone (singularValues T) :=
  fun _ _ hij =>
    Real.sqrt_le_sqrt ((adjComp_self_isPositive T).isSymmetric.eigenvalues_antitone rfl hij)

/-- The eigenvalues of the positive operator {lit}`T* T` are nonnegative (7.64(a)). -/
theorem eigenvalues_nonneg (T : V →ₗ[𝕜] W) (i : Fin (finrank 𝕜 V)) :
    0 ≤ (adjComp_self_isPositive T).isSymmetric.eigenvalues rfl i := by
  have hpos := adjComp_self_isPositive T
  have hev : HasEigenvalue (LinearMap.adjoint T ∘ₗ T)
      ((hpos.isSymmetric.eigenvalues rfl i : ℝ) : 𝕜) :=
    hpos.isSymmetric.hasEigenvalue_eigenvalues rfl i
  have := (LADR.Section_7C.eigenvalue_nonneg hpos hev).1
  rwa [RCLike.ofReal_re] at this

omit [FiniteDimensional 𝕜 V] in
/-- Eigenspace dimensions from *any* diagonalizing orthonormal basis: if
{lit}`S bᵢ = dᵢ bᵢ` for an orthonormal basis {lit}`b`, then {lit}`dim E(μ, S)` is the number
of indices with {lit}`dᵢ = μ`. mathlib has this only for its own
{name}`LinearMap.IsSymmetric.eigenvectorBasis`
({name}`LinearMap.IsSymmetric.card_filter_eigenvalues_eq`), whereas Examples 7.66 and 7.67
diagonalize {lit}`T* T` by a basis exhibited by hand — which is also how Axler reads the
eigenvalues off. -/
theorem finrank_eigenspace_of_orthonormalBasis {m : ℕ} {S : V →ₗ[𝕜] V}
    (b : OrthonormalBasis (Fin m) 𝕜 V) (d : Fin m → 𝕜) (hb : ∀ i, S (b i) = d i • b i)
    (μ : 𝕜) :
    finrank 𝕜 (Module.End.eigenspace S μ) = Fintype.card {i // d i = μ} := by
  classical
  have hindep : LinearIndependent 𝕜 b := b.orthonormal.linearIndependent
  have hspan : Module.End.eigenspace S μ
      = Submodule.span 𝕜 (Set.range fun i : {i // d i = μ} => b i.1) := by
    apply le_antisymm
    · intro v hv
      rw [Module.End.mem_eigenspace_iff] at hv
      -- expand `v` in the basis; the coefficient at `i` vanishes unless `dᵢ = μ`
      have hrepr : ∑ i, ⟪b i, v⟫_𝕜 • b i = v := b.sum_repr' v
      have hcoeff : ∀ i, d i ≠ μ → ⟪b i, v⟫_𝕜 = 0 := by
        intro i hi
        have hzero : ∑ j, (⟪b j, v⟫_𝕜 * d j - μ * ⟪b j, v⟫_𝕜) • b j = 0 := by
          have h1 : S v = ∑ j, (⟪b j, v⟫_𝕜 * d j) • b j := by
            conv_lhs => rw [← hrepr]
            rw [map_sum]
            exact Finset.sum_congr rfl fun j _ => by
              rw [map_smul, hb j, smul_smul]
          have h2 : μ • v = ∑ j, (μ * ⟪b j, v⟫_𝕜) • b j := by
            conv_lhs => rw [← hrepr]
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
          rw [← sub_eq_zero, h1, h2, ← Finset.sum_sub_distrib] at hv
          simpa [sub_smul] using hv
        have hfac : ⟪b i, v⟫_𝕜 * (d i - μ) = 0 := by
          have h := (Fintype.linearIndependent_iff.mp hindep) _ hzero i
          linear_combination h
        rcases mul_eq_zero.mp hfac with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h) hi
      rw [← hrepr]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases hi : d i = μ
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      · rw [hcoeff i hi, zero_smul]; exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, hb i.1, i.2]
  rw [hspan]
  exact finrank_span_eq_card
    ((b.orthonormal.comp _ Subtype.val_injective).linearIndependent)

omit [FiniteDimensional 𝕜 V] in
/-- The eigenvalue list is independent of the diagonalizing basis: if {lit}`S` is diagonal
with eigenvalues {lit}`d` in one orthonormal basis and with {lit}`d'` in another, then
{lit}`d` and {lit}`d'` agree as multisets — with multiplicity, and even for bases of different
index types. Both counts are eigenspace dimensions
({name}`finrank_eigenspace_of_orthonormalBasis`). Taking one basis to be mathlib's
{name}`LinearMap.IsSymmetric.eigenvectorBasis` identifies a hand-exhibited eigenvalue list
with {name}`LinearMap.IsSymmetric.eigenvalues`, which is how Examples 7.66 and 7.67 read the
singular values off. -/
theorem eigenvalues_multiset_eq_of_orthonormalBases {m m' : ℕ} {S : V →ₗ[𝕜] V}
    (b : OrthonormalBasis (Fin m) 𝕜 V) (d : Fin m → ℝ)
    (hb : ∀ i, S (b i) = ((d i : ℝ) : 𝕜) • b i)
    (b' : OrthonormalBasis (Fin m') 𝕜 V) (d' : Fin m' → ℝ)
    (hb' : ∀ i, S (b' i) = ((d' i : ℝ) : 𝕜) • b' i) :
    Multiset.map d Finset.univ.val = Multiset.map d' Finset.univ.val := by
  classical
  refine Multiset.ext.mpr fun r => ?_
  rw [Multiset.count_map, Multiset.count_map]
  have hcount : ∀ {k : ℕ} (c : OrthonormalBasis (Fin k) 𝕜 V) (e : Fin k → ℝ),
      (∀ i, S (c i) = ((e i : ℝ) : 𝕜) • c i) →
      (Finset.univ.val.filter fun i => r = e i).card
        = finrank 𝕜 (Module.End.eigenspace S ((r : ℝ) : 𝕜)) := by
    intro k c e hc
    rw [finrank_eigenspace_of_orthonormalBasis c (fun i => ((e i : ℝ) : 𝕜)) hc ((r : ℝ) : 𝕜),
      Fintype.card_subtype, ← Finset.filter_val, Finset.card_val]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    simp [eq_comm]
  rw [hcount b d hb, hcount b' d' hb']

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
theorem adjComp_T_7_66_apply_basisFun (i : Fin 4) :
    (LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66) (EuclideanSpace.basisFun (Fin 4) 𝕜 i)
      = ![(9 : 𝕜), 4, 0, 9] i • EuclideanSpace.basisFun (Fin 4) 𝕜 i := by
  rw [adjComp_T_7_66_eq]
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.single,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

theorem finrank_eigenspace_adjComp_T_7_66 :
    finrank 𝕜 (Module.End.eigenspace (LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66) 9) = 2 ∧
      finrank 𝕜
          (Module.End.eigenspace (LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66) 4) = 1 ∧
      finrank 𝕜
          (Module.End.eigenspace (LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66) 0) = 1 := by
  classical
  have key : ∀ μ : 𝕜,
      finrank 𝕜 (Module.End.eigenspace (LinearMap.adjoint (T_7_66 (𝕜 := 𝕜)) ∘ₗ T_7_66) μ)
        = Fintype.card {i // ![(9 : 𝕜), 4, 0, 9] i = μ} := fun μ =>
    finrank_eigenspace_of_orthonormalBasis (EuclideanSpace.basisFun (Fin 4) 𝕜) _
      adjComp_T_7_66_apply_basisFun μ
  refine ⟨?_, ?_, ?_⟩
  · rw [key, Fintype.card_subtype,
      show (Finset.univ.filter fun i => ![(9 : 𝕜), 4, 0, 9] i = 9) = {0, 3} from ?_]
    · decide
    · ext i
      fin_cases i <;>
        norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
          Matrix.vecTail] <;> decide
  · rw [key, Fintype.card_subtype,
      show (Finset.univ.filter fun i => ![(9 : 𝕜), 4, 0, 9] i = 4) = {1} from ?_]
    · decide
    · ext i
      fin_cases i <;>
        norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
          Matrix.vecTail]
  · rw [key, Fintype.card_subtype,
      show (Finset.univ.filter fun i => ![(9 : 𝕜), 4, 0, 9] i = 0) = {2} from ?_]
    · decide
    · ext i
      fin_cases i <;>
        norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead,
          Matrix.vecTail] <;> decide

/-- 7.66 The singular values of {lit}`T` are {lit}`3, 3, 2, 0` — as a multiset, i.e. with
multiplicity, which is how 7.65 lists them. (This pin's
{name}`LinearMap.IsSymmetric.eigenvalues` are sorted decreasingly, so
{name}`singularValues` is in fact already Axler's decreasing list; the multiset form avoids
transporting along {lit}`finrank 𝕜 (EuclideanSpace 𝕜 (Fin 4)) = 4`.) -/
theorem singularValues_T_7_66 :
    Multiset.map (singularValues (T_7_66 (𝕜 := 𝕜))) Finset.univ.val = {3, 3, 2, 0} := by
  classical
  set T := T_7_66 (𝕜 := 𝕜) with hT
  set S := LinearMap.adjoint T ∘ₗ T with hS
  -- the standard basis diagonalizes `S` with eigenvalues `9, 4, 0, 9`
  have hstd : ∀ i, S (EuclideanSpace.basisFun (Fin 4) 𝕜 i)
      = ((![(9 : ℝ), 4, 0, 9] i : ℝ) : 𝕜) • EuclideanSpace.basisFun (Fin 4) 𝕜 i := by
    intro i
    rw [hS, hT, adjComp_T_7_66_apply_basisFun i]
    congr 1
    fin_cases i <;>
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
        RCLike.ofReal_ofNat, RCLike.ofReal_zero]
  -- so does the Gram–Schmidt eigenbasis, with eigenvalues `sᵢ²`
  have hmul := eigenvalues_multiset_eq_of_orthonormalBases (S := S) (svdBasis T)
    (fun i => singularValues T i ^ 2) (fun i => adjComp_apply_svdBasis T i)
    (EuclideanSpace.basisFun (Fin 4) 𝕜) ![(9 : ℝ), 4, 0, 9] hstd
  -- take square roots on both sides
  have hsq := congrArg (Multiset.map Real.sqrt) hmul
  simp only [Multiset.map_map, Function.comp] at hsq
  have hcast : Multiset.map (singularValues T) Finset.univ.val
      = Multiset.map (fun i => Real.sqrt (singularValues T i ^ 2)) Finset.univ.val :=
    Multiset.map_congr rfl fun i _ => (Real.sqrt_sq (singularValues_nonneg T i)).symm
  have h9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hcast, hsq, show (Finset.univ : Finset (Fin 4)).val = {0, 1, 2, 3} from rfl]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, h9, h4]
  refine Multiset.ext.mpr fun r => ?_
  by_cases h3 : r = 3 <;> by_cases h2' : r = 2 <;> by_cases h0 : r = 0 <;>
    simp_all []

/-! 7.67 Example: singular values of a linear map from {lit}`𝔽⁴` to {lit}`𝔽³`

For the {lit}`T ∈ ℒ(𝔽⁴, 𝔽³)` with matrix {lit}`!![0,0,0,-5; 0,0,0,0; 1,1,0,0]` in the
standard bases, the matrix of {lit}`T* T` is {lit}`!![1,1,0,0; 1,1,0,0; 0,0,0,0; 0,0,0,25]`,
whose eigenvalues are {lit}`25, 2, 0` with {lit}`dim E(25, T* T) = 1`,
{lit}`dim E(2, T* T) = 1` and {lit}`dim E(0, T* T) = 2`; so the singular values of
{lit}`T` are {lit}`5, √2, 0, 0`. -/

/-! Arithmetic helpers for the {lit}`√2` in Examples 7.67 and 7.79. Everything below treats
{lit}`√2` as an element of {lit}`𝕜` satisfying {lit}`c * c = 2`, so the computations are ring
arithmetic in {lit}`𝕜` with no {lit}`ℝ → 𝕜` coercion bookkeeping. -/

theorem ofReal_sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : 𝕜) * ((Real.sqrt 2 : ℝ) : 𝕜) = 2 := by
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), RCLike.ofReal_ofNat]

theorem ofReal_sqrt_two_sq : ((Real.sqrt 2 : ℝ) : 𝕜) ^ 2 = 2 := by
  rw [sq]; exact ofReal_sqrt_two_mul_self

theorem ofReal_sqrt_two_ne_zero : ((Real.sqrt 2 : ℝ) : 𝕜) ≠ 0 := by
  intro h
  have h2 := ofReal_sqrt_two_mul_self (𝕜 := 𝕜)
  rw [h, mul_zero] at h2
  exact two_ne_zero h2.symm

theorem ofReal_sqrt_two_inv :
    (((Real.sqrt 2)⁻¹ : ℝ) : 𝕜) = ((Real.sqrt 2 : ℝ) : 𝕜)⁻¹ := RCLike.ofReal_inv _

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

/-- 7.67 {lit}`T* T` is the operator of the matrix
{lit}`!![1,1,0,0; 1,1,0,0; 0,0,0,0; 0,0,0,25]`, the operator form of
{name}`conjTranspose_mul_A_7_67`. -/
theorem adjComp_T_7_67_eq :
    LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) ∘ₗ T_7_67 =
      Matrix.toEuclideanLin (!![1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 25] :
        Matrix (Fin 4) (Fin 4) 𝕜) := by
  have hadj : LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) = Matrix.toEuclideanLin (A_7_67 (𝕜 := 𝕜))ᴴ := by
    rw [T_7_67, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hmul : ∀ (M : Matrix (Fin 4) (Fin 3) 𝕜) (P : Matrix (Fin 3) (Fin 4) 𝕜),
      (M * P).toEuclideanLin = M.toEuclideanLin ∘ₗ P.toEuclideanLin := by
    intro M P; ext v
    simp only [LinearMap.comp_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec]
  rw [hadj, T_7_67, ← hmul, conjTranspose_mul_A_7_67]

/-- The orthonormal eigenbasis of {lit}`T* T` for Example 7.67:
{lit}`(1,1,0,0)/√2` and {lit}`(1,−1,0,0)/√2` diagonalize the {lit}`(1,1;1,1)` block, with
eigenvalues {lit}`2` and {lit}`0`, while the last two standard basis vectors give {lit}`0`
and {lit}`25`. Axler exhibits the first and last of these when computing the SVD in 7.79. -/
noncomputable def u_7_67 : Fin 4 → EuclideanSpace 𝕜 (Fin 4) :=
  ![!₂[(((Real.sqrt 2)⁻¹ : ℝ) : 𝕜), (((Real.sqrt 2)⁻¹ : ℝ) : 𝕜), 0, 0],
    !₂[(((Real.sqrt 2)⁻¹ : ℝ) : 𝕜), -(((Real.sqrt 2)⁻¹ : ℝ) : 𝕜), 0, 0],
    !₂[0, 0, 1, 0],
    !₂[0, 0, 0, 1]]

theorem orthonormal_u_7_67 : Orthonormal 𝕜 (u_7_67 (𝕜 := 𝕜)) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> rw [PiLp.inner_apply] <;>
    simp [u_7_67, RCLike.inner_apply, Fin.sum_univ_four, map_inv₀,
      RCLike.conj_ofReal, abs_of_nonneg (Real.sqrt_nonneg 2), ofReal_sqrt_two_sq] <;>
    field_simp <;> norm_num

/-- {lit}`u_7_67` is an orthonormal basis: four orthonormal vectors in a 4-dimensional
space. -/
noncomputable def basis_7_67 : OrthonormalBasis (Fin 4) 𝕜 (EuclideanSpace 𝕜 (Fin 4)) := by
  classical
  refine OrthonormalBasis.mk orthonormal_u_7_67 ?_
  have hcard : Fintype.card (Fin 4) = finrank 𝕜 (EuclideanSpace 𝕜 (Fin 4)) := by simp
  rw [← coe_basisOfOrthonormalOfCardEqFinrank orthonormal_u_7_67 hcard]
  exact (basisOfOrthonormalOfCardEqFinrank orthonormal_u_7_67 hcard).span_eq.ge

theorem basis_7_67_apply (i : Fin 4) : ⇑(basis_7_67 (𝕜 := 𝕜)) i = u_7_67 i := by
  rw [basis_7_67, OrthonormalBasis.coe_mk]

/-- The eigen-equations for {lit}`u_7_67`: {lit}`T* T uᵢ = dᵢ uᵢ` with
{lit}`d = (2, 0, 0, 25)`. -/
theorem adjComp_T_7_67_apply_basis (i : Fin 4) :
    (LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) ∘ₗ T_7_67) (⇑(basis_7_67 (𝕜 := 𝕜)) i)
      = ((![(2 : ℝ), 0, 0, 25] i : ℝ) : 𝕜) • ⇑(basis_7_67 (𝕜 := 𝕜)) i := by
  rw [adjComp_T_7_67_eq, basis_7_67_apply]
  ext k
  fin_cases i <;> fin_cases k <;>
    simp [u_7_67, Matrix.toLpLin_apply, RCLike.ofReal_ofNat, RCLike.ofReal_zero] <;>
    field_simp <;> ring

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
  classical
  have key : ∀ μ : 𝕜,
      finrank 𝕜 (Module.End.eigenspace (LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) ∘ₗ T_7_67) μ)
        = Fintype.card {i // ((![(2 : ℝ), 0, 0, 25] i : ℝ) : 𝕜) = μ} := fun μ =>
    finrank_eigenspace_of_orthonormalBasis basis_7_67 _ adjComp_T_7_67_apply_basis μ
  have hfilter : ∀ (μ : 𝕜) (t : Finset (Fin 4)),
      (Finset.univ.filter fun i => ((![(2 : ℝ), 0, 0, 25] i : ℝ) : 𝕜) = μ) = t →
      finrank 𝕜 (Module.End.eigenspace (LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) ∘ₗ T_7_67) μ)
        = t.card := by
    intro μ t ht
    rw [key, Fintype.card_subtype, ht]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro μ
    have hbot : Module.End.eigenspace (LinearMap.adjoint (T_7_67 (𝕜 := 𝕜)) ∘ₗ T_7_67) μ = ⊥
        ↔ Fintype.card {i // ((![(2 : ℝ), 0, 0, 25] i : ℝ) : 𝕜) = μ} = 0 := by
      rw [← key μ, Submodule.finrank_eq_zero]
    rw [Module.End.hasEigenvalue_iff, ne_eq, hbot, Fintype.card_eq_zero_iff,
      not_isEmpty_iff]
    constructor
    · rintro ⟨⟨i, hi⟩⟩
      fin_cases i <;>
        simp_all [RCLike.ofReal_ofNat, RCLike.ofReal_zero, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨3, by simp [RCLike.ofReal_ofNat]⟩⟩
      · exact ⟨⟨0, by simp [RCLike.ofReal_ofNat]⟩⟩
      · exact ⟨⟨1, by simp⟩⟩
  · rw [hfilter 25 {3} ?_]
    · decide
    · ext i
      fin_cases i <;>
        norm_num [RCLike.ofReal_ofNat, RCLike.ofReal_zero, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> decide
  · rw [hfilter 2 {0} ?_]
    · decide
    · ext i
      fin_cases i <;>
        norm_num [RCLike.ofReal_ofNat, RCLike.ofReal_zero, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  · rw [hfilter 0 {1, 2} ?_]
    · decide
    · ext i
      fin_cases i <;>
        norm_num [RCLike.ofReal_ofNat, RCLike.ofReal_zero, Matrix.cons_val_two,
          Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> decide

/-- 7.67 The singular values of {lit}`T` are {lit}`5, √2, 0, 0`, as a multiset. -/
theorem singularValues_T_7_67 :
    Multiset.map (singularValues (T_7_67 (𝕜 := 𝕜))) Finset.univ.val =
      {5, Real.sqrt 2, 0, 0} := by
  classical
  set T := T_7_67 (𝕜 := 𝕜) with hT
  have hmul := eigenvalues_multiset_eq_of_orthonormalBases
    (S := LinearMap.adjoint T ∘ₗ T) (svdBasis T) (fun i => singularValues T i ^ 2)
    (fun i => adjComp_apply_svdBasis T i) basis_7_67 ![(2 : ℝ), 0, 0, 25]
    (by rw [hT]; exact adjComp_T_7_67_apply_basis)
  have hsq := congrArg (Multiset.map Real.sqrt) hmul
  simp only [Multiset.map_map, Function.comp] at hsq
  have hcast : Multiset.map (singularValues T) Finset.univ.val
      = Multiset.map (fun i => Real.sqrt (singularValues T i ^ 2)) Finset.univ.val :=
    Multiset.map_congr rfl fun i _ => (Real.sqrt_sq (singularValues_nonneg T i)).symm
  have h25 : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs5 : Real.sqrt 2 ≠ 5 := by
    intro h
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    rw [h] at this
    norm_num at this
  rw [hcast, hsq, show (Finset.univ : Finset (Fin 4)).val = {0, 1, 2, 3} from rfl]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Real.sqrt_zero]
  refine Multiset.ext.mpr fun r => ?_
  by_cases h5 : r = 5
  · subst h5
    simp [h25, Ne.symm hs5,
      (by norm_num : (5 : ℝ) ≠ 0)]
  · by_cases hsr : r = Real.sqrt 2
    · subst hsr
      simp [h25, hs5, hs0]
    · by_cases h0 : r = 0
      · subst h0
        simp [h25, Ne.symm hs0, (by norm_num : (0 : ℝ) ≠ 5)]
      · simp [h25, h5, hsr, h0]

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


/-! 7.79 Example: finding a singular value decomposition

For the {lit}`T ∈ ℒ(𝔽⁴, 𝔽³)` of Example 7.67, {lit}`T(x₁,x₂,x₃,x₄) = (−5x₄, 0, x₁+x₂)`,
the positive eigenvalues of {lit}`T* T` are {lit}`25, 2` (each of multiplicity one), so the
positive singular values are {lit}`5, √2`. Orthonormal bases of the two eigenspaces are
{lit}`(0,0,0,1)` and {lit}`(1/√2, 1/√2, 0, 0)`, so following the proof of 7.70 Axler takes
{lit}`e₁ = (0,0,0,1)`, {lit}`e₂ = (1/√2, 1/√2, 0, 0)` and
{lit}`f₁ = T e₁ / 5 = (−1,0,0)`, {lit}`f₂ = T e₂ / √2 = (0,0,1)`, giving
{lit}`T v = 5⟨v, e₁⟩ f₁ + √2⟨v, e₂⟩ f₂`.

Where the eigenvalues came from is 7.67's computation; what makes *this* example checkable
on its own is that Axler's concluding "as expected, we see that …" is a direct verification:
the two lists are orthonormal and the formula holds, both by coordinate arithmetic. That is
what {lit}`svd_7_79` proves — no eigenvalue extraction needed. (Axler's {lit}`⟨v, eₖ⟩` is
mathlib's {lit}`⟪eₖ, v⟫`.) -/

/-- {lit}`e₁ = (0,0,0,1)`, {lit}`e₂ = (1/√2, 1/√2, 0, 0)`: the orthonormal list in
{lit}`𝔽⁴` of Example 7.79. -/
noncomputable def e_7_79 : Fin 2 → EuclideanSpace 𝕜 (Fin 4) :=
  ![!₂[0, 0, 0, 1], !₂[(((Real.sqrt 2)⁻¹ : ℝ) : 𝕜), (((Real.sqrt 2)⁻¹ : ℝ) : 𝕜), 0, 0]]

/-- {lit}`f₁ = T e₁ / 5 = (−1,0,0)`, {lit}`f₂ = T e₂ / √2 = (0,0,1)`: the orthonormal list
in {lit}`𝔽³` of Example 7.79. -/
def f_7_79 : Fin 2 → EuclideanSpace 𝕜 (Fin 3) :=
  ![!₂[-1, 0, 0], !₂[0, 0, 1]]

/-- 7.79 {lit}`T(x₁,x₂,x₃,x₄) = (−5x₄, 0, x₁+x₂)`, coordinate by coordinate. -/
theorem T_7_67_apply (v : EuclideanSpace 𝕜 (Fin 4)) :
    T_7_67 v 0 = -5 * v 3 ∧ T_7_67 v 1 = 0 ∧ T_7_67 v 2 = v 0 + v 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [T_7_67, A_7_67, Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_four]

/-- 7.79 Axler's lists really are a singular value decomposition of {lit}`T`: {lit}`e` is
orthonormal in {lit}`𝔽⁴`, {lit}`f` is orthonormal in {lit}`𝔽³`, and
{lit}`T v = 5 ⟪e₁, v⟫ f₁ + √2 ⟪e₂, v⟫ f₂` for every {lit}`v`. -/
theorem svd_7_79 :
    Orthonormal 𝕜 (e_7_79 (𝕜 := 𝕜)) ∧ Orthonormal 𝕜 (f_7_79 (𝕜 := 𝕜)) ∧
      ∀ v : EuclideanSpace 𝕜 (Fin 4), T_7_67 v =
        (5 : 𝕜) • ⟪e_7_79 0, v⟫_𝕜 • f_7_79 0 +
          (((Real.sqrt 2 : ℝ) : 𝕜)) • ⟪e_7_79 1, v⟫_𝕜 • f_7_79 1 := by
  -- Treat `√2` as an element of `𝕜` with `c * c = 2`; then everything below is ring
  -- arithmetic in `𝕜` and no `ℝ → 𝕜` coercion lemma is needed.
  have hc2 : ((Real.sqrt 2 : ℝ) : 𝕜) * ((Real.sqrt 2 : ℝ) : 𝕜) = 2 := by
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      RCLike.ofReal_ofNat]
  have hcne : ((Real.sqrt 2 : ℝ) : 𝕜) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc2
    exact two_ne_zero hc2.symm
  have hinv : (((Real.sqrt 2)⁻¹ : ℝ) : 𝕜) = ((Real.sqrt 2 : ℝ) : 𝕜)⁻¹ := RCLike.ofReal_inv _
  have hcsq : ((Real.sqrt 2 : ℝ) : 𝕜) ^ 2 = 2 := by rw [sq]; exact hc2
  refine ⟨?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      (rw [PiLp.inner_apply]
       simp [e_7_79, RCLike.inner_apply, Fin.sum_univ_four, hinv, map_inv₀,
         RCLike.conj_ofReal, abs_of_nonneg (Real.sqrt_nonneg 2), hcsq]
       try field_simp
       try norm_num)
  · rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> rw [PiLp.inner_apply] <;>
      simp [f_7_79, RCLike.inner_apply, Fin.sum_univ_three]
  · intro v
    obtain ⟨hT0, hT1, hT2⟩ := T_7_67_apply (𝕜 := 𝕜) v
    have he0 : ⟪e_7_79 (𝕜 := 𝕜) 0, v⟫_𝕜 = v 3 := by
      rw [PiLp.inner_apply]
      simp [e_7_79, RCLike.inner_apply, Fin.sum_univ_four]
    have he1 : ⟪e_7_79 (𝕜 := 𝕜) 1, v⟫_𝕜
        = ((Real.sqrt 2 : ℝ) : 𝕜)⁻¹ * v 0 + ((Real.sqrt 2 : ℝ) : 𝕜)⁻¹ * v 1 := by
      rw [PiLp.inner_apply]
      simp [e_7_79, RCLike.inner_apply, Fin.sum_univ_four, hinv, map_inv₀,
        RCLike.conj_ofReal, mul_comm]
    ext k
    fin_cases k <;>
      simp [hT0, hT1, hT2, he0, he1, f_7_79, RCLike.real_smul_eq_coe_mul]

/-- The {lit}`(k,l)` entry of {lit}`A` read off the SVD of {lit}`Matrix.toEuclideanLin A`:
`A k l = ∑ᵢ sᵢ conj(eᵢ l) fᵢ k` (the {lit}`sᵢ = 0` terms vanish).

This is the entrywise form of 7.71, and it exists only as a step in the proof of 7.80
below: that proof compares {lit}`A k l` with {lit}`(B D Cᴴ) k l`, whose expansion is
exactly the right-hand side here. Axler does it inline; it is separated out because
getting from the SVD formula to a single entry (apply it to
{lit}`EuclideanSpace.single l 1`, then read coordinate {lit}`k`) takes long enough to
obscure the entry comparison. -/
theorem toEuclideanLin_entry_eq_svd {p n : ℕ} (A : Matrix (Fin p) (Fin n) 𝕜)
    (k : Fin p) (l : Fin n) :
    A k l = ∑ i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin n))),
      (singularValues (Matrix.toEuclideanLin A) i : 𝕜)
      * (starRingEnd 𝕜) (svdBasis (Matrix.toEuclideanLin A) i l)
      * svdImage (Matrix.toEuclideanLin A) i k := by
  set T := Matrix.toEuclideanLin A with hTdef
  have hL := congrArg (⇑(EuclideanSpace.equiv (Fin p) 𝕜))
    (svd_apply T (EuclideanSpace.single l (1 : 𝕜)))
  rw [map_sum] at hL
  simp only [map_smul] at hL
  have hLk := congrFun hL k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hLk
  have hAkl : A k l = (⇑(EuclideanSpace.equiv (Fin p) 𝕜)
      (T (EuclideanSpace.single l (1:𝕜)))) k := by
    rw [hTdef, Matrix.toLpLin_apply]
    simp [EuclideanSpace.single, Matrix.mulVec_single]
  rw [hAkl, hLk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.inner_single_right]
  simp only [show ∀ (w : EuclideanSpace 𝕜 (Fin p)) (m : Fin p),
    ⇑(EuclideanSpace.equiv (Fin p) 𝕜) w m = w m from fun _ _ => rfl, one_mul]
  ring

/-- Axler's index set {lit}`1, …, m` in 7.80: the indices carrying a *positive* singular
value of {lit}`A`. Its cardinality is {lit}`A.rank`
({lit}`rank_eq_card_posSingularIdx`), so using it as the middle index of the
factorization is Axler's "rank {lit}`m`" without a numeral and an equation to carry
around. -/
abbrev posSingularIdx {p n : ℕ} (A : Matrix (Fin p) (Fin n) 𝕜) :=
  {i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin n))) //
    singularValues (Matrix.toEuclideanLin A) i ≠ 0}

/-- The number of positive singular values of {lit}`A` is the rank of {lit}`A`: 7.68(b)
({name}`card_pos_singularValues_eq_finrank_range`) transported from
{lit}`dim range (toEuclideanLin A)` to {name}`Matrix.rank` along
{name}`Matrix.rank_eq_finrank_range_toLin`. -/
theorem rank_eq_card_posSingularIdx {p n : ℕ} (A : Matrix (Fin p) (Fin n) 𝕜) :
    A.rank = Fintype.card (posSingularIdx A) := by
  rw [Matrix.rank_eq_finrank_range_toLin A (EuclideanSpace.basisFun (Fin p) 𝕜).toBasis
      (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis,
    ← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact (card_pos_singularValues_eq_finrank_range _).symm

/-- 7.80 Matrix version of the SVD, in Axler's generality: a {lit}`p`-by-{lit}`n` matrix
{lit}`A` of rank {lit}`m` factors as {lit}`A = B D Cᴴ` where {lit}`B` is
{lit}`p`-by-{lit}`m` with orthonormal columns, {lit}`D` is {lit}`m`-by-{lit}`m` diagonal
with positive numbers on the diagonal, and {lit}`C` is {lit}`n`-by-{lit}`m` with
orthonormal columns.

Here {lit}`m` is {name}`posSingularIdx` {lit}`A`, of cardinality {lit}`A.rank`. Following
Axler's proof, the columns of {lit}`B` are the image vectors {lit}`fₖ`, the columns of
{lit}`C` are the eigenbasis vectors {lit}`eₖ`, and {lit}`D` holds the positive singular
values {lit}`sₖ` — but as with 7.70, Axler's statement asserts only that {lit}`D` is
diagonal with positive entries, not what those entries are, so neither does this one.
"Orthonormal columns" is read as Axler reads it, "orthonormal with respect to the standard
Euclidean inner product": the columns {lit}`B.col i` as vectors of {lit}`EuclideanSpace`.
That is equivalent to {lit}`Bᴴ B = Cᴴ C = 1`, because {lit}`(Bᴴ B) i j` *is* the inner
product of columns {lit}`i` and {lit}`j`
({name}`LADR.Section_7D.orthonormal_columns_iff`, which is how the proof below discharges
it). The positive diagonal is {name}`LADR.Section_7D.HasPosRealDiag`.

Axler's hypothesis {lit}`m ≥ 1` is not needed: for {lit}`A = 0` the index type is empty and
the factorization holds trivially. -/
theorem matrix_svd {p n : ℕ} (A : Matrix (Fin p) (Fin n) 𝕜) :
    ∃ (B : Matrix (Fin p) (posSingularIdx A) 𝕜) (C : Matrix (Fin n) (posSingularIdx A) 𝕜)
      (D : Matrix (posSingularIdx A) (posSingularIdx A) 𝕜),
      Orthonormal 𝕜 (fun i => (WithLp.toLp 2 (B.col i) : EuclideanSpace 𝕜 (Fin p))) ∧
        Orthonormal 𝕜 (fun i => (WithLp.toLp 2 (C.col i) : EuclideanSpace 𝕜 (Fin n))) ∧
        D.IsDiag ∧ LADR.Section_7D.HasPosRealDiag D ∧ A = B * D * Cᴴ := by
  classical
  set T := Matrix.toEuclideanLin A with hTdef
  refine ⟨Matrix.of fun k i => svdImage T i.1 k, Matrix.of fun k i => svdBasis T i.1 k,
    Matrix.diagonal fun i => (singularValues T i.1 : 𝕜),
    (LADR.Section_7D.orthonormal_columns_iff _).mpr ?_,
    (LADR.Section_7D.orthonormal_columns_iff _).mpr ?_,
    fun _ _ hij => Matrix.diagonal_apply_ne _ hij, fun i => ?_, ?_⟩
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
  · -- the diagonal entries are positive reals: `sᵢ ≥ 0` and `sᵢ ≠ 0`
    rw [Matrix.diagonal_apply_eq]
    exact ⟨by rw [RCLike.ofReal_re]
              exact lt_of_le_of_ne (singularValues_nonneg T i.1) (Ne.symm i.2),
      by rw [RCLike.ofReal_im]⟩
  · ext k l
    rw [Matrix.mul_assoc, Matrix.mul_apply, toEuclideanLin_entry_eq_svd A k l]
    rw [show (∑ i : Fin (finrank 𝕜 (EuclideanSpace 𝕜 (Fin n))),
        (singularValues T i : 𝕜) * (starRingEnd 𝕜) (svdBasis T i l) * svdImage T i k)
        = ∑ i : posSingularIdx A,
          (singularValues T i.1 : 𝕜) * (starRingEnd 𝕜) (svdBasis T i.1 l) * svdImage T i.1 k
      from ?_]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [Matrix.diagonal_apply_eq, Matrix.of_apply, Matrix.conjTranspose_apply,
          Matrix.of_apply, RCLike.star_def]; ring
      · intro b _ hb; rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [← Finset.sum_subtype (Finset.univ.filter fun i => singularValues T i ≠ 0)
        (fun x => by simp [hTdef]) fun i => (singularValues T i : 𝕜)
          * (starRingEnd 𝕜) (svdBasis T i l) * svdImage T i k]
      exact (Finset.sum_filter_of_ne fun i _ hne => by
        intro hz
        exact hne (by rw [hz, RCLike.ofReal_zero, zero_mul, zero_mul])).symm

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

/-- The operator of 7E.3, to be supplied by the solver: the exercise says "give an example",
so the witness is the answer and the two properties below are the obligations. -/
noncomputable def T_7E_3 : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2) := sorry

/-- 7E.3 Give an example of {lit}`T ∈ ℒ(ℂ²)` whose only eigenvalue is {lit}`0` but whose
singular values are {lit}`5, 0`. Here the *numbers* are Axler's, so they appear in the
statement; what the solver supplies is {lit}`T_7E_3`. The singular values are compared as an
ordered list, which is legitimate because {name}`singularValues_antitone` says
{name}`singularValues` is already listed decreasingly, as in 7.65. -/
theorem exercise_7E_3 :
    (∀ μ : ℂ, HasEigenvalue T_7E_3 μ ↔ μ = 0) ∧
      List.ofFn (singularValues T_7E_3) = [5, 0] := by
  sorry

/-- 7E.4 With {lit}`s₁` the largest and {lit}`sₙ` the smallest singular value,
{lit}`{‖Tv‖ : ‖v‖ = 1} = [sₙ, s₁]`. -/
theorem exercise_7E_4 (T : V →ₗ[𝕜] W) (s₁ sₙ : ℝ)
    (h1 : IsGreatest (Set.range (singularValues T)) s₁)
    (hn : IsLeast (Set.range (singularValues T)) sₙ) :
    {r : ℝ | ∃ v : V, ‖v‖ = 1 ∧ ‖T v‖ = r} = Set.Icc sₙ s₁ := by
  sorry

/-- The singular values of the operator of 7E.5 — the numbers to be found by the solver,
as with {lit}`singularValues_7E_6` below. -/
noncomputable def singularValues_7E_5 : Fin 2 → ℝ := sorry

/-- 7E.5 Find the singular values of {lit}`T(x, y) = (−4y, x)` on {lit}`ℂ²`. The answer is
{lit}`singularValues_7E_5`: stating it that way leaves the numbers to the solver instead of
giving them away in the statement. The two are compared as ordered lists —
{name}`List.ofFn` avoids transporting along
{lit}`finrank ℂ (EuclideanSpace ℂ (Fin 2)) = 2`, and the order is meaningful because
{name}`singularValues_antitone` lists them decreasingly. -/
theorem exercise_7E_5 (T : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] EuclideanSpace ℂ (Fin 2))
    (hT : ∀ z : EuclideanSpace ℂ (Fin 2), T z = !₂[-4 * z 1, z 0]) :
    List.ofFn (singularValues T) = List.ofFn singularValues_7E_5 := by
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
      (D p : Polynomial ℝ) = (p : Polynomial ℝ).derivative) :
    List.ofFn (singularValues D) = List.ofFn singularValues_7E_6 := by
  sorry

/-- 7E.7(a) For self-adjoint {lit}`T`, the singular values of {lit}`T` are the absolute
values of its eigenvalues.

Two things about the phrasing. First, Axler's hypothesis is "{lit}`T` is self-adjoint, *or*
{lit}`𝔽 = ℂ` and {lit}`T` is normal" — two separate problems, so they are (a) and (b) here.
Second, his conclusion counts multiplicities ("each included as many times as the dimension
of the corresponding eigenspace", then sorted decreasingly), so the comparison is of
*multisets*: a pointwise claim would be false, since taking absolute values need not preserve
the decreasing order (from {lit}`1, −5` one gets {lit}`1, 5`). The eigenvalues with
multiplicity are the roots of the characteristic polynomial
({name}`Module.End.hasEigenvalue_iff_isRoot_charpoly`); for the diagonalizable operators in
this exercise root multiplicity is exactly the eigenspace dimension Axler counts. -/
theorem exercise_7E_7a (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) :
    Multiset.map (singularValues T) Finset.univ.val
      = (LinearMap.charpoly T).roots.map (fun μ => ‖μ‖) := by
  sorry

/-- 7E.7(b) The other half of 7E.7: over {lit}`ℂ` the same holds for *normal* {lit}`T`. -/
theorem exercise_7E_7b {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : IsStarNormal T) :
    Multiset.map (singularValues T) Finset.univ.val
      = (LinearMap.charpoly T).roots.map (fun μ => ‖μ‖) := by
  sorry

/-- 7E.8(a) In an SVD, {lit}`f₁, …, fₘ` is an orthonormal basis of {lit}`range T`.

The conclusion is spelled as {lit}`span {f₁, …, fₘ} = range T`, which for an *orthonormal*
family is the same as "is an orthonormal basis of {lit}`range T`": orthonormal families are
linearly independent ({name}`Orthonormal.linearIndependent`), and a linearly independent
spanning family is a basis ({lit}`Basis.mk`). So the only content left to prove is the
spanning, and no basis needs to be constructed to state it. (The same reading is used in
7.68(b) above, where {lit}`svdImage` spans {lit}`range T`.) -/
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

/-- 7E.8(c) In an SVD, {lit}`s₁, …, sₘ` are the positive singular values of {lit}`T`.

Compared as multisets, not as sets of values: Axler's {lit}`s₁, …, sₘ` is a list, so a
repeated singular value has to appear as often on both sides. The set reading is strictly
weaker — it would accept {lit}`s = (2, 2)` for an operator whose only positive singular value
is a single {lit}`2`. Filtering by {lit}`0 < r` drops the zero singular values, which have no
counterpart among the {lit}`sₖ` (positive by hypothesis). -/
theorem exercise_7E_8c {m : ℕ} (T : V →ₗ[𝕜] W) (e : Fin m → V) (f : Fin m → W)
    (s : Fin m → ℝ) (hs : ∀ i, 0 < s i) (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f)
    (hT : ∀ v, T v = ∑ i, (s i : 𝕜) • ⟪e i, v⟫_𝕜 • f i) :
    Multiset.filter (fun r => 0 < r) (Multiset.map (singularValues T) Finset.univ.val)
      = Multiset.map s Finset.univ.val := by
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

/-- 7E.9 {lit}`T` and {lit}`T*` have the same positive singular values — as multisets, so
with multiplicity, as in 7E.8(c). The two lists are indexed by {lit}`Fin (dim V)` and
{lit}`Fin (dim W)` respectively, which the multiset comparison bridges without a cast. -/
theorem exercise_7E_9 (T : V →ₗ[𝕜] W) :
    Multiset.filter (fun r => 0 < r) (Multiset.map (singularValues T) Finset.univ.val)
      = Multiset.filter (fun r => 0 < r)
          (Multiset.map (singularValues (LinearMap.adjoint T)) Finset.univ.val) := by
  sorry

/-- 7E.10 If {lit}`T` is invertible, then the singular values of {lit}`T⁻¹` are the
reciprocals of those of {lit}`T`.

As multisets, with multiplicity, as in 7E.8(c) and 7E.9. Axler writes the answer as
{lit}`1/sₙ, …, 1/s₁`: reciprocation reverses the order, and the list has to come back sorted
decreasingly — a multiset comparison makes that bookkeeping unnecessary. No {lit}`sᵢ ≠ 0`
guard is needed either, since an invertible {lit}`T` has all singular values positive
({name}`injective_iff_singularValues_ne_zero`, 7.68(a)). -/
theorem exercise_7E_10 (T : V ≃ₗ[𝕜] V) :
    Multiset.map (singularValues (T.symm : V →ₗ[𝕜] V)) Finset.univ.val
      = Multiset.map (fun i => (singularValues (T : V →ₗ[𝕜] V) i)⁻¹) Finset.univ.val := by
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
    ∑ j, ⟪c j, T (c j)⟫_𝕜 = ((∑ i, singularValues T i : ℝ) : 𝕜) := by
  sorry

/-- The operator of 7E.12(a), to be supplied by the solver: the exercise says "give an
example", so the witness is the answer, as in 7E.3 and 7E.5. -/
noncomputable def T_7E_12a : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) := sorry

/-- 7E.12(a) Give an operator whose {lit}`T²` singular values are not the squares of the
singular values of {lit}`T`. Compared as multisets, so the counterexample may also be one
where the two lists agree as *sets* but not with multiplicity. -/
theorem exercise_7E_12a :
    Multiset.map (singularValues (T_7E_12a (𝕜 := 𝕜) ∘ₗ T_7E_12a)) Finset.univ.val ≠
      Multiset.map (fun i => singularValues (T_7E_12a (𝕜 := 𝕜)) i ^ 2) Finset.univ.val := by
  sorry

/-- 7E.12(b) For normal {lit}`T`, the singular values of {lit}`T²` are the squares
of the singular values of {lit}`T` — as multisets, with multiplicity. -/
theorem exercise_7E_12b (T : V →ₗ[𝕜] V) (hN : IsStarNormal T) :
    Multiset.map (singularValues (T ∘ₗ T)) Finset.univ.val
      = Multiset.map (fun i => singularValues T i ^ 2) Finset.univ.val := by
  sorry

/-- 7E.13 {lit}`T₁, T₂` have the same singular values iff {lit}`T₁ = S₁ T₂ S₂` for
unitary {lit}`S₁, S₂`. "Same singular values" as multisets, with multiplicity: the set
reading would be false here — {lit}`diag(1,1)` and {lit}`diag(1,0)`… have different
multiplicities but overlapping value sets, and no unitary pair relates operators whose
singular values differ in multiplicity. -/
theorem exercise_7E_13 (T₁ T₂ : V →ₗ[𝕜] V) :
    (Multiset.map (singularValues T₁) Finset.univ.val
        = Multiset.map (singularValues T₂) Finset.univ.val) ↔
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
