import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Data.List.TFAE
import LinearAlgebraDoneRightLean.Section_7B
import LinearAlgebraDoneRightLean.Section_7C
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7D: Isometries, Unitary Operators, and Matrix Factorization
-/

namespace LADR.Section_7D

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate Matrix
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! # Isometries -/

/-! 7.44 Definition: isometry

A linear map {lit}`S ∈ ℒ(V, W)` is an *isometry* if {lit}`‖S v‖ = ‖v‖` for every
{lit}`v` — i.e. it preserves norms. mathlib packages norm-preserving linear maps
as {name}`LinearIsometry`; here we work with the predicate on ordinary linear
maps to stay close to Axler. -/

def IsIsometry (S : V →ₗ[𝕜] W) : Prop := ∀ v, ‖S v‖ = ‖v‖

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- Every isometry is injective (if {lit}`S v = 0` then {lit}`‖v‖ = ‖S v‖ = 0`). -/
theorem IsIsometry.injective {S : V →ₗ[𝕜] W} (h : IsIsometry S) : Function.Injective S := by
  intro a b hab
  have h0 : ‖a - b‖ = 0 := by rw [← h (a - b), map_sub, hab, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-! 7.45 Example: if {lit}`S` maps an orthonormal basis {lit}`e₁, …, eₙ` of
{lit}`V` to an orthonormal list {lit}`g₁, …, gₙ` in {lit}`W`, then {lit}`S` is an
isometry.

We prove the sharper fact that such an {lit}`S` *preserves inner products*: writing
{lit}`u, v` in the basis {lit}`e` and using the orthonormality of the {lit}`gₖ`
collapses the double sum to {name}`OrthonormalBasis.sum_inner_mul_inner`. This is
also the engine of the equivalences (a) ⟺ (c) ⟺ (d) in 7.49. -/

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
theorem isometry_of_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] W)
    (h : Orthonormal 𝕜 (fun i => S (b i))) (u v : V) :
    ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜 := by
  have hSu : S u = ∑ i, ⟪b i, u⟫_𝕜 • S (b i) := by
    conv_lhs => rw [← b.sum_repr' u]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hSv : S v = ∑ i, ⟪b i, v⟫_𝕜 • S (b i) := by
    conv_lhs => rw [← b.sum_repr' v]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [hSu, hSv, sum_inner, ← b.sum_inner_mul_inner u v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp h) i i, if_pos rfl,
      mul_one, inner_conj_symm]
  · intro j _ hij
    rw [inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp h) i j,
      if_neg (Ne.symm hij), mul_zero, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- 7.45, as stated by Axler: the map is an isometry. -/
theorem isometry_of_orthonormal_image_isometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] W)
    (h : Orthonormal 𝕜 (fun i => S (b i))) : IsIsometry S :=
  (LinearMap.norm_map_iff_inner_map_map S).mpr fun u v =>
    isometry_of_orthonormal_image b S h u v

/-! 7.49 Characterizations of isometries

For {lit}`S ∈ ℒ(V, W)` with orthonormal bases {lit}`e` of {lit}`V` and {lit}`f`
of {lit}`W`, the following are equivalent:
(a) {lit}`S` is an isometry;
(b) {lit}`S* S = I`;
(c) {lit}`⟨S u, S v⟩ = ⟨u, v⟩` for all {lit}`u, v`;
(d) {lit}`S e₁, …, S eₙ` is an orthonormal list;
(e) the columns of {lit}`ℳ(S, e, f)` form an orthonormal list in {lit}`𝔽ᵐ`.

(a) ⟺ (c) is {name}`LinearMap.norm_map_iff_inner_map_map`. We prove (c) ⟺ (b)
and (a) ⟺ (d) below. Condition (e) is the matrix restatement of (d) once the
columns of {lit}`ℳ(S, e, f)` are identified with the coordinate vectors of the
{lit}`S eₖ`; it adds no mathematical content over (d) and is not separately
formalized here. -/

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- (a) ⟺ (c): an isometry is exactly an inner-product-preserving map. -/
theorem isometry_iff_inner (S : V →ₗ[𝕜] W) :
    IsIsometry S ↔ ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜 :=
  LinearMap.norm_map_iff_inner_map_map S

/-- (c) ⟺ (b): preserving inner products is equivalent to {lit}`S* S = I`. -/
theorem inner_iff_adjoint_comp (S : V →ₗ[𝕜] W) :
    (∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜) ↔ LinearMap.adjoint S ∘ₗ S = 1 := by
  constructor
  · intro h; ext u
    refine ext_inner_right 𝕜 fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, Module.End.one_apply, h]
  · intro h u v
    have hu := LinearMap.congr_fun h u
    rw [LinearMap.comp_apply, Module.End.one_apply] at hu
    rw [← LinearMap.adjoint_inner_left, hu]

/-- (a) ⟺ (b). -/
theorem isometry_iff_adjoint_comp (S : V →ₗ[𝕜] W) :
    IsIsometry S ↔ LinearMap.adjoint S ∘ₗ S = 1 :=
  (isometry_iff_inner S).trans (inner_iff_adjoint_comp S)

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- (a) ⟺ (d): {lit}`S` is an isometry iff it carries some (hence any) orthonormal
basis to an orthonormal list. -/
theorem isometry_iff_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] W) :
    IsIsometry S ↔ Orthonormal 𝕜 (fun i => S (b i)) := by
  constructor
  · intro h
    rw [orthonormal_iff_ite]
    intro i j
    rw [(isometry_iff_inner S).mp h (b i) (b j)]
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  · exact isometry_of_orthonormal_image_isometry b S

/-! # Unitary Operators -/

/-! 7.51 Definition: unitary operator

An operator {lit}`S ∈ ℒ(V)` is *unitary* if it is an invertible isometry. Since
{lit}`V` is finite-dimensional, every isometry is already invertible (injective +
finite dimension ⟹ bijective), so the word "invertible" is redundant here; we keep
it for faithfulness to the definition. -/

def IsUnitary (S : V →ₗ[𝕜] V) : Prop := Function.Bijective S ∧ IsIsometry S

/-- On a finite-dimensional space an isometry is automatically bijective. -/
theorem IsIsometry.bijective {S : V →ₗ[𝕜] V} (h : IsIsometry S) : Function.Bijective S :=
  ⟨h.injective, LinearMap.injective_iff_surjective.mp h.injective⟩

/-- Hence on {lit}`ℒ(V)` "unitary" and "isometry" coincide. -/
theorem isUnitary_iff_isometry (S : V →ₗ[𝕜] V) : IsUnitary S ↔ IsIsometry S :=
  ⟨fun h => h.2, fun h => ⟨h.bijective, h⟩⟩

/-! 7.52 Example: rotation of {lit}`ℝ²`

The matrix {lit}`((cos θ, -sin θ), (sin θ, cos θ))` has orthonormal columns, so the
associated operator on {lit}`ℝ²` is an isometry, hence unitary. We record this as
membership of the rotation matrix in mathlib's {name}`Matrix.unitaryGroup`. -/

noncomputable def rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotationMatrix_mem_unitaryGroup (θ : ℝ) :
    rotationMatrix θ ∈ Matrix.unitaryGroup (Fin 2) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.star_eq_conjTranspose] <;>
    ring_nf <;>
    linarith [Real.sin_sq_add_cos_sq θ, Real.cos_sq_add_sin_sq θ]

/-! 7.53 Characterizations of unitary operators

For {lit}`S ∈ ℒ(V)` with orthonormal basis {lit}`e`, the following are equivalent:
(a) {lit}`S` unitary; (b) {lit}`S* S = S S* = I`; (c) {lit}`S` invertible with
{lit}`S⁻¹ = S*`; (d) {lit}`S e₁, …, S eₙ` is an orthonormal basis; (e) the rows of
{lit}`ℳ(S, e)` are orthonormal; (f) {lit}`S*` is unitary.

We prove (a) ⟺ (b), (a) ⟺ (d), and (a) ⟺ (f). Statement (c) is the reading of (b)
as "{lit}`S*` is the two-sided inverse", recorded in {lit}`isUnitary_inverse`; (e) is
the matrix restatement of the columns/rows exchange (Exercise 13) and is not
separately formalized. -/

/-- (a) ⟺ (b). -/
theorem isUnitary_iff_adjoint (S : V →ₗ[𝕜] V) :
    IsUnitary S ↔ LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1 := by
  constructor
  · rintro ⟨hbij, hiso⟩
    have hSS : LinearMap.adjoint S ∘ₗ S = 1 := (isometry_iff_adjoint_comp S).mp hiso
    refine ⟨hSS, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := hbij.surjective w
    have hx : LinearMap.adjoint S (S x) = x := by
      have := LinearMap.congr_fun hSS x
      rwa [LinearMap.comp_apply, Module.End.one_apply] at this
    rw [LinearMap.comp_apply, hx, Module.End.one_apply]
  · rintro ⟨h1, h2⟩
    have hiso : IsIsometry S := (isometry_iff_adjoint_comp S).mpr h1
    refine ⟨Function.bijective_iff_has_inverse.mpr
      ⟨LinearMap.adjoint S, fun x => ?_, fun x => ?_⟩, hiso⟩
    · have := LinearMap.congr_fun h1 x
      rwa [LinearMap.comp_apply, Module.End.one_apply] at this
    · have := LinearMap.congr_fun h2 x
      rwa [LinearMap.comp_apply, Module.End.one_apply] at this

/-- (c): for a unitary operator, {lit}`S*` is a two-sided inverse of {lit}`S`. -/
theorem isUnitary_inverse {S : V →ₗ[𝕜] V} (h : IsUnitary S) :
    LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1 :=
  (isUnitary_iff_adjoint S).mp h

/-- (a) ⟺ (d). -/
theorem isUnitary_iff_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] V) :
    IsUnitary S ↔ Orthonormal 𝕜 (fun i => S (b i)) :=
  (isUnitary_iff_isometry S).trans (isometry_iff_orthonormal_image b S)

/-- (a) ⟺ (f): {lit}`S` is unitary iff {lit}`S*` is unitary. -/
theorem isUnitary_adjoint_iff (S : V →ₗ[𝕜] V) :
    IsUnitary S ↔ IsUnitary (LinearMap.adjoint S) := by
  rw [isUnitary_iff_adjoint, isUnitary_iff_adjoint, LinearMap.adjoint_adjoint, and_comm]

/-! 7.54 Eigenvalues of unitary operators have absolute value 1.

If {lit}`S v = λ v` with {lit}`v ≠ 0`, then
{lit}`|λ| ‖v‖ = ‖λ v‖ = ‖S v‖ = ‖v‖`, so {lit}`|λ| = 1`. -/

omit [FiniteDimensional 𝕜 V] in
theorem unitary_eigenvalue_abs_one {S : V →ₗ[𝕜] V} (h : IsUnitary S) {μ : 𝕜}
    (hμ : HasEigenvalue S μ) : ‖μ‖ = 1 := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hmem : S v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hn : ‖v‖ = ‖μ‖ * ‖v‖ := by
    have hsv : ‖S v‖ = ‖μ‖ * ‖v‖ := by rw [hmem, norm_smul]
    rw [← hsv, h.2 v]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have h1 : ‖μ‖ * ‖v‖ = 1 * ‖v‖ := by rw [one_mul]; linarith [hn]
  exact mul_right_cancel₀ (ne_of_gt hvpos) h1

/-! 7.55 Description of unitary operators on complex inner product spaces.

Over {lit}`ℂ`, {lit}`S` is unitary iff there is an orthonormal basis of eigenvectors
whose eigenvalues all have absolute value 1. Forward: a unitary operator is normal
({lit}`S* S = S S* = I`), so the complex spectral theorem
({module -checked}`LinearAlgebraDoneRightLean.Section_7B`) supplies an orthonormal
eigenbasis, and 7.54 gives {lit}`|λ| = 1`. Backward: such a basis makes
{lit}`S e₁, …, S eₙ` orthonormal, so {lit}`S` is an isometry, hence unitary. -/

theorem unitary_iff_orthonormal_eigenbasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) :
    IsUnitary S ↔ ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ E),
      ∀ i, ∃ μ : ℂ, S (e i) = μ • e i ∧ ‖μ‖ = 1 := by
  constructor
  · intro hS
    obtain ⟨h1, h2⟩ := (isUnitary_iff_adjoint S).mp hS
    have hnorm : IsStarNormal S :=
      (LADR.Section_7A.normal_iff_comp S).mpr (by rw [h1, h2])
    obtain ⟨n, e, he⟩ := LADR.Section_7B.complex_spectral S hnorm
    refine ⟨n, e, fun i => ⟨⟪e i, S (e i)⟫_ℂ, he i, ?_⟩⟩
    have hnormeq : ‖S (e i)‖ = ‖e i‖ := hS.2 (e i)
    rw [he i, norm_smul, e.orthonormal.1 i, mul_one] at hnormeq
    exact hnormeq
  · rintro ⟨n, e, he⟩
    have horth : Orthonormal ℂ (fun i => S (e i)) := by
      rw [orthonormal_iff_ite]
      intro i j
      rcases eq_or_ne i j with hEq | hNe
      · subst hEq
        obtain ⟨μi, hi, hni⟩ := he i
        have he1 : ⟪e i, e i⟫_ℂ = 1 := by
          rw [(orthonormal_iff_ite.mp e.orthonormal) i i, if_pos rfl]
        rw [hi, inner_smul_left, inner_smul_right, he1, mul_one, RCLike.conj_mul, hni, if_pos rfl]
        norm_num
      · obtain ⟨μi, hi, hni⟩ := he i
        obtain ⟨μj, hj, hnj⟩ := he j
        rw [hi, hj, inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp e.orthonormal) i j]
        simp only [if_neg hNe, mul_zero]
    have hiso : IsIsometry S := isometry_of_orthonormal_image_isometry e S horth
    exact ⟨hiso.bijective, hiso⟩

/-! # QR Factorization -/

/-! 7.56 Definition: unitary matrix

An {lit}`n`-by-{lit}`n` matrix is *unitary* if its columns form an orthonormal list
in {lit}`𝔽ⁿ`. Equivalently (Euclidean inner product of columns {lit}`k, r` equals
{lit}`(Q* Q)ₖᵣ`), {lit}`Q* Q = I`. This is mathlib's {name}`Matrix.unitaryGroup`. -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

def IsUnitaryMatrix (Q : Matrix n n 𝕜) : Prop := Q ∈ Matrix.unitaryGroup n 𝕜

/-! 7.57 Characterizations of unitary matrices

For a square matrix {lit}`Q`: (a) {lit}`Q` unitary (columns orthonormal); (b) rows
orthonormal; (c) {lit}`‖Q v‖ = ‖v‖`; (d) {lit}`Q* Q = Q Q* = I`. Axler leaves the
proof as Exercise 17. The core equivalence (a) ⟺ (d) is immediate from mathlib's
{name}`Matrix.mem_unitaryGroup_iff` / {name}`Matrix.mem_unitaryGroup_iff'`, using
{lit}`star Q = Q*` (the conjugate transpose). -/

theorem isUnitaryMatrix_iff_conjTranspose (Q : Matrix n n 𝕜) :
    IsUnitaryMatrix Q ↔ Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 := by
  rw [IsUnitaryMatrix, ← Matrix.star_eq_conjTranspose]
  constructor
  · intro h
    exact ⟨(Matrix.mem_unitaryGroup_iff').mp h, (Matrix.mem_unitaryGroup_iff).mp h⟩
  · rintro ⟨h, _⟩
    exact (Matrix.mem_unitaryGroup_iff').mpr h

/-! 7.58 QR factorization

If {lit}`A` is a square matrix with linearly independent columns, then
{lit}`A = QR` with {lit}`Q` unitary and {lit}`R` upper triangular with positive
diagonal. Following Axler, the construction is Gram–Schmidt applied to the columns
of {lit}`A`: with {lit}`e` the resulting orthonormal basis (mathlib's
{name}`InnerProductSpace.gramSchmidtOrthonormalBasis`), take {lit}`Q` to have
columns {lit}`eⱼ` and {lit}`Rⱼₖ = ⟨eⱼ, aₖ⟩`. Then {lit}`A = QR` (orthonormal
expansion of each column), {lit}`Q` is unitary (its columns are orthonormal),
{lit}`R` is upper triangular ({name}`InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular`),
and the diagonal {lit}`Rₖₖ = ‖gramSchmidt aₖ‖ > 0` is a positive real.
*Uniqueness* is {lit}`QR_unique` below, via the lemma that a unitary upper-triangular
matrix with positive diagonal is the identity ({lit}`unitary_upperTri_eq_one`). -/

/-- The diagonal Gram–Schmidt coefficient: {lit}`⟨ê i, f i⟩ = ‖gramSchmidt f i‖`,
a positive real. This is the entry that becomes the (positive) diagonal of {lit}`R`
in the QR factorization. -/
theorem gramSchmidtNormed_inner_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [WellFoundedLT ι] {f : ι → E} (hf : LinearIndependent 𝕜 f) (i : ι) :
    inner 𝕜 (InnerProductSpace.gramSchmidtNormed 𝕜 f i) (f i) =
      ((‖InnerProductSpace.gramSchmidt 𝕜 f i‖ : ℝ) : 𝕜) := by
  have hne : InnerProductSpace.gramSchmidt 𝕜 f i ≠ 0 :=
    InnerProductSpace.gramSchmidt_ne_zero i hf
  rw [InnerProductSpace.gramSchmidt_def' 𝕜 f i, inner_add_right, inner_sum]
  have hzero : ∀ j ∈ Finset.Iio i, inner 𝕜 (InnerProductSpace.gramSchmidtNormed 𝕜 f i)
      ((𝕜 ∙ InnerProductSpace.gramSchmidt 𝕜 f j).starProjection (f i)) = 0 := by
    intro j hj
    have hji : j ≠ i := ne_of_lt (Finset.mem_Iio.mp hj)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      ((𝕜 ∙ InnerProductSpace.gramSchmidt 𝕜 f j).starProjection_apply_mem (f i))
    rw [← ha, inner_smul_right, InnerProductSpace.gramSchmidtNormed, inner_smul_left,
      InnerProductSpace.gramSchmidt_orthogonal 𝕜 f (Ne.symm hji)]
    simp
  rw [Finset.sum_eq_zero hzero, add_zero, InnerProductSpace.gramSchmidtNormed,
    inner_smul_left, inner_self_eq_norm_sq_to_K, map_inv₀, RCLike.conj_ofReal]
  have hn : (‖InnerProductSpace.gramSchmidt 𝕜 f i‖ : 𝕜) ≠ 0 := by
    rw [Ne, RCLike.ofReal_eq_zero]; exact norm_ne_zero_iff.mpr hne
  field_simp

/-- 7.58 QR factorization (existence). A square matrix with linearly independent
columns factors as {lit}`A = QR` with {lit}`Q` unitary, {lit}`R` upper triangular,
and the diagonal of {lit}`R` a positive real. -/
theorem QR_factorization {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (hA : LinearIndependent 𝕜 (fun i => (EuclideanSpace.equiv (Fin N) 𝕜).symm (Aᵀ i))) :
    ∃ Q R : Matrix (Fin N) (Fin N) 𝕜, Q ∈ Matrix.unitaryGroup (Fin N) 𝕜 ∧
      (∀ i j, j < i → R i j = 0) ∧
      (∀ i, 0 < RCLike.re (R i i) ∧ RCLike.im (R i i) = 0) ∧ A = Q * R := by
  classical
  set f : Fin N → EuclideanSpace 𝕜 (Fin N) :=
    fun i => (EuclideanSpace.equiv (Fin N) 𝕜).symm (Aᵀ i) with hf
  have h : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin N)) = Fintype.card (Fin N) := by
    simp [finrank_euclideanSpace]
  set e := InnerProductSpace.gramSchmidtOrthonormalBasis h f with he
  refine ⟨Matrix.of fun k j => e j k, Matrix.of fun j i => inner 𝕜 (e j) (f i),
    ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply,
      RCLike.star_def]
    have hortho := orthonormal_iff_ite.mp e.orthonormal i j
    rw [PiLp.inner_apply] at hortho
    simp only [RCLike.inner_apply] at hortho
    rw [← hortho]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  · intro i j hji
    simp only [Matrix.of_apply]
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular h f hji
  · intro i
    have hne : InnerProductSpace.gramSchmidtNormed 𝕜 f i ≠ 0 := by
      have hlen : ‖InnerProductSpace.gramSchmidtNormed 𝕜 f i‖ = 1 :=
        InnerProductSpace.gramSchmidtNormed_unit_length i hA
      intro hz; rw [hz, norm_zero] at hlen; norm_num at hlen
    have hei : e i = InnerProductSpace.gramSchmidtNormed 𝕜 f i :=
      InnerProductSpace.gramSchmidtOrthonormalBasis_apply h hne
    simp only [Matrix.of_apply, hei, gramSchmidtNormed_inner_self hA i]
    have hpos : 0 < ‖InnerProductSpace.gramSchmidt 𝕜 f i‖ :=
      norm_pos_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero i hA)
    exact ⟨by rw [RCLike.ofReal_re]; exact hpos, by rw [RCLike.ofReal_im]⟩
  · ext k i
    simp only [Matrix.mul_apply, Matrix.of_apply]
    have hsum := e.sum_repr (f i)
    have hL := congrArg (EuclideanSpace.equiv (Fin N) 𝕜) hsum
    rw [map_sum] at hL
    simp only [map_smul, OrthonormalBasis.repr_apply_apply] at hL
    have hLk := congrFun hL k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hLk
    rw [ContinuousLinearEquiv.apply_symm_apply, Matrix.transpose_apply] at hLk
    rw [← hLk]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- A unitary upper-triangular matrix with positive real diagonal is the identity.
Since {lit}`U⁻¹ = U*` is upper triangular ({name}`Matrix.blockTriangular_inv_of_blockTriangular`)
while {lit}`U*` is lower triangular, {lit}`U` is diagonal; being unitary with
positive real diagonal then forces {lit}`U = I`. This is the key to QR uniqueness. -/
theorem unitary_upperTri_eq_one {N : ℕ} (U : Matrix (Fin N) (Fin N) 𝕜)
    (hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜) (hUT : U.BlockTriangular id)
    (hdiag : ∀ i, 0 < RCLike.re (U i i) ∧ RCLike.im (U i i) = 0) : U = 1 := by
  have hmem1 : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
  have hmem2 : U * star U = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
  letI : Invertible U := ⟨star U, hmem1, hmem2⟩
  have hUinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hmem1
  have hup : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hUT
  rw [hUinv] at hup
  have hoff : ∀ i j, i ≠ j → U i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hz := hup h
      rw [Matrix.star_apply, star_eq_zero] at hz
      exact hz
    · exact hUT h
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · have hentry : (star U * U) i i = 1 := by rw [hmem1]; simp
    rw [Matrix.mul_apply] at hentry
    have hsum : ∑ k, (star U) i k * U k i = (star U) i i * U i i := by
      refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rw [Matrix.star_apply, star_eq_zero.mpr (hoff k i hk), zero_mul]
    rw [hsum, Matrix.star_apply, RCLike.star_def, RCLike.conj_mul] at hentry
    have hnorm : ‖U i i‖ = 1 := by
      have h2 : ‖U i i‖ ^ 2 = 1 := by exact_mod_cast hentry
      rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]
    obtain ⟨hre, him⟩ := hdiag i
    have hval : U i i = ((RCLike.re (U i i) : ℝ) : 𝕜) := by
      conv_lhs => rw [← RCLike.re_add_im (U i i)]
      rw [him, RCLike.ofReal_zero, zero_mul, add_zero]
    have hre1 : RCLike.re (U i i) = 1 := by
      have h1 : |RCLike.re (U i i)| = 1 := by
        rw [← RCLike.norm_ofReal (K := 𝕜), ← hval, hnorm]
      rwa [abs_of_pos hre] at h1
    rw [Matrix.one_apply_eq, hval, hre1, RCLike.ofReal_one]
  · rw [hoff i j hij, Matrix.one_apply_ne hij]

/-- 7.58 QR factorization (uniqueness). The unitary/upper-triangular/positive-diagonal
factors of a QR factorization are unique. Following Axler: if {lit}`A = Q₁R₁ = Q₂R₂`,
then {lit}`U = Q₂* Q₁ = R₂ R₁⁻¹` is unitary, upper triangular, and has positive
diagonal, so {lit}`U = I` by {name}`unitary_upperTri_eq_one`; hence {lit}`Q₁ = Q₂` and
{lit}`R₁ = R₂`. -/
theorem QR_unique {N : ℕ} (A Q₁ R₁ Q₂ R₂ : Matrix (Fin N) (Fin N) 𝕜)
    (hQ₁ : Q₁ ∈ Matrix.unitaryGroup (Fin N) 𝕜) (hR₁t : R₁.BlockTriangular id)
    (hR₁d : ∀ i, 0 < RCLike.re (R₁ i i) ∧ RCLike.im (R₁ i i) = 0) (hA₁ : A = Q₁ * R₁)
    (hQ₂ : Q₂ ∈ Matrix.unitaryGroup (Fin N) 𝕜) (hR₂t : R₂.BlockTriangular id)
    (hR₂d : ∀ i, 0 < RCLike.re (R₂ i i) ∧ RCLike.im (R₂ i i) = 0) (hA₂ : A = Q₂ * R₂) :
    Q₁ = Q₂ ∧ R₁ = R₂ := by
  have diagval : ∀ z : 𝕜, RCLike.im z = 0 → z = ((RCLike.re z : ℝ) : 𝕜) := by
    intro z hz
    conv_lhs => rw [← RCLike.re_add_im z]
    rw [hz, RCLike.ofReal_zero, zero_mul, add_zero]
  have hR₁ne : ∀ i, R₁ i i ≠ 0 := by
    intro i h; have := (hR₁d i).1; rw [h] at this; simp at this
  have hdet1 : R₁.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hR₁t]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hR₁ne i)
  letI : Invertible R₁ := Matrix.invertibleOfIsUnitDet R₁ (isUnit_iff_ne_zero.mpr hdet1)
  set U := star Q₂ * Q₁ with hUdef
  have hQ₂s1 : star Q₂ * Q₂ = 1 := (Matrix.mem_unitaryGroup_iff').mp hQ₂
  have hQ₂s2 : Q₂ * star Q₂ = 1 := (Matrix.mem_unitaryGroup_iff).mp hQ₂
  have hUunit : U ∈ Matrix.unitaryGroup (Fin N) 𝕜 := mul_mem (Unitary.star_mem hQ₂) hQ₁
  have hUR : U * R₁ = R₂ := by
    have h : Q₁ * R₁ = Q₂ * R₂ := by rw [← hA₁, ← hA₂]
    rw [hUdef, Matrix.mul_assoc, h, ← Matrix.mul_assoc, hQ₂s1, Matrix.one_mul]
  have hUeq : U = R₂ * R₁⁻¹ := by
    rw [← hUR, Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]
  have hR₁invt : R₁⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hR₁t
  have hUt : U.BlockTriangular id := hUeq ▸ hR₂t.mul hR₁invt
  have hUd : ∀ i, 0 < RCLike.re (U i i) ∧ RCLike.im (U i i) = 0 := by
    intro i
    have hprod : (U * R₁) i i = U i i * R₁ i i := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · rw [hUt hlt, zero_mul]
      · rw [hR₁t hgt, mul_zero]
    rw [hUR] at hprod
    obtain ⟨hr1, hi1⟩ := hR₁d i
    obtain ⟨hr2, hi2⟩ := hR₂d i
    have hR1v := diagval _ hi1
    have hR2v := diagval _ hi2
    have ha : ((RCLike.re (R₁ i i) : ℝ) : 𝕜) ≠ 0 := by rw [← hR1v]; exact hR₁ne i
    have hUii : U i i = ((RCLike.re (R₂ i i) / RCLike.re (R₁ i i) : ℝ) : 𝕜) := by
      rw [RCLike.ofReal_div, eq_div_iff ha, ← hR1v, ← hR2v]
      exact hprod.symm
    refine ⟨?_, ?_⟩
    · rw [hUii, RCLike.ofReal_re]; positivity
    · rw [hUii, RCLike.ofReal_im]
  have hU1 : U = 1 := unitary_upperTri_eq_one U hUunit hUt hUd
  refine ⟨?_, ?_⟩
  · calc Q₁ = Q₂ * (star Q₂ * Q₁) := by rw [← Matrix.mul_assoc, hQ₂s2, Matrix.one_mul]
      _ = Q₂ * 1 := by rw [← hUdef, hU1]
      _ = Q₂ := Matrix.mul_one Q₂
  · rw [← hUR, hU1, Matrix.one_mul]

/-! 7.60 Example: QR factorization of a 3-by-3 matrix.

A concrete numeric illustration of 7.58 (with entries involving {lit}`√10`). It is
**deferred** together with the QR factorization it illustrates. -/

/-! # Cholesky Factorization -/

end Matrices

/-! 7.61 Positive invertible operator

A self-adjoint {lit}`T ∈ ℒ(V)` is a positive invertible operator iff
{lit}`⟨T v, v⟩ > 0` for every nonzero {lit}`v`. Using a positive square root
{lit}`R` of {lit}`T` (7.39, from
{module -checked}`LinearAlgebraDoneRightLean.Section_7C`), we have
{lit}`⟨T v, v⟩ = ‖R v‖²`, so positivity of {lit}`⟨T v, v⟩` for nonzero {lit}`v` is
exactly injectivity of {lit}`R`, equivalently of {lit}`T`. On a finite-dimensional
space injectivity is invertibility. -/

theorem positive_invertible_iff {T : V →ₗ[𝕜] V} (hT : T.IsPositive) :
    Function.Injective T ↔ ∀ v : V, v ≠ 0 → 0 < RCLike.re ⟪T v, v⟫_𝕜 := by
  obtain ⟨R, hR, hRT⟩ := LADR.Section_7C.exists_positive_sqrt hT
  have hval : ∀ v, RCLike.re ⟪T v, v⟫_𝕜 = ‖R v‖ ^ 2 := by
    intro v
    rw [← hRT]
    simp only [LinearMap.comp_apply]
    rw [hR.isSymmetric (R v) v, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hRinj : Function.Injective T → Function.Injective R := by
    intro hinj a b hab
    apply hinj
    rw [← hRT]
    simp only [LinearMap.comp_apply, hab]
  constructor
  · intro hinj v hv
    rw [hval]
    have hRv : R v ≠ 0 := fun h => hv (hRinj hinj (h.trans (map_zero R).symm))
    exact pow_pos (norm_pos_iff.mpr hRv) 2
  · intro hpos a b hab
    by_contra hne
    have hd : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hgt := hpos (a - b) hd
    have hTz : ⟪T (a - b), a - b⟫_𝕜 = 0 := by
      rw [map_sub, hab, sub_self, inner_zero_left]
    rw [hTz, map_zero] at hgt
    exact lt_irrefl 0 hgt

/-! 7.62 Definition: positive definite matrix

A matrix {lit}`B ∈ 𝔽ⁿ'ⁿ` is *positive definite* if {lit}`B* = B` and
{lit}`⟨B x, x⟩ > 0` for every nonzero {lit}`x ∈ 𝔽ⁿ` (Euclidean inner product). -/

def IsPositiveDefinite {n : Type*} [Fintype n] (B : Matrix n n 𝕜) : Prop :=
  Bᴴ = B ∧ ∀ x : n → 𝕜, x ≠ 0 → 0 < RCLike.re (∑ i, conj (B.mulVec x i) * x i)

/-- 7.63 Cholesky factorization (existence). Every positive definite matrix {lit}`B`
factors as {lit}`B = Rᴴ * R` with {lit}`R` upper triangular and positive real diagonal.
Following Axler: the positive square root of {lit}`B` supplies an invertible {lit}`A` with
{lit}`Aᴴ * A = B`; a QR factorization {lit}`A = Q * R` then gives
`B = Rᴴ * Qᴴ * Q * R = Rᴴ * R`. -/
theorem cholesky_factorization {N : ℕ} (B : Matrix (Fin N) (Fin N) 𝕜)
    (hB : IsPositiveDefinite B) :
    ∃ R : Matrix (Fin N) (Fin N) 𝕜, (∀ i j, j < i → R i j = 0) ∧
      (∀ i, 0 < RCLike.re (R i i) ∧ RCLike.im (R i i) = 0) ∧ B = Rᴴ * R := by
  classical
  obtain ⟨hBherm, hBpos⟩ := hB
  -- `toEuclideanLin` turns matrix product into composition of operators.
  have hmul : ∀ M P : Matrix (Fin N) (Fin N) 𝕜,
      (M * P).toEuclideanLin = M.toEuclideanLin ∘ₗ P.toEuclideanLin := by
    intro M P; ext v
    simp only [LinearMap.comp_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec]
  -- `re ⟪Bop v, v⟫` equals the positive-definite quadratic form at `ofLp v`.
  have hre : ∀ v : EuclideanSpace 𝕜 (Fin N),
      RCLike.re (⟪B.toEuclideanLin v, v⟫_𝕜)
        = RCLike.re (∑ i, conj (B.mulVec (WithLp.ofLp v) i) * WithLp.ofLp v i) := by
    intro v
    rw [Matrix.toLpLin_apply, PiLp.inner_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, mul_comm]
  -- `Bop = toEuclideanLin B` is a positive operator.
  have hBoppos : B.toEuclideanLin.IsPositive := by
    rw [LADR.Section_7C.isPositive_iff_symmetric_nonneg]
    refine ⟨?_, fun v => ?_⟩
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff',
        ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hBherm]
    · rw [hre]
      by_cases hv : WithLp.ofLp v = 0
      · simp [hv]
      · exact le_of_lt (hBpos _ hv)
  -- positive square root `Rop` with `Rop ∘ Rop = Bop`.
  obtain ⟨Rop, hRoppos, hRopRop⟩ := LADR.Section_7C.exists_positive_sqrt hBoppos
  -- `Bop` is injective (strict positivity kills the kernel), hence so is `Rop`.
  have hBopinj : Function.Injective B.toEuclideanLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hvne
    have hx : WithLp.ofLp v ≠ 0 := fun h => hvne (by
      have h2 := congrArg (WithLp.toLp 2) h; simpa using h2)
    have hpos := hBpos _ hx
    rw [← hre, hv] at hpos
    simp at hpos
  have hRopinj : Function.Injective Rop := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hBopinj
    rw [map_zero, ← hRopRop, LinearMap.comp_apply, hv, map_zero]
  -- matrix `A` of `Rop`; its columns are linearly independent.
  set A := Matrix.toEuclideanLin.symm Rop with hAdef
  have hARop : A.toEuclideanLin = Rop := LinearEquiv.apply_symm_apply _ _
  have hAcol : ∀ i, (EuclideanSpace.equiv (Fin N) 𝕜).symm (Aᵀ i)
      = Rop (EuclideanSpace.single i 1) := by
    intro i
    rw [← hARop, Matrix.toLpLin_apply]
    ext k
    simp [EuclideanSpace.single, Matrix.mulVec_single, Matrix.transpose_apply]
  have hA : LinearIndependent 𝕜 (fun i => (EuclideanSpace.equiv (Fin N) 𝕜).symm (Aᵀ i)) := by
    have hbasis : LinearIndependent 𝕜
        (fun i : Fin N => (EuclideanSpace.single i 1 : EuclideanSpace 𝕜 (Fin N))) := by
      have h := (EuclideanSpace.basisFun (Fin N) 𝕜).orthonormal.linearIndependent
      have he : (fun i : Fin N => (EuclideanSpace.single i 1 : EuclideanSpace 𝕜 (Fin N)))
          = ⇑(EuclideanSpace.basisFun (Fin N) 𝕜) := by
        ext i : 1
        simp [EuclideanSpace.basisFun_apply]
      rw [he]; exact h
    have hmap := hbasis.map' (Rop : EuclideanSpace 𝕜 (Fin N) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin N))
      (LinearMap.ker_eq_bot.mpr hRopinj)
    have heq : (fun i => (EuclideanSpace.equiv (Fin N) 𝕜).symm (Aᵀ i))
        = ⇑Rop ∘ fun i => (EuclideanSpace.single i 1 : EuclideanSpace 𝕜 (Fin N)) := funext hAcol
    rw [heq]; exact hmap
  -- QR factorization of `A` and the Cholesky identity.
  obtain ⟨Q, R, hQ, hRt, hRd, hAQR⟩ := QR_factorization A hA
  refine ⟨R, hRt, hRd, ?_⟩
  have hAA : Aᴴ * A = B := by
    apply Matrix.toEuclideanLin.injective
    rw [hmul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hARop,
      (LADR.Section_7C.isPositive_iff_symmetric_nonneg Rop).mp hRoppos |>.1.adjoint_eq, hRopRop]
  have hQuni : Qᴴ * Q = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact (Matrix.mem_unitaryGroup_iff').mp hQ
  rw [← hAA, hAQR, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ Q R,
    hQuni, Matrix.one_mul]

/-- 7.63 Cholesky factorization (uniqueness). The upper-triangular positive-diagonal
factor is unique: if `B = R₁ᴴ * R₁ = R₂ᴴ * R₂` with both {lit}`Rₖ` upper triangular with
positive diagonal, then {lit}`R₁ = R₂`. Following Axler's QR uniqueness argument,
{lit}`U = R₂ * R₁⁻¹` is unitary (from {lit}`R₁ᴴ R₁ = R₂ᴴ R₂`), upper triangular, and has
positive diagonal, so {lit}`U = I` by {name}`unitary_upperTri_eq_one`. -/
theorem cholesky_unique {N : ℕ} (B R₁ R₂ : Matrix (Fin N) (Fin N) 𝕜)
    (hR₁t : ∀ i j, j < i → R₁ i j = 0)
    (hR₁d : ∀ i, 0 < RCLike.re (R₁ i i) ∧ RCLike.im (R₁ i i) = 0) (hB₁ : B = R₁ᴴ * R₁)
    (hR₂t : ∀ i j, j < i → R₂ i j = 0)
    (hR₂d : ∀ i, 0 < RCLike.re (R₂ i i) ∧ RCLike.im (R₂ i i) = 0) (hB₂ : B = R₂ᴴ * R₂) :
    R₁ = R₂ := by
  have diagval : ∀ z : 𝕜, RCLike.im z = 0 → z = ((RCLike.re z : ℝ) : 𝕜) := by
    intro z hz
    conv_lhs => rw [← RCLike.re_add_im z]
    rw [hz, RCLike.ofReal_zero, zero_mul, add_zero]
  have hR₁bt : R₁.BlockTriangular id := fun i j h => hR₁t i j h
  have hR₁ne : ∀ i, R₁ i i ≠ 0 := fun i h => by have := (hR₁d i).1; rw [h] at this; simp at this
  have hdet1 : R₁.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hR₁bt]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hR₁ne i)
  letI : Invertible R₁ := Matrix.invertibleOfIsUnitDet R₁ (isUnit_iff_ne_zero.mpr hdet1)
  set U := R₂ * R₁⁻¹ with hUdef
  have hUR : U * R₁ = R₂ := by
    rw [hUdef, Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_one]
  have hUunit : U ∈ Matrix.unitaryGroup (Fin N) 𝕜 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have hBeq : R₂ᴴ * R₂ = R₁ᴴ * R₁ := by rw [← hB₂, ← hB₁]
    rw [hUdef, Matrix.conjTranspose_mul]
    rw [show (R₁⁻¹)ᴴ * R₂ᴴ * (R₂ * R₁⁻¹) = (R₁⁻¹)ᴴ * (R₂ᴴ * R₂) * R₁⁻¹ by
      simp only [Matrix.mul_assoc], hBeq]
    rw [show (R₁⁻¹)ᴴ * (R₁ᴴ * R₁) * R₁⁻¹ = (R₁⁻¹)ᴴ * R₁ᴴ * (R₁ * R₁⁻¹) by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.mul_inv_of_invertible, Matrix.mul_one, ← Matrix.conjTranspose_mul,
      Matrix.mul_inv_of_invertible, Matrix.conjTranspose_one]
  have hR₁invt : R₁⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hR₁bt
  have hUt : U.BlockTriangular id := by
    have hR₂bt : R₂.BlockTriangular id := fun i j h => hR₂t i j h
    exact hUdef ▸ hR₂bt.mul hR₁invt
  have hUd : ∀ i, 0 < RCLike.re (U i i) ∧ RCLike.im (U i i) = 0 := by
    intro i
    have hprod : (U * R₁) i i = U i i * R₁ i i := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rcases lt_or_gt_of_ne hk with hlt | hgt
      · rw [hUt hlt, zero_mul]
      · rw [hR₁t _ _ hgt, mul_zero]
    rw [hUR] at hprod
    obtain ⟨hr1, hi1⟩ := hR₁d i
    obtain ⟨hr2, hi2⟩ := hR₂d i
    have hR1v := diagval _ hi1
    have hR2v := diagval _ hi2
    have ha : ((RCLike.re (R₁ i i) : ℝ) : 𝕜) ≠ 0 := by rw [← hR1v]; exact hR₁ne i
    have hUii : U i i = ((RCLike.re (R₂ i i) / RCLike.re (R₁ i i) : ℝ) : 𝕜) := by
      rw [RCLike.ofReal_div, eq_div_iff ha, ← hR1v, ← hR2v]
      exact hprod.symm
    refine ⟨?_, ?_⟩
    · rw [hUii, RCLike.ofReal_re]; positivity
    · rw [hUii, RCLike.ofReal_im]
  have hU1 : U = 1 := unitary_upperTri_eq_one U hUunit hUt hUd
  rw [← hUR, hU1, Matrix.one_mul]

/-! # Exercises 7D -/

/-- 7D.1 Suppose {lit}`dim V ≥ 2`. Then {lit}`S` is an isometry iff it maps every
orthonormal list of length two to an orthonormal list. -/
theorem exercise_7D_1 (S : V →ₗ[𝕜] W) :
    IsIsometry S ↔ ∀ e : Fin 2 → V, Orthonormal 𝕜 e → Orthonormal 𝕜 (fun i => S (e i)) := by
  sorry

/-- 7D.2 A nonzero {lit}`T` is a scalar multiple of an isometry iff {lit}`T`
preserves orthogonality. -/
theorem exercise_7D_2 (T : V →ₗ[𝕜] W) (hT : T ≠ 0) :
    (∃ (c : 𝕜) (S : V →ₗ[𝕜] W), IsIsometry S ∧ T = c • S) ↔
      ∀ u v, ⟪u, v⟫_𝕜 = 0 → ⟪T u, T v⟫_𝕜 = 0 := by
  sorry

/-- 7D.3(a) The product of two unitary operators is unitary. -/
theorem exercise_7D_3a {S T : V →ₗ[𝕜] V} (hS : IsUnitary S) (hT : IsUnitary T) :
    IsUnitary (S ∘ₗ T) := by
  sorry

/-- 7D.3(b) The adjoint (inverse) of a unitary operator is unitary. -/
theorem exercise_7D_3b {S : V →ₗ[𝕜] V} (hS : IsUnitary S) :
    IsUnitary (LinearMap.adjoint S) := by
  sorry

/-- 7D.4 Over {lit}`ℂ`, for self-adjoint {lit}`A, B`, the operator {lit}`A + iB` is
unitary iff {lit}`AB = BA` and {lit}`A² + B² = I`. -/
theorem exercise_7D_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : E →ₗ[ℂ] E}
    (hA : LinearMap.IsSymmetric A) (hB : LinearMap.IsSymmetric B) :
    IsUnitary (A + Complex.I • B) ↔
      (A ∘ₗ B = B ∘ₗ A ∧ A ∘ₗ A + B ∘ₗ B = 1) := by
  sorry

/-- 7D.5 The following are equivalent: (a) {lit}`S` is a self-adjoint unitary;
(b) {lit}`S = 2P − I` for an orthogonal projection {lit}`P`; (c) {lit}`S = 1` on
some {lit}`U` and {lit}`S = −1` on {lit}`U⟂`. -/
theorem exercise_7D_5 (S : V →ₗ[𝕜] V) :
    [LinearMap.IsSymmetric S ∧ IsUnitary S,
      ∃ P : V →ₗ[𝕜] V, LinearMap.adjoint P = P ∧ P ∘ₗ P = P ∧ S = 2 • P - 1,
      ∃ U : Submodule 𝕜 V, (∀ u ∈ U, S u = u) ∧ ∀ w ∈ Uᗮ, S w = -w].TFAE := by
  sorry

/-- 7D.6 Two normal operators on {lit}`𝔽³` with eigenvalues {lit}`2, 5, 7` are
unitarily equivalent. -/
theorem exercise_7D_6
    (T₁ T₂ : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3))
    (hN1 : IsStarNormal T₁) (hN2 : IsStarNormal T₂)
    (he1 : ∀ μ : 𝕜, HasEigenvalue T₁ μ ↔ μ = 2 ∨ μ = 5 ∨ μ = 7)
    (he2 : ∀ μ : 𝕜, HasEigenvalue T₂ μ ↔ μ = 2 ∨ μ = 5 ∨ μ = 7) :
    ∃ S : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3),
      IsUnitary S ∧ T₁ = LinearMap.adjoint S ∘ₗ T₂ ∘ₗ S := by
  sorry

/-- 7D.7 There are self-adjoint operators on {lit}`𝔽⁴` both with eigenvalues
{lit}`2, 5, 7` that are not unitarily equivalent. -/
theorem exercise_7D_7 :
    ∃ T₁ T₂ : EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4),
      LinearMap.IsSymmetric T₁ ∧ LinearMap.IsSymmetric T₂ ∧
      (∀ μ : 𝕜, HasEigenvalue T₁ μ ↔ μ = 2 ∨ μ = 5 ∨ μ = 7) ∧
      (∀ μ : 𝕜, HasEigenvalue T₂ μ ↔ μ = 2 ∨ μ = 5 ∨ μ = 7) ∧
      ¬ ∃ S : EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4),
        IsUnitary S ∧ T₁ = LinearMap.adjoint S ∘ₗ T₂ ∘ₗ S := by
  sorry

/-- 7D.8 Counterexample: {lit}`‖S eₖ‖ = 1` on an orthonormal basis does not imply
{lit}`S` is unitary. -/
theorem exercise_7D_8 :
    ¬ ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
      (S : E →ₗ[𝕜] E) (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 E),
      (∀ k, ‖S (e k)‖ = 1) → IsUnitary S := by
  sorry

/-- 7D.9 Over {lit}`ℂ`, if every eigenvalue of {lit}`T` has absolute value 1 and
{lit}`‖T v‖ ≤ ‖v‖` for all {lit}`v`, then {lit}`T` is unitary. -/
theorem exercise_7D_9 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (h1 : ∀ μ : ℂ, HasEigenvalue T μ → ‖μ‖ = 1) (h2 : ∀ v, ‖T v‖ ≤ ‖v‖) :
    IsUnitary T := by
  sorry

/-- 7D.10 Over {lit}`ℂ`, for self-adjoint {lit}`T` with {lit}`‖Tv‖ ≤ ‖v‖`:
(a) {lit}`I − T²` is positive; (b) {lit}`T + i√(I − T²)` is unitary. -/
theorem exercise_7D_10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : LinearMap.IsSymmetric T)
    (hnorm : ∀ v, ‖T v‖ ≤ ‖v‖) :
    (1 - T ∘ₗ T).IsPositive ∧
      ∀ R : E →ₗ[ℂ] E, R.IsPositive → R ∘ₗ R = 1 - T ∘ₗ T →
        IsUnitary (T + Complex.I • R) := by
  sorry

/-- 7D.11 {lit}`S` is unitary iff it maps the closed unit ball onto itself. -/
theorem exercise_7D_11 (S : V →ₗ[𝕜] V) :
    IsUnitary S ↔ (S '' {v | ‖v‖ ≤ 1}) = {v | ‖v‖ ≤ 1} := by
  sorry

/-- 7D.12 Counterexample: {lit}`S` invertible with {lit}`‖S⁻¹v‖ = ‖Sv‖` for all
{lit}`v` need not be unitary. -/
theorem exercise_7D_12 :
    ¬ ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
      (S : E ≃ₗ[𝕜] E), (∀ v, ‖S.symm v‖ = ‖S v‖) → IsUnitary (S : E →ₗ[𝕜] E) := by
  sorry

/-- 7D.13 For a square complex matrix, the columns form an orthonormal list iff the
rows do (equivalently {lit}`Q* Q = I ⟺ Q Q* = I`). -/
theorem exercise_7D_13 {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix n n 𝕜) :
    Qᴴ * Q = 1 ↔ Q * Qᴴ = 1 := by
  sorry

/-- 7D.14 For a unit vector {lit}`v` and {lit}`b ∈ 𝔽` (with {lit}`dim V ≥ 2`), there
is a unitary {lit}`S` with {lit}`⟨Sv, v⟩ = b` iff {lit}`|b| ≤ 1`. -/
theorem exercise_7D_14 (h : 2 ≤ finrank 𝕜 V) (v : V) (hv : ‖v‖ = 1) (b : 𝕜) :
    (∃ S : V →ₗ[𝕜] V, IsUnitary S ∧ ⟪S v, v⟫_𝕜 = b) ↔ ‖b‖ ≤ 1 := by
  sorry

/-- 7D.15 For unitary {lit}`T` with {lit}`T − I` invertible (inverse {lit}`Tinv`):
(a) {lit}`(T + I)(T − I)⁻¹` is skew. -/
theorem exercise_7D_15a (T : V →ₗ[𝕜] V) (hT : IsUnitary T) (Tinv : V →ₗ[𝕜] V)
    (hi1 : Tinv ∘ₗ (T - 1) = 1) (hi2 : (T - 1) ∘ₗ Tinv = 1) :
    LinearMap.adjoint ((T + 1) ∘ₗ Tinv) = -((T + 1) ∘ₗ Tinv) := by
  sorry

/-- 7D.15 (b) Over {lit}`ℂ`, {lit}`i(T + I)(T − I)⁻¹` is self-adjoint. -/
theorem exercise_7D_15b {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : IsUnitary T) (Tinv : E →ₗ[ℂ] E)
    (hi1 : Tinv ∘ₗ (T - 1) = 1) (hi2 : (T - 1) ∘ₗ Tinv = 1) :
    LinearMap.IsSymmetric (Complex.I • ((T + 1) ∘ₗ Tinv)) := by
  sorry

/-- 7D.16 Over {lit}`ℂ`, for self-adjoint {lit}`T`, {lit}`(T + iI)(T − iI)⁻¹` is
unitary and {lit}`1` is not an eigenvalue of it. -/
theorem exercise_7D_16 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : LinearMap.IsSymmetric T)
    (Tinv : E →ₗ[ℂ] E) (hi1 : Tinv ∘ₗ (T - Complex.I • 1) = 1)
    (hi2 : (T - Complex.I • 1) ∘ₗ Tinv = 1) :
    IsUnitary ((T + Complex.I • 1) ∘ₗ Tinv) ∧
      ¬ HasEigenvalue ((T + Complex.I • 1) ∘ₗ Tinv) 1 := by
  sorry

/-- 7D.17 (7.57) A matrix is unitary iff its conjugate transpose is unitary
(columns orthonormal iff rows orthonormal). -/
theorem exercise_7D_17 {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix n n 𝕜) :
    IsUnitaryMatrix Q ↔ IsUnitaryMatrix Qᴴ := by
  sorry

/-- 7D.18 A real symmetric matrix is orthogonally diagonalizable: there is a real
unitary {lit}`Q` with {lit}`Q* A Q` diagonal. -/
theorem exercise_7D_18 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.transpose = A) :
    ∃ Q : Matrix n n ℝ, Q ∈ Matrix.unitaryGroup n ℝ ∧ Matrix.IsDiag (Qᴴ * A * Q) := by
  sorry

/-- 7D.19 The discrete Fourier transform {lit}`ℱ` on {lit}`ℂⁿ` is unitary and
satisfies {lit}`ℱ⁴ = I`. -/
theorem exercise_7D_19 {n : ℕ} (hn : 0 < n)
    (F : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (hF : ∀ (z : EuclideanSpace ℂ (Fin n)) (j : Fin n),
      F z j = (1 / Real.sqrt n : ℂ) *
        ∑ m : Fin n, z m *
          Complex.exp (-2 * Real.pi * Complex.I * (j : ℂ) * (m : ℂ) / (n : ℂ))) :
    IsUnitary F ∧ F ∘ₗ F ∘ₗ F ∘ₗ F = 1 := by
  sorry

/-! 7D.20 (deferred): a matrix with linearly independent columns factors uniquely
as {lit}`A = RQ` with {lit}`R` lower triangular (positive diagonal) and {lit}`Q`
unitary. This is the {lit}`RQ` variant of the QR factorization (7.58), which is
itself deferred — the pinned mathlib has no packaged QR/RQ factorization. -/

end LADR.Section_7D
