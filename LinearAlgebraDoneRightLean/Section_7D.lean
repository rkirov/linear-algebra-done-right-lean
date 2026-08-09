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
{lit}`v` — i.e. it preserves norms. This is mathlib's {name}`Isometry` predicate
applied to the underlying function: for a linear map the distance-preserving and
norm-preserving conditions agree ({name}`AddMonoidHomClass.isometry_iff_norm`), so
we use {lit}`Isometry S` throughout and get {name}`Isometry.injective` and the rest
of the mathlib API for free. (Norm-preserving linear maps *bundled as a type* are
{name}`LinearIsometry`; a predicate on a given {lit}`S ∈ ℒ(V, W)` is what the
characterizations below need.) -/

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- Axler's form of the definition. -/
theorem isometry_iff_norm (S : V →ₗ[𝕜] W) : Isometry S ↔ ∀ v, ‖S v‖ = ‖v‖ :=
  AddMonoidHomClass.isometry_iff_norm S

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
theorem isometry_norm_map {S : V →ₗ[𝕜] W} (h : Isometry S) (v : V) : ‖S v‖ = ‖v‖ :=
  (isometry_iff_norm S).mp h v

/-! 7.45 Example: if {lit}`S` maps an orthonormal basis {lit}`e₁, …, eₙ` of
{lit}`V` to an orthonormal list {lit}`g₁, …, gₙ` in {lit}`W`, then {lit}`S` is an
isometry.

We prove the sharper fact that such an {lit}`S` *preserves inner products*: writing
{lit}`u, v` in the basis {lit}`e` and using the orthonormality of the {lit}`gₖ`
collapses the double sum to {name}`OrthonormalBasis.sum_inner_mul_inner`. -/

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
    (h : Orthonormal 𝕜 (fun i => S (b i))) : Isometry S :=
  (isometry_iff_norm S).mpr <| (LinearMap.norm_map_iff_inner_map_map S).mpr fun u v =>
    isometry_of_orthonormal_image b S h u v

/-! 7.49 Characterizations of isometries

For {lit}`S ∈ ℒ(V, W)` with orthonormal bases {lit}`e` of {lit}`V` and {lit}`f`
of {lit}`W`, the following are equivalent:
(a) {lit}`S` is an isometry;
(b) {lit}`S* S = I`;
(c) {lit}`⟨S u, S v⟩ = ⟨u, v⟩` for all {lit}`u, v`;
(d) {lit}`S e₁, …, S eₙ` is an orthonormal list;
(e) the columns of {lit}`ℳ(S, e, f)` form an orthonormal list in {lit}`𝔽ᵐ`.

(a) ⟺ (c) is {name}`LinearMap.norm_map_iff_inner_map_map`. We prove (c) ⟺ (b),
(a) ⟺ (d), and (d) ⟺ (e) below, then collect all five into a single
{lit}`TFAE` list. Condition (e) is the matrix restatement of (d): column
{lit}`k` of {lit}`ℳ(S, e, f)` is the coordinate vector of {lit}`S eₖ` in the
basis {lit}`f`. -/

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- (a) ⟺ (c): an isometry is exactly an inner-product-preserving map. -/
theorem isometry_iff_inner (S : V →ₗ[𝕜] W) :
    Isometry S ↔ ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜 :=
  (isometry_iff_norm S).trans (LinearMap.norm_map_iff_inner_map_map S)

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
    Isometry S ↔ LinearMap.adjoint S ∘ₗ S = 1 :=
  (isometry_iff_inner S).trans (inner_iff_adjoint_comp S)

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- (a) ⟺ (d): {lit}`S` is an isometry iff it carries some (hence any) orthonormal
basis to an orthonormal list. -/
theorem isometry_iff_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] W) :
    Isometry S ↔ Orthonormal 𝕜 (fun i => S (b i)) := by
  constructor
  · intro h
    rw [orthonormal_iff_ite]
    intro i j
    rw [(isometry_iff_inner S).mp h (b i) (b j)]
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  · exact isometry_of_orthonormal_image_isometry b S

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- (d) ⟺ (e): column {lit}`j` of {lit}`ℳ(S, e, f)` is the coordinate vector
{lit}`f.repr (S eⱼ)`, and {lit}`f.repr` is a linear isometry onto {lit}`𝔽ᵐ`, so the
columns are orthonormal exactly when the {lit}`S eⱼ` are. -/
theorem orthonormal_image_iff_orthonormal_columns {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (e : OrthonormalBasis ι 𝕜 V) (f : OrthonormalBasis κ 𝕜 W) (S : V →ₗ[𝕜] W) :
    Orthonormal 𝕜 (fun i => S (e i)) ↔
      Orthonormal 𝕜 (fun j => (WithLp.toLp 2 fun i =>
        LinearMap.toMatrix e.toBasis f.toBasis S i j : EuclideanSpace 𝕜 κ)) := by
  have hcol : (fun j => (WithLp.toLp 2 fun i =>
      LinearMap.toMatrix e.toBasis f.toBasis S i j : EuclideanSpace 𝕜 κ))
      = f.repr ∘ fun j => S (e j) := by
    funext j
    ext i
    simp [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  rw [hcol, ← LinearIsometryEquiv.coe_toLinearIsometry,
    f.repr.toLinearIsometry.orthonormal_comp_iff]

/-- 7.49 in full: all five conditions of the book, as one {name}`List.TFAE`. -/
theorem tfae_isometry {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : OrthonormalBasis ι 𝕜 V) (f : OrthonormalBasis κ 𝕜 W) (S : V →ₗ[𝕜] W) :
    [Isometry S,
      LinearMap.adjoint S ∘ₗ S = 1,
      ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜,
      (Orthonormal 𝕜 fun i => S (e i)),
      (Orthonormal 𝕜 fun j => (WithLp.toLp 2 fun i =>
        LinearMap.toMatrix e.toBasis f.toBasis S i j : EuclideanSpace 𝕜 κ))].TFAE := by
  tfae_have 1 ↔ 2 := isometry_iff_adjoint_comp S
  tfae_have 1 ↔ 3 := isometry_iff_inner S
  tfae_have 1 ↔ 4 := isometry_iff_orthonormal_image e S
  tfae_have 4 ↔ 5 := orthonormal_image_iff_orthonormal_columns e f S
  tfae_finish

/-! # Unitary Operators -/

/-! 7.51 Definition: unitary operator

An operator {lit}`S ∈ ℒ(V)` is *unitary* if it is an invertible isometry. Since
{lit}`V` is finite-dimensional, every isometry is already invertible (injective +
finite dimension ⟹ bijective), so the word "invertible" is redundant here.

In finite dimensions {lit}`ℒ(V)` is a star ring with the adjoint as star
({name}`LinearMap.star_eq_adjoint`), so mathlib already has the unitary operators:
the submonoid {name}`unitary`, whose membership condition {lit}`star S * S = 1 ∧
S * star S = 1` is exactly 7.53(b). We write {lit}`S ∈ unitary (V →ₗ[𝕜] V)` for
"{lit}`S` is unitary" and record Axler's definition as the equivalence
{lit}`mem_unitary_iff_bijective_isometry`. -/

/-- On a finite-dimensional space an isometry is automatically bijective. -/
theorem isometry_bijective {S : V →ₗ[𝕜] V} (h : Isometry S) : Function.Bijective S :=
  ⟨h.injective, LinearMap.injective_iff_surjective.mp h.injective⟩

/-- (b) as it is spelled in mathlib: {lit}`star` on {lit}`ℒ(V)` is the adjoint. -/
theorem mem_unitary_iff_adjoint (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔
      LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1 :=
  Unitary.mem_iff

/-- Hence on {lit}`ℒ(V)` "unitary" and "isometry" coincide. -/
theorem mem_unitary_iff_isometry (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔ Isometry S := by
  rw [mem_unitary_iff_adjoint]
  constructor
  · exact fun h => (isometry_iff_adjoint_comp S).mpr h.1
  · intro hiso
    have hSS : LinearMap.adjoint S ∘ₗ S = 1 := (isometry_iff_adjoint_comp S).mp hiso
    refine ⟨hSS, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := (isometry_bijective hiso).surjective w
    have hx : LinearMap.adjoint S (S x) = x := by
      have := LinearMap.congr_fun hSS x
      rwa [LinearMap.comp_apply, Module.End.one_apply] at this
    rw [LinearMap.comp_apply, hx, Module.End.one_apply]

/-- Axler's definition — an *invertible* isometry — on the record. -/
theorem mem_unitary_iff_bijective_isometry (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔ Function.Bijective S ∧ Isometry S :=
  (mem_unitary_iff_isometry S).trans ⟨fun h => ⟨isometry_bijective h, h⟩, fun h => h.2⟩

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

Conditions (a) and (b) are the same statement in mathlib: membership in
{name}`unitary` *is* {lit}`S* S = S S* = I` ({lit}`mem_unitary_iff_adjoint`, above).
We prove (a) ⟺ (d) and (a) ⟺ (f), and the two matrix conditions, then collect all
six into a single {lit}`TFAE` list. Statement (c) is the reading of (b) as
"{lit}`S*` is the two-sided inverse", spelled with {name}`Ring.inverse` on the ring
{lit}`ℒ(V)`. In (d) the orthonormal list {lit}`S e₁, …, S eₙ` is indexed by the
basis index type, so being orthonormal already makes it a basis. Condition (e) is
the rows-versus-columns exchange (Exercise 13): the columns of {lit}`ℳ(S, e)` are
orthonormal iff {lit}`ℳᴴ ℳ = I`, the rows iff {lit}`ℳ ℳᴴ = I`, and for a square
matrix those two agree ({name}`Matrix.unitaryGroup`). -/

/-- (c): for a unitary operator, {lit}`S*` is a two-sided inverse of {lit}`S`. -/
theorem mem_unitary_inverse {S : V →ₗ[𝕜] V} (h : S ∈ unitary (V →ₗ[𝕜] V)) :
    LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1 :=
  (mem_unitary_iff_adjoint S).mp h

/-- (a) ⟺ (d). -/
theorem mem_unitary_iff_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔ Orthonormal 𝕜 (fun i => S (b i)) :=
  (mem_unitary_iff_isometry S).trans (isometry_iff_orthonormal_image b S)

/-- (a) ⟺ (f): {lit}`S` is unitary iff {lit}`S*` is unitary. This is
{name}`Unitary.star_mem_iff` for the star ring {lit}`ℒ(V)`. -/
theorem mem_unitary_adjoint_iff (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔ LinearMap.adjoint S ∈ unitary (V →ₗ[𝕜] V) :=
  Unitary.star_mem_iff.symm

/-- (b) ⟺ (c): the two-sided-inverse reading of {lit}`S* S = S S* = I`. -/
theorem adjoint_comp_iff_isUnit (S : V →ₗ[𝕜] V) :
    (LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1) ↔
      (IsUnit S ∧ Ring.inverse S = LinearMap.adjoint S) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨S, LinearMap.adjoint S, h2, h1⟩, rfl⟩,
      Ring.inverse_unit ⟨S, LinearMap.adjoint S, h2, h1⟩⟩
  · rintro ⟨hu, hinv⟩
    exact ⟨by rw [← hinv]; exact Ring.inverse_mul_cancel S hu,
      by rw [← hinv]; exact Ring.mul_inverse_cancel S hu⟩

/-- A list of vectors in {lit}`𝔽ᵐ` given by the columns of {lit}`M` is orthonormal
iff {lit}`Mᴴ M = I`. -/
theorem orthonormal_columns_iff {n m : Type*} [Fintype m] [DecidableEq n]
    (M : Matrix m n 𝕜) :
    Orthonormal 𝕜 (fun j => (WithLp.toLp 2 fun i => M i j : EuclideanSpace 𝕜 m)) ↔
      Mᴴ * M = 1 := by
  have hinner : ∀ j k, ⟪(WithLp.toLp 2 fun i => M i j : EuclideanSpace 𝕜 m),
      (WithLp.toLp 2 fun i => M i k : EuclideanSpace 𝕜 m)⟫_𝕜 = (Mᴴ * M) j k := by
    intro j k
    simp [PiLp.inner_apply, Matrix.mul_apply, RCLike.inner_apply, Matrix.conjTranspose_apply,
      mul_comm]
  rw [orthonormal_iff_ite]
  constructor
  · intro h; ext j k; rw [← hinner, h j k, Matrix.one_apply]
  · intro h j k; rw [hinner, h, Matrix.one_apply]

/-- Dually, the rows of {lit}`M` are orthonormal iff {lit}`M Mᴴ = I`. -/
theorem orthonormal_rows_iff {n m : Type*} [Fintype n] [DecidableEq m]
    (M : Matrix m n 𝕜) :
    Orthonormal 𝕜 (fun i => (WithLp.toLp 2 fun j => M i j : EuclideanSpace 𝕜 n)) ↔
      M * Mᴴ = 1 := by
  have hinner : ∀ i i', ⟪(WithLp.toLp 2 fun j => M i j : EuclideanSpace 𝕜 n),
      (WithLp.toLp 2 fun j => M i' j : EuclideanSpace 𝕜 n)⟫_𝕜 = (M * Mᴴ) i' i := by
    intro i i'
    simp [PiLp.inner_apply, Matrix.mul_apply, RCLike.inner_apply, Matrix.conjTranspose_apply]
  rw [orthonormal_iff_ite]
  constructor
  · intro h; ext i i'
    rw [← hinner i' i, h i' i, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · intro h i i'
    rw [hinner, h, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl

/-- 7.53 in full: all six conditions of the book, as one {name}`List.TFAE`. -/
theorem tfae_mem_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] V) :
    [S ∈ unitary (V →ₗ[𝕜] V),
      LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1,
      IsUnit S ∧ Ring.inverse S = LinearMap.adjoint S,
      (Orthonormal 𝕜 fun i => S (e i)),
      (Orthonormal 𝕜 fun i => (WithLp.toLp 2 fun j =>
        LinearMap.toMatrix e.toBasis e.toBasis S i j : EuclideanSpace 𝕜 ι)),
      LinearMap.adjoint S ∈ unitary (V →ₗ[𝕜] V)].TFAE := by
  tfae_have 1 ↔ 2 := mem_unitary_iff_adjoint S
  tfae_have 2 ↔ 3 := adjoint_comp_iff_isUnit S
  tfae_have 1 ↔ 4 := mem_unitary_iff_orthonormal_image e S
  tfae_have 4 ↔ 5 := by
    rw [orthonormal_image_iff_orthonormal_columns e e S, orthonormal_columns_iff,
      orthonormal_rows_iff, ← Matrix.star_eq_conjTranspose, ← Matrix.mem_unitaryGroup_iff',
      Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  tfae_have 1 ↔ 6 := mem_unitary_adjoint_iff S
  tfae_finish

/-! 7.54 Eigenvalues of unitary operators have absolute value 1.

If {lit}`S v = λ v` with {lit}`v ≠ 0`, then
{lit}`|λ| ‖v‖ = ‖λ v‖ = ‖S v‖ = ‖v‖`, so {lit}`|λ| = 1`. Only the isometry half of
unitarity is used, so we state it for {lit}`Isometry S` — which drops the
finite-dimensionality hypothesis, and by {lit}`mem_unitary_iff_isometry` is
unitarity when {lit}`V` is finite-dimensional. -/

omit [FiniteDimensional 𝕜 V] in
theorem unitary_eigenvalue_abs_one {S : V →ₗ[𝕜] V} (h : Isometry S) {μ : 𝕜}
    (hμ : HasEigenvalue S μ) : ‖μ‖ = 1 := by
  obtain ⟨v, hv, hv0⟩ := hμ.exists_hasEigenvector
  have hmem : S v = μ • v := Module.End.mem_eigenspace_iff.mp hv
  have hn : ‖v‖ = ‖μ‖ * ‖v‖ := by
    have hsv : ‖S v‖ = ‖μ‖ * ‖v‖ := by rw [hmem, norm_smul]
    rw [← hsv, isometry_norm_map h v]
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
    S ∈ unitary (E →ₗ[ℂ] E) ↔ ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ E),
      ∀ i, ∃ μ : ℂ, S (e i) = μ • e i ∧ ‖μ‖ = 1 := by
  constructor
  · intro hS
    obtain ⟨h1, h2⟩ := (mem_unitary_iff_adjoint S).mp hS
    have hnorm : IsStarNormal S :=
      (LADR.Section_7A.normal_iff_comp S).mpr (by rw [h1, h2])
    obtain ⟨n, e, he⟩ := LADR.Section_7B.complex_spectral S hnorm
    refine ⟨n, e, fun i => ⟨⟪e i, S (e i)⟫_ℂ, he i, ?_⟩⟩
    have hnormeq : ‖S (e i)‖ = ‖e i‖ :=
      isometry_norm_map ((mem_unitary_iff_isometry S).mp hS) (e i)
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
    exact (mem_unitary_iff_isometry S).mpr
      (isometry_of_orthonormal_image_isometry e S horth)

/-! # QR Factorization -/

/-! 7.56 Definition: unitary matrix

An {lit}`n`-by-{lit}`n` matrix is *unitary* if its columns form an orthonormal list
in {lit}`𝔽ⁿ`. Equivalently (Euclidean inner product of columns {lit}`k, r` equals
{lit}`(Q* Q)ₖᵣ`), {lit}`Q* Q = I`, which is the membership condition of mathlib's
{name}`Matrix.unitaryGroup` — the spelling we use for "{lit}`Q` is unitary". -/

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- {lit}`ℳ` of the operator {lit}`v ↦ Q v` in the standard basis of {lit}`𝔽ⁿ` is
{lit}`Q` itself. -/
theorem toMatrix_toEuclideanLin (Q : Matrix n n 𝕜) :
    LinearMap.toMatrix (EuclideanSpace.basisFun n 𝕜).toBasis
      (EuclideanSpace.basisFun n 𝕜).toBasis (Matrix.toEuclideanLin Q) = Q := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

/-! 7.57 Characterizations of unitary matrices

For a square matrix {lit}`Q`: (a) the columns of {lit}`Q` are orthonormal, i.e.
{lit}`Q` is unitary; (b) the rows are orthonormal; (c) {lit}`‖Q v‖ = ‖v‖` for all
{lit}`v ∈ 𝔽ⁿ`; (d) {lit}`Q* Q = Q Q* = I`, i.e. {lit}`Q ∈ Matrix.unitaryGroup`.
Axler leaves the proof as Exercise 17. (a) ⟺ (d) and (b) ⟺ (d) are
{lit}`orthonormal_columns_iff` / {lit}`orthonormal_rows_iff` combined with
{name}`Matrix.mem_unitaryGroup_iff'` / {name}`Matrix.mem_unitaryGroup_iff` (using
{lit}`star Q = Q*`, the conjugate transpose); (c) ⟺ (a) is 7.49 for the operator
{name}`Matrix.toEuclideanLin` {lit}`Q` in the standard basis. -/

theorem tfae_mem_unitaryGroup (Q : Matrix n n 𝕜) :
    [(Orthonormal 𝕜 fun j => (WithLp.toLp 2 fun i => Q i j : EuclideanSpace 𝕜 n)),
      (Orthonormal 𝕜 fun i => (WithLp.toLp 2 fun j => Q i j : EuclideanSpace 𝕜 n)),
      Isometry (Matrix.toEuclideanLin Q),
      Q ∈ Matrix.unitaryGroup n 𝕜].TFAE := by
  tfae_have 1 ↔ 4 := by
    rw [orthonormal_columns_iff, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff']
  tfae_have 2 ↔ 4 := by
    rw [orthonormal_rows_iff, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff]
  tfae_have 3 ↔ 1 := by
    rw [isometry_iff_orthonormal_image (EuclideanSpace.basisFun n 𝕜) (Matrix.toEuclideanLin Q),
      orthonormal_image_iff_orthonormal_columns (EuclideanSpace.basisFun n 𝕜)
        (EuclideanSpace.basisFun n 𝕜) (Matrix.toEuclideanLin Q), toMatrix_toEuclideanLin]
  tfae_finish

/-- (a) ⟺ (d) in the equational form used by the QR proofs below. -/
theorem mem_unitaryGroup_iff_conjTranspose (Q : Matrix n n 𝕜) :
    Q ∈ Matrix.unitaryGroup n 𝕜 ↔ Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact ⟨fun h => ⟨(Matrix.mem_unitaryGroup_iff').mp h, (Matrix.mem_unitaryGroup_iff).mp h⟩,
    fun h => (Matrix.mem_unitaryGroup_iff').mpr h.1⟩

/-- {lit}`R` has only positive numbers on its diagonal, in the sense Axler uses for
{lit}`𝐅 = ℂ` as well: each {lit}`R i i` is a *positive real*. This is the normalization
that makes the {lit}`QR` (7.58) and Cholesky (7.63) factorizations unique. Equivalently
{lit}`0 < R i i` for the {lit}`ComplexOrder` order on {lit}`𝕜` ({name}`RCLike.pos_iff`). -/
def HasPosRealDiag {m : Type*} (R : Matrix m m 𝕜) : Prop :=
  ∀ i, 0 < RCLike.re (R i i) ∧ RCLike.im (R i i) = 0

open scoped ComplexOrder in
/-- {name}`HasPosRealDiag` is diagonal positivity for the {lit}`ComplexOrder` order. -/
theorem hasPosRealDiag_iff {m : Type*} (R : Matrix m m 𝕜) :
    HasPosRealDiag R ↔ ∀ i, 0 < R i i :=
  forall_congr' fun _ => RCLike.pos_iff.symm

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
    (hA : LinearIndependent 𝕜 A.col) :
    ∃ Q R : Matrix (Fin N) (Fin N) 𝕜, Q ∈ Matrix.unitaryGroup (Fin N) 𝕜 ∧
      R.BlockTriangular id ∧ HasPosRealDiag R ∧ A = Q * R := by
  classical
  -- Gram–Schmidt needs the columns as vectors of the inner product space
  -- `EuclideanSpace`; linear independence transfers along `WithLp.linearEquiv`.
  set f : Fin N → EuclideanSpace 𝕜 (Fin N) := fun i => WithLp.toLp 2 (A.col i) with hfdef
  have hf : LinearIndependent 𝕜 f :=
    hA.map' (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm.injective)
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
        InnerProductSpace.gramSchmidtNormed_unit_length i hf
      intro hz; rw [hz, norm_zero] at hlen; norm_num at hlen
    have hei : e i = InnerProductSpace.gramSchmidtNormed 𝕜 f i :=
      InnerProductSpace.gramSchmidtOrthonormalBasis_apply h hne
    simp only [Matrix.of_apply, hei, gramSchmidtNormed_inner_self hf i]
    have hpos : 0 < ‖InnerProductSpace.gramSchmidt 𝕜 f i‖ :=
      norm_pos_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero i hf)
    exact ⟨by rw [RCLike.ofReal_re]; exact hpos, by rw [RCLike.ofReal_im]⟩
  · ext k i
    simp only [Matrix.mul_apply, Matrix.of_apply]
    have hsum := e.sum_repr (f i)
    have hL := congrArg (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)) hsum
    rw [map_sum] at hL
    simp only [map_smul, OrthonormalBasis.repr_apply_apply] at hL
    have hLk := congrFun hL k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hLk
    have hfik : (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)) (f i) k = A k i := rfl
    rw [hfik] at hLk
    rw [← hLk]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- A unitary upper-triangular matrix with positive real diagonal is the identity.
Since {lit}`U⁻¹ = U*` is upper triangular ({name}`Matrix.blockTriangular_inv_of_blockTriangular`)
while {lit}`U*` is lower triangular, {lit}`U` is diagonal; being unitary with
positive real diagonal then forces {lit}`U = I`. This is the key to QR uniqueness. -/
theorem unitary_upperTri_eq_one {N : ℕ} (U : Matrix (Fin N) (Fin N) 𝕜)
    (hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜) (hUT : U.BlockTriangular id)
    (hdiag : HasPosRealDiag U) : U = 1 := by
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
    (hR₁d : HasPosRealDiag R₁) (hA₁ : A = Q₁ * R₁)
    (hQ₂ : Q₂ ∈ Matrix.unitaryGroup (Fin N) 𝕜) (hR₂t : R₂.BlockTriangular id)
    (hR₂d : HasPosRealDiag R₂) (hA₂ : A = Q₂ * R₂) :
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
  have hUd : HasPosRealDiag U := by
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

/-- 7.58 QR factorization, existence and uniqueness in one statement: a square matrix
with linearly independent columns has a *unique* pair {lit}`(Q, R)` with {lit}`Q`
unitary, {lit}`R` upper triangular with positive real diagonal, and {lit}`A = QR`.
This is {name}`QR_factorization` and {name}`QR_unique` packaged as an {lit}`∃!`. -/
theorem QR_factorization_existsUnique {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (hA : LinearIndependent 𝕜 A.col) :
    ∃! QR : Matrix (Fin N) (Fin N) 𝕜 × Matrix (Fin N) (Fin N) 𝕜,
      QR.1 ∈ Matrix.unitaryGroup (Fin N) 𝕜 ∧
        QR.2.BlockTriangular id ∧ HasPosRealDiag QR.2 ∧ A = QR.1 * QR.2 := by
  obtain ⟨Q, R, hQ, hRt, hRd, hAQR⟩ := QR_factorization A hA
  refine ⟨(Q, R), ⟨hQ, hRt, hRd, hAQR⟩, ?_⟩
  rintro ⟨Q', R'⟩ ⟨hQ', hR't, hR'd, hAQR'⟩
  obtain ⟨hQeq, hReq⟩ := QR_unique A Q' R' Q R hQ' hR't hR'd hAQR' hQ hRt hRd hAQR
  simp only [Prod.mk.injEq]
  exact ⟨hQeq, hReq⟩

/-! 7.60 Example: QR factorization of a 3-by-3 matrix

Axler runs the construction in the proof of 7.58 on
{lit}`A = !![1,2,1; 0,1,-4; 0,3,2]`. Gram–Schmidt applied to the columns
{lit}`v₁ = (1,0,0)`, {lit}`v₂ = (2,1,3)`, {lit}`v₃ = (1,−4,2)` produces the
orthonormal list {lit}`e₁ = (1,0,0)`, {lit}`e₂ = (0,1/√10,3/√10)`,
{lit}`e₃ = (0,−3/√10,1/√10)`; then {lit}`Q` has columns {lit}`e₁, e₂, e₃` and
{lit}`Rⱼₖ = ⟨vₖ, eⱼ⟩`. -/

/-- The matrix {lit}`A` of Example 7.60. -/
def A_7_60 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 2, 1; 0, 1, -4; 0, 3, 2]

/-- The unitary factor {lit}`Q` of Example 7.60: its columns are the Gram–Schmidt
orthonormalization {lit}`e₁, e₂, e₃` of the columns of {lit}`A`. -/
noncomputable def Q_7_60 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0;
     0, 1 / Real.sqrt 10, -3 / Real.sqrt 10;
     0, 3 / Real.sqrt 10, 1 / Real.sqrt 10]

/-- The upper-triangular factor {lit}`R` of Example 7.60, with
{lit}`Rⱼₖ = ⟨vₖ, eⱼ⟩`. -/
noncomputable def R_7_60 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 2, 1;
     0, Real.sqrt 10, Real.sqrt 10 / 5;
     0, 0, 7 * Real.sqrt 10 / 5]

/-- 7.60: {lit}`A = QR` really is a QR factorization — {lit}`Q` is unitary and
{lit}`R` is upper triangular with only positive numbers on its diagonal. By
{lit}`QR_unique` it is the only one. -/
theorem QR_7_60 :
    Q_7_60 ∈ Matrix.unitaryGroup (Fin 3) ℝ ∧
      R_7_60.BlockTriangular id ∧ HasPosRealDiag R_7_60 ∧
      A_7_60 = Q_7_60 * R_7_60 := by
  have hs : (0 : ℝ) < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 10 * Real.sqrt 10 = 10 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q_7_60, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;> linarith [hs2]
  · intro i j h
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd h (by decide)
        | simp [R_7_60]
  · intro i
    refine ⟨?_, ?_⟩ <;> fin_cases i <;> simp [R_7_60]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A_7_60, Q_7_60, R_7_60, Matrix.mul_apply, Fin.sum_univ_three] <;>
      field_simp <;> linarith [hs2]

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
{lit}`⟨B x, x⟩ > 0` for every nonzero {lit}`x ∈ 𝔽ⁿ` (Euclidean inner product).

This is mathlib's {name}`Matrix.PosDef`: {lit}`B.IsHermitian` (i.e. {lit}`Bᴴ = B`)
together with {lit}`0 < xᴴ B x` for {lit}`x ≠ 0`, where the quadratic form is written
with the Euclidean dot product ({name}`Matrix.posDef_iff_dotProduct_mulVec`) and
{lit}`0 < ·` is the {lit}`ComplexOrder` order on {lit}`𝕜`, i.e. "positive real"
({name}`RCLike.pos_iff`). Axler's {lit}`⟨B x, x⟩` and mathlib's
{lit}`xᴴ B x = ⟨x, B x⟩` are complex conjugates of each other, so they are positive
together. -/

open scoped ComplexOrder in
/-- 7.63 Cholesky factorization (existence). Every positive definite matrix {lit}`B`
factors as {lit}`B = Rᴴ * R` with {lit}`R` upper triangular and positive real diagonal.
Following Axler: the positive square root of {lit}`B` supplies an invertible {lit}`A` with
{lit}`Aᴴ * A = B`; a QR factorization {lit}`A = Q * R` then gives
`B = Rᴴ * Qᴴ * Q * R = Rᴴ * R`. -/
theorem cholesky_factorization {N : ℕ} (B : Matrix (Fin N) (Fin N) 𝕜)
    (hB : B.PosDef) :
    ∃ R : Matrix (Fin N) (Fin N) 𝕜, R.BlockTriangular id ∧
      HasPosRealDiag R ∧ B = Rᴴ * R := by
  classical
  -- `toEuclideanLin` turns matrix product into composition of operators.
  have hmul : ∀ M P : Matrix (Fin N) (Fin N) 𝕜,
      (M * P).toEuclideanLin = M.toEuclideanLin ∘ₗ P.toEuclideanLin := by
    intro M P; ext v
    simp only [LinearMap.comp_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec]
  -- `Bop = toEuclideanLin B` is a positive operator, and it is injective since `B` is
  -- positive *definite*, hence invertible.
  have hBoppos : B.toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hB.posSemidef
  have hBopinj : Function.Injective B.toEuclideanLin := by
    have hmv : Function.Injective B.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hB.isUnit
    intro u v huv
    refine WithLp.ofLp_injective 2 (hmv ?_)
    simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp] using congrArg WithLp.ofLp huv
  -- positive square root `Rop` with `Rop ∘ Rop = Bop`.
  obtain ⟨Rop, hRoppos, hRopRop⟩ := LADR.Section_7C.exists_positive_sqrt hBoppos
  have hRopinj : Function.Injective Rop := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply hBopinj
    rw [map_zero, ← hRopRop, LinearMap.comp_apply, hv, map_zero]
  -- matrix `A` of `Rop`; its columns are linearly independent.
  set A := Matrix.toEuclideanLin.symm Rop with hAdef
  have hARop : A.toEuclideanLin = Rop := LinearEquiv.apply_symm_apply _ _
  have hAcol : ∀ i, (WithLp.toLp 2 (A.col i) : EuclideanSpace 𝕜 (Fin N))
      = Rop (EuclideanSpace.single i 1) := by
    intro i
    rw [← hARop, Matrix.toLpLin_apply]
    ext k
    simp [EuclideanSpace.single, Matrix.mulVec_single, Matrix.col_apply]
  have hA : LinearIndependent 𝕜 A.col := by
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
    have heq : (fun i => (WithLp.toLp 2 (A.col i) : EuclideanSpace 𝕜 (Fin N)))
        = ⇑Rop ∘ fun i => (EuclideanSpace.single i 1 : EuclideanSpace 𝕜 (Fin N)) := funext hAcol
    rw [← heq] at hmap
    -- descend from the `EuclideanSpace` lift back to the plain columns
    exact hmap.map' (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).injective)
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
    (hR₁t : R₁.BlockTriangular id)
    (hR₁d : HasPosRealDiag R₁) (hB₁ : B = R₁ᴴ * R₁)
    (hR₂t : R₂.BlockTriangular id)
    (hR₂d : HasPosRealDiag R₂) (hB₂ : B = R₂ᴴ * R₂) :
    R₁ = R₂ := by
  have diagval : ∀ z : 𝕜, RCLike.im z = 0 → z = ((RCLike.re z : ℝ) : 𝕜) := by
    intro z hz
    conv_lhs => rw [← RCLike.re_add_im z]
    rw [hz, RCLike.ofReal_zero, zero_mul, add_zero]
  have hR₁ne : ∀ i, R₁ i i ≠ 0 := fun i h => by have := (hR₁d i).1; rw [h] at this; simp at this
  have hdet1 : R₁.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hR₁t]
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
  have hR₁invt : R₁⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hR₁t
  have hUt : U.BlockTriangular id := hUdef ▸ hR₂t.mul hR₁invt
  have hUd : HasPosRealDiag U := by
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
  rw [← hUR, hU1, Matrix.one_mul]

open scoped ComplexOrder in
/-- 7.63 Cholesky factorization, existence and uniqueness in one statement: a positive
definite {lit}`B` has a *unique* upper-triangular {lit}`R` with positive real diagonal and
{lit}`B = Rᴴ R`. This is {name}`cholesky_factorization` and {name}`cholesky_unique`
packaged as an {lit}`∃!`, the analogue of {name}`QR_factorization_existsUnique`. -/
theorem cholesky_factorization_existsUnique {N : ℕ} (B : Matrix (Fin N) (Fin N) 𝕜)
    (hB : B.PosDef) :
    ∃! R : Matrix (Fin N) (Fin N) 𝕜,
      R.BlockTriangular id ∧ HasPosRealDiag R ∧ B = Rᴴ * R := by
  obtain ⟨R, hRt, hRd, hBR⟩ := cholesky_factorization B hB
  refine ⟨R, ⟨hRt, hRd, hBR⟩, ?_⟩
  rintro R' ⟨hR't, hR'd, hBR'⟩
  exact cholesky_unique B R' R hR't hR'd hBR' hRt hRd hBR

/-! # Exercises 7D -/

/-- 7D.1 Suppose {lit}`dim V ≥ 2`. Then {lit}`S` is an isometry iff it maps every
orthonormal list of length two to an orthonormal list. -/
theorem exercise_7D_1 (S : V →ₗ[𝕜] W) :
    Isometry S ↔ ∀ e : Fin 2 → V, Orthonormal 𝕜 e → Orthonormal 𝕜 (fun i => S (e i)) := by
  sorry

/-- 7D.2 A nonzero {lit}`T` is a scalar multiple of an isometry iff {lit}`T`
preserves orthogonality. -/
theorem exercise_7D_2 (T : V →ₗ[𝕜] W) (hT : T ≠ 0) :
    (∃ (c : 𝕜) (S : V →ₗ[𝕜] W), Isometry S ∧ T = c • S) ↔
      ∀ u v, ⟪u, v⟫_𝕜 = 0 → ⟪T u, T v⟫_𝕜 = 0 := by
  sorry

/-- 7D.3(a) The product of two unitary operators is unitary. -/
theorem exercise_7D_3a {S T : V →ₗ[𝕜] V} (hS : S ∈ unitary (V →ₗ[𝕜] V))
    (hT : T ∈ unitary (V →ₗ[𝕜] V)) : S ∘ₗ T ∈ unitary (V →ₗ[𝕜] V) := by
  sorry

/-- 7D.3(b) The adjoint (inverse) of a unitary operator is unitary. -/
theorem exercise_7D_3b {S : V →ₗ[𝕜] V} (hS : S ∈ unitary (V →ₗ[𝕜] V)) :
    LinearMap.adjoint S ∈ unitary (V →ₗ[𝕜] V) := by
  sorry

/-- 7D.4 Over {lit}`ℂ`, for self-adjoint {lit}`A, B`, the operator {lit}`A + iB` is
unitary iff {lit}`AB = BA` and {lit}`A² + B² = I`. -/
theorem exercise_7D_4 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : E →ₗ[ℂ] E}
    (hA : LinearMap.IsSymmetric A) (hB : LinearMap.IsSymmetric B) :
    A + Complex.I • B ∈ unitary (E →ₗ[ℂ] E) ↔
      (A ∘ₗ B = B ∘ₗ A ∧ A ∘ₗ A + B ∘ₗ B = 1) := by
  sorry

/-- 7D.5 The following are equivalent: (a) {lit}`S` is a self-adjoint unitary;
(b) {lit}`S = 2P − I` for an orthogonal projection {lit}`P`; (c) {lit}`S = 1` on
some {lit}`U` and {lit}`S = −1` on {lit}`U⟂`. -/
theorem exercise_7D_5 (S : V →ₗ[𝕜] V) :
    [LinearMap.IsSymmetric S ∧ S ∈ unitary (V →ₗ[𝕜] V),
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
      S ∈ unitary (EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3)) ∧
        T₁ = LinearMap.adjoint S ∘ₗ T₂ ∘ₗ S := by
  sorry

/-- 7D.7 There are self-adjoint operators on {lit}`𝔽⁴` both with eigenvalues
{lit}`2, 5, 7` that are not unitarily equivalent. -/
theorem exercise_7D_7 :
    ∃ T₁ T₂ : EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4),
      LinearMap.IsSymmetric T₁ ∧ LinearMap.IsSymmetric T₂ ∧
      (∀ μ : 𝕜, HasEigenvalue T₁ μ ↔ μ = 2 ∨ μ = 5 ∨ μ = 7) ∧
      (∀ μ : 𝕜, HasEigenvalue T₂ μ ↔ μ = 2 ∨ μ = 5 ∨ μ = 7) ∧
      ¬ ∃ S : EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4),
        S ∈ unitary (EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4)) ∧
          T₁ = LinearMap.adjoint S ∘ₗ T₂ ∘ₗ S := by
  sorry

/-- 7D.8 Counterexample: {lit}`‖S eₖ‖ = 1` on an orthonormal basis does not imply
{lit}`S` is unitary. -/
theorem exercise_7D_8 :
    ¬ ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
      (S : E →ₗ[𝕜] E) (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 E),
      (∀ k, ‖S (e k)‖ = 1) → S ∈ unitary (E →ₗ[𝕜] E) := by
  sorry

/-- 7D.9 Over {lit}`ℂ`, if every eigenvalue of {lit}`T` has absolute value 1 and
{lit}`‖T v‖ ≤ ‖v‖` for all {lit}`v`, then {lit}`T` is unitary. -/
theorem exercise_7D_9 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (h1 : ∀ μ : ℂ, HasEigenvalue T μ → ‖μ‖ = 1) (h2 : ∀ v, ‖T v‖ ≤ ‖v‖) :
    T ∈ unitary (E →ₗ[ℂ] E) := by
  sorry

/-- 7D.10 Over {lit}`ℂ`, for self-adjoint {lit}`T` with {lit}`‖Tv‖ ≤ ‖v‖`:
(a) {lit}`I − T²` is positive; (b) {lit}`T + i√(I − T²)` is unitary. -/
theorem exercise_7D_10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : LinearMap.IsSymmetric T)
    (hnorm : ∀ v, ‖T v‖ ≤ ‖v‖) :
    (1 - T ∘ₗ T).IsPositive ∧
      ∀ R : E →ₗ[ℂ] E, R.IsPositive → R ∘ₗ R = 1 - T ∘ₗ T →
        T + Complex.I • R ∈ unitary (E →ₗ[ℂ] E) := by
  sorry

/-- 7D.11 {lit}`S` is unitary iff it maps the closed unit ball onto itself. -/
theorem exercise_7D_11 (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔ (S '' {v | ‖v‖ ≤ 1}) = {v | ‖v‖ ≤ 1} := by
  sorry

/-- 7D.12 Counterexample: {lit}`S` invertible with {lit}`‖S⁻¹v‖ = ‖Sv‖` for all
{lit}`v` need not be unitary. -/
theorem exercise_7D_12 :
    ¬ ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
      (S : E ≃ₗ[𝕜] E), (∀ v, ‖S.symm v‖ = ‖S v‖) → (S : E →ₗ[𝕜] E) ∈ unitary (E →ₗ[𝕜] E) := by
  sorry

/-- 7D.13 For a square complex matrix, the columns form an orthonormal list iff the
rows do (equivalently {lit}`Q* Q = I ⟺ Q Q* = I`). -/
theorem exercise_7D_13 {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix n n 𝕜) :
    Qᴴ * Q = 1 ↔ Q * Qᴴ = 1 := by
  sorry

/-- 7D.14 For a unit vector {lit}`v` and {lit}`b ∈ 𝔽` (with {lit}`dim V ≥ 2`), there
is a unitary {lit}`S` with {lit}`⟨Sv, v⟩ = b` iff {lit}`|b| ≤ 1`. -/
theorem exercise_7D_14 (h : 2 ≤ finrank 𝕜 V) (v : V) (hv : ‖v‖ = 1) (b : 𝕜) :
    (∃ S : V →ₗ[𝕜] V, S ∈ unitary (V →ₗ[𝕜] V) ∧ ⟪S v, v⟫_𝕜 = b) ↔ ‖b‖ ≤ 1 := by
  sorry

/-- 7D.15 For unitary {lit}`T` with {lit}`T − I` invertible (inverse {lit}`Tinv`):
(a) {lit}`(T + I)(T − I)⁻¹` is skew. -/
theorem exercise_7D_15a (T : V →ₗ[𝕜] V) (hT : T ∈ unitary (V →ₗ[𝕜] V)) (Tinv : V →ₗ[𝕜] V)
    (hi1 : Tinv ∘ₗ (T - 1) = 1) (hi2 : (T - 1) ∘ₗ Tinv = 1) :
    LinearMap.adjoint ((T + 1) ∘ₗ Tinv) = -((T + 1) ∘ₗ Tinv) := by
  sorry

/-- 7D.15 (b) Over {lit}`ℂ`, {lit}`i(T + I)(T − I)⁻¹` is self-adjoint. -/
theorem exercise_7D_15b {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T ∈ unitary (E →ₗ[ℂ] E)) (Tinv : E →ₗ[ℂ] E)
    (hi1 : Tinv ∘ₗ (T - 1) = 1) (hi2 : (T - 1) ∘ₗ Tinv = 1) :
    LinearMap.IsSymmetric (Complex.I • ((T + 1) ∘ₗ Tinv)) := by
  sorry

/-- 7D.16 Over {lit}`ℂ`, for self-adjoint {lit}`T`, {lit}`(T + iI)(T − iI)⁻¹` is
unitary and {lit}`1` is not an eigenvalue of it. -/
theorem exercise_7D_16 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : LinearMap.IsSymmetric T)
    (Tinv : E →ₗ[ℂ] E) (hi1 : Tinv ∘ₗ (T - Complex.I • 1) = 1)
    (hi2 : (T - Complex.I • 1) ∘ₗ Tinv = 1) :
    (T + Complex.I • 1) ∘ₗ Tinv ∈ unitary (E →ₗ[ℂ] E) ∧
      ¬ HasEigenvalue ((T + Complex.I • 1) ∘ₗ Tinv) 1 := by
  sorry

/-- 7D.17 (7.57) A matrix is unitary iff its conjugate transpose is unitary
(columns orthonormal iff rows orthonormal). -/
theorem exercise_7D_17 {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix n n 𝕜) :
    Q ∈ Matrix.unitaryGroup n 𝕜 ↔ Qᴴ ∈ Matrix.unitaryGroup n 𝕜 := by
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
    F ∈ unitary (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) ∧
      F ∘ₗ F ∘ₗ F ∘ₗ F = 1 := by
  sorry

/-- 7D.20 A square matrix with linearly independent columns has unique matrices
{lit}`R` lower triangular with only positive numbers on its diagonal and {lit}`Q`
unitary with {lit}`A = RQ` (the {lit}`RQ` variant of 7.58). -/
theorem exercise_7D_20 {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (hA : LinearIndependent 𝕜 A.col) :
    ∃! RQ : Matrix (Fin N) (Fin N) 𝕜 × Matrix (Fin N) (Fin N) 𝕜,
      RQ.1.BlockTriangular OrderDual.toDual ∧
        HasPosRealDiag RQ.1 ∧
        RQ.2 ∈ Matrix.unitaryGroup (Fin N) 𝕜 ∧ A = RQ.1 * RQ.2 := by
  sorry

end LADR.Section_7D
