module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.Data.List.TFAE
public import LinearAlgebraDoneRightLean.Section_7B
public import LinearAlgebraDoneRightLean.Section_7C
public import Mathlib.Tactic.Linter.Style
public import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7D: Isometries, Unitary Operators, and Matrix Factorization
-/

@[expose] public section

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

Axler's proof: write {lit}`v = ⟨v, e₁⟩e₁ + ⋯ + ⟨v, eₙ⟩eₙ` (7.46, i.e. 6.30(a)), so
{lit}`‖v‖² = |⟨v, e₁⟩|² + ⋯ + |⟨v, eₙ⟩|²` (7.47, 6.30(b)). Applying {lit}`S` gives
{lit}`S v = ⟨v, e₁⟩g₁ + ⋯ + ⟨v, eₙ⟩gₙ`, so {lit}`‖S v‖²` is the same sum (7.48, 6.24). -/

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
@[avoiding LinearMap.norm_map_iff_inner_map_map]
theorem isometry_of_orthonormal_image_isometry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] W)
    (h : Orthonormal 𝕜 (fun i => S (b i))) : Isometry S := by
  refine (isometry_iff_norm S).mpr fun v => ?_
  -- 7.46 with S applied: S v = ⟨v, e₁⟩ S e₁ + ⋯ + ⟨v, eₙ⟩ S eₙ
  have hSv : S v = ∑ i, ⟪b i, v⟫_𝕜 • S (b i) := by
    conv_lhs => rw [LADR.Section_6B.orthonormalBasis_repr b v]
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  -- 7.47 and 7.48: both squared norms equal ∑ |⟨v, eₖ⟩|²
  have h2 : ‖S v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [hSv, LADR.Section_6B.norm_sq_sum_orthonormal h, LADR.Section_6B.parseval b v]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-! 7.49 Characterizations of isometries

For {lit}`S ∈ ℒ(V, W)` with orthonormal bases {lit}`e` of {lit}`V` and {lit}`f`
of {lit}`W`, the following are equivalent:
(a) {lit}`S` is an isometry;
(b) {lit}`S* S = I`;
(c) {lit}`⟨S u, S v⟩ = ⟨u, v⟩` for all {lit}`u, v`;
(d) {lit}`S e₁, …, S eₙ` is an orthonormal list;
(e) the columns of {lit}`ℳ(S, e, f)` form an orthonormal list in {lit}`𝔽ᵐ`.

Axler proves the cycle (a) ⟹ (b) ⟹ (c) ⟹ (d) ⟹ (e) ⟹ (a). (a) ⟹ (b): for an
isometry, {lit}`⟨(I − S*S)v, v⟩ = ‖v‖² − ‖Sv‖² = 0`, so the self-adjoint operator
{lit}`I − S*S` is {lit}`0` by 7.16. (b) ⟹ (c): {lit}`⟨Su, Sv⟩ = ⟨S*Su, v⟩ = ⟨u, v⟩`.
(c) ⟹ (d) is immediate. (d) ⟺ (e) is 7.50: column {lit}`k` of {lit}`ℳ(S, e, f)` is the
coordinate vector of {lit}`S eₖ` in the basis {lit}`f`. (d) ⟹ (a) is Example 7.45. -/

/-- (a) ⟹ (b): an isometry satisfies {lit}`S* S = I`, by 7.16 applied to the
self-adjoint operator {lit}`I − S* S`. -/
@[avoiding LinearMap.norm_map_iff_inner_map_map]
theorem adjoint_comp_self_of_isometry {S : V →ₗ[𝕜] W} (h : Isometry S) : S† ∘ₗ S = 1 := by
  have hsym : (1 - S† ∘ₗ S : V →ₗ[𝕜] V).IsSymmetric := by
    intro u v
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply, inner_sub_left,
      inner_sub_right, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_right]
  -- ⟨(I − S*S)v, v⟩ = ‖v‖² − ‖Sv‖² = 0
  have hzero : ∀ v, ⟪(1 - S† ∘ₗ S : V →ₗ[𝕜] V) v, v⟫_𝕜 = 0 := by
    intro v
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply, inner_sub_left,
      LinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      isometry_norm_map h v, sub_self]
  have h0 := (LADR.Section_7A.symmetric_inner_map_self_eq_zero hsym).mp hzero
  exact (sub_eq_zero.mp h0).symm

omit [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] in
/-- (c) ⟹ (a): preserving inner products preserves {lit}`‖v‖² = ⟨v, v⟩`. -/
theorem isometry_of_inner {S : V →ₗ[𝕜] W} (h : ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜) :
    Isometry S := by
  refine (isometry_iff_norm S).mpr fun v => ?_
  have h2 : ‖S v‖ ^ 2 = ‖v‖ ^ 2 := by
    have := h v v
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
    exact_mod_cast this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- (c) ⟺ (b): preserving inner products is equivalent to {lit}`S* S = I`. -/
theorem inner_iff_adjoint_comp (S : V →ₗ[𝕜] W) :
    (∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜) ↔ S† ∘ₗ S = 1 := by
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
    Isometry S ↔ S† ∘ₗ S = 1 :=
  ⟨adjoint_comp_self_of_isometry, fun h => isometry_of_inner ((inner_iff_adjoint_comp S).mpr h)⟩

/-- (a) ⟺ (c): an isometry is exactly an inner-product-preserving map. -/
theorem isometry_iff_inner (S : V →ₗ[𝕜] W) :
    Isometry S ↔ ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜 :=
  (isometry_iff_adjoint_comp S).trans (inner_iff_adjoint_comp S).symm

/-- (a) ⟺ (d): {lit}`S` is an isometry iff it carries some (hence any) orthonormal
basis to an orthonormal list. Forward is (a) ⟹ (c) ⟹ (d); backward is 7.45. -/
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
      Orthonormal 𝕜 (fun j =>
        (WithLp.toLp 2 ((LinearMap.toMatrix e.toBasis f.toBasis S).col j) :
          EuclideanSpace 𝕜 κ)) := by
  have hcol : (fun j =>
      (WithLp.toLp 2 ((LinearMap.toMatrix e.toBasis f.toBasis S).col j) :
        EuclideanSpace 𝕜 κ))
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
      S† ∘ₗ S = 1,
      ∀ u v, ⟪S u, S v⟫_𝕜 = ⟪u, v⟫_𝕜,
      (Orthonormal 𝕜 fun i => S (e i)),
      (Orthonormal 𝕜 fun j =>
        (WithLp.toLp 2 ((LinearMap.toMatrix e.toBasis f.toBasis S).col j) :
          EuclideanSpace 𝕜 κ))].TFAE := by
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
      S† ∘ₗ S = 1 ∧ S ∘ₗ S† = 1 :=
  Unitary.mem_iff

/-- Hence on {lit}`ℒ(V)` "unitary" and "isometry" coincide. -/
theorem mem_unitary_iff_isometry (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔ Isometry S := by
  rw [mem_unitary_iff_adjoint]
  constructor
  · exact fun h => (isometry_iff_adjoint_comp S).mpr h.1
  · intro hiso
    have hSS : S† ∘ₗ S = 1 := (isometry_iff_adjoint_comp S).mp hiso
    refine ⟨hSS, ?_⟩
    ext w
    obtain ⟨x, rfl⟩ := (isometry_bijective hiso).surjective w
    have hx : S† (S x) = x := by
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
  -- check both `Qᴴ Q = I` and `Q Qᴴ = I` by direct computation
  refine Unitary.mem_iff.mpr ⟨?_, ?_⟩ <;>
  · ext i j
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
We prove (a) ⟺ (d), (a) ⟺ (f), and (f) ⟺ (e), then collect all six into a single
{lit}`TFAE` list. Statement (c) is the reading of (b) as "{lit}`S*` is the two-sided
inverse", spelled with {name}`Ring.inverse` on the ring {lit}`ℒ(V)`. In (d) the
orthonormal list {lit}`S e₁, …, S eₙ` is indexed by the basis index type, so being
orthonormal already makes it a basis. For (e) we follow Axler: {lit}`S*` is unitary
exactly when it is an isometry, i.e. (7.49) when the columns of {lit}`ℳ(S*, e)` are
orthonormal; and {lit}`ℳ(S*, e) = ℳ(S, e)ᴴ` (7.9), whose columns are the complex
conjugates of the rows of {lit}`ℳ(S, e)`. -/

/-- (c): for a unitary operator, {lit}`S*` is a two-sided inverse of {lit}`S`. -/
theorem mem_unitary_inverse {S : V →ₗ[𝕜] V} (h : S ∈ unitary (V →ₗ[𝕜] V)) :
    S† ∘ₗ S = 1 ∧ S ∘ₗ S† = 1 :=
  (mem_unitary_iff_adjoint S).mp h

/-- (a) ⟺ (d). -/
theorem mem_unitary_iff_orthonormal_image {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔ Orthonormal 𝕜 (fun i => S (b i)) :=
  (mem_unitary_iff_isometry S).trans (isometry_iff_orthonormal_image b S)

/-- (a) ⟺ (f): {lit}`S` is unitary iff {lit}`S*` is unitary. This is
{name}`Unitary.star_mem_iff` for the star ring {lit}`ℒ(V)`. -/
theorem mem_unitary_adjoint_iff (S : V →ₗ[𝕜] V) :
    S ∈ unitary (V →ₗ[𝕜] V) ↔ S† ∈ unitary (V →ₗ[𝕜] V) :=
  Unitary.star_mem_iff.symm

/-- (b) ⟺ (c): the two-sided-inverse reading of {lit}`S* S = S S* = I`. -/
theorem adjoint_comp_iff_isUnit (S : V →ₗ[𝕜] V) :
    (S† ∘ₗ S = 1 ∧ S ∘ₗ S† = 1) ↔
      (IsUnit S ∧ Ring.inverse S = S†) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨⟨S, S†, h2, h1⟩, rfl⟩,
      Ring.inverse_unit ⟨S, S†, h2, h1⟩⟩
  · rintro ⟨hu, hinv⟩
    exact ⟨by rw [← hinv]; exact Ring.inverse_mul_cancel S hu,
      by rw [← hinv]; exact Ring.mul_inverse_cancel S hu⟩

/-- A list of vectors in {lit}`𝔽ᵐ` given by the columns of {lit}`M` is orthonormal
iff {lit}`Mᴴ M = I`. -/
theorem orthonormal_columns_iff {n m : Type*} [Fintype m] [DecidableEq n]
    (M : Matrix m n 𝕜) :
    Orthonormal 𝕜 (fun j => (WithLp.toLp 2 (M.col j) : EuclideanSpace 𝕜 m)) ↔
      Mᴴ * M = 1 := by
  have hinner : ∀ j k, ⟪(WithLp.toLp 2 (M.col j) : EuclideanSpace 𝕜 m),
      (WithLp.toLp 2 (M.col k) : EuclideanSpace 𝕜 m)⟫_𝕜 = (Mᴴ * M) j k := by
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
    Orthonormal 𝕜 (fun i => (WithLp.toLp 2 (M.row i) : EuclideanSpace 𝕜 n)) ↔
      M * Mᴴ = 1 := by
  have hinner : ∀ i i', ⟪(WithLp.toLp 2 (M.row i) : EuclideanSpace 𝕜 n),
      (WithLp.toLp 2 (M.row i') : EuclideanSpace 𝕜 n)⟫_𝕜 = (M * Mᴴ) i' i := by
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
@[avoiding Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
theorem tfae_mem_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι 𝕜 V) (S : V →ₗ[𝕜] V) :
    [S ∈ unitary (V →ₗ[𝕜] V),
      S† ∘ₗ S = 1 ∧ S ∘ₗ S† = 1,
      IsUnit S ∧ Ring.inverse S = S†,
      (Orthonormal 𝕜 fun i => S (e i)),
      (Orthonormal 𝕜 fun i =>
        (WithLp.toLp 2 ((LinearMap.toMatrix e.toBasis e.toBasis S).row i) :
          EuclideanSpace 𝕜 ι)),
      S† ∈ unitary (V →ₗ[𝕜] V)].TFAE := by
  tfae_have 1 ↔ 2 := mem_unitary_iff_adjoint S
  tfae_have 2 ↔ 3 := adjoint_comp_iff_isUnit S
  tfae_have 1 ↔ 4 := mem_unitary_iff_orthonormal_image e S
  tfae_have 1 ↔ 6 := mem_unitary_adjoint_iff S
  -- (f) ⟺ (e): S* is unitary iff it is an isometry iff the columns of ℳ(S*) are
  -- orthonormal (7.49); ℳ(S*) = ℳ(S)ᴴ (7.9), whose columns are the conjugated rows of ℳ(S).
  tfae_have 6 ↔ 5 := by
    rw [mem_unitary_iff_isometry, isometry_iff_orthonormal_image e,
      orthonormal_image_iff_orthonormal_columns e e, orthonormal_columns_iff,
      orthonormal_rows_iff, LADR.Section_7A.toMatrix_adjoint_eq_conjTranspose e e,
      Matrix.conjTranspose_conjTranspose]
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
          rw [(orthonormal_iff_ite.mp e.orthonormal) i i, ite_eq_left rfl]
        rw [hi, inner_smul_left, inner_smul_right, he1, mul_one, RCLike.conj_mul, hni, ite_eq_left rfl]
        norm_num
      · obtain ⟨μi, hi, hni⟩ := he i
        obtain ⟨μj, hj, hnj⟩ := he j
        rw [hi, hj, inner_smul_left, inner_smul_right, (orthonormal_iff_ite.mp e.orthonormal) i j]
        simp only [ite_eq_right hNe, mul_zero]
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

Axler states this result but leaves its proof to Exercise 17 ("whose proof will be left as
an exercise for the reader"). We prove it outright, because it is the operator results
read in the standard basis of {lit}`𝔽ⁿ`, where the operator {lit}`v ↦ Q v`
({name}`Matrix.toEuclideanLin`) has matrix {lit}`Q`: (c) ⟺ (a) is 7.49 (a) ⟺ (e);
(c) ⟺ (d) is "isometry = unitary" on {lit}`𝔽ⁿ` (7.51) together with 7.9; and
(d) ⟺ (b) is 7.53 (a) ⟺ (e). -/

/-- (d) as an equation pair. Definitional: membership in {name}`unitary` *is* the
conjunction of the two equations ({name}`Unitary.mem_iff`), with
{lit}`star Q = Q*` the conjugate transpose. Also the form used by the QR proofs below. -/
theorem mem_unitaryGroup_iff_conjTranspose (Q : Matrix n n 𝕜) :
    Q ∈ Matrix.unitaryGroup n 𝕜 ↔ Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.mem_iff

/-- A matrix is unitary iff the operator {lit}`v ↦ Q v` on {lit}`𝔽ⁿ` is: in the standard
(orthonormal) basis that operator has matrix {lit}`Q` and its adjoint has matrix
{lit}`Qᴴ` (7.9), so {lit}`S* S = S S* = I` reads {lit}`Qᴴ Q = Q Qᴴ = I`. -/
theorem mem_unitaryGroup_iff_toEuclideanLin (Q : Matrix n n 𝕜) :
    Q ∈ Matrix.unitaryGroup n 𝕜 ↔
      Matrix.toEuclideanLin Q ∈ unitary (EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n) := by
  set b := EuclideanSpace.basisFun n 𝕜
  have hM : ∀ T U : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n,
      T ∘ₗ U = 1 ↔ LinearMap.toMatrix b.toBasis b.toBasis T *
        LinearMap.toMatrix b.toBasis b.toBasis U = 1 := by
    intro T U
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_one b.toBasis]
    exact (LinearMap.toMatrix b.toBasis b.toBasis).injective.eq_iff.symm
  rw [mem_unitaryGroup_iff_conjTranspose, mem_unitary_iff_adjoint, hM, hM,
    LADR.Section_7A.toMatrix_adjoint_eq_conjTranspose b b, toMatrix_toEuclideanLin]

/-- 7.57, following the book: apply 7.49 and 7.53 to the operator {lit}`v ↦ Q v`,
whose matrix in the standard basis is {lit}`Q`. -/
@[avoiding Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
theorem tfae_mem_unitaryGroup (Q : Matrix n n 𝕜) :
    [(Orthonormal 𝕜 fun j => (WithLp.toLp 2 (Q.col j) : EuclideanSpace 𝕜 n)),
      (Orthonormal 𝕜 fun i => (WithLp.toLp 2 (Q.row i) : EuclideanSpace 𝕜 n)),
      Isometry (Matrix.toEuclideanLin Q),
      Q ∈ Matrix.unitaryGroup n 𝕜].TFAE := by
  set b := EuclideanSpace.basisFun n 𝕜
  -- (c) ⟺ (a): 7.49 (a) ⟺ (e) in the standard basis
  tfae_have 3 ↔ 1 := by
    rw [isometry_iff_orthonormal_image b (Matrix.toEuclideanLin Q),
      orthonormal_image_iff_orthonormal_columns b b (Matrix.toEuclideanLin Q),
      toMatrix_toEuclideanLin]
  -- (c) ⟺ (d): on 𝔽ⁿ an isometry is the same as a unitary operator (7.51)
  tfae_have 3 ↔ 4 := by
    rw [mem_unitaryGroup_iff_toEuclideanLin, mem_unitary_iff_isometry]
  -- (d) ⟺ (b): 7.53 (a) ⟺ (e) in the standard basis
  tfae_have 4 ↔ 2 := by
    have h := (tfae_mem_unitary b (Matrix.toEuclideanLin Q)).out 1 5
    rw [toMatrix_toEuclideanLin] at h
    rw [mem_unitaryGroup_iff_toEuclideanLin]
    exact h
  tfae_finish

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
of {lit}`A`: with {lit}`e` the resulting orthonormal basis (packaged as mathlib's
{name}`InnerProductSpace.gramSchmidtOrthonormalBasis`), take {lit}`Q` to have
columns {lit}`eⱼ` and {lit}`Rⱼₖ = ⟨vₖ, eⱼ⟩`. Then {lit}`A = QR` (orthonormal
expansion of each column, 6.30(a)), {lit}`Q` is unitary (its columns are orthonormal),
{lit}`R` is upper triangular because {lit}`span(v₁, …, vₖ) = span(e₁, …, eₖ)` (7.59) is
orthogonal to {lit}`eⱼ` for {lit}`j > k`, and the diagonal
{lit}`Rₖₖ = ‖gramSchmidt vₖ‖ > 0` is a positive real.
*Uniqueness* ({lit}`QR_unique` below) is Axler's argument: in any QR factorization the
columns of the unitary factor satisfy the conditions of Exercise 6B.10, so they are the
Gram–Schmidt list. -/

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
@[avoiding InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular,
  Matrix.mem_unitaryGroup_iff']
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
  -- since the columns are independent, `e` is exactly the Gram–Schmidt list (6.32)
  have hei : ∀ l, e l = InnerProductSpace.gramSchmidtNormed 𝕜 f l := fun l =>
    InnerProductSpace.gramSchmidtOrthonormalBasis_apply h (by
      have hlen := InnerProductSpace.gramSchmidtNormed_unit_length l hf
      intro hz; rw [hz, norm_zero] at hlen; norm_num at hlen)
  refine ⟨Matrix.of fun k j => e j k, Matrix.of fun j i => inner 𝕜 (e j) (f i),
    ?_, ?_, ?_, ?_⟩
  · -- `Q` has orthonormal columns `e₁, …, eₙ`, so it is unitary (7.57)
    refine ((tfae_mem_unitaryGroup _).out 1 4).mp ?_
    have hcol : (fun j => (WithLp.toLp 2 ((Matrix.of fun k j => e j k).col j) :
        EuclideanSpace 𝕜 (Fin N))) = ⇑e := by
      funext j; ext k; simp
    rw [hcol]; exact e.orthonormal
  · -- 7.59: `vⱼ ∈ span(e₁, …, eⱼ)`, and `eᵢ` is orthogonal to that span when `j < i`
    intro i j hji
    simp only [Matrix.of_apply]
    have hmem : f j ∈ Submodule.span 𝕜 (InnerProductSpace.gramSchmidtNormed 𝕜 f '' Set.Iic j) := by
      rw [LADR.Section_6B.span_gramSchmidtNormed_initial]
      exact Submodule.subset_span ⟨j, Set.mem_Iic.mpr le_rfl, rfl⟩
    have hle : Submodule.span 𝕜 (InnerProductSpace.gramSchmidtNormed 𝕜 f '' Set.Iic j) ≤
        (𝕜 ∙ e i)ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left, ← hei l]
      exact e.orthonormal.2 (ne_of_lt (lt_of_le_of_lt (Set.mem_Iic.mp hl) hji))
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hle hmem)
  · intro i
    simp only [Matrix.of_apply, hei i, gramSchmidtNormed_inner_self hf i]
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

omit [FiniteDimensional 𝕜 V] in
/-- The inductive step of Exercise 6B.10 (below): if {lit}`e` has the same initial spans
as {lit}`v`, and
{lit}`eₖ` and {lit}`fₖ` are both orthogonal to {lit}`e₁, …, eₖ₋₁`, then {lit}`eₖ` is a multiple
of {lit}`fₖ`. Write {lit}`W = span(e₁, …, eₖ₋₁)`, {lit}`vₖ = fₖ + w` and {lit}`eₖ = a vₖ + u` with
{lit}`u, w ∈ W`: then {lit}`eₖ - a fₖ = a w + u` is in {lit}`W` and also orthogonal to {lit}`W`. -/
theorem gramSchmidt_unique_step {m : ℕ} (v e : Fin m → V)
    (hspan : ∀ k, Submodule.span 𝕜 (e '' {i | i ≤ k}) = Submodule.span 𝕜 (v '' {i | i ≤ k}))
    (k : Fin m)
    (hfe : ∀ i, i < k → ⟪e i, InnerProductSpace.gramSchmidt 𝕜 v k⟫_𝕜 = 0)
    (hee : ∀ i, i < k → ⟪e i, e k⟫_𝕜 = 0) :
    ∃ a : 𝕜, e k = a • InnerProductSpace.gramSchmidt 𝕜 v k := by
  set f := InnerProductSpace.gramSchmidt 𝕜 v k with hf
  set W := Submodule.span 𝕜 (e '' Set.Iio k) with hW
  -- anything orthogonal to `e₁, …, eₖ₋₁` is orthogonal to their span `W`
  have hperp : ∀ y, (∀ i, i < k → ⟪e i, y⟫_𝕜 = 0) → ∀ x ∈ W, ⟪x, y⟫_𝕜 = 0 := by
    intro y hy x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact hy i hi
    | zero => simp
    | add _ _ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
    | smul c _ _ h => rw [inner_smul_left, h, mul_zero]
  have hfW : ∀ x ∈ W, ⟪x, f⟫_𝕜 = 0 := hperp f hfe
  have heW : ∀ x ∈ W, ⟪x, e k⟫_𝕜 = 0 := hperp (e k) hee
  have hsub : ∀ i, i < k → Submodule.span 𝕜 (v '' {j | j ≤ i}) ≤ W := fun i hi => by
    rw [← hspan i]
    exact Submodule.span_mono (Set.image_mono fun j hj => lt_of_le_of_lt hj hi)
  -- `vₖ = fₖ + w` with `w ∈ W`
  obtain ⟨w, hwW, hvf⟩ : ∃ w ∈ W, v k = f + w := by
    refine ⟨_, Submodule.sum_mem _ fun j hj => ?_, InnerProductSpace.gramSchmidt_def' 𝕜 v k⟩
    rw [Submodule.starProjection_singleton]
    exact Submodule.smul_mem _ _
      (hsub j (Finset.mem_Iio.mp hj) (LADR.Section_6B.gramSchmidt_mem_span_of_le v le_rfl))
  -- `eₖ = a vₖ + u` with `u ∈ W`
  have hek : e k ∈ Submodule.span 𝕜 (insert (v k) (v '' Set.Iio k)) := by
    have h : e k ∈ Submodule.span 𝕜 (v '' {i | i ≤ k}) :=
      hspan k ▸ Submodule.subset_span ⟨k, le_refl k, rfl⟩
    rwa [← Set.image_insert_eq, Set.Iio_insert]
  obtain ⟨a, u, hu, hau⟩ := Submodule.mem_span_insert.mp hek
  have huW : u ∈ W := by
    refine Submodule.span_le.mpr ?_ hu
    rintro _ ⟨i, hi, rfl⟩
    exact hsub i hi (Submodule.subset_span ⟨i, le_refl i, rfl⟩)
  -- the part of `eₖ - a fₖ` in `W` is also orthogonal to `W`, so `eₖ = a fₖ`
  have hr : a • w + u = 0 := by
    have hrW : a • w + u ∈ W := add_mem (Submodule.smul_mem _ _ hwW) huW
    have hrr : e k - a • f = a • w + u := by rw [hau, hvf, smul_add]; abel
    rw [← inner_self_eq_zero (𝕜 := 𝕜)]
    nth_rw 2 [← hrr]
    rw [inner_sub_right, inner_smul_right, heW _ hrW, hfW _ hrW, mul_zero, sub_zero]
  exact ⟨a, by rw [hau, hvf, smul_add, add_assoc, hr, add_zero]⟩

omit [FiniteDimensional 𝕜 V] in
open scoped ComplexOrder in
/-- Exercise 6B.10: the orthonormal list produced by Gram–Schmidt (6.32) is the *unique*
orthonormal list {lit}`e₁, …, eₘ` with {lit}`⟨vₖ, eₖ⟩ > 0` and
{lit}`span(v₁, …, vₖ) = span(e₁, …, eₖ)` for each {lit}`k`. Axler's proof of uniqueness in
7.58 cites this exercise, so we prove it here in the main text. -/
theorem eq_gramSchmidtNormed_of_span {m : ℕ} (v : Fin m → V) (hv : LinearIndependent 𝕜 v)
    (e : Fin m → V) (he : Orthonormal 𝕜 e)
    (hpos : ∀ k, 0 < ⟪e k, v k⟫_𝕜)
    (hspan : ∀ k, Submodule.span 𝕜 (e '' {i | i ≤ k}) =
      Submodule.span 𝕜 (v '' {i | i ≤ k})) :
    e = InnerProductSpace.gramSchmidtNormed 𝕜 v := by
  -- we will proceed by induction
  -- assume ei = gram-schmidt for all i < k
  -- enough to show that there is a unique choice for ek under the conditions
  -- 1. ek is in span(v₁, …, vₖ) = span(e₁, …, eₖ₋₁, vk)
  -- 2. ek is orthogonal to e₁, …, eₖ₋₁
  -- 3. ⟨vk, ek⟩ > 0
  -- 4. ‖ek‖ = 1
  -- let W = span(e₁, …, eₖ₋₁); by 2, ek ⟂ W, and by induction (ei = fi/‖fi‖) also fk ⟂ W
  -- the Gram-Schmidt recursion gives vk = fk + w with w ∈ W
  -- by 1, ek = a vk + u with u ∈ W, so ek - a fk = a w + u
  -- this is in W and also orthogonal to W, so it is 0, i.e. ek = a fk
  -- vk = fk + w and fk ⟂ w give ⟨vk, fk⟩ = ‖fk‖², and fk ≠ 0 by linear independence of vi
  -- by 3, 0 < ⟨vk, ek⟩ = ā ‖fk‖², so a is Real and positive, which fixes the phase of a
  -- by 4, 1 = ‖ek‖ = a ‖fk‖, so a = 1/‖fk‖
  funext k
  induction k using WellFoundedLT.induction with | ind k ih
  set f := InnerProductSpace.gramSchmidt 𝕜 v k with hf
  have hf0 : f ≠ 0 := LADR.Section_6B.gramSchmidt_ne_zero_of_linearIndependent hv k
  obtain ⟨a, hea⟩ : ∃ a : 𝕜, e k = a • f := gramSchmidt_unique_step v e hspan k
    (fun i hi => by
      rw [ih i hi, InnerProductSpace.gramSchmidtNormed, inner_smul_left,
        LADR.Section_6B.gramSchmidt_orthogonal_of_lt v hi, mul_zero])
    (fun i hi => he.2 hi.ne)
  -- `⟨vₖ, fₖ⟩ = ‖fₖ‖²`, so positivity of `⟨vₖ, eₖ⟩` says `a` is a positive real `t`
  have hfv : ⟪f, v k⟫_𝕜 = ((‖f‖ ^ 2 : ℝ) : 𝕜) := by
    rw [InnerProductSpace.gramSchmidt_def' 𝕜 v k, ← hf, inner_add_right, inner_sum,
      Finset.sum_eq_zero, add_zero, inner_self_eq_norm_sq_to_K]
    · push_cast; rfl
    · intro j hj
      rw [Submodule.starProjection_singleton, inner_smul_right,
        inner_eq_zero_symm.mp (LADR.Section_6B.gramSchmidt_orthogonal_of_lt v (Finset.mem_Iio.mp hj)), mul_zero]
  have hnf : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have hp := hpos k
  rw [hea, inner_smul_left, hfv] at hp
  obtain ⟨x, hx, hxa⟩ := RCLike.pos_iff_exists_ofReal.mp hp
  have hta : a = ((x / ‖f‖ ^ 2 : ℝ) : 𝕜) := by
    have hc : (starRingEnd 𝕜) a = ((x / ‖f‖ ^ 2 : ℝ) : 𝕜) := by
      have hne : ((‖f‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (by positivity)
      rw [RCLike.ofReal_div, hxa, mul_div_cancel_right₀ _ hne]
    rw [← RCLike.conj_conj a, hc, RCLike.conj_ofReal]
  set t := x / ‖f‖ ^ 2 with ht
  have htpos : 0 < t := by positivity
  -- `‖eₖ‖ = 1` gives `t = 1/‖fₖ‖`
  have hnorm : t * ‖f‖ = 1 := by
    have h1 := he.1 k
    rw [hea, norm_smul, hta, RCLike.norm_ofReal, abs_of_pos htpos] at h1
    exact h1
  have htf : t = ‖f‖⁻¹ := eq_inv_of_mul_eq_one_left hnorm
  rw [hea, hta, htf, InnerProductSpace.gramSchmidtNormed, RCLike.ofReal_inv]



/-- Column {lit}`k` of {lit}`QR` is the linear combination of the columns of {lit}`Q` with
coefficients from column {lit}`k` of {lit}`R` (3.51(a)). -/
theorem col_mul_eq_sum {N : ℕ} (Q R : Matrix (Fin N) (Fin N) 𝕜) (k : Fin N) :
    (WithLp.toLp 2 ((Q * R).col k) : EuclideanSpace 𝕜 (Fin N)) =
      ∑ j, R j k • (WithLp.toLp 2 (Q.col j) : EuclideanSpace 𝕜 (Fin N)) := by
  ext i
  simp [Matrix.mul_apply, mul_comm]

/-- If {lit}`R` is upper triangular with nonzero diagonal, the columns {lit}`q₁, …, qₙ` of
{lit}`Q` and the columns {lit}`v₁, …, vₙ` of {lit}`QR` have the same initial spans:
{lit}`vₖ = R₁ₖq₁ + ⋯ + Rₖₖqₖ`, and conversely {lit}`qₖ` is recovered from {lit}`vₖ` and
{lit}`q₁, …, qₖ₋₁` because {lit}`Rₖₖ ≠ 0`. -/
theorem span_cols_eq_of_upperTriangular {N : ℕ} (Q R : Matrix (Fin N) (Fin N) 𝕜)
    (hRt : R.BlockTriangular id) (hRd : HasPosRealDiag R) (k : Fin N) :
    Submodule.span 𝕜 ((fun j => (WithLp.toLp 2 (Q.col j) : EuclideanSpace 𝕜 (Fin N))) ''
        {i | i ≤ k}) =
      Submodule.span 𝕜 ((fun j => (WithLp.toLp 2 ((Q * R).col j) : EuclideanSpace 𝕜 (Fin N))) ''
        {i | i ≤ k}) := by
  set q := fun j => (WithLp.toLp 2 (Q.col j) : EuclideanSpace 𝕜 (Fin N)) with hq
  set f := fun j => (WithLp.toLp 2 ((Q * R).col j) : EuclideanSpace 𝕜 (Fin N)) with hf
  -- fᵢ = ∑_{j ≤ i} R j i • q j
  have hfi : ∀ i, f i = ∑ j ∈ Finset.Iic i, R j i • q j := by
    intro i
    show WithLp.toLp 2 ((Q * R).col i) = _
    rw [col_mul_eq_sum]
    refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_).symm
    rw [Finset.mem_Iic, not_le] at hj
    rw [hRt hj, zero_smul]
  have hRne : ∀ i, R i i ≠ 0 := fun i h => by have := (hRd i).1; rw [h] at this; simp at this
  apply le_antisymm
  · -- qₖ = (R k k)⁻¹ (fₖ − ∑_{j<k} R j k qⱼ), by strong induction
    have hmem : ∀ k, q k ∈ Submodule.span 𝕜 (f '' {i | i ≤ k}) := by
      intro k
      induction k using WellFoundedLT.induction with | ind k ih
      have hsplit : f k = R k k • q k + ∑ j ∈ Finset.Iio k, R j k • q j := by
        rw [hfi, ← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
      have hqk : q k = (R k k)⁻¹ • (f k - ∑ j ∈ Finset.Iio k, R j k • q j) := by
        rw [hsplit, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ (hRne k), one_smul]
      rw [hqk]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨k, Set.mem_ofPred.mpr le_rfl, rfl⟩)
        (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_))
      have hjk : j < k := Finset.mem_Iio.mp hj
      exact Submodule.span_mono (Set.image_mono fun i (hi : i ≤ j) => le_trans hi hjk.le) (ih j hjk)
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.span_mono (Set.image_mono fun l (hl : l ≤ i) => le_trans hl hi) (hmem i)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, hfi]
    exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, le_trans (Finset.mem_Iic.mp hj) hi, rfl⟩)


/-- The columns of {lit}`A`, as vectors of {lit}`𝔽ⁿ` with the Euclidean inner product. -/
theorem linearIndependent_toLp_col {N : ℕ} {A : Matrix (Fin N) (Fin N) 𝕜}
    (hA : LinearIndependent 𝕜 A.col) :
    LinearIndependent 𝕜 fun i => (WithLp.toLp 2 (A.col i) : EuclideanSpace 𝕜 (Fin N)) :=
  hA.map' (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 𝕜 (Fin N → 𝕜)).symm.injective)

/-- The key step of Axler's uniqueness proof in 7.58: in any QR factorization of {lit}`A`,
the columns {lit}`q₁, …, qₙ` of {lit}`Q` satisfy {lit}`span(v₁, …, vₖ) = span(q₁, …, qₖ)`
and {lit}`⟨vₖ, qₖ⟩ = Rₖₖ > 0`, so by Exercise 6B.10 they are the Gram–Schmidt list of the
columns {lit}`v₁, …, vₙ` of {lit}`A`. -/
theorem cols_eq_gramSchmidtNormed {N : ℕ} (A Q R : Matrix (Fin N) (Fin N) 𝕜)
    (hA : LinearIndependent 𝕜 A.col)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin N) 𝕜) (hRt : R.BlockTriangular id)
    (hRd : HasPosRealDiag R) (hAQR : A = Q * R) :
    (fun j => (WithLp.toLp 2 (Q.col j) : EuclideanSpace 𝕜 (Fin N))) =
      InnerProductSpace.gramSchmidtNormed 𝕜
        (fun j => (WithLp.toLp 2 (A.col j) : EuclideanSpace 𝕜 (Fin N))) := by
  have hf := linearIndependent_toLp_col hA
  subst hAQR
  have horth : Orthonormal 𝕜 fun j => (WithLp.toLp 2 (Q.col j) : EuclideanSpace 𝕜 (Fin N)) :=
    ((tfae_mem_unitaryGroup Q).out 4 1).mp hQ
  refine eq_gramSchmidtNormed_of_span _ hf _ horth (fun k => ?_)
    (span_cols_eq_of_upperTriangular Q R hRt hRd)
  -- ⟨qₖ, vₖ⟩ = Rₖₖ > 0, since vₖ = ∑ⱼ Rⱼₖ qⱼ
  rw [col_mul_eq_sum, inner_sum, Finset.sum_eq_single k
    (fun j _ hjk => by rw [inner_smul_right, horth.2 (Ne.symm hjk), mul_zero])
    (fun h => absurd (Finset.mem_univ k) h), inner_smul_right,
    orthonormal_iff_ite.mp horth k k, ite_eq_left rfl, mul_one]
  exact (hasPosRealDiag_iff R).mp hRd k

/-- 7.58 QR factorization (uniqueness). Following Axler: the columns of both unitary
factors are the Gram–Schmidt list of the columns of {lit}`A`
({name}`cols_eq_gramSchmidtNormed`), so {lit}`Q₁ = Q₂`, and then
{lit}`R₁ = Q₁* A = Q₂* A = R₂`. -/
@[avoiding Matrix.blockTriangular_inv_of_blockTriangular, Matrix.det_of_isUpperTriangular]
theorem QR_unique {N : ℕ} (A Q₁ R₁ Q₂ R₂ : Matrix (Fin N) (Fin N) 𝕜)
    (hA : LinearIndependent 𝕜 A.col)
    (hQ₁ : Q₁ ∈ Matrix.unitaryGroup (Fin N) 𝕜) (hR₁t : R₁.BlockTriangular id)
    (hR₁d : HasPosRealDiag R₁) (hA₁ : A = Q₁ * R₁)
    (hQ₂ : Q₂ ∈ Matrix.unitaryGroup (Fin N) 𝕜) (hR₂t : R₂.BlockTriangular id)
    (hR₂d : HasPosRealDiag R₂) (hA₂ : A = Q₂ * R₂) :
    Q₁ = Q₂ ∧ R₁ = R₂ := by
  have h := (cols_eq_gramSchmidtNormed A Q₁ R₁ hA hQ₁ hR₁t hR₁d hA₁).trans
    (cols_eq_gramSchmidtNormed A Q₂ R₂ hA hQ₂ hR₂t hR₂d hA₂).symm
  have hQ : Q₁ = Q₂ := by
    ext i j
    simpa using congrArg (fun g => g j i) h
  refine ⟨hQ, ?_⟩
  have hR : ∀ Q R : Matrix (Fin N) (Fin N) 𝕜, Q ∈ Matrix.unitaryGroup (Fin N) 𝕜 →
      A = Q * R → R = Qᴴ * A := fun Q R hQ h => by
    rw [h, ← Matrix.mul_assoc, ((mem_unitaryGroup_iff_conjTranspose Q).mp hQ).1, Matrix.one_mul]
  rw [hR Q₁ R₁ hQ₁ hA₁, hR Q₂ R₂ hQ₂ hA₂, hQ]


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
  obtain ⟨hQeq, hReq⟩ := QR_unique A Q' R' Q R hA hQ' hR't hR'd hAQR' hQ hRt hRd hAQR
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
  · -- the columns of `Q` are orthonormal, so `Q` is unitary (7.57)
    refine ((tfae_mem_unitaryGroup _).out 1 4).mp ((orthonormal_columns_iff _).mpr ?_)
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
{lit}`⟨T v, v⟩ > 0` for every nonzero {lit}`v`. We write "invertible" as "injective",
which on a finite-dimensional space is the same thing (3.65).

Axler's proof: if {lit}`T` is positive and invertible and {lit}`v ≠ 0`, then
{lit}`T v ≠ 0`, so {lit}`⟨T v, v⟩ ≠ 0` by 7.43, and it is {lit}`≥ 0` because {lit}`T` is
positive. Conversely, {lit}`⟨T v, v⟩ > 0` for {lit}`v ≠ 0` makes {lit}`T` positive and
forces {lit}`T v ≠ 0`, so {lit}`T` is injective. -/

theorem positive_invertible_iff {T : V →ₗ[𝕜] V} (hT : T.IsSymmetric) :
    (T.IsPositive ∧ Function.Injective T) ↔ ∀ v : V, v ≠ 0 → 0 < RCLike.re ⟪T v, v⟫_𝕜 := by
  -- ⟨T v, v⟩ is real because T is self-adjoint
  have hreal : ∀ v, ((RCLike.re ⟪T v, v⟫_𝕜 : ℝ) : 𝕜) = ⟪T v, v⟫_𝕜 := fun v =>
    RCLike.conj_eq_iff_re.mp (by rw [inner_conj_symm, hT])
  constructor
  · rintro ⟨hpos, hinj⟩ v hv
    have hTv : T v ≠ 0 := fun h => hv (hinj (h.trans (map_zero T).symm))
    have hne : RCLike.re ⟪T v, v⟫_𝕜 ≠ 0 := fun h => hTv
      (LADR.Section_7C.apply_eq_zero_of_isPositive_of_inner_eq_zero hpos
        (by rw [← hreal, h, RCLike.ofReal_zero]))
    exact lt_of_le_of_ne (hpos.2 v) (Ne.symm hne)
  · intro h
    refine ⟨⟨hT, fun v => ?_⟩, ?_⟩
    · rcases eq_or_ne v 0 with rfl | hv
      · simp
      · exact (h v hv).le
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      by_contra hv0
      have := h v hv0
      rw [hv, inner_zero_left, map_zero] at this
      exact lt_irrefl 0 this

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
/-- Definition 7.62 in operator language: {lit}`B` is positive definite iff the operator
{lit}`x ↦ B x` on {lit}`𝔽ⁿ` is self-adjoint with {lit}`⟨B x, x⟩ > 0` for {lit}`x ≠ 0`. -/
theorem posDef_iff_toEuclideanLin {N : ℕ} (B : Matrix (Fin N) (Fin N) 𝕜) :
    B.PosDef ↔ B.toEuclideanLin.IsSymmetric ∧
      ∀ x : EuclideanSpace 𝕜 (Fin N), x ≠ 0 → 0 < RCLike.re ⟪B.toEuclideanLin x, x⟫_𝕜 := by
  rw [Matrix.posDef_iff_dotProduct_mulVec, ← Matrix.isSymmetric_toEuclideanLin_iff]
  refine and_congr_right fun hsym => ?_
  -- ⟨B x, x⟩ = ⟨x, B x⟩ = xᴴ B x, and it is real
  have hq : ∀ x : EuclideanSpace 𝕜 (Fin N),
      ⟪B.toEuclideanLin x, x⟫_𝕜 = star (WithLp.ofLp x) ⬝ᵥ (B *ᵥ WithLp.ofLp x) := by
    intro x
    rw [hsym]
    simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct, Matrix.toLpLin_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have him : ∀ x : EuclideanSpace 𝕜 (Fin N), RCLike.im ⟪B.toEuclideanLin x, x⟫_𝕜 = 0 := by
    intro x
    have hreal : ((RCLike.re ⟪B.toEuclideanLin x, x⟫_𝕜 : ℝ) : 𝕜) = ⟪B.toEuclideanLin x, x⟫_𝕜 :=
      RCLike.conj_eq_iff_re.mp (by rw [inner_conj_symm, hsym])
    rw [← hreal, RCLike.ofReal_im]
  constructor
  · intro h x hx
    have := h (x := WithLp.ofLp x) (fun h0 => hx (by simpa using congrArg (WithLp.toLp 2) h0))
    rw [hq]
    exact (RCLike.pos_iff.mp this).1
  · intro h x hx
    have h1 := h (WithLp.toLp 2 x) (fun h0 => hx (by simpa using congrArg WithLp.ofLp h0))
    have h2 := him (WithLp.toLp 2 x)
    rw [hq, WithLp.ofLp_toLp] at h1 h2
    exact RCLike.pos_iff.mpr ⟨h1, h2⟩

open scoped ComplexOrder in
/-- A positive definite matrix is invertible: by 7.61 the operator {lit}`x ↦ B x` is
injective. -/
theorem PosDef.mulVec_injective {N : ℕ} {B : Matrix (Fin N) (Fin N) 𝕜} (hB : B.PosDef) :
    Function.Injective B.mulVec := by
  obtain ⟨hsym, hpos⟩ := (posDef_iff_toEuclideanLin B).mp hB
  have h := ((positive_invertible_iff hsym).mpr hpos).2
  intro x y hxy
  have := @h (WithLp.toLp 2 x) (WithLp.toLp 2 y) (by simp [Matrix.toLpLin_apply, hxy])
  simpa using congrArg WithLp.ofLp this

open scoped ComplexOrder in
/-- 7.63 Cholesky factorization (existence). Every positive definite matrix {lit}`B`
factors as {lit}`B = Rᴴ * R` with {lit}`R` upper triangular and positive real diagonal.
Following Axler: {lit}`B` is a positive invertible operator (7.61), so its positive square
root supplies an invertible {lit}`A` with {lit}`Aᴴ * A = B` (7.38); a QR factorization
{lit}`A = Q * R` (7.58) then gives `B = Rᴴ * Qᴴ * Q * R = Rᴴ * R`. -/
@[avoiding Matrix.isPositive_toEuclideanLin_iff, Matrix.PosDef.isUnit]
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
  -- `Bop = toEuclideanLin B` is a positive invertible operator (7.61).
  obtain ⟨hBsym, hBq⟩ := (posDef_iff_toEuclideanLin B).mp hB
  obtain ⟨hBoppos, hBopinj⟩ := (positive_invertible_iff hBsym).mpr hBq
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
  have hQuni : Qᴴ * Q = 1 := ((mem_unitaryGroup_iff_conjTranspose Q).mp hQ).1
  rw [← hAA, hAQR, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ Q R,
    hQuni, Matrix.one_mul]

open scoped ComplexOrder in
/-- 7.63 Cholesky factorization (uniqueness). Following Axler: if {lit}`B = Aᴴ A` with
{lit}`A` invertible (here {lit}`A = R₁`) and {lit}`B = Sᴴ S` with {lit}`S = R₂` upper
triangular with positive diagonal, then {lit}`S` is invertible because {lit}`B` is
(Exercise 3D.11), {lit}`A S⁻¹` is unitary because
{lit}`(A S⁻¹)ᴴ (A S⁻¹) = (Sᴴ)⁻¹ B S⁻¹ = I`, and {lit}`A = (A S⁻¹) S` is a QR factorization of
{lit}`A`; uniqueness of the QR factorization (7.58) gives {lit}`S = R₁`. -/
@[avoiding Matrix.blockTriangular_inv_of_blockTriangular, Matrix.det_of_isUpperTriangular]
theorem cholesky_unique {N : ℕ} (B R₁ R₂ : Matrix (Fin N) (Fin N) 𝕜) (hB : B.PosDef)
    (hR₁t : R₁.BlockTriangular id)
    (hR₁d : HasPosRealDiag R₁) (hB₁ : B = R₁ᴴ * R₁)
    (hR₂t : R₂.BlockTriangular id)
    (hR₂d : HasPosRealDiag R₂) (hB₂ : B = R₂ᴴ * R₂) :
    R₁ = R₂ := by
  -- `B` is invertible (7.61), hence so is any `R` with `B = Rᴴ R` (Exercise 3D.11)
  have hRinj : ∀ R : Matrix (Fin N) (Fin N) 𝕜, B = Rᴴ * R → Function.Injective R.mulVec :=
    fun R hR x y hxy => hB.mulVec_injective (by rw [hR, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hxy])
  have hR₁ind : LinearIndependent 𝕜 R₁.col := Matrix.linearIndependent_col_iff_isUnit.mpr
    (Matrix.mulVec_injective_iff_isUnit.mp (hRinj R₁ hB₁))
  have hR₂u : IsUnit R₂.det := (Matrix.isUnit_iff_isUnit_det R₂).mp
    (Matrix.mulVec_injective_iff_isUnit.mp (hRinj R₂ hB₂))
  -- `U = R₁ R₂⁻¹` is unitary and `R₁ = U R₂`
  set U := R₁ * R₂⁻¹ with hUdef
  have hUR : U * R₂ = R₁ := by
    rw [hUdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hR₂u, Matrix.mul_one]
  have hUU : Uᴴ * U = 1 := by
    calc Uᴴ * U = (R₂⁻¹)ᴴ * (R₁ᴴ * R₁) * R₂⁻¹ := by
          rw [hUdef, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (R₂ * R₂⁻¹)ᴴ * (R₂ * R₂⁻¹) := by
          rw [← hB₁, hB₂, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hR₂u, Matrix.conjTranspose_one, Matrix.one_mul]
  have hU : U ∈ Matrix.unitaryGroup (Fin N) 𝕜 :=
    ((tfae_mem_unitaryGroup U).out 1 4).mp ((orthonormal_columns_iff U).mpr hUU)
  -- `R₁ = I R₁ = U R₂` are two QR factorizations of `R₁`
  exact (QR_unique R₁ 1 R₁ U R₂ hR₁ind (one_mem _) hR₁t hR₁d (Matrix.one_mul R₁).symm
    hU hR₂t hR₂d hUR.symm).2

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
  exact cholesky_unique B R' R hB hR't hR'd hBR' hRt hRd hBR

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

/-- 7D.3(b) The inverse of a unitary operator is unitary.

The book says {lit}`S⁻¹`; we say {lit}`S*`. These name the same operator: a unitary
{lit}`S` is invertible with {lit}`S⁻¹ = S*`, since {lit}`S* S = S S* = I`
({name}`mem_unitary_inverse`, which is 7.53(c)). Stating the exercise for
{lit}`S*` avoids wrapping it in a {lit}`V ≃ₗ[𝕜] V` or {name}`Ring.inverse` just to
name the inverse, and loses nothing: {lit}`S*` *is* the inverse whose unitarity the
exercise asks about. -/
theorem exercise_7D_3b {S : V →ₗ[𝕜] V} (hS : S ∈ unitary (V →ₗ[𝕜] V)) :
    S† ∈ unitary (V →ₗ[𝕜] V) := by
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
      ∃ P : V →ₗ[𝕜] V, P† = P ∧ P ∘ₗ P = P ∧ S = 2 • P - 1,
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
        T₁ = S† ∘ₗ T₂ ∘ₗ S := by
  sorry

/-- 7D.7 The student supplies two operators on {lit}`𝔽⁴` (replacing the
{lit}`sorry`s), both self-adjoint with eigenvalues {lit}`2, 5, 7`, that are *not*
unitarily equivalent. The exercise asks for an example, so the witnesses are answers
in their own right rather than an existential to be discharged. -/
noncomputable def exercise_7D_7_T₁ :
    EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4) := sorry

/-- The second witness operator for 7D.7. -/
noncomputable def exercise_7D_7_T₂ :
    EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4) := sorry

theorem exercise_7D_7_isSymmetric_T₁ :
    LinearMap.IsSymmetric (exercise_7D_7_T₁ (𝕜 := 𝕜)) := by sorry

theorem exercise_7D_7_isSymmetric_T₂ :
    LinearMap.IsSymmetric (exercise_7D_7_T₂ (𝕜 := 𝕜)) := by sorry

theorem exercise_7D_7_eigenvalues_T₁ (μ : 𝕜) :
    HasEigenvalue exercise_7D_7_T₁ μ ↔ μ = 2 ∨ μ = 5 ∨ μ = 7 := by sorry

theorem exercise_7D_7_eigenvalues_T₂ (μ : 𝕜) :
    HasEigenvalue exercise_7D_7_T₂ μ ↔ μ = 2 ∨ μ = 5 ∨ μ = 7 := by sorry

/-- 7D.7 The content of the exercise: the two operators above are not unitarily
equivalent, even though they are self-adjoint with the same eigenvalues (so the
converse of 7D.6 fails once an eigenvalue can repeat — {lit}`dim = 4` with three
eigenvalues leaves the multiplicities free). -/
theorem exercise_7D_7 :
    ¬ ∃ S : EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4),
      S ∈ unitary (EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 4)) ∧
        exercise_7D_7_T₁ = S† ∘ₗ exercise_7D_7_T₂ ∘ₗ S := by
  sorry

/-- 7D.8 *Prove or counterexample.* If {lit}`S ∈ ℒ(V)` and there is an orthonormal
basis {lit}`e₁, …, eₙ` of {lit}`V` with {lit}`‖S eₖ‖ = 1` for each {lit}`eₖ`, is
{lit}`S` unitary? The space is quantified inside the proposition, since a
counterexample is allowed to choose it. -/
def exercise_7D_8 :
    Decidable (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
      [FiniteDimensional 𝕜 E] (S : E →ₗ[𝕜] E) (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 E),
      (∀ k, ‖S (e k)‖ = 1) → S ∈ unitary (E →ₗ[𝕜] E)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
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

/-- 7D.12 *Prove or counterexample.* If {lit}`S ∈ ℒ(V)` is invertible and
{lit}`‖S⁻¹ v‖ = ‖S v‖` for every {lit}`v`, is {lit}`S` unitary? As in 7D.8 the space
is quantified inside the proposition, since a counterexample may choose it. -/
def exercise_7D_12 :
    Decidable (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
      [FiniteDimensional 𝕜 E] (S : E ≃ₗ[𝕜] E), (∀ v, ‖S.symm v‖ = ‖S v‖) →
      (S : E →ₗ[𝕜] E) ∈ unitary (E →ₗ[𝕜] E)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 7D.13 For a square matrix, the columns form an orthonormal list in {lit}`𝔽ⁿ` if and
only if the rows do. Rows and columns are read as vectors of {lit}`EuclideanSpace` —
that is where "orthonormal" gets its inner product — using {name}`Matrix.col` and
{name}`Matrix.row`. Under the hood this is {lit}`Qᴴ Q = I ⟺ Q Qᴴ = I`, the exchange
that lets {name}`Matrix.unitaryGroup` be defined by either equation and that condition
(e) of 7.53 relies on. -/
theorem exercise_7D_13 {n : Type*} [Fintype n] [DecidableEq n] (Q : Matrix n n 𝕜) :
    Orthonormal 𝕜 (fun j => (WithLp.toLp 2 (Q.col j) : EuclideanSpace 𝕜 n)) ↔
      Orthonormal 𝕜 (fun i => (WithLp.toLp 2 (Q.row i) : EuclideanSpace 𝕜 n)) := by
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
    ((T + 1) ∘ₗ Tinv)† = -((T + 1) ∘ₗ Tinv) := by
  sorry

/-- 7D.15 (b) Over {lit}`ℂ`, {lit}`i(T + I)(T − I)⁻¹` is self-adjoint. -/
theorem exercise_7D_15b {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T ∈ unitary (E →ₗ[ℂ] E)) (Tinv : E →ₗ[ℂ] E)
    (hi1 : Tinv ∘ₗ (T - 1) = 1) (hi2 : (T - 1) ∘ₗ Tinv = 1) :
    LinearMap.IsSymmetric (Complex.I • ((T + 1) ∘ₗ Tinv)) := by
  sorry

/-- 7D.16 (first step) Over {lit}`ℂ`, for self-adjoint {lit}`T` the operator
{lit}`T − iI` is invertible. Axler does not state this as a hypothesis — unlike 7D.15,
where {lit}`T − I` invertible is a genuine restriction on the unitary {lit}`T` (take
{lit}`T = I`) — because here it is a consequence: {lit}`i` is not an eigenvalue of a
self-adjoint operator, since every eigenvalue is real
({name}`LADR.Section_7A.eigenvalue_real`), and injective is invertible in finite
dimensions. Alternatively {lit}`(T + iI)(T − iI) = T² + I` is invertible by 7.26
({name}`LADR.Section_7B.quadratic_isInvertible` with {lit}`b = 0`, {lit}`c = 1`), so both
factors are. Prove this before 7D.16, which presupposes it by writing
{lit}`(T − iI)⁻¹`. -/
theorem exercise_7D_16_isUnit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : LinearMap.IsSymmetric T) :
    IsUnit (T - Complex.I • (1 : E →ₗ[ℂ] E)) := by
  sorry

/-- 7D.16 Over {lit}`ℂ`, for self-adjoint {lit}`T`, {lit}`(T + iI)(T − iI)⁻¹` is
unitary and {lit}`1` is not an eigenvalue of it. The inverse is spelled with
{name}`Ring.inverse` on the ring {lit}`ℒ(E)` (composition as multiplication), so the
statement assumes no inverse of its own: it exists by
{name}`exercise_7D_16_isUnit`. -/
theorem exercise_7D_16 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : LinearMap.IsSymmetric T) :
    (T + Complex.I • 1) * Ring.inverse (T - Complex.I • (1 : E →ₗ[ℂ] E)) ∈
        unitary (E →ₗ[ℂ] E) ∧
      ¬ HasEigenvalue ((T + Complex.I • 1) *
        Ring.inverse (T - Complex.I • (1 : E →ₗ[ℂ] E))) 1 := by
  sorry

/-! 7D.17 asks to explain why the characterizations of unitary matrices in 7.57 hold. It is
a straightforward application of 7D.13 — the columns-versus-rows exchange
{lit}`Q* Q = I ⟺ Q Q* = I` is the only ingredient not already in the text — so no separate
statement is left here: 7.57 is proved above as
{name}`LADR.Section_7D.tfae_mem_unitaryGroup`, and the exchange itself is
{name}`LADR.Section_7D.exercise_7D_13`. -/

/-- 7D.18 A real symmetric matrix is orthogonally diagonalizable: there is a real
unitary {lit}`Q` with {lit}`Q* A Q` diagonal. -/
theorem exercise_7D_18 {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.transpose = A) :
    ∃ Q : Matrix n n ℝ, Q ∈ Matrix.unitaryGroup n ℝ ∧ Matrix.IsDiag (Qᴴ * A * Q) := by
  sorry

/-- The discrete Fourier transform of 7D.19:
{lit}`(ℱ z)ⱼ = n^(-1/2) ∑ₘ zₘ e^(−2πijm/n)`, with {lit}`ℂⁿ` indexed by
{lit}`0, …, n−1` as Axler does. Extracted as a predicate because 7D.19 has three parts
about the same operator. -/
def IsDFT {n : ℕ} (F : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) : Prop :=
  ∀ (z : EuclideanSpace ℂ (Fin n)) (j : Fin n),
    F z j = (1 / Real.sqrt n : ℂ) *
      ∑ m : Fin n, z m *
        Complex.exp (-2 * Real.pi * Complex.I * (j : ℂ) * (m : ℂ) / (n : ℂ))

/-- 7D.19 (a) The discrete Fourier transform {lit}`ℱ` on {lit}`ℂⁿ` is a unitary
operator. -/
theorem exercise_7D_19a {n : ℕ} (hn : 0 < n)
    (F : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (hF : IsDFT F) :
    F ∈ unitary (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
  sorry

/-- 7D.19 (b) {lit}`ℱ⁻¹(z₀, …, z_{n−1}) = ℱ(zₙ, z_{n−1}, …, z₁)` where {lit}`zₙ = z₀`.
The reversal is {lit}`j ↦ z (-j)` in {lit}`Fin n` arithmetic
({name}`Fin.instInvolutiveNeg`), which is {lit}`z 0 = zₙ` at {lit}`j = 0` and
{lit}`z (n − j)` otherwise — exactly Axler's list. The inverse exists by (a) and is
spelled with {name}`Ring.inverse` on the ring {lit}`ℒ(ℂⁿ)`, so the statement needs no
inverse hypothesis of its own. -/
theorem exercise_7D_19b {n : ℕ} (hn : 0 < n)
    (F : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (hF : IsDFT F)
    (z : EuclideanSpace ℂ (Fin n)) :
    Ring.inverse F z = F (WithLp.toLp 2 fun j => z (-j)) := by
  sorry

/-- 7D.19 (c) {lit}`ℱ⁴ = I`. -/
theorem exercise_7D_19c {n : ℕ} (hn : 0 < n)
    (F : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) (hF : IsDFT F) :
    F ∘ₗ F ∘ₗ F ∘ₗ F = 1 := by
  sorry

/-- 7D.20 A square matrix with linearly independent columns has unique matrices
{lit}`R` lower triangular with only positive numbers on its diagonal and {lit}`Q`
unitary with {lit}`A = RQ` (the {lit}`RQ` variant of 7.58).

*Why {lit}`BlockTriangular OrderDual.toDual` is "lower triangular".* Everywhere else in
this file triangularity is {lit}`BlockTriangular id`; this is the one place the index map
is not {lit}`id`. Unfolding {name}`Matrix.BlockTriangular`, {lit}`M.BlockTriangular b`
means {lit}`∀ i j, b j < b i → M i j = 0`. Taking {lit}`b = id` gives
{lit}`j < i → M i j = 0`: the entries strictly *below* the diagonal vanish, i.e. upper
triangular. Taking {lit}`b = OrderDual.toDual` reverses the order —
{lit}`toDual j < toDual i ↔ i < j` ({name}`OrderDual.toDual_lt_toDual`) — so the condition
becomes {lit}`i < j → M i j = 0`: the entries strictly *above* the diagonal vanish, i.e.
lower triangular. This is the same spelling mathlib uses in
{name}`Matrix.det_of_lowerTriangular`. -/
theorem exercise_7D_20 {N : ℕ} (A : Matrix (Fin N) (Fin N) 𝕜)
    (hA : LinearIndependent 𝕜 A.col) :
    ∃! RQ : Matrix (Fin N) (Fin N) 𝕜 × Matrix (Fin N) (Fin N) 𝕜,
      RQ.1.BlockTriangular OrderDual.toDual ∧
        HasPosRealDiag RQ.1 ∧
        RQ.2 ∈ Matrix.unitaryGroup (Fin N) 𝕜 ∧ A = RQ.1 * RQ.2 := by
  sorry

end LADR.Section_7D
