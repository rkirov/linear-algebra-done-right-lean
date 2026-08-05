import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linter.Style
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_7C
import LinearAlgebraDoneRightLean.Section_7D
import LinearAlgebraDoneRightLean.Section_7E
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 9C: Determinants
-/

namespace LADR.Section_9C

open Module (Finite finrank)
open Module.End (HasEigenvalue)
open LADR.Section_3D (IsInvertible)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! 9.43 Definition: determinant of a matrix, {lit}`det A`.

Axler defines {lit}`det A` for a square matrix {lit}`A` as {lit}`det T`, where
{lit}`T ∈ ℒ(Fⁿ)` is the operator whose matrix with respect to the standard basis
of {lit}`Fⁿ` equals {lit}`A`. mathlib takes the matrix determinant
{name}`Matrix.det` as primitive and proves the equivalence with the operator
determinant {name}`LinearMap.det`: the operator {lit}`T = Matrix.toLin' A`
associated to {lit}`A` via the standard basis has {lit}`det T = det A`
({name}`LinearMap.det_toLin'`). -/

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    A.det = LinearMap.det (Matrix.toLin' A) :=
  (LinearMap.det_toLin' A).symm

/-! 9.44 Example: determinants of matrices.

The determinant of the identity matrix is {lit}`1` ({name}`Matrix.det_one`), and
the determinant of a diagonal matrix with {lit}`λ₁, …, λₙ` on the diagonal is the
product {lit}`λ₁ ⋯ λₙ` ({name}`Matrix.det_diagonal`) — matching the first and
last bullet points of 9.42 applied to the associated operator. -/

example {n : ℕ} : (1 : Matrix (Fin n) (Fin n) F).det = 1 := Matrix.det_one

example {n : ℕ} (d : Fin n → F) :
    (Matrix.diagonal d).det = ∏ i, d i := Matrix.det_diagonal

/-! 9.45 Determinant is an alternating multilinear form.

The map taking a list of {lit}`n` vectors in {lit}`Fⁿ` (the rows of a matrix,
or, via the transpose, the columns) to the determinant is an alternating
{lit}`n`-linear form. In mathlib this alternating form *is* the definition of the
determinant: {name}`Matrix.detRowAlternating` is an
{lit}`AlternatingMap` (which packages both multilinearity and the alternating
property), and {name}`Matrix.det` is its underlying function. -/

example {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    (Matrix.detRowAlternating : (Fin n → F) [⋀^Fin n]→ₗ[F] F) M = M.det := rfl

/-! 9.46 Formula for determinant of a matrix.

{lit}`det A = ∑_{σ ∈ perm n} (sign σ) A_{σ(1),1} ⋯ A_{σ(n),n}`
({name}`Matrix.det_apply`). -/

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    A.det = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i :=
  Matrix.det_apply A

/-! 9.47 Example: explicit formula for the determinant of a {lit}`2×2` and a
{lit}`3×3` matrix. -/

example (A : Matrix (Fin 2) (Fin 2) F) :
    A.det = A 0 0 * A 1 1 - A 1 0 * A 0 1 := by
  rw [Matrix.det_fin_two]; ring

example (A : Matrix (Fin 3) (Fin 3) F) :
    A.det =
      A 0 0 * A 1 1 * A 2 2 - A 1 0 * A 0 1 * A 2 2 - A 2 0 * A 1 1 * A 0 2
      - A 0 0 * A 2 1 * A 1 2 + A 2 0 * A 0 1 * A 1 2 + A 1 0 * A 2 1 * A 0 2 := by
  rw [Matrix.det_fin_three]; ring

/-! 9.48 Determinant of an upper-triangular matrix equals the product of its
diagonal entries. -/

theorem det_of_upperTriangular {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (h : M.BlockTriangular id) : M.det = ∏ i, M i i :=
  Matrix.det_of_upperTriangular h

/-! 9.49 Determinant is multiplicative.

(a) For operators {lit}`S, T ∈ ℒ(V)`: {lit}`det(ST) = (det S)(det T)`
({name}`LinearMap.det_comp`, using {lit}`ST = S ∘ₗ T`).

(b) For square matrices of the same size: {lit}`det(AB) = (det A)(det B)`
({name}`Matrix.det_mul`). -/

theorem det_comp_operator (S T : V →ₗ[F] V) :
    LinearMap.det (S ∘ₗ T) = LinearMap.det S * LinearMap.det T :=
  LinearMap.det_comp S T

theorem det_mul_matrix {n : ℕ} (A B : Matrix (Fin n) (Fin n) F) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

/-! 9.50 An operator is invertible if and only if its determinant is nonzero;
furthermore {lit}`det(T⁻¹) = 1 / det T`. Here invertibility is Axler's
two-sided-inverse notion {name}`LADR.Section_3D.IsInvertible`. -/

theorem isInvertible_iff_det_ne_zero [Finite F V] (T : V →ₗ[F] V) :
    IsInvertible T ↔ LinearMap.det T ≠ 0 := by
  constructor
  · rintro ⟨S, hST, -⟩
    -- {lit}`det S · det T = det(S ∘ₗ T) = det I = 1`, so {lit}`det T ≠ 0`.
    have h : LinearMap.det S * LinearMap.det T = 1 := by
      rw [← LinearMap.det_comp, hST, LinearMap.det_id]
    intro hd
    rw [hd, mul_zero] at h
    exact one_ne_zero h.symm
  · intro hd
    -- {lit}`det T ≠ 0` forces {lit}`ker T = ⊥`, hence injectivity, hence (3.65)
    -- bijectivity, hence invertibility.
    have hker : LinearMap.ker T = ⊥ := by
      by_contra h
      exact hd (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
    have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hker
    have hbij : Function.Bijective T :=
      ⟨hinj, (LADR.Section_3D.injective_iff_surjective rfl T).mp hinj⟩
    exact LADR.Section_3D.isInvertible_of_bijective T hbij

theorem det_inv_eq_inv_det [Finite F V] {T : V →ₗ[F] V} (h : IsInvertible T) :
    LinearMap.det h.inv = (LinearMap.det T)⁻¹ := by
  have h1 : LinearMap.det T * LinearMap.det h.inv = 1 := by
    rw [← LinearMap.det_comp, h.comp_inv, LinearMap.det_id]
  exact eq_inv_of_mul_eq_one_right h1

/-! 9.51 Eigenvalues and determinants: {lit}`λ` is an eigenvalue of {lit}`T` if
and only if {lit}`det(λI − T) = 0`.

We route through the fact that {lit}`λ` is an eigenvalue iff it is a root of the
characteristic polynomial ({name}`Module.End.hasEigenvalue_iff_isRoot_charpoly`)
together with {name}`LinearMap.eval_charpoly`, which evaluates the characteristic
polynomial at {lit}`λ` as {lit}`det(λI − T)`. -/

theorem hasEigenvalue_iff_det_eq_zero [Finite F V] (T : V →ₗ[F] V) (γ : F) :
    HasEigenvalue T γ ↔ LinearMap.det (γ • LinearMap.id - T) = 0 := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Polynomial.IsRoot.def,
    LinearMap.eval_charpoly, ← Module.algebraMap_end_eq_smul_id]

/-! 9.52 Determinant is a similarity invariant: if {lit}`T ∈ ℒ(V)` and
{lit}`S : W → V` is an invertible linear map, then {lit}`det(S⁻¹TS) = det T`.

We phrase {lit}`S⁻¹` as an isomorphism {lit}`e : V ≃ W` (so {lit}`e` plays the
role of {lit}`S⁻¹` and {lit}`e.symm` the role of {lit}`S`); mathlib's
{name}`LinearMap.det_conj` then gives the result, which is valid even when
{lit}`W ≠ V`. -/

theorem det_conj_eq {W : Type*} [AddCommGroup W] [Module F W]
    (T : V →ₗ[F] V) (e : V ≃ₗ[F] W) :
    LinearMap.det ((e : V →ₗ[F] W) ∘ₗ T ∘ₗ (e.symm : W →ₗ[F] V)) = LinearMap.det T :=
  LinearMap.det_conj T e

/-! 9.53 Determinant of an operator equals the determinant of its matrix with
respect to any basis: {lit}`det T = det ℳ(T, (e₁, …, eₙ))`
({name}`LinearMap.det_toMatrix`). -/

theorem det_eq_det_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F V) (T : V →ₗ[F] V) :
    LinearMap.det T = (LinearMap.toMatrix b b T).det :=
  (LinearMap.det_toMatrix b T).symm

/-! 9.55 If {lit}`F = ℂ`, then {lit}`det T` equals the product of the eigenvalues
of {lit}`T`, each included as many times as its multiplicity. The eigenvalues
with multiplicity are exactly the roots of the characteristic polynomial (a
degree-{lit}`dim V` polynomial that splits over {lit}`ℂ`). -/

theorem det_eq_prod_eigenvalues {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    LinearMap.det T = (LinearMap.charpoly T).roots.prod := by
  classical
  rw [← LinearMap.det_toMatrix (Module.Free.chooseBasis ℂ V) T,
    Matrix.det_eq_prod_roots_charpoly, ← LinearMap.charpoly_def]

/-! 9.56 Determinant of transpose, dual, or adjoint.

(a) For a square matrix, {lit}`det Aᵗ = det A` ({name}`Matrix.det_transpose`).

(b) For an operator, {lit}`det T' = det T` where {lit}`T'` is the dual (transpose)
map ({name}`LinearMap.det_dualMap`). -/

theorem det_transpose_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    A.transpose.det = A.det :=
  Matrix.det_transpose A

theorem det_dualMap_eq [Finite F V] (T : V →ₗ[F] V) :
    LinearMap.det T.dualMap = LinearMap.det T :=
  LinearMap.det_dualMap T

/-! 9.56 (c) {lit}`det(T*) = conj(det T)` for an operator on an inner-product
space. -/

section InnerProductDet

open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- 9.56 (c) The determinant of the adjoint is the conjugate of the determinant.
Following Axler: in an orthonormal basis the matrix of {lit}`T*` is the conjugate
transpose of the matrix of {lit}`T` ({name}`LinearMap.toMatrix_adjoint`), so the
result follows from part (a) via {name}`Matrix.det_conjTranspose`. -/
theorem det_adjoint_eq_conj (T : E →ₗ[𝕜] E) :
    LinearMap.det (LinearMap.adjoint T) = conj (LinearMap.det T) := by
  classical
  let b := stdOrthonormalBasis 𝕜 E
  rw [← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint T),
    LinearMap.toMatrix_adjoint b b T, Matrix.det_conjTranspose,
    ← LinearMap.det_toMatrix b.toBasis T]
  rfl

end InnerProductDet

/-! 9.57 Helpful results in evaluating determinants. All follow from the fact
that the determinant is an alternating multilinear form in the columns (9.45)
and rows (9.56(a)). -/

/-- 9.57 (a) If two columns of a square matrix are equal, its determinant is
{lit}`0` (and likewise for two equal rows). -/
theorem det_eq_zero_of_column_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    {i j : Fin n} (h : i ≠ j) (hcol : ∀ k, M k i = M k j) : M.det = 0 :=
  Matrix.det_zero_of_column_eq h hcol

theorem det_eq_zero_of_row_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    {i j : Fin n} (h : i ≠ j) (hrow : M i = M j) : M.det = 0 :=
  Matrix.det_zero_of_row_eq h hrow

/-- 9.57 (b) Swapping two rows negates the determinant (and likewise columns). -/
theorem det_swap_rows {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    {i j : Fin n} (h : i ≠ j) :
    (M.submatrix (Equiv.swap i j) id).det = - M.det := by
  rw [Matrix.det_permute, Equiv.Perm.sign_swap h]
  simp

/-- 9.57 (c) Multiplying one row by a scalar {lit}`s` multiplies the determinant
by {lit}`s`. -/
theorem det_row_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i : Fin n) (s : F) :
    (M.updateRow i (s • M i)).det = s * M.det := by
  rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

/-- 9.57 (d) Adding a scalar multiple of one column to another leaves the
determinant unchanged. -/
theorem det_updateCol_add_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    {i j : Fin n} (h : i ≠ j) (c : F) :
    (A.updateCol i fun k => A k i + c • A k j).det = A.det :=
  Matrix.det_updateCol_add_smul_self A h c

/-- 9.57 (e) Adding a scalar multiple of one row to another leaves the
determinant unchanged. -/
theorem det_updateRow_add_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    {i j : Fin n} (h : i ≠ j) (c : F) :
    (A.updateRow i (A i + c • A j)).det = A.det :=
  Matrix.det_updateRow_add_smul_self A h c

section InnerProductDetOps

open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- 9.58 Every unitary operator has determinant with absolute value {lit}`1`.
Following Axler: {lit}`S* S = I` (7.53), so {lit}`conj(det S)·det S = det(S*)·det S
= det(S* S) = 1` using 9.56(c) ({name}`det_adjoint_eq_conj`); taking norms gives
{lit}`‖det S‖² = 1`. -/
theorem det_unitary_norm_eq_one {S : E →ₗ[𝕜] E} (h : LADR.Section_7D.IsUnitary S) :
    ‖LinearMap.det S‖ = 1 := by
  have hSS : LinearMap.adjoint S ∘ₗ S = 1 :=
    ((LADR.Section_7D.isUnitary_iff_adjoint S).mp h).1
  have hdet : conj (LinearMap.det S) * LinearMap.det S = 1 := by
    rw [← det_adjoint_eq_conj, ← LinearMap.det_comp, hSS, Module.End.one_eq_id,
      LinearMap.det_id]
  have hnorm := congrArg norm hdet
  rw [norm_mul, RCLike.norm_conj, norm_one] at hnorm
  nlinarith [norm_nonneg (LinearMap.det S)]

/-- 9.59 Every positive operator has nonnegative determinant. Following Axler:
a positive {lit}`T` has a positive (hence self-adjoint) square root {lit}`R` with
{lit}`R² = T` (7.39), so {lit}`det T = (det R)²`; and {lit}`det R` is real because
{lit}`R` self-adjoint gives {lit}`conj(det R) = det(R*) = det R` (9.56(c)). Hence
{lit}`det T` is the square of a real number, so it is a nonnegative real. -/
theorem det_positive_nonneg {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    ∃ c : ℝ, 0 ≤ c ∧ LinearMap.det T = (c : 𝕜) := by
  obtain ⟨R, hR, hRT⟩ := LADR.Section_7C.exists_positive_sqrt hT
  have hsym : LinearMap.adjoint R = R :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint R).mp hR.1
  have hreal : conj (LinearMap.det R) = LinearMap.det R := by
    rw [← det_adjoint_eq_conj, hsym]
  have hdreal : ((RCLike.re (LinearMap.det R) : ℝ) : 𝕜) = LinearMap.det R :=
    RCLike.conj_eq_iff_re.mp hreal
  refine ⟨(RCLike.re (LinearMap.det R)) ^ 2, sq_nonneg _, ?_⟩
  have hTd : LinearMap.det T = LinearMap.det R * LinearMap.det R := by
    rw [← hRT, LinearMap.det_comp]
  rw [hTd, ← hdreal]
  push_cast
  ring

/-! 9.60 {lit}`|det T|` equals the product of the singular values of {lit}`T`,
equivalently {lit}`√det(T*T)`.

We prove the {lit}`√det(T*T)` characterization directly: {lit}`det(T* T) =
conj(det T)·det T = ‖det T‖²` by 9.56(c) ({name}`det_adjoint_eq_conj`), so
{lit}`‖det T‖ = √det(T* T)`. The equivalent *product of singular values* form
{lit}`|det T| = s₁ ⋯ sₙ` is proved below in
{lit}`norm_det_eq_prod_singularValues`: since {lit}`T* T` acts as {lit}`sₖ²` on
the SVD eigenbasis (7.72, Section 7E), {lit}`det(T* T) = ∏ sₖ²`. -/

/-- 9.60 auxiliary: {lit}`det(T* T) = ‖det T‖²` (a nonnegative real). -/
theorem det_adjoint_comp_self (T : E →ₗ[𝕜] E) :
    LinearMap.det (LinearMap.adjoint T ∘ₗ T) = ((‖LinearMap.det T‖ ^ 2 : ℝ) : 𝕜) := by
  rw [LinearMap.det_comp, det_adjoint_eq_conj, RCLike.conj_mul]; push_cast; ring

/-- 9.60 ({lit}`√det(T*T)` form): {lit}`‖det T‖ = √det(T* T)`. -/
theorem norm_det_eq_sqrt_det_adjoint_comp_self (T : E →ₗ[𝕜] E) :
    ‖LinearMap.det T‖ =
      Real.sqrt (RCLike.re (LinearMap.det (LinearMap.adjoint T ∘ₗ T))) := by
  rw [det_adjoint_comp_self, RCLike.ofReal_re, Real.sqrt_sq (norm_nonneg _)]

/-- The determinant of an operator diagonal on a basis is the product of its
diagonal scalars. -/
theorem det_eq_prod_of_apply_eq_smul {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    {n : ℕ} (b : Module.Basis (Fin n) K W) (f : W →ₗ[K] W) (d : Fin n → K)
    (hf : ∀ i, f (b i) = d i • b i) : LinearMap.det f = ∏ i, d i := by
  rw [← LinearMap.det_toMatrix b, show LinearMap.toMatrix b b f = Matrix.diagonal d from ?_,
    Matrix.det_diagonal]
  ext i j
  rw [LinearMap.toMatrix_apply, hf, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.single_apply, Matrix.diagonal_apply]
  rcases eq_or_ne i j with h | h
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]

/-- 9.60 (product-of-singular-values form): {lit}`‖det T‖ = s₁ ⋯ sₙ`, the product
of the singular values. Since {lit}`T* T` acts as {lit}`sₖ²` on the SVD eigenbasis
(7.72), {lit}`det(T* T) = ∏ sₖ²`, so {lit}`‖det T‖ = √det(T* T) = ∏ sₖ`. -/
theorem norm_det_eq_prod_singularValues (T : E →ₗ[𝕜] E) :
    ‖LinearMap.det T‖ = ∏ i, LADR.Section_7E.singularValues T i := by
  set b := (LADR.Section_7E.svdBasis T).toBasis with hb
  have hf : ∀ i, (LinearMap.adjoint T ∘ₗ T) (b i)
      = (((LADR.Section_7E.singularValues T i) ^ 2 : ℝ) : 𝕜) • b i := by
    intro i
    rw [hb, OrthonormalBasis.coe_toBasis]
    exact LADR.Section_7E.adjComp_apply_svdBasis T i
  rw [norm_det_eq_sqrt_det_adjoint_comp_self,
    det_eq_prod_of_apply_eq_smul b (LinearMap.adjoint T ∘ₗ T) _ hf,
    ← RCLike.ofReal_prod, RCLike.ofReal_re, Finset.prod_pow,
    Real.sqrt_sq (Finset.prod_nonneg fun i _ => LADR.Section_7E.singularValues_nonneg T i)]

end InnerProductDetOps

/-- 9.61 An operator {lit}`T ∈ ℒ(ℝⁿ)` changes volume by the factor {lit}`|det T|`:
{lit}`volume T(Ω) = |det T| · volume Ω`. This is mathlib's Haar change-of-variables
{name}`MeasureTheory.Measure.addHaar_image_linearMap`. -/
theorem volume_image_eq_9_61 {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    MeasureTheory.volume (T '' Ω) =
      ENNReal.ofReal |LinearMap.det T| * MeasureTheory.volume Ω :=
  MeasureTheory.Measure.addHaar_image_linearMap MeasureTheory.volume T Ω

/-- **7.111** (singular-values form of the volume change) On {lit}`ℝⁿ` an operator
{lit}`T` scales volume by the product of its singular values:
{lit}`volume T(Ω) = (s₁ ⋯ sₙ) · volume Ω`. This is 9.61 with the Jacobian
{lit}`|det T|` rewritten as {lit}`s₁ ⋯ sₙ` by 9.60
({name}`LADR.Section_9C.norm_det_eq_prod_singularValues`). -/
theorem volume_image_eq_prod_singularValues {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    MeasureTheory.volume (T '' Ω) =
      ENNReal.ofReal (∏ i, LADR.Section_7E.singularValues T i) * MeasureTheory.volume Ω := by
  rw [volume_image_eq_9_61, ← Real.norm_eq_abs, norm_det_eq_prod_singularValues]

/-! 9.62 If {lit}`F = ℂ`, the characteristic polynomial of {lit}`T` equals
{lit}`(z − λ₁)^{d₁} ⋯ (z − λₘ)^{dₘ}`, where {lit}`λ₁, …, λₘ` are the distinct
eigenvalues with multiplicities {lit}`d₁, …, dₘ`. Equivalently, over {lit}`ℂ`
the (monic, splitting) characteristic polynomial is the product over its roots
of {lit}`(z − λ)`, and those roots are exactly the eigenvalues of {lit}`T`. -/

theorem charpoly_eq_prod_roots {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    LinearMap.charpoly T =
        (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
          (LinearMap.charpoly T).roots).prod ∧
      ∀ γ : ℂ, γ ∈ (LinearMap.charpoly T).roots ↔ HasEigenvalue T γ := by
  have hmonic : (LinearMap.charpoly T).Monic := LinearMap.charpoly_monic T
  constructor
  · have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (p := LinearMap.charpoly T)
      (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _))
    rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul] at h
    exact h.symm
  · intro γ
    rw [Polynomial.mem_roots hmonic.ne_zero]
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly T γ).symm

/-! 9.63 Definition: characteristic polynomial.

The characteristic polynomial of {lit}`T` is the polynomial {lit}`z ↦ det(zI − T)`
(mathlib's {name}`LinearMap.charpoly`, whose evaluation at {lit}`z` is
{lit}`det(zI − T)` by {name}`LinearMap.eval_charpoly`). It is monic of degree
{lit}`dim V`, and its zeros in {lit}`F` are exactly the eigenvalues of {lit}`T`. -/

example [Finite F V] (T : V →ₗ[F] V) (z : F) :
    (LinearMap.charpoly T).eval z = LinearMap.det (z • LinearMap.id - T) := by
  rw [LinearMap.eval_charpoly, ← Module.algebraMap_end_eq_smul_id]

example [Finite F V] (T : V →ₗ[F] V) : (LinearMap.charpoly T).Monic :=
  LinearMap.charpoly_monic T

example [Finite F V] (T : V →ₗ[F] V) :
    (LinearMap.charpoly T).natDegree = finrank F V :=
  LinearMap.charpoly_natDegree T

/-! 9.64 Cayley–Hamilton theorem: if {lit}`q` is the characteristic polynomial of
{lit}`T`, then {lit}`q(T) = 0`. mathlib's {name}`LinearMap.aeval_self_charpoly`
holds over any commutative ring, so in particular over both {lit}`ℝ` and
{lit}`ℂ`. -/

theorem cayley_hamilton [Finite F V] (T : V →ₗ[F] V) :
    Polynomial.aeval T (LinearMap.charpoly T) = 0 :=
  LinearMap.aeval_self_charpoly T

/-! 9.65 Characteristic polynomial, trace, and determinant.

Fixing a basis and writing {lit}`A = ℳ(T)`, the characteristic polynomial is
{lit}`zⁿ − (tr T) z^{n−1} + ⋯ + (−1)ⁿ (det T)`. We record: it is monic of degree
{lit}`n`; the coefficient of {lit}`z^{n−1}` is {lit}`− tr A`
({name}`Matrix.trace_eq_neg_charpoly_coeff`); and the constant term relates to the
determinant by {lit}`det A = (−1)ⁿ · (constant term)`
({name}`Matrix.det_eq_sign_charpoly_coeff`). -/

theorem charpoly_monic_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    A.charpoly.Monic :=
  Matrix.charpoly_monic A

theorem charpoly_natDegree_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    A.charpoly.natDegree = n := by
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem charpoly_coeff_trace {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) F) :
    A.trace = - A.charpoly.coeff (n - 1) := by
  have h := Matrix.trace_eq_neg_charpoly_coeff A
  rwa [Fintype.card_fin] at h

theorem charpoly_coeff_det {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    A.det = (-1) ^ n * A.charpoly.coeff 0 := by
  have h := Matrix.det_eq_sign_charpoly_coeff A
  rwa [Fintype.card_fin] at h

open scoped Matrix in
/-- 9.66 Hadamard's inequality: for an {lit}`n×n` matrix {lit}`A` with columns
{lit}`v₁, …, vₙ`, {lit}`|det A| ≤ ∏ₖ ‖vₖ‖`.

Following Axler: if the columns are dependent then {lit}`det A = 0` and the bound
is trivial; otherwise take a QR factorization {lit}`A = QR` (7.58). Then
{lit}`|det A| = |det R| = ∏ₖ |Rₖₖ|` (Q unitary has {lit}`|det| = 1` (9.58), R
triangular), and {lit}`|Rₖₖ| ≤ ‖vₖ‖` because {lit}`‖vₖ‖² = (A*A)ₖₖ = (R*R)ₖₖ =
∑ⱼ |Rⱼₖ|² ≥ |Rₖₖ|²` (using {lit}`Q*Q = I`). -/
theorem hadamard_inequality {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ i, ‖(EuclideanSpace.equiv (Fin n) 𝕜).symm (Aᵀ i)‖ := by
  classical
  set col : Fin n → EuclideanSpace 𝕜 (Fin n) :=
    fun i => (EuclideanSpace.equiv (Fin n) 𝕜).symm (Aᵀ i) with hcol
  by_cases hindep : LinearIndependent 𝕜 col
  · obtain ⟨Q, R, hQ, hRtri, _, hAQR⟩ := LADR.Section_7D.QR_factorization A hindep
    have hRupper : R.BlockTriangular id := hRtri
    have hQdet : ‖Q.det‖ = 1 := by
      have hu := (Unitary.mem_iff.mp (Matrix.det_of_mem_unitary hQ)).1
      rw [RCLike.star_def, RCLike.conj_mul] at hu
      have h2 : ‖Q.det‖ ^ 2 = 1 := by exact_mod_cast hu
      rw [← Real.sqrt_sq (norm_nonneg Q.det), h2, Real.sqrt_one]
    have hnormdet : ‖A.det‖ = ∏ i, ‖R i i‖ := by
      rw [hAQR, Matrix.det_mul, norm_mul, hQdet, one_mul,
        Matrix.det_of_upperTriangular hRupper, norm_prod]
    rw [hnormdet]
    refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
    -- ‖R i i‖ ≤ ‖col i‖
    have hARR : Aᴴ * A = Rᴴ * R := by
      have hQQ : Qᴴ * Q = 1 := (Matrix.mem_unitaryGroup_iff').mp hQ
      rw [hAQR, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ,
        hQQ, Matrix.one_mul]
    have hcolsq : ‖col i‖ ^ 2 = ∑ k, ‖A k i‖ ^ 2 := by
      rw [hcol, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      rfl
    have hARentry : ∑ k, ‖A k i‖ ^ 2 = ∑ k, ‖R k i‖ ^ 2 := by
      have hdiag := congrFun (congrFun hARR i) i
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
        RCLike.conj_mul] at hdiag
      have := congrArg RCLike.re hdiag
      push_cast at this ⊢
      simpa using this
    have hge : ‖R i i‖ ^ 2 ≤ ‖col i‖ ^ 2 := by
      rw [hcolsq, hARentry]
      refine Finset.single_le_sum (f := fun k => ‖R k i‖ ^ 2) (fun k _ => ?_)
        (Finset.mem_univ i)
      positivity
    have h1 := Real.sqrt_le_sqrt hge
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1
  · have hdet0 : A.det = 0 := by
      apply Matrix.det_eq_zero_of_not_linearIndependent_cols
      intro hdep
      exact hindep (hdep.map' ((EuclideanSpace.equiv (Fin n) 𝕜).symm.toLinearEquiv.toLinearMap)
        (LinearMap.ker_eq_bot.mpr (EuclideanSpace.equiv (Fin n) 𝕜).symm.injective))
    rw [hdet0, norm_zero]
    exact Finset.prod_nonneg (fun i _ => norm_nonneg _)

/-! 9.67 Determinant of a Vandermonde matrix:
{lit}`det V(β₁, …, βₙ) = ∏_{1 ≤ j < k ≤ n} (βₖ − βⱼ)`
({name}`Matrix.det_vandermonde`). -/

theorem det_vandermonde {n : ℕ} (v : Fin n → F) :
    (Matrix.vandermonde v).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) :=
  Matrix.det_vandermonde v

/-! # Exercises 9C -/

/-- 9C.1 Prove or give a counterexample: {lit}`det(S + T) = det S + det T`. (The
statement is false; exhibit operators on {lit}`F²` for which it fails.) -/
theorem exercise_9C_1 :
    ∃ S T : (Fin 2 → F) →ₗ[F] (Fin 2 → F),
      LinearMap.det (S + T) ≠ LinearMap.det S + LinearMap.det T := by
  sorry

/-- 9C.2 If the first column of {lit}`A` is zero except possibly the top entry
{lit}`A₀,₀`, and {lit}`B` is obtained by deleting the first row and column, then
{lit}`det A = A₀,₀ · det B`. -/
theorem exercise_9C_2 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (h : ∀ i : Fin (n + 1), i ≠ 0 → A i 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det := by
  sorry

/-- 9C.3 If {lit}`T` is nilpotent, then {lit}`det(I + T) = 1`. -/
theorem exercise_9C_3 [Finite F V] (T : V →ₗ[F] V) (h : IsNilpotent T) :
    LinearMap.det (LinearMap.id + T) = 1 := by
  sorry

/-! 9C.4 (deferred): {lit}`S` is unitary iff {lit}`|det S| = ‖S‖ = 1`. Deferred —
it mixes the determinant with the operator norm {lit}`‖S‖` of Section 7F, whose
inner-product-space norm machinery is outside this determinant-focused section. -/

/-- 9C.5 The determinant of a block upper-triangular matrix is the product of the
determinants of the diagonal blocks. -/
@[avoiding Matrix.det_fromBlocks_zero₂₁]
theorem exercise_9C_5 {m n : ℕ} (A : Matrix (Fin m) (Fin m) F)
    (B : Matrix (Fin n) (Fin n) F) (C : Matrix (Fin m) (Fin n) F) :
    (Matrix.fromBlocks A C 0 B).det = A.det * B.det := by
  sorry

/-- 9C.6 Permuting the columns of {lit}`A` by {lit}`σ` multiplies the determinant
by {lit}`sign σ`. -/
@[avoiding Matrix.det_permute']
theorem exercise_9C_6 {n : ℕ} (A : Matrix (Fin n) (Fin n) F)
    (σ : Equiv.Perm (Fin n)) :
    (A.submatrix id σ).det = Equiv.Perm.sign σ * A.det := by
  sorry

/-- 9C.7 For invertible {lit}`T` with characteristic polynomials {lit}`p` (of
{lit}`T`) and {lit}`q` (of {lit}`T⁻¹`), {lit}`q(z) = z^{dim V} · p(1/z) / p(0)` for
every nonzero {lit}`z`. -/
theorem exercise_9C_7 [Finite F V] (T : V ≃ₗ[F] V) (z : F) (hz : z ≠ 0) :
    (LinearMap.charpoly (T.symm : V →ₗ[F] V)).eval z =
      z ^ finrank F V * (LinearMap.charpoly (T : V →ₗ[F] V)).eval (1 / z) /
        (LinearMap.charpoly (T : V →ₗ[F] V)).eval 0 := by
  sorry

/-- 9C.8 An operator on a finite-dimensional real vector space with no
eigenvalues has {lit}`det T > 0`. -/
theorem exercise_9C_8 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    (T : V →ₗ[ℝ] V) (h : ∀ γ : ℝ, ¬ HasEigenvalue T γ) :
    0 < LinearMap.det T := by
  sorry

/-- 9C.9 If {lit}`V` is a real vector space of even dimension, {lit}`T ∈ ℒ(V)`,
and {lit}`det T < 0`, then {lit}`T` has at least two distinct eigenvalues. -/
theorem exercise_9C_9 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    (hdim : Even (finrank ℝ V)) (T : V →ₗ[ℝ] V) (h : LinearMap.det T < 0) :
    ∃ a b : ℝ, a ≠ b ∧ HasEigenvalue T a ∧ HasEigenvalue T b := by
  sorry

/-- 9C.10 An operator on a real vector space of odd dimension has an eigenvalue.
(To be proved here via determinants / the characteristic polynomial, rather than
the minimal-polynomial argument of 5.34.) -/
@[avoiding LADR.Section_5B.exists_eigenvalue_of_odd_finrank]
theorem exercise_9C_10 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    (hdim : Odd (finrank ℝ V)) (T : V →ₗ[ℝ] V) :
    ∃ γ : ℝ, HasEigenvalue T γ := by
  sorry

/-- 9C.11 Counterexample: over {lit}`ℝ`, {lit}`det T > 0` does not imply that
{lit}`T` has a square root. -/
theorem exercise_9C_11 :
    ∃ (n : ℕ) (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)),
      0 < LinearMap.det T ∧ ¬ ∃ S : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), S ∘ₗ S = T := by
  sorry

/-! 9C.12 (deferred): for invertible {lit}`S`, {lit}`p(z) = det(zS − T)` is a
polynomial of degree {lit}`dim V` with leading coefficient {lit}`det S`. Deferred —
establishing that {lit}`z ↦ det(zS − T)` is a polynomial (and reading off its
degree and leading coefficient) needs the determinant-as-polynomial-in-a-parameter
development not set up here. -/

/-- 9C.13 Over {lit}`ℂ` with {lit}`n = dim V > 2`, the coefficient of {lit}`z^{n−2}`
in the characteristic polynomial is the elementary symmetric polynomial {lit}`e₂` of
the eigenvalues, and the coefficient of {lit}`z` is {lit}`(−1)^{n−1} e_{n−1}`. -/
theorem exercise_9C_13 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (hn : 2 < finrank ℂ V) :
    (LinearMap.charpoly T).coeff (finrank ℂ V - 2) =
        (LinearMap.charpoly T).roots.esymm 2 ∧
      (LinearMap.charpoly T).coeff 1 =
        (-1) ^ (finrank ℂ V - 1) * (LinearMap.charpoly T).roots.esymm (finrank ℂ V - 1) := by
  sorry

/-- 9C.14 For a positive operator {lit}`T` with positive square root {lit}`R`,
{lit}`det √T = √(det T)`. -/
theorem exercise_9C_14 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (T R : E →ₗ[𝕜] E)
    (hT : T.IsPositive) (hR : R.IsPositive) (hRT : R ∘ₗ R = T) :
    LinearMap.det R = ((Real.sqrt (RCLike.re (LinearMap.det T)) : ℝ) : 𝕜) := by
  sorry

/-- 9C.15 Via the polar decomposition, {lit}`|det T| = √(det(T*T))`. -/
theorem exercise_9C_15 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    ‖LinearMap.det T‖ =
      Real.sqrt (RCLike.re (LinearMap.det (LinearMap.adjoint T ∘ₗ T))) := by
  sorry

/-- 9C.16 For {lit}`g(x) = det(I + xT)`, {lit}`g′(0) = tr T`. -/
theorem exercise_9C_16 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) :
    deriv (fun x : ℂ => LinearMap.det (LinearMap.id + x • T)) 0 =
      LinearMap.trace ℂ V T := by
  sorry

/-- 9C.17 The ellipsoid is the image of the open unit ball under the diagonal
operator {lit}`T = diag(a, b, c)`, so its volume is {lit}`abc` times the volume of
the unit ball ({name}`MeasureTheory.Measure.addHaar_image_linearMap`). -/
theorem exercise_9C_17 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), T x = !₂[a * x 0, b * x 1, c * x 2]) :
    MeasureTheory.volume (T '' {x | ‖x‖ < 1}) =
      ENNReal.ofReal (a * b * c) *
        MeasureTheory.volume {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ < 1} := by
  sorry

/-! 9C.18–9C.20: Hadamard's inequality (9.66) is proved above as
{lit}`hadamard_inequality`, which is Exercise 9C.18. Its equality case (9C.19) and
the matrix-entry bound (9C.20) build on it and are left as exercises. -/

/-- 9C.21 The determinant is the unique multiplicative function on complex square
matrices that agrees with the product of diagonal entries on diagonal matrices. -/
theorem exercise_9C_21 {n : ℕ} (δ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hmul : ∀ A B, δ (A * B) = δ A * δ B)
    (hdiag : ∀ d : Fin n → ℂ, δ (Matrix.diagonal d) = ∏ i, d i) :
    ∀ A, δ A = A.det := by
  sorry

end LADR.Section_9C
