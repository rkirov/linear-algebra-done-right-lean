import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linter.Style
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 8D: Trace
-/

namespace LADR.Section_8D

open scoped InnerProductSpace
open Module (finrank)

section Field

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-! 8.47 Definition: trace of a matrix.

The *trace* of a square matrix {lit}`A`, denoted {lit}`tr A`, is the sum of its
diagonal entries — mathlib's {name}`Matrix.trace`. -/

/-- 8.48 Example: the trace of a {lit}`3`-by-{lit}`3` matrix is the sum of its
diagonal entries; here {lit}`3 + 2 + 0 = 5`. -/
example : Matrix.trace !![(3 : ℚ), -1, -2; 5, 2, -3; 1, 6, 0] = 5 := by
  simp [Matrix.trace_fin_three]; norm_num

/-- 8.49 The trace of {lit}`AB` equals the trace of {lit}`BA`, for {lit}`A` an
{lit}`m`-by-{lit}`n` matrix and {lit}`B` an {lit}`n`-by-{lit}`m` matrix — mathlib's
{name}`Matrix.trace_mul_comm`. -/
theorem trace_mul_comm {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n F)
    (B : Matrix n m F) : (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

/-! 8.50 The trace of the matrix of an operator does not depend on the basis.

For any two bases {lit}`b`, {lit}`c` of {lit}`V`, the matrices {lit}`ℳ(T, b)`
and {lit}`ℳ(T, c)` have the same trace — both equal the basis-independent
{name}`LinearMap.trace`. -/
omit [FiniteDimensional F V] in
theorem trace_toMatrix_indep {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] (b : Module.Basis ι F V) (c : Module.Basis κ F V) (T : V →ₗ[F] V) :
    (LinearMap.toMatrix b b T).trace = (LinearMap.toMatrix c c T).trace := by
  rw [← LinearMap.trace_eq_matrix_trace F b T, ← LinearMap.trace_eq_matrix_trace F c T]

/-! 8.51 Definition: trace of an operator, {lit}`tr T`.

By 8.50 the definition {lit}`tr T = ` trace of the matrix of {lit}`T` (with
respect to any basis) makes sense; this is mathlib's {name}`LinearMap.trace`. -/

omit [FiniteDimensional F V] in
theorem trace_eq_toMatrix_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F V) (T : V →ₗ[F] V) :
    LinearMap.trace F V T = (LinearMap.toMatrix b b T).trace :=
  LinearMap.trace_eq_matrix_trace F b T

/-! 8.54 Trace and the characteristic polynomial.

For {lit}`n = dim V`, {lit}`tr T` equals the negative of the coefficient of
{lit}`z^{n-1}` in the characteristic polynomial of {lit}`T`. This is the
operator form of {name}`Matrix.trace_eq_neg_charpoly_coeff`. -/
theorem trace_eq_neg_charpoly_coeff [Nontrivial V] (T : V →ₗ[F] V) :
    LinearMap.trace F V T = -(T.charpoly).coeff (finrank F V - 1) := by
  classical
  haveI : Nonempty (Fin (finrank F V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let b := Module.finBasis F V
  have hcard : Fintype.card (Fin (finrank F V)) = finrank F V := by simp
  rw [trace_eq_toMatrix_trace b, Matrix.trace_eq_neg_charpoly_coeff,
    LinearMap.charpoly_toMatrix T b, hcard]

/-! 8.56 The trace is linear, and {lit}`tr(ST) = tr(TS)`. -/

omit [FiniteDimensional F V] in
theorem trace_add (S T : V →ₗ[F] V) :
    LinearMap.trace F V (S + T) = LinearMap.trace F V S + LinearMap.trace F V T :=
  map_add _ _ _

omit [FiniteDimensional F V] in
theorem trace_smul (a : F) (T : V →ₗ[F] V) :
    LinearMap.trace F V (a • T) = a • LinearMap.trace F V T :=
  map_smul _ _ _

omit [FiniteDimensional F V] in
theorem trace_comp_comm (S T : V →ₗ[F] V) :
    LinearMap.trace F V (S ∘ₗ T) = LinearMap.trace F V (T ∘ₗ S) :=
  LinearMap.trace_mul_comm F S T

/-! 8.57 There is no pair {lit}`S, T ∈ ℒ(V)` with {lit}`ST - TS = I` (when the
dimension of {lit}`V` is nonzero in {lit}`F`, e.g. always in characteristic 0),
because {lit}`tr(ST - TS) = 0` while {lit}`tr I = dim V`. -/
theorem sub_comp_comm_ne_one [Nontrivial V] (hF : (finrank F V : F) ≠ 0)
    (S T : V →ₗ[F] V) : S ∘ₗ T - T ∘ₗ S ≠ LinearMap.id := by
  intro h
  have h0 : LinearMap.trace F V (S ∘ₗ T - T ∘ₗ S) = 0 := by
    rw [map_sub, trace_comp_comm, sub_self]
  rw [h, LinearMap.trace_id] at h0
  exact hF h0

end Field

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-! 8.52 On complex vector spaces, the trace equals the sum of the eigenvalues,
each included as many times as its multiplicity.

Axler's "eigenvalues with multiplicity" are the roots of the characteristic
polynomial; over {lit}`ℂ` (algebraically closed) {lit}`tr T` is their sum. This
is the operator form of {name}`Matrix.trace_eq_sum_roots_charpoly`. -/
theorem trace_eq_sum_roots_charpoly (T : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V T = (T.charpoly).roots.sum := by
  classical
  let b := Module.finBasis ℂ V
  rw [trace_eq_toMatrix_trace b, Matrix.trace_eq_sum_roots_charpoly,
    LinearMap.charpoly_toMatrix T b]

/-- 8.53 Example: for {lit}`T(z₁,z₂,z₃) = (3z₁−z₂−2z₃, 3z₁+2z₂−3z₃, z₁+2z₂)` on
{lit}`ℂ³` — whose standard-basis matrix has diagonal {lit}`3, 2, 0` — the trace is
{lit}`5` (equivalently the sum {lit}`1 + (2+3i) + (2−3i)` of its eigenvalues, 8.52). -/
example : LinearMap.trace ℂ (Fin 3 → ℂ)
    (Matrix.toLin (Pi.basisFun ℂ (Fin 3)) (Pi.basisFun ℂ (Fin 3))
      !![(3 : ℂ), -1, -2; 3, 2, -3; 1, 2, 0]) = 5 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 3)), LinearMap.toMatrix_toLin]
  simp [Matrix.trace_fin_three]; norm_num

end Complex

section Inner

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-! 8.55 Trace on an inner product space.

If {lit}`e₁, …, eₙ` is an orthonormal basis of {lit}`V`, then
{lit}`tr T = ∑ₖ ⟨T eₖ, eₖ⟩`. (mathlib conjugates the *first* slot, so the
statement reads {lit}`tr T = ∑ₖ ⟨eₖ, T eₖ⟩`; over a real space the two agree,
and over {lit}`ℂ` they are complex conjugates whose sum equals {lit}`tr T`.) -/
omit [FiniteDimensional 𝕜 E] in
theorem trace_eq_sum_inner {ι : Type*} [Fintype ι] (T : E →ₗ[𝕜] E)
    (b : OrthonormalBasis ι 𝕜 E) :
    LinearMap.trace 𝕜 E T = ∑ i, ⟪b i, T (b i)⟫_𝕜 :=
  T.trace_eq_sum_inner b

end Inner

/-! # Exercises 8D -/

section Exercises

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- 8D.1 For {lit}`T u = ⟨u, v⟩ w` on an inner product space, {lit}`tr T = ⟨w, v⟩`. -/
theorem exercise_8D_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (v w : E) (T : E →ₗ[𝕜] E)
    (hT : ∀ u, T u = ⟪v, u⟫_𝕜 • w) :
    LinearMap.trace 𝕜 E T = ⟪v, w⟫_𝕜 := by
  sorry

/-- 8D.2 If {lit}`P² = P` then {lit}`tr P = dim (range P)`. -/
theorem exercise_8D_2 (P : V →ₗ[F] V) (hP : P ∘ₗ P = P) :
    LinearMap.trace F V P = (finrank F (LinearMap.range P) : F) := by
  sorry

/-- 8D.3 If {lit}`T⁵ = T` over {lit}`ℂ`, then the real and imaginary parts of
{lit}`tr T` are both integers. -/
theorem exercise_8D_3 {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : V →ₗ[ℂ] V) (h : T ^ 5 = T) :
    (∃ a : ℤ, (LinearMap.trace ℂ V T).re = a) ∧
      (∃ b : ℤ, (LinearMap.trace ℂ V T).im = b) := by
  sorry

/-- 8D.4 {lit}`tr T* = conj (tr T)`. -/
theorem exercise_8D_4 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) :
    LinearMap.trace 𝕜 E (LinearMap.adjoint T) = (starRingEnd 𝕜) (LinearMap.trace 𝕜 E T) := by
  sorry

/-- 8D.5 A positive operator with trace {lit}`0` is {lit}`0`. -/
theorem exercise_8D_5 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E) (hT : T.IsPositive)
    (h : LinearMap.trace 𝕜 E T = 0) : T = 0 := by
  sorry

/-- 8D.6 For orthogonal projections {lit}`P, Q`, {lit}`tr(PQ) ≥ 0`. -/
theorem exercise_8D_6 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (P Q : E →ₗ[𝕜] E)
    (hP : LinearMap.adjoint P = P ∧ P ∘ₗ P = P)
    (hQ : LinearMap.adjoint Q = Q ∧ Q ∘ₗ Q = Q) :
    0 ≤ RCLike.re (LinearMap.trace 𝕜 E (P ∘ₗ Q)) := by
  sorry

/-- 8D.7 For the given {lit}`3×3` matrix on {lit}`ℂ³` with eigenvalues {lit}`−48`
and {lit}`24`, the third eigenvalue is {lit}`36` (the eigenvalues sum to the
trace). -/
theorem exercise_8D_7 (T : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (hT : LinearMap.toMatrix' T = !![51, -12, -21; 60, -40, -28; 57, -68, 1])
    (h1 : Module.End.HasEigenvalue T (-48)) (h2 : Module.End.HasEigenvalue T 24) :
    Module.End.HasEigenvalue T 36 := by
  sorry

/-- 8D.8 Counterexample: {lit}`tr(ST) = (tr S)(tr T)` can fail. -/
theorem exercise_8D_8 :
    ¬ ∀ (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E]
      (S T : E →ₗ[F] E),
      LinearMap.trace F E (S ∘ₗ T) =
        LinearMap.trace F E S * LinearMap.trace F E T := by
  sorry

/-- 8D.9 If {lit}`tr (S ∘ₗ T) = 0` for all {lit}`S ∈ ℒ(V)`, then {lit}`T = 0`. -/
theorem exercise_8D_9 (T : V →ₗ[F] V)
    (h : ∀ S : V →ₗ[F] V, LinearMap.trace F V (S ∘ₗ T) = 0) : T = 0 := by
  sorry

/-- 8D.10 The trace is the only linear functional {lit}`τ` with {lit}`τ(ST) = τ(TS)`
and {lit}`τ(I) = dim V`. -/
theorem exercise_8D_10 (τ : (V →ₗ[F] V) →ₗ[F] F)
    (hcomm : ∀ S T : V →ₗ[F] V, τ (S ∘ₗ T) = τ (T ∘ₗ S))
    (hid : τ LinearMap.id = (finrank F V : F)) :
    ∀ T : V →ₗ[F] V, τ T = LinearMap.trace F V T := by
  sorry

/-- 8D.11 {lit}`tr(T*T) = ∑ₖ ∑ⱼ |⟨T eₖ, fⱼ⟩|²` for orthonormal bases {lit}`e`,
{lit}`f` (Frobenius norm; basis independent). -/
theorem exercise_8D_11 {𝕜 : Type*} [RCLike 𝕜] {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    {n m : ℕ} (T : E →ₗ[𝕜] G) (e : OrthonormalBasis (Fin n) 𝕜 E)
    (f : OrthonormalBasis (Fin m) 𝕜 G) :
    LinearMap.trace 𝕜 E (LinearMap.adjoint T ∘ₗ T) =
      ((∑ k, ∑ j, ‖⟪f j, T (e k)⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  sorry

/-- 8D.12 (a) {lit}`⟨S, T⟩ = tr(T*S)` defines an inner product on {lit}`ℒ(V, W)`
(the Frobenius / Hilbert–Schmidt inner product). -/
theorem exercise_8D_12a {𝕜 : Type*} [RCLike 𝕜] {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] :
    ∃ core : InnerProductSpace.Core 𝕜 (E →ₗ[𝕜] G),
      ∀ S T : E →ₗ[𝕜] G,
        core.inner S T = LinearMap.trace 𝕜 E (LinearMap.adjoint T ∘ₗ S) := by
  sorry

/-- 8D.13 There exist {lit}`S, T ∈ ℒ(𝒫(𝔽))` with {lit}`ST − TS = I` (impossible in
finite dimensions by 8.57). -/
theorem exercise_8D_13 :
    ∃ S T : Polynomial F →ₗ[F] Polynomial F, S ∘ₗ T - T ∘ₗ S = LinearMap.id := by
  sorry

end Exercises

end LADR.Section_8D
