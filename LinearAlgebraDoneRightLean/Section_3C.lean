import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3C: Matrices
-/

namespace LADR.Section_3C

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis isBasis_stdBasis isBasis_stdBasis_repr
  isBasis_polyMono isBasis_polyMono_repr)
open Module (Finite finrank)

variable {F : Type*} [Field F] {U V W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-! 3.29 Definition: matrix, {lit}`A_{j,k}`

An {lit}`m`-by-{lit}`n` matrix with entries in {lit}`F` is encoded in mathlib
as {lit}`Matrix (Fin m) (Fin n) F`, which unfolds to {lit}`Fin m → Fin n → F`.
The notation {lit}`A j k` denotes the entry in row {lit}`j`, column {lit}`k`. -/

example (m n : ℕ) (A : Matrix (Fin m) (Fin n) F) (j : Fin m) (k : Fin n) : F :=
  A j k

/-! 3.30 Example: {lit}`A_{j,k}` equals entry in row {lit}`j`, column {lit}`k`
The literal syntax in lean is {lit}`!![a, b, c; d, e, f]` for the 2-by-3 matrix.
-/

example : (!![8, 4, (5 - 3 * Complex.I : ℂ); 1, 9, 7] : Matrix (Fin 2) (Fin 3) ℂ)
    1 2 = 7 := by
  rfl

/-! 3.31 Definition: matrix of a linear map, {lit}`ℳ(T)`

Given bases {lit}`v₁, …, vₙ` of {lit}`V` and {lit}`w₁, …, wₘ` of {lit}`W`, the
matrix {lit}`ℳ(T)` is the {lit}`m`-by-{lit}`n` matrix with entries
{lit}`A_{j,k}` defined by {lit}`T vₖ = ∑ⱼ A_{j,k} wⱼ`.

In mathlib this is {name}`LinearMap.toMatrix`, which we wrap to use this
project's {name}`LADR.Section_2B.IsBasis`. -/

noncomputable def matrixOf {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) : Matrix (Fin m) (Fin n) F :=
  LinearMap.toMatrix hv.toModuleBasis hw.toModuleBasis T

/-- The defining property of {lit}`ℳ(T)`: column {lit}`k` of the matrix gives
the coefficients of {lit}`T vₖ` in basis {lit}`w`. -/
theorem matrixOf_apply {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) (j : Fin m) (k : Fin n) :
    matrixOf hv hw T j k = hw.toModuleBasis.repr (T (v k)) j := by
  simp [matrixOf, LinearMap.toMatrix_apply]

/-- Equivalently: {lit}`T vₖ = ∑ⱼ A_{j,k} wⱼ` (Axler's defining equation). -/
theorem matrixOf_spec {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) (k : Fin n) :
    T (v k) = ∑ j, matrixOf hv hw T j k • w j := by
  have h : ∀ j, hw.toModuleBasis j = w j := IsBasis.toModuleBasis_apply hw
  have hsum : T (v k) = ∑ j, hw.toModuleBasis.repr (T (v k)) j • w j := by
    have hb := hw.toModuleBasis.sum_repr (T (v k))
    conv_lhs => rw [← hb]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [h]
  rw [hsum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [matrixOf_apply]

/-! 3.32 Example: matrix of a linear map from {lit}`F²` to {lit}`F³`

For {lit}`T(x, y) = (x + 3y, 2x + 5y, 7x + 9y)` with standard bases,
{lit}`ℳ(T) = [[1, 3], [2, 5], [7, 9]]`. -/

/-- The map {lit}`T(x, y) = (x + 3y, 2x + 5y, 7x + 9y)` from Axler 3.32. -/
noncomputable def T_3_32 : (Fin 2 → F) →ₗ[F] (Fin 3 → F) where
  toFun x := ![x 0 + 3 * x 1, 2 * x 0 + 5 * x 1, 7 * x 0 + 9 * x 1]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp <;> ring

example : matrixOf (isBasis_stdBasis (F := F) 2) (isBasis_stdBasis (F := F) 3)
    T_3_32 = !![1, 3; 2, 5; 7, 9] := by
  ext j k
  rw [matrixOf_apply, isBasis_stdBasis_repr]
  fin_cases j <;> fin_cases k <;> simp [T_3_32]

/-! 3.33 Example: matrix of the differentiation map from {lit}`𝒫₃(ℝ)` to
{lit}`𝒫₂(ℝ)`.

With the standard bases {lit}`1, x, x², x³` and {lit}`1, x, x²`, the matrix
of {lit}`D` is the 3-by-4 matrix
{lit}`[[0,1,0,0],[0,0,2,0],[0,0,0,3]]`. -/

/-- The differentiation map {lit}`D : 𝒫₃(ℝ) → 𝒫₂(ℝ)` from Axler 3.33. -/
noncomputable def D_3_33 :
    Polynomial.degreeLT ℝ 4 →ₗ[ℝ] Polynomial.degreeLT ℝ 3 :=
  LinearMap.codRestrict (Polynomial.degreeLT ℝ 3)
    (Polynomial.derivative.comp (Polynomial.degreeLT ℝ 4).subtype) <| by
    intro p
    rw [Polynomial.mem_degreeLT]
    by_cases hd : (p.val.derivative : Polynomial ℝ) = 0
    · show (p.val.derivative).degree < (3 : ℕ)
      rw [hd, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · have hp : (p : Polynomial ℝ) ≠ 0 := by
        rintro h0; apply hd; simp [h0]
      have hpnd : (p : Polynomial ℝ).natDegree ≠ 0 := by
        intro h
        apply hd
        show (p : Polynomial ℝ).derivative = 0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.derivative_C]
      have h1 : (p : Polynomial ℝ).derivative.natDegree <
          (p : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_derivative_lt hpnd
      have h2 : (p : Polynomial ℝ).natDegree < 4 :=
        (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
          (Polynomial.mem_degreeLT.mp p.2)
      have h3 : (p : Polynomial ℝ).derivative.natDegree < 3 := by omega
      exact (Polynomial.natDegree_lt_iff_degree_lt hd).mp h3

example : matrixOf (isBasis_polyMono 4) (isBasis_polyMono 3) D_3_33 =
    !![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3] := by
  ext j k
  rw [matrixOf_apply, isBasis_polyMono_repr]
  show (D_3_33 ((Polynomial.degreeLT.basis ℝ 4) k) : Polynomial ℝ).coeff j =
    !![0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 3] j k
  have hD : (D_3_33 ((Polynomial.degreeLT.basis ℝ 4) k) : Polynomial ℝ) =
      Polynomial.derivative (Polynomial.X ^ (k : ℕ)) := by
    show ((Polynomial.degreeLT.basis ℝ 4) k : Polynomial ℝ).derivative = _
    rw [Polynomial.degreeLT.basis_val]
  rw [hD, Polynomial.derivative_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
  fin_cases j <;> fin_cases k <;> simp

/-! 3.34 Definition: matrix addition (mathlib provides this pointwise on
{lit}`Matrix`). -/

example {m n : ℕ} (A C : Matrix (Fin m) (Fin n) F) (j : Fin m) (k : Fin n) :
    (A + C) j k = A j k + C j k := by simp

/-! 3.35 Matrix of the sum of linear maps:
{lit}`ℳ(S + T) = ℳ(S) + ℳ(T)`. Left to the reader as exercise 3C.3 (a). -/

/-! 3.36 Definition: scalar multiplication of a matrix (mathlib pointwise). -/

example {m n : ℕ} (γ : F) (A : Matrix (Fin m) (Fin n) F)
    (j : Fin m) (k : Fin n) : (γ • A) j k = γ • A j k := rfl

/-! 3.37 Example: matrix arithmetic -/

example : (2 : ℝ) • (!![3, 1; -1, 5] : Matrix (Fin 2) (Fin 2) ℝ) +
    !![4, 2; 1, 6]
    = !![10, 4; -1, 16] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-! 3.38 Matrix of a scalar times a linear map:
{lit}`ℳ(λT) = λ ℳ(T)`. Left to the reader as exercise 3C.3 (b). -/

/-! 3.39 Notation: {lit}`F^{m,n}` is {lit}`Matrix (Fin m) (Fin n) F`. -/

example (m n : ℕ) : Type _ := Matrix (Fin m) (Fin n) F

/-! 3.40 {lit}`dim F^{m,n} = mn` -/

@[avoiding Module.finrank_matrix]
theorem finrank_matrix (m n : ℕ) :
    finrank F (Matrix (Fin m) (Fin n) F) = m * n := by
  show finrank F (Fin m → Fin n → F) = m * n
  rw [Module.finrank_pi_fintype (R := F)]
  simp

/-! 3.41 Definition: matrix multiplication

In mathlib, this is the {lit}`*` operation on {lit}`Matrix`, where
{lit}`(A * B) j k = ∑ r, A j r * B r k`. -/

example {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (j : Fin m) (k : Fin p) : (A * B) j k = ∑ r, A j r * B r k := by
  simp [Matrix.mul_apply]

/-! 3.42 Example: matrix multiplication -/

example :
    ((!![1, 2; 3, 4; 5, 6] : Matrix (Fin 3) (Fin 2) ℝ) *
      (!![6, 5, 4, 3; 2, 1, 0, -1] : Matrix (Fin 2) (Fin 4) ℝ)) =
    !![10, 7, 4, 1; 26, 19, 12, 5; 42, 31, 20, 9] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring

/-! 3.43 Matrix of product of linear maps -/

theorem matrixOf_comp {p m n : ℕ}
    {u : Fin p → U} {v : Fin n → V} {w : Fin m → W}
    (hu : IsBasis F u) (hv : IsBasis F v) (hw : IsBasis F w)
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    matrixOf hu hw (S ∘ₗ T) = matrixOf hv hw S * matrixOf hu hv T := by
  classical
  simp [matrixOf, LinearMap.toMatrix_comp hu.toModuleBasis hv.toModuleBasis
    hw.toModuleBasis S T]

/-! 3.44 Notation: {lit}`A_{j,·}` and {lit}`A_{·,k}` (rows and columns).
Axler treats {lit}`A_{j,·}` as a 1-by-{lit}`n` matrix and {lit}`A_{·,k}` as
an {lit}`m`-by-1 matrix, not as vectors in {lit}`Fⁿ` or {lit}`Fᵐ`. -/

def row {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (j : Fin m) :
    Matrix (Fin 1) (Fin n) F := fun _ k => A j k

def column {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (k : Fin n) :
    Matrix (Fin m) (Fin 1) F := fun j _ => A j k

/-! 3.45 Example: row and column -/

example :
    row (!![8, 4, 5; 1, 9, 7] : Matrix (Fin 2) (Fin 3) F) 1 = !![1, 9, 7] := by
  ext i j; fin_cases i; fin_cases j <;> rfl

example :
    column (!![8, 4, 5; 1, 9, 7] : Matrix (Fin 2) (Fin 3) F) 1 = !![4; 9] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-! The product of a 1-by-{lit}`n` matrix and an {lit}`n`-by-1 matrix is a
1-by-1 matrix, which we frequently identify with its single entry. For example,
{lit}`(3, 4) * (6; 2) = (3·6 + 4·2) = (26)`, identified with {lit}`26`. -/

example : (!![3, 4] : Matrix (Fin 1) (Fin 2) ℝ) *
    (!![6; 2] : Matrix (Fin 2) (Fin 1) ℝ) = !![26] := by
  ext i j; fin_cases i; fin_cases j; simp [Matrix.mul_apply]; ring

/-! 3.46 Entry of matrix product equals row times column.
{lit}`(AB)_{j,k} = A_{j,·} B_{·,k}` (1-by-{lit}`n` times {lit}`n`-by-1,
identified with its single entry). -/

theorem matrix_mul_entry_eq_row_mul_col {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (j : Fin m) (k : Fin p) :
    (A * B) j k = (row A j * column B k) 0 0 := by
  simp [Matrix.mul_apply, row, column]

/-! 3.47 The same, expanded as a sum:
{lit}`(AB)_{j,k} = A_{j,1} B_{1,k} + … + A_{j,n} B_{n,k}`. -/

theorem matrix_mul_entry {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (j : Fin m) (k : Fin p) :
    (A * B) j k = ∑ r, A j r * B r k := by
  simp [Matrix.mul_apply]

/-! 3.48 Column of matrix product equals matrix times column.
{lit}`(AB)_{·,k} = A B_{·,k}`. -/

theorem column_mul {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F) (k : Fin p) :
    column (A * B) k = A * column B k := by
  ext j _; simp [Matrix.mul_apply, column]

/-! 3.49 Example: matrix-column product equals linear combination of columns.
{lit}`(1, 2; 3, 4; 5, 6) * (5; 1) = (7; 19; 31) = 5·(1; 3; 5) + 1·(2; 4; 6)`.
-/

example : (!![1, 2; 3, 4; 5, 6] : Matrix (Fin 3) (Fin 2) ℝ) *
    (!![5; 1] : Matrix (Fin 2) (Fin 1) ℝ) =
    (5 : ℝ) • (!![1; 3; 5] : Matrix (Fin 3) (Fin 1) ℝ) + (1 : ℝ) • !![2; 4; 6] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]; ring

/-! 3.50 Linear combination of columns.
For {lit}`A : Fᵐ,ⁿ` and {lit}`b : Fⁿ,¹`,
{lit}`A b = b_{1,1} A_{·,1} + … + b_{n,1} A_{·,n}`. -/

theorem matrix_mul_col_eq_sum_columns {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (b : Matrix (Fin n) (Fin 1) F) :
    A * b = ∑ k, b k 0 • column A k := by
  ext j i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, column]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/-! 3.51 Matrix multiplication as linear combinations of columns or rows. -/

/-- (a) Column {lit}`k` of {lit}`C R` is a linear combination of the columns of
{lit}`C`, with coefficients coming from column {lit}`k` of {lit}`R`. -/
theorem column_mul_eq_sum_columns {m c n : ℕ}
    (C : Matrix (Fin m) (Fin c) F) (R : Matrix (Fin c) (Fin n) F) (k : Fin n) :
    column (C * R) k = ∑ r, R r k • column C r := by
  rw [column_mul, matrix_mul_col_eq_sum_columns]
  rfl

/-- (b) Row {lit}`j` of {lit}`C R` is a linear combination of the rows of
{lit}`R`, with coefficients coming from row {lit}`j` of {lit}`C`. -/
theorem row_mul_eq_sum_rows {m c n : ℕ}
    (C : Matrix (Fin m) (Fin c) F) (R : Matrix (Fin c) (Fin n) F) (j : Fin m) :
    row (C * R) j = ∑ r, C j r • row R r := by
  ext i k
  simp only [row, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]

/-! 3.52 Definition: column rank, row rank -/

/-- Column rank: dimension of the span of the columns of {lit}`A` in
{lit}`Fᵐ¹`. -/
noncomputable def columnRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : ℕ :=
  finrank F (Submodule.span F (Set.range (column A)))

/-- Row rank: dimension of the span of the rows of {lit}`A` in
{lit}`F¹ⁿ`. -/
noncomputable def rowRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : ℕ :=
  finrank F (Submodule.span F (Set.range (row A)))

/-! From the definitions: column rank is at most {lit}`n` (there are
{lit}`n` columns) and at most {lit}`m` (since {lit}`dim Fᵐ¹ = m`); row rank
satisfies the symmetric bounds, hence {lit}`min m n` for both. -/

theorem columnRank_le_width {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    columnRank A ≤ n := by
  have := finrank_range_le_card (R := F) (column A)
  simpa [columnRank, Set.finrank] using this

theorem columnRank_le_height {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    columnRank A ≤ m := by
  have h : columnRank A ≤ finrank F (Matrix (Fin m) (Fin 1) F) :=
    Submodule.finrank_le _
  rwa [finrank_matrix, mul_one] at h

theorem rowRank_le_width {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    rowRank A ≤ n := by
  have h : rowRank A ≤ finrank F (Matrix (Fin 1) (Fin n) F) :=
    Submodule.finrank_le _
  rwa [finrank_matrix, one_mul] at h

theorem rowRank_le_height {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    rowRank A ≤ m := by
  have := finrank_range_le_card (R := F) (row A)
  simpa [rowRank, Set.finrank] using this

theorem columnRank_le_min {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    columnRank A ≤ min m n :=
  le_min (columnRank_le_height A) (columnRank_le_width A)

theorem rowRank_le_min {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    rowRank A ≤ min m n :=
  le_min (rowRank_le_height A) (rowRank_le_width A)

/-! 3.53 Example: column rank and row rank of a 2-by-4 matrix.

For {lit}`A = [[4, 7, 1, 8], [3, 5, 2, 9]]`, both ranks equal 2: the bound
{lit}`≤ 2` follows from {name}`rowRank_le_height` / {name}`columnRank_le_height`
(since {lit}`dim F²·¹ = dim F¹·⁴ = 2`); the bound {lit}`≥ 2` comes from two
non-proportional rows. -/

private theorem rowRank_3_53 :
    rowRank (!![4, 7, 1, 8; 3, 5, 2, 9] : Matrix (Fin 2) (Fin 4) ℝ) = 2 := by
  set A : Matrix (Fin 2) (Fin 4) ℝ := !![4, 7, 1, 8; 3, 5, 2, 9] with hA
  have h_le : rowRank A ≤ 2 := rowRank_le_height A
  suffices h_ge : 2 ≤ rowRank A by omega
  -- Show rows 0 and 1 are linearly independent.
  let f : Fin 2 → Matrix (Fin 1) (Fin 4) ℝ := ![row A 0, row A 1]
  have hLI : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : 4 * c 0 + 3 * c 1 = 0 := by
      have := congrFun (congrFun hc 0) 0
      simp [f, row, A, Fin.sum_univ_succ, Matrix.smul_apply,
        Matrix.add_apply] at this
      linarith
    have h1 : 7 * c 0 + 5 * c 1 = 0 := by
      have := congrFun (congrFun hc 0) 1
      simp [f, row, A, Fin.sum_univ_succ, Matrix.smul_apply,
        Matrix.add_apply] at this
      linarith
    intro i
    fin_cases i
    · show c 0 = 0; linarith
    · show c 1 = 0; linarith
  -- Span of {row A 0, row A 1} is contained in span of all rows of A.
  have h_sub : Submodule.span ℝ (Set.range f) ≤
      Submodule.span ℝ (Set.range (row A)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  calc 2 = Fintype.card (Fin 2) := by simp
    _ = finrank ℝ ↥(Submodule.span ℝ (Set.range f)) :=
        (finrank_span_eq_card hLI).symm
    _ ≤ rowRank A := Submodule.finrank_mono h_sub

example : rowRank (!![4, 7, 1, 8; 3, 5, 2, 9] : Matrix (Fin 2) (Fin 4) ℝ) = 2 :=
  rowRank_3_53

example : columnRank (!![4, 7, 1, 8; 3, 5, 2, 9] : Matrix (Fin 2) (Fin 4) ℝ) = 2 := by
  set A : Matrix (Fin 2) (Fin 4) ℝ := !![4, 7, 1, 8; 3, 5, 2, 9] with hA
  have h_le : columnRank A ≤ 2 := columnRank_le_height A
  suffices h_ge : 2 ≤ columnRank A by omega
  let f : Fin 2 → Matrix (Fin 2) (Fin 1) ℝ := ![column A 0, column A 1]
  have hLI : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h0 : 4 * c 0 + 7 * c 1 = 0 := by
      have := congrFun (congrFun hc 0) 0
      simp [f, column, A, Fin.sum_univ_succ, Matrix.smul_apply,
        Matrix.add_apply] at this
      linarith
    have h1 : 3 * c 0 + 5 * c 1 = 0 := by
      have := congrFun (congrFun hc 1) 0
      simp [f, column, A, Fin.sum_univ_succ, Matrix.smul_apply,
        Matrix.add_apply] at this
      linarith
    intro i
    fin_cases i
    · show c 0 = 0; linarith
    · show c 1 = 0; linarith
  have h_sub : Submodule.span ℝ (Set.range f) ≤
      Submodule.span ℝ (Set.range (column A)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Submodule.subset_span ⟨0, rfl⟩
    · exact Submodule.subset_span ⟨1, rfl⟩
  calc 2 = Fintype.card (Fin 2) := by simp
    _ = finrank ℝ ↥(Submodule.span ℝ (Set.range f)) :=
        (finrank_span_eq_card hLI).symm
    _ ≤ columnRank A := Submodule.finrank_mono h_sub

/-! 3.54 Definition: transpose, {lit}`Aᵀ`

In mathlib this is {name}`Matrix.transpose`. -/

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : Matrix (Fin n) (Fin m) F :=
  A.transpose

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (j : Fin m) (k : Fin n) :
    A.transpose k j = A j k := rfl

/-! 3.55 Example: transpose -/
example :
    (!![5, -7; 3, 8; -4, 2] : Matrix (Fin 3) (Fin 2) ℝ).transpose =
      !![5, 3, -4; -7, 8, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-! 3.56 Column–row factorization

If {lit}`A` is {lit}`m`-by-{lit}`n` with column rank {lit}`c ≥ 1`, then there
exist {lit}`C` ({lit}`m`-by-{lit}`c`) and {lit}`R` ({lit}`c`-by-{lit}`n`)
with {lit}`A = C * R`. -/

theorem column_row_factorization {m n : ℕ} (A : Matrix (Fin m) (Fin n) F)
    (_hc : 1 ≤ columnRank A) :
    ∃ (c : ℕ) (C : Matrix (Fin m) (Fin c) F) (R : Matrix (Fin c) (Fin n) F),
      c = columnRank A ∧ A = C * R := by
  classical
  -- The columns of A and their span U.
  let cols : Fin n → Matrix (Fin m) (Fin 1) F := column A
  let U : Submodule F (Matrix (Fin m) (Fin 1) F) :=
    Submodule.span F (Set.range cols)
  haveI : Module.Finite F U :=
    Module.Finite.of_injective U.subtype Subtype.val_injective
  -- A basis b of U.
  obtain ⟨c, b, hb_basis⟩ :=
    LADR.Section_2B.exists_basis (F := F) (V := U)
  have hc_eq : c = columnRank A :=
    LADR.Section_2C.isBasis_card_eq_finrank b hb_basis
  -- Each column of A lives in U.
  have h_cols_in : ∀ k, cols k ∈ U :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  -- C: column k of C is the k-th basis vector (as an m-by-1 matrix).
  let C : Matrix (Fin m) (Fin c) F :=
    fun j k => (b k : Matrix (Fin m) (Fin 1) F) j 0
  -- R: column k of R holds the coordinates of {lit}`cols k` in basis b.
  let R : Matrix (Fin c) (Fin n) F := fun r k =>
    hb_basis.toModuleBasis.repr ⟨cols k, h_cols_in k⟩ r
  refine ⟨c, C, R, hc_eq, ?_⟩
  ext j k
  show A j k = ∑ r, C j r * R r k
  -- Lift the basis representation back to {lit}`Matrix (Fin m) (Fin 1) F`.
  have hb_eq : ∀ r, hb_basis.toModuleBasis r = b r :=
    IsBasis.toModuleBasis_apply hb_basis
  have hsr := hb_basis.toModuleBasis.sum_repr ⟨cols k, h_cols_in k⟩
  have hsr_lift :
      (∑ r, hb_basis.toModuleBasis.repr ⟨cols k, h_cols_in k⟩ r •
          (b r : Matrix (Fin m) (Fin 1) F))
        = cols k := by
    have h := congrArg Subtype.val hsr
    rw [Submodule.coe_sum] at h
    simp_rw [Submodule.coe_smul_of_tower, hb_eq] at h
    exact h
  -- Evaluate at (j, 0) and rearrange.
  have hj := congrFun (congrFun hsr_lift j) 0
  rw [Matrix.sum_apply] at hj
  simp_rw [Matrix.smul_apply, smul_eq_mul] at hj
  have hAj : A j k = (cols k) j 0 := rfl
  rw [hAj, ← hj]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  show hb_basis.toModuleBasis.repr ⟨cols k, h_cols_in k⟩ r *
      (b r : Matrix (Fin m) (Fin 1) F) j 0 =
    (b r : Matrix (Fin m) (Fin 1) F) j 0 *
      hb_basis.toModuleBasis.repr ⟨cols k, h_cols_in k⟩ r
  ring

/-! 3.57 Column rank equals row rank -/

/-- Helper: row {lit}`j` of {lit}`C * R` lies in the span of the rows of
{lit}`R`. -/
private theorem mul_row_in_row_span {m c n : ℕ}
    (C : Matrix (Fin m) (Fin c) F) (R : Matrix (Fin c) (Fin n) F) (j : Fin m) :
    row (C * R) j ∈ Submodule.span F (Set.range (row R)) := by
  rw [row_mul_eq_sum_rows]
  apply Submodule.sum_mem
  intro r _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

/-- Helper: {lit}`columnRank A = 0` iff {lit}`A = 0`. -/
private theorem columnRank_zero_iff_eq_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) F) : columnRank A = 0 ↔ A = 0 := by
  classical
  haveI : Module.Finite F (Submodule.span F (Set.range (column A))) :=
    Module.Finite.of_injective (Submodule.span F (Set.range (column A))).subtype
      Subtype.val_injective
  constructor
  · intro hc
    have hspan_bot : Submodule.span F (Set.range (column A)) = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; exact hc
    rw [Submodule.span_eq_bot] at hspan_bot
    ext j k
    have hcolk : column A k = 0 := hspan_bot _ ⟨k, rfl⟩
    exact congrFun (congrFun hcolk j) 0
  · intro hA
    subst hA
    show finrank F (Submodule.span F
      (Set.range (column (0 : Matrix (Fin m) (Fin n) F)))) = 0
    have hbot : Submodule.span F (Set.range
        (column (0 : Matrix (Fin m) (Fin n) F))) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro x ⟨k, rfl⟩; ext j i; rfl
    rw [hbot]; simp

/-- Helper inequality: row rank is at most column rank, valid for any
matrix. -/
private theorem rowRank_le_columnRank {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) F) : rowRank A ≤ columnRank A := by
  by_cases hc1 : 1 ≤ columnRank A
  · -- Use the column-row factorization {lit}`A = C * R`.
    obtain ⟨c, C, R, hc_eq, hA⟩ := column_row_factorization A hc1
    -- Every row of A lies in the span of the rows of R.
    have h_sub : Submodule.span F (Set.range (row A)) ≤
        Submodule.span F (Set.range (row R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [hA]; exact mul_row_in_row_span C R j
    -- Span of the rows of R has dimension ≤ c.
    have h_R_le : finrank F (Submodule.span F (Set.range (row R))) ≤ c := by
      have := finrank_range_le_card (R := F) (row R)
      simpa using this
    calc rowRank A
        ≤ finrank F (Submodule.span F (Set.range (row R))) :=
          Submodule.finrank_mono h_sub
      _ ≤ c := h_R_le
      _ = columnRank A := hc_eq
  · -- {lit}`columnRank A = 0` forces {lit}`A = 0`, hence {lit}`rowRank A = 0`.
    have hc0 : columnRank A = 0 := by omega
    have hAzero : A = 0 := (columnRank_zero_iff_eq_zero A).mp hc0
    have hr0 : rowRank A = 0 := by
      rw [hAzero]
      show finrank F (Submodule.span F
        (Set.range (row (0 : Matrix (Fin m) (Fin n) F)))) = 0
      have hbot : Submodule.span F (Set.range
          (row (0 : Matrix (Fin m) (Fin n) F))) = ⊥ := by
        rw [Submodule.span_eq_bot]
        rintro x ⟨j, rfl⟩; ext i k; rfl
      rw [hbot]; simp
    omega

/-- Rows of {lit}`Aᵀ` are the transposes of the columns of {lit}`A`, so the
ranks swap via the linear equivalence {name}`Matrix.transposeLinearEquiv`. -/
private theorem rowRank_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    rowRank A.transpose = columnRank A := by
  let τ : Matrix (Fin m) (Fin 1) F ≃ₗ[F] Matrix (Fin 1) (Fin m) F :=
    Matrix.transposeLinearEquiv (Fin m) (Fin 1) F F
  have h_row_eq : row A.transpose = (τ : _ →ₗ[F] _) ∘ column A := by
    funext k; ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  show finrank F (Submodule.span F (Set.range (row A.transpose))) = _
  rw [h_row_eq, Set.range_comp, ← Submodule.map_span]
  exact τ.finrank_map_eq _

theorem columnRank_transpose {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) F) :
    columnRank A.transpose = rowRank A := by
  let τ : Matrix (Fin 1) (Fin n) F ≃ₗ[F] Matrix (Fin n) (Fin 1) F :=
    Matrix.transposeLinearEquiv (Fin 1) (Fin n) F F
  have h_col_eq : column A.transpose = (τ : _ →ₗ[F] _) ∘ row A := by
    funext j; ext k i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  show finrank F (Submodule.span F (Set.range (column A.transpose))) = _
  rw [h_col_eq, Set.range_comp, ← Submodule.map_span]
  exact τ.finrank_map_eq _

theorem columnRank_eq_rowRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    columnRank A = rowRank A := by
  have h1 : rowRank A ≤ columnRank A := rowRank_le_columnRank A
  have h2 : rowRank A.transpose ≤ columnRank A.transpose :=
    rowRank_le_columnRank A.transpose
  rw [rowRank_transpose, columnRank_transpose] at h2
  omega

/-! 3.58 Definition: rank.

mathlib provides this directly as {name}`Matrix.rank`, defined as
{lit}`finrank R (LinearMap.range A.mulVecLin)` (equivalently, the dimension
of the column space). It agrees with our {name}`columnRank`. -/

noncomputable example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) : ℕ := A.rank

theorem matrix_rank_eq_columnRank {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    A.rank = columnRank A := by
  rw [Matrix.rank_eq_finrank_span_cols]
  -- {lit}`A.col k = fun j => A j k`; lift to {name}`Matrix (Fin m) (Fin 1) F`
  -- via the trivial linear equivalence.
  let φ : (Fin m → F) ≃ₗ[F] Matrix (Fin m) (Fin 1) F :=
    { toFun := fun v j _ => v j
      invFun := fun M j => M j 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => by
        ext j i; obtain rfl : i = 0 := Subsingleton.elim _ _; rfl }
  have h_col_eq : column A = (φ : _ →ₗ[F] _) ∘ A.col := by
    funext k; ext j i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  show _ = finrank F (Submodule.span F (Set.range (column A)))
  rw [h_col_eq, Set.range_comp, ← Submodule.map_span,
      φ.finrank_map_eq]

/-! # Exercises -/

/-- 3C.1 -/
theorem exercise_3C_1 [Finite F V] [Finite F W] {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W} (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T) ≤
      Nat.card {p : Fin m × Fin n // matrixOf hv hw T p.1 p.2 ≠ 0} := by
  -- assume otherwise, then M has less than dim range T non-zero columns,
  -- but T v is a linear combination of the columns of M
  -- thus range is spanned by fewer than dim range T non-zero vectors, a contradiction.
  classical
  set A := matrixOf hv hw T with hA
  -- {lit}`S` = the indices of the non-zero columns of {lit}`ℳ(T)`; there are at
  -- most as many of them as there are non-zero entries.
  set S : Finset (Fin n) := Finset.univ.filter (fun k => ∃ j, A j k ≠ 0) with hSdef
  have hmem : ∀ k : Fin n, k ∈ S ↔ ∃ j, A j k ≠ 0 := by
    intro k; simp [hSdef]
  -- {lit}`T vₖ` is the linear combination of {lit}`w` read off column {lit}`k`,
  -- so a zero column contributes nothing.
  have hzero : ∀ k : Fin n, k ∉ S → T (v k) = 0 := by
    intro k hk
    have hcol : ∀ j, A j k = 0 := by
      intro j
      by_contra hj
      exact hk ((hmem k).mpr ⟨j, hj⟩)
    rw [matrixOf_spec hv hw T k, ← hA]
    simp [hcol]
  -- hence the range is spanned by the {lit}`T vₖ` with {lit}`k ∈ S`.
  have hrange : LinearMap.range T
      = Submodule.span F (Set.range (fun k : S => T (v k))) := by
    have h1 : LinearMap.range T
        = Submodule.span F (Set.range (fun k => T (v k))) := by
      rw [LinearMap.range_eq_map, ← hv.2, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1]
    refine le_antisymm ?_ (Submodule.span_mono ?_)
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      by_cases hk : k ∈ S
      · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
      · show T (v k) ∈ _
        rw [hzero k hk]
        exact Submodule.zero_mem _
    · rintro _ ⟨k, rfl⟩
      exact ⟨k.1, rfl⟩
  -- dim range T ≤ #(non-zero columns) ≤ #(non-zero entries)
  have h2 : finrank F (LinearMap.range T) ≤ S.card := by
    rw [hrange]
    have h := finrank_range_le_card (R := F) (fun k : S => T (v k))
    simpa [Set.finrank, Fintype.card_coe] using h
  have h3 : S.card ≤ Nat.card {p : Fin m × Fin n // A p.1 p.2 ≠ 0} := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe S]
    -- send a non-zero column to one of its non-zero entries
    refine Fintype.card_le_of_injective
      (fun k => ⟨(((hmem k.1).mp k.2).choose, k.1), ((hmem k.1).mp k.2).choose_spec⟩) ?_
    intro k1 k2 hk
    exact Subtype.ext
      (congrArg (fun p : {p : Fin m × Fin n // A p.1 p.2 ≠ 0} => p.1.2) hk)
  omega

/-- 3C.2 -/
theorem exercise_3C_2 [Finite F V] [Finite F W]
    (hV : 0 < finrank F V) (hW : 0 < finrank F W) (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T) = 1 ↔
      ∃ (m n : ℕ) (v : Fin n → V) (w : Fin m → W)
        (hv : IsBasis F v) (hw : IsBasis F w),
        ∀ j k, matrixOf hv hw T j k = 1 := by
  -- => range T has dimension 1, so it is spanned by a single vector w
  -- pick x with T x = w, (at least one x exists T x = a_i w for ai ≠ 0, use x / ai)
  -- take a basis u_1, …, u_p of ker T, and take
  --  v' = x, u_1 + x, …, u_p + x, which likewise has T v' i = w for all i)
  -- one can easily show v' is a basis of ker T, and
  -- with x added it becomes a basis of V.
  --
  -- extend w to a basis of W, so w0 = w
  -- however this just gives a matrix with a single row of 1s and the rest 0s.
  -- to get all ones, construct a new basis of W as follows.
  -- w' 0 = w0 - w1 - ... - wm for the rest of the basis vectors of W
  -- and w' i = wi for i > 0
  -- now T v' i = w 0 = w'0 + w'1 + ... + w'm
  -- one can easily show w' is still a basis
  -- <= T vi = ∑ w k = w' for all i, thus T ∑ ai vi = (∑ ai) w',
  -- so image is spanned by a single vector w', thus dim range T = 1.
  classical
  constructor
  · intro hrank
    -- {lit}`T ≠ 0`, so pick {lit}`x` with {lit}`w0 = T x ≠ 0`; as
    -- {lit}`dim range T = 1`, the range is exactly {lit}`span {w0}`.
    obtain ⟨x, hx⟩ : ∃ x : V, T x ≠ 0 := by
      by_contra hcon
      have h : ∀ y : V, T y = 0 := fun y => not_not.mp fun hy => hcon ⟨y, hy⟩
      have hbot : LinearMap.range T = ⊥ := by
        rw [LinearMap.range_eq_bot]
        ext y
        simp [h y]
      rw [hbot] at hrank
      simp at hrank
    set w0 := T x with hw0def
    have hw0 : w0 ≠ 0 := hx
    have hspan : Submodule.span F {w0} = LinearMap.range T := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_le]
        rintro _ rfl
        exact ⟨x, rfl⟩
      · rw [finrank_span_singleton hw0, hrank]
    -- a basis u of ker T (2.31), viewed as vectors of V; dim ker T = dim V - 1
    obtain ⟨p, u, hu⟩ := LADR.Section_2B.exists_basis (F := F) (V := (LinearMap.ker T))
    have hup : p = finrank F (LinearMap.ker T) :=
      LADR.Section_2C.isBasis_card_eq_finrank u hu
    have hdim : p + 1 = finrank F V := by
      have h := LADR.Section_3B.finrank_ker_add_finrank_range T
      omega
    have huV : LinearIndependent F (fun i => ((u i : V))) :=
      hu.1.map' (LinearMap.ker T).subtype
        (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
    -- v' = x, u_1 + x, …, u_p + x, so that T v'ₖ = w0 for every k
    set vv : Fin (p + 1) → V := Fin.cons x (fun i => (u i : V) + x) with hvv
    have hTvv : ∀ k, T (vv k) = w0 := by
      intro k
      refine Fin.cases ?_ ?_ k
      · simp [hvv, hw0def]
      · intro i
        have hui : T (u i : V) = 0 := LinearMap.mem_ker.mp (u i).2
        simp [hvv, hui, hw0def]
    -- v' is linearly independent: applying T to a relation ∑ cₖ v'ₖ = 0 gives
    -- (∑ cₖ) w0 = 0, hence ∑ cₖ = 0; the x-terms then cancel and the relation
    -- becomes a relation on the basis u of ker T.
    have hvvLI : LinearIndependent F vv := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hT : (∑ k, c k) • w0 = 0 := by
        have h := congrArg T hc
        rw [map_sum] at h
        simpa [hTvv, ← Finset.sum_smul] using h
      have hsum0 : (∑ k, c k) = 0 := by
        rcases smul_eq_zero.mp hT with h | h
        · exact h
        · exact absurd h hw0
      have hexp : ∑ k, c k • vv k
          = (∑ k, c k) • x + ∑ i : Fin p, c i.succ • (u i : V) := by
        rw [Fin.sum_univ_succ (fun k => c k • vv k), Fin.sum_univ_succ c, add_smul,
          Finset.sum_smul]
        simp only [hvv, Fin.cons_zero, Fin.cons_succ, smul_add]
        rw [Finset.sum_add_distrib]
        abel
      rw [hexp, hsum0, zero_smul, zero_add] at hc
      have hcs : ∀ i : Fin p, c i.succ = 0 :=
        Fintype.linearIndependent_iff.mp huV _ hc
      intro k
      refine Fin.cases ?_ ?_ k
      · have hz : ∑ k, c k = c 0 + ∑ i : Fin p, c i.succ := Fin.sum_univ_succ c
        rw [hsum0] at hz
        simp [hcs] at hz
        exact hz.symm
      · exact hcs
    -- a linearly independent list of length dim V is a basis (2.38)
    have hvvBasis : IsBasis F vv :=
      LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq vv hvvLI hdim
    -- extend w0 to a basis b of W (2.32), with b 0 = w0
    have hli1 : LinearIndependent F ![w0] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      fin_cases i
      have hg0 : g 0 • w0 = 0 := by simpa using hg
      rcases smul_eq_zero.mp hg0 with h | h
      · exact h
      · exact absurd h hw0
    obtain ⟨q, b, hq1, hb, hb0⟩ :=
      LADR.Section_2B.exists_basis_extending (F := F) ![w0] hli1
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have hb0' : b 0 = w0 := by simpa using hb0 0
    have hbcard : r + 1 = finrank F W := LADR.Section_2C.isBasis_card_eq_finrank b hb
    -- w' 0 = b 0 - b 1 - … - b r and w' i = b i otherwise, so that ∑ⱼ w'ⱼ = w0
    set ww : Fin (r + 1) → W :=
      Fin.cons (w0 - ∑ i : Fin r, b i.succ) (fun i => b i.succ) with hww
    have hwsum : ∑ j, ww j = w0 := by
      rw [Fin.sum_univ_succ]
      simp [hww]
    -- w' spans W, since b 0 = ∑ⱼ w'ⱼ and b i = w' i for i > 0
    have hwwSpans : Spans F ww := by
      have hb_mem : ∀ k : Fin (r + 1), b k ∈ Submodule.span F (Set.range ww) := by
        intro k
        refine Fin.cases ?_ ?_ k
        · rw [hb0', ← hwsum]
          exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨j, rfl⟩
        · intro i
          have hbi : b i.succ = ww i.succ := by simp [hww]
          rw [hbi]
          exact Submodule.subset_span ⟨i.succ, rfl⟩
      show Submodule.span F (Set.range ww) = ⊤
      rw [eq_top_iff, ← hb.2, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hb_mem k
    -- a spanning list of length dim W is a basis (2.42)
    have hwwBasis : IsBasis F ww :=
      LADR.Section_2C.isBasis_of_spans_of_card_eq ww hwwSpans hbcard
    refine ⟨r + 1, p + 1, vv, ww, hvvBasis, hwwBasis, ?_⟩
    -- every column of ℳ(T) is the coordinate vector of w0 = ∑ⱼ w'ⱼ, i.e. all 1s
    intro j k
    rw [matrixOf_apply, hTvv k]
    have hrepr : hwwBasis.toModuleBasis.repr w0
        = ∑ j' : Fin (r + 1), Finsupp.single j' (1 : F) := by
      rw [← hwsum, map_sum]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← IsBasis.toModuleBasis_apply hwwBasis j', Module.Basis.repr_self]
    rw [hrepr]
    simp
  · rintro ⟨m, n, v, w, hv, hw, hall⟩
    -- the bases have the lengths of the dimensions, so both are positive
    have hn : n = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v hv
    have hm : m = finrank F W := LADR.Section_2C.isBasis_card_eq_finrank w hw
    -- every T vₖ is the same vector s = ∑ⱼ wⱼ, which is non-zero as w is a basis
    have hTv : ∀ k, T (v k) = ∑ j, w j := by
      intro k
      rw [matrixOf_spec hv hw T k]
      simp [hall]
    have hs : (∑ j, w j) ≠ 0 := by
      intro h
      have hg := Fintype.linearIndependent_iff.mp hw.1 (fun _ => 1) (by simpa using h)
      exact one_ne_zero (hg ⟨0, by omega⟩)
    -- so range T = span {s}, of dimension 1
    have hrange : LinearMap.range T = Submodule.span F {∑ j, w j} := by
      have h1 : LinearMap.range T
          = Submodule.span F (Set.range (fun k => T (v k))) := by
        rw [LinearMap.range_eq_map, ← hv.2, Submodule.map_span, ← Set.range_comp]
        rfl
      have hset : (Set.range (fun k => T (v k))) = {∑ j, w j} := by
        ext y
        simp only [Set.mem_range, Set.mem_singleton_iff]
        constructor
        · rintro ⟨k, rfl⟩
          exact hTv k
        · rintro rfl
          exact ⟨⟨0, by omega⟩, hTv _⟩
      rw [h1, hset]
    rw [hrange]
    exact finrank_span_singleton hs

/-- 3C.3 (a) {lit}`ℳ(S + T) = ℳ(S) + ℳ(T)`. Verifies 3.35. -/
theorem exercise_3C_3a {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W} (hv : IsBasis F v) (hw : IsBasis F w)
    (S T : V →ₗ[F] W) :
    matrixOf hv hw (S + T) = matrixOf hv hw S + matrixOf hv hw T := by
  -- Column {lit}`k` of {lit}`ℳ(S + T)` is *the* coefficient list of
  -- {lit}`(S + T) vₖ` in the basis {lit}`w` (3.31), and by 2.28 such a list is
  -- unique; so it suffices to check that column {lit}`k` of
  -- {lit}`ℳ(S) + ℳ(T)` satisfies the same defining equation.
  ext j k
  have huniq := (LADR.Section_2B.isBasis_iff_unique_combo w).mp hw ((S + T) (v k))
  have h1 : ∑ j, matrixOf hv hw (S + T) j k • w j = (S + T) (v k) :=
    (matrixOf_spec hv hw (S + T) k).symm
  have h2 : ∑ j, (matrixOf hv hw S + matrixOf hv hw T) j k • w j = (S + T) (v k) := by
    -- {lit}`∑ⱼ (A + B)_{j,k} wⱼ = ∑ⱼ A_{j,k} wⱼ + ∑ⱼ B_{j,k} wⱼ = S vₖ + T vₖ`
    have hS := matrixOf_spec hv hw S k
    have hT := matrixOf_spec hv hw T k
    simp only [Matrix.add_apply, add_smul]
    rw [Finset.sum_add_distrib, ← hS, ← hT, LinearMap.add_apply]
  exact congrFun (huniq.unique h1 h2) j

/-- 3C.3 (b) {lit}`ℳ(λT) = λ ℳ(T)`. Verifies 3.38. -/
theorem exercise_3C_3b {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W} (hv : IsBasis F v) (hw : IsBasis F w)
    (lam : F) (T : V →ₗ[F] W) :
    matrixOf hv hw (lam • T) = lam • matrixOf hv hw T := by
  -- Same argument: {lit}`λ ℳ(T)` satisfies the equation (3.31) that defines
  -- {lit}`ℳ(λT)` column by column, and 2.28 makes those coefficients unique.
  ext j k
  have huniq := (LADR.Section_2B.isBasis_iff_unique_combo w).mp hw ((lam • T) (v k))
  have h1 : ∑ j, matrixOf hv hw (lam • T) j k • w j = (lam • T) (v k) :=
    (matrixOf_spec hv hw (lam • T) k).symm
  have h2 : ∑ j, (lam • matrixOf hv hw T) j k • w j = (lam • T) (v k) := by
    -- {lit}`∑ⱼ (λ A)_{j,k} wⱼ = λ ∑ⱼ A_{j,k} wⱼ = λ (T vₖ)`
    have hT := matrixOf_spec hv hw T k
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul]
    rw [← Finset.smul_sum, ← hT, LinearMap.smul_apply]
  exact congrFun (huniq.unique h1 h2) j

/-- The basis {lit}`x, x², x³, 1` of {lit}`𝒫₃(ℝ)` used in exercise 3C.4. -/
noncomputable def exercise_3C_4_v : Fin 4 → Polynomial.degreeLT ℝ 4 :=
  ![Polynomial.degreeLT.basis ℝ 4 1, Polynomial.degreeLT.basis ℝ 4 2,
    Polynomial.degreeLT.basis ℝ 4 3, Polynomial.degreeLT.basis ℝ 4 0]

/-- The basis {lit}`1, 2x, 3x²` of {lit}`𝒫₂(ℝ)` used in exercise 3C.4. -/
noncomputable def exercise_3C_4_w : Fin 3 → Polynomial.degreeLT ℝ 3 :=
  ![Polynomial.degreeLT.basis ℝ 3 0, (2 : ℝ) • Polynomial.degreeLT.basis ℝ 3 1,
    (3 : ℝ) • Polynomial.degreeLT.basis ℝ 3 2]

/-- A permutation of the monomial basis is again a basis: it spans and has the
right length (2.42). -/
theorem exercise_3C_4_isBasis_v : IsBasis ℝ exercise_3C_4_v := by
  refine LADR.Section_2C.isBasis_of_spans_of_card_eq _ ?_
    (LADR.Section_2C.isBasis_card_eq_finrank _ (isBasis_polyMono 4))
  show Submodule.span ℝ (Set.range exercise_3C_4_v) = ⊤
  rw [eq_top_iff, ← (isBasis_polyMono (F := ℝ) 4).2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Submodule.subset_span ⟨3, rfl⟩
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩
  · exact Submodule.subset_span ⟨2, rfl⟩

/-- Rescaling the monomial basis by non-zero scalars again gives a basis. -/
theorem exercise_3C_4_isBasis_w : IsBasis ℝ exercise_3C_4_w := by
  have hm1 : Polynomial.degreeLT.basis ℝ 3 1 ∈
      Submodule.span ℝ (Set.range exercise_3C_4_w) := by
    have h : Polynomial.degreeLT.basis ℝ 3 1 = (2⁻¹ : ℝ) • exercise_3C_4_w 1 := by
      simp [exercise_3C_4_w, smul_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  have hm2 : Polynomial.degreeLT.basis ℝ 3 2 ∈
      Submodule.span ℝ (Set.range exercise_3C_4_w) := by
    have h : Polynomial.degreeLT.basis ℝ 3 2 = (3⁻¹ : ℝ) • exercise_3C_4_w 2 := by
      simp [exercise_3C_4_w, smul_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)
  refine LADR.Section_2C.isBasis_of_spans_of_card_eq _ ?_
    (LADR.Section_2C.isBasis_card_eq_finrank _ (isBasis_polyMono 3))
  show Submodule.span ℝ (Set.range exercise_3C_4_w) = ⊤
  rw [eq_top_iff, ← (isBasis_polyMono (F := ℝ) 3).2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact hm1
  · exact hm2

/-- 3C.4 Find bases of {lit}`𝒫₃(ℝ)` and {lit}`𝒫₂(ℝ)` for which the matrix of
the differentiation map is {lit}`[[1,0,0,0],[0,1,0,0],[0,0,1,0]]`. -/
theorem exercise_3C_4 :
    ∃ (v : Fin 4 → Polynomial.degreeLT ℝ 4) (w : Fin 3 → Polynomial.degreeLT ℝ 3)
      (hv : IsBasis ℝ v) (hw : IsBasis ℝ w),
      ∃ (D : Polynomial.degreeLT ℝ 4 →ₗ[ℝ] Polynomial.degreeLT ℝ 3),
        (∀ p, (D p : Polynomial ℝ) = (p : Polynomial ℝ).derivative) ∧
        matrixOf hv hw D = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] := by
  -- the basis vectors of the input have to match the basis of the output after diff.
  -- except the last one going to 0
  -- X -> 1
  -- X^2 -> 2X
  -- X^3 -> 3X^2
  -- 1 -> 0
  -- thus a suitable basis for 𝒫₃(ℝ) is {X, X^2, X^3, 1}
  -- and a suitable basis for 𝒫₂(ℝ) is {1, 2X, 3X^2}
  refine ⟨exercise_3C_4_v, exercise_3C_4_w, exercise_3C_4_isBasis_v,
    exercise_3C_4_isBasis_w, D_3_33, fun p => rfl, ?_⟩
  -- the four derivatives, as claimed in the sketch
  have hD0 : D_3_33 (exercise_3C_4_v 0) = exercise_3C_4_w 0 := by
    apply Subtype.ext
    show Polynomial.derivative (exercise_3C_4_v 0 : Polynomial ℝ)
      = (exercise_3C_4_w 0 : Polynomial ℝ)
    simp [exercise_3C_4_v, exercise_3C_4_w, Polynomial.degreeLT.basis_val]
  have hD1 : D_3_33 (exercise_3C_4_v 1) = exercise_3C_4_w 1 := by
    apply Subtype.ext
    show Polynomial.derivative (exercise_3C_4_v 1 : Polynomial ℝ)
      = (exercise_3C_4_w 1 : Polynomial ℝ)
    simp [exercise_3C_4_v, exercise_3C_4_w, Polynomial.degreeLT.basis_val,
      Polynomial.smul_eq_C_mul, map_ofNat]
    norm_num
  have hD2 : D_3_33 (exercise_3C_4_v 2) = exercise_3C_4_w 2 := by
    apply Subtype.ext
    show Polynomial.derivative (exercise_3C_4_v 2 : Polynomial ℝ)
      = (exercise_3C_4_w 2 : Polynomial ℝ)
    simp [exercise_3C_4_v, exercise_3C_4_w, Polynomial.degreeLT.basis_val,
      Polynomial.smul_eq_C_mul, map_ofNat]
    norm_num
  have hD3 : D_3_33 (exercise_3C_4_v 3) = 0 := by
    apply Subtype.ext
    show Polynomial.derivative (exercise_3C_4_v 3 : Polynomial ℝ) = 0
    simp [exercise_3C_4_v, Polynomial.degreeLT.basis_val]
  -- as in 3C.3, compare with the defining equation of ℳ(D) column by column
  ext j k
  have huniq := (LADR.Section_2B.isBasis_iff_unique_combo exercise_3C_4_w).mp
    exercise_3C_4_isBasis_w (D_3_33 (exercise_3C_4_v k))
  have h1 : ∑ j, matrixOf exercise_3C_4_isBasis_v exercise_3C_4_isBasis_w D_3_33 j k
      • exercise_3C_4_w j = D_3_33 (exercise_3C_4_v k) :=
    (matrixOf_spec exercise_3C_4_isBasis_v exercise_3C_4_isBasis_w D_3_33 k).symm
  have h2 : ∑ j, (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] : Matrix (Fin 3) (Fin 4) ℝ) j k
      • exercise_3C_4_w j = D_3_33 (exercise_3C_4_v k) := by
    fin_cases k
    · simp [Fin.sum_univ_three, hD0]
    · simp [Fin.sum_univ_three, hD1]
    · simp [Fin.sum_univ_three, hD2]
    · simp [Fin.sum_univ_three, hD3]
  exact congrFun (huniq.unique h1 h2) j

/-- 3C.5 -/
theorem exercise_3C_5 [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    ∃ (m n : ℕ) (v : Fin n → V) (w : Fin m → W)
      (hv : IsBasis F v) (hw : IsBasis F w),
      ∀ j k, matrixOf hv hw T j k =
        if (j : ℕ) = (k : ℕ) ∧ j < finrank F (LinearMap.range T) then 1 else 0 := by
  -- take a basis for the ragnge of T - w_i
  -- extend it to a basis of W
  -- for each w_i of the range find a preimage under T - vi
  -- by 3A.4 those vi are linearly independent too
  -- extend those to a basis of V adding a basis of ker T, by rank-nulity this is full basis.
  classical
  -- basis of range T (2.31), viewed as vectors of W, extended to a basis w of W
  obtain ⟨r, wr, hwr⟩ := LADR.Section_2B.exists_basis (F := F) (V := (LinearMap.range T))
  have hr : r = finrank F (LinearMap.range T) :=
    LADR.Section_2C.isBasis_card_eq_finrank wr hwr
  have hwrV : LinearIndependent F (fun i => ((wr i : W))) :=
    hwr.1.map' (LinearMap.range T).subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  obtain ⟨m, w, hrm, hw, hwpre⟩ :=
    LADR.Section_2B.exists_basis_extending (F := F) (fun i => ((wr i : W))) hwrV
  -- a preimage xᵢ of each wrᵢ
  have hpre : ∀ i : Fin r, ∃ y : V, T y = (wr i : W) :=
    fun i => LinearMap.mem_range.mp (wr i).2
  choose xp hxp using hpre
  -- a basis of ker T, which supplies the extension
  obtain ⟨s, u, hu⟩ := LADR.Section_2B.exists_basis (F := F) (V := (LinearMap.ker T))
  have hs : s = finrank F (LinearMap.ker T) :=
    LADR.Section_2C.isBasis_card_eq_finrank u hu
  have hdim : r + s = finrank F V := by
    have h := LADR.Section_3B.finrank_ker_add_finrank_range T
    omega
  have huV : LinearIndependent F (fun i => ((u i : V))) :=
    hu.1.map' (LinearMap.ker T).subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  have hu0 : ∀ i : Fin s, T (u i : V) = 0 := fun i => LinearMap.mem_ker.mp (u i).2
  set vv : Fin (r + s) → V := Fin.append xp (fun i => (u i : V)) with hvv
  -- v = x₁, …, x_r, u₁, …, u_s is linearly independent: applying T to a relation
  -- kills the u-part and leaves a relation on the basis wr, so the x-coefficients
  -- vanish; what is left is a relation on the basis u.
  have hvvLI : LinearIndependent F vv := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_add] at hc
    simp only [hvv, Fin.append_left, Fin.append_right] at hc
    have hT := congrArg T hc
    rw [map_add, map_sum, map_sum] at hT
    simp only [map_smul, hxp, hu0, smul_zero, Finset.sum_const_zero, add_zero,
      map_zero] at hT
    have hc1 : ∀ i : Fin r, c (Fin.castAdd s i) = 0 :=
      Fintype.linearIndependent_iff.mp hwrV _ hT
    simp only [hc1, zero_smul, Finset.sum_const_zero, zero_add] at hc
    have hc2 : ∀ i : Fin s, c (Fin.natAdd r i) = 0 :=
      Fintype.linearIndependent_iff.mp huV _ hc
    intro k
    refine Fin.addCases ?_ ?_ k
    · exact hc1
    · exact hc2
  -- it has length dim V = dim range T + dim ker T (3.21), so it is a basis (2.38)
  have hvvBasis : IsBasis F vv :=
    LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq vv hvvLI hdim
  refine ⟨m, r + s, vv, w, hvvBasis, hw, ?_⟩
  intro j k
  rw [matrixOf_apply, ← hr]
  refine Fin.addCases ?_ ?_ k
  · -- the first r columns: T xᵢ = wrᵢ = wᵢ, so the column is the i-th unit vector
    intro i
    have h1 : T (vv (Fin.castAdd s i)) = w (Fin.castLE hrm i) := by
      rw [hvv]
      simp only [Fin.append_left, hxp, hwpre i]
    rw [h1, ← IsBasis.toModuleBasis_apply hw (Fin.castLE hrm i),
      Module.Basis.repr_self, Finsupp.single_apply]
    have hiff : (Fin.castLE hrm i = j) ↔
        ((j : ℕ) = ((Fin.castAdd s i : Fin (r + s)) : ℕ) ∧ (j : ℕ) < r) := by
      constructor
      · rintro rfl
        exact ⟨rfl, i.isLt⟩
      · rintro ⟨h2, -⟩
        exact (Fin.ext h2.symm)
    simp only [hiff]
  · -- the remaining columns come from ker T, so they are zero
    intro i
    have h1 : T (vv (Fin.natAdd r i)) = 0 := by
      rw [hvv]
      simp only [Fin.append_right, hu0]
    rw [h1, map_zero, Finsupp.coe_zero, Pi.zero_apply, eq_comm, if_neg]
    rintro ⟨h2, h3⟩
    have h4 : ((Fin.natAdd r i : Fin (r + s)) : ℕ) = r + (i : ℕ) := rfl
    omega

/-- 3C.6 — The first column of {lit}`ℳ(T)` can be made either the zero column
or the column {lit}`(1, 0, …, 0)`. -/
theorem exercise_3C_6 [Finite F W] {m : ℕ} (hm : 1 ≤ m)
    {v : Fin m → V} (hv : IsBasis F v) (T : V →ₗ[F] W) :
    ∃ (n : ℕ) (w : Fin n → W) (hw : IsBasis F w),
      column (matrixOf hv hw T) ⟨0, hm⟩ = 0 ∨
      column (matrixOf hv hw T) ⟨0, hm⟩ =
        fun (j : Fin n) (_ : Fin 1) => if (j : ℕ) = 0 then (1 : F) else 0 := by
  -- if T v0 = 0, then take any basis W, and the first column will be zero
  -- if T v0 ≠ 0, then extend T v0 to a basis of W
  -- since T v0 = w0 is a unique representation in that basis, the first column will be (1, 0, …, 0)
  classical
  by_cases h0 : T (v ⟨0, hm⟩) = 0
  · -- any basis of W does: the first column is the coordinate list of 0
    obtain ⟨n, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
    refine ⟨n, w, hw, Or.inl ?_⟩
    ext j i
    show matrixOf hv hw T j ⟨0, hm⟩ = 0
    rw [matrixOf_apply, h0]
    simp
  · -- extend T v₀ to a basis of W (2.32), with w₀ = T v₀
    have hli1 : LinearIndependent F ![T (v ⟨0, hm⟩)] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      fin_cases i
      have hg0 : g 0 • T (v ⟨0, hm⟩) = 0 := by simpa using hg
      rcases smul_eq_zero.mp hg0 with h | h
      · exact h
      · exact absurd h h0
    obtain ⟨n, w, hn1, hw, hw0⟩ :=
      LADR.Section_2B.exists_basis_extending (F := F) ![T (v ⟨0, hm⟩)] hli1
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    have hw0' : w 0 = T (v ⟨0, hm⟩) := by simpa using hw0 0
    refine ⟨r + 1, w, hw, Or.inr ?_⟩
    ext j i
    show matrixOf hv hw T j ⟨0, hm⟩ = if (j : ℕ) = 0 then (1 : F) else 0
    rw [matrixOf_apply, ← hw0', ← IsBasis.toModuleBasis_apply hw 0,
      Module.Basis.repr_self, Finsupp.single_apply]
    have hiff : ((0 : Fin (r + 1)) = j) ↔ (j : ℕ) = 0 := by
      constructor
      · intro h; rw [← h]; rfl
      · intro h; exact Fin.ext h.symm
    simp only [hiff]

/-- 3C.7 — The first row of {lit}`ℳ(T)` can be made either the zero row or
the row {lit}`(1, 0, …, 0)`. -/
theorem exercise_3C_7 [Finite F V] {n : ℕ} (hn : 1 ≤ n)
    {w : Fin n → W} (hw : IsBasis F w) (T : V →ₗ[F] W) :
    ∃ (m : ℕ) (v : Fin m → V) (hv : IsBasis F v),
      row (matrixOf hv hw T) ⟨0, hn⟩ = 0 ∨
      row (matrixOf hv hw T) ⟨0, hn⟩ =
        fun (_ : Fin 1) (k : Fin m) => if (k : ℕ) = 0 then (1 : F) else 0 := by
  -- look for a vector v s.t. T v = ∑ c_i w_i, where c0 ≠ 0,
  -- if not such v exists, then take any basis of V, and by contra,
  -- for each vi, T vi will have zero w0 in it's 0 coordinate
  -- else, take that vector v, extend v0 = v / c0 to a basis of V,
  -- it will have 1 in the first row.
  -- elsewhere if T vi has a nonzero w0 component = ci,
  -- modify the basis v' i = v i - ci v0
  -- one can easily show that this is still a basis
  classical
  -- start from any basis and record the w₀-coordinate cₖ of each T vₖ
  obtain ⟨m, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
  by_cases hzero : ∀ k, hw.toModuleBasis.repr (T (v k)) ⟨0, hn⟩ = 0
  · -- no such vector: this basis already has a zero first row
    refine ⟨m, v, hv, Or.inl ?_⟩
    ext i k
    show matrixOf hv hw T ⟨0, hn⟩ k = 0
    rw [matrixOf_apply]
    exact hzero k
  · push Not at hzero
    obtain ⟨k0, hk0⟩ := hzero
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by have := k0.isLt; omega⟩
    -- swap that vector into position 0; a reindexed basis is still a basis
    set σ : Fin (p + 1) ≃ Fin (p + 1) := Equiv.swap 0 k0 with hσ
    set v1 : Fin (p + 1) → V := v ∘ σ with hv1def
    have hv1 : IsBasis F v1 := by
      refine ⟨hv.1.comp (⇑σ) σ.injective, ?_⟩
      show Submodule.span F (Set.range v1) = ⊤
      have hrange : Set.range v1 = Set.range v := by
        rw [hv1def, Set.range_comp, σ.range_eq_univ, Set.image_univ]
      rw [hrange]
      exact hv.2
    set c : Fin (p + 1) → F := fun k => hw.toModuleBasis.repr (T (v1 k)) ⟨0, hn⟩
      with hcdef
    have hc : ∀ k, hw.toModuleBasis.repr (T (v1 k)) ⟨0, hn⟩ = c k := fun _ => rfl
    have hc0 : c 0 ≠ 0 := by
      have h : v1 0 = v k0 := by simp [hv1def, hσ]
      show hw.toModuleBasis.repr (T (v1 0)) ⟨0, hn⟩ ≠ 0
      rw [h]
      exact hk0
    set a : F := (c 0)⁻¹ with ha
    have hac : a * c 0 = 1 := inv_mul_cancel₀ hc0
    -- v'₀ = v₀ / c₀, and v'ᵢ = vᵢ - cᵢ v'₀ for i > 0
    set v2 : Fin (p + 1) → V :=
      Fin.cons (a • v1 0) (fun i => v1 i.succ - (c i.succ * a) • v1 0) with hv2def
    have hv10 : v1 0 = c 0 • v2 0 := by
      rw [hv2def, Fin.cons_zero, smul_smul, mul_comm, hac, one_smul]
    -- v' spans (each vₖ is recovered from it) and has length dim V, so it is a
    -- basis by 2.42
    have hspan : Spans F v2 := by
      have hmem : ∀ k, v1 k ∈ Submodule.span F (Set.range v2) := by
        intro k
        refine Fin.cases ?_ ?_ k
        · rw [hv10]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
        · intro i
          have h : v1 i.succ = v2 i.succ + c i.succ • v2 0 := by
            have h1 : v2 i.succ = v1 i.succ - (c i.succ * a) • v1 0 := by
              rw [hv2def, Fin.cons_succ]
            rw [h1, hv10, smul_smul, mul_assoc, hac, mul_one]
            abel
          rw [h]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨i.succ, rfl⟩)
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      show Submodule.span F (Set.range v2) = ⊤
      rw [eq_top_iff, ← hv1.2, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hmem k
    have hcard : p + 1 = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v1 hv1
    have hv2basis : IsBasis F v2 :=
      LADR.Section_2C.isBasis_of_spans_of_card_eq v2 hspan hcard
    refine ⟨p + 1, v2, hv2basis, Or.inr ?_⟩
    ext i k
    show matrixOf hv2basis hw T ⟨0, hn⟩ k = if (k : ℕ) = 0 then (1 : F) else 0
    rw [matrixOf_apply]
    refine Fin.cases ?_ ?_ k
    · -- the first entry is c₀ / c₀ = 1
      have h0 : v2 0 = a • v1 0 := by rw [hv2def, Fin.cons_zero]
      rw [h0]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, hc]
      simpa using hac
    · -- the others are cᵢ - cᵢ (c₀ / c₀) = 0
      intro i
      have h1 : v2 i.succ = v1 i.succ - (c i.succ * a) • v1 0 := by
        rw [hv2def, Fin.cons_succ]
      rw [h1]
      simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
        smul_eq_mul, hc]
      rw [mul_assoc, hac, mul_one, sub_self]
      simp

/-- 3C.8 Row version of 3.48: {lit}`(AB)_{j,·} = A_{j,·} B`. -/
theorem exercise_3C_8 {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F) (j : Fin m) :
    row (A * B) j = row A j * B := by rfl

/-- 3C.9 Row version of 3.50: a row times a matrix is a linear combination of
the rows of the matrix. -/
theorem exercise_3C_9 {n p : ℕ}
    (a : Matrix (Fin 1) (Fin n) F) (B : Matrix (Fin n) (Fin p) F) :
    a * B = ∑ r, a 0 r • row B r := by
  ext i j
  -- expand definitions
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, row]

/-- 3C.10 -/
theorem exercise_3C_10 :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  -- use [0 1, 0 0] and [1 1, 1 0]
  refine ⟨!![0, 1; 0, 0], !![1, 1; 1, 0], ?_⟩
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- 3C.11 (a) Left distributivity. -/
@[avoiding Matrix.mul_add]
theorem exercise_3C_11a {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F)
    (B C : Matrix (Fin n) (Fin p) F) :
    A * (B + C) = A * B + A * C := by
  -- translate into linear transformation statement
  -- ((A * (B + C)) x = A ((B + C) x) = A (B x + C x) = A (B x) + A (C x) = (A * B + A * C) x
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, map_add, map_add, Matrix.toLin'_mul, Matrix.toLin'_mul,
    LinearMap.comp_add]

/-- 3C.11 (b) Right distributivity. -/
@[avoiding Matrix.add_mul]
theorem exercise_3C_11b {m n p : ℕ} (D E : Matrix (Fin m) (Fin n) F)
    (F' : Matrix (Fin n) (Fin p) F) :
    (D + E) * F' = D * F' + E * F' := by
  -- translate into linear transformation statement
  -- ((D + E) F') x = (D + E) (F' x) = D (F' x) + E (F' x) = (D F' + E F') x
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, map_add, map_add, Matrix.toLin'_mul, Matrix.toLin'_mul,
    LinearMap.add_comp]

/-- 3C.12 Associativity. -/
@[avoiding Matrix.mul_assoc]
theorem exercise_3C_12 {m n p q : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (C : Matrix (Fin p) (Fin q) F) :
    (A * B) * C = A * (B * C) := by
  -- translate into linear transformation statement
  -- composition of functions is associative
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_mul,
    LinearMap.comp_assoc]

/-- 3C.13 Entry of {lit}`A³` -/
theorem exercise_3C_13 {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (j k : Fin n) :
    (A * A * A) j k = ∑ p, ∑ r, A j p * A p r * A r k := by
  repeat simp only [Matrix.mul_apply]
  -- expand the summations
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

/-- 3C.14 Transposition is a linear map. -/
def exercise_3C_14 (m n : ℕ) :
    Matrix (Fin m) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin m) F where
  toFun A := A.transpose
  map_add' := by
    intro x y
    ext i j
    simp only [Matrix.transpose_apply, Matrix.add_apply]
  map_smul' := by
    intro c x
    ext i j
    simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- 3C.15 {lit}`(A * C)ᵀ = Cᵀ * Aᵀ` -/
theorem exercise_3C_15 {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (C : Matrix (Fin n) (Fin p) F) :
    (A * C).transpose = C.transpose * A.transpose := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  simp [mul_comm]

/-- 3C.16 -/
theorem exercise_3C_16 {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (hA : A ≠ 0) :
    A.rank = 1 ↔
      ∃ (c : Fin m → F) (d : Fin n → F), ∀ j k, A j k = c j * d k := by
  -- (<=) each column i is d_i multiple of the c vector
  -- so the span of all the columns is also just the span of the c vector
  -- so rank is 1 (since A ≠ 0)
  -- (=>) if rank is 1, the span of columns is 1-dimensional span by {c} for
  -- some nonzero c
  -- then each column is a multiple of c, giving each desired d_i
  classical
  rw [matrix_rank_eq_columnRank]
  constructor
  · intro h1
    -- some column is non-zero, and being 1-dimensional the column space is its span
    have hex : ∃ k0, column A k0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hA (by ext j k; exact congrFun (congrFun (hcon k) j) 0)
    obtain ⟨k0, hk0⟩ := hex
    haveI : Module.Finite F (Submodule.span F (Set.range (column A))) :=
      Module.Finite.of_injective (Submodule.span F (Set.range (column A))).subtype
        Subtype.val_injective
    have heq : Submodule.span F {column A k0}
        = Submodule.span F (Set.range (column A)) := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
      · rw [Submodule.span_le]
        rintro _ rfl
        exact Submodule.subset_span ⟨k0, rfl⟩
      · rw [finrank_span_singleton hk0]
        exact h1.symm
    -- so every column is a multiple of column k0, which supplies the dₖ
    have hmul : ∀ k, ∃ t : F, t • column A k0 = column A k := by
      intro k
      have hmem : column A k ∈ Submodule.span F {column A k0} := by
        rw [heq]
        exact Submodule.subset_span ⟨k, rfl⟩
      rwa [Submodule.mem_span_singleton] at hmem
    choose d hd using hmul
    refine ⟨fun j => A j k0, d, ?_⟩
    intro j k
    have h := congrFun (congrFun (hd k) j) 0
    simpa [column, mul_comm] using h.symm
  · rintro ⟨c, d, hcd⟩
    -- each column is dₖ times the single column c, so the column rank is at most 1
    set g : Matrix (Fin m) (Fin 1) F := fun j _ => c j with hg
    have hcolg : ∀ k, column A k = d k • g := by
      intro k
      ext j i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp [column, hg, hcd j k, mul_comm]
    have hsub : Submodule.span F (Set.range (column A)) ≤ Submodule.span F {g} := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      rw [hcolg k]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have hle1 : finrank F (Submodule.span F {g}) ≤ 1 := by
      have hrange : ({g} : Set (Matrix (Fin m) (Fin 1) F))
          = Set.range (fun _ : Fin 1 => g) := by
        ext x
        simp
      rw [hrange]
      have h := finrank_range_le_card (R := F) (fun _ : Fin 1 => g)
      simpa [Set.finrank] using h
    have hle : columnRank A ≤ 1 := le_trans (Submodule.finrank_mono hsub) hle1
    -- and it is not 0, since A ≠ 0
    have hne : columnRank A ≠ 0 := fun h => hA ((columnRank_zero_iff_eq_zero A).mp h)
    omega

/-- 3C.17 -/
theorem exercise_3C_17 {n : ℕ} (T : V →ₗ[F] V)
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v) :
      [Function.Injective T,
       LinearIndependent F (column (matrixOf hu hv T) ·),
       Spans F (column (matrixOf hu hv T) ·),
       Spans F (row (matrixOf hu hv T) ·),
       LinearIndependent F (row (matrixOf hu hv T) ·)].TFAE := by
  -- 1 => 2, assume otherwise, then exists ∑ c_i * column_i = 0, with some c_i ≠ 0
  -- using c_i one can make a vector c ≠ 0, s.t. T(c) = 0, contradicting injectivity.
  -- 2 => 3, dim V vectors in V are linearly independent, so they span V
  -- 3 => 4, col rank = row rank, so rows also span V
  -- 4 => 5, dim V vectors span V, so they must be linearly independent
  -- 5 => 1, by contra, assume we can have ∑ c_i * row_i = 0 with some c_i ≠ 0
  -- then we can construct a non-zero vector s.t. T(c) = 0, using ex 9. contradicting injectivity.
  classical
  have hdimc : finrank F (Matrix (Fin n) (Fin 1) F) = n := by
    rw [finrank_matrix]; ring
  have hdimr : finrank F (Matrix (Fin 1) (Fin n) F) = n := by
    rw [finrank_matrix]; ring
  -- T applied to a combination of the basis u, expanded in the basis v
  have hTsum : ∀ c : Fin n → F,
      T (∑ k, c k • u k) = ∑ j, (∑ k, c k * matrixOf hu hv T j k) • v j := by
    intro c
    rw [map_sum]
    simp only [map_smul, matrixOf_spec hu hv T, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_smul]
  -- T (∑ cₖ uₖ) = 0 exactly when c is a linear relation among the columns
  have hkey : ∀ c : Fin n → F,
      T (∑ k, c k • u k) = 0 ↔ ∑ k, c k • column (matrixOf hu hv T) k = 0 := by
    intro c
    rw [hTsum]
    constructor
    · intro h
      have hz := Fintype.linearIndependent_iff.mp hv.1 _ h
      ext j i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simpa [Matrix.sum_apply, column] using hz j
    · intro h
      have hz : ∀ j, ∑ k, c k * matrixOf hu hv T j k = 0 := by
        intro j
        have hj := congrFun (congrFun h j) 0
        simpa [Matrix.sum_apply, column] using hj
      simp [hz]
  -- 1 ↔ 2: a relation among the columns is exactly a vector killed by T
  have hinj_col : Function.Injective T ↔
      LinearIndependent F (column (matrixOf hu hv T) ·) := by
    constructor
    · intro hT
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have h0 : T (∑ k, c k • u k) = 0 := (hkey c).mpr hc
      have hx : ∑ k, c k • u k = 0 := by
        have h1 : T (∑ k, c k • u k) = T 0 := by rw [h0, map_zero]
        exact hT h1
      exact Fintype.linearIndependent_iff.mp hu.1 _ hx
    · intro hcol
      have hker : ∀ z, T z = 0 → z = 0 := by
        intro z hz
        obtain ⟨c, hc, -⟩ := (LADR.Section_2B.isBasis_iff_unique_combo u).mp hu z
        have h0 : T (∑ k, c k • u k) = 0 := by rw [hc]; exact hz
        have hc0 : ∀ k, c k = 0 :=
          Fintype.linearIndependent_iff.mp hcol _ ((hkey c).mp h0)
        rw [← hc]
        simp [hc0]
      intro x y hxy
      have h : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      exact sub_eq_zero.mp (hker _ h)
  -- spanning is the same as full rank, for the columns and for the rows
  have hcs : Spans F (column (matrixOf hu hv T) ·) →
      columnRank (matrixOf hu hv T) = n := by
    intro h
    show finrank F (Submodule.span F (Set.range (column (matrixOf hu hv T)))) = n
    rw [show Submodule.span F (Set.range (column (matrixOf hu hv T))) = ⊤ from h,
      finrank_top]
    exact hdimc
  have hsc : columnRank (matrixOf hu hv T) = n →
      Spans F (column (matrixOf hu hv T) ·) := by
    intro h
    show Submodule.span F (Set.range (column (matrixOf hu hv T))) = ⊤
    exact LADR.Section_2C.subspace_eq_top_of_finrank_eq _ (by rw [hdimc]; exact h)
  have hrs : Spans F (row (matrixOf hu hv T) ·) → rowRank (matrixOf hu hv T) = n := by
    intro h
    show finrank F (Submodule.span F (Set.range (row (matrixOf hu hv T)))) = n
    rw [show Submodule.span F (Set.range (row (matrixOf hu hv T))) = ⊤ from h,
      finrank_top]
    exact hdimr
  have hsr : rowRank (matrixOf hu hv T) = n → Spans F (row (matrixOf hu hv T) ·) := by
    intro h
    show Submodule.span F (Set.range (row (matrixOf hu hv T))) = ⊤
    exact LADR.Section_2C.subspace_eq_top_of_finrank_eq _ (by rw [hdimr]; exact h)
  tfae_have 1 → 2 := hinj_col.mp
  -- n linearly independent vectors in an n-dimensional space span it (2.38)
  tfae_have 2 → 3 := fun h =>
    (LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq _ h hdimc.symm).2
  -- column rank = row rank (3.57)
  tfae_have 3 → 4 := by
    intro h
    apply hsr
    rw [← columnRank_eq_rowRank]
    exact hcs h
  -- n spanning vectors in an n-dimensional space are independent (2.42)
  tfae_have 4 → 5 := fun h =>
    (LADR.Section_2C.isBasis_of_spans_of_card_eq _ h hdimr.symm).1
  tfae_have 5 → 1 := by
    intro h
    apply hinj_col.mpr
    refine (LADR.Section_2C.isBasis_of_spans_of_card_eq _ ?_ hdimc.symm).1
    apply hsc
    rw [columnRank_eq_rowRank]
    exact hrs ((LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq _ h hdimr.symm).2)
  tfae_finish

end LADR.Section_3C
