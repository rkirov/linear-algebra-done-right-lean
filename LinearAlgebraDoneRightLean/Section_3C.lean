module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.Ring
public import LinearAlgebraDoneRightLean.Section_2A
public import LinearAlgebraDoneRightLean.Section_2B
public import LinearAlgebraDoneRightLean.Section_2C
public import LinearAlgebraDoneRightLean.Section_3A
public import LinearAlgebraDoneRightLean.Section_3B
public import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3C: Matrices
-/

@[expose] public section

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
  have : Module.Finite F U :=
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
  have : Module.Finite F (Submodule.span F (Set.range (column A))) :=
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
      exact (finrank_range_le_card (R := F) (row R)).trans_eq (Fintype.card_fin c)
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
  sorry

/-- 3C.2 -/
theorem exercise_3C_2 [Finite F V] [Finite F W]
    (hV : 0 < finrank F V) (hW : 0 < finrank F W) (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T) = 1 ↔
      ∃ (m n : ℕ) (v : Fin n → V) (w : Fin m → W)
        (hv : IsBasis F v) (hw : IsBasis F w),
        ∀ j k, matrixOf hv hw T j k = 1 := by
  sorry

/-- 3C.3 (a) {lit}`ℳ(S + T) = ℳ(S) + ℳ(T)`. Verifies 3.35. -/
theorem exercise_3C_3a {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W} (hv : IsBasis F v) (hw : IsBasis F w)
    (S T : V →ₗ[F] W) :
    matrixOf hv hw (S + T) = matrixOf hv hw S + matrixOf hv hw T := by
  sorry

/-- 3C.3 (b) {lit}`ℳ(λT) = λ ℳ(T)`. Verifies 3.38. -/
theorem exercise_3C_3b {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W} (hv : IsBasis F v) (hw : IsBasis F w)
    (lam : F) (T : V →ₗ[F] W) :
    matrixOf hv hw (lam • T) = lam • matrixOf hv hw T := by
  sorry

/-- 3C.4 Find bases of {lit}`𝒫₃(ℝ)` and {lit}`𝒫₂(ℝ)` for which the matrix of
the differentiation map is {lit}`[[1,0,0,0],[0,1,0,0],[0,0,1,0]]`. -/
theorem exercise_3C_4 :
    ∃ (v : Fin 4 → Polynomial.degreeLT ℝ 4) (w : Fin 3 → Polynomial.degreeLT ℝ 3)
      (hv : IsBasis ℝ v) (hw : IsBasis ℝ w),
      ∃ (D : Polynomial.degreeLT ℝ 4 →ₗ[ℝ] Polynomial.degreeLT ℝ 3),
        (∀ p, (D p : Polynomial ℝ) = (p : Polynomial ℝ).derivative) ∧
        matrixOf hv hw D = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] := by
  sorry

/-- 3C.5 -/
theorem exercise_3C_5 [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    ∃ (m n : ℕ) (v : Fin n → V) (w : Fin m → W)
      (hv : IsBasis F v) (hw : IsBasis F w),
      ∀ j k, matrixOf hv hw T j k =
        if (j : ℕ) = (k : ℕ) ∧ j < finrank F (LinearMap.range T) then 1 else 0 := by
  sorry

/-- 3C.6 — The first column of {lit}`ℳ(T)` can be made either the zero column
or the column {lit}`(1, 0, …, 0)`. -/
theorem exercise_3C_6 [Finite F W] {m : ℕ} (hm : 1 ≤ m)
    {v : Fin m → V} (hv : IsBasis F v) (T : V →ₗ[F] W) :
    ∃ (n : ℕ) (w : Fin n → W) (hw : IsBasis F w),
      column (matrixOf hv hw T) ⟨0, hm⟩ = 0 ∨
      column (matrixOf hv hw T) ⟨0, hm⟩ =
        fun (j : Fin n) (_ : Fin 1) => if (j : ℕ) = 0 then (1 : F) else 0 := by
  sorry

/-- 3C.7 — The first row of {lit}`ℳ(T)` can be made either the zero row or
the row {lit}`(1, 0, …, 0)`. -/
theorem exercise_3C_7 [Finite F V] {n : ℕ} (hn : 1 ≤ n)
    {w : Fin n → W} (hw : IsBasis F w) (T : V →ₗ[F] W) :
    ∃ (m : ℕ) (v : Fin m → V) (hv : IsBasis F v),
      row (matrixOf hv hw T) ⟨0, hn⟩ = 0 ∨
      row (matrixOf hv hw T) ⟨0, hn⟩ =
        fun (_ : Fin 1) (k : Fin m) => if (k : ℕ) = 0 then (1 : F) else 0 := by
  sorry

/-- 3C.8 Row version of 3.48: {lit}`(AB)_{j,·} = A_{j,·} B`. -/
theorem exercise_3C_8 {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F) (j : Fin m) :
    row (A * B) j = row A j * B := by
  sorry

/-- 3C.9 Row version of 3.50: a row times a matrix is a linear combination of
the rows of the matrix. -/
theorem exercise_3C_9 {n p : ℕ}
    (a : Matrix (Fin 1) (Fin n) F) (B : Matrix (Fin n) (Fin p) F) :
    a * B = ∑ r, a 0 r • row B r := by
  sorry

/-- 3C.10 -/
theorem exercise_3C_10 :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A := by
  sorry

/-- 3C.11 (a) Left distributivity. -/
@[avoiding Matrix.mul_add]
theorem exercise_3C_11a {m n p : ℕ} (A : Matrix (Fin m) (Fin n) F)
    (B C : Matrix (Fin n) (Fin p) F) :
    A * (B + C) = A * B + A * C := by
  sorry

/-- 3C.11 (b) Right distributivity. -/
@[avoiding Matrix.add_mul]
theorem exercise_3C_11b {m n p : ℕ} (D E : Matrix (Fin m) (Fin n) F)
    (F' : Matrix (Fin n) (Fin p) F) :
    (D + E) * F' = D * F' + E * F' := by
  sorry

/-- 3C.12 Associativity. -/
@[avoiding Matrix.mul_assoc]
theorem exercise_3C_12 {m n p q : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (B : Matrix (Fin n) (Fin p) F)
    (C : Matrix (Fin p) (Fin q) F) :
    (A * B) * C = A * (B * C) := by
  sorry

/-- 3C.13 Entry of {lit}`A³` -/
theorem exercise_3C_13 {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (j k : Fin n) :
    (A * A * A) j k = ∑ p, ∑ r, A j p * A p r * A r k := by
  sorry

/-- 3C.14 Transposition is a linear map. -/
def exercise_3C_14 (m n : ℕ) :
    Matrix (Fin m) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin m) F where
  toFun A := A.transpose
  map_add' := by sorry
  map_smul' := by sorry

/-- 3C.15 {lit}`(A * C)ᵀ = Cᵀ * Aᵀ` -/
theorem exercise_3C_15 {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) F) (C : Matrix (Fin n) (Fin p) F) :
    (A * C).transpose = C.transpose * A.transpose := by
  sorry

/-- 3C.16 -/
theorem exercise_3C_16 {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) (hA : A ≠ 0) :
    A.rank = 1 ↔
      ∃ (c : Fin m → F) (d : Fin n → F), ∀ j k, A j k = c j * d k := by
  sorry

/-- 3C.17 -/
theorem exercise_3C_17 {n : ℕ} (T : V →ₗ[F] V)
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v) :
      [Function.Injective T,
       LinearIndependent F (column (matrixOf hu hv T) ·),
       Spans F (column (matrixOf hu hv T) ·),
       Spans F (row (matrixOf hu hv T) ·),
       LinearIndependent F (row (matrixOf hu hv T) ·)].TFAE := by
  sorry

end LADR.Section_3C
