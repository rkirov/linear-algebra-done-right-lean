module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.Data.List.TFAE
public import LinearAlgebraDoneRightLean.Section_5A
public import LinearAlgebraDoneRightLean.Section_5D
public import LinearAlgebraDoneRightLean.Section_6B
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linter.Style
public import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7A: Self-Adjoint and Normal Operators
-/

@[expose] public section

namespace LADR

/-- Axler's {lit}`T*`: postfix notation {lit}`T†` for {name}`LinearMap.adjoint`
(following mathlib's {lit}`†` for {name}`ContinuousLinearMap.adjoint`; a postfix
{lit}`*` would clash with multiplication, as {lit}`T* w` parses as {lit}`T * w`).
Scoped to {lit}`LADR`, so it is active in every section file. -/
scoped postfix:max "†" => LinearMap.adjoint

open Lean PrettyPrinter Delaborator SubExpr in
/-- Pretty-print {lit}`LinearMap.adjoint T` as {lit}`T†` (and {lit}`T† w` when
applied), so goals display Axler's notation. -/
@[scoped delab app.DFunLike.coe]
meta def delabAdjoint : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  guard <| e.getAppNumArgs ≥ 6
  guard <| (e.getArg! 4).isAppOf ``LinearMap.adjoint
  let T ← withNaryArg 5 delab
  let base ← `($T†)
  let rest ← (List.range (e.getAppNumArgs - 6)).mapM fun i => withNaryArg (6 + i) delab
  return Syntax.mkApp base rest.toArray

end LADR

namespace LADR.Section_7A

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate Matrix
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)

/-! From now on (Axler's standing assumption for Chapters 7–9) {lit}`V` and
{lit}`W` are finite-dimensional inner product spaces over {lit}`𝕜` ({lit}`ℝ` or
{lit}`ℂ`). Finite-dimensionality is what lets mathlib form the adjoint. -/

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]

/-! # Adjoints -/

/-! 7.1 Definition: adjoint, {lit}`T*`

For {lit}`T ∈ ℒ(V, W)` and {lit}`w ∈ W`, the map {lit}`v ↦ ⟨Tv, w⟩` is a linear
functional on {lit}`V` (mathlib: {lit}`v ↦ ⟪w, T v⟫`, linear in the second slot).
By the Riesz representation theorem (6.42, {name}`Section_6B.riesz_representation`)
there is a unique vector {lit}`T*w ∈ V` representing it, so that
{lit}`⟨Tv, w⟩ = ⟨v, T*w⟩` for all {lit}`v`. We first follow Axler literally and
define {lit}`T*` this way ({lit}`adjointRiesz`), then show it agrees with
mathlib's {name}`LinearMap.adjoint` ({lit}`adjointRiesz_eq_adjoint`); from then
on we use the mathlib map, whose defining property is
{name}`LinearMap.adjoint_inner_right`. -/

/-- Axler's definition 7.1: {lit}`T*w` is the Riesz vector (6.42) of the linear
functional {lit}`v ↦ ⟨Tv, w⟩` on {lit}`V`. -/
noncomputable def adjointRiesz (T : V →ₗ[𝕜] W) (w : W) : V :=
  (Section_6B.riesz_representation ((innerₛₗ 𝕜 w).comp T)).exists.choose

omit [FiniteDimensional 𝕜 W] in
/-- The Riesz property of {name}`adjointRiesz`, in mathlib's slot order:
{lit}`⟪w, T v⟫ = ⟪T*w, v⟫`. -/
theorem adjointRiesz_spec (T : V →ₗ[𝕜] W) (w : W) (v : V) :
    ⟪w, T v⟫_𝕜 = ⟪adjointRiesz T w, v⟫_𝕜 :=
  (Section_6B.riesz_representation ((innerₛₗ 𝕜 w).comp T)).exists.choose_spec v

omit [FiniteDimensional 𝕜 W] in
/-- The defining property of {name}`adjointRiesz`: {lit}`⟨Tv, w⟩ = ⟨v, T*w⟩`. -/
theorem inner_adjointRiesz (T : V →ₗ[𝕜] W) (v : V) (w : W) :
    ⟪T v, w⟫_𝕜 = ⟪v, adjointRiesz T w⟫_𝕜 := by
  rw [← inner_conj_symm, adjointRiesz_spec, inner_conj_symm]

/-- Axler's {lit}`T*` (via Riesz) is mathlib's {name}`LinearMap.adjoint`: both
{lit}`T*w` and {lit}`T† w` (mathlib) represent the functional
{lit}`v ↦ ⟨Tv, w⟩`, so they coincide by the uniqueness half of 6.42. -/
theorem adjointRiesz_eq_adjoint (T : V →ₗ[𝕜] W) (w : W) :
    adjointRiesz T w = T† w :=
  (Section_6B.riesz_representation ((innerₛₗ 𝕜 w).comp T)).unique
    (adjointRiesz_spec T w) fun v => (LinearMap.adjoint_inner_left T v w).symm

theorem adjoint_inner (T : V →ₗ[𝕜] W) (v : V) (w : W) :
    ⟪T v, w⟫_𝕜 = ⟪v, T† w⟫_𝕜 :=
  (LinearMap.adjoint_inner_right T v w).symm

/-! 7.2 Example: adjoint of a linear map from {lit}`ℝ³` to {lit}`ℝ²`

For {lit}`T(x₁, x₂, x₃) = (x₂ + 3x₃, 2x₁)` the adjoint is
{lit}`T*(y₁, y₂) = (2y₂, y₁, 3y₁)`. -/

example (T : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), T x = !₂[x 1 + 3 * x 2, 2 * x 0])
    (y : EuclideanSpace ℝ (Fin 2)) :
    T† y = !₂[2 * y 1, y 0, 3 * y 0] := by
  refine ext_inner_left ℝ fun x => ?_
  rw [← adjoint_inner, hT]
  simp [PiLp.inner_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

/-! 7.3 Example: for fixed {lit}`u ∈ V`, {lit}`x ∈ W`, the map {lit}`T v = ⟨v, u⟩ x`
has adjoint {lit}`T* w = ⟨w, x⟩ u` (reading Axler's {lit}`⟨v, u⟩` as {lit}`⟪u, v⟫`). -/

example (u x : V) (T : V →ₗ[𝕜] V) (hT : ∀ v, T v = ⟪u, v⟫_𝕜 • x) (w : V) :
    T† w = ⟪x, w⟫_𝕜 • u := by
  refine ext_inner_left 𝕜 fun v => ?_
  rw [← adjoint_inner, hT, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

/-! 7.4 The adjoint of a linear map is a linear map: {lit}`T* ∈ ℒ(W, V)`. In
mathlib {name}`LinearMap.adjoint` is already a (conjugate-linear) isomorphism of
linear maps, so {lit}`T*` is a {lit}`LinearMap` by construction. -/

noncomputable example (T : V →ₗ[𝕜] W) : W →ₗ[𝕜] V := T†

/-- The additivity that Axler's proof of 7.4 verifies: {lit}`T*(w₁ + w₂) = T*w₁ + T*w₂`. -/
theorem adjoint_apply_add (T : V →ₗ[𝕜] W) (w₁ w₂ : W) :
    T† (w₁ + w₂) = T† w₁ + T† w₂ :=
  map_add _ _ _

/-- The homogeneity that Axler's proof of 7.4 verifies: {lit}`T*(λw) = λ T*w`. -/
theorem adjoint_apply_smul (T : V →ₗ[𝕜] W) (a : 𝕜) (w : W) :
    T† (a • w) = a • T† w :=
  map_smul _ _ _

/-! 7.5 Properties of the adjoint

Following Axler, each identity is checked by pairing both sides with an
arbitrary {lit}`v` and moving maps across the inner product with
{name}`adjoint_inner`; {name}`ext_inner_left` then identifies the vectors. -/

/-- (a) {lit}`(S + T)* = S* + T*`:
{lit}`⟨v, (S+T)*w⟩ = ⟨Sv, w⟩ + ⟨Tv, w⟩ = ⟨v, S*w⟩ + ⟨v, T*w⟩ = ⟨v, S*w + T*w⟩`. -/
theorem adjoint_add (S T : V →ₗ[𝕜] W) :
    (S + T)† = S† + T† := by
  ext w
  refine ext_inner_left 𝕜 fun v => ?_
  rw [← adjoint_inner, LinearMap.add_apply, LinearMap.add_apply, inner_add_left,
    inner_add_right, adjoint_inner, adjoint_inner]

/-- (b) {lit}`(λT)* = conj λ · T*` (the map {lit}`T ↦ T*` is conjugate-linear):
{lit}`⟨v, (λT)*w⟩ = ⟨λTv, w⟩ = λ⟨v, T*w⟩ = ⟨v, conj λ · T*w⟩`. -/
theorem adjoint_smul (a : 𝕜) (T : V →ₗ[𝕜] W) :
    (a • T)† = conj a • T† := by
  ext w
  refine ext_inner_left 𝕜 fun v => ?_
  rw [← adjoint_inner, LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, adjoint_inner]

/-- (c) {lit}`(T*)* = T`:
{lit}`⟨w, (T*)*v⟩ = ⟨T*w, v⟩ = conj ⟨v, T*w⟩ = conj ⟨Tv, w⟩ = ⟨w, Tv⟩`. -/
theorem adjoint_adjoint (T : V →ₗ[𝕜] W) :
    T†† = T := by
  ext v
  refine ext_inner_left 𝕜 fun w => ?_
  rw [← adjoint_inner, ← inner_conj_symm, ← adjoint_inner, inner_conj_symm]

/-- (d) {lit}`(ST)* = T* S*`:
{lit}`⟨v, (ST)*u⟩ = ⟨S(Tv), u⟩ = ⟨Tv, S*u⟩ = ⟨v, T*(S*u)⟩`. -/
theorem adjoint_comp {U : Type*} [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
    [FiniteDimensional 𝕜 U] (S : W →ₗ[𝕜] U) (T : V →ₗ[𝕜] W) :
    (S ∘ₗ T)† = T† ∘ₗ S† := by
  ext u
  refine ext_inner_left 𝕜 fun v => ?_
  rw [← adjoint_inner, LinearMap.comp_apply, LinearMap.comp_apply, adjoint_inner,
    adjoint_inner]

/-- (e) {lit}`I* = I`: {lit}`⟨v, I*u⟩ = ⟨Iv, u⟩ = ⟨v, u⟩`. -/
theorem adjoint_id : (LinearMap.id : V →ₗ[𝕜] V)† = LinearMap.id := by
  ext u
  refine ext_inner_left 𝕜 fun v => ?_
  rw [← adjoint_inner, LinearMap.id_apply, LinearMap.id_apply]

/-- (f) If {lit}`T` is invertible with inverse {lit}`S`, then {lit}`T*` is
invertible with inverse {lit}`S* = (T⁻¹)*`. -/
theorem adjoint_inv (T : V →ₗ[𝕜] W) (S : W →ₗ[𝕜] V)
    (h₁ : S ∘ₗ T = LinearMap.id) (h₂ : T ∘ₗ S = LinearMap.id) :
    T† ∘ₗ S† = LinearMap.id ∧
      S† ∘ₗ T† = LinearMap.id :=
  ⟨by rw [← adjoint_comp, h₁, adjoint_id], by rw [← adjoint_comp, h₂, adjoint_id]⟩

/-! 7.6 Null space and range of {lit}`T*` -/

/-- (a) {lit}`null T* = (range T)⟂`. -/
theorem ker_adjoint (T : V →ₗ[𝕜] W) :
    LinearMap.ker T† = (LinearMap.range T)ᗮ := by
  ext w
  rw [LinearMap.mem_ker, Submodule.mem_orthogonal]
  constructor
  · intro h u hu
    obtain ⟨v, rfl⟩ := hu
    rw [adjoint_inner, h, inner_zero_right]
  · intro h
    refine ext_inner_left 𝕜 fun v => ?_
    rw [inner_zero_right, ← adjoint_inner]
    exact h (T v) ⟨v, rfl⟩

/-- (b) {lit}`range T* = (null T)⟂`. -/
theorem range_adjoint (T : V →ₗ[𝕜] W) :
    LinearMap.range T† = (LinearMap.ker T)ᗮ :=
  (LinearMap.orthogonal_ker T).symm

/-- (c) {lit}`null T = (range T*)⟂`. -/
theorem ker_eq_orthogonal_range_adjoint (T : V →ₗ[𝕜] W) :
    LinearMap.ker T = (LinearMap.range T†)ᗮ := by
  rw [range_adjoint, Submodule.orthogonal_orthogonal]

/-- (d) {lit}`range T = (null T*)⟂`. -/
theorem range_eq_orthogonal_ker_adjoint (T : V →ₗ[𝕜] W) :
    LinearMap.range T = (LinearMap.ker T†)ᗮ := by
  rw [ker_adjoint, Submodule.orthogonal_orthogonal]

/-! 7.7 Definition: conjugate transpose, {lit}`A*`

The conjugate transpose of an {lit}`m`-by-{lit}`n` matrix {lit}`A` is the
{lit}`n`-by-{lit}`m` matrix with entries {lit}`(A*)ⱼ,ₖ = conj Aₖ,ⱼ`. This is
mathlib's {name}`Matrix.conjTranspose`, written {lit}`Aᴴ`. -/

theorem conjTranspose_apply {m n : Type*} (A : Matrix m n 𝕜) (j : n) (k : m) :
    Aᴴ j k = conj (A k j) :=
  rfl

/-! 7.8 Example: the conjugate transpose of a 2-by-3 matrix. -/

example : (!![(2 : ℂ), 3 + 4 * Complex.I, 7; 6, 5, 8 * Complex.I])ᴴ =
    !![(2 : ℂ), 6; 3 - 4 * Complex.I, 5; 7, -(8 * Complex.I)] := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.conjTranspose_apply, Complex.ext_iff]

/-! 7.9 The matrix of {lit}`T*` equals the conjugate transpose of the matrix of
{lit}`T`, with respect to orthonormal bases of {lit}`V` and {lit}`W`.

Axler's proof: in an orthonormal basis the coefficients of a vector are its
inner products with the basis vectors (6.30), so the {lit}`(k, j)` entry of
{lit}`M(T*)` is {lit}`⟨T* fⱼ, eₖ⟩ = ⟨fⱼ, T eₖ⟩ = conj ⟨T eₖ, fⱼ⟩`, which is
{lit}`conj` of the {lit}`(j, k)` entry of {lit}`M(T)`. In mathlib's slot order
the coefficient of {lit}`v` along {lit}`eₖ` is {lit}`⟪eₖ, v⟫`
({name}`OrthonormalBasis.repr_apply_apply`). -/

theorem toMatrix_adjoint_eq_conjTranspose {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (b : OrthonormalBasis n 𝕜 V) (c : OrthonormalBasis m 𝕜 W)
    (T : V →ₗ[𝕜] W) :
    LinearMap.toMatrix c.toBasis b.toBasis T†
      = (LinearMap.toMatrix b.toBasis c.toBasis T)ᴴ := by
  ext k j
  rw [Matrix.conjTranspose_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    ← adjoint_inner]
  exact (inner_conj_symm _ _).symm

/-! # Self-Adjoint Operators -/

/-! 7.10 Definition: self-adjoint

An operator {lit}`T ∈ ℒ(V)` is *self-adjoint* if {lit}`T = T*`. mathlib's
{name}`IsSelfAdjoint` (in the star ring {lit}`ℒ(V)`, whose star is the adjoint)
captures this; equivalently {name}`LinearMap.IsSymmetric`
({lit}`⟨Tv, w⟩ = ⟨v, Tw⟩`). -/

theorem isSelfAdjoint_iff (T : V →ₗ[𝕜] V) :
    LinearMap.IsSymmetric T ↔ T† = T :=
  LinearMap.isSymmetric_iff_isSelfAdjoint T

omit [FiniteDimensional 𝕜 V] in
theorem isSymmetric_iff_inner (T : V →ₗ[𝕜] V) :
    LinearMap.IsSymmetric T ↔ ∀ v w, ⟪T v, w⟫_𝕜 = ⟪v, T w⟫_𝕜 :=
  Iff.rfl

/-! 7.11 Example: determining whether {lit}`T` is self-adjoint from its matrix.

If the matrix of {lit}`T` with respect to an orthonormal basis of {lit}`𝔽²` is
{lit}`!![2, c; 3, 7]`, then {lit}`T` is self-adjoint if and only if {lit}`c = 3`,
because by 7.9 self-adjointness says the matrix equals its conjugate transpose. -/

example (c : 𝕜) (b : OrthonormalBasis (Fin 2) 𝕜 V) (T : V →ₗ[𝕜] V)
    (hT : LinearMap.toMatrix b.toBasis b.toBasis T = !![2, c; 3, 7]) :
    LinearMap.IsSymmetric T ↔ c = 3 := by
  rw [isSelfAdjoint_iff, ← (LinearMap.toMatrix b.toBasis b.toBasis).injective.eq_iff,
    toMatrix_adjoint_eq_conjTranspose b b, hT]
  constructor
  · intro h
    have := congrFun (congrFun h 0) 1
    simpa using this.symm
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-! 7.12 Eigenvalues of self-adjoint operators are real.

Axler's proof: if {lit}`Tv = λv` with {lit}`v ≠ 0`, compare {lit}`⟨Tv, v⟩` with
{lit}`⟨v, Tv⟩` and cancel {lit}`⟨v, v⟩ ≠ 0`. -/

omit [FiniteDimensional 𝕜 V] in
theorem eigenvalue_real (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) {μ : 𝕜}
    (hμ : HasEigenvalue T μ) : conj μ = μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hTv : T v = μ • v := hv.apply_eq_smul
  have key : conj μ * ⟪v, v⟫_𝕜 = μ * ⟪v, v⟫_𝕜 :=
    calc conj μ * ⟪v, v⟫_𝕜 = ⟪μ • v, v⟫_𝕜 := (inner_smul_left _ _ _).symm
      _ = ⟪T v, v⟫_𝕜 := by rw [hTv]
      _ = ⟪v, T v⟫_𝕜 := hT v v
      _ = ⟪v, μ • v⟫_𝕜 := by rw [hTv]
      _ = μ * ⟪v, v⟫_𝕜 := inner_smul_right _ _ _
  exact mul_right_cancel₀ (inner_self_ne_zero.mpr hv.2) key

/-! 7.13 {lit}`⟨Tv, v⟩ = 0` for all {lit}`v` iff {lit}`T = 0` (over {lit}`ℂ`).

Axler's proof: expand the polarization-style identity that writes
{lit}`⟨Tu, w⟩` as a combination of four terms of the form {lit}`⟨Tv, v⟩`, then
take {lit}`w = Tu`. -/

theorem inner_map_self_eq_zero_iff {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (T : V →ₗ[ℂ] V) :
    (∀ v, ⟪T v, v⟫_ℂ = 0) ↔ T = 0 := by
  constructor
  · intro h
    have key : ∀ u w : V, ⟪T u, w⟫_ℂ = 0 := by
      intro u w
      have e1 := h (u + w)
      have e2 := h (u - w)
      have e3 := h (u + Complex.I • w)
      have e4 := h (u - Complex.I • w)
      simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
        inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_I, h u, h w] at e1 e2 e3 e4
      linear_combination (e1 - e2) / 4 - (e3 - e4) * Complex.I / 4 +
        ((⟪T u, w⟫_ℂ - ⟪T w, u⟫_ℂ) / 2) * Complex.I_sq
    refine LinearMap.ext fun u => ?_
    simpa using inner_self_eq_zero.mp (key u (T u))
  · rintro rfl
    simp

/-! 7.14 On a complex inner product space, {lit}`T` is self-adjoint iff
{lit}`⟨Tv, v⟩` is real for every {lit}`v`.

Axler's proof runs through 7.15, {lit}`⟨T*v, v⟩ = conj ⟨Tv, v⟩`, and then applies
7.13 to {lit}`T − T*`. -/

/-- 7.15 {lit}`⟨T*v, v⟩ = conj ⟨Tv, v⟩`. -/
theorem inner_adjoint_self (T : V →ₗ[𝕜] V) (v : V) :
    ⟪T† v, v⟫_𝕜 = conj ⟪T v, v⟫_𝕜 := by
  rw [LinearMap.adjoint_inner_left, inner_conj_symm]

theorem isSymmetric_iff_inner_real {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    LinearMap.IsSymmetric T ↔ ∀ v, conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ := by
  rw [isSelfAdjoint_iff, ← sub_eq_zero, ← inner_map_self_eq_zero_iff]
  refine forall_congr' fun v => ?_
  rw [LinearMap.sub_apply, inner_sub_left, inner_adjoint_self, sub_eq_zero]

/-! 7.16 A self-adjoint operator with {lit}`⟨Tv, v⟩ = 0` for all {lit}`v` is
{lit}`0` (over both {lit}`ℝ` and {lit}`ℂ`).

Axler's proof expands {lit}`⟨T(u + w), u + w⟩ = 0` (as in 7.17) to get
{lit}`⟨Tu, w⟩ + ⟨Tw, u⟩ = 0`; taking {lit}`w = Tu` and using self-adjointness
turns this into {lit}`2⟨Tu, Tu⟩ = 0`. -/

omit [FiniteDimensional 𝕜 V] in
theorem symmetric_inner_map_self_eq_zero {T : V →ₗ[𝕜] V}
    (hT : LinearMap.IsSymmetric T) : (∀ v, ⟪T v, v⟫_𝕜 = 0) ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h v => by simp [h]⟩
  have key : ∀ u w : V, ⟪T u, w⟫_𝕜 + ⟪T w, u⟫_𝕜 = 0 := by
    intro u w
    have e1 := h (u + w)
    simp only [map_add, inner_add_left, inner_add_right, h u, h w] at e1
    linear_combination e1
  refine LinearMap.ext fun u => ?_
  have h1 := key u (T u)
  rw [hT (T u) u] at h1
  have h2 : ⟪T u, T u⟫_𝕜 = 0 := by linear_combination h1 / 2
  simpa using inner_self_eq_zero.mp h2

/-! # Normal Operators -/

/-! 7.18 Definition: normal

An operator is *normal* if it commutes with its adjoint: {lit}`T T* = T* T`.
This is mathlib's {name}`IsStarNormal` (the star on {lit}`ℒ(V)` being the
adjoint, so {lit}`star T = T*`). -/

example (T : V →ₗ[𝕜] V) : IsStarNormal T ↔ Commute T† T :=
  ⟨fun h => h.star_comm_self, fun h => ⟨h⟩⟩

/-- Every self-adjoint operator is normal. -/
theorem symmetric_isStarNormal {T : V →ₗ[𝕜] V} (hT : LinearMap.IsSymmetric T) :
    IsStarNormal T := by
  have h : IsSelfAdjoint T := by
    show star T = T
    rw [LinearMap.star_eq_adjoint]
    exact (isSelfAdjoint_iff T).mp hT
  exact h.isStarNormal

/-- {lit}`T` is normal iff its adjoint commutes with it (in composition form). -/
theorem normal_iff_comp (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ T† ∘ₗ T = T ∘ₗ T† := by
  rw [isStarNormal_iff, LinearMap.star_eq_adjoint, ← Module.End.mul_eq_comp,
    ← Module.End.mul_eq_comp]
  exact commute_iff_eq _ _

/-- The commutator {lit}`T* T − T T*` is self-adjoint. -/
theorem comm_symmetric (T : V →ₗ[𝕜] V) :
    (T† ∘ₗ T - T ∘ₗ T†).IsSymmetric := by
  refine (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr ?_
  rw [_root_.isSelfAdjoint_iff, LinearMap.star_eq_adjoint]
  simp only [map_sub, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]

/-! 7.19 Example: an operator that is normal but not self-adjoint.

The operator on {lit}`𝔽²` with matrix {lit}`!![2, -3; 3, 2]`, that is
{lit}`T(w, z) = (2w − 3z, 3w + 2z)`, has {lit}`T*(w, z) = (2w + 3z, −3w + 2z)`;
both {lit}`T*T` and {lit}`TT*` are multiplication by 13, yet {lit}`T ≠ T*`. -/

example (T : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2))
    (hT : ∀ v : EuclideanSpace 𝕜 (Fin 2), T v = !₂[2 * v 0 - 3 * v 1, 3 * v 0 + 2 * v 1]) :
    IsStarNormal T ∧ ¬ LinearMap.IsSymmetric T := by
  have hadj : ∀ w : EuclideanSpace 𝕜 (Fin 2),
      T† w = !₂[2 * w 0 + 3 * w 1, -(3 * w 0) + 2 * w 1] := by
    intro w
    refine ext_inner_left 𝕜 fun v => ?_
    rw [← adjoint_inner, hT]
    simp [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, map_add, map_sub, map_mul,
      map_ofNat]
    ring
  refine ⟨?_, ?_⟩
  · rw [normal_iff_comp]
    ext v i
    fin_cases i <;> simp [LinearMap.comp_apply, hT, hadj] <;> ring
  · intro h
    have h1 : T† (!₂[1, 0] : EuclideanSpace 𝕜 (Fin 2)) 1
        = T (!₂[1, 0] : EuclideanSpace 𝕜 (Fin 2)) 1 := by
      rw [(isSelfAdjoint_iff T).mp h]
    rw [hadj, hT] at h1
    norm_num at h1

/-- 7.20 {lit}`T` is normal if and only if {lit}`‖Tv‖ = ‖T*v‖` for every {lit}`v`. -/
theorem normal_iff_norm (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ ∀ v, ‖T v‖ = ‖T† v‖ := by
  have key : ∀ v, ⟪(T† ∘ₗ T - T ∘ₗ T†) v, v⟫_𝕜
      = (‖T v‖ : 𝕜) ^ 2 - (‖T† v‖ : 𝕜) ^ 2 := by
    intro v
    have e2 : ⟪T (T† v), v⟫_𝕜 = (‖T† v‖ : 𝕜) ^ 2 := by
      rw [← LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left,
      LinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K, e2]
  rw [normal_iff_comp, ← sub_eq_zero, ← (comm_symmetric T).inner_map_self_eq_zero]
  constructor
  · intro h v
    have hk := key v
    rw [h v] at hk
    have h4 : (‖T v‖ : 𝕜) ^ 2 = (‖T† v‖ : 𝕜) ^ 2 := sub_eq_zero.mp hk.symm
    have h3 : ‖T v‖ ^ 2 = ‖T† v‖ ^ 2 := by exact_mod_cast h4
    rw [← Real.sqrt_sq (norm_nonneg (T v)),
      ← Real.sqrt_sq (norm_nonneg (T† v)), h3]
  · intro h v
    rw [key v, h v, sub_self]

/-! 7.21 Range, null space, and eigenvectors of a normal operator -/

/-- (a) {lit}`null T = null T*`. -/
theorem ker_eq_ker_adjoint {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) :
    LinearMap.ker T = LinearMap.ker T† := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← norm_eq_zero,
    ← norm_eq_zero (a := T† v), (normal_iff_norm T).mp hT v]

/-- (b) {lit}`range T = range T*`. -/
theorem range_eq_range_adjoint {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) :
    LinearMap.range T = LinearMap.range T† := by
  have h2 : (LinearMap.range T)ᗮ = (LinearMap.range T†)ᗮ := by
    rw [← ker_adjoint, ← ker_adjoint, LinearMap.adjoint_adjoint, ← ker_eq_ker_adjoint hT]
  rw [← Submodule.orthogonal_orthogonal (LinearMap.range T), h2,
    Submodule.orthogonal_orthogonal]

/-- (c) {lit}`V = null T ⊕ range T`. -/
theorem isCompl_ker_range {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) :
    IsCompl (LinearMap.ker T) (LinearMap.range T) := by
  have h1 : (LinearMap.range T)ᗮ = LinearMap.ker T := by
    rw [← ker_adjoint, ← ker_eq_ker_adjoint hT]
  have := (LinearMap.range T).isCompl_orthogonal
  rw [h1] at this
  exact this.symm

/-- The adjoint of the identity is the identity. -/
theorem adjoint_one : (1 : V →ₗ[𝕜] V)† = 1 := by
  rw [Module.End.one_eq_id, LinearMap.adjoint_id]

/-- (d) {lit}`T − λI` is normal for every {lit}`λ`. -/
theorem sub_smul_normal {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (μ : 𝕜) :
    IsStarNormal (T - μ • (1 : V →ₗ[𝕜] V)) := by
  have hstar : star (T - μ • (1 : V →ₗ[𝕜] V)) = star T - conj μ • 1 := by
    rw [LinearMap.star_eq_adjoint, LinearMap.star_eq_adjoint, map_sub,
      LinearEquiv.map_smulₛₗ, adjoint_one]
  refine ⟨?_⟩
  rw [hstar]
  refine Commute.sub_right
    (Commute.sub_left hT.star_comm_self ((Commute.one_left T).smul_left (conj μ))) ?_
  exact ((Commute.one_left (star T - conj μ • (1 : V →ₗ[𝕜] V))).smul_left μ).symm

/-- (e) For normal {lit}`T`, {lit}`Tv = λv ⟺ T*v = conj λ · v`. -/
theorem eigenvector_adjoint {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (v : V) (μ : 𝕜) :
    T v = μ • v ↔ T† v = (conj μ) • v := by
  have hnorm := (normal_iff_norm _).mp (sub_smul_normal hT μ) v
  have hadj : (T - μ • (1 : V →ₗ[𝕜] V))† v
      = T† v - (conj μ) • v := by
    rw [map_sub, LinearEquiv.map_smulₛₗ, adjoint_one]; simp [Module.End.one_apply]
  rw [hadj] at hnorm
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hnorm
  constructor
  · intro h
    have h0 : T v - μ • v = 0 := by rw [h, sub_self]
    rw [h0, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at hnorm
    exact hnorm
  · intro h
    have h0 : T† v - (conj μ) • v = 0 := by rw [h, sub_self]
    rw [h0, norm_zero, norm_eq_zero, sub_eq_zero] at hnorm
    exact hnorm

/-! 7.22 Orthogonal eigenvectors for normal operators

Eigenvectors of a normal operator corresponding to distinct eigenvalues are
orthogonal. -/

theorem orthogonal_eigenvectors {T : V →ₗ[𝕜] V} (hT : IsStarNormal T)
    {α β : 𝕜} {u v : V} (hαβ : α ≠ β) (hu : T u = α • u) (hv : T v = β • v) :
    ⟪u, v⟫_𝕜 = 0 := by
  have hstar : T† v = (conj β) • v := (eigenvector_adjoint hT v β).mp hv
  have h1 : conj α * ⟪u, v⟫_𝕜 = conj β * ⟪u, v⟫_𝕜 := by
    calc conj α * ⟪u, v⟫_𝕜 = ⟪α • u, v⟫_𝕜 := (inner_smul_left u v α).symm
    _ = ⟪T u, v⟫_𝕜 := by rw [hu]
    _ = ⟪u, T† v⟫_𝕜 := by rw [LinearMap.adjoint_inner_right]
    _ = ⟪u, (conj β) • v⟫_𝕜 := by rw [hstar]
    _ = conj β * ⟪u, v⟫_𝕜 := inner_smul_right u v (conj β)
  have h2 : (conj α - conj β) * ⟪u, v⟫_𝕜 = 0 := by rw [sub_mul]; linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (RingHom.injective _ (sub_eq_zero.mp h)) hαβ
  · exact h

/-! 7.23 Over a complex inner product space, {lit}`T` is normal if and only if
{lit}`T = A + iB` for some commuting self-adjoint operators {lit}`A, B` (the real
and imaginary parts of {lit}`T`). -/

theorem normal_iff_real_imag {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔ ∃ A B : V →ₗ[ℂ] V, LinearMap.IsSymmetric A ∧
      LinearMap.IsSymmetric B ∧ Commute A B ∧ T = A + Complex.I • B := by
  constructor
  · intro hT
    set s := T† with hs
    refine ⟨(2⁻¹ : ℂ) • (T + s), (Complex.I / 2) • (s - T), ?_, ?_, ?_, ?_⟩
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint, _root_.isSelfAdjoint_iff,
        LinearMap.star_eq_adjoint, LinearEquiv.map_smulₛₗ, map_add, hs,
        LinearMap.adjoint_adjoint, show conj (2⁻¹ : ℂ) = 2⁻¹ by rw [map_inv₀, map_ofNat]]
      module
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint, _root_.isSelfAdjoint_iff,
        LinearMap.star_eq_adjoint, LinearEquiv.map_smulₛₗ, map_sub, hs,
        LinearMap.adjoint_adjoint,
        show conj (Complex.I / 2) = -(Complex.I / 2) by
          norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.conj_re,
            Complex.conj_im]]
      module
    · have hident : ((2⁻¹ : ℂ) • (T + s)) ∘ₗ ((Complex.I / 2) • (s - T))
          - ((Complex.I / 2) • (s - T)) ∘ₗ ((2⁻¹ : ℂ) • (T + s))
          = (Complex.I / 2) • (T ∘ₗ s - s ∘ₗ T) := by
        ext x
        simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          map_smul, map_add, map_sub, LinearMap.add_apply]
        module
      rw [commute_iff_eq, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← sub_eq_zero, hident, smul_eq_zero]
      right
      rw [sub_eq_zero]
      exact ((normal_iff_comp T).mp hT).symm
    · have hI : Complex.I * (Complex.I / 2) = -(2⁻¹ : ℂ) := by
        rw [mul_div_assoc', Complex.I_mul_I]; norm_num
      rw [smul_smul, hI]
      module
  · rintro ⟨A, B, hA, hB, hAB, rfl⟩
    have hadjA : A† = A := by
      rw [← LinearMap.star_eq_adjoint]; exact (LinearMap.isSymmetric_iff_isSelfAdjoint A).mp hA
    have hadjB : B† = B := by
      rw [← LinearMap.star_eq_adjoint]; exact (LinearMap.isSymmetric_iff_isSelfAdjoint B).mp hB
    rw [normal_iff_comp]
    have hadj : (A + Complex.I • B)† = A - Complex.I • B := by
      rw [map_add, LinearEquiv.map_smulₛₗ, Complex.conj_I, hadjA, hadjB]; module
    rw [hadj]
    ext x
    have hc := LinearMap.congr_fun hAB.eq x
    simp only [Module.End.mul_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub, map_smul] at hc ⊢
    rw [hc]
    module

/-! # Exercises 7A -/

/-- The solution to 7A.1. Fill it in. -/
noncomputable def exercise_7A_1_sol {n : ℕ} :
    EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) :=
  -- writing ⟨Tx, y⟩ = x1 y0 + ... + xn yn-1 = (x, (y0, ..., yn-1))
  -- makes it clear that T* (y0, ... yn) = (y1, ..., yn, 0)
  { toFun y := WithLp.toLp 2 (Fin.snoc (α := fun _ => 𝕜) (Fin.tail fun j => y j) 0)
    map_add' x y := by
      ext i; refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [Fin.tail]
    map_smul' a y := by
      ext i; refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [Fin.tail] }

/-- 7A.1 For the forward shift {lit}`T(z₁, …, zₙ) = (0, z₁, …, zₙ₋₁)` on
{lit}`𝔽ⁿ`, find a formula for the adjoint. -/
theorem exercise_7A_1 {n : ℕ}
    (T : EuclideanSpace 𝕜 (Fin (n + 1)) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))
    (hT : ∀ (z : EuclideanSpace 𝕜 (Fin (n + 1))),
      T z = Fin.cons (α := fun _ => 𝕜) 0 (Fin.init fun j => z j)) :
    T† = exercise_7A_1_sol := by
  -- ⟨x, T* y⟩ = ⟨Tx, y⟩ = x₀ y₁ + ⋯ + xₙ₋₁ yₙ = ⟨x, (y₁, …, yₙ, 0)⟩: peel the
  -- (zero) first term of ⟨Tx, y⟩ and the (zero) last term of ⟨x, sol y⟩.
  ext y : 1
  refine ext_inner_left 𝕜 fun x => ?_
  rw [← adjoint_inner, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc]
  simp [hT, exercise_7A_1_sol, Fin.tail, Fin.init]

/-- 7A.2 {lit}`T = 0 ⟺ T* = 0 ⟺ T*T = 0 ⟺ TT* = 0`. -/
theorem exercise_7A_2 (T : V →ₗ[𝕜] W) :
    [T = 0, T† = 0, T† ∘ₗ T = 0,
      T ∘ₗ T† = 0].TFAE := by
  -- 1 -> 2 - T = 0 implies ⟨Tv, w⟩ = 0 for all v, w, hence ⟨v, T†w⟩ = 0 for all v, w,
  --   take v = T†w for arbitrary w, then ‖T†w‖² = ⟨T†T†w, w⟩ = 0, so T† = 0
  -- 2 -> 1 - same argument in reverse
  -- 1 -> 3 - sub in 0
  -- 3 -> 1 - T† T = 0 -> <T†Tv, v> = 0 -> <Tv, Tv> = 0 -> ‖Tv‖ = 0 -> Tv = 0 for all v, so T = 0
  -- 2 -> 4 - sub in 0
  -- 4 -> 2 - similar argument as 3 -> 1 to get ‖T†w‖ = 0 for all w, so T† = 0
  tfae_have 1 → 2 := fun h => by
    ext w
    have : ⟪T† w, T† w⟫_𝕜 = 0 := by
      rw [← adjoint_inner, h, LinearMap.zero_apply, inner_zero_left]
    simpa using inner_self_eq_zero.mp this
  tfae_have 2 → 1 := fun h => by
    ext v
    have : ⟪T v, T v⟫_𝕜 = 0 := by
      rw [adjoint_inner, h, LinearMap.zero_apply, inner_zero_right]
    simpa using inner_self_eq_zero.mp this
  tfae_have 1 → 3 := fun h => by rw [h, LinearMap.comp_zero]
  tfae_have 3 → 1 := fun h => by
    ext v
    have : ⟪T v, T v⟫_𝕜 = 0 := by
      rw [adjoint_inner, ← LinearMap.comp_apply, h, LinearMap.zero_apply, inner_zero_right]
    simpa using inner_self_eq_zero.mp this
  tfae_have 2 → 4 := fun h => by rw [h, LinearMap.comp_zero]
  tfae_have 4 → 2 := fun h => by
    ext w
    have : ⟪T† w, T† w⟫_𝕜 = 0 := by
      rw [← adjoint_inner, ← LinearMap.comp_apply, h, LinearMap.zero_apply, inner_zero_left]
    simpa using inner_self_eq_zero.mp this
  tfae_finish

/-- 7A.3 {lit}`λ` is an eigenvalue of {lit}`T` iff {lit}`conj λ` is an eigenvalue
of {lit}`T*`. -/
theorem exercise_7A_3 (T : V →ₗ[𝕜] V) (μ : 𝕜) :
    HasEigenvalue T μ ↔ HasEigenvalue T† (conj μ) := by
  -- γ eigenvalue for T iff T - γ I is not injective
  -- take adjoint of both sides
  -- (T - γ I)† = T† - conj γ I, so conj γ is an eigenvalue of T† if and only if T - γ I is not injective
  -- in finite dimensions; and A is invertible iff A† is, by 7.5 (f).)
  -- take adjoint again to get back to T - γ I, confirming the equivalence
  have inj : ∀ A : V →ₗ[𝕜] V, Function.Injective A → Function.Injective A† := by
    intro A hA
    let e := LinearEquiv.ofBijective A ⟨hA, LinearMap.injective_iff_surjective.mp hA⟩
    have h₁ : e.symm.toLinearMap ∘ₗ A = LinearMap.id := by
      ext v; exact e.symm_apply_apply v
    have h₂ : A ∘ₗ e.symm.toLinearMap = LinearMap.id := by
      ext v; exact e.apply_symm_apply v
    have := (adjoint_inv A _ h₁ h₂).2
    exact Function.LeftInverse.injective (g := (e.symm.toLinearMap)†)
      fun w => LinearMap.congr_fun this w
  -- (T - μ I)* = T* - conj μ I, by 7.5 (a), (b), (e)
  have hadj : (T - μ • LinearMap.id)† = T† - conj μ • LinearMap.id := by
    rw [sub_eq_add_neg, adjoint_add, ← neg_smul, adjoint_smul, adjoint_id, map_neg,
      neg_smul, ← sub_eq_add_neg]
  have key : ∀ (S : V →ₗ[𝕜] V) (a : 𝕜), HasEigenvalue S a ↔
      ¬ Function.Injective (S - a • LinearMap.id : V →ₗ[𝕜] V) := by
    intro S a
    rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def,
      Module.End.one_eq_id, Ne, LinearMap.ker_eq_bot]
  rw [key, key, ← hadj]
  exact not_congr ⟨inj _, fun h => by simpa [adjoint_adjoint] using inj _ h⟩

/-- 7A.4 {lit}`U` is invariant under {lit}`T` iff {lit}`U⟂` is invariant under
{lit}`T*`. -/
theorem exercise_7A_4 (T : V →ₗ[𝕜] V) (U : Submodule 𝕜 V) :
    Section_5A.InvariantUnder T U ↔
      Section_5A.InvariantUnder T† Uᗮ := by
  -- assume T U invariant
  -- take u' ∈ Uᗮ, so ⟪u', u⟫_𝕜 = 0 for all u ∈
  -- since T u ∈ U for all u ∈ U, we have ⟪u', T u⟫_𝕜 = 0 for all u ∈ U too
  -- then ⟪T† u', u⟫_𝕜 = 0 for all u ∈ U, so T† u' ∈ Uᗮ
  -- so we shown that T† maps Uᗮ into itself, i.e., Uᗮ is invariant under T†
  -- for the converse use the fact that (Uᗮ)ᗮ = U and T†† = T, and run the same argument.
  have fwd : ∀ (S : V →ₗ[𝕜] V) (U : Submodule 𝕜 V),
      Section_5A.InvariantUnder S U → Section_5A.InvariantUnder S† Uᗮ := by
    intro S U h u' hu'
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [← adjoint_inner]
    exact Submodule.inner_right_of_mem_orthogonal (h u hu) hu'
  refine ⟨fwd T U, fun h => ?_⟩
  simpa [adjoint_adjoint, Submodule.orthogonal_orthogonal] using fwd T† Uᗮ h

/-- 7A.5 {lit}`∑ ‖Teₖ‖² = ∑ ‖T*fⱼ‖²` for orthonormal bases {lit}`e` of {lit}`V`
and {lit}`f` of {lit}`W` — in particular the left sum is basis-independent. -/
theorem exercise_7A_5 {n m : ℕ} (T : V →ₗ[𝕜] W)
    (e : OrthonormalBasis (Fin n) 𝕜 V) (f : OrthonormalBasis (Fin m) 𝕜 W) :
    ∑ i, ‖T (e i)‖ ^ 2 = ∑ j, ‖T† (f j)‖ ^ 2 := by
  sorry

/-- 7A.6 (a) {lit}`T` injective ⟺ {lit}`T*` surjective; (b) {lit}`T` surjective
⟺ {lit}`T*` injective. -/
theorem exercise_7A_6 (T : V →ₗ[𝕜] W) :
    (Function.Injective T ↔ Function.Surjective T†) ∧
      (Function.Surjective T ↔ Function.Injective T†) := by
  -- T injective ↔ ker T = 0 ↔ range T†ᗮ = 0 ↔ range T† = V (surjective)
  -- T surjective ↔ range T = W ↔ (ker T†)ᗮ = W ↔ ker T† = 0 ↔ T† injective
  constructor
  · rw [← LinearMap.ker_eq_bot, ker_eq_orthogonal_range_adjoint, Submodule.orthogonal_eq_bot_iff,
      LinearMap.range_eq_top]
  · rw [← LinearMap.range_eq_top, range_eq_orthogonal_ker_adjoint,
      Submodule.orthogonal_eq_top_iff, LinearMap.ker_eq_bot]

/-- 7A.7 (a) {lit}`dim null T* = dim null T + dim W − dim V`; -/
theorem exercise_7A_7 (T : V →ₗ[𝕜] W) :
    finrank 𝕜 (LinearMap.ker T†) =
        finrank 𝕜 (LinearMap.ker T) + finrank 𝕜 W - finrank 𝕜 V := by
  -- dim null T + dim range T = dim V          (rank–nullity, T : V → W)
  -- dim null T† + dim range T† = dim W        (rank–nullity, T† : W → V)
  -- dim null T† - dim null T = dim W - dim V - dim range T† + dim range T
  -- but range T† = (ker T)ᗮ ⊆ V, so dim range T† = dim V - dim null T = dim range T
  -- so the range terms cancel
  -- hence dim null T† = dim null T + dim W - dim V
  have h₁ := LinearMap.finrank_range_add_finrank_ker T
  have h₂ := LinearMap.finrank_range_add_finrank_ker T†
  have h₃ := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker T)
  rw [← range_adjoint] at h₃
  omega

/-- 7A.7 (b) {lit}`dim range T* = dim range T`. -/
theorem exercise_7A_7b (T : V →ₗ[𝕜] W) :
      finrank 𝕜 (LinearMap.range T†) =
        finrank 𝕜 (LinearMap.range T) := by
  -- from (a) and rank–nullity for T and T†
  have ha := exercise_7A_7 T
  have h₁ := LinearMap.finrank_range_add_finrank_ker T
  have h₂ := LinearMap.finrank_range_add_finrank_ker T†
  have h₃ := Submodule.finrank_le (LinearMap.range T)
  omega

/-- 7A.8 The row rank of a matrix equals its column rank (via 7A.7(b)). -/
theorem exercise_7A_8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝕜) :
    A.transpose.rank = A.rank := by
  -- the 
  sorry

/-- 7A.9 The product of two self-adjoint operators is self-adjoint iff they
commute. -/
theorem exercise_7A_9 (S T : V →ₗ[𝕜] V) (hS : LinearMap.IsSymmetric S)
    (hT : LinearMap.IsSymmetric T) :
    LinearMap.IsSymmetric (S ∘ₗ T) ↔ S ∘ₗ T = T ∘ₗ S := by
  sorry

/-- 7A.10 For {lit}`𝔽 = ℂ`, {lit}`T` is self-adjoint iff {lit}`⟨Tv, v⟩ = ⟨T*v, v⟩`
for all {lit}`v`. -/
theorem exercise_7A_10 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    LinearMap.IsSymmetric T ↔
      ∀ v, ⟪T v, v⟫_ℂ = ⟪T† v, v⟫_ℂ := by
  sorry

/-- The operator {lit}`S(w, z) = (−z, w)` on {lit}`𝔽²` of 7A.11. -/
def exercise_7A_11_S : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) where
  toFun v := !₂[- v 1, v 0]
  map_add' u v := by ext i; fin_cases i <;> simp; ring
  map_smul' a v := by ext i; fin_cases i <;> simp

/-- The solution to 7A.11(a). Fill it in. -/
noncomputable def exercise_7A_11_S_adj :
    EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
  sorry

/-- 7A.11 For {lit}`S(w, z) = (−z, w)` on {lit}`𝔽²`: (a) find {lit}`S*`;
(b) {lit}`S` is normal but not self-adjoint. -/
theorem exercise_7A_11 :
    (exercise_7A_11_S (𝕜 := 𝕜))† = exercise_7A_11_S_adj ∧
      IsStarNormal (exercise_7A_11_S (𝕜 := 𝕜)) ∧
      ¬ LinearMap.IsSymmetric (exercise_7A_11_S (𝕜 := 𝕜)) := by
  sorry

/-- 7A.12 {lit}`T` is normal iff {lit}`T = A + B` for commuting {lit}`A, B` with
{lit}`A` self-adjoint and {lit}`B` skew ({lit}`B* = −B`). -/
theorem exercise_7A_12 (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ ∃ A B : V →ₗ[𝕜] V, LinearMap.IsSymmetric A ∧
      B† = -B ∧ A ∘ₗ B = B ∘ₗ A ∧ T = A + B := by
  sorry

/-- The set of eigenvalues asked for in 7A.13(a). Fill it in. -/
def exercise_7A_13a_sol : Set ℝ :=
  sorry

/-- The minimal polynomial asked for in 7A.13(b). Fill it in. -/
def exercise_7A_13b_sol : Polynomial ℝ :=
  sorry

/-- 7A.13 For {lit}`𝔽 = ℝ` and the operator {lit}`𝒜 T = T*` on {lit}`ℒ(V)`:
(a) find all eigenvalues of {lit}`𝒜`; (b) find its minimal polynomial. -/
theorem exercise_7A_13 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V]
    (𝒜 : (V →ₗ[ℝ] V) →ₗ[ℝ] (V →ₗ[ℝ] V))
    (h𝒜 : ∀ T : V →ₗ[ℝ] V, 𝒜 T = T†) :
    (∀ μ : ℝ, HasEigenvalue 𝒜 μ ↔ μ ∈ exercise_7A_13a_sol) ∧
      minpoly ℝ 𝒜 = exercise_7A_13b_sol := by
  sorry

/-! 7A.14 The {lit}`L²` inner product {lit}`⟨p, q⟩ = ∫₀¹ pq` on {lit}`𝒫₂(ℝ)`,
modelled as {name}`Polynomial.degreeLT` {lit}`ℝ 3`. mathlib has no instance for
this, so we build it from an {name}`InnerProductSpace.Core` (the analytic axioms —
symmetry, positivity, definiteness — are left as {lit}`sorry`, like the exercises). -/

@[reducible]
noncomputable def l2Core_7A14 : InnerProductSpace.Core ℝ (Polynomial.degreeLT ℝ 3) where
  inner p q := ∫ x in (0 : ℝ)..1, ((p : Polynomial ℝ).eval x) * ((q : Polynomial ℝ).eval x)
  conj_inner_symm := by sorry
  re_inner_nonneg := by sorry
  add_left := by sorry
  smul_left := by sorry
  definite := by sorry

noncomputable instance : NormedAddCommGroup (Polynomial.degreeLT ℝ 3) :=
  l2Core_7A14.toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℝ (Polynomial.degreeLT ℝ 3) :=
  InnerProductSpace.ofCore _

noncomputable instance : FiniteDimensional ℝ (Polynomial.degreeLT ℝ 3) :=
  Module.Finite.equiv (Polynomial.degreeLTEquiv ℝ 3).symm

/-- The operator {lit}`T(ax² + bx + c) = bx` on {lit}`𝒫₂(ℝ)` of 7A.14. -/
noncomputable def exercise_7A_14_T :
    (Polynomial.degreeLT ℝ 3) →ₗ[ℝ] (Polynomial.degreeLT ℝ 3) where
  toFun p := ⟨Polynomial.C ((p : Polynomial ℝ).coeff 1) * Polynomial.X, by
    rw [Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) (by norm_num)⟩
  map_add' p q := by
    apply Subtype.ext
    simp [Polynomial.C_add, add_mul]
  map_smul' a p := by
    apply Subtype.ext
    simp [Polynomial.C_mul, Polynomial.smul_eq_C_mul, mul_assoc]

/-- 7A.14 With {lit}`⟨p, q⟩ = ∫₀¹ pq` on {lit}`𝒫₂(ℝ)` and {lit}`T(ax² + bx + c) =
bx`, the operator {lit}`T` is not self-adjoint — even though its matrix with
respect to {lit}`1, x, x²` equals its own conjugate transpose. -/
theorem exercise_7A_14 : ¬ LinearMap.IsSymmetric exercise_7A_14_T := by
  sorry

/-- 7A.15 (a) For invertible {lit}`T`, {lit}`T` is self-adjoint iff {lit}`T⁻¹` is
self-adjoint. -/
theorem exercise_7A_15a (T : V ≃ₗ[𝕜] V) :
    LinearMap.IsSymmetric (T : V →ₗ[𝕜] V) ↔
      LinearMap.IsSymmetric (T.symm : V →ₗ[𝕜] V) := by
  sorry

/-- 7A.15 (b) For invertible {lit}`T`, {lit}`T` is normal iff {lit}`T⁻¹` is
normal. -/
theorem exercise_7A_15b (T : V ≃ₗ[𝕜] V) :
    IsStarNormal (T : V →ₗ[𝕜] V) ↔ IsStarNormal (T.symm : V →ₗ[𝕜] V) := by
  sorry

/-- 7A.16 For {lit}`𝔽 = ℝ`: (a) the self-adjoint operators form a subspace of
{lit}`ℒ(V)`; (b) what is the dimension of this subspace. -/
theorem exercise_7A_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] :
    ∃ U : Submodule ℝ (V →ₗ[ℝ] V),
      (∀ T, T ∈ U ↔ LinearMap.IsSymmetric T) ∧
        finrank ℝ U = sorry := by
  sorry

/-- 7A.17 For {lit}`𝔽 = ℂ` and {lit}`V ≠ 0`, the self-adjoint operators do not
form a subspace of {lit}`ℒ(V)`. -/
theorem exercise_7A_17 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] :
    ¬ ∃ U : Submodule ℂ (V →ₗ[ℂ] V), ∀ T, T ∈ U ↔ LinearMap.IsSymmetric T := by
  sorry

/-- 7A.18 If {lit}`dim V ≥ 2`, the normal operators do not form a subspace of
{lit}`ℒ(V)`. -/
theorem exercise_7A_18 (h : 2 ≤ finrank 𝕜 V) :
    ¬ ∃ U : Submodule 𝕜 (V →ₗ[𝕜] V), ∀ T, T ∈ U ↔ IsStarNormal T := by
  sorry

/-- 7A.19 If {lit}`‖T*v‖ ≤ ‖Tv‖` for every {lit}`v`, then {lit}`T` is normal. -/
theorem exercise_7A_19 (T : V →ₗ[𝕜] V)
    (h : ∀ v, ‖T† v‖ ≤ ‖T v‖) : IsStarNormal T := by
  sorry

/-- 7A.20 If {lit}`P² = P`, the following are equivalent: (a) {lit}`P` self-adjoint;
(b) {lit}`P` normal; (c) {lit}`P = P_U` for some subspace {lit}`U`. -/
theorem exercise_7A_20 (P : V →ₗ[𝕜] V) (hP : P ∘ₗ P = P) :
    [LinearMap.IsSymmetric P, IsStarNormal P,
      ∃ U : Submodule 𝕜 V, (U.starProjection : V →ₗ[𝕜] V) = P].TFAE := by
  sorry

/-- 7A.21 For the differentiation operator {lit}`D p = p′` on {lit}`𝒫₈(ℝ)`, no
inner product makes {lit}`D` normal.

Quantifying over inner products uses {name}`InnerProductSpace.Core`, a bundled
structure over {lit}`AddCommGroup` + {lit}`Module` (unlike the
{name}`InnerProductSpace` class, it does not fix the norm), and normality is
spelled out: some {lit}`S` is an adjoint of {lit}`D` for that inner product and
commutes with {lit}`D`. -/
theorem exercise_7A_21
    (D : Polynomial.degreeLT ℝ 9 →ₗ[ℝ] Polynomial.degreeLT ℝ 9)
    (hD : ∀ p : Polynomial.degreeLT ℝ 9,
      (D p : Polynomial ℝ) = Polynomial.derivative (p : Polynomial ℝ)) :
    ¬ ∃ (c : InnerProductSpace.Core ℝ (Polynomial.degreeLT ℝ 9))
        (S : Polynomial.degreeLT ℝ 9 →ₗ[ℝ] Polynomial.degreeLT ℝ 9),
        (∀ v w, c.inner (D v) w = c.inner v (S w)) ∧ D ∘ₗ S = S ∘ₗ D := by
  sorry

/-- The operator on {lit}`ℝ³` asked for in 7A.22. Fill it in. -/
noncomputable def exercise_7A_22_sol :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  sorry

/-- 7A.22 There is an operator on {lit}`ℝ³` that is normal but not self-adjoint. -/
theorem exercise_7A_22 :
    IsStarNormal exercise_7A_22_sol ∧ ¬ LinearMap.IsSymmetric exercise_7A_22_sol := by
  sorry

/-- 7A.23 If {lit}`T` is normal, {lit}`‖v‖ = ‖w‖ = 2`, {lit}`Tv = 3v`,
{lit}`Tw = 4w`, then {lit}`‖T(v + w)‖ = 10`. -/
theorem exercise_7A_23 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) {v w : V}
    (hv : ‖v‖ = 2) (hw : ‖w‖ = 2) (hTv : T v = (3 : 𝕜) • v) (hTw : T w = (4 : 𝕜) • w) :
    ‖T (v + w)‖ = 10 := by
  sorry

/-- 7A.24 If the minimal polynomial of {lit}`T` is {lit}`∑ aₖ zᵏ + zᵐ`, then the
minimal polynomial of {lit}`T*` has the conjugated coefficients — i.e. it is
{lit}`(minpoly T)` with {lit}`conj` applied to each coefficient. -/
theorem exercise_7A_24 (T : V →ₗ[𝕜] V) :
    minpoly 𝕜 T† = (minpoly 𝕜 T).map (starRingEnd 𝕜) := by
  sorry

/-- 7A.25 {lit}`T` is diagonalizable iff {lit}`T*` is diagonalizable, using the
{lit}`5.50` definition {name}`LADR.Section_5D.IsDiagonalizable`. -/
theorem exercise_7A_25 (T : V →ₗ[𝕜] V) :
    Section_5D.IsDiagonalizable T ↔
      Section_5D.IsDiagonalizable T† := by
  sorry

/-- 7A.26 (a) On a real inner product space, for {lit}`T v = ⟨v, u⟩ x` the
operator {lit}`T` is self-adjoint iff the list {lit}`u, x` is linearly
dependent. -/
theorem exercise_7A_26a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (u x : V) (T : V →ₗ[ℝ] V)
    (hT : ∀ v, T v = ⟪u, v⟫_ℝ • x) :
    LinearMap.IsSymmetric T ↔ ¬ LinearIndependent ℝ ![u, x] := by
  sorry

/-- 7A.26 (b) For {lit}`T v = ⟨v, u⟩ x`, {lit}`T` is normal iff the list
{lit}`u, x` is linearly dependent. -/
theorem exercise_7A_26b (u x : V) (T : V →ₗ[𝕜] V) (hT : ∀ v, T v = ⟪u, v⟫_𝕜 • x) :
    IsStarNormal T ↔ ¬ LinearIndependent 𝕜 ![u, x] := by
  sorry

/-- 7A.27 If {lit}`T` is normal, then {lit}`null Tᵏ = null T` and
{lit}`range Tᵏ = range T` for every positive integer {lit}`k`. -/
theorem exercise_7A_27 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (k : ℕ) (hk : 0 < k) :
    LinearMap.ker (T ^ k) = LinearMap.ker T ∧
      LinearMap.range (T ^ k) = LinearMap.range T := by
  sorry

/-- 7A.28 If {lit}`T` is normal, then for every {lit}`λ` the minimal polynomial of
{lit}`T` is not a polynomial multiple of {lit}`(z − λ)²`. -/
theorem exercise_7A_28 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (μ : 𝕜) :
    ¬ (Polynomial.X - Polynomial.C μ) ^ 2 ∣ minpoly 𝕜 T := by
  sorry

/-- 7A.29 Prove or give a counterexample: if there is an orthonormal basis
{lit}`e₁, …, eₙ` of {lit}`V` with {lit}`‖Teₖ‖ = ‖T*eₖ‖` for each {lit}`k`, then
{lit}`T` is normal. -/
def exercise_7A_29 {n : ℕ} (T : V →ₗ[𝕜] V) (e : OrthonormalBasis (Fin n) 𝕜 V) :
    Decidable ((∀ k, ‖T (e k)‖ = ‖T† (e k)‖) → IsStarNormal T) := by
  sorry

/-- 7A.30 If {lit}`T ∈ ℒ(𝔽³)` is normal with {lit}`T(1,1,1) = (2,2,2)`, then every
{lit}`(z₁, z₂, z₃) ∈ null T` has {lit}`z₁ + z₂ + z₃ = 0`. -/
theorem exercise_7A_30 (T : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3))
    (hT : IsStarNormal T) (h1 : T !₂[1, 1, 1] = !₂[2, 2, 2])
    (z : EuclideanSpace 𝕜 (Fin 3)) (hz : T z = 0) :
    z 0 + z 1 + z 2 = 0 := by
  sorry

/-- The span of {lit}`1, cos x, …, cos nx, sin x, …, sin nx` inside {lit}`ℝ → ℝ`,
the space of 7A.31. -/
noncomputable def trigSpan (n : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ ({fun _ : ℝ => (1 : ℝ)} ∪
    (fun k : ℕ => fun x : ℝ => Real.cos (k * x)) '' Set.Icc 1 n ∪
    (fun k : ℕ => fun x : ℝ => Real.sin (k * x)) '' Set.Icc 1 n)

/-- The {lit}`L²` inner product {lit}`⟨f, g⟩ = ∫₋π^π fg` on {name}`trigSpan`. As
for 7A.14 the analytic axioms are left as {lit}`sorry`, like the exercises. -/
@[reducible]
noncomputable def l2Core_7A31 (n : ℕ) : InnerProductSpace.Core ℝ (trigSpan n) where
  inner f g := ∫ x in (-Real.pi)..Real.pi, (f : ℝ → ℝ) x * (g : ℝ → ℝ) x
  conj_inner_symm := by sorry
  re_inner_nonneg := by sorry
  add_left := by sorry
  smul_left := by sorry
  definite := by sorry

noncomputable instance (n : ℕ) : NormedAddCommGroup (trigSpan n) :=
  (l2Core_7A31 n).toNormedAddCommGroup

noncomputable instance (n : ℕ) : InnerProductSpace ℝ (trigSpan n) :=
  InnerProductSpace.ofCore _

instance (n : ℕ) : FiniteDimensional ℝ (trigSpan n) := by
  rw [trigSpan]
  exact FiniteDimensional.span_of_finite ℝ
    (((Set.finite_singleton _).union ((Set.finite_Icc 1 n).image _)).union
      ((Set.finite_Icc 1 n).image _))

/-- 7A.31 (a) On {lit}`span(1, cos x, …, cos nx, sin x, …, sin nx)` with
{lit}`⟨f, g⟩ = ∫₋π^π fg`, the operator {lit}`D f = f′` satisfies {lit}`D* = −D`,
so {lit}`D` is normal but not self-adjoint. -/
theorem exercise_7A_31a (n : ℕ) (hn : 0 < n) (D : trigSpan n →ₗ[ℝ] trigSpan n)
    (hD : ∀ f : trigSpan n, (D f : ℝ → ℝ) = deriv (f : ℝ → ℝ)) :
    D† = -D ∧ IsStarNormal D ∧ ¬ LinearMap.IsSymmetric D := by
  sorry

/-- 7A.31 (b) The operator {lit}`T f = f″` on the same space is self-adjoint. -/
theorem exercise_7A_31b (n : ℕ) (T : trigSpan n →ₗ[ℝ] trigSpan n)
    (hT : ∀ f : trigSpan n, (T f : ℝ → ℝ) = deriv (deriv (f : ℝ → ℝ))) :
    LinearMap.IsSymmetric T := by
  sorry

/-- 7A.32 Under the identification of {lit}`V` with {lit}`V′` sending {lit}`w` to
the functional {lit}`φ_w = ⟨·, w⟩` (6.58), the adjoint corresponds to the dual
map: {lit}`T′(φ_w) = φ_{T*w}`. -/
theorem exercise_7A_32 (T : V →ₗ[𝕜] W) (w : W) :
    LinearMap.dualMap T (innerₛₗ 𝕜 w) = innerₛₗ 𝕜 (T† w) := by
  sorry

end LADR.Section_7A
