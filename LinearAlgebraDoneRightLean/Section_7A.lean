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
public import Mathlib.Data.Sym.Card
public import LinearAlgebraDoneRightLean.Section_5A
public import LinearAlgebraDoneRightLean.Section_5D
public import LinearAlgebraDoneRightLean.Section_6B
public import LinearAlgebraDoneRightLean.Section_6C
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

/-- (b) {lit}`range T* = (null T)⟂`: replace {lit}`T` with {lit}`T*` in (a), getting
{lit}`null T = (range T*)⟂`, and take orthogonal complements (6.52). -/
@[avoiding LinearMap.orthogonal_ker]
theorem range_adjoint (T : V →ₗ[𝕜] W) :
    LinearMap.range T† = (LinearMap.ker T)ᗮ := by
  have h := ker_adjoint T†
  rw [LinearMap.adjoint_adjoint] at h
  rw [h, Submodule.orthogonal_orthogonal]

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
  -- If A is (T, e, f), Then the ith column is T (e i) in f terms
  -- So ‖T (e j)‖² = ∑ i, |Ai,j|²
  -- so ∑ i, ‖T (e i)‖² = ∑ i, ∑ j, |Ai,j|²
  -- IF B is (T†, f, e), it's ith column is T† (f i) in e terms
  -- we have shown that A† = B
  -- so ∑ j, ‖T† (f j)‖² = ∑ j, ∑ i, |A† i,j|²
  -- but |A† i,j|² = |Aj,i|² and since we are summing over all i and j
  -- the two sums are equal, which proves the theorem.
  set A := LinearMap.toMatrix e.toBasis f.toBasis T
  -- entries in an orthonormal basis are inner products (6.30)
  have hA : ∀ j k, A j k = ⟪f j, T (e k)⟫_𝕜 := by
    intro j k
    show LinearMap.toMatrix e.toBasis f.toBasis T j k = _
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
  have hB : ∀ k j, LinearMap.toMatrix f.toBasis e.toBasis T† k j = ⟪e k, T† (f j)⟫_𝕜 := by
    intro k j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
  -- ‖T eₖ‖² = ∑ⱼ |A j k|² (column k of A)
  have hcol : ∀ k, ‖T (e k)‖ ^ 2 = ∑ j, ‖A j k‖ ^ 2 := by
    intro k; simp_rw [hA]; exact (f.sum_sq_norm_inner_right _).symm
  -- ‖T* fⱼ‖² = ∑ₖ |B k j|² = ∑ₖ |A j k|², since B = Aᴴ (7.9)
  have hrow : ∀ j, ‖T† (f j)‖ ^ 2 = ∑ k, ‖A j k‖ ^ 2 := by
    intro j
    rw [← e.sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hB, toMatrix_adjoint_eq_conjTranspose, Matrix.conjTranspose_apply, norm_star]
  simp_rw [hcol, hrow]
  exact Finset.sum_comm

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
  -- First show A.conj.rank = A.transpose.rank by observing
  -- ∑ a_i v_i = 0 ↔ ∑ conj a_i conj v_i = 0
  -- then notice A.conj is the matrix for T† and A is the matrix for T
  -- for the standard basis of ℂ^n.
  -- Hence A.transpose.rank = A.conj.rank = rank range T† = rank range T (by 7b)
  -- Conjugating every entry does not change the rank: v ↦ conj v is a
  -- conjugate-linear bijection carrying range B onto range (conj B).
  have hconj : ∀ {k l : ℕ} (B : Matrix (Fin k) (Fin l) 𝕜), (B.map star).rank = B.rank := by
    intro k l B
    -- (conj C)(conj v) = conj (C v), so conj maps range C into range (conj C)
    have hmem : ∀ (C : Matrix (Fin k) (Fin l) 𝕜) (y : Fin k → 𝕜),
        y ∈ LinearMap.range C.mulVecLin → star y ∈ LinearMap.range (C.map star).mulVecLin := by
      rintro C y ⟨v, rfl⟩
      exact ⟨star v, by ext i; simp [Matrix.mulVec, dotProduct, star_sum]⟩
    have hBB : (B.map star).map star = B := by ext; simp
    let j : LinearMap.range B.mulVecLin ≃+ LinearMap.range (B.map star).mulVecLin :=
      { toFun y := ⟨star y.1, hmem B y.1 y.2⟩
        invFun y := ⟨star y.1, by have := hmem _ y.1 y.2; rwa [hBB] at this⟩
        left_inv y := by simp
        right_inv y := by simp
        map_add' x y := by ext1; simp }
    have := rank_eq_of_equiv_equiv (starRingEnd 𝕜) j
      (Function.Involutive.bijective (fun a => by simp))
      (fun r y => by ext1; simp [j, star_smul])
    exact (congrArg Cardinal.toNat this).symm
  -- The matrix of T† (standard orthonormal bases) is Aᴴ, by 7.9.
  let b := EuclideanSpace.basisFun (Fin n) 𝕜
  let c := EuclideanSpace.basisFun (Fin m) 𝕜
  let T := Matrix.toLin b.toBasis c.toBasis A
  have hT : LinearMap.toMatrix b.toBasis c.toBasis T = A := LinearMap.toMatrix_toLin _ _ _
  have hT' : T† = Matrix.toLin c.toBasis b.toBasis Aᴴ := by
    rw [← hT, ← toMatrix_adjoint_eq_conjTranspose, Matrix.toLin_toMatrix]
  calc A.transpose.rank = Aᴴ.rank := (hconj Aᵀ).symm
    _ = finrank 𝕜 (LinearMap.range (Matrix.toLin c.toBasis b.toBasis Aᴴ)) :=
      Matrix.rank_eq_finrank_range_toLin Aᴴ b.toBasis c.toBasis
    _ = finrank 𝕜 (LinearMap.range T†) := by rw [hT']
    _ = finrank 𝕜 (LinearMap.range T) := exercise_7A_7b T
    _ = A.rank := (Matrix.rank_eq_finrank_range_toLin A c.toBasis b.toBasis).symm

/-- 7A.9 The product of two self-adjoint operators is self-adjoint iff they
commute. -/
theorem exercise_7A_9 (S T : V →ₗ[𝕜] V) (hS : LinearMap.IsSymmetric S)
    (hT : LinearMap.IsSymmetric T) :
    LinearMap.IsSymmetric (S ∘ₗ T) ↔ S ∘ₗ T = T ∘ₗ S := by
  -- S† = S and T† = T, so (S ∘ₗ T)† = T† ∘ₗ S† = T ∘ₗ S
  -- so ST self-adjoint ↔ TS = ST
  rw [isSelfAdjoint_iff] at hS hT ⊢
  rw [adjoint_comp, hS, hT, eq_comm]

/-- 7A.10 For {lit}`𝔽 = ℂ`, {lit}`T` is self-adjoint iff {lit}`⟨Tv, v⟩ = ⟨T*v, v⟩`
for all {lit}`v`. -/
theorem exercise_7A_10 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    LinearMap.IsSymmetric T ↔
      ∀ v, ⟪T v, v⟫_ℂ = ⟪T† v, v⟫_ℂ := by
  -- => Tv = T†v for all v, so trivial
  -- <= ⟪T v, v⟫ - ⟪T†v,v⟫ = 0 fo all v
  -- so ⟨T - T†)v, v⟩ = 0 for all v, which implies T - T† = 0 in C, i.e., T = T†
  rw [isSelfAdjoint_iff]
  constructor
  · intro h v; rw [h]
  · intro h
    have : T - T† = 0 := (inner_map_self_eq_zero_iff _).mp fun v => by
      rw [LinearMap.sub_apply, inner_sub_left, h, sub_self]
    exact (sub_eq_zero.mp this).symm

/-- The operator {lit}`S(w, z) = (−z, w)` on {lit}`𝔽²` of 7A.11. -/
def exercise_7A_11_S : EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) where
  toFun v := !₂[- v 1, v 0]
  map_add' u v := by ext i; fin_cases i <;> simp; ring
  map_smul' a v := by ext i; fin_cases i <;> simp

/-- The solution to 7A.11(a). Fill it in. -/
noncomputable def exercise_7A_11_S_adj :
    EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) :=
  -- ⟨S(w,z), (x,y)⟩ = ⟨(-z, w), (x, y)⟩ = -z * x + w * y = ⟪(w, z), (y, -x)⟫
  -- so S*(x, y) = (y, -x)
  { toFun v := !₂[v 1, - v 0]
    map_add' u v := by ext i; fin_cases i <;> simp; ring
    map_smul' a v := by ext i; fin_cases i <;> simp }

/-- 7A.11 For {lit}`S(w, z) = (−z, w)` on {lit}`𝔽²`: (a) find {lit}`S*`;
(b) {lit}`S` is normal but not self-adjoint. -/
theorem exercise_7A_11 :
    (exercise_7A_11_S (𝕜 := 𝕜))† = exercise_7A_11_S_adj ∧
      IsStarNormal (exercise_7A_11_S (𝕜 := 𝕜)) ∧
      ¬ LinearMap.IsSymmetric (exercise_7A_11_S (𝕜 := 𝕜)) := by
  -- S(1,1) = (-1, 1) and S*(1,1) = (1, -1) so not self-adjoint
  -- but SS* = (-x, -y) and S*S = (-x, -y), so S is normal
  have ha : (exercise_7A_11_S (𝕜 := 𝕜))† = exercise_7A_11_S_adj := by
    ext v : 1
    refine ext_inner_left 𝕜 fun u => ?_
    rw [← adjoint_inner]
    simp [exercise_7A_11_S, exercise_7A_11_S_adj, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  refine ⟨ha, ?_, ?_⟩
  · rw [normal_iff_comp, ha]
    ext v i
    fin_cases i <;> simp [exercise_7A_11_S, exercise_7A_11_S_adj]
  · rw [isSelfAdjoint_iff, ha]
    intro h
    have := congrArg (· 0) (LinearMap.congr_fun h !₂[1, 1])
    norm_num [exercise_7A_11_S, exercise_7A_11_S_adj] at this

/-- 7A.12 {lit}`T` is normal iff {lit}`T = A + B` for commuting {lit}`A, B` with
{lit}`A` self-adjoint and {lit}`B` skew ({lit}`B* = −B`). -/
theorem exercise_7A_12 (T : V →ₗ[𝕜] V) :
    IsStarNormal T ↔ ∃ A B : V →ₗ[𝕜] V, LinearMap.IsSymmetric A ∧
      B† = -B ∧ A ∘ₗ B = B ∘ₗ A ∧ T = A + B := by
  -- => T†T = TT† let A = (T + T†)/2 and B = (T - T†)/2
  -- easy to see that A† = A and B† = -B and A + B = T
  -- finally AB = 1/4 ((T + T†)(T - T†)) = 1/4 (T² - TT† + T†T - (T†)²)
  -- BA = 1/4 ((T - T†)(T + T†)) = 1/4 (T² - T†T + TT† - (T†)²)
  -- but since T†T = TT†, we have AB = BA, so A and B commute.
  -- <= T = A + B, so T† = A† + B† = A - B
  -- TT† = (A + B)(A - B) = A² - AB + BA - B² = A² - B² since AB = BA
  -- T†T = (A - B)(A + B) = A² + AB - BA - B² = A² - B² since AB = BA
  -- (computations in the ring ℒ(V), where composition is multiplication)
  simp only [normal_iff_comp, ← Module.End.mul_eq_comp]
  constructor
  · intro h
    have h2 : conj (2 : 𝕜) = 2 := map_ofNat _ 2
    refine ⟨(2⁻¹ : 𝕜) • (T + T†), (2⁻¹ : 𝕜) • (T - T†), ?_, ?_, ?_, ?_⟩
    · rw [isSelfAdjoint_iff, adjoint_smul, adjoint_add, adjoint_adjoint, add_comm, map_inv₀,
        h2]
    · rw [adjoint_smul, map_sub, adjoint_adjoint, ← smul_neg, neg_sub, map_inv₀, h2]
    · have e₁ : (T + T†) * (T - T†) = T * T - T† * T† := by
        rw [show (T + T†) * (T - T†) = T * T - T * T† + T† * T - T† * T† by noncomm_ring, h]
        abel
      have e₂ : (T - T†) * (T + T†) = T * T - T† * T† := by
        rw [show (T - T†) * (T + T†) = T * T + T * T† - T† * T - T† * T† by noncomm_ring, h]
        abel
      simp only [smul_mul_assoc, mul_smul_comm, e₁, e₂]
    · module
  · rintro ⟨A, B, hA, hB, hc, rfl⟩
    rw [isSelfAdjoint_iff] at hA
    have hT : (A + B)† = A - B := by rw [adjoint_add, hA, hB, sub_eq_add_neg]
    rw [hT]
    rw [show (A - B) * (A + B) = A * A + A * B - B * A - B * B by noncomm_ring,
      show (A + B) * (A - B) = A * A - A * B + B * A - B * B by noncomm_ring, hc]
    abel

/-- The set of eigenvalues asked for in 7A.13(a), as a function of
{lit}`n = dim V`. Fill it in. -/
def exercise_7A_13a_sol (n : ℕ) : Set ℝ :=
  -- T†† = T, so min poly divides z^2 - 1 = (z - 1)(z + 1)
  -- but 1 is an eigenvalue because I† = I
  -- (0, 1; -1 0) transpose = (0, -1; 1 0) = - (0, 1; -1 0)
  -- so any T that swaps two basis vectors and gives - to one of them has -1 as an eigenvalue.
  -- T v0 = -v1 and T v1 = v0
  -- note this happens in dim > 1 only; in dim 1 every T = c I is self-adjoint, so 𝒜 = I
  if n = 1 then {1} else {1, -1}

/-- The minimal polynomial asked for in 7A.13(b), as a function of
{lit}`n = dim V`. Fill it in. -/
noncomputable def exercise_7A_13b_sol (n : ℕ) : Polynomial ℝ :=
  -- by above min poly = z^2 - 1 (and z - 1 when dim V = 1, since then 𝒜 = I)
  if n = 1 then Polynomial.X - 1 else Polynomial.X ^ 2 - 1

open Polynomial in
/-- 7A.13 For {lit}`𝔽 = ℝ` and the operator {lit}`𝒜 T = T*` on {lit}`ℒ(V)`:
(a) find all eigenvalues of {lit}`𝒜`; (b) find its minimal polynomial.

The book does not fix {lit}`dim V`, and the answer depends on it: when
{lit}`dim V = 1` every operator is self-adjoint, so {lit}`𝒜 = I`. Hence the
answers are functions of {lit}`dim V`. -/
theorem exercise_7A_13 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V]
    (𝒜 : (V →ₗ[ℝ] V) →ₗ[ℝ] (V →ₗ[ℝ] V))
    (h𝒜 : ∀ T : V →ₗ[ℝ] V, 𝒜 T = T†) :
    (∀ μ : ℝ, HasEigenvalue 𝒜 μ ↔ μ ∈ exercise_7A_13a_sol (finrank ℝ V)) ∧
      minpoly ℝ 𝒜 = exercise_7A_13b_sol (finrank ℝ V) := by
  -- 𝒜² = I since T** = T
  have hA2 : 𝒜 * 𝒜 = 1 := LinearMap.ext fun T => by
    rw [Module.End.mul_apply, h𝒜, h𝒜, adjoint_adjoint, Module.End.one_apply]
  -- so every eigenvalue satisfies μ² = 1
  have hμ : ∀ μ, HasEigenvalue 𝒜 μ → μ = 1 ∨ μ = -1 := by
    intro μ hμ
    obtain ⟨T, hT⟩ := hμ.exists_hasEigenvector
    have h := LinearMap.congr_fun hA2 T
    rw [Module.End.mul_apply, hT.apply_eq_smul, map_smul, hT.apply_eq_smul, smul_smul,
      Module.End.one_apply] at h
    have : (μ * μ - 1) • T = 0 := by rw [sub_smul, h, one_smul, sub_self]
    exact mul_self_eq_one_iff.mp (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hT.2))
  -- 1 is an eigenvalue: I* = I
  have h1 : HasEigenvalue 𝒜 1 :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [h𝒜, one_smul]; exact adjoint_id),
        one_ne_zero⟩
  -- 𝒜 is annihilated by z² - 1
  have hann : aeval 𝒜 (X ^ 2 - 1 : ℝ[X]) = 0 := by
    simp [sq, hA2]
  have hdvd : minpoly ℝ 𝒜 ∣ X ^ 2 - 1 := minpoly.dvd ℝ 𝒜 hann
  by_cases hd : finrank ℝ V = 1
  · -- dim V = 1: every operator is a scalar multiple of I, hence self-adjoint, so 𝒜 = I
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hspan := (finrank_eq_one_iff_of_nonzero' v hv).mp hd
    have hself : ∀ T : V →ₗ[ℝ] V, T† = T := by
      intro T
      obtain ⟨c, hc⟩ := hspan (T v)
      have hT : T = c • LinearMap.id := by
        ext w
        obtain ⟨a, rfl⟩ := hspan w
        rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
      rw [hT, adjoint_smul, adjoint_id]
      rfl
    have hA : 𝒜 = 1 := LinearMap.ext fun T => by rw [h𝒜, hself, Module.End.one_apply]
    simp only [exercise_7A_13a_sol, exercise_7A_13b_sol, hd, ↓reduceIte, Set.mem_singleton_iff]
    refine ⟨fun μ => ⟨fun h => ?_, fun h => h ▸ h1⟩, by rw [hA, minpoly.one]⟩
    rw [Module.End.hasEigenvalue_iff_isRoot, hA, minpoly.one] at h
    simpa [sub_eq_zero] using h
  · -- dim V ≥ 2: the skew operator v ↦ ⟨e₀, v⟩e₁ - ⟨e₁, v⟩e₀ is an eigenvector for -1
    have h2 : 2 ≤ finrank ℝ V := by
      have := Module.finrank_pos (R := ℝ) (M := V); omega
    let b := stdOrthonormalBasis ℝ V
    let i₀ : Fin (finrank ℝ V) := ⟨0, by omega⟩
    let i₁ : Fin (finrank ℝ V) := ⟨1, by omega⟩
    have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
    let T : V →ₗ[ℝ] V := (innerₛₗ ℝ (b i₀)).smulRight (b i₁) - (innerₛₗ ℝ (b i₁)).smulRight (b i₀)
    have hTadj : T† = -T := by
      ext w : 1
      refine ext_inner_left ℝ fun u => ?_
      rw [← adjoint_inner]
      simp only [T, LinearMap.sub_apply, LinearMap.smulRight_apply, innerₛₗ_apply_apply,
        LinearMap.neg_apply, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        inner_neg_right, real_inner_comm, conj_trivial]
      ring
    have hT0 : T ≠ 0 := by
      intro h
      have := LinearMap.congr_fun h (b i₀)
      simp only [T, LinearMap.sub_apply, LinearMap.smulRight_apply, innerₛₗ_apply_apply,
        LinearMap.zero_apply, b.inner_eq_zero h01.symm, b.inner_eq_one, one_smul,
        zero_smul, sub_zero] at this
      exact b.orthonormal.ne_zero i₁ this
    have hm1 : HasEigenvalue 𝒜 (-1) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (by rw [h𝒜, hTadj, neg_one_smul]), hT0⟩
    simp only [exercise_7A_13a_sol, exercise_7A_13b_sol, hd, ↓reduceIte, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨fun μ => ⟨hμ μ, ?_⟩, ?_⟩
    · rintro (rfl | rfl)
      exacts [h1, hm1]
    · -- (z - 1) and (z + 1) both divide the minimal polynomial; it divides z² - 1
      have r1 := Module.End.hasEigenvalue_iff_isRoot.mp h1
      have r2 := Module.End.hasEigenvalue_iff_isRoot.mp hm1
      have hcop : IsCoprime (X - C (1 : ℝ)) (X - C (-1)) :=
        Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by norm_num)
      have hfac : (X - C 1) * (X - C (-1)) ∣ minpoly ℝ 𝒜 :=
        hcop.mul_dvd (dvd_iff_isRoot.mpr r1) (dvd_iff_isRoot.mpr r2)
      have hX : (X ^ 2 - 1 : ℝ[X]) = (X - C 1) * (X - C (-1)) := by
        simp only [map_neg, map_one, sub_neg_eq_add]; ring
      rw [hX] at hdvd ⊢
      exact (eq_of_monic_of_associated (minpoly.monic (Algebra.IsIntegral.isIntegral 𝒜))
        ((monic_X_sub_C _).mul (monic_X_sub_C _)) (associated_of_dvd_dvd hdvd hfac))

/-! 7A.14 The {lit}`L²` inner product {lit}`⟨p, q⟩ = ∫₀¹ pq` on {lit}`𝒫₂(ℝ)`,
modelled as {name}`Polynomial.degreeLT` {lit}`ℝ 3`. We reuse the inner product
space {name}`L2C` {lit}`0 1` ({lit}`C[0, 1]` with {lit}`∫₀¹ fg`, from
{lit}`L2Interval`) and pull it back along the inclusion
{lit}`𝒫₂(ℝ) → C[0, 1]` ({name}`Section_6C.polyL2`), which is injective because a
polynomial vanishing on {lit}`[0, 1]` has infinitely many roots. -/

/-- The inclusion {lit}`𝒫₂(ℝ) → C[0, 1]`. -/
noncomputable def p2ToL2 : Polynomial.degreeLT ℝ 3 →ₗ[ℝ] L2C 0 1 :=
  (Section_6C.polyL2 0 1).comp (Polynomial.degreeLT ℝ 3).subtype

theorem p2ToL2_injective : Function.Injective p2ToL2 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  -- p vanishes at every point of [0, 1], so it has infinitely many roots
  have hroot : ∀ x ∈ Set.Icc (0 : ℝ) 1, (p : Polynomial ℝ).IsRoot x := fun x hx =>
    congrArg (fun f : C(Set.Icc (0 : ℝ) 1, ℝ) => f ⟨x, hx⟩) hp
  exact Subtype.ext (Polynomial.eq_zero_of_infinite_isRoot _
    ((Set.Icc_infinite zero_lt_one).mono hroot))

noncomputable instance : NormedAddCommGroup (Polynomial.degreeLT ℝ 3) :=
  NormedAddCommGroup.induced _ _ p2ToL2 p2ToL2_injective

noncomputable instance : InnerProductSpace ℝ (Polynomial.degreeLT ℝ 3) :=
  InnerProductSpace.induced p2ToL2

/-- The induced inner product is {lit}`⟨p, q⟩ = ∫₀¹ pq`. -/
theorem inner_p2 (p q : Polynomial.degreeLT ℝ 3) :
    ⟪p, q⟫_ℝ = ∫ x in (0 : ℝ)..1, (p : Polynomial ℝ).eval x * (q : Polynomial ℝ).eval x :=
  Section_6C.inner_polyL2 _ _

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
  -- take p = x and q = 1, then ⟨Tp, q⟩ = ⟪x, 1⟫ = ∫₀¹ x * 1 = 1/2
  -- but ⟨p, Tq⟩ = ⟪x, 0⟫ = ∫₀¹ x * 0 = 0
  -- so ⟨Tp, q⟩ ≠ ⟨p, Tq⟩, hence T is not self-adjoint.
  -- for b) the key missing piece is that 1,x,x^2 is not an orthonormal basis.
  intro h
  let p : Polynomial.degreeLT ℝ 3 := ⟨Polynomial.X, by
    rw [Polynomial.mem_degreeLT, Polynomial.degree_X]; norm_num⟩
  let q : Polynomial.degreeLT ℝ 3 := ⟨1, by
    rw [Polynomial.mem_degreeLT, Polynomial.degree_one]; norm_num⟩
  have := h p q
  rw [inner_p2, inner_p2] at this
  simp [exercise_7A_14_T, p, q, Polynomial.coeff_one] at this

/-- An invertible operator {lit}`T` as a unit of the ring {lit}`ℒ(V)`. -/
noncomputable def endUnit (T : V ≃ₗ[𝕜] V) : (Module.End 𝕜 V)ˣ where
  val := T
  inv := T.symm
  val_inv := by ext; simp
  inv_val := by ext; simp

/-- 7.5 (f) as a unit: {lit}`T*` is invertible with inverse {lit}`(T⁻¹)*`. -/
noncomputable def adjointUnit (T : V ≃ₗ[𝕜] V) : (Module.End 𝕜 V)ˣ where
  val := (T : V →ₗ[𝕜] V)†
  inv := (T.symm : V →ₗ[𝕜] V)†
  val_inv := (adjoint_inv _ _ (endUnit T).inv_val (endUnit T).val_inv).1
  inv_val := (adjoint_inv _ _ (endUnit T).inv_val (endUnit T).val_inv).2

/-- 7A.15 (a) For invertible {lit}`T`, {lit}`T` is self-adjoint iff {lit}`T⁻¹` is
self-adjoint. -/
theorem exercise_7A_15a (T : V ≃ₗ[𝕜] V) :
    LinearMap.IsSymmetric (T : V →ₗ[𝕜] V) ↔
      LinearMap.IsSymmetric (T.symm : V →ₗ[𝕜] V) := by
  -- TT⁻¹ = I, so T⁻¹† T† = I† = I, hence T⁻¹† = T†⁻¹
  -- T† = T ↔ T†⁻¹ = T⁻¹ ↔ T⁻¹† = T⁻¹
  rw [isSelfAdjoint_iff, isSelfAdjoint_iff]
  calc (T : V →ₗ[𝕜] V)† = T ↔ adjointUnit T = endUnit T := by
        rw [Units.ext_iff]; rfl
    _ ↔ (adjointUnit T)⁻¹ = (endUnit T)⁻¹ := inv_inj.symm
    _ ↔ (T.symm : V →ₗ[𝕜] V)† = T.symm := Units.ext_iff

/-- 7A.15 (b) For invertible {lit}`T`, {lit}`T` is normal iff {lit}`T⁻¹` is
normal. -/
theorem exercise_7A_15b (T : V ≃ₗ[𝕜] V) :
    IsStarNormal (T : V →ₗ[𝕜] V) ↔ IsStarNormal (T.symm : V →ₗ[𝕜] V) := by
  -- TT† = T†T ↔ (TT†)⁻¹ = (T†T)⁻¹ ↔ T⁻¹T†⁻¹ = T†⁻¹T⁻¹ ↔ T⁻¹ is normal
  -- where we know TT† and T†T are invertible
  -- because they are products of invertible operators.
  simp only [normal_iff_comp, ← Module.End.mul_eq_comp]
  calc (T : V →ₗ[𝕜] V)† * T = T * (T : V →ₗ[𝕜] V)† ↔
        adjointUnit T * endUnit T = endUnit T * adjointUnit T := by
        rw [Units.ext_iff]; rfl
    _ ↔ (adjointUnit T * endUnit T)⁻¹ = (endUnit T * adjointUnit T)⁻¹ := inv_inj.symm
    _ ↔ (endUnit T)⁻¹ * (adjointUnit T)⁻¹ = (adjointUnit T)⁻¹ * (endUnit T)⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev]
    _ ↔ (T.symm : V →ₗ[𝕜] V) * (T.symm : V →ₗ[𝕜] V)† =
        (T.symm : V →ₗ[𝕜] V)† * T.symm := Units.ext_iff
    _ ↔ _ := eq_comm

/-- The dimension asked for in 7A.16(b), as a function of {lit}`n = dim V`. -/
def exercise_7A_16_sol (n : ℕ) : ℕ :=
  (n + 1) * n / 2

/-- 7A.16 For {lit}`𝔽 = ℝ`: (a) the self-adjoint operators form a subspace of
{lit}`ℒ(V)`; (b) what is the dimension of this subspace. -/
theorem exercise_7A_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] :
    ∃ U : Submodule ℝ (V →ₗ[ℝ] V),
      (∀ T, T ∈ U ↔ LinearMap.IsSymmetric T) ∧
        finrank ℝ U = exercise_7A_16_sol (finrank ℝ V) := by
  rw [exercise_7A_16_sol]
  -- we showed (S + T)* = S* + T* and (c • T)* = conj c • T*, so the self-adjoint operators form a subspace.
  -- pick a basis and argue about dimension using matrices
  -- the subspace is spanned by matrices that zero except Aij=Aji=1 for some i ≤ j
  -- thus dimension is (n + 1)n /2
  -- (formally: T ↦ (⟨eᵢ, T eⱼ⟩) indexed by unordered pairs {i, j} is a linear bijection
  --  onto functions on unordered pairs, of which there are (n+1 choose 2) = (n + 1)n/2)
  -- (a) T* = T is preserved by + and scalar multiplication (7.5 (a), (b))
  let U : Submodule ℝ (V →ₗ[ℝ] V) :=
    { carrier := {T | T† = T}
      add_mem' := fun {S T} hS hT => by
        simp only [Set.mem_ofPred_eq] at *; rw [adjoint_add, hS, hT]
      zero_mem' := map_zero LinearMap.adjoint
      smul_mem' := fun c T hT => by
        simp only [Set.mem_ofPred_eq] at *; rw [adjoint_smul, hT, conj_trivial] }
  refine ⟨U, fun T => (isSelfAdjoint_iff T).symm, ?_⟩
  -- (b) in an orthonormal basis, T ∈ U is determined by ⟨eᵢ, T eⱼ⟩ for unordered {i, j}
  set n := finrank ℝ V
  let b := stdOrthonormalBasis ℝ V
  have hsymm : ∀ T : U, ∀ i j, ⟪b i, T.1 (b j)⟫ = ⟪b j, T.1 (b i)⟫ := by
    intro T i j
    rw [real_inner_comm, adjoint_inner, T.2]
  let φ : U →ₗ[ℝ] (Sym2 (Fin n) → ℝ) :=
    { toFun T := Sym2.lift ⟨fun i j => ⟪b i, T.1 (b j)⟫, hsymm T⟩
      map_add' S T := by
        funext s; induction s using Sym2.ind
        simp [Sym2.lift_mk, inner_add_right]
      map_smul' c T := by
        funext s; induction s using Sym2.ind
        simp [Sym2.lift_mk, inner_smul_right] }
  have hentry : ∀ (T : V →ₗ[ℝ] V) i j,
      LinearMap.toMatrix b.toBasis b.toBasis T i j = ⟪b i, T (b j)⟫ := by
    intro T i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    have h0 : ∀ i j, ⟪b i, T.1 (b j)⟫ = 0 := fun i j => by
      simpa [φ, Sym2.lift_mk] using congrFun hT s(i, j)
    refine Subtype.ext (b.toBasis.ext fun j => ?_)
    exact InnerProductSpace.ext_inner_left_basis b.toBasis fun i => by simpa using h0 i j
  have hsurj : Function.Surjective φ := by
    intro f
    -- the symmetric matrix A i j = f {i, j} gives an operator T with T* = T (7.9)
    let A : Matrix (Fin n) (Fin n) ℝ := fun i j => f s(i, j)
    let T := Matrix.toLin b.toBasis b.toBasis A
    have hT : LinearMap.toMatrix b.toBasis b.toBasis T = A := LinearMap.toMatrix_toLin _ _ _
    have hA : Aᴴ = A := by
      ext i j; rw [Matrix.conjTranspose_apply, star_trivial]; exact congrArg f Sym2.eq_swap
    have hTU : T† = T := by
      rw [← Matrix.toLin_toMatrix b.toBasis b.toBasis T†, toMatrix_adjoint_eq_conjTranspose,
        hT, hA]
    refine ⟨⟨T, hTU⟩, ?_⟩
    funext s; induction s using Sym2.ind with | _ i j => ?_
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Sym2.lift_mk]
    rw [← hentry, hT]
  rw [(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel]

/-- 7A.17 For {lit}`𝔽 = ℂ` and {lit}`V ≠ 0`, the self-adjoint operators do not
form a subspace of {lit}`ℒ(V)`. -/
theorem exercise_7A_17 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] :
    ¬ ∃ U : Submodule ℂ (V →ₗ[ℂ] V), ∀ T, T ∈ U ↔ LinearMap.IsSymmetric T := by
  -- (cS)* = conj c S*, which breaks scalar multiplication.
  -- so I is self-adjoint, but i I is not, which shows the set is not closed under scalar multiplication.
  rintro ⟨U, hU⟩
  have hI : (LinearMap.id : V →ₗ[ℂ] V) ∈ U := (hU _).mpr ((isSelfAdjoint_iff _).mpr adjoint_id)
  -- (i I)* = conj i · I* = -i I, which must equal i I
  have h := (isSelfAdjoint_iff _).mp ((hU _).mp (U.smul_mem Complex.I hI))
  rw [adjoint_smul, adjoint_id] at h
  -- apply both sides to some v ≠ 0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hv' := LinearMap.congr_fun h v
  simp only [Complex.conj_I, neg_smul, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hv'
  -- -(i v) = i v gives (2i) v = 0
  have h2 : (2 * Complex.I) • v = 0 := by
    rw [two_mul, add_smul]
    nth_rw 1 [← hv']
    exact neg_add_cancel _
  exact ((smul_eq_zero.mp h2).resolve_left (by simp [Complex.I_ne_zero])) |> hv

/-- 7A.18 If {lit}`dim V ≥ 2`, the normal operators do not form a subspace of
{lit}`ℒ(V)`. -/
theorem exercise_7A_18 (h : 2 ≤ finrank 𝕜 V) :
    ¬ ∃ U : Submodule 𝕜 (V →ₗ[𝕜] V), ∀ T, T ∈ U ↔ IsStarNormal T := by
  -- take A(x,y) = (-y, x) (for two basis vectors) as we shown earlier it is normal, but not self-adjoint
  -- also easy to see since A* = -A, and by characterization of normal as sum of commuting self-adjoint and skew-adjoint parts
  -- let B = 𝟙, easy to see that B is self-adjoint hence normal
  -- but AB ≠ BA easy to check
  -- then (B + A)* = B - A
  -- so (B + A)(B + A)* = BB - BA + AB - AA
  -- while (B + A)*(B + A) = BB + BA - AB - AA
  -- so B + A is not normal, hence the normal operators do not form a subspace
  rintro ⟨U, hU⟩
  let b := stdOrthonormalBasis 𝕜 V
  let i₀ : Fin (finrank 𝕜 V) := ⟨0, by omega⟩
  let i₁ : Fin (finrank 𝕜 V) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  -- E i j v = ⟨e j, v⟩ e i, whose adjoint is E j i (as in 7.3)
  let E : Fin (finrank 𝕜 V) → Fin (finrank 𝕜 V) → V →ₗ[𝕜] V :=
    fun i j => (innerₛₗ 𝕜 (b j)).smulRight (b i)
  have hE : ∀ i j, (E i j)† = E j i := by
    intro i j
    ext w : 1
    refine ext_inner_left 𝕜 fun v => ?_
    rw [← adjoint_inner]
    simp only [E, LinearMap.smulRight_apply, innerₛₗ_apply_apply, inner_smul_left,
      inner_smul_right, inner_conj_symm]
    ring
  -- A(x, y) = (-y, x) and B = 𝟙 (the all-ones matrix, B(x, y) = (x + y, x + y))
  -- on span(e₀, e₁)
  let A := E i₁ i₀ - E i₀ i₁
  let B := E i₀ i₀ + E i₀ i₁ + E i₁ i₀ + E i₁ i₁
  have hA : A† = -A := by rw [map_sub, hE, hE, neg_sub]
  have hB : B† = B := by
    show (E i₀ i₀ + E i₀ i₁ + E i₁ i₀ + E i₁ i₁)† = E i₀ i₀ + E i₀ i₁ + E i₁ i₀ + E i₁ i₁
    rw [adjoint_add, adjoint_add, adjoint_add, hE, hE, hE, hE]
    abel
  have hAn : IsStarNormal A := by
    rw [normal_iff_comp, hA]
    ext v; simp
  have hBn : IsStarNormal B := symmetric_isStarNormal ((isSelfAdjoint_iff B).mpr hB)
  have hN := (hU _).mp (U.add_mem ((hU B).mpr hBn) ((hU A).mpr hAn))
  -- (B + A)* = B - A, so normality of B + A says (B - A)(B + A) = (B + A)(B - A)
  rw [normal_iff_comp, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, adjoint_add, hA,
    hB] at hN
  -- the two products differ by 2(BA - AB), so AB = BA
  have hcomm : B * A = A * B := by
    have h2 : (2 : 𝕜) • (B * A - A * B) = 0 := by
      rw [two_smul]
      calc (B * A - A * B) + (B * A - A * B) = (B + -A) * (B + A) - (B + A) * (B + -A) := by
            noncomm_ring
        _ = 0 := by rw [hN, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left two_ne_zero)
  -- but AB ≠ BA: BAe₀ = Be₁ = e₀ + e₁ while ABe₀ = A(e₀ + e₁) = e₁ - e₀;
  -- comparing e₀-coordinates gives 1 = -1
  have := congrArg (fun x => ⟪b i₀, x⟫_𝕜) (LinearMap.congr_fun hcomm (b i₀))
  simp [A, B, E, b.inner_eq_zero h01, b.inner_eq_zero h01.symm, Module.End.mul_apply,
    inner_add_right, inner_sub_right] at this
  norm_num at this


/-- 7A.19 If {lit}`‖T*v‖ ≤ ‖Tv‖` for every {lit}`v`, then {lit}`T` is normal. -/
theorem exercise_7A_19 (T : V →ₗ[𝕜] V)
    (h : ∀ v, ‖T† v‖ ≤ ‖T v‖) : IsStarNormal T := by
  -- we showed that if ‖T† v‖ = ‖T v‖ for all v, then T is normal.
  -- we proved the ∑‖T ei‖^2 = ∑‖T† ei‖^2 for any orthonormal basis {ei} in ex5.
  -- but if each ‖T† ei‖ ≤ ‖T ei‖, then the equation above can only happen
  -- if each is an equality.
  -- To prove it for any v, we extend v / ‖v‖ to an orthonormal basis {ei}
  -- then we get ‖T† v‖ = ‖v‖ * ‖T† v / ‖v‖‖ = ‖v‖ * ‖T v / ‖v‖‖ = ‖T v‖
  rw [normal_iff_norm]
  intro v
  by_cases hv : v = 0
  · simp [hv]
  -- u = v / ‖v‖ is a unit vector; extend {u} to an orthonormal basis
  set u := ((‖v‖⁻¹ : ℝ) : 𝕜) • v with hu_def
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hnv]
  have hs : Orthonormal 𝕜 ((↑) : ({u} : Set V) → V) :=
    ⟨fun i => by rw [show (i : V) = u from i.2]; exact hu,
      fun i j hij => absurd (Subtype.ext (i.2.trans j.2.symm)) hij⟩
  obtain ⟨s, b, hsub, hb⟩ := hs.exists_orthonormalBasis_extension
  -- index the basis by Fin n so that ex5 applies; k₀ is the position of u
  let e := b.reindex (Fintype.equivFin s)
  let k₀ := Fintype.equivFin s ⟨u, hsub rfl⟩
  have he : e k₀ = u := by simp [e, k₀, hb]
  -- ex5 (with f = e): ∑ ‖T eₖ‖² = ∑ ‖T† eₖ‖², and termwise ‖T† eₖ‖² ≤ ‖T eₖ‖²
  have hsum := exercise_7A_5 T e e
  have hle : ∀ k ∈ Finset.univ, ‖T† (e k)‖ ^ 2 ≤ ‖T (e k)‖ ^ 2 := fun k _ =>
    pow_le_pow_left₀ (norm_nonneg _) (h _) 2
  have hk := (Finset.sum_eq_sum_iff_of_le hle).mp hsum.symm k₀ (Finset.mem_univ _)
  rw [he, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] at hk
  -- undo the scaling: ‖T u‖ = ‖v‖⁻¹ ‖T v‖, likewise for T†
  rw [hu_def, map_smul, map_smul, norm_smul, norm_smul] at hk
  exact (mul_left_cancel₀ (by simpa using hnv) hk).symm

/-- 7A.20 If {lit}`P² = P`, the following are equivalent: (a) {lit}`P` self-adjoint;
(b) {lit}`P` normal; (c) {lit}`P = P_U` for some subspace {lit}`U`. -/
theorem exercise_7A_20 (P : V →ₗ[𝕜] V) (hP : P ∘ₗ P = P) :
    [LinearMap.IsSymmetric P, IsStarNormal P,
      ∃ U : Submodule 𝕜 V, (U.starProjection : V →ₗ[𝕜] V) = P].TFAE := by
  -- 1 => 2 true dor all symmetric
  -- 2 => 3 we have proven for normal null P ⊥ range P and in 6C we proved that P^2 = P and that
  --   is enough to show that P is the star projection onto its range.
  -- 3 => 1 pick an orthnormal basis for U and extend it to an orthonormal basis for V
  --   in this basis P is represented by a diagonal matrix with 1's on the diagonal corresponding to U and 0's elsewhere
  --   which is clearly symmetric.
  tfae_have 1 → 2 := symmetric_isStarNormal
  tfae_have 2 → 3 := fun hN => by
    refine LADR.Section_6C.exercise_6C_9 P hP fun x hx y hy => ?_
    -- null P = null P* = (range P)⟂ (7.21, 7.6)
    rw [ker_eq_ker_adjoint hN, ker_adjoint] at hx
    exact Submodule.inner_left_of_mem_orthogonal hy hx
  tfae_have 3 → 1 := by
    classical
    rintro ⟨U, rfl⟩
    -- an orthonormal basis of U, viewed in V, extended to an orthonormal basis b of V
    let bU := stdOrthonormalBasis 𝕜 U
    let s : Set V := Set.range fun i => (bU i : V)
    have hs : Orthonormal 𝕜 ((↑) : s → V) :=
      (orthonormal_subtype_range (Subtype.val_injective.comp bU.toBasis.injective)).mpr
        (bU.orthonormal.comp_linearIsometry U.subtypeₗᵢ)
    obtain ⟨u, b, hsu, hb⟩ := hs.exists_orthonormalBasis_extension
    have hspan : Submodule.span 𝕜 s = U := by
      rw [show s = U.subtype '' Set.range bU from Set.range_comp U.subtype bU,
        Submodule.span_image, ← OrthonormalBasis.coe_toBasis, bU.toBasis.span_eq,
        Submodule.map_subtype_top]
    -- P_U fixes the basis vectors from U and kills the others (they lie in U⟂)
    let d : u → 𝕜 := fun j => if (j : V) ∈ s then 1 else 0
    have hPb : ∀ j, U.starProjection (b j) = d j • b j := by
      intro j
      by_cases hj : (j : V) ∈ s
      · simp only [d, hj, ↓reduceIte, one_smul, hb]
        rw [Submodule.starProjection_eq_self_iff, ← hspan]
        exact Submodule.subset_span hj
      · simp only [d, hj, ↓reduceIte, zero_smul, hb]
        rw [Submodule.starProjection_apply_eq_zero_iff, ← hspan, Submodule.mem_orthogonal']
        -- for y ∈ s, y ≠ j are distinct basis vectors, so ⟨j, y⟩ = 0
        intro y hy
        rw [Submodule.mem_span_set'] at hy
        obtain ⟨n, c, x, rfl⟩ := hy
        rw [inner_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        have hne : (⟨(x i : V), hsu (x i).2⟩ : u) ≠ j := fun h => hj (h ▸ (x i).2)
        have := orthonormal_iff_ite.mp b.orthonormal j ⟨x i, hsu (x i).2⟩
        rw [hb] at this
        rw [inner_smul_right, this, ite_eq_right (Ne.symm hne), mul_zero]
    -- so the matrix of P_U in b is diagonal with entries 0, 1, hence equals its conjugate
    -- transpose, and P_U* = P_U by 7.9
    have hM : LinearMap.toMatrix b.toBasis b.toBasis U.starProjection = Matrix.diagonal d := by
      ext i j
      rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply, ContinuousLinearMap.coe_coe,
        hPb, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal, Matrix.diagonal_apply]
      split_ifs with h <;> simp [h]
    have hd : star d = d := by
      funext j; simp only [Pi.star_apply, d]; split_ifs <;> simp
    rw [isSelfAdjoint_iff]
    apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    rw [toMatrix_adjoint_eq_conjTranspose, hM, Matrix.diagonal_conjTranspose, hd]
  tfae_finish

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
  -- by contra, assume there is an inner product s.t. D is normal
  -- we have proved that then V = null space of D ⨁ range of D
  -- but constants are both in null of D and in the range (D cx = c)
  rintro ⟨c, S, hadj, hcomm⟩
  -- make c the inner product of 𝒫₈(ℝ), so the normal-operator theorems apply
  let _ : InnerProductSpace.Core ℝ (Polynomial.degreeLT ℝ 9) := c
  let _ : NormedAddCommGroup (Polynomial.degreeLT ℝ 9) := c.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ (Polynomial.degreeLT ℝ 9) := InnerProductSpace.ofCore _
  have : FiniteDimensional ℝ (Polynomial.degreeLT ℝ 9) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv ℝ 9).symm
  -- S is the adjoint of D, so DS = SD says D is normal
  have hDS : D = S† := (LinearMap.eq_adjoint_iff D S).mpr hadj
  have hS : D† = S := by rw [hDS, adjoint_adjoint]
  have hN : IsStarNormal D := by rw [normal_iff_comp, hS]; exact hcomm.symm
  -- 7.21 (c): null D ⊕ range D = V, so null D ∩ range D = 0
  have hC := isCompl_ker_range hN
  -- but 1 is in both: D 1 = 0 and D x = 1
  let one : Polynomial.degreeLT ℝ 9 := ⟨1, by
    rw [Polynomial.mem_degreeLT, Polynomial.degree_one]; norm_num⟩
  let x : Polynomial.degreeLT ℝ 9 := ⟨Polynomial.X, by
    rw [Polynomial.mem_degreeLT, Polynomial.degree_X]; norm_num⟩
  have h₁ : one ∈ LinearMap.ker D := by
    rw [LinearMap.mem_ker]; exact Subtype.ext (by rw [hD]; exact Polynomial.derivative_one)
  have h₂ : one ∈ LinearMap.range D :=
    ⟨x, Subtype.ext (by rw [hD]; exact Polynomial.derivative_X)⟩
  have h0 : one = 0 := Submodule.disjoint_def.mp hC.disjoint one h₁ h₂
  exact one_ne_zero (congrArg Subtype.val h0 : (1 : Polynomial ℝ) = 0)

/-- The operator on {lit}`ℝ³` asked for in 7A.22. Fill it in. -/
noncomputable def exercise_7A_22_sol :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  -- 90 deg rotatation in x-y plane
  { toFun v := !₂[- v 1, v 0, v 2]
    map_add' u v := by ext i; fin_cases i <;> simp; ring
    map_smul' a v := by ext i; fin_cases i <;> simp }

/-- 7A.22 There is an operator on {lit}`ℝ³` that is normal but not self-adjoint. -/
theorem exercise_7A_22 :
    IsStarNormal exercise_7A_22_sol ∧ ¬ LinearMap.IsSymmetric exercise_7A_22_sol := by
  -- the adjoint is the rotation the other way, R(x, y, z) = (y, -x, z) (as in 7A.11)
  let R : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toFun v := !₂[v 1, - v 0, v 2]
      map_add' u v := by ext i; fin_cases i <;> simp; ring
      map_smul' a v := by ext i; fin_cases i <;> simp }
  have ha : exercise_7A_22_sol† = R := by
    ext v : 1
    refine ext_inner_left ℝ fun u => ?_
    rw [← adjoint_inner]
    simp [exercise_7A_22_sol, R, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  refine ⟨?_, ?_⟩
  · -- R T = T R = the identity on z, minus the identity on the x-y plane
    rw [normal_iff_comp, ha]
    ext v i
    fin_cases i <;> simp [exercise_7A_22_sol, R]
  · -- T(0, 1, 0) = (-1, 0, 0) but T*(0, 1, 0) = (1, 0, 0)
    rw [isSelfAdjoint_iff, ha]
    intro h
    have := congrArg (· 0) (LinearMap.congr_fun h !₂[0, 1, 0])
    norm_num [exercise_7A_22_sol, R] at this

/-- 7A.23 If {lit}`T` is normal, {lit}`‖v‖ = ‖w‖ = 2`, {lit}`Tv = 3v`,
{lit}`Tw = 4w`, then {lit}`‖T(v + w)‖ = 10`. -/
theorem exercise_7A_23 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) {v w : V}
    (hv : ‖v‖ = 2) (hw : ‖w‖ = 2) (hTv : T v = (3 : 𝕜) • v) (hTw : T w = (4 : 𝕜) • w) :
    ‖T (v + w)‖ = 10 := by
  -- w and v are eigenvectors of distinct eigenvalues, so orthogonal by earlier theorem
  -- ⟪T v, T w⟫ = ⟪3 v, 4 w⟫ = 12 ⟪v, w⟫ = 0, so T v and T w are orthogonal too
  -- then ‖T(v + w)‖² = ‖T v‖² + ‖T w‖² = 9‖v‖² + 16‖w‖² = 9·4 + 16·4 = 100, so ‖T(v + w)‖ = 10
  have h0 : ⟪v, w⟫_𝕜 = 0 := orthogonal_eigenvectors hT (by norm_num) hTv hTw
  have h1 : ⟪T v, T w⟫_𝕜 = 0 := by
    rw [hTv, hTw, inner_smul_left, inner_smul_right, h0, mul_zero, mul_zero]
  -- Pythagoras (6.12) for T v ⟂ T w
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h1
  rw [← map_add] at hp
  have h6 : ‖T v‖ = 6 := by rw [hTv, norm_smul, hv]; norm_num
  have h8 : ‖T w‖ = 8 := by rw [hTw, norm_smul, hw]; norm_num
  rw [h6, h8] at hp
  nlinarith [norm_nonneg (T (v + w))]

/-- 7A.24 If the minimal polynomial of {lit}`T` is {lit}`∑ aₖ zᵏ + zᵐ`, then the
minimal polynomial of {lit}`T*` has the conjugated coefficients — i.e. it is
{lit}`(minpoly T)` with {lit}`conj` applied to each coefficient. -/
theorem exercise_7A_24 (T : V →ₗ[𝕜] V) :
    minpoly 𝕜 T† = (minpoly 𝕜 T).map (starRingEnd 𝕜) := by
  -- p(T) = 0 iff ⟨pT v, w⟩ = 0 for all v, w iff
  -- ⟨v, p(T)† w⟩ = 0 for all v,w, where p(T)† is map conj to p coeffs.
  -- iff p(T)† = 0
  -- so the set of polynomials that annihilate T† is the set of polynomials obtained
  -- by conjugating the coefficients of polynomials that annihilate T.
  -- thus the minimal polynomial of T† is obtained by conjugating the coefficients of the minimal polynomial of T.
  -- key step: p(S)† = p̄(S†), by 7.5 (a), (b), (d) on p = ∑ aₙ zⁿ
  have hpow : ∀ (S : V →ₗ[𝕜] V) (n : ℕ), (S ^ n)† = S† ^ n := by
    intro S n
    induction n with
    | zero => rw [pow_zero, pow_zero, adjoint_one]
    | succ n ih =>
      rw [pow_succ, Module.End.mul_eq_comp, adjoint_comp, ih, ← Module.End.mul_eq_comp,
        ← pow_succ']
  have key : ∀ (S : V →ₗ[𝕜] V) (p : Polynomial 𝕜),
      (Polynomial.aeval S p)† = Polynomial.aeval S† (p.map (starRingEnd 𝕜)) := by
    intro S p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, adjoint_add, hp, hq, Polynomial.map_add, map_add]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        ← Algebra.smul_def, ← Algebra.smul_def, adjoint_smul, hpow]
  have hconj : ∀ p : Polynomial 𝕜, (p.map (starRingEnd 𝕜)).map (starRingEnd 𝕜) = p := by
    intro p; ext n; simp
  -- so p̄ kills T† exactly when p kills T
  have hiff : ∀ p : Polynomial 𝕜,
      Polynomial.aeval T† (p.map (starRingEnd 𝕜)) = 0 ↔ Polynomial.aeval T p = 0 := by
    intro p
    rw [← key, show (Polynomial.aeval T p)† = 0 ↔ Polynomial.aeval T p = 0 from
      ⟨fun h => by rw [← adjoint_adjoint (Polynomial.aeval T p), h, map_zero], fun h => by
        rw [h, map_zero]⟩]
  have hmon := (minpoly.monic (Algebra.IsIntegral.isIntegral (R := 𝕜) T)).map (starRingEnd 𝕜)
  refine (minpoly.unique 𝕜 T† hmon ((hiff _).mpr (minpoly.aeval 𝕜 T)) fun q hq hq0 => ?_).symm
  -- minimality: if q kills T†, then q̄ kills T, so deg minpoly T ≤ deg q̄ = deg q
  rw [Polynomial.degree_map]
  have hq' : Polynomial.aeval T (q.map (starRingEnd 𝕜)) = 0 := by
    rw [← hiff, hconj]; exact hq0
  have := minpoly.min 𝕜 T (hq.map (starRingEnd 𝕜)) hq'
  rwa [Polynomial.degree_map] at this

/-- 7A.25 {lit}`T` is diagonalizable iff {lit}`T*` is diagonalizable, using the
{lit}`5.50` definition {name}`LADR.Section_5D.IsDiagonalizable`. -/
theorem exercise_7A_25 (T : V →ₗ[𝕜] V) :
    Section_5D.IsDiagonalizable T ↔
      Section_5D.IsDiagonalizable T† := by
  -- by theorem, T is diagonalizable iff its minimal polynomial
  -- splits into distinct linear factors.
  -- by ex24, we know that minpoly T† is the conjugate of minpoly T,
  -- so the roots are conjugated, but distinct split of one implies
  -- distinct split of the other and vice versa.
  have hconj : ∀ s : Finset 𝕜,
      (∏ a ∈ s, (Polynomial.X - Polynomial.C a)).map (starRingEnd 𝕜) =
        ∏ a ∈ s.image (starRingEnd 𝕜), (Polynomial.X - Polynomial.C a) := by
    intro s
    rw [Polynomial.map_prod, Finset.prod_image fun a _ b _ h => (starRingEnd 𝕜).injective h]
    simp [Polynomial.map_sub]
  have hT : minpoly 𝕜 T = (minpoly 𝕜 T†).map (starRingEnd 𝕜) := by
    rw [exercise_7A_24]; ext n; simp
  rw [Section_5D.isDiagonalizable_iff_minpoly_eq_prod_distinct,
    Section_5D.isDiagonalizable_iff_minpoly_eq_prod_distinct]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s.image (starRingEnd 𝕜), by rw [exercise_7A_24, hs, hconj]⟩
  · rintro ⟨s, hs⟩
    exact ⟨s.image (starRingEnd 𝕜), by rw [hT, hs, hconj]⟩

/-- The adjoint of {lit}`T v = ⟨v, u⟩ x` is {lit}`T* w = ⟨w, x⟩ u` (used in 7A.26). -/
theorem adjoint_rankOne {u x : V} {T : V →ₗ[𝕜] V} (hT : ∀ v, T v = ⟪u, v⟫_𝕜 • x)
    (w : V) : T† w = ⟪x, w⟫_𝕜 • u := by
  -- ⟨Tv, w⟩ = ⟨v, u⟩⟨x, w⟩ = ⟨v, ⟨w, x⟩ u⟩ for every v
  apply ext_inner_left 𝕜
  intro v
  rw [← adjoint_inner, hT, inner_smul_left, inner_conj_symm, inner_smul_right, mul_comm]

/-- 7A.26 (a) On a real inner product space, for {lit}`T v = ⟨v, u⟩ x` the
operator {lit}`T` is self-adjoint iff the list {lit}`u, x` is linearly
dependent. -/
theorem exercise_7A_26a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (u x : V) (T : V →ₗ[ℝ] V)
    (hT : ∀ v, T v = ⟪u, v⟫_ℝ • x) :
    LinearMap.IsSymmetric T ↔ ¬ LinearIndependent ℝ ![u, x] := by
  -- in ℝ (axler notation)
  -- ⟪T v, w⟫ = ⟪⟪v, u⟫_ℝ • x, w⟫ =  ⟪v, u⟫_ℝ ⟪x, w⟫ = ⟪v, ⟪x, w⟫ u⟫
  -- so T* v = ⟪x, v⟫ u
  -- => if Tv = T*v, then ⟪u, v⟫_ℝ • x = ⟪x, v⟫_ℝ • u for all v
  -- this implies x and u are collinear.
  -- <= if x or u is 0, trivially T = T*
  -- assume x = c u for some c otherwise
  -- Tv = ⟪u, v⟫ c u and T*v = ⟪v, c u⟫ u = c ⟪u, v⟫ u
  have hadj := adjoint_rankOne hT
  rw [isSelfAdjoint_iff]
  by_cases hu : u = 0
  · -- u = 0: T = 0 = T*, and the list 0, x is dependent
    subst hu
    exact iff_of_true (by ext v; simp [hadj, hT]) (fun h => h.ne_zero 0 (by simp))
  simp only [LinearIndependent.pair_iff' hu, not_forall, not_not]
  constructor
  · -- T*u = Tu gives ⟪x, u⟫ u = ‖u‖² x, so x = (⟪x, u⟫ / ‖u‖²) u
    intro h
    have h' : ⟪x, u⟫_ℝ • u = ⟪u, u⟫_ℝ • x := by rw [← hadj, h, hT]
    have hne : ⟪u, u⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr hu
    exact ⟨⟪x, u⟫_ℝ / ⟪u, u⟫_ℝ, by rw [div_eq_inv_mul, mul_smul, h', inv_smul_smul₀ hne]⟩
  · rintro ⟨c, rfl⟩
    ext v
    rw [hadj, hT, real_inner_smul_left, smul_smul, mul_comm c]

/-- 7A.26 (b) For {lit}`T v = ⟨v, u⟩ x`, {lit}`T` is normal iff the list
{lit}`u, x` is linearly dependent. -/
theorem exercise_7A_26b (u x : V) (T : V →ₗ[𝕜] V) (hT : ∀ v, T v = ⟪u, v⟫_𝕜 • x) :
    IsStarNormal T ↔ ¬ LinearIndependent 𝕜 ![u, x] := by
  -- in ℂ
  -- ⟪T v, w⟫ = ⟪⟪v, u⟫ • x, w⟫ =  ⟪v, u⟫ ⟪x, w⟫ = ⟪v, u⟫ ⟪x, w⟫
  -- = ⟪v, (conj ⟪x, w⟫) u⟫ = ⟪v, ⟪w, x⟫ u⟫
  -- so T* w = ⟪w, x⟫ u

  -- now TT* v = T (T* v) = T (⟪v, x⟫ u) = ⟪v, x⟫ T u = ⟪v, x⟫ ‖u‖^2 x
  -- and T*T v = T* (T v) = T* (⟪v, u⟫ x) = ⟪v, u⟫ T* x = ⟪v, u⟫ ‖x‖^2 u
  -- => if T is normal, then ⟪v, x⟫ ‖u‖^2 x = ⟪v, u⟫ ‖x‖^2 u for all v
  -- which means u and x have to be collinear: if x = 0 it's trivial, otherwise
  -- take v = x to get ‖x‖^2 ‖u‖^2 x = ⟪x, u⟫ ‖x‖^2 u, and divide by ‖x‖^2 ‖u‖^2.
  -- <= if either is 0 trivially normal,
  -- otherwise assume x = c u
  -- TT* v = ⟨v, cu⟩ ‖u‖^2 cu = (conj c * c) ⟪v, u⟫ ‖u‖^2 u = |c|^2 ⟪v, u⟫ ‖u‖^2 u
  -- T*T v = ⟨v, u⟩ ‖cu‖^2 u = |c|^2 ⟪v, u⟫ ‖u‖^2 u
  have hadj := adjoint_rankOne hT
  rw [normal_iff_comp]
  by_cases hu : u = 0
  · -- u = 0: T = 0 is normal, and the list 0, x is dependent
    subst hu
    exact iff_of_true (by ext v; simp [hadj, hT]) (fun h => h.ne_zero 0 (by simp))
  simp only [LinearIndependent.pair_iff' hu, not_forall, not_not]
  constructor
  · intro h
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    -- v = x: ⟪u, x⟫ ‖x‖² u = ‖x‖² ‖u‖² x
    have h' := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply, hT, hadj, inner_smul_right] at h'
    have hne : ⟪x, x⟫_𝕜 * ⟪u, u⟫_𝕜 ≠ 0 :=
      mul_ne_zero (inner_self_ne_zero.mpr hx) (inner_self_ne_zero.mpr hu)
    exact ⟨(⟪x, x⟫_𝕜 * ⟪u, u⟫_𝕜)⁻¹ * (⟪u, x⟫_𝕜 * ⟪x, x⟫_𝕜),
      by rw [mul_smul, h', inv_smul_smul₀ hne]⟩
  · -- x = c u: both sides are |c|² ⟪v, u⟫ ‖u‖² u
    rintro ⟨c, rfl⟩
    ext v
    simp only [LinearMap.comp_apply, hT, hadj, inner_smul_left, inner_smul_right, smul_smul]
    congr 1
    ring

/-- 7A.27 If {lit}`T` is normal, then {lit}`null Tᵏ = null T` and
{lit}`range Tᵏ = range T` for every positive integer {lit}`k`. -/
theorem exercise_7A_27 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (k : ℕ) (hk : 0 < k) :
    LinearMap.ker (T ^ k) = LinearMap.ker T ∧
      LinearMap.range (T ^ k) = LinearMap.range T := by
  -- for the first one, we know that if T normal, null T ⊥ range T
  -- since T v is in range T, it cannot be be annihilated by T, unless it is 0.
  -- so T (T v) = 0 implies T v = 0, which gives ker (T^2) = ker T.
  -- we can repeat it for any k by induction.
  -- for range, we notice that T^n is normal too (T^n* = (T*)^n)
  -- so since we know the null T^n, the range T^n is the orthogonal complement of null T^n
  -- which is same as range T.
  -- null T ∩ range T = 0 for normal T (7.21 (c))
  have hdisj := (isCompl_ker_range hT).disjoint
  have hker : ∀ n, 1 ≤ n → LinearMap.ker (T ^ n) = LinearMap.ker T := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rw [pow_one]
    | succ n hn ih =>
      ext v
      rw [LinearMap.mem_ker, LinearMap.mem_ker, pow_succ, Module.End.mul_apply]
      constructor
      · -- Tⁿ(Tv) = 0 gives T(Tv) = 0 by induction; Tv ∈ null T ∩ range T, so Tv = 0
        intro h
        have h1 : T v ∈ LinearMap.ker T := by
          rw [← ih]; exact h
        exact Submodule.disjoint_def.mp hdisj _ h1 ⟨v, rfl⟩
      · intro h; rw [h, map_zero]
  -- Tⁿ is normal, since (Tⁿ)* = (T*)ⁿ commutes with Tⁿ
  have hpow : IsStarNormal (T ^ k) := ⟨by rw [star_pow]; exact hT.star_comm_self.pow_pow k k⟩
  -- for normal S, range S = (null S*)⟂ = (null S)⟂ (7.6, 7.21)
  have hrange : ∀ S : V →ₗ[𝕜] V, IsStarNormal S → LinearMap.range S = (LinearMap.ker S)ᗮ :=
    fun S hS => by rw [range_eq_orthogonal_ker_adjoint, ← ker_eq_ker_adjoint hS]
  have hk' := hker k hk
  exact ⟨hk', by rw [hrange _ hpow, hrange _ hT, hk']⟩

/-- 7A.28 If {lit}`T` is normal, then for every {lit}`λ` the minimal polynomial of
{lit}`T` is not a polynomial multiple of {lit}`(z − λ)²`. -/
theorem exercise_7A_28 {T : V →ₗ[𝕜] V} (hT : IsStarNormal T) (μ : 𝕜) :
    ¬ (Polynomial.X - Polynomial.C μ) ^ 2 ∣ minpoly 𝕜 T := by
  -- this means there is a vector s.t. (T - μ)^2 v = 0,
  -- but (T - μ) v ≠ 0.
  -- To prove that say min poly = (x - μ)^2 q(x)
  -- There is at least one w s.t. (T - μ) q(T) w ≠ 0 (otherwise that's minpoly)
  -- Take v = q(x)w, then (T - μ) v ≠ 0 but (T - μ)^2 v = 0
  -- But we proved that (T - μ I) is normal (proved in the chapter)
  -- and for normal operators, ker T^n = ker T, which is contradiction
  open Polynomial in
  rintro ⟨q, hq⟩
  set S := T - μ • (1 : V →ₗ[𝕜] V) with hS_def
  have hS : aeval T (X - C μ) = S := by
    rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  -- (x - μ) q(x) has smaller degree than the minimal polynomial, so it doesn't kill T
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact minpoly.ne_zero (Algebra.IsIntegral.isIntegral T) (by rw [hq, mul_zero])
  have hne : aeval T ((X - C μ) * q) ≠ 0 := by
    intro h0
    -- minpoly would divide (x - μ) q, i.e. (x - μ)² q ∣ (x - μ) q, forcing (x - μ) ∣ 1
    have hdvd := minpoly.dvd 𝕜 T h0
    rw [hq, pow_two, mul_assoc] at hdvd
    have h1 : X - C μ ∣ 1 := (mul_dvd_mul_iff_right (mul_ne_zero (X_sub_C_ne_zero μ) hq0)).mp
      (by rwa [one_mul])
    exact not_isUnit_X_sub_C μ (isUnit_of_dvd_one h1)
  -- so some w has (T - μ) q(T) w ≠ 0; take v = q(T) w
  obtain ⟨w, hw⟩ : ∃ w, aeval T ((X - C μ) * q) w ≠ 0 := by
    by_contra! h; exact hne (LinearMap.ext h)
  set v := aeval T q w
  have hSv : S v ≠ 0 := by
    rwa [aeval_mul, hS, Module.End.mul_apply] at hw
  have hS2v : (S ^ 2) v = 0 := by
    have : aeval T (minpoly 𝕜 T) w = 0 := by rw [minpoly.aeval]; rfl
    rwa [hq, aeval_mul, map_pow, hS, Module.End.mul_apply] at this
  -- but T - μ is normal, so null (T - μ)² = null (T - μ) (7A.27)
  have hker := (exercise_7A_27 (sub_smul_normal hT μ) 2 (by norm_num)).1
  have : v ∈ LinearMap.ker (S ^ 2) := hS2v
  rw [hker] at this
  exact hSv this

/-- 7A.29 Prove or give a counterexample: if there is an orthonormal basis
{lit}`e₁, …, eₙ` of {lit}`V` with {lit}`‖Teₖ‖ = ‖T*eₖ‖` for each {lit}`k`, then
{lit}`T` is normal. -/
def exercise_7A_29.{u} {𝕜 : Type u} [RCLike 𝕜] :
    Decidable (∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
      [FiniteDimensional 𝕜 V] (n : ℕ) (T : V →ₗ[𝕜] V) (e : OrthonormalBasis (Fin n) 𝕜 V),
      (∀ k, ‖T (e k)‖ = ‖T† (e k)‖) → IsStarNormal T) := by
  apply isFalse
  -- in R^n and e^n, ‖Teₖ‖ = ‖T*eₖ‖ means the sum of the squares for
  -- ith column of the matrix, should equal the sum of the squares of the entries
  -- in the ith row of the matrix (since adjoint is matrix transpose).
  -- but normal means the row i . row j equals column i . column j
  -- one can construct a matrix where condition 1) is true but 2) is not
  -- e.g. [0 1 √24; 3 0 2; 4 √12 0]
  -- or even simpler [1 -1; 1 2]
  intro h
  let M : Matrix (Fin 2) (Fin 2) 𝕜 := !![1, -1; 1, 2]
  let T := M.toEuclideanLin
  have hadj : T† = Mᴴ.toEuclideanLin :=
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint M).symm
  -- row k and column k have the same norm: 1² + 1² = 2 and 1² + 2² = 5
  have hcond : ∀ k, ‖T (EuclideanSpace.basisFun (Fin 2) 𝕜 k)‖
      = ‖T† (EuclideanSpace.basisFun (Fin 2) 𝕜 k)‖ := by
    intro k; rw [hadj]; fin_cases k <;> simp [T, M, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  -- but T is not normal: on v = (1, 1), ‖Tv‖ = ‖(0, 3)‖ = 3 while ‖T*v‖ = ‖(2, 1)‖ = √5
  have hN := (normal_iff_norm T).mp (h _ 2 T (EuclideanSpace.basisFun (Fin 2) 𝕜) hcond) !₂[1, 1]
  have h1 : T !₂[1, 1] = !₂[0, 3] := by
    ext i; fin_cases i <;> simp [T, M]; norm_num
  have h2 : T† !₂[1, 1] = !₂[2, 1] := by
    rw [hadj]; ext i
    fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, map_ofNat] <;> norm_num
  rw [h1, h2] at hN
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] at hN
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq] at hN
  · norm_num at hN
  all_goals positivity

/-- 7A.30 If {lit}`T ∈ ℒ(𝔽³)` is normal with {lit}`T(1,1,1) = (2,2,2)`, then every
{lit}`(z₁, z₂, z₃) ∈ null T` has {lit}`z₁ + z₂ + z₃ = 0`. -/
theorem exercise_7A_30 (T : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3))
    (hT : IsStarNormal T) (h1 : T !₂[1, 1, 1] = !₂[2, 2, 2])
    (z : EuclideanSpace 𝕜 (Fin 3)) (hz : T z = 0) :
    z 0 + z 1 + z 2 = 0 := by
  -- for normal null T ⊥ range T, so ⟪z, T (1, 1, 1)⟫ = 0
  -- so 2 * z 0 + 2 * z 1 + 2 * z 2 = 0, hence z 0 + z 1 + z 2 = 0
  -- null T = null T* (7.20), so ⟪z, T w⟫ = ⟪T* z, w⟫ = 0 for every w
  have hz' : T† z = 0 := by
    have : z ∈ LinearMap.ker T† := by rw [← ker_eq_ker_adjoint hT]; exact hz
    exact this
  have h := adjoint_inner T !₂[1, 1, 1] z
  rw [h1, hz', inner_zero_right] at h
  -- ⟪(2, 2, 2), z⟫ = 2 z₀ + 2 z₁ + 2 z₂
  simp [PiLp.inner_apply, Fin.sum_univ_three, map_ofNat] at h
  linear_combination h / 2

/-- The span of {lit}`1, cos x, …, cos nx, sin x, …, sin nx` inside {lit}`ℝ → ℝ`,
the space of 7A.31. -/
noncomputable def trigSpan (n : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ ({fun _ : ℝ => (1 : ℝ)} ∪
    (fun k : ℕ => fun x : ℝ => Real.cos (k * x)) '' Set.Icc 1 n ∪
    (fun k : ℕ => fun x : ℝ => Real.sin (k * x)) '' Set.Icc 1 n)

/-- Every element of {name}`trigSpan` is continuous and {lit}`2π`-periodic. -/
theorem trigSpan_cont_periodic {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ trigSpan n) :
    Continuous f ∧ Function.Periodic f (2 * Real.pi) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with (rfl | ⟨k, -, rfl⟩) | ⟨k, -, rfl⟩
    · exact ⟨continuous_const, fun _ => rfl⟩
    · exact ⟨by fun_prop, fun x => by
        simp only [mul_add]; exact Real.cos_add_nat_mul_two_pi _ k⟩
    · exact ⟨by fun_prop, fun x => by
        simp only [mul_add]; exact Real.sin_add_nat_mul_two_pi _ k⟩
  | zero => exact ⟨continuous_const, fun _ => rfl⟩
  | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  | smul c f _ hf => exact ⟨hf.1.const_smul c, hf.2.smul c⟩

/-- Restricting to {lit}`[-π, π]` embeds {name}`trigSpan` into the space
{lit}`C[-π, π]` of Chapter 6, whose inner product is {lit}`⟨f, g⟩ = ∫₋π^π fg`. -/
noncomputable def trigToL2 (n : ℕ) : trigSpan n →ₗ[ℝ] L2C (-Real.pi) Real.pi where
  toFun f := (⟨fun x : Set.Icc (-Real.pi) Real.pi => (f : ℝ → ℝ) x,
    (trigSpan_cont_periodic f.2).1.comp continuous_subtype_val⟩ :
      C(Set.Icc (-Real.pi) Real.pi, ℝ))
  map_add' _ _ := ContinuousMap.ext fun _ => rfl
  map_smul' _ _ := ContinuousMap.ext fun _ => rfl

theorem trigToL2_injective (n : ℕ) : Function.Injective (trigToL2 n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  -- f vanishes on [-π, π] and is 2π-periodic, so it vanishes everywhere
  have hzero : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, (f : ℝ → ℝ) y = 0 := fun y hy =>
    congrArg (fun g : C(Set.Icc (-Real.pi) Real.pi, ℝ) => g ⟨y, hy⟩) hf
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨y, hy, hxy⟩ := (trigSpan_cont_periodic f.2).2.exists_mem_Ico
    Real.two_pi_pos x (-Real.pi)
  rw [hxy, hzero y ⟨hy.1, by linarith [hy.2]⟩]
  rfl

noncomputable instance (n : ℕ) : NormedAddCommGroup (trigSpan n) :=
  NormedAddCommGroup.induced _ _ (trigToL2 n) (trigToL2_injective n)

noncomputable instance (n : ℕ) : InnerProductSpace ℝ (trigSpan n) :=
  InnerProductSpace.induced (trigToL2 n)

open MeasureTheory in
/-- The induced inner product is {lit}`⟨f, g⟩ = ∫₋π^π fg`. -/
theorem inner_trig {n : ℕ} (f g : trigSpan n) :
    ⟪f, g⟫_ℝ = ∫ x in (-Real.pi)..Real.pi, (f : ℝ → ℝ) x * (g : ℝ → ℝ) x := by
  calc _ = ∫ x : ↥(Set.Icc (-Real.pi) Real.pi),
          (fun y => (f : ℝ → ℝ) y * (g : ℝ → ℝ) y) (x : ℝ) := rfl
    _ = ∫ x in Set.Icc (-Real.pi) Real.pi, (f : ℝ → ℝ) x * (g : ℝ → ℝ) x :=
        integral_subtype_comap measurableSet_Icc (fun y => (f : ℝ → ℝ) y * (g : ℝ → ℝ) y)
    _ = _ := by
        rw [integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le)]

instance (n : ℕ) : FiniteDimensional ℝ (trigSpan n) := by
  rw [trigSpan]
  exact FiniteDimensional.span_of_finite ℝ
    (((Set.finite_singleton _).union ((Set.finite_Icc 1 n).image _)).union
      ((Set.finite_Icc 1 n).image _))

/-! ## The orthonormal basis of {name}`trigSpan` (setup for 7A.31) -/

/-- {lit}`∫₋π^π cos(mx) dx` is {lit}`2π` for {lit}`m = 0` and {lit}`0` otherwise. -/
theorem integral_cos_int_mul (m : ℤ) :
    ∫ x in (-Real.pi)..Real.pi, Real.cos (m * x) = if m = 0 then 2 * Real.pi else 0 := by
  split_ifs with hm
  · subst hm; simp; ring
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hm', integral_cos,
      mul_neg, Real.sin_neg, Real.sin_int_mul_pi]
    simp

/-- {lit}`∫₋π^π sin(mx) dx = 0`. -/
theorem integral_sin_int_mul (m : ℤ) :
    ∫ x in (-Real.pi)..Real.pi, Real.sin (m * x) = 0 := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hm', integral_sin,
      mul_neg, Real.cos_neg]
    simp

theorem integral_cos_succ (k : ℕ) :
    ∫ x in (-Real.pi)..Real.pi, Real.cos ((k + 1 : ℕ) * x) = 0 := by
  have := integral_cos_int_mul ((k + 1 : ℕ) : ℤ)
  rw [Int.cast_natCast] at this
  rw [this]; simp; omega

theorem integral_sin_succ (k : ℕ) :
    ∫ x in (-Real.pi)..Real.pi, Real.sin ((k + 1 : ℕ) * x) = 0 := by
  have := integral_sin_int_mul ((k + 1 : ℕ) : ℤ)
  rwa [Int.cast_natCast] at this

/-- {lit}`cos a cos b = (cos(a − b) + cos(a + b))/2`, integrated. -/
theorem integral_cos_mul_cos (k l : ℕ) :
    ∫ x in (-Real.pi)..Real.pi, Real.cos ((k + 1 : ℕ) * x) * Real.cos ((l + 1 : ℕ) * x)
      = if k = l then Real.pi else 0 := by
  have h : ∀ x : ℝ, Real.cos ((k + 1 : ℕ) * x) * Real.cos ((l + 1 : ℕ) * x)
      = (Real.cos (((k : ℤ) - l : ℤ) * x) + Real.cos (((k : ℤ) + l + 2 : ℤ) * x)) / 2 := by
    intro x
    have e1 : (((k : ℤ) - l : ℤ) : ℝ) * x = (k + 1 : ℕ) * x - (l + 1 : ℕ) * x := by
      push_cast; ring
    have e2 : (((k : ℤ) + l + 2 : ℤ) : ℝ) * x = (k + 1 : ℕ) * x + (l + 1 : ℕ) * x := by
      push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul, integral_cos_int_mul]
  have h2 : ((k : ℤ) + l + 2) ≠ 0 := by omega
  simp only [h2, ↓reduceIte]
  by_cases hkl : k = l
  · subst hkl; simp
  · have : (k : ℤ) - l ≠ 0 := by omega
    simp [this, hkl]

/-- {lit}`sin a sin b = (cos(a − b) − cos(a + b))/2`, integrated. -/
theorem integral_sin_mul_sin (k l : ℕ) :
    ∫ x in (-Real.pi)..Real.pi, Real.sin ((k + 1 : ℕ) * x) * Real.sin ((l + 1 : ℕ) * x)
      = if k = l then Real.pi else 0 := by
  have h : ∀ x : ℝ, Real.sin ((k + 1 : ℕ) * x) * Real.sin ((l + 1 : ℕ) * x)
      = (Real.cos (((k : ℤ) - l : ℤ) * x) - Real.cos (((k : ℤ) + l + 2 : ℤ) * x)) / 2 := by
    intro x
    have e1 : (((k : ℤ) - l : ℤ) : ℝ) * x = (k + 1 : ℕ) * x - (l + 1 : ℕ) * x := by
      push_cast; ring
    have e2 : (((k : ℤ) + l + 2 : ℤ) : ℝ) * x = (k + 1 : ℕ) * x + (l + 1 : ℕ) * x := by
      push_cast; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_int_mul, integral_cos_int_mul]
  have h2 : ((k : ℤ) + l + 2) ≠ 0 := by omega
  simp only [h2, ↓reduceIte]
  by_cases hkl : k = l
  · subst hkl; simp
  · have : (k : ℤ) - l ≠ 0 := by omega
    simp [this, hkl]

/-- {lit}`sin a cos b = (sin(a + b) + sin(a − b))/2`, integrated. -/
theorem integral_sin_mul_cos (k l : ℕ) :
    ∫ x in (-Real.pi)..Real.pi, Real.sin ((k + 1 : ℕ) * x) * Real.cos ((l + 1 : ℕ) * x) = 0 := by
  have h : ∀ x : ℝ, Real.sin ((k + 1 : ℕ) * x) * Real.cos ((l + 1 : ℕ) * x)
      = (Real.sin (((k : ℤ) + l + 2 : ℤ) * x) + Real.sin (((k : ℤ) - l : ℤ) * x)) / 2 := by
    intro x
    have e1 : (((k : ℤ) - l : ℤ) : ℝ) * x = (k + 1 : ℕ) * x - (l + 1 : ℕ) * x := by
      push_cast; ring
    have e2 : (((k : ℤ) + l + 2 : ℤ) : ℝ) * x = (k + 1 : ℕ) * x + (l + 1 : ℕ) * x := by
      push_cast; ring
    rw [e1, e2, Real.sin_sub, Real.sin_add]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_sin_int_mul, integral_sin_int_mul]
  simp

theorem integral_mul_const_mul {a b : ℝ} (c d : ℝ) (f g : ℝ → ℝ) :
    ∫ x in a..b, (c * f x) * (d * g x) = c * d * ∫ x in a..b, f x * g x := by
  rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring

/-- Index set of the orthonormal basis of {name}`trigSpan`: {lit}`none` is the constant,
{lit}`inl k` is {lit}`cos (k+1)x` and {lit}`inr k` is {lit}`sin (k+1)x`. -/
abbrev TrigIdx (n : ℕ) := Option (Fin n ⊕ Fin n)

/-- The normalized functions {lit}`1/√(2π), cos (k+1)x / √π, sin (k+1)x / √π`. -/
noncomputable def trigFun {n : ℕ} : TrigIdx n → ℝ → ℝ
  | none => fun _ => (Real.sqrt (2 * Real.pi))⁻¹
  | some (.inl k) => fun x => (Real.sqrt Real.pi)⁻¹ * Real.cos (((k : ℕ) + 1 : ℕ) * x)
  | some (.inr k) => fun x => (Real.sqrt Real.pi)⁻¹ * Real.sin (((k : ℕ) + 1 : ℕ) * x)

/-- The orthonormality integrals: {lit}`∫₋π^π eᵢ eⱼ = δᵢⱼ`. -/
theorem integral_trigFun_mul {n : ℕ} (i j : TrigIdx n) :
    ∫ x in (-Real.pi)..Real.pi, trigFun i x * trigFun j x = if i = j then 1 else 0 := by
  have hpi := Real.pi_pos
  have hs : (Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹ * Real.pi = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hpi.le, inv_mul_cancel₀ hpi.ne']
  rcases i with _ | k | k <;> rcases j with _ | l | l <;> simp only [trigFun]
  · rw [intervalIntegral.integral_const, smul_eq_mul, ← mul_inv,
      Real.mul_self_sqrt (by positivity)]
    simp; field_simp; ring
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_succ]; simp
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_sin_succ]; simp
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_cos_succ]; simp
  · rw [integral_mul_const_mul, integral_cos_mul_cos]
    by_cases h : k = l
    · subst h; simp [hs]
    · simp [h, Fin.val_inj]
  · rw [integral_mul_const_mul]
    simp_rw [mul_comm (Real.cos _)]
    rw [integral_sin_mul_cos]; simp
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      integral_sin_succ]; simp
  · rw [integral_mul_const_mul, integral_sin_mul_cos]; simp
  · rw [integral_mul_const_mul, integral_sin_mul_sin]
    by_cases h : k = l
    · subst h; simp [hs]
    · simp [h, Fin.val_inj]

theorem hasDerivAt_trigFun_cos {n : ℕ} (k : Fin n) (x : ℝ) :
    HasDerivAt (trigFun (some (.inl k) : TrigIdx n))
      (-(((k : ℕ) + 1 : ℕ) : ℝ) * trigFun (some (.inr k) : TrigIdx n) x) x := by
  have := (((hasDerivAt_id x).const_mul (((k : ℕ) + 1 : ℕ) : ℝ)).cos).const_mul
    (Real.sqrt Real.pi)⁻¹
  simp only [id_eq, mul_one] at this
  convert this using 1
  · rfl
  · change _ * ((Real.sqrt Real.pi)⁻¹ * Real.sin _) = _
    ring

theorem hasDerivAt_trigFun_sin {n : ℕ} (k : Fin n) (x : ℝ) :
    HasDerivAt (trigFun (some (.inr k) : TrigIdx n))
      ((((k : ℕ) + 1 : ℕ) : ℝ) * trigFun (some (.inl k) : TrigIdx n) x) x := by
  have := (((hasDerivAt_id x).const_mul (((k : ℕ) + 1 : ℕ) : ℝ)).sin).const_mul
    (Real.sqrt Real.pi)⁻¹
  simp only [id_eq, mul_one] at this
  convert this using 1
  · rfl
  · change _ * ((Real.sqrt Real.pi)⁻¹ * Real.cos _) = _
    ring

theorem trigFun_mem {n : ℕ} (i : TrigIdx n) : trigFun i ∈ trigSpan n := by
  rcases i with _ | k | k
  · have : trigFun (none : TrigIdx n) = (Real.sqrt (2 * Real.pi))⁻¹ • fun _ : ℝ => (1 : ℝ) := by
      funext x; simp [trigFun]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl rfl)))
  · exact Submodule.smul_mem _ (Real.sqrt Real.pi)⁻¹
      (Submodule.subset_span (Or.inl (Or.inr ⟨(k : ℕ) + 1, ⟨by omega, k.isLt⟩, rfl⟩)))
  · exact Submodule.smul_mem _ (Real.sqrt Real.pi)⁻¹
      (Submodule.subset_span (Or.inr ⟨(k : ℕ) + 1, ⟨by omega, k.isLt⟩, rfl⟩))

/-- The basis vectors as elements of {name}`trigSpan`. -/
noncomputable def trigVec {n : ℕ} (i : TrigIdx n) : trigSpan n := ⟨trigFun i, trigFun_mem i⟩

theorem trigVec_orthonormal (n : ℕ) : Orthonormal ℝ (trigVec (n := n)) :=
  orthonormal_iff_ite.mpr fun i j => by rw [inner_trig]; exact integral_trigFun_mul i j

/-- Each generator of {name}`trigSpan` is a multiple of some {name}`trigVec`. -/
theorem trigVec_span (n : ℕ) : ⊤ ≤ Submodule.span ℝ (Set.range (trigVec (n := n))) := by
  rintro ⟨f, hf⟩ -
  have hpi := Real.pi_pos
  have hmem : ∀ (c : ℝ) (i : TrigIdx n),
      c • trigVec i ∈ Submodule.span ℝ (Set.range (trigVec (n := n))) := fun c i =>
    Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self i))
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with (rfl | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
    · -- 1 = √(2π) • e_none
      convert hmem (Real.sqrt (2 * Real.pi)) none using 1
      refine Subtype.ext (funext fun x => ?_)
      change (1 : ℝ) = Real.sqrt (2 * Real.pi) * (Real.sqrt (2 * Real.pi))⁻¹
      rw [mul_inv_cancel₀ (by positivity)]
    · -- cos kx = √π • e_{inl (k-1)}
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk.1; omega⟩
      convert hmem (Real.sqrt Real.pi) (some (.inl ⟨j, hk.2⟩)) using 1
      refine Subtype.ext (funext fun x => ?_)
      change _ = Real.sqrt Real.pi * ((Real.sqrt Real.pi)⁻¹ * _)
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    · -- sin kx = √π • e_{inr (k-1)}
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := hk.1; omega⟩
      convert hmem (Real.sqrt Real.pi) (some (.inr ⟨j, hk.2⟩)) using 1
      refine Subtype.ext (funext fun x => ?_)
      change _ = Real.sqrt Real.pi * ((Real.sqrt Real.pi)⁻¹ * _)
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  | zero => exact zero_mem _
  | add f g _ _ hf hg => exact add_mem hf hg
  | smul c f _ hf => exact Submodule.smul_mem _ c hf

/-- The orthonormal basis {lit}`1/√(2π), cos x/√π, …, cos nx/√π, sin x/√π, …, sin nx/√π`. -/
noncomputable def trigBasis (n : ℕ) : OrthonormalBasis (TrigIdx n) ℝ (trigSpan n) :=
  OrthonormalBasis.mk (trigVec_orthonormal n) (trigVec_span n)

/-- Differentiation on {name}`trigSpan`: if {lit}`D f = f′`, then {lit}`D* = −D`.
The matrix of {lit}`D` in {name}`trigBasis` is antisymmetric: {lit}`D` kills the constant,
sends {lit}`cos (k+1)x ↦ −(k+1) sin (k+1)x` and {lit}`sin (k+1)x ↦ (k+1) cos (k+1)x`,
so each {lit}`2×2` block is {lit}`[[0, k+1], [−(k+1), 0]]`. By 7.9 the matrix of
{lit}`D*` is the transpose, i.e. the matrix of {lit}`−D`. -/
theorem adjoint_deriv_eq_neg {n : ℕ} (D : trigSpan n →ₗ[ℝ] trigSpan n)
    (hD : ∀ f : trigSpan n, (D f : ℝ → ℝ) = deriv (f : ℝ → ℝ)) : D† = -D := by
  -- D on the basis vectors
  have hD0 : D (trigVec none) = 0 :=
    Subtype.ext (by rw [hD]; exact deriv_const' _)
  have hDc : ∀ k, D (trigVec (some (.inl k))) = (-(((k : ℕ) + 1 : ℕ) : ℝ)) • trigVec (some (.inr k)) :=
    fun k => Subtype.ext (by rw [hD]; exact funext fun x => (hasDerivAt_trigFun_cos k x).deriv)
  have hDs : ∀ k, D (trigVec (some (.inr k))) = (((k : ℕ) + 1 : ℕ) : ℝ) • trigVec (some (.inl k)) :=
    fun k => Subtype.ext (by rw [hD]; exact funext fun x => (hasDerivAt_trigFun_sin k x).deriv)
  have hon := orthonormal_iff_ite.mp (trigVec_orthonormal n)
  -- M(D*) = M(D)ᵀ (7.9), and M(D)ᵀ = −M(D) entry by entry
  set b := trigBasis n
  apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
  rw [toMatrix_adjoint_eq_conjTranspose, map_neg]
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.neg_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, b, trigBasis, OrthonormalBasis.coe_mk]
  rcases i with _ | k | k <;> rcases j with _ | l | l <;>
    simp only [hD0, hDc, hDs, inner_zero_right, inner_smul_right, hon]
  all_goals first
    | simp; done
    | (obtain rfl | h := eq_or_ne k l
       · simp
       · simp [h, h.symm])

/-- 7A.31 (a) On {lit}`span(1, cos x, …, cos nx, sin x, …, sin nx)` with
{lit}`⟨f, g⟩ = ∫₋π^π fg`, the operator {lit}`D f = f′` satisfies {lit}`D* = −D`,
so {lit}`D` is normal but not self-adjoint. -/
theorem exercise_7A_31a (n : ℕ) (hn : 0 < n) (D : trigSpan n →ₗ[ℝ] trigSpan n)
    (hD : ∀ f : trigSpan n, (D f : ℝ → ℝ) = deriv (f : ℝ → ℝ)) :
    D† = -D ∧ IsStarNormal D ∧ ¬ LinearMap.IsSymmetric D := by
  -- notice the trigspan set is orthogonal in the inner product
  -- so once normalized 1/√2π, and 1/√π for the rest, it is an orthonormal basis.
  -- then list them 1,cos x, sin x, …, cos nx, sin nx and write up D as a matrix in this basis.
  -- it is 0 on the diagonal, and each 2x2 block looks like [[0, k], [-k, 0]] for some k
  -- hence D† = -D, clearnly not self-adjoint
  -- but D†D = DD† = -D^2 so normal
  have hadj := adjoint_deriv_eq_neg D hD
  refine ⟨hadj, ?_, ?_⟩
  · rw [normal_iff_comp, hadj, LinearMap.neg_comp, LinearMap.comp_neg]
  · -- if D* = D too, then D = -D, so D = 0; but D (sin x) = cos x ≠ 0
    rw [isSelfAdjoint_iff, hadj]
    intro h
    let k : Fin n := ⟨0, hn⟩
    have hDs : D (trigVec (some (.inr k))) = (((k : ℕ) + 1 : ℕ) : ℝ) • trigVec (some (.inl k)) :=
      Subtype.ext (by rw [hD]; exact funext fun x => (hasDerivAt_trigFun_sin k x).deriv)
    have h0 : D (trigVec (some (.inr k))) = 0 := by
      have := LinearMap.congr_fun h (trigVec (some (.inr k)))
      rw [LinearMap.neg_apply, neg_eq_iff_add_eq_zero, ← two_smul ℝ] at this
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    rw [hDs, smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · norm_num [k] at h0
    · exact (trigVec_orthonormal n).ne_zero _ h0

/-- {name}`trigSpan` is closed under differentiation (and its elements are differentiable),
so {lit}`D f = f′` is an operator on it. -/
theorem trigSpan_deriv {n : ℕ} {f : ℝ → ℝ} (hf : f ∈ trigSpan n) :
    Differentiable ℝ f ∧ deriv f ∈ trigSpan n := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with (rfl | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩
    · exact ⟨differentiable_const _, by rw [deriv_const']; exact zero_mem _⟩
    · -- (cos kx)′ = -k sin kx
      refine ⟨by fun_prop, ?_⟩
      have : deriv (fun x : ℝ => Real.cos (k * x)) = (-(k : ℝ)) • fun x => Real.sin (k * x) := by
        funext x
        have := ((hasDerivAt_id x).const_mul (k : ℝ)).cos
        simp only [id_eq, mul_one] at this
        rw [this.deriv]; change _ = -(k : ℝ) * _; ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨k, hk, rfl⟩))
    · -- (sin kx)′ = k cos kx
      refine ⟨by fun_prop, ?_⟩
      have : deriv (fun x : ℝ => Real.sin (k * x)) = (k : ℝ) • fun x => Real.cos (k * x) := by
        funext x
        have := ((hasDerivAt_id x).const_mul (k : ℝ)).sin
        simp only [id_eq, mul_one] at this
        rw [this.deriv]; change _ = (k : ℝ) * _; ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨k, hk, rfl⟩)))
  | zero => exact ⟨differentiable_const 0, by
      rw [show (0 : ℝ → ℝ) = fun _ => 0 from rfl, deriv_const']; exact zero_mem _⟩
  | add f g _ _ hf hg =>
    refine ⟨hf.1.add hg.1, ?_⟩
    rw [show deriv (f + g) = deriv f + deriv g from
      funext fun x => deriv_add (hf.1 x) (hg.1 x)]
    exact add_mem hf.2 hg.2
  | smul c f _ hf =>
    refine ⟨hf.1.const_smul c, ?_⟩
    rw [show deriv (c • f) = c • deriv f from funext fun x => deriv_const_smul c (hf.1 x)]
    exact Submodule.smul_mem _ c hf.2

/-- The differentiation operator {lit}`D f = f′` on {name}`trigSpan`. -/
noncomputable def trigDeriv (n : ℕ) : trigSpan n →ₗ[ℝ] trigSpan n where
  toFun f := ⟨deriv (f : ℝ → ℝ), (trigSpan_deriv f.2).2⟩
  map_add' f g := Subtype.ext (funext fun x =>
    deriv_add ((trigSpan_deriv f.2).1 x) ((trigSpan_deriv g.2).1 x))
  map_smul' c f := Subtype.ext (funext fun x => deriv_const_smul c ((trigSpan_deriv f.2).1 x))

/-- 7A.31 (b) The operator {lit}`T f = f″` on the same space is self-adjoint. -/
theorem exercise_7A_31b (n : ℕ) (T : trigSpan n →ₗ[ℝ] trigSpan n)
    (hT : ∀ f : trigSpan n, (T f : ℝ → ℝ) = deriv (deriv (f : ℝ → ℝ))) :
    LinearMap.IsSymmetric T := by
  -- This is just T = D^2 from a), so T† = (D^2)† = (D†)^2 = (-D)^2 = D^2 = T, hence self-adjoint.
  have hT' : T = trigDeriv n ∘ₗ trigDeriv n :=
    LinearMap.ext fun f => Subtype.ext (by rw [hT]; rfl)
  rw [isSelfAdjoint_iff, hT', adjoint_comp, adjoint_deriv_eq_neg _ (fun _ => rfl),
    LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]

/-- 7A.32 Under the identification of {lit}`V` with {lit}`V′` sending {lit}`w` to
the functional {lit}`φ_w = ⟨·, w⟩` (6.58), the adjoint corresponds to the dual
map: {lit}`T′(φ_w) = φ_{T*w}`. -/
theorem exercise_7A_32 (T : V →ₗ[𝕜] W) (w : W) :
    LinearMap.dualMap T (innerₛₗ 𝕜 w) = innerₛₗ 𝕜 (T† w) := by
  -- T'φ_w v = φ_w (T v) = ⟪T v, w⟫ = ⟪v, T† w⟫ = φ_{T† w} v
  -- (in mathlib's slot order φ_w v is ⟪w, v⟫, so the middle step reads ⟪w, T v⟫ = ⟪T† w, v⟫)
  ext v
  rw [LinearMap.dualMap_apply, innerₛₗ_apply_apply, innerₛₗ_apply_apply, ← inner_conj_symm,
    adjoint_inner, inner_conj_symm]

end LADR.Section_7A
