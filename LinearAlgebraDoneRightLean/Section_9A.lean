import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 9A: Bilinear Forms and Quadratic Forms
-/

namespace LADR.Section_9A

open Module (finrank Dual Basis)
open LinearMap (BilinForm BilinMap)
open scoped RealInnerProductSpace Matrix

/-! # The setting

Axler's field {lit}`𝐅` is always {lit}`ℝ` or {lit}`ℂ`; the results of this section
hold over any field in which {lit}`2 ≠ 0` (needed for the symmetric/alternating
decomposition 9.17 and everything downstream of it). We therefore fix a field
{lit}`F` with an invertible {lit}`2`, and a vector space {lit}`V` over {lit}`F`.

A *bilinear form* on {lit}`V` is captured in mathlib by {name}`LinearMap.BilinForm`,
which is definitionally {lit}`V →ₗ[F] V →ₗ[F] F`: a linear map from {lit}`V` into
the space of linear functionals on {lit}`V`. Applying such a {lit}`B` to two
vectors is written {lit}`B u v`. -/

variable {F : Type*} [Field F] [Invertible (2 : F)]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! # Bilinear Forms -/

/-! 9.1 Definition: bilinear form

A bilinear form on {lit}`V` is a function {lit}`β : V × V → F` that is linear in
each slot separately. In mathlib this bundled object is {name}`LinearMap.BilinForm`,
which unfolds to {lit}`V →ₗ[F] V →ₗ[F] F`. The two slot-linearity requirements of
Axler's definition are exactly the linearity of {lit}`B` (first slot) and of each
{lit}`B u` (second slot). -/

example : LinearMap.BilinForm F V = (V →ₗ[F] V →ₗ[F] F) := rfl

/-! Linearity in the first slot: {lit}`v ↦ β(v, u)`. -/
example (B : BilinForm F V) (u : V) (v w : V) (a : F) :
    B (v + w) u = B v u + B w u ∧ B (a • v) u = a • B v u := by
  constructor
  · rw [map_add]; rfl
  · rw [map_smul]; rfl

/-- Linearity in the second slot: {lit}`v ↦ β(u, v)`. -/
example (B : BilinForm F V) (u : V) (v w : V) (a : F) :
    B u (v + w) = B u v + B u w ∧ B u (a • v) = a • B u v := by
  constructor
  · rw [map_add]
  · rw [map_smul]

/-! 9.2 Example: bilinear forms

The central family: to each {lit}`n`-by-{lit}`n` matrix {lit}`A` corresponds the
bilinear form {lit}`β_A` on {lit}`Fⁿ` given by
{lit}`β_A(x, y) = ∑ⱼ ∑ₖ Aⱼ,ₖ xⱼ yₖ`. In mathlib this is {name}`Matrix.toBilin'`. -/

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (x y : Fin n → F) :
    Matrix.toBilin' A x y = ∑ i, ∑ j, x i * A i j * y j :=
  Matrix.toBilin'_apply A x y

/-- The third bullet: for {lit}`φ, τ ∈ V'`, the map {lit}`(u, v) ↦ φ(u)·τ(v)` is a
bilinear form. It is realized by {name}`LinearMap.compl₁₂` of multiplication. -/
def bilinOfDualPair (φ τ : Module.Dual F V) : BilinForm F V :=
  (LinearMap.mul F F).compl₁₂ φ τ

omit [Invertible (2 : F)] in
theorem bilinOfDualPair_apply (φ τ : Module.Dual F V) (u v : V) :
    bilinOfDualPair φ τ u v = φ u * τ v := by
  rw [bilinOfDualPair, LinearMap.compl₁₂_apply, LinearMap.mul_apply']

/-- The fourth (general) bullet: a finite sum {lit}`∑ᵢ φᵢ(u)·τᵢ(v)` is a bilinear
form. -/
def bilinOfDualPairs {n : ℕ} (φ τ : Fin n → Module.Dual F V) : BilinForm F V :=
  ∑ i, bilinOfDualPair (φ i) (τ i)

example {n : ℕ} (φ τ : Fin n → Module.Dual F V) (u v : V) :
    bilinOfDualPairs φ τ u v = ∑ i, φ i u * τ i v := by
  simp only [bilinOfDualPairs, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ => bilinOfDualPair_apply (φ i) (τ i) u v

/-! The first bullet of 9.2 — the concrete form
{lit}`β((x₁,x₂,x₃),(y₁,y₂,y₃)) = x₁y₂ − 5x₂y₃ + 2x₃y₁` on {lit}`F³` — is the
special case {lit}`n = 3` of {name}`Matrix.toBilin'` with the displayed matrix. The
remaining bullets of 9.2 ({lit}`(u,v) ↦ ⟨u,v⟩` on a real inner product space and
{lit}`(p,q) ↦ p(2)·q′(3)` on {lit}`𝒫ₙ(ℝ)`) are further instances; the inner-product
one reappears in 9.10 below. -/

/-! 9.3 Definition: {lit}`V⁽²⁾`

The set of bilinear forms on {lit}`V`, with pointwise addition and scalar
multiplication, is a vector space. In mathlib {name}`LinearMap.BilinForm` already
carries this {name}`Module` structure. -/

example : Module F (BilinForm F V) := inferInstance

/-! 9.4 Definition: matrix of a bilinear form, {lit}`ℳ(β)`

Given a basis {lit}`e₁, …, eₙ` of {lit}`V`, the matrix of {lit}`β` has entry
{lit}`ℳ(β)ⱼ,ₖ = β(eⱼ, eₖ)`. In mathlib this is {name}`LinearMap.BilinForm.toMatrix`. -/

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example (b : Basis ι F V) (B : BilinForm F V) (j k : ι) :
    LinearMap.BilinForm.toMatrix b B j k = B (b j) (b k) :=
  LinearMap.BilinForm.toMatrix_apply b B j k

/-! 9.5 {lit}`dim V⁽²⁾ = (dim V)²`

The map {lit}`β ↦ ℳ(β)` is the linear isomorphism {name}`LinearMap.BilinForm.toMatrix`
from {lit}`V⁽²⁾` onto {lit}`Fⁿ,ⁿ`, so the two spaces have equal dimension, namely
{lit}`(dim V)²`. -/

noncomputable example (b : Basis ι F V) : BilinForm F V ≃ₗ[F] Matrix ι ι F :=
  LinearMap.BilinForm.toMatrix b

omit [Invertible (2 : F)] in
theorem finrank_bilinForm [FiniteDimensional F V] :
    finrank F (BilinForm F V) = (finrank F V) ^ 2 := by
  classical
  set n := finrank F V with hn
  let b : Basis (Fin n) F V := Module.finBasis F V
  rw [(LinearMap.BilinForm.toMatrix b).finrank_eq, Module.finrank_matrix, Module.finrank_self,
    mul_one, Fintype.card_fin, sq]

/-! 9.6 Composition of a bilinear form and an operator

For {lit}`β` a bilinear form and {lit}`T` an operator, the forms
{lit}`α(u,v) = β(u,Tv)` and {lit}`ρ(u,v) = β(Tu,v)` satisfy
{lit}`ℳ(α) = ℳ(β)ℳ(T)` and {lit}`ℳ(ρ) = ℳ(T)ᵗℳ(β)`. In mathlib
{lit}`α = β.compRight T` and {lit}`ρ = β.compLeft T`. -/

example (B : BilinForm F V) (T : V →ₗ[F] V) (u v : V) :
    B.compRight T u v = B u (T v) := BilinForm.compRight_apply B T u v

example (B : BilinForm F V) (T : V →ₗ[F] V) (u v : V) :
    B.compLeft T u v = B (T u) v := BilinForm.compLeft_apply B T u v

omit [Invertible (2 : F)] in
theorem toMatrix_compRight (b : Basis ι F V) (B : BilinForm F V) (T : V →ₗ[F] V) :
    LinearMap.BilinForm.toMatrix b (B.compRight T) =
      LinearMap.BilinForm.toMatrix b B * LinearMap.toMatrix b b T :=
  LinearMap.BilinForm.toMatrix_compRight b B T

omit [Invertible (2 : F)] in
theorem toMatrix_compLeft (b : Basis ι F V) (B : BilinForm F V) (T : V →ₗ[F] V) :
    LinearMap.BilinForm.toMatrix b (B.compLeft T) =
      (LinearMap.toMatrix b b T)ᵀ * LinearMap.BilinForm.toMatrix b B :=
  LinearMap.BilinForm.toMatrix_compLeft b B T

/-! 9.7 Change-of-basis formula

If {lit}`A = ℳ(β, e)`, {lit}`B = ℳ(β, f)` and {lit}`C = ℳ(I, e, f)` is the
change-of-basis matrix ({lit}`f.toMatrix e`, expressing the basis {lit}`e` in the
basis {lit}`f`), then {lit}`A = CᵗBC`. -/

omit [Invertible (2 : F)] in
theorem changeOfBasis (β : BilinForm F V) (e f : Basis ι F V) :
    LinearMap.BilinForm.toMatrix e β =
      (f.toMatrix e)ᵀ * LinearMap.BilinForm.toMatrix f β * f.toMatrix e :=
  (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := f) e β).symm

end Matrix

/-! 9.8 Example: the matrix of a bilinear form on {lit}`𝒫₂(ℝ)`

For {lit}`β(p, q) = p(2)·q′(3)` on {lit}`𝒫₂(ℝ)`, Axler exhibits three explicit
matrices {lit}`A`, {lit}`B`, {lit}`C` and checks {lit}`A = CᵗBC` numerically. This
is a concrete numerical instance of the change-of-basis formula 9.7, which we have
proved in full generality above; we do not repeat the {lit}`3×3` arithmetic here. -/

/-! # Symmetric Bilinear Forms -/

/-! 9.9 Definition: symmetric bilinear form, {lit}`V⁽²⁾_sym`

{lit}`ρ` is symmetric if {lit}`ρ(u, w) = ρ(w, u)` for all {lit}`u, w`. In mathlib
this is {name}`LinearMap.BilinForm.IsSymm`. -/

example (B : BilinForm F V) : B.IsSymm ↔ ∀ u w, B u w = B w u :=
  LinearMap.BilinForm.isSymm_def

/-! 9.10 Example: symmetric bilinear forms

The map {lit}`ρ(S, T) = tr(ST)` on {lit}`ℒ(V)` is symmetric because
{lit}`tr(ST) = tr(TS)`. (The inner-product examples — {lit}`ρ(u,w) = ⟨u,w⟩` and,
more generally, {lit}`ρ(u,w) = ⟨u,Tw⟩` for {lit}`T` self-adjoint — are the content
of Exercises 4 and 5.) -/

example [FiniteDimensional F V] (S T : V →ₗ[F] V) :
    LinearMap.trace F V (S * T) = LinearMap.trace F V (T * S) := by
  rw [LinearMap.trace_mul_comm]

/-! 9.11 Definition: symmetric matrix

A square matrix is symmetric if it equals its transpose; in mathlib
{name}`Matrix.IsSymm`. -/

example {ι : Type*} (A : Matrix ι ι F) : A.IsSymm ↔ Aᵀ = A := Iff.rfl

/-! 9.12 Symmetric bilinear forms are diagonalizable

For {lit}`ρ ∈ V⁽²⁾`, the following are equivalent: (a) {lit}`ρ` is symmetric;
(b)/(c) the matrix {lit}`ℳ(ρ)` is symmetric in every/some basis; (d) {lit}`ℳ(ρ)`
is diagonal in some basis. We record (a) ⟺ (b/c) as: {lit}`ρ` is symmetric iff its
matrix in any given basis is symmetric (holding for all bases and for some basis
simultaneously); and (a) ⟺ (d) as the existence of a diagonalizing basis. -/

section Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! (a) ⟺ (b) ⟺ (c): {lit}`ρ` is a symmetric bilinear form iff its matrix with
respect to a basis {lit}`b` is a symmetric matrix. Since {lit}`b` is arbitrary,
this gives the equivalence of "symmetric with respect to every basis" and
"symmetric with respect to some basis". -/

omit [Invertible (2 : F)] in
theorem isSymm_iff_toMatrix_isSymm (b : Basis ι F V) (B : BilinForm F V) :
    B.IsSymm ↔ (LinearMap.BilinForm.toMatrix b B).IsSymm := by
  constructor
  · intro h
    ext i j
    rw [Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply]
    exact (LinearMap.BilinForm.isSymm_iff_basis b).1 h j i
  · intro h
    rw [LinearMap.BilinForm.isSymm_iff_basis b]
    intro i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.transpose_apply] at hij
    rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.toMatrix_apply] at hij
    exact hij.symm

end Matrix

/-- (a) ⟺ (d): a bilinear form is symmetric iff there is a basis with respect to
which its matrix is diagonal. The forward direction is mathlib's
{name}`LinearMap.BilinForm.exists_orthogonal_basis` (valid because {lit}`2` is
invertible); the reverse direction holds because a diagonal matrix is symmetric. -/
theorem isSymm_iff_exists_diag [FiniteDimensional F V] (B : BilinForm F V) :
    B.IsSymm ↔
      ∃ v : Basis (Fin (finrank F V)) F V,
        Matrix.IsDiag (LinearMap.BilinForm.toMatrix v B) := by
  classical
  constructor
  · intro h
    obtain ⟨v, hv⟩ :=
      LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.1 h)
    refine ⟨v, ?_⟩
    intro i j hij
    rw [LinearMap.BilinForm.toMatrix_apply]
    exact hv hij
  · rintro ⟨v, hv⟩
    rw [isSymm_iff_toMatrix_isSymm v]
    ext i j
    rw [Matrix.transpose_apply]
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · rw [hv hij, hv (Ne.symm hij)]

/-! 9.13 Diagonalization of a symmetric bilinear form by an orthonormal basis

Axler's proof: on a real inner product space, represent the symmetric bilinear
form {lit}`ρ` by the self-adjoint operator {lit}`T` with {lit}`⟨T u, w⟩ = ρ(u, w)`
(Riesz representation, {name}`InnerProductSpace.toDual`), diagonalize {lit}`T` by an
orthonormal eigenbasis via the real spectral theorem (7.29,
{name}`LinearMap.IsSymmetric.eigenvectorBasis`), and read off
{lit}`ρ(eᵢ, eⱼ) = ⟨T eᵢ, eⱼ⟩ = λᵢ⟨eᵢ, eⱼ⟩ = λᵢ δᵢⱼ`, a diagonal matrix. -/

section SpectralBilinear

open Module (finrank)
open scoped RealInnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The self-adjoint operator representing a bilinear form via the inner product:
{lit}`⟨bilinOp B u, w⟩ = B u w` (Riesz representation). -/
noncomputable def bilinOp (B : LinearMap.BilinForm ℝ W) : W →ₗ[ℝ] W :=
  (InnerProductSpace.toDual ℝ W).symm.toLinearMap ∘ₗ
    (LinearMap.toContinuousLinearMap : (W →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (W →L[ℝ] ℝ)).toLinearMap ∘ₗ B

theorem bilinOp_inner (B : LinearMap.BilinForm ℝ W) (u w : W) :
    ⟪bilinOp B u, w⟫ = B u w := by
  show ⟪(InnerProductSpace.toDual ℝ W).symm ((B u).toContinuousLinearMap), w⟫ = B u w
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem bilinOp_isSymmetric {B : LinearMap.BilinForm ℝ W} (hB : B.IsSymm) :
    LinearMap.IsSymmetric (bilinOp B) := by
  intro u w
  rw [bilinOp_inner, real_inner_comm, bilinOp_inner, hB.eq u w]

/-- 9.13 On a real inner product space, every symmetric bilinear form has a
diagonal matrix with respect to some orthonormal basis. -/
theorem exists_orthonormal_diag (B : LinearMap.BilinForm ℝ W) (hB : B.IsSymm) :
    ∃ e : OrthonormalBasis (Fin (finrank ℝ W)) ℝ W,
      Matrix.IsDiag (LinearMap.BilinForm.toMatrix e.toBasis B) := by
  have hT : LinearMap.IsSymmetric (bilinOp B) := bilinOp_isSymmetric hB
  refine ⟨hT.eigenvectorBasis rfl, ?_⟩
  intro i j hij
  rw [LinearMap.BilinForm.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    ← bilinOp_inner, hT.apply_eigenvectorBasis rfl i, inner_smul_left,
    (hT.eigenvectorBasis rfl).orthonormal.2 hij]
  simp

end SpectralBilinear

/-! Now we turn to alternating bilinear forms. -/

/-! 9.14 Definition: alternating bilinear form, {lit}`V⁽²⁾_alt`

{lit}`α` is alternating if {lit}`α(v, v) = 0` for all {lit}`v`; in mathlib
{name}`LinearMap.BilinForm.IsAlt`. -/

example (B : BilinForm F V) : B.IsAlt ↔ ∀ v, B v v = 0 := Iff.rfl

/-! 9.15 Example: alternating bilinear forms

For {lit}`φ, τ ∈ V'`, the form {lit}`α(u, w) = φ(u)τ(w) − φ(w)τ(u)` is alternating.
(The concrete example on {lit}`Fⁿ` with {lit}`n ≥ 3` is another instance.) -/

def altOfDualPair (φ τ : Module.Dual F V) : BilinForm F V :=
  bilinOfDualPair φ τ - bilinOfDualPair τ φ

omit [Invertible (2 : F)] in
theorem altOfDualPair_apply (φ τ : Module.Dual F V) (u w : V) :
    altOfDualPair φ τ u w = φ u * τ w - φ w * τ u := by
  rw [altOfDualPair, LinearMap.sub_apply, LinearMap.sub_apply, bilinOfDualPair_apply,
    bilinOfDualPair_apply]
  ring

omit [Invertible (2 : F)] in
theorem altOfDualPair_isAlt (φ τ : Module.Dual F V) : (altOfDualPair φ τ).IsAlt := by
  intro v
  rw [altOfDualPair_apply, sub_self]

/-! 9.16 Characterization of alternating bilinear forms

{lit}`α` is alternating if and only if {lit}`α(u, w) = −α(w, u)` for all
{lit}`u, w`. -/

theorem isAlt_iff_neg_swap (B : BilinForm F V) :
    B.IsAlt ↔ ∀ u w, B u w = - B w u := by
  constructor
  · intro h u w
    exact (LinearMap.BilinForm.IsAlt.neg_eq h w u).symm
  · intro h v
    have hv := h v v
    have h2 : (2 : F) * B v v = 0 := by linear_combination hv
    have hne : (2 : F) ≠ 0 := Invertible.ne_zero (2 : F)
    exact (mul_eq_zero.mp h2).resolve_left hne

/-! 9.17 {lit}`V⁽²⁾ = V⁽²⁾_sym ⊕ V⁽²⁾_alt`

The symmetric and alternating bilinear forms are subspaces of {lit}`V⁽²⁾`, and
{lit}`V⁽²⁾` is their direct sum. The decomposition of {lit}`β` is
{lit}`ρ = ½(β + βᵗ)` (symmetric) and {lit}`α = ½(β − βᵗ)` (alternating), where
{lit}`βᵗ` is the flip {name}`LinearMap.BilinForm.flipHom`. -/

/-- The subspace of symmetric bilinear forms. -/
def symmSubmodule : Submodule F (BilinForm F V) where
  carrier := {B | B.IsSymm}
  add_mem' ha hb := ha.add hb
  zero_mem' := LinearMap.BilinForm.isSymm_zero
  smul_mem' c _ hB := LinearMap.BilinForm.IsSymm.smul c hB

/-- The subspace of alternating bilinear forms. -/
def altSubmodule : Submodule F (BilinForm F V) where
  carrier := {B | B.IsAlt}
  add_mem' ha hb := ha.add hb
  zero_mem' := LinearMap.BilinForm.isAlt_zero
  smul_mem' c _ hB := LinearMap.BilinForm.IsAlt.smul c hB

omit [Invertible (2 : F)] in
theorem mem_symmSubmodule {B : BilinForm F V} : B ∈ symmSubmodule (F := F) (V := V) ↔ B.IsSymm :=
  Iff.rfl

omit [Invertible (2 : F)] in
theorem mem_altSubmodule {B : BilinForm F V} : B ∈ altSubmodule (F := F) (V := V) ↔ B.IsAlt :=
  Iff.rfl

theorem isCompl_symm_alt : IsCompl (symmSubmodule (F := F) (V := V)) altSubmodule := by
  have hne : (2 : F) ≠ 0 := Invertible.ne_zero (2 : F)
  constructor
  · -- Disjoint: a form that is both symmetric and alternating is 0.
    rw [disjoint_iff_inf_le]
    intro B hB
    obtain ⟨hBs, hBa⟩ := hB
    rw [Submodule.mem_bot]
    ext u w
    have hsymm : B u w = B w u := (LinearMap.BilinForm.isSymm_def.1 hBs) u w
    have halt : B u w = - B w u := (isAlt_iff_neg_swap B).1 hBa u w
    have h2 : (2 : F) * B u w = 0 := by linear_combination halt + hsymm
    rw [LinearMap.zero_apply, LinearMap.zero_apply]
    exact (mul_eq_zero.mp h2).resolve_left hne
  · -- Codisjoint: β = ρ + α with ρ symmetric, α alternating.
    rw [codisjoint_iff_le_sup]
    intro B _
    rw [Submodule.mem_sup]
    refine ⟨(2⁻¹ : F) • (B + LinearMap.BilinForm.flipHom B), ?_,
      (2⁻¹ : F) • (B - LinearMap.BilinForm.flipHom B), ?_, ?_⟩
    · -- ρ is symmetric
      rw [mem_symmSubmodule]
      have hs : (B + LinearMap.BilinForm.flipHom B).IsSymm := by
        rw [LinearMap.BilinForm.isSymm_def]
        intro u w
        simp only [LinearMap.add_apply, LinearMap.BilinForm.flip_apply]
        ring
      exact LinearMap.BilinForm.IsSymm.smul _ hs
    · -- α is alternating
      rw [mem_altSubmodule]
      have ha : (B - LinearMap.BilinForm.flipHom B).IsAlt := by
        intro v
        simp only [LinearMap.sub_apply, LinearMap.BilinForm.flip_apply, sub_self]
      exact LinearMap.BilinForm.IsAlt.smul _ ha
    · -- their sum is β
      ext u w
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
        LinearMap.BilinForm.flip_apply, smul_eq_mul]
      field_simp
      ring

/-! # Quadratic Forms -/

/-! 9.18 Definition: quadratic form associated with a bilinear form, {lit}`q_β`

For a bilinear form {lit}`β`, define {lit}`q_β(v) = β(v, v)`. A function
{lit}`q : V → F` is a quadratic form if {lit}`q = q_β` for some {lit}`β`. In mathlib
{lit}`q_β` is {name}`LinearMap.BilinMap.toQuadraticMap`, and a quadratic form is a
{name}`QuadraticForm`. -/

example (B : BilinForm F V) (v : V) : B.toQuadraticMap v = B v v :=
  LinearMap.BilinMap.toQuadraticMap_apply B v

/-- {lit}`q_β = 0` if and only if {lit}`β` is alternating. -/
example (B : BilinForm F V) : B.toQuadraticMap = 0 ↔ B.IsAlt :=
  LinearMap.BilinMap.toQuadraticMap_eq_zero

/-! 9.19 Example: quadratic form

For {lit}`β((x₁,x₂,x₃),(y₁,y₂,y₃)) = x₁y₁ − 4x₁y₂ + 8x₁y₃ − 3x₃y₃` on {lit}`ℝ³`,
the associated quadratic form is
{lit}`q_β(x₁,x₂,x₃) = x₁² − 4x₁x₂ + 8x₁x₃ − 3x₃²`. This is the special case
{lit}`v = w` of the formula for a bilinear form on {lit}`Fⁿ`; the general statement
that every quadratic form on {lit}`Fⁿ` has this shape is 9.20. -/

/-! 9.20 Quadratic forms on {lit}`Fⁿ`

A function {lit}`q : Fⁿ → F` is a quadratic form if and only if there is a matrix
{lit}`A` with {lit}`q(x) = ∑ᵢ ∑ⱼ Aᵢ,ⱼ xᵢ xⱼ`. -/

omit [Invertible (2 : F)] in
theorem quadraticForm_on_pi {n : ℕ} (q : (Fin n → F) → F) :
    (∃ B : BilinForm F (Fin n → F), ∀ x, q x = B x x) ↔
      (∃ A : Matrix (Fin n) (Fin n) F, ∀ x, q x = ∑ i, ∑ j, A i j * x i * x j) := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨LinearMap.BilinForm.toMatrix' B, fun x => ?_⟩
    rw [hB]
    conv_lhs => rw [← Matrix.toBilin'_toMatrix' B]
    rw [Matrix.toBilin'_apply]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  · rintro ⟨A, hA⟩
    refine ⟨Matrix.toBilin' A, fun x => ?_⟩
    rw [hA, Matrix.toBilin'_apply]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring

/-! 9.21 Characterizations of quadratic forms

The key content (equivalence of Axler's (a) and (b)) is that every quadratic form
{lit}`q` arises from a *unique symmetric* bilinear form {lit}`ρ`. In mathlib the
witness is {name}`QuadraticMap.associated`, the symmetric bilinear form
{lit}`ρ(u,w) = ½(q(u+w) − q(u) − q(w))`. Parts (c)/(d) record the scaling law
{lit}`q(λv) = λ²q(v)` and the bilinearity of the polar map, both packaged into the
{name}`QuadraticForm` structure. -/

/-- (a) ⟺ (b): a quadratic form has a unique symmetric associated bilinear form. -/
theorem exists_unique_symm_of_quadratic (q : QuadraticForm F V) :
    ∃! ρ : BilinForm F V, ρ.IsSymm ∧ ρ.toQuadraticMap = q := by
  refine ⟨QuadraticMap.associated q,
    ⟨LinearMap.BilinForm.isSymm_iff.2 (QuadraticForm.associated_isSymm F q), ?_⟩, ?_⟩
  · exact QuadraticMap.toQuadraticMap_associated F q
  · rintro ρ' ⟨hsymm, hq⟩
    have := QuadraticMap.associated_left_inverse F (B₁ := ρ')
      (LinearMap.BilinForm.isSymm_def.1 hsymm)
    rw [hq] at this
    exact this.symm

/-- (c), first part: the scaling law {lit}`q(λv) = λ²q(v)`. -/
example (q : QuadraticForm F V) (a : F) (v : V) : q (a • v) = a ^ 2 * q v := by
  rw [q.map_smul, smul_eq_mul, pow_two]

/-- (c), second part: the polar map {lit}`(u,w) ↦ q(u+w) − q(u) − q(w)` is a
symmetric bilinear form; here it is {name}`QuadraticMap.polarBilin`, whose
symmetry is {name}`QuadraticMap.polar_comm`. -/
example (q : QuadraticForm F V) (u w : V) :
    QuadraticMap.polar q u w = QuadraticMap.polar q w u :=
  QuadraticMap.polar_comm q u w

/-! 9.22 Example: symmetric bilinear form associated with a quadratic form

For {lit}`q(x₁,x₂,x₃) = x₁² − 4x₁x₂ + 8x₁x₃ − 3x₃²` on {lit}`ℝ³`, the unique
symmetric bilinear form with {lit}`q = q_ρ` (guaranteed by 9.21(b)) is
{lit}`ρ((x),(y)) = x₁y₁ − 2x₁y₂ − 2x₂y₁ + 4x₁y₃ + 4x₃y₁ − 3x₃y₃`, obtained by
symmetrizing the off-diagonal coefficients — exactly {name}`QuadraticMap.associated`
applied to this {lit}`q`. -/

/-! 9.23 Diagonalization of a quadratic form

(a) There is a basis {lit}`e₁, …, eₙ` and scalars {lit}`λ₁, …, λₙ` with
{lit}`q(x₁e₁ + ⋯ + xₙeₙ) = λ₁x₁² + ⋯ + λₙxₙ²`. -/

theorem diagonalize_quadratic [FiniteDimensional F V] (q : QuadraticForm F V) :
    ∃ (v : Basis (Fin (finrank F V)) F V) (l : Fin (finrank F V) → F),
      ∀ x : Fin (finrank F V) → F,
        q (∑ i, x i • v i) = ∑ i, l i * (x i) ^ 2 := by
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm F q)
  refine ⟨v, fun i => q (v i), fun x => ?_⟩
  have hrepr := QuadraticMap.basisRepr_eq_of_iIsOrtho q v hv
  rw [show q (∑ i, x i • v i) = q.basisRepr v x from (QuadraticMap.basisRepr_apply q x).symm,
    hrepr, QuadraticMap.weightedSumSquares_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_eq_mul, pow_two]

/-! (b) When {lit}`F = ℝ` and {lit}`V` is an inner product space, the diagonalizing
basis in (a) can be taken orthonormal — the quadratic-form restatement of 9.13. -/

theorem diagonalize_quadratic_orthonormal {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] (q : QuadraticForm ℝ W) :
    ∃ (e : OrthonormalBasis (Fin (finrank ℝ W)) ℝ W) (l : Fin (finrank ℝ W) → ℝ),
      ∀ x : Fin (finrank ℝ W) → ℝ,
        q (∑ i, x i • e i) = ∑ i, l i * (x i) ^ 2 := by
  obtain ⟨e, hdiag⟩ :=
    exists_orthonormal_diag _
      (LinearMap.BilinForm.isSymm_iff.mpr (QuadraticForm.associated_isSymm ℝ q))
  have hv : LinearMap.IsOrthoᵢ (QuadraticMap.associated q) ⇑e.toBasis := by
    intro i j hij
    have h0 := hdiag hij
    simp only [LinearMap.BilinForm.toMatrix_apply] at h0
    exact h0
  refine ⟨e, fun i => q (e i), fun x => ?_⟩
  have hrepr := QuadraticMap.basisRepr_eq_of_iIsOrtho q e.toBasis hv
  rw [show q (∑ i, x i • e i) = q.basisRepr e.toBasis x from ?_, hrepr,
    QuadraticMap.weightedSumSquares_apply]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [OrthonormalBasis.coe_toBasis, smul_eq_mul, pow_two]
  · rw [QuadraticMap.basisRepr_apply]
    simp only [OrthonormalBasis.coe_toBasis]

/-! # Exercises 9A -/

/-- 9A.1 If {lit}`β` is a bilinear form on {lit}`F`, then {lit}`β(x, y) = cxy` for
some {lit}`c ∈ F`. -/
theorem exercise_9A_1 (B : BilinForm F F) : ∃ c : F, ∀ x y : F, B x y = c * x * y := by
  sorry

/-- 9A.2 If {lit}`n = dim V`, every bilinear form on {lit}`V` has the shape of the
last bullet of Example 9.2: {lit}`β(u,v) = ∑ᵢ φᵢ(u)·τᵢ(v)` for some
{lit}`φ₁,…,φₙ, τ₁,…,τₙ ∈ V'`. -/
theorem exercise_9A_2 [FiniteDimensional F V] (B : BilinForm F V) :
    ∃ (φ τ : Fin (finrank F V) → Module.Dual F V),
      ∀ u v, B u v = ∑ i, φ i u * τ i v := by
  sorry

/-- 9A.3 If a bilinear form {lit}`β` on {lit}`V` is also a linear functional on
{lit}`V × V` (i.e. the uncurried map is linear), then {lit}`β = 0`. -/
theorem exercise_9A_3 (B : BilinForm F V)
    (h : IsLinearMap F (fun p : V × V => B p.1 p.2)) : B = 0 := by
  sorry

/-- 9A.4 If {lit}`V` is a real inner product space, every bilinear form on
{lit}`V` is {lit}`β(u,v) = ⟨u, Tv⟩` for a unique operator {lit}`T ∈ ℒ(V)`. -/
theorem exercise_9A_4 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (B : BilinForm ℝ V) :
    ∃! T : V →ₗ[ℝ] V, ∀ u v, B u v = ⟪u, T v⟫ := by
  sorry

/-- 9A.6 Prove or give a counterexample: if {lit}`ρ` is symmetric, then
{lit}`{v : ρ(v,v) = 0}` is a subspace of {lit}`V`. (It need not be: the hyperbolic
form {lit}`ρ((x₁,x₂),(y₁,y₂)) = x₁y₁ − x₂y₂` on {lit}`ℝ²` has zero-set
{lit}`{v : v₁² = v₂²}`, which is not closed under addition.) -/
theorem exercise_9A_6 :
    ∃ ρ : BilinForm ℝ (Fin 2 → ℝ), ρ.IsSymm ∧
      ¬ ∃ U : Submodule ℝ (Fin 2 → ℝ), (U : Set (Fin 2 → ℝ)) = {v | ρ v v = 0} := by
  sorry

/-- 9A.8 Formulas for the dimensions of the symmetric and alternating subspaces:
{lit}`dim V⁽²⁾_sym = n(n+1)/2` and {lit}`dim V⁽²⁾_alt = n(n−1)/2`, where
{lit}`n = dim V`. -/
theorem exercise_9A_8 [FiniteDimensional F V] :
    finrank F (symmSubmodule (F := F) (V := V)) * 2 = finrank F V * (finrank F V + 1) ∧
      finrank F (altSubmodule (F := F) (V := V)) * 2 = finrank F V * (finrank F V - 1) := by
  sorry

/-- 9A.5 With {lit}`T` the operator of Exercise 4 ({lit}`β(u,v) = ⟨u, Tv⟩`),
{lit}`β` is an inner product iff {lit}`T` is an invertible positive operator. -/
theorem exercise_9A_5 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (B : BilinForm ℝ V) (T : V →ₗ[ℝ] V)
    (hT : ∀ u v, B u v = ⟪u, T v⟫) :
    (∃ core : InnerProductSpace.Core ℝ V, ∀ u v, core.inner u v = B u v) ↔
      (T.IsPositive ∧ Function.Bijective T) := by
  sorry

/-! 9A.7 (prose, not formalizable): explain why the proof of 9.13 (diagonalization of a symmetric
bilinear form by an orthonormal basis) fails when {lit}`𝔽 ≠ ℝ`. This is a prose
"explain why the proof fails" exercise with no crisp propositional content to
state in Lean. -/

/-- 9A.9 On {lit}`V = {p ∈ 𝒫ₙ(ℝ) : p(0) = p(1)}`, the form
{lit}`α(p, q) = ∫₀¹ p q′` is alternating: {lit}`α(p, p) = 0`. -/
theorem exercise_9A_9 (p : Polynomial ℝ) (hp : p.eval 0 = p.eval 1) :
    (∫ x in (0 : ℝ)..1, p.eval x * (Polynomial.derivative p).eval x) = 0 := by
  sorry

/-- 9A.10 On {lit}`V = {p ∈ 𝒫ₙ(ℝ) : p(0) = p(1), p′(0) = p′(1)}`, the form
{lit}`ρ(p, q) = ∫₀¹ p q″` is symmetric: {lit}`ρ(p, q) = ρ(q, p)`. -/
theorem exercise_9A_10 (p q : Polynomial ℝ)
    (hp0 : p.eval 0 = p.eval 1)
    (hp1 : (Polynomial.derivative p).eval 0 = (Polynomial.derivative p).eval 1)
    (hq0 : q.eval 0 = q.eval 1)
    (hq1 : (Polynomial.derivative q).eval 0 = (Polynomial.derivative q).eval 1) :
    (∫ x in (0 : ℝ)..1,
        p.eval x * (Polynomial.derivative (Polynomial.derivative q)).eval x) =
      (∫ x in (0 : ℝ)..1,
        q.eval x * (Polynomial.derivative (Polynomial.derivative p)).eval x) := by
  sorry

end LADR.Section_9A
