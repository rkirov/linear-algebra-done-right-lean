import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_5A
import LinearAlgebraDoneRightLean.Section_5B
import LinearAlgebraDoneRightLean.Section_5C
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 8A: Generalized Eigenvectors and Nilpotent Operators
-/

namespace LADR.Section_8A

open LADR.Section_2B (IsBasis)
open LADR.Section_3D (IsInvertible)
open LADR.Section_5A (InvariantUnder tfae_isEigenvalue)
open LADR.Section_5B (isEigenvalue_iff_isRoot aeval_eq_zero_iff_minpoly_dvd
  minpoly_eq_prod_roots)
open Module.End (HasEigenvalue HasEigenvector maxGenEigenspace genEigenspace
  mem_maxGenEigenspace independent_genEigenspace disjoint_genEigenspace)
open LADR.Section_3C (matrixOf)
open LADR.Section_5C (IsUpperTriangular exists_upperTriangular_iff_minpoly_eq_prod
  isEigenvalue_iff_diag)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! # Null Spaces of Powers of an Operator -/

/-! 8.1 Sequence of increasing null spaces.

For {lit}`T ∈ ℒ(V)` the null spaces of the powers of {lit}`T` form an increasing
chain {lit}`{0} = null T⁰ ⊆ null T¹ ⊆ ⋯`. Each inclusion holds because if
{lit}`Tᵏv = 0` then {lit}`Tᵏ⁺¹v = T(Tᵏv) = 0`. -/

theorem ker_pow_le_ker_pow_succ (T : V →ₗ[F] V) (k : ℕ) :
    ker (T ^ k) ≤ ker (T ^ (k + 1)) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [pow_succ', Module.End.mul_apply, hv, map_zero]

/-! 8.2 Equality in the sequence of null spaces.

If two consecutive terms coincide, {lit}`null Tᵐ = null Tᵐ⁺¹`, then all later
terms coincide. This is mathlib's {name}`Module.End.ker_pow_constant`. -/

theorem ker_pow_stabilizes (T : V →ₗ[F] V) {m : ℕ}
    (h : ker (T ^ m) = ker (T ^ (m + 1))) (k : ℕ) :
    ker (T ^ (m + k)) = ker (T ^ m) :=
  (Module.End.ker_pow_constant h k).symm

/-! 8.3 Null spaces stop growing: {lit}`null T^{dim V} = null T^{dim V + 1} = ⋯`.

Once we pass the dimension of the space the null spaces of the powers stabilize.
This is mathlib's {name}`Module.End.ker_pow_eq_ker_pow_finrank_of_le`. -/

theorem ker_pow_eq_ker_pow_finrank [Finite F V] (T : V →ₗ[F] V) (k : ℕ) :
    ker (T ^ (finrank F V + k)) = ker (T ^ finrank F V) :=
  Module.End.ker_pow_eq_ker_pow_finrank_of_le (Nat.le_add_right _ _)

/-! 8.5 First step of 8.4: {lit}`(null T^{dim V}) ∩ (range T^{dim V}) = {0}`.

If {lit}`v` lies in both and {lit}`n = dim V`, write {lit}`v = Tⁿu`. Then
{lit}`T²ⁿu = Tⁿv = 0`, so {lit}`u ∈ null T²ⁿ = null Tⁿ` (by 8.3), giving
{lit}`v = Tⁿu = 0`. -/

theorem disjoint_ker_range_pow_finrank [Finite F V] (T : V →ₗ[F] V) :
    Disjoint (ker (T ^ finrank F V)) (range (T ^ finrank F V)) := by
  set n := finrank F V with hn
  rw [Submodule.disjoint_def]
  rintro v hker ⟨u, rfl⟩
  rw [LinearMap.mem_ker] at hker
  have hu : (T ^ (n + n)) u = 0 := by rw [pow_add, Module.End.mul_apply]; exact hker
  have hkk : ker (T ^ (n + n)) = ker (T ^ n) := ker_pow_eq_ker_pow_finrank T n
  have hmem : u ∈ ker (T ^ n) := by rw [← hkk, LinearMap.mem_ker]; exact hu
  rw [LinearMap.mem_ker] at hmem
  exact hmem

/-! 8.4 {lit}`V` is the direct sum of {lit}`null T^{dim V}` and
{lit}`range T^{dim V}`.

The intersection is trivial (8.5), and a dimension count using the fundamental
theorem of linear maps (3.21) shows the sum is all of {lit}`V`. We package the
decomposition as {name}`IsCompl`. -/

theorem isCompl_ker_range_pow_finrank [Finite F V] (T : V →ₗ[F] V) :
    IsCompl (ker (T ^ finrank F V)) (range (T ^ finrank F V)) := by
  set n := finrank F V with hn
  have hdis : Disjoint (ker (T ^ n)) (range (T ^ n)) :=
    disjoint_ker_range_pow_finrank T
  refine ⟨hdis, codisjoint_iff.mpr (Submodule.eq_top_of_disjoint _ _ ?_ hdis)⟩
  exact (LADR.Section_3B.finrank_ker_add_finrank_range (T ^ n)).ge

/-! 8.6 Example: {lit}`F³ = null T³ ⊕ range T³` for
{lit}`T(z₁, z₂, z₃) = (4z₂, 0, 5z₃)`.

For this {lit}`T` neither {lit}`null T` nor {lit}`range T` alone gives a direct
sum decomposition ({lit}`(1, 0, 0)` lies in both), but the powers {lit}`T³` do,
as guaranteed by 8.4 (here {lit}`dim F³ = 3`). We record the computation
{lit}`T³(z₁, z₂, z₃) = (0, 0, 125z₃)`. -/

def T_8_6 (F : Type*) [Field F] : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun v := ![4 * v 1, 0, 5 * v 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

theorem T_8_6_pow_three (F : Type*) [Field F] (v : Fin 3 → F) :
    ((T_8_6 F) ^ 3) v = ![0, 0, 125 * v 2] := by
  funext i
  fin_cases i <;> simp [pow_succ, Module.End.mul_apply, T_8_6]
  all_goals ring

-- {lit}`(1, 0, 0)` lies in both {lit}`null T` and {lit}`range T`, so
-- {lit}`null T + range T` is not a direct sum.
example : ¬ Disjoint (ker (T_8_6 ℝ)) (range (T_8_6 ℝ)) := by
  rw [Submodule.disjoint_def]
  intro h
  have h1 : (![1, 0, 0] : Fin 3 → ℝ) ∈ ker (T_8_6 ℝ) := by
    rw [LinearMap.mem_ker]; funext i; fin_cases i <;> simp [T_8_6]
  have h2 : (![1, 0, 0] : Fin 3 → ℝ) ∈ range (T_8_6 ℝ) :=
    ⟨![0, 1 / 4, 0], by funext i; fin_cases i <;> simp [T_8_6]⟩
  have := h _ h1 h2
  have h0 : (![1, 0, 0] : Fin 3 → ℝ) 0 = 0 := by rw [this]; rfl
  simp at h0

-- However {lit}`F³ = null T³ ⊕ range T³` (this is 8.4 at exponent {lit}`3`).
example : IsCompl (ker ((T_8_6 ℝ) ^ 3)) (range ((T_8_6 ℝ) ^ 3)) := by
  have h := isCompl_ker_range_pow_finrank (T_8_6 ℝ)
  have hdim : finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  rwa [hdim] at h

/-! # Generalized Eigenvectors -/

/-! 8.8 Definition: generalized eigenvector.

Axler: {lit}`v ≠ 0` is a *generalized eigenvector* of {lit}`T` corresponding to
{lit}`λ` if {lit}`(T − λI)ᵏv = 0` for some positive integer {lit}`k`. In mathlib
the set of such vectors together with {lit}`0` is the *maximal generalized
eigenspace* {name}`Module.End.maxGenEigenspace` (the union of the kernels of
{lit}`(T − λI)ᵏ`), written {lit}`G(λ, T)` by Axler. We define a generalized
eigenvector as a nonzero element of this subspace and bridge to Axler's literal
formulation. -/

def IsGeneralizedEigenvector (T : V →ₗ[F] V) (lam : F) (v : V) : Prop :=
  v ≠ 0 ∧ v ∈ maxGenEigenspace T lam

theorem isGeneralizedEigenvector_iff_exists_pow (T : V →ₗ[F] V) (lam : F) (v : V) :
    IsGeneralizedEigenvector T lam v ↔
      v ≠ 0 ∧ ∃ k : ℕ, 0 < k ∧ ((T - lam • (1 : Module.End F V)) ^ k) v = 0 := by
  unfold IsGeneralizedEigenvector
  rw [mem_maxGenEigenspace]
  constructor
  · rintro ⟨hv, k, hk⟩
    refine ⟨hv, ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [pow_zero, Module.End.one_apply] at hk
      exact absurd hk hv
    · exact ⟨k, hpos, hk⟩
  · rintro ⟨hv, k, _, hk⟩
    exact ⟨hv, k, hk⟩

/-! The characterization from the margin note of 8.8: a nonzero vector is a
generalized eigenvector for {lit}`λ` iff {lit}`(T − λI)^{dim V}v = 0`. This is
{name}`Module.End.maxGenEigenspace_eq_genEigenspace_finrank` combined with
{name}`Module.End.genEigenspace_nat`. -/

theorem mem_maxGenEigenspace_iff_pow_finrank [Finite F V] (T : V →ₗ[F] V) (lam : F)
    (v : V) :
    v ∈ maxGenEigenspace T lam ↔
      ((T - lam • (1 : Module.End F V)) ^ finrank F V) v = 0 := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat,
    LinearMap.mem_ker]

/-! 8.9 A basis of generalized eigenvectors.

If {lit}`F = ℂ` then {lit}`V` has a basis consisting of generalized eigenvectors
of {lit}`T`. The essential content — that the generalized eigenspaces span
{lit}`V` — is mathlib's {name}`Module.End.iSup_maxGenEigenspace_eq_top` (valid
over any algebraically closed field). A basis of generalized eigenvectors can
then be extracted from a spanning set. -/

theorem iSup_maxGenEigenspace_eq_top {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    ⨆ μ : ℂ, maxGenEigenspace T μ = ⊤ :=
  Module.End.iSup_maxGenEigenspace_eq_top T

/-! 8.10 Example: generalized eigenvectors of an operator on {lit}`ℂ³`.

For {lit}`T(z₁, z₂, z₃) = (4z₂, 0, 5z₃)` the eigenvalues are {lit}`0` and
{lit}`5`. The generalized eigenvectors for {lit}`0` are the nonzero
{lit}`(z₁, z₂, 0)` and those for {lit}`5` are the nonzero {lit}`(0, 0, z₃)`. In
particular each standard basis vector of {lit}`ℂ³` is a generalized eigenvector,
witnessing 8.9. -/

example : IsGeneralizedEigenvector (T_8_6 ℂ) 0 ![1, 0, 0] := by
  refine ⟨?_, ?_⟩
  · intro h; have := congrFun h 0; simp at this
  · rw [mem_maxGenEigenspace]
    refine ⟨3, ?_⟩
    rw [zero_smul, sub_zero, T_8_6_pow_three]
    funext i; fin_cases i <;> simp

example : IsGeneralizedEigenvector (T_8_6 ℂ) 0 ![0, 1, 0] := by
  refine ⟨?_, ?_⟩
  · intro h; have := congrFun h 1; simp at this
  · rw [mem_maxGenEigenspace]
    refine ⟨3, ?_⟩
    rw [zero_smul, sub_zero, T_8_6_pow_three]
    funext i; fin_cases i <;> simp

example : IsGeneralizedEigenvector (T_8_6 ℂ) 5 ![0, 0, 1] := by
  refine ⟨?_, ?_⟩
  · intro h; have := congrFun h 2; simp at this
  · rw [mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    funext i
    fin_cases i <;>
      simp [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        T_8_6]

/-! 8.11 A generalized eigenvector corresponds to a unique eigenvalue.

If {lit}`v ≠ 0` is a generalized eigenvector for both {lit}`α` and {lit}`λ` then
{lit}`α = λ`, because the maximal generalized eigenspaces for distinct scalars
are disjoint ({name}`Module.End.disjoint_genEigenspace`). -/

theorem generalizedEigenvector_unique_eigenvalue (T : V →ₗ[F] V) {alpha lam : F}
    {v : V} (hv : v ≠ 0) (ha : v ∈ maxGenEigenspace T alpha)
    (hl : v ∈ maxGenEigenspace T lam) : alpha = lam := by
  by_contra hne
  have hdis : Disjoint (maxGenEigenspace T alpha) (maxGenEigenspace T lam) :=
    disjoint_genEigenspace T hne ⊤ ⊤
  have hmem : v ∈ maxGenEigenspace T alpha ⊓ maxGenEigenspace T lam := ⟨ha, hl⟩
  rw [disjoint_iff.mp hdis] at hmem
  exact hv (Submodule.mem_bot F |>.mp hmem)

/-! 8.12 Linearly independent generalized eigenvectors.

Generalized eigenvectors corresponding to distinct eigenvalues are linearly
independent. Axler's inductive argument (peeling off {lit}`(T − λₘI)ⁿ`) is
captured in mathlib by the independence of the generalized eigenspaces
({name}`Module.End.independent_genEigenspace`): a choice of nonzero vector from
each of an independent family of subspaces is linearly independent. -/

theorem generalizedEigenvectors_linearIndependent (T : V →ₗ[F] V) {m : ℕ}
    (lam : Fin m → F) (hlam : Function.Injective lam) (v : Fin m → V)
    (hv_ne : ∀ k, v k ≠ 0) (hv_mem : ∀ k, v k ∈ maxGenEigenspace T (lam k)) :
    LinearIndependent F v := by
  have hcomp := (independent_genEigenspace T ⊤).comp hlam
  exact hcomp.linearIndependent _ hv_mem hv_ne

/-! # Nilpotent Operators -/

/-! 8.14 Definition: nilpotent.

An operator is *nilpotent* if some power of it is {lit}`0`; this is mathlib's
{name}`IsNilpotent`. Equivalently every nonzero vector is a generalized
eigenvector corresponding to the eigenvalue {lit}`0` (recorded below in
{lit}`isNilpotent_iff_maxGenEigenspace_zero_eq_top`). -/

theorem isNilpotent_iff_exists_pow (T : V →ₗ[F] V) :
    IsNilpotent T ↔ ∃ k : ℕ, T ^ k = 0 := Iff.rfl

/-! 8.15 Example: nilpotent operators.

(a) {lit}`T(z₁, z₂, z₃, z₄) = (0, 0, z₁, z₂)` on {lit}`F⁴` is nilpotent because
{lit}`T² = 0`.

(b) The operator on {lit}`F³` with matrix
{lit}`[[-3, 9, 0], [-7, 9, 6], [4, 0, -6]]` is nilpotent, its cube being the zero
matrix.

(c) Differentiation on {lit}`𝒫ₘ(ℝ)` is nilpotent, since the {lit}`(m+1)`-th
derivative of a polynomial of degree at most {lit}`m` is {lit}`0`. -/

def T_8_15a (F : Type*) [Field F] : (Fin 4 → F) →ₗ[F] (Fin 4 → F) where
  toFun v := ![0, 0, v 0, v 1]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

example : IsNilpotent (T_8_15a F) := by
  refine ⟨2, ?_⟩
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;>
    simp [pow_succ, Module.End.mul_apply, T_8_15a]

/-- The matrix of 8.15(b). -/
def A_8_15b (F : Type*) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![-3, 9, 0; -7, 9, 6; 4, 0, -6]

/-- 8.15(b) The cube of the matrix of 8.15(b) is the zero matrix. -/
theorem A_8_15b_pow_three : (A_8_15b F) ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A_8_15b, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- 8.15(b) The operator on {lit}`F³` with that matrix is therefore nilpotent. -/
theorem isNilpotent_toLin'_A_8_15b : IsNilpotent (Matrix.toLinAlgEquiv' (A_8_15b F)) :=
  ⟨3, by rw [← map_pow, A_8_15b_pow_three, map_zero]⟩

/-- 8.15(c) Differentiation {lit}`D p = p′` on {lit}`𝒫ₘ(ℝ)`, modelled as
{lit}`Polynomial.degreeLT ℝ (m+1)`, is nilpotent: {lit}`D^{m+1} = 0` because the
{lit}`(m+1)`-th derivative of a polynomial of degree at most {lit}`m` is
{lit}`0`. -/
theorem isNilpotent_derivative_degreeLT (m : ℕ)
    (D : Polynomial.degreeLT ℝ (m + 1) →ₗ[ℝ] Polynomial.degreeLT ℝ (m + 1))
    (hD : ∀ p : Polynomial.degreeLT ℝ (m + 1),
      (D p : Polynomial ℝ) = Polynomial.derivative (p : Polynomial ℝ)) :
    IsNilpotent D := by
  have hpow : ∀ (k : ℕ) (p : Polynomial.degreeLT ℝ (m + 1)),
      ((D ^ k) p : Polynomial ℝ) = Polynomial.derivative^[k] (p : Polynomial ℝ) := by
    intro k
    induction k with
    | zero => intro p; simp
    | succ n ih =>
      intro p
      rw [pow_succ, Module.End.mul_apply, ih (D p), hD p, ← Function.iterate_succ_apply]
  refine ⟨m + 1, ?_⟩
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  rw [hpow]
  have hdeg : (p : Polynomial ℝ).natDegree < m + 1 := by
    rcases eq_or_ne (p : Polynomial ℝ) 0 with h0 | h0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (Polynomial.mem_degreeLT.mp p.2)
  rw [Polynomial.iterate_derivative_eq_zero hdeg]
  rfl

/-! 8.16 A nilpotent operator raised to the dimension of the domain is
{lit}`0`: if {lit}`T` is nilpotent then {lit}`T^{dim V} = 0`.

If {lit}`Tᵏ = 0` then {lit}`null Tᵏ = V`, and by 8.1 and 8.3 also
{lit}`null T^{dim V} = V`, whence {lit}`T^{dim V} = 0`. -/

theorem pow_finrank_eq_zero_of_isNilpotent [Finite F V] (T : V →ₗ[F] V)
    (h : IsNilpotent T) : T ^ finrank F V = 0 := by
  obtain ⟨k, hk⟩ := h
  have hker : ker (T ^ k) = ⊤ := by rw [hk]; exact LinearMap.ker_zero
  have hle := Module.End.ker_pow_le_ker_pow_finrank T k
  rw [hker, top_le_iff] at hle
  exact LinearMap.ker_eq_top.mp hle

/-! Axler's remark following 8.14: {lit}`T` is nilpotent iff every nonzero
vector is a generalized eigenvector for {lit}`0`, i.e. iff
{lit}`G(0, T) = V`. -/

theorem maxGenEigenspace_zero_eq_ker_pow [Finite F V] (T : V →ₗ[F] V) :
    maxGenEigenspace T 0 = ker (T ^ finrank F V) := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_zero_nat]

theorem isNilpotent_iff_maxGenEigenspace_zero_eq_top [Finite F V] (T : V →ₗ[F] V) :
    IsNilpotent T ↔ maxGenEigenspace T 0 = ⊤ := by
  rw [maxGenEigenspace_zero_eq_ker_pow, LinearMap.ker_eq_top]
  exact ⟨fun h => pow_finrank_eq_zero_of_isNilpotent T h, fun h => ⟨finrank F V, h⟩⟩

/-! 8.17 Eigenvalues of a nilpotent operator.

(a) If {lit}`T` is nilpotent then {lit}`0` is an eigenvalue of {lit}`T` (when
{lit}`V ≠ {0}`) and {lit}`T` has no other eigenvalues.

(b) If {lit}`F = ℂ` and {lit}`0` is the only eigenvalue of {lit}`T`, then
{lit}`T` is nilpotent. -/

theorem zero_hasEigenvalue_of_isNilpotent [Finite F V] [Nontrivial V]
    (T : V →ₗ[F] V) (h : IsNilpotent T) : HasEigenvalue T 0 := by
  have hnotinj : ¬ Function.Injective T := by
    intro hinj
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hne : ∀ k, (T ^ k) v ≠ 0 := by
      intro k
      induction k with
      | zero => simpa using hv
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact fun hh => ih (hinj (hh.trans (map_zero T).symm))
    exact hne (finrank F V)
      (by rw [pow_finrank_eq_zero_of_isNilpotent T h, LinearMap.zero_apply])
  have htfae := (tfae_isEigenvalue T 0).out 0 1
  rw [htfae]
  simpa using hnotinj

theorem eigenvalue_eq_zero_of_isNilpotent (T : V →ₗ[F] V) (h : IsNilpotent T)
    {lam : F} (hlam : HasEigenvalue T lam) : lam = 0 := by
  obtain ⟨v, hv, hTv⟩ := Module.End.hasEigenvalue_iff_exists.mp hlam
  obtain ⟨k, hk⟩ := h
  have h1 : ∀ n, (T ^ n) v = lam ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hTv, smul_smul, pow_succ]
  have hpow : (lam ^ k) • v = 0 := by rw [← h1, hk, LinearMap.zero_apply]
  have hlk : lam ^ k = 0 := (smul_eq_zero.mp hpow).resolve_right hv
  have hk0 : k ≠ 0 := by rintro rfl; simp at hlk
  exact pow_eq_zero_iff hk0 |>.mp hlk

theorem isNilpotent_of_zero_only_eigenvalue {V : Type*} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (T : V →ₗ[ℂ] V)
    (h : ∀ lam : ℂ, HasEigenvalue T lam → lam = 0) : IsNilpotent T := by
  obtain ⟨hprod, hroots⟩ := minpoly_eq_prod_roots T
  have hall : ∀ a ∈ (minpoly ℂ T).roots, a = 0 := fun a ha => h a ((hroots a).mp ha)
  have hmap : Multiset.map (fun a => Polynomial.X - Polynomial.C a) (minpoly ℂ T).roots
      = Multiset.replicate (minpoly ℂ T).roots.card Polynomial.X := by
    rw [Multiset.eq_replicate]
    refine ⟨by rw [Multiset.card_map], ?_⟩
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
    rw [hall a ha, map_zero, sub_zero]
  have hmin : minpoly ℂ T = Polynomial.X ^ (minpoly ℂ T).roots.card := by
    conv_lhs => rw [hprod, hmap, Multiset.prod_replicate]
  have haeval := minpoly.aeval ℂ T
  rw [hmin, map_pow, Polynomial.aeval_X] at haeval
  exact ⟨_, haeval⟩

/-! 8.18 Minimal polynomial and upper-triangular matrix of a nilpotent operator.

Axler proves the equivalence of three conditions: (a) {lit}`T` is nilpotent;
(b) the minimal polynomial of {lit}`T` is {lit}`zᵐ` for some positive integer
{lit}`m`; (c) there is a basis with respect to which the matrix of {lit}`T` is
strictly upper triangular. We prove the equivalence (a) ↔ (b) as
{lit}`isNilpotent_iff_minpoly_eq_X_pow`, and the "(a) ⟹ (c)" direction as
{lit}`exists_strictUpperTriangular_of_nilpotent` below — following Axler, since the
minimal polynomial {lit}`zᵐ` splits, 5.44 gives a basis with an upper-triangular
matrix (Section 5C {name}`exists_upperTriangular_iff_minpoly_eq_prod`), and its diagonal
entries are eigenvalues (5.41) hence {lit}`0`, so the matrix is strictly upper
triangular (zero on and below the diagonal). -/

theorem isNilpotent_iff_minpoly_eq_X_pow [Finite F V] [Nontrivial V] (T : V →ₗ[F] V) :
    IsNilpotent T ↔ ∃ m : ℕ, 0 < m ∧ minpoly F T = Polynomial.X ^ m := by
  constructor
  · rintro ⟨k, hk⟩
    have hdvd : minpoly F T ∣ Polynomial.X ^ k := by
      rw [← aeval_eq_zero_iff_minpoly_dvd, map_pow, Polynomial.aeval_X]; exact hk
    obtain ⟨i, _, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X k).mp hdvd
    have hmonicX : (Polynomial.X ^ i : Polynomial F).Monic := Polynomial.monic_X.pow i
    have heq : minpoly F T = Polynomial.X ^ i :=
      Polynomial.eq_of_monic_of_associated
        (minpoly.monic (Algebra.IsIntegral.isIntegral T)) hmonicX hassoc
    refine ⟨i, ?_, heq⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exfalso
      rw [pow_zero] at heq
      have haeval := minpoly.aeval F T
      rw [heq, map_one] at haeval
      exact one_ne_zero haeval
    · exact hpos
  · rintro ⟨m, _, heq⟩
    refine ⟨m, ?_⟩
    have haeval := minpoly.aeval F T
    rw [heq, map_pow, Polynomial.aeval_X] at haeval
    exact haeval

/-- 8.18(c) A nilpotent operator has a basis with respect to which its matrix is
strictly upper triangular: upper triangular with all diagonal entries {lit}`0`
(equivalently, all entries on and below the diagonal are {lit}`0`). -/
theorem exists_strictUpperTriangular_of_nilpotent [Finite F V] [Nontrivial V]
    (T : V →ₗ[F] V) (hT : IsNilpotent T) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T) ∧ ∀ k, matrixOf hv hv T k k = 0 := by
  obtain ⟨m, hm, hminpoly⟩ := (isNilpotent_iff_minpoly_eq_X_pow T).mp hT
  have hprod : minpoly F T = ∏ _k : Fin m, (Polynomial.X - Polynomial.C (0 : F)) := by
    rw [hminpoly]
    simp only [map_zero, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨n, v, hv, hA⟩ :=
    (exists_upperTriangular_iff_minpoly_eq_prod T).mpr ⟨m, fun _ => 0, hprod⟩
  refine ⟨n, v, hv, hA, fun k => ?_⟩
  have heig : HasEigenvalue T (matrixOf hv hv T k k) :=
    (isEigenvalue_iff_diag hv T hA _).mpr ⟨k, rfl⟩
  have hroot := (isEigenvalue_iff_isRoot T _).mp heig
  rw [hminpoly, Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_X] at hroot
  exact (pow_eq_zero_iff (by omega : m ≠ 0)).mp hroot

/-! # Exercises -/

/-- 8A.1 -/
theorem exercise_8A_1 [Finite F V] (T : V →ₗ[F] V)
    (h4 : finrank F (ker (T ^ 4)) = 8) (h6 : finrank F (ker (T ^ 6)) = 9)
    (m : ℕ) (hm : 5 ≤ m) : finrank F (ker (T ^ m)) = 9 := by
  sorry

/-- 8A.2 -/
theorem exercise_8A_2 (T : V →ₗ[F] V) {m : ℕ} (hm : 0 < m) (v : V)
    (h1 : (T ^ (m - 1)) v ≠ 0) (h2 : (T ^ m) v = 0) :
    LinearIndependent F (fun k : Fin m => (T ^ (k : ℕ)) v) := by
  sorry

/-- 8A.3 -/
theorem exercise_8A_3 [Finite F V] (T : V →ₗ[F] V) :
    IsCompl (ker T) (range T) ↔ ker (T ^ 2) = ker T := by
  sorry

/-- 8A.4 -/
theorem exercise_8A_4 [Finite F V] (T : V →ₗ[F] V) (lam : F) (m : ℕ) (hm : 0 < m)
    (h : (Polynomial.X - Polynomial.C lam) ^ m ∣ minpoly F T) :
    m ≤ finrank F (ker ((T - lam • (1 : Module.End F V)) ^ m)) := by
  sorry

/-- 8A.5 -/
theorem exercise_8A_5 [Finite F V] (T : V →ₗ[F] V) (m : ℕ) :
    finrank F (ker (T ^ m)) ≤ m * finrank F (ker T) := by
  sorry

/-- 8A.6 -/
theorem exercise_8A_6 (T : V →ₗ[F] V) (k : ℕ) :
    range (T ^ (k + 1)) ≤ range (T ^ k) := by
  sorry

/-- 8A.7 -/
theorem exercise_8A_7 (T : V →ₗ[F] V) (m : ℕ)
    (h : range (T ^ m) = range (T ^ (m + 1))) (k : ℕ) (hk : m < k) :
    range (T ^ k) = range (T ^ m) := by
  sorry

/-- 8A.8 -/
theorem exercise_8A_8 [Finite F V] (T : V →ₗ[F] V) (k : ℕ) :
    range (T ^ (finrank F V + k)) = range (T ^ finrank F V) := by
  sorry

/-- 8A.9 -/
theorem exercise_8A_9 [Finite F V] (T : V →ₗ[F] V) (m : ℕ) :
    ker (T ^ m) = ker (T ^ (m + 1)) ↔ range (T ^ m) = range (T ^ (m + 1)) := by
  sorry

/-- 8A.10 {lit}`T(w, z) = (z, 0)` on {lit}`ℂ²`: find all generalized
eigenvectors. -/
def T_ex_8A_10 : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 1, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- The set of generalized eigenvectors of {lit}`T_ex_8A_10` — to be
determined. -/
def genEigenvectors_8A_10 : Set (Fin 2 → ℂ) := sorry

theorem exercise_8A_10 (v : Fin 2 → ℂ) :
    (∃ lam : ℂ, IsGeneralizedEigenvector T_ex_8A_10 lam v) ↔
      v ∈ genEigenvectors_8A_10 := by
  sorry

/-- 8A.11 (stated for {lit}`F = ℝ`; the case {lit}`F = ℂ` follows from 5.27(b)
and 8.9). Existence of a basis of generalized eigenvectors — encoded as the
generalized eigenspaces spanning {lit}`V` — is equivalent to the minimal
polynomial being a product of linear factors. -/
theorem exercise_8A_11 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    (T : V →ₗ[ℝ] V) :
    (⨆ μ : ℝ, maxGenEigenspace T μ) = ⊤ ↔
      ∃ (m : ℕ) (lam : Fin m → ℝ),
        minpoly ℝ T = ∏ i, (Polynomial.X - Polynomial.C (lam i)) := by
  sorry

/-- 8A.12 -/
theorem exercise_8A_12 [Finite F V] (T : V →ₗ[F] V)
    (h : ∀ v : V, v ≠ 0 → ∃ lam : F, v ∈ maxGenEigenspace T lam) :
    ∃ lam : F, IsNilpotent (T - lam • (1 : Module.End F V)) := by
  sorry

/-- 8A.13 -/
theorem exercise_8A_13 (S T : V →ₗ[F] V) (h : IsNilpotent (S * T)) :
    IsNilpotent (T * S) := by
  sorry

/-- 8A.14 A nonzero nilpotent operator is not diagonalizable (Axler:
diagonalizable means {lit}`V` has a basis of eigenvectors, i.e. the eigenspaces
span {lit}`V`). -/
theorem exercise_8A_14 [Finite F V] (T : V →ₗ[F] V) (hnil : IsNilpotent T)
    (hne : T ≠ 0) : ¬ ((⨆ μ : F, Module.End.eigenspace T μ) = ⊤) := by
  sorry

/-- 8A.15 Over {lit}`ℂ`, {lit}`T` is diagonalizable iff every generalized
eigenvector is an eigenvector (i.e. each generalized eigenspace equals the
corresponding eigenspace). -/
theorem exercise_8A_15 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) :
    (⨆ μ : ℂ, Module.End.eigenspace T μ) = ⊤ ↔
      ∀ μ : ℂ, maxGenEigenspace T μ = Module.End.eigenspace T μ := by
  sorry

/-- 8A.16 (a) -/
theorem exercise_8A_16a :
    ∃ (S T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)),
      IsNilpotent S ∧ IsNilpotent T ∧ ¬ IsNilpotent (S + T) ∧
        ¬ IsNilpotent (S * T) := by
  sorry

/-- 8A.16 (b) -/
@[avoiding Commute.isNilpotent_add]
theorem exercise_8A_16b (S T : V →ₗ[F] V) (hS : IsNilpotent S) (hT : IsNilpotent T)
    (hcomm : S * T = T * S) : IsNilpotent (S + T) ∧ IsNilpotent (S * T) := by
  sorry

/-- 8A.17 If {lit}`T` is nilpotent with {lit}`Tᵐ = 0`, then {lit}`I − T` is
invertible with inverse {lit}`I + T + ⋯ + Tᵐ⁻¹`. -/
theorem exercise_8A_17 (T : V →ₗ[F] V) {m : ℕ} (hm : 0 < m) (hT : T ^ m = 0) :
    (1 - T) * (∑ i ∈ Finset.range m, T ^ i) = 1 ∧
      (∑ i ∈ Finset.range m, T ^ i) * (1 - T) = 1 := by
  sorry

/-- 8A.18 -/
theorem exercise_8A_18 [Finite F V] (T : V →ₗ[F] V) (hnil : IsNilpotent T) :
    T ^ (1 + finrank F (range T)) = 0 := by
  sorry

/-- 8A.19 -/
theorem exercise_8A_19 [Finite F V] (T : V →ₗ[F] V) (hnil : ¬ IsNilpotent T) :
    IsCompl (ker (T ^ (finrank F V - 1))) (range (T ^ (finrank F V - 1))) := by
  sorry

/-- 8A.20 On an inner product space, a normal nilpotent operator is {lit}`0`. -/
theorem exercise_8A_20 {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] E)
    (hN : IsStarNormal T) (hnil : IsNilpotent T) : T = 0 := by
  sorry

/-- 8A.21 -/
theorem exercise_8A_21 [Finite F V] (T : V →ₗ[F] V)
    (h : ker (T ^ (finrank F V - 1)) ≠ ker (T ^ finrank F V)) :
    IsNilpotent T ∧
      ∀ k : ℕ, k ≤ finrank F V → finrank F (ker (T ^ k)) = k := by
  sorry

/-- 8A.22 -/
theorem exercise_8A_22 (T : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ))
    (h : range (T ^ 4) ≠ range (T ^ 5)) : IsNilpotent T := by
  sorry

/-- 8A.23 An operator on a real vector space whose only eigenvalue is {lit}`0`
but which is not nilpotent (so the hypothesis {lit}`F = ℂ` cannot be dropped
from 8.17(b)). -/
theorem exercise_8A_23 :
    ∃ T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ),
      (∀ lam : ℝ, HasEigenvalue T lam → lam = 0) ∧ ¬ IsNilpotent T := by
  sorry

/-! 8A.24 For each operator of Example 8.15, exhibit a basis putting it into the
strictly-upper-triangular normal form of 8.18(c). 8.18(c) itself is proved above
({name}`LADR.Section_8A.exists_strictUpperTriangular_of_nilpotent`); what is asked
here is the explicit basis in each case, so each part gets a named
{lit}`def … := sorry` for the solver to fill in. -/

/-- The basis of {lit}`F⁴` for 8A.24 putting {name}`T_8_15a` into strictly
upper-triangular form. -/
def basis_8A_24a (F : Type*) [Field F] : Fin 4 → (Fin 4 → F) := sorry

theorem exercise_8A_24a (hv : IsBasis F (basis_8A_24a F)) :
    IsUpperTriangular (matrixOf hv hv (T_8_15a F)) ∧
      ∀ k, matrixOf hv hv (T_8_15a F) k k = 0 := by
  sorry

/-- The basis of {lit}`F³` for 8A.24 putting the operator of {name}`A_8_15b` into
strictly upper-triangular form. -/
def basis_8A_24b (F : Type*) [Field F] : Fin 3 → (Fin 3 → F) := sorry

theorem exercise_8A_24b (hv : IsBasis F (basis_8A_24b F)) :
    IsUpperTriangular (matrixOf hv hv (Matrix.toLinAlgEquiv' (A_8_15b F))) ∧
      ∀ k, matrixOf hv hv (Matrix.toLinAlgEquiv' (A_8_15b F)) k k = 0 := by
  sorry

/-- The basis of {lit}`𝒫ₘ(ℝ)` for 8A.24 putting differentiation into strictly
upper-triangular form. -/
noncomputable def basis_8A_24c (m : ℕ) : Fin (m + 1) → Polynomial.degreeLT ℝ (m + 1) := sorry

theorem exercise_8A_24c (m : ℕ) (hv : IsBasis ℝ (basis_8A_24c m))
    (D : Polynomial.degreeLT ℝ (m + 1) →ₗ[ℝ] Polynomial.degreeLT ℝ (m + 1))
    (hD : ∀ p : Polynomial.degreeLT ℝ (m + 1),
      (D p : Polynomial ℝ) = Polynomial.derivative (p : Polynomial ℝ)) :
    IsUpperTriangular (matrixOf hv hv D) ∧ ∀ k, matrixOf hv hv D k k = 0 := by
  sorry

/-- 8A.25 On an inner product space, a nilpotent operator has an *orthonormal*
basis giving the strictly-upper-triangular form of 8.18(c) — the Gram–Schmidt
refinement of {name}`LADR.Section_8A.exists_strictUpperTriangular_of_nilpotent`. -/
theorem exercise_8A_25 {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Nontrivial E] (T : E →ₗ[𝕜] E)
    (hT : IsNilpotent T) :
    ∃ (n : ℕ) (e : Fin n → E) (he : Orthonormal 𝕜 e) (hb : IsBasis 𝕜 e),
      IsUpperTriangular (matrixOf hb hb T) ∧ ∀ k, matrixOf hb hb T k k = 0 := by
  sorry

end LADR.Section_8A
