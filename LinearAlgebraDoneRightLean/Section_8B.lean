import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import LinearAlgebraDoneRightLean.Section_1B
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_5A
import LinearAlgebraDoneRightLean.Section_5B
import LinearAlgebraDoneRightLean.Section_8A
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 8B: Generalized Eigenspace Decomposition
-/

namespace LADR.Section_8B

open LADR.Section_5A (InvariantUnder tfae_isEigenvalue)
open LADR.Section_5B (isEigenvalue_iff_isRoot aeval_eq_zero_iff_minpoly_dvd)
open Module.End (HasEigenvalue HasEigenvector maxGenEigenspace genEigenspace
  mem_maxGenEigenspace independent_maxGenEigenspace mapsTo_maxGenEigenspace_of_comm
  isNilpotent_restrict_maxGenEigenspace_sub_algebraMap iSup_maxGenEigenspace_eq_top
  disjoint_genEigenspace)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval X C)
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf matrixOf_apply)
open LADR.Section_5C (IsUpperTriangular)
open LADR.Section_8A (exists_strictUpperTriangular_of_nilpotent)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! # The Generalized Eigenspace Decomposition -/

/-! 8.21 Example: generalized eigenspaces of an operator on {lit}`ℂ³`. For
{lit}`T(z₁, z₂, z₃) = (4z₂, 0, 5z₃)`, one has {lit}`G(0, T) = {(z₁, z₂, 0)}` and
{lit}`G(5, T) = {(0, 0, z₃)}`, so {lit}`ℂ³ = G(0, T) ⊕ G(5, T)` — a concrete
instance of the decomposition 8.22 (the generalized eigenvectors of this same
operator appear in 8A's Example 8.10). We formalize all three claims. Since
{lit}`dim ℂ³ = 3`, the generalized eigenspace {lit}`G(λ, T)` is
{lit}`null(T − λI)³` (8.20), computed here from the explicit cubes. -/

section Example_8_21

open scoped Matrix

/-- The operator {lit}`T(z₁, z₂, z₃) = (4z₂, 0, 5z₃)` on {lit}`ℂ³` of Example 8.21. -/
def T_8_21 : Module.End ℂ (Fin 3 → ℂ) where
  toFun z := ![4 * z 1, 0, 5 * z 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

/-- {lit}`T³(z₁, z₂, z₃) = (0, 0, 125 z₃)`. -/
theorem T_8_21_cube (z : Fin 3 → ℂ) : (T_8_21 ^ 3) z = ![0, 0, 125 * z 2] := by
  funext i; fin_cases i <;> simp [pow_succ, Module.End.mul_apply, T_8_21]; ring

/-- {lit}`(T − 5I)³(z₁, z₂, z₃) = (−125 z₁ + 300 z₂, −125 z₂, 0)`. -/
theorem T_8_21_sub_cube (z : Fin 3 → ℂ) :
    ((T_8_21 - (5:ℂ) • (1 : Module.End ℂ (Fin 3 → ℂ))) ^ 3) z
      = ![-125 * z 0 + 300 * z 1, -125 * z 1, 0] := by
  funext i
  fin_cases i <;>
    simp [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, smul_eq_mul, T_8_21] <;>
    ring

/-- 8.21: {lit}`G(0, T) = {(z₁, z₂, 0)}`, the vectors with vanishing third
coordinate. -/
theorem maxGenEigenspace_zero_8_21 :
    maxGenEigenspace T_8_21 0 = LinearMap.ker (LinearMap.proj 2) := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat]
  simp only [Module.finrank_pi, Fintype.card_fin]
  ext z
  simp only [LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · intro h; have := congrFun h 2; simpa [T_8_21_cube] using this
  · intro h; funext i; fin_cases i <;> simp [T_8_21_cube, h]

/-- 8.21: {lit}`G(5, T) = {(0, 0, z₃)}`, the vectors with vanishing first two
coordinates. -/
theorem maxGenEigenspace_five_8_21 :
    maxGenEigenspace T_8_21 5 =
      LinearMap.ker (LinearMap.proj 0) ⊓ LinearMap.ker (LinearMap.proj (1 : Fin 3)) := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.genEigenspace_nat]
  simp only [Module.finrank_pi, Fintype.card_fin]
  ext z
  simp only [LinearMap.mem_ker, Submodule.mem_inf, LinearMap.proj_apply]
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp only [T_8_21_sub_cube, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    have hz1 : z 1 = 0 := by linear_combination (-1/125 : ℂ) * h1
    have hz0 : z 0 = 0 := by linear_combination (-1/125 : ℂ) * h0 + (12/5 : ℂ) * hz1
    exact ⟨hz0, hz1⟩
  · rintro ⟨hz0, hz1⟩; funext i; fin_cases i <;> simp [T_8_21_sub_cube, hz0, hz1]

/-- 8.21: {lit}`ℂ³ = G(0, T) ⊕ G(5, T)`, packaged as complementarity of the two
generalized eigenspaces. -/
theorem isCompl_maxGenEigenspace_8_21 :
    IsCompl (maxGenEigenspace T_8_21 0) (maxGenEigenspace T_8_21 5) := by
  rw [maxGenEigenspace_zero_8_21, maxGenEigenspace_five_8_21]
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro z hzmem
    simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply] at hzmem
    obtain ⟨h2, h0, h1⟩ := hzmem
    simp only [Submodule.mem_bot]; funext i; fin_cases i <;> simp_all
  · rw [codisjoint_iff, eq_top_iff]
    intro z _
    rw [Submodule.mem_sup]
    exact ⟨![z 0, z 1, 0], by simp [LinearMap.mem_ker], ![0, 0, z 2],
      by simp [Submodule.mem_inf, LinearMap.mem_ker], by funext i; fin_cases i <;> simp⟩

end Example_8_21

/-! 8.22 Generalized eigenspace decomposition.

Suppose {lit}`F = ℂ` and {lit}`T ∈ ℒ(V)`, with distinct eigenvalues
{lit}`λ₁, …, λₘ`. Then (a) each {lit}`G(λₖ, T)` is invariant under {lit}`T`;
(b) {lit}`(T − λₖI)|_{G(λₖ,T)}` is nilpotent; (c)
{lit}`V = G(λ₁, T) ⊕ ⋯ ⊕ G(λₘ, T)`.

Part (a) holds over any field: the generalized eigenspace
{lit}`G(μ, T) = null(T − μI)^{dim V}` is invariant under {lit}`T` because
{lit}`T` commutes with {lit}`(T − μI)^{dim V}` (this is Axler's use of 5.18). In
mathlib this is {name}`Module.End.mapsTo_maxGenEigenspace_of_comm`. -/

theorem invariantUnder_maxGenEigenspace (T : V →ₗ[F] V) (μ : F) :
    InvariantUnder T (maxGenEigenspace T μ) := fun _u hu =>
  mapsTo_maxGenEigenspace_of_comm (Commute.refl T) μ hu

/-! 8.22 (b) The restriction of {lit}`T − λI` to {lit}`G(λ, T)` is nilpotent.
If {lit}`v ∈ G(λ, T)` then {lit}`(T − λI)^{dim V}v = 0` (by 8.20), so the
restriction raised to {lit}`dim V` is {lit}`0`. In mathlib the operator
{lit}`T − λI` is {lit}`T − algebraMap F (End F V) λ = T − λ • 1`, and the
nilpotency of its restriction is
{name}`Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap`. -/

theorem isNilpotent_restrict_sub_algebraMap [Finite F V] (T : V →ₗ[F] V) (μ : F)
    (h : Set.MapsTo ((T : Module.End F V) - algebraMap F (Module.End F V) μ)
        (maxGenEigenspace T μ) (maxGenEigenspace T μ) :=
      mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes T μ) μ) :
    IsNilpotent (((T : Module.End F V) - algebraMap F (Module.End F V) μ).restrict h) :=
  isNilpotent_restrict_maxGenEigenspace_sub_algebraMap T μ

/-- Axler writes the operator of 8.22(b) as {lit}`T − λI`. Because
{lit}`algebraMap F (End F V) λ = λ • 1`, the invariant subspace {lit}`G(λ, T)`
is invariant under {lit}`T − λ • 1` too. -/
theorem invariantUnder_sub_smul (T : V →ₗ[F] V) (μ : F) :
    InvariantUnder (T - μ • (1 : Module.End F V)) (maxGenEigenspace T μ) := by
  intro u hu
  have h1 : T u ∈ maxGenEigenspace T μ := invariantUnder_maxGenEigenspace T μ u hu
  have h2 : (μ • (1 : Module.End F V)) u ∈ maxGenEigenspace T μ := by
    rw [LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.smul_mem _ _ hu
  have := Submodule.sub_mem _ h1 h2
  rwa [← LinearMap.sub_apply] at this

/-! 8.22 (c) {lit}`V` is the direct sum of the generalized eigenspaces. This
combines the independence of the generalized eigenspaces (8.12,
{name}`Module.End.independent_maxGenEigenspace`) with the fact that they span
{lit}`V` (8.9, {name}`Module.End.iSup_maxGenEigenspace_eq_top`, valid over any
algebraically closed field). We package it as
{name}`DirectSum.IsInternal`. -/

theorem isInternal_maxGenEigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    DirectSum.IsInternal (fun μ : ℂ => maxGenEigenspace T μ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (independent_maxGenEigenspace T) (iSup_maxGenEigenspace_eq_top T)

/-! # Multiplicity of an Eigenvalue -/

/-! 8.23 Definition: multiplicity.

The *multiplicity* of an eigenvalue {lit}`λ` of {lit}`T` is the dimension of the
generalized eigenspace {lit}`G(λ, T)`, equivalently
{lit}`dim null(T − λI)^{dim V}` (using {lit}`G(λ, T) = null(T − λI)^{dim V}`,
see 8.20). Mathlib records this dimension as the multiplicity of {lit}`λ` as a
root of the (determinant) characteristic polynomial
{name}`LinearMap.charpoly`: {name}`LinearMap.finrank_maxGenEigenspace_eq`. -/

noncomputable def multiplicity {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (μ : ℂ) : ℕ :=
  finrank ℂ (maxGenEigenspace T μ)

theorem multiplicity_eq_rootMultiplicity {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (μ : ℂ) :
    multiplicity T μ = (LinearMap.charpoly T).rootMultiplicity μ := by
  rw [multiplicity, LinearMap.finrank_maxGenEigenspace_eq]

/-- The multiplicity equals {lit}`dim null(T − λI)^{dim V}` (second bullet of
8.23), because {lit}`G(λ, T) = null(T − λI)^{dim V}` (8.20). -/
theorem multiplicity_eq_finrank_ker_pow {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (μ : ℂ) :
    multiplicity T μ =
      finrank ℂ (ker ((T - μ • (1 : Module.End ℂ V)) ^ finrank ℂ V)) := by
  rw [multiplicity, Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.genEigenspace_nat]

/-! 8.24 Example: multiplicity of each eigenvalue of an operator.

Let {lit}`T ∈ ℒ(ℂ³)` be {lit}`T(z₁, z₂, z₃) = (6z₁ + 3z₂ + 4z₃, 6z₂ + 2z₃, 7z₃)`.
The eigenvalues of {lit}`T` are {lit}`6` and {lit}`7`, with
{lit}`G(6, T) = span((1,0,0), (0,1,0))` and {lit}`G(7, T) = span((10,2,1))`, so
the multiplicity of {lit}`6` is {lit}`2` and of {lit}`7` is {lit}`1`. We record
the operator and verify that {lit}`6` and {lit}`7` are eigenvalues (with
eigenvectors {lit}`(1,0,0)` and {lit}`(10,2,1)`); the full computation of the
generalized eigenspaces (hence of the multiplicities) is omitted, as it requires
the upper-triangular multiplicity count 8.31 which we defer below. -/

def T_8_24 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![6 * v 0 + 3 * v 1 + 4 * v 2, 6 * v 1 + 2 * v 2, 7 * v 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

example : HasEigenvalue T_8_24 6 := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := ![1, 0, 0])
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    funext i; fin_cases i <;> simp [T_8_24]
  · intro h; have := congrFun h 0; simp at this

example : HasEigenvalue T_8_24 7 := by
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := ![10, 2, 1])
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    funext i; fin_cases i <;> simp [T_8_24] <;> ring
  · intro h; have := congrFun h 2; simp at this

/-! 8.25 The sum of the multiplicities equals {lit}`dim V`.

For {lit}`F = ℂ`, summing over the distinct eigenvalues (the roots of the
characteristic polynomial) gives {lit}`dim V`. This follows from the generalized
eigenspace decomposition (8.22) and additivity of dimension over a direct sum
(3.94); we obtain it directly from the fact that the characteristic polynomial
splits over {lit}`ℂ` and has degree {lit}`dim V`. -/

theorem sum_multiplicity_eq_finrank {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    ∑ μ ∈ (LinearMap.charpoly T).roots.toFinset, multiplicity T μ = finrank ℂ V := by
  classical
  have hcard : Multiset.card (LinearMap.charpoly T).roots =
      (LinearMap.charpoly T).natDegree :=
    Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits (LinearMap.charpoly T))
  calc ∑ μ ∈ (LinearMap.charpoly T).roots.toFinset, multiplicity T μ
      = ∑ μ ∈ (LinearMap.charpoly T).roots.toFinset,
          (LinearMap.charpoly T).roots.count μ := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [multiplicity_eq_rootMultiplicity, Polynomial.count_roots]
    _ = Multiset.card (LinearMap.charpoly T).roots := Multiset.toFinset_sum_count_eq _
    _ = (LinearMap.charpoly T).natDegree := hcard
    _ = finrank ℂ V := LinearMap.charpoly_natDegree T

/-! # The Characteristic Polynomial -/

/-! 8.26 Definition: characteristic polynomial.

For {lit}`F = ℂ` and {lit}`T ∈ ℒ(V)` with distinct eigenvalues
{lit}`λ₁, …, λₘ` of multiplicities {lit}`d₁, …, dₘ`, the *characteristic
polynomial* of {lit}`T` is {lit}`(z − λ₁)^{d₁} ⋯ (z − λₘ)^{dₘ}`. We define it as
the product over the distinct eigenvalues (the roots of the mathlib
determinant-characteristic polynomial, which by 8.28(b) are exactly the
eigenvalues) and prove it agrees with mathlib's {name}`LinearMap.charpoly`. The
agreement — Axler's product-form equals the determinant form — is the content of
9.62; here it is immediate from
{name}`LinearMap.finrank_maxGenEigenspace_eq`. -/

noncomputable def charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) : Polynomial ℂ :=
  ∏ μ ∈ (LinearMap.charpoly T).roots.toFinset, (X - C μ) ^ multiplicity T μ

theorem charpoly_eq_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) : charpoly T = LinearMap.charpoly T := by
  classical
  have hcard : Multiset.card (LinearMap.charpoly T).roots =
      (LinearMap.charpoly T).natDegree :=
    Polynomial.splits_iff_card_roots.mp
      (IsAlgClosed.splits (LinearMap.charpoly T))
  rw [charpoly]
  rw [Finset.prod_congr rfl (fun μ _ => by rw [multiplicity_eq_rootMultiplicity])]
  rw [← Polynomial.prod_multiset_root_eq_finset_root]
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (LinearMap.charpoly_monic T) hcard

/-! 8.27 Example: the characteristic polynomial of the operator {lit}`T` of
Example 8.24. Because the eigenvalues of {lit}`T` are {lit}`6` (multiplicity
{lit}`2`) and {lit}`7` (multiplicity {lit}`1`), the characteristic polynomial of
{lit}`T` is {lit}`(z − 6)²(z − 7)`. This depends on the multiplicity computation
of 8.24, which we deferred, so we only record the statement here. -/

/-! 8.28 Degree and zeros of the characteristic polynomial.

(a) The characteristic polynomial of {lit}`T` has degree {lit}`dim V`; this
follows from 8.25. (b) The zeros of the characteristic polynomial are the
eigenvalues of {lit}`T`. Both follow from the identification of {name}`charpoly`
with {name}`LinearMap.charpoly` and mathlib's
{name}`LinearMap.charpoly_natDegree` and
{name}`Module.End.hasEigenvalue_iff_isRoot_charpoly`. -/

theorem charpoly_natDegree {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) : (charpoly T).natDegree = finrank ℂ V := by
  rw [charpoly_eq_charpoly, LinearMap.charpoly_natDegree]

theorem isRoot_charpoly_iff_hasEigenvalue {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (μ : ℂ) :
    (charpoly T).IsRoot μ ↔ HasEigenvalue T μ := by
  rw [charpoly_eq_charpoly, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]

/-! 8.29 Cayley–Hamilton theorem.

If {lit}`q` is the characteristic polynomial of {lit}`T` then {lit}`q(T) = 0`.
Axler's proof: on each {lit}`G(λₖ, T)` the factor {lit}`(T − λₖI)^{dₖ}` vanishes
(by 8.16, since the restriction is nilpotent), the factors commute, and 8.22
shows every vector is a sum of generalized eigenvectors. Since our
{name}`charpoly` equals {name}`LinearMap.charpoly`, the result is mathlib's
{name}`LinearMap.aeval_self_charpoly`. -/

theorem aeval_self_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) : aeval T (charpoly T) = 0 := by
  rw [charpoly_eq_charpoly]
  exact LinearMap.aeval_self_charpoly T

/-! 8.30 The characteristic polynomial is a polynomial multiple of the minimal
polynomial. This follows from the Cayley–Hamilton theorem (8.29) and 5.29. -/

theorem minpoly_dvd_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) : minpoly ℂ T ∣ charpoly T := by
  rw [charpoly_eq_charpoly]
  exact LinearMap.minpoly_dvd_charpoly T

/-- 8.31 Multiplicity of an eigenvalue equals the number of times it appears on
the diagonal of an upper-triangular matrix representing {lit}`T`. Following Axler:
the characteristic polynomial is basis-independent ({name}`LinearMap.charpoly_toMatrix`)
and, for an upper-triangular matrix, factors as {lit}`∏ₖ (z − Aₖₖ)`
({name}`Matrix.charpoly_of_upperTriangular`); so the multiplicity of {lit}`μ` (the
root multiplicity of the characteristic polynomial, 8.23) is the number of
diagonal entries equal to {lit}`μ`. -/
theorem multiplicity_eq_diagonal_count {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (μ : ℂ) {n : ℕ} {v : Fin n → V} (hv : IsBasis ℂ v)
    (hUT : (matrixOf hv hv T).BlockTriangular id) :
    multiplicity T μ = (Finset.univ.filter fun k => matrixOf hv hv T k k = μ).card := by
  classical
  rw [multiplicity_eq_rootMultiplicity,
    show LinearMap.charpoly T = (matrixOf hv hv T).charpoly from
      (LinearMap.charpoly_toMatrix T hv.toModuleBasis).symm,
    Matrix.charpoly_of_upperTriangular _ hUT, ← Polynomial.count_roots]
  have hroots : (∏ i : Fin n, (X - C (matrixOf hv hv T i i))).roots
      = Finset.univ.val.map fun i => matrixOf hv hv T i i := by
    rw [show (∏ i : Fin n, (X - C (matrixOf hv hv T i i)))
        = ((Finset.univ.val.map fun i => matrixOf hv hv T i i).map fun a => X - C a).prod from by
      rw [Multiset.map_map]; rfl]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  rw [hroots, Multiset.count_map]
  congr 1
  rw [Finset.filter_val]
  congr 1
  ext k
  simp [eq_comm]

/-! # Block Diagonal Matrices -/

/-! 8.35 Definition: block diagonal matrix. A *block diagonal matrix* is a
square matrix with square matrices {lit}`A₁, …, Aₘ` along the diagonal and zeros
elsewhere. In mathlib this is {name}`Matrix.blockDiagonal'`. We do not develop
the matrix-of-a-basis correspondence here, so we describe it only in prose. -/

/-! 8.36 Example: a block diagonal matrix — a {lit}`5`-by-{lit}`5` matrix built
from a {lit}`1`-by-{lit}`1` block {lit}`(4)`, a {lit}`2`-by-{lit}`2` block, and
another {lit}`2`-by-{lit}`2` block. Omitted (see 8.35). -/

/-! 8.37 Block diagonal matrix with upper-triangular blocks.

For {lit}`F = ℂ`, there is a basis with respect to which {lit}`T` has a block
diagonal matrix whose {lit}`k`-th block is upper triangular with {lit}`λₖ` on the
diagonal. The block-diagonal structure is the generalized eigenspace decomposition
{lit}`V = ⊕ G(λₖ, T)` ({name}`isInternal_maxGenEigenspace`); the content of each
block is the theorem below — {lit}`T` restricted to {lit}`G(μ, T)` has an
upper-triangular matrix with {lit}`μ` on the diagonal, since
{lit}`(T − μI)|_{G(μ,T)}` is nilpotent (8.18(c)). -/

/-- 8.37 (per generalized eigenspace). {lit}`T` restricted to {lit}`G(μ, T)` has, with
respect to a basis making `(T − μI)|_{G(μ,T)}` strictly upper triangular (8.18(c)),
an upper-triangular matrix with {lit}`μ` on the diagonal. -/
theorem exists_upperTriangular_restrict_maxGenEigenspace [Finite F V] (T : V →ₗ[F] V)
    (μ : F) (hT : Set.MapsTo T (maxGenEigenspace T μ) (maxGenEigenspace T μ)) :
    ∃ (n : ℕ) (e : Fin n → maxGenEigenspace T μ) (he : IsBasis F e),
      IsUpperTriangular (matrixOf he he (T.restrict hT)) ∧
      ∀ k, matrixOf he he (T.restrict hT) k k = μ := by
  classical
  set N := ((T : Module.End F V) - algebraMap F (Module.End F V) μ).restrict
    (mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes T μ) μ) with hNdef
  have hNnil : IsNilpotent N := isNilpotent_restrict_sub_algebraMap T μ
  have hvec : ∀ x : maxGenEigenspace T μ, (T.restrict hT) x = N x + μ • x := by
    intro x
    apply Subtype.ext
    simp only [LinearMap.restrict_coe_apply, hNdef, Submodule.coe_add, Submodule.coe_smul,
      LinearMap.sub_apply, Module.algebraMap_end_apply]
    abel
  by_cases hnt : Nontrivial (maxGenEigenspace T μ)
  · obtain ⟨n, e, he, hUT, hdiag⟩ := exists_strictUpperTriangular_of_nilpotent N hNnil
    refine ⟨n, e, he, ?_, fun k => ?_⟩
    · intro i j hji
      rw [matrixOf_apply, hvec (e j)]
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply]
      have hN0 : he.toModuleBasis.repr (N (e j)) i = 0 := by
        rw [← matrixOf_apply]; exact hUT i j hji
      have he0 : he.toModuleBasis.repr (e j) i = 0 := by
        rw [← IsBasis.toModuleBasis_apply he j, he.toModuleBasis.repr_self_apply,
          if_neg (ne_of_lt hji)]
      rw [hN0, he0, smul_zero, add_zero]
    · rw [matrixOf_apply, hvec (e k)]
      simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply]
      have hN0 : he.toModuleBasis.repr (N (e k)) k = 0 := by
        rw [← matrixOf_apply]; exact hdiag k
      have he1 : he.toModuleBasis.repr (e k) k = 1 := by
        rw [← IsBasis.toModuleBasis_apply he k, he.toModuleBasis.repr_self_apply, if_pos rfl]
      rw [hN0, he1, smul_eq_mul, mul_one, zero_add]
  · haveI : Subsingleton (maxGenEigenspace T μ) := not_nontrivial_iff_subsingleton.mp hnt
    refine ⟨0, Fin.elim0, ⟨linearIndependent_empty_type, ?_⟩, fun i j _ => i.elim0,
      fun k => k.elim0⟩
    show Submodule.span F (Set.range (Fin.elim0 : Fin 0 → maxGenEigenspace T μ)) = ⊤
    rw [Set.range_eq_empty, Submodule.span_empty, eq_top_iff]
    intro x _
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _

/-! 8.38 Example: block diagonal matrix via generalized eigenvectors — for the
operator of 8.24, with respect to the basis {lit}`(1,0,0), (0,1,0), (10,2,1)` of
generalized eigenvectors, {lit}`T` has the block diagonal matrix with blocks
{lit}`[[6,3],[0,6]]` and {lit}`(7)`. Omitted (see 8.37). -/

/-! # Exercises -/

/-- 8B.1 {lit}`T(w, z) = (−z, w)` on {lit}`ℂ²`: find the generalized
eigenspaces of the distinct eigenvalues. -/
def T_ex_8B_1 : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![-v 1, v 0]
  map_add' x y := by funext i; fin_cases i <;> simp; ring
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- The generalized eigenspaces of {lit}`T_ex_8B_1`, indexed by eigenvalue — to
be determined by the solver. -/
noncomputable def genEigenspaces_8B_1 : ℂ → Submodule ℂ (Fin 2 → ℂ) := sorry

theorem exercise_8B_1 (μ : ℂ) (hμ : HasEigenvalue T_ex_8B_1 μ) :
    maxGenEigenspace T_ex_8B_1 μ = genEigenspaces_8B_1 μ := by
  sorry

/-- 8B.2 If {lit}`T` is invertible and {lit}`λ ≠ 0`, then
{lit}`G(λ, T) = G(1/λ, T⁻¹)`. Here {lit}`S` is a two-sided inverse of
{lit}`T`. -/
theorem exercise_8B_2 (T S : V →ₗ[F] V) (hTS : T * S = 1) (hST : S * T = 1)
    (μ : F) (hμ : μ ≠ 0) :
    maxGenEigenspace T μ = maxGenEigenspace S μ⁻¹ := by
  sorry

/-- 8B.3 {lit}`T` and {lit}`S⁻¹TS` have the same eigenvalues with the same
multiplicities (here {lit}`S` has two-sided inverse {lit}`S'`). -/
theorem exercise_8B_3 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T S S' : V →ₗ[ℂ] V) (hSS' : S * S' = 1) (hS'S : S' * S = 1) (μ : ℂ) :
    (HasEigenvalue T μ ↔ HasEigenvalue (S' * T * S) μ) ∧
      multiplicity T μ = multiplicity (S' * T * S) μ := by
  sorry

/-- 8B.4 If {lit}`dim V ≥ 2` and {lit}`null T^{dim V - 2} ≠ null T^{dim V - 1}`,
then {lit}`T` has at most two distinct eigenvalues. Over {lit}`ℂ` the distinct
eigenvalues are the roots of the characteristic polynomial. -/
theorem exercise_8B_4 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (hdim : 2 ≤ finrank ℂ V)
    (h : ker (T ^ (finrank ℂ V - 2)) ≠ ker (T ^ (finrank ℂ V - 1))) :
    (LinearMap.charpoly T).roots.toFinset.card ≤ 2 := by
  sorry

/-- 8B.5 If {lit}`3` and {lit}`8` are eigenvalues of {lit}`T` and
{lit}`n = dim V`, then {lit}`V = null T^{n-2} ⊕ range T^{n-2}`. -/
theorem exercise_8B_5 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (h3 : HasEigenvalue T 3) (h8 : HasEigenvalue T 8) :
    IsCompl (ker (T ^ (finrank ℂ V - 2))) (range (T ^ (finrank ℂ V - 2))) := by
  sorry

/-- 8B.6 The exponent of {lit}`z − λ` in the minimal polynomial of {lit}`T` is the
smallest {lit}`m > 0` such that {lit}`(T − λI)^m = 0` on {lit}`G(λ, T)`. -/
theorem exercise_8B_6 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (μ : ℂ) (hμ : HasEigenvalue T μ) (m : ℕ) (hm : 0 < m) :
    (minpoly ℂ T).rootMultiplicity μ = m ↔
      (∀ v ∈ maxGenEigenspace T μ, ((T - μ • (1 : Module.End ℂ V)) ^ m) v = 0) ∧
        ∀ k, 0 < k → (∀ v ∈ maxGenEigenspace T μ,
          ((T - μ • (1 : Module.End ℂ V)) ^ k) v = 0) → m ≤ k := by
  sorry

/-- 8B.7 If {lit}`λ` is an eigenvalue of {lit}`T` with multiplicity {lit}`d`,
then {lit}`G(λ, T) = null(T − λI)^d`. When {lit}`d < dim V` this improves
8.20. -/
theorem exercise_8B_7 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (μ : ℂ) :
    maxGenEigenspace T μ =
      ker ((T - μ • (1 : Module.End ℂ V)) ^ multiplicity T μ) := by
  sorry

/-- 8B.8 {lit}`V = G(λ₁, T) ⊕ ⋯ ⊕ G(λₘ, T)` (the generalized eigenspaces span
{lit}`V`) iff the minimal polynomial of {lit}`T` is a product of linear factors.
(Over {lit}`ℂ` this is automatic; the exercise is interesting for {lit}`F = ℝ`.
We state the {lit}`ℝ` case, mirroring Exercise 8A.11.) -/
theorem exercise_8B_8 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    (T : V →ₗ[ℝ] V) :
    (⨆ μ : ℝ, maxGenEigenspace T μ) = ⊤ ↔
      ∃ (m : ℕ) (lam : Fin m → ℝ) (k : Fin m → ℕ),
        minpoly ℝ T = ∏ i, (X - C (lam i)) ^ (k i) := by
  sorry

/-- 8B.9 (F = ℂ) Every operator decomposes as {lit}`T = D + N` with {lit}`D`
diagonalizable (its eigenspaces span {lit}`V`), {lit}`N` nilpotent, and
{lit}`DN = ND`. -/
theorem exercise_8B_9 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) :
    ∃ D N : V →ₗ[ℂ] V, T = D + N ∧
      (⨆ μ : ℂ, Module.End.eigenspace D μ) = ⊤ ∧ IsNilpotent N ∧ D * N = N * D := by
  sorry

/-- 8B.10 On a complex inner product space, {lit}`∑ |λₖ|² ≤ ∑ ‖T eₖ‖²`, where the
{lit}`λₖ` are the eigenvalues with multiplicity (the roots of the characteristic
polynomial) and {lit}`e` is an orthonormal basis. -/
theorem exercise_8B_10 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E)
    (e : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E) :
    ((charpoly T).roots.map (fun μ => ‖μ‖ ^ 2)).sum ≤ ∑ i, ‖T (e i)‖ ^ 2 := by
  sorry

/-- 8B.11 An operator on {lit}`ℂ⁴` whose characteristic polynomial is
{lit}`(z − 7)²(z − 8)²`. -/
theorem exercise_8B_11 :
    ∃ T : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ),
      charpoly T = (X - C 7) ^ 2 * (X - C 8) ^ 2 := by
  sorry

/-- 8B.12 An operator on {lit}`ℂ⁴` with characteristic polynomial
{lit}`(z − 1)(z − 5)³` and minimal polynomial {lit}`(z − 1)(z − 5)²`. -/
theorem exercise_8B_12 :
    ∃ T : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ),
      charpoly T = (X - C 1) * (X - C 5) ^ 3 ∧
        minpoly ℂ T = (X - C 1) * (X - C 5) ^ 2 := by
  sorry

/-- 8B.13 An operator on {lit}`ℂ⁴` whose characteristic and minimal polynomials
both equal {lit}`z(z − 1)²(z − 3)`. -/
theorem exercise_8B_13 :
    ∃ T : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ),
      charpoly T = X * (X - C 1) ^ 2 * (X - C 3) ∧
        minpoly ℂ T = X * (X - C 1) ^ 2 * (X - C 3) := by
  sorry

/-- 8B.14 An operator on {lit}`ℂ⁴` with characteristic polynomial
{lit}`z(z − 1)²(z − 3)` and minimal polynomial {lit}`z(z − 1)(z − 3)`. -/
theorem exercise_8B_14 :
    ∃ T : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ),
      charpoly T = X * (X - C 1) ^ 2 * (X - C 3) ∧
        minpoly ℂ T = X * (X - C 1) * (X - C 3) := by
  sorry

/-- 8B.15 {lit}`T(z₁, z₂, z₃, z₄) = (0, z₁, z₂, z₃)` on {lit}`ℂ⁴`: find the
characteristic and minimal polynomials. -/
def T_ex_8B_15 : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![0, v 0, v 1, v 2]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- The characteristic polynomial of {lit}`T_ex_8B_15` — to be determined. -/
noncomputable def charpoly_8B_15 : Polynomial ℂ := sorry

/-- The minimal polynomial of {lit}`T_ex_8B_15` — to be determined. -/
noncomputable def minpoly_8B_15 : Polynomial ℂ := sorry

theorem exercise_8B_15 :
    charpoly T_ex_8B_15 = charpoly_8B_15 ∧
      minpoly ℂ T_ex_8B_15 = minpoly_8B_15 := by
  sorry

/-- 8B.16 {lit}`T(z₁, …, z₆) = (0, z₁, z₂, 0, z₄, 0)` on {lit}`ℂ⁶`: find the
characteristic and minimal polynomials. -/
def T_ex_8B_16 : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun v := ![0, v 0, v 1, 0, v 3, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- The characteristic polynomial of {lit}`T_ex_8B_16` — to be determined. -/
noncomputable def charpoly_8B_16 : Polynomial ℂ := sorry

/-- The minimal polynomial of {lit}`T_ex_8B_16` — to be determined. -/
noncomputable def minpoly_8B_16 : Polynomial ℂ := sorry

theorem exercise_8B_16 :
    charpoly T_ex_8B_16 = charpoly_8B_16 ∧
      minpoly ℂ T_ex_8B_16 = minpoly_8B_16 := by
  sorry

/-- 8B.17 (F = ℂ) If {lit}`P² = P` then the characteristic polynomial of
{lit}`P` is {lit}`zᵐ(z − 1)ⁿ` with {lit}`m = dim null P` and
{lit}`n = dim range P`. -/
theorem exercise_8B_17 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (P : V →ₗ[ℂ] V) (hP : P * P = P) :
    charpoly P = X ^ (finrank ℂ (ker P)) * (X - C 1) ^ (finrank ℂ (range P)) := by
  sorry

/-- 8B.18 For an eigenvalue {lit}`λ` of {lit}`T`, four numbers coincide. Here we
state the equality of (a) the exponent of {lit}`z − λ` in the minimal polynomial
with (c) the smallest {lit}`m` at which {lit}`null(T − λI)^m` stabilizes and (d) the
smallest {lit}`m` at which {lit}`range(T − λI)^m` stabilizes. (Characterization (b),
the nilpotency index on {lit}`G(λ, T)`, is Exercise 8B.6.) -/
theorem exercise_8B_18 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (μ : ℂ) (m : ℕ) (hm : 0 < m) :
    (minpoly ℂ T).rootMultiplicity μ = m ↔
      (ker ((T - μ • (1 : Module.End ℂ V)) ^ m) =
          ker ((T - μ • (1 : Module.End ℂ V)) ^ (m + 1)) ∧
        (∀ k, 0 < k → k < m → ker ((T - μ • (1 : Module.End ℂ V)) ^ k) ≠
          ker ((T - μ • (1 : Module.End ℂ V)) ^ (k + 1))) ∧
        range ((T - μ • (1 : Module.End ℂ V)) ^ m) =
          range ((T - μ • (1 : Module.End ℂ V)) ^ (m + 1)) ∧
        (∀ k, 0 < k → k < m → range ((T - μ • (1 : Module.End ℂ V)) ^ k) ≠
          range ((T - μ • (1 : Module.End ℂ V)) ^ (k + 1)))) := by
  sorry

/-- 8B.19 For a unitary {lit}`S` over {lit}`ℂ`, the constant term of the
characteristic polynomial has absolute value 1. -/
theorem exercise_8B_19 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (S : E →ₗ[ℂ] E)
    (hS : LinearMap.adjoint S ∘ₗ S = 1 ∧ S ∘ₗ LinearMap.adjoint S = 1) :
    ‖(charpoly S).coeff 0‖ = 1 := by
  sorry

/-- 8B.20 If {lit}`V = V₁ ⊕ ⋯ ⊕ Vₘ` with each {lit}`Vₖ` invariant under {lit}`T`,
then {lit}`charpoly T = ∏ charpoly (T|Vₖ)`. -/
theorem exercise_8B_20 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) {m : ℕ} (Vs : Fin m → Submodule ℂ V)
    (hne : ∀ k, Vs k ≠ ⊥) (hindep : iSupIndep Vs) (hsup : ⨆ k, Vs k = ⊤)
    (hinv : ∀ k, ∀ v ∈ Vs k, T v ∈ Vs k) :
    charpoly T = ∏ k, charpoly (T.restrict (hinv k)) := by
  sorry

/-- 8B.21 If {lit}`p, q ∈ 𝒫(ℂ)` are monic with the same zeros and {lit}`q` is a
polynomial multiple of {lit}`p`, then there is an operator on {lit}`ℂ^{deg q}`
with characteristic polynomial {lit}`q` and minimal polynomial {lit}`p`. -/
theorem exercise_8B_21 (p q : Polynomial ℂ) (hp : p.Monic) (hq : q.Monic)
    (hzeros : p.roots.toFinset = q.roots.toFinset) (hdvd : p ∣ q) :
    ∃ T : (Fin q.natDegree → ℂ) →ₗ[ℂ] (Fin q.natDegree → ℂ),
      charpoly T = q ∧ minpoly ℂ T = p := by
  sorry

/-- 8B.22 The product of two block-diagonal matrices (matching block sizes) is the
block-diagonal matrix of the blockwise products. -/
theorem exercise_8B_22 {m p : ℕ} (A B : Fin m → Matrix (Fin p) (Fin p) ℂ) :
    Matrix.blockDiagonal A * Matrix.blockDiagonal B =
      Matrix.blockDiagonal (fun k => A k * B k) := by
  sorry

open LADR.Section_1B (Complexification exercise_1B_8) in
open LADR.Section_3B (complexification_map) in
/-- 8B.23 (a) For {lit}`F = ℝ` and {lit}`λ ∈ ℂ`, the complexification {lit}`T_ℂ`
(Exercise 3B.33) satisfies {lit}`u + iv ∈ G(λ, T_ℂ) ↔ u − iv ∈ G(λ̄, T_ℂ)`. In the
{lit}`V × V` model, {lit}`u + iv = (u, v)` and {lit}`u − iv = (u, −v)`. -/
theorem exercise_8B_23a {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    (T : V →ₗ[ℝ] V) (μ : ℂ) (u v : V) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    ((u, v) ∈ maxGenEigenspace (complexification_map T) μ ↔
      (u, -v) ∈ maxGenEigenspace (complexification_map T) (starRingEnd ℂ μ)) := by
  sorry

/-- 8B.23 (c),(d) If {lit}`V` is a real vector space of odd dimension, then
{lit}`T` has a (real) eigenvalue — obtained here via the complexification and the
multiplicity count (an alternative proof of 5.34). -/
theorem exercise_8B_23c {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    (T : V →ₗ[ℝ] V) (hodd : Odd (finrank ℝ V)) :
    ∃ γ : ℝ, HasEigenvalue T γ := by
  sorry

end LADR.Section_8B
