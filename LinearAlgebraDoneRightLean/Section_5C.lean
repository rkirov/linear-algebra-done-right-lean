import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import Mathlib.Tactic.TFAE
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_5A
import LinearAlgebraDoneRightLean.Section_5B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5C: Upper-Triangular Matrices
-/

namespace LADR.Section_5C

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis isBasis_stdBasis isBasis_stdBasis_repr)
open LADR.Section_3C (matrixOf matrixOf_apply matrixOf_spec)
open LADR.Section_3D (IsInvertible)
open Module.End (HasEigenvalue)
open LADR.Section_5A (InvariantUnder aeval_mul_eq_comp
  range_aeval_invariant exercise_5A_38_quotient_op)
open LADR.Section_5B (aeval_eq_zero_iff_minpoly_dvd isEigenvalue_iff_isRoot
  aeval_restrict_coe)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

universe u

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! 5.35 Definition: matrix of an operator, {lit}`ℳ(T)`.

An operator {lit}`T ∈ ℒ(V)` gets a *square* matrix with respect to a single
basis {lit}`v₁, …, vₙ` of {lit}`V`: this is Section 3C's
{name}`LADR.Section_3C.matrixOf` with the same basis used twice,
{lit}`matrixOf hv hv T`. -/

noncomputable example {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) : Matrix (Fin n) (Fin n) F :=
  matrixOf hv hv T

/-! 5.36 Example: {lit}`T(x, y, z) = (2x + y, 5y + 3z, 8z)` has matrix
{lit}`[[2,1,0],[0,5,3],[0,0,8]]` with respect to the standard basis. -/

noncomputable def T_5_36 : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun x := ![2 * x 0 + x 1, 5 * x 1 + 3 * x 2, 8 * x 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

theorem matrixOf_T_5_36 :
    matrixOf (isBasis_stdBasis (F := F) 3) (isBasis_stdBasis (F := F) 3)
      T_5_36 = !![2, 1, 0; 0, 5, 3; 0, 0, 8] := by
  ext j k
  rw [matrixOf_apply, isBasis_stdBasis_repr]
  fin_cases j <;> fin_cases k <;> simp [T_5_36]

/-! 5.37 Definition: diagonal of a square matrix — mathlib's
{name}`Matrix.diag`. -/

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (k : Fin n) :
    A.diag k = A k k := rfl

/-! 5.38 Definition: upper-triangular matrix -/

/-- A square matrix is *upper triangular* if all entries below the diagonal
are {lit}`0`. (mathlib's general notion is {name}`Matrix.BlockTriangular`
with respect to {lit}`id`.) -/
def IsUpperTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ j k, k < j → A j k = 0

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    IsUpperTriangular A ↔ A.BlockTriangular id :=
  ⟨fun h _ _ hij => h _ _ hij, fun h _ _ hij => h hij⟩

/-! 5.39 Conditions for upper-triangular matrix.

For a basis {lit}`v₁, …, vₙ` of {lit}`V`, the matrix of {lit}`T` is upper
triangular iff {lit}`span(v₁, …, vₖ)` is invariant under {lit}`T` for each
{lit}`k`, iff {lit}`T vₖ ∈ span(v₁, …, vₖ)` for each {lit}`k`. -/

theorem tfae_upperTriangular {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) :
    [IsUpperTriangular (matrixOf hv hv T),
      ∀ k : Fin n, InvariantUnder T (Submodule.span F (v '' {i | i ≤ k})),
      ∀ k : Fin n, T (v k) ∈ Submodule.span F (v '' {i | i ≤ k})].TFAE := by
  tfae_have 1 → 2 := by
    intro hA k x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      -- {lit}`T vⱼ = ∑ᵢ A_{i,j} vᵢ`, and the entries with {lit}`i > j`
      -- vanish, so {lit}`T vⱼ ∈ span(v₁, …, vⱼ) ⊆ span(v₁, …, vₖ)`.
      rw [matrixOf_spec hv hv T j]
      apply Submodule.sum_mem
      intro i _
      by_cases hij : i ≤ j
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i, le_trans hij hj, rfl⟩)
      · rw [hA i j (lt_of_not_ge hij), zero_smul]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy
  tfae_have 2 → 3 := fun h k =>
    h k (v k) (Submodule.subset_span ⟨k, le_refl k, rfl⟩)
  tfae_have 3 → 1 := by
    intro h j k hkj
    -- The coefficients of {lit}`T vₖ` are supported on {lit}`{i : i ≤ k}`.
    rw [matrixOf_apply]
    have himg : v '' {i | i ≤ k} = ⇑hv.toModuleBasis '' {i | i ≤ k} :=
      Set.image_congr fun i _ => (hv.toModuleBasis_apply i).symm
    have hmem := h k
    rw [himg] at hmem
    have hsupp := (Module.Basis.mem_span_image hv.toModuleBasis).mp hmem
    by_contra hne
    exact absurd (hsupp (Finsupp.mem_support_iff.mpr hne)) (not_le.mpr hkj)
  tfae_finish

/-! 5.40 -/

/-- The key step in 5.40 and 5.41: {lit}`T − λₖI` maps
{lit}`span(v₁, …, vₖ)` into {lit}`span(v₁, …, v_{k−1})`. -/
private lemma sub_diag_maps_into {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hA : IsUpperTriangular (matrixOf hv hv T)) (k : Fin n) :
    ∀ x ∈ Submodule.span F (v '' {i | i ≤ k}),
      (T - matrixOf hv hv T k k • (LinearMap.id : V →ₗ[F] V)) x ∈
        Submodule.span F (v '' {i | i < k}) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' : j ≤ k := hj
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rcases eq_or_lt_of_le hj' with rfl | hjk
    · -- {lit}`(T − λⱼI)vⱼ = ∑_{i<j} A_{i,j} vᵢ`: the diagonal cancels.
      rw [matrixOf_spec hv hv T j]
      have hsplit : (∑ i, matrixOf hv hv T i j • v i) =
          matrixOf hv hv T j j • v j +
            ∑ i ∈ Finset.univ.erase j, matrixOf hv hv T i j • v i :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
      rw [hsplit, add_sub_cancel_left]
      apply Submodule.sum_mem
      intro i hi
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with hlt | hgt
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hlt, rfl⟩)
      · rw [hA i j hgt, zero_smul]
        exact Submodule.zero_mem _
    · -- For {lit}`j < k` both terms already lie in
      -- {lit}`span(v₁, …, v_{k−1})`.
      apply Submodule.sub_mem
      · have h3 := (tfae_upperTriangular hv T).out 0 2
        have hTj := h3.mp hA j
        refine Submodule.span_mono ?_ hTj
        rintro y ⟨i, hi, rfl⟩
        exact ⟨i, lt_of_le_of_lt hi hjk, rfl⟩
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hjk, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy

private lemma aeval_X_sub_C_apply (T : V →ₗ[F] V) (a : F) (x : V) :
    aeval T (Polynomial.X - Polynomial.C a) x =
      (T - a • (LinearMap.id : V →ₗ[F] V)) x := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
    LinearMap.sub_apply, Module.algebraMap_end_apply, LinearMap.smul_apply,
    LinearMap.id_apply]

theorem aeval_prod_diag_eq_zero {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hA : IsUpperTriangular (matrixOf hv hv T)) :
    aeval T (∏ k, (Polynomial.X -
      Polynomial.C (matrixOf hv hv T k k))) = 0 := by
  -- Main claim: the partial products annihilate the partial spans.
  have hmain : ∀ m : ℕ, ∀ k : Fin n, (k : ℕ) + 1 ≤ m →
      ∀ x ∈ Submodule.span F (v '' {i | i ≤ k}),
        aeval T (∏ i ∈ Finset.univ.filter (· ≤ k),
          (Polynomial.X - Polynomial.C (matrixOf hv hv T i i))) x = 0 := by
    intro m
    induction m with
    | zero => intro k hk; omega
    | succ m ih =>
      intro k hk x hx
      -- Pull out the factor {lit}`(z − λₖ)` from the product.
      have hk_mem : k ∈ Finset.univ.filter (· ≤ k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ k, le_refl k⟩
      have hsplit : (∏ i ∈ Finset.univ.filter (· ≤ k),
          (Polynomial.X - Polynomial.C (matrixOf hv hv T i i))) =
          (∏ i ∈ (Finset.univ.filter (· ≤ k)).erase k,
            (Polynomial.X - Polynomial.C (matrixOf hv hv T i i))) *
            (Polynomial.X - Polynomial.C (matrixOf hv hv T k k)) :=
        (Finset.prod_erase_mul _ _ hk_mem).symm
      rw [hsplit, aeval_mul_eq_comp, LinearMap.comp_apply,
        aeval_X_sub_C_apply]
      have hstep := sub_diag_maps_into hv T hA k x hx
      -- The image lands in {lit}`span(v₁, …, v_{k−1})`.
      rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
      · -- {lit}`k = 0`: the image is in {lit}`span ∅ = {0}`.
        have hempty : {i : Fin n | i < k} = ∅ := by
          ext i
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
            not_lt, Fin.le_def]
          omega
        rw [hempty, Set.image_empty, Submodule.span_empty,
          Submodule.mem_bot] at hstep
        rw [hstep, map_zero]
      · -- {lit}`k > 0`: erase {lit}`k` to get the predecessor's product.
        set k' : Fin n := ⟨(k : ℕ) - 1, by omega⟩ with hk'_def
        have hlt_iff : ∀ i : Fin n, i < k ↔ i ≤ k' := by
          intro i
          rw [Fin.lt_def, Fin.le_def]
          simp only [hk'_def]
          omega
        have hset : {i : Fin n | i < k} = {i | i ≤ k'} := by
          ext i
          exact hlt_iff i
        have hfilter : (Finset.univ.filter (· ≤ k)).erase k =
            Finset.univ.filter (· ≤ k') := by
          ext i
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · rintro ⟨hne, hle⟩
            exact (hlt_iff i).mp (lt_of_le_of_ne hle hne)
          · intro hle
            have := (hlt_iff i).mpr hle
            exact ⟨ne_of_lt this, le_of_lt this⟩
        rw [hset] at hstep
        rw [hfilter]
        exact ih k' (by simp only [hk'_def]; omega) _ hstep
  -- Now apply the claim to all of {lit}`V`.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- {lit}`n = 0`: the basis is empty, so {lit}`V = {0}`.
    subst hn0
    apply LinearMap.ext
    intro x
    have hx : x ∈ Submodule.span F (Set.range v) := by
      rw [hv.2]
      exact Submodule.mem_top
    rw [Set.range_eq_empty v, Submodule.span_empty, Submodule.mem_bot] at hx
    rw [hx, map_zero, LinearMap.zero_apply]
  · apply LinearMap.ext
    intro x
    set klast : Fin n := ⟨n - 1, by omega⟩ with hklast_def
    have huniv : Finset.univ.filter (· ≤ klast) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [Fin.le_def]
      simp only [hklast_def]
      omega
    have hx : x ∈ Submodule.span F (v '' {i | i ≤ klast}) := by
      have hall : {i : Fin n | i ≤ klast} = Set.univ := by
        ext i
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        rw [Fin.le_def]
        simp only [hklast_def]
        omega
      rw [hall, Set.image_univ, hv.2]
      exact Submodule.mem_top
    have := hmain n klast (by simp only [hklast_def]; omega) x hx
    rw [huniv] at this
    rw [this, LinearMap.zero_apply]

/-! 5.41 Determination of eigenvalues from an upper-triangular matrix: the
eigenvalues of {lit}`T` are precisely the diagonal entries. -/

theorem isEigenvalue_iff_diag [Finite F V] {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (T : V →ₗ[F] V)
    (hA : IsUpperTriangular (matrixOf hv hv T)) (γ : F) :
    HasEigenvalue T γ ↔ ∃ k, matrixOf hv hv T k k = γ := by
  constructor
  · -- An eigenvalue is a zero of the minimal polynomial (5.27), which
    -- divides {lit}`∏ (z − λₖ)` (5.40 + 5.29), so it equals some {lit}`λₖ`.
    intro hγ
    have hroot := (isEigenvalue_iff_isRoot T γ).mp hγ
    have hdvd : minpoly F T ∣ ∏ k, (Polynomial.X -
        Polynomial.C (matrixOf hv hv T k k)) :=
      (aeval_eq_zero_iff_minpoly_dvd T _).mp (aeval_prod_diag_eq_zero hv T hA)
    have hroot' : (∏ k, (Polynomial.X -
        Polynomial.C (matrixOf hv hv T k k))).IsRoot γ :=
      hroot.dvd hdvd
    rw [Polynomial.IsRoot.def, Polynomial.eval_prod] at hroot'
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hroot'
    refine ⟨k, ?_⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hk
    exact hk.symm
  · -- A diagonal entry {lit}`γₖ` is an eigenvalue: {lit}`T − γₖI` maps the
    -- {lit}`(k+1)`-dimensional {lit}`span(v₁, …, vₖ)` into the
    -- {lit}`k`-dimensional {lit}`span(v₁, …, v_{k−1})`, so it is not
    -- injective there (3.22).
    rintro ⟨k, rfl⟩
    set Uk := Submodule.span F (v '' {i | i ≤ k}) with hUk_def
    set Uk' := Submodule.span F (v '' {i | i < k}) with hUk'_def
    -- Dimensions: spans of {lit}`k+1` resp. {lit}`k` linearly independent
    -- vectors.
    have himg_le : v '' {i | i ≤ k} =
        Set.range (v ∘ Fin.castLE (show (k : ℕ) + 1 ≤ n by omega)) := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨(j : ℕ), by have := Fin.le_def.mp hj; omega⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨Fin.castLE _ i, ?_, rfl⟩
        rw [Set.mem_setOf_eq, Fin.le_def]
        simp only [Fin.val_castLE]
        omega
    have himg_lt : v '' {i | i < k} =
        Set.range (v ∘ Fin.castLE (show (k : ℕ) ≤ n by omega)) := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨(j : ℕ), Fin.lt_def.mp hj⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨Fin.castLE _ i, ?_, rfl⟩
        rw [Set.mem_setOf_eq, Fin.lt_def]
        simp only [Fin.val_castLE]
        omega
    have hli := hv.1
    have hrank_le : finrank F Uk = (k : ℕ) + 1 := by
      rw [hUk_def, himg_le, finrank_span_eq_card
        (hli.comp _ (Fin.castLE_injective _)), Fintype.card_fin]
    have hrank_lt : finrank F Uk' = (k : ℕ) := by
      rw [hUk'_def, himg_lt, finrank_span_eq_card
        (hli.comp _ (Fin.castLE_injective _)), Fintype.card_fin]
    -- The restricted map {lit}`Uk → Uk'` is not injective.
    set f := T - matrixOf hv hv T k k • (LinearMap.id : V →ₗ[F] V) with hf_def
    have hmaps := sub_diag_maps_into hv T hA k
    set g : Uk →ₗ[F] Uk' := LinearMap.codRestrict Uk' (f.domRestrict Uk)
      (fun x => hmaps (x : V) x.2) with hg_def
    have hginj : ¬ Function.Injective g := by
      apply LADR.Section_3B.not_injective_of_finrank_lt
      rw [hrank_le, hrank_lt]
      omega
    rw [LADR.Section_3B.injective_iff_ker_eq_bot] at hginj
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hginj
    rw [LinearMap.mem_ker] at hx_mem
    have hfx : f (x : V) = 0 := by
      have := congrArg Subtype.val hx_mem
      exact this
    refine Module.End.hasEigenvalue_iff_exists.mpr
      ⟨(x : V), fun h => hx_ne (Subtype.ext h), ?_⟩
    rw [hf_def] at hfx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hfx
    exact hfx

/-! 5.42 Example: the eigenvalues of the operator of 5.36 are exactly the
diagonal entries {lit}`2, 5, 8` of its upper-triangular matrix. -/

example : ∀ γ : F, HasEigenvalue (T_5_36 (F := F)) γ ↔
    γ = 2 ∨ γ = 5 ∨ γ = 8 := by
  intro γ
  have hA : IsUpperTriangular
      (matrixOf (isBasis_stdBasis (F := F) 3) (isBasis_stdBasis 3) T_5_36) := by
    rw [matrixOf_T_5_36]
    intro j k hkj
    fin_cases j <;> fin_cases k <;> simp_all [Fin.lt_def]
  rw [isEigenvalue_iff_diag (isBasis_stdBasis 3) T_5_36 hA γ,
    matrixOf_T_5_36]
  constructor
  · rintro ⟨k, hk⟩
    fin_cases k <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp⟩

/-! 5.43 Example: whether {lit}`T` has an upper-triangular matrix can depend on
{lit}`F`. The operator on {lit}`ℝ⁴` with matrix
{lit}`[[0,−1,0,0],[1,0,0,0],[2,0,3,0],[0,0,1,3]]` has minimal polynomial
{lit}`(z² + 1)(z − 3)²`, which factors into linear factors over {lit}`ℂ` but
not over {lit}`ℝ`; by 5.44 it is upper-triangularizable over {lit}`ℂ` only.

We formalize the minimal-polynomial computation, which Axler omits. The strategy
(see {lit}`Example_5_43.minpoly_eq` below):
* {lit}`p A = 0` for {lit}`p = (z²+1)(z−3)²` — a finite computation in
  {lit}`Mat₄(ℝ)` — so {lit}`minpoly ∣ p` by {lit}`minpoly.dvd`;
* neither maximal proper monic divisor {lit}`(z²+1)(z−3)` nor {lit}`(z−3)²`
  annihilates {lit}`A`, so {lit}`minpoly` is not a proper divisor of {lit}`p`;
* therefore {lit}`minpoly A = p`.

The blocks {lit}`[[0,−1],[1,0]]` and {lit}`[[3,0],[1,3]]` (a rotation and a
Jordan block) contribute the factors {lit}`z²+1` and {lit}`(z−3)²`. -/

namespace Example_5_43

open Polynomial Matrix

/-- The operator of 5.43, as a matrix on {lit}`ℝ⁴`. -/
noncomputable def A : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, -1, 0, 0;
     1,  0, 0, 0;
     2,  0, 3, 0;
     0,  0, 1, 3]

/-- The irreducible quadratic factor {lit}`z² + 1`. -/
noncomputable def u1 : Polynomial ℝ := X ^ 2 + 1
/-- The linear factor {lit}`z − 3`. -/
noncomputable def u2 : Polynomial ℝ := X - C 3
/-- The candidate minimal polynomial {lit}`(z² + 1)(z − 3)²`. -/
noncomputable def p : Polynomial ℝ := u1 * u2 ^ 2

/-- {lit}`z² + 1` is irreducible over {lit}`ℝ` (degree two, no real root), hence
prime. -/
private theorem u1_prime : Prime u1 := by
  have hirr : Irreducible u1 := by
    apply irreducible_of_degree_le_three_of_not_isRoot (p := u1)
    · have h : u1.natDegree = 2 := by unfold u1; compute_degree!
      rw [h]; decide
    · intro x hx
      simp only [u1, IsRoot.def, eval_add, eval_pow, eval_X, eval_one] at hx
      nlinarith [sq_nonneg x]
  exact hirr.prime

private theorem u2_prime : Prime u2 := prime_X_sub_C 3

private theorem p_monic : p.Monic := by unfold p u1 u2; monicity!

/-- {lit}`aeval A` sends each factor of {lit}`p` to the matching matrix. -/
private theorem aeval_p : aeval A p = (A ^ 2 + 1) * (A - (3 : ℝ) • 1) ^ 2 := by
  simp [p, u1, u2, map_mul, map_pow, map_add, map_sub, map_one, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one]

/-- {lit}`p` annihilates {lit}`A`: a finite entrywise computation in
{lit}`Mat₄(ℝ)`. -/
private theorem aeval_p_eq_zero : aeval A p = 0 := by
  rw [aeval_p]; ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] <;> norm_num

/-- The maximal proper divisor {lit}`(z²+1)(z−3)` does *not* annihilate
{lit}`A` (witnessed by entry {lit}`(3,2) = 10`). -/
private theorem aeval_q1_ne_zero : aeval A (u1 * u2) ≠ 0 := by
  have e : aeval A (u1 * u2) = (A ^ 2 + 1) * (A - (3 : ℝ) • 1) := by
    simp [u1, u2, map_mul, map_pow, map_add, map_sub, map_one, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one]
  rw [e]; intro h; have := congrFun (congrFun h 3) 2
  simp [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply] at this; norm_num at this

/-- The maximal proper divisor {lit}`(z−3)²` does *not* annihilate {lit}`A`
(witnessed by entry {lit}`(0,0) = 8`). -/
private theorem aeval_q2_ne_zero : aeval A (u2 ^ 2) ≠ 0 := by
  have e : aeval A (u2 ^ 2) = (A - (3 : ℝ) • 1) ^ 2 := by
    simp [u2, map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
  rw [e]; intro h; have := congrFun (congrFun h 0) 0
  simp [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply] at this; norm_num at this

/-- **5.43.** The minimal polynomial of the operator is {lit}`(z² + 1)(z − 3)²`.
Since {lit}`z² + 1` is irreducible over {lit}`ℝ`, this does not split into linear
factors over {lit}`ℝ`; by 5.44 the operator is therefore *not*
upper-triangularizable over {lit}`ℝ`, though it is over {lit}`ℂ` (where
{lit}`z² + 1 = (z − i)(z + i)`). -/
theorem minpoly_eq : minpoly ℝ A = p := by
  have hint : IsIntegral ℝ A := Matrix.isIntegral A
  -- `minpoly ∣ q` forces `q` to annihilate `A`.
  have hdvd_imp : ∀ q : Polynomial ℝ, minpoly ℝ A ∣ q → aeval A q = 0 := by
    rintro q ⟨r, rfl⟩; rw [map_mul, minpoly.aeval, zero_mul]
  have hndvd_q1 : ¬minpoly ℝ A ∣ u1 * u2 := fun h => aeval_q1_ne_zero (hdvd_imp _ h)
  have hndvd_q2 : ¬minpoly ℝ A ∣ u2 ^ 2 := fun h => aeval_q2_ne_zero (hdvd_imp _ h)
  have hpdvd : minpoly ℝ A ∣ u1 * u2 ^ 2 := by
    have h := minpoly.dvd ℝ A aeval_p_eq_zero; simpa [p] using h
  -- `z² + 1` must divide `minpoly`; otherwise it is coprime to `minpoly`,
  -- forcing `minpoly ∣ (z−3)²`, contradicting `aeval_q2_ne_zero`.
  have hu1_dvd : u1 ∣ minpoly ℝ A := by
    by_contra h1
    exact hndvd_q2 ((u1_prime.coprime_iff_not_dvd.mpr h1).symm.dvd_of_dvd_mul_left hpdvd)
  obtain ⟨m, hm⟩ := hu1_dvd
  have hm_dvd : m ∣ u2 ^ 2 := (mul_dvd_mul_iff_left u1_prime.ne_zero).mp (hm ▸ hpdvd)
  have hm_ndvd : ¬m ∣ u2 := fun h => hndvd_q1 (hm ▸ mul_dvd_mul_left u1 h)
  -- divisors of the prime power `(z−3)²` are `1, z−3, (z−3)²`; the first two
  -- divide `z−3`, so `m` is associate to `(z−3)²`, giving `p ∣ minpoly`.
  obtain ⟨i, _, hassoc⟩ := (dvd_prime_pow u2_prime 2).mp hm_dvd
  have hpm : p ∣ minpoly ℝ A := by
    interval_cases i
    · simp only [pow_zero] at hassoc
      exact absurd (hassoc.dvd.trans (one_dvd u2)) hm_ndvd
    · simp only [pow_one] at hassoc
      exact absurd hassoc.dvd hm_ndvd
    · rw [hm, p]; exact mul_dvd_mul_left u1 hassoc.symm.dvd
  exact eq_of_monic_of_associated (minpoly.monic hint) p_monic
    (associated_of_dvd_dvd (minpoly.dvd ℝ A aeval_p_eq_zero) hpm)

end Example_5_43

/-! Hint toward 5.44: {lit}`Example_5_43.minpoly_eq` is exactly the input 5.44
needs. Once 5.44 is available as a theorem — {lit}`T` has an upper-triangular
matrix over {lit}`F` iff {lit}`minpoly F T` is a product of linear factors
{lit}`(z − λ₁)⋯(z − λₘ)`, {lit}`λᵢ ∈ F` — the example follows by feeding it this
minimal polynomial: over {lit}`ℝ` the factor {lit}`z² + 1` is irreducible (no
real root), so {lit}`minpoly` is not a product of linear factors and 5.44 denies
an upper-triangular matrix; over {lit}`ℂ`, {lit}`z² + 1 = (z − I)(z + I)` splits,
so 5.44 grants one. Formalizing that step needs 5.44 itself (currently the
doc-comment below) and the {lit}`ℂ`-vs-{lit}`ℝ` splitting of {lit}`z² + 1`. -/

/-! 5.44 Necessary and sufficient condition to have an upper-triangular
matrix: {lit}`T` has an upper-triangular matrix with respect to some basis
of {lit}`V` iff the minimal polynomial of {lit}`T` equals
{lit}`(z − λ₁)⋯(z − λₘ)` for some {lit}`λ₁, …, λₘ ∈ F`. -/

/-- A monic polynomial that splits is the (finite, indexed) product of its
linear factors. -/
private lemma monic_splits_eq_prod_fin {p : Polynomial F} (hmonic : p.Monic)
    (hsplits : p.Splits) :
    ∃ (m : ℕ) (γ : Fin m → F),
      p = ∏ k, (Polynomial.X - Polynomial.C (γ k)) ∧ m = p.natDegree := by
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := p) (Polynomial.splits_iff_card_roots.mp hsplits)
  rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul] at h
  refine ⟨p.roots.toList.length, fun k => p.roots.toList.get k, ?_, ?_⟩
  · conv_lhs => rw [← h]
    conv_lhs => rw [show p.roots = ↑p.roots.toList from
      (Multiset.coe_toList p.roots).symm]
    rw [Multiset.map_coe, Multiset.prod_coe]
    rw [show p.roots.toList.map (fun a => Polynomial.X - Polynomial.C a) =
      List.ofFn ((fun a => Polynomial.X - Polynomial.C a) ∘
        p.roots.toList.get) by
        rw [← List.map_ofFn, List.ofFn_get]]
    rw [List.prod_ofFn]
    rfl
  · rw [Multiset.length_toList]
    exact (Polynomial.splits_iff_card_roots.mp hsplits)

/-- The inductive heart of 5.44: if the minimal polynomial of {lit}`T` is a
product of {lit}`m` monic linear factors, then {lit}`V` has a basis with
respect to which {lit}`T` is upper triangular. Strong induction on
{lit}`m`, restricting to {lit}`U = range(T − λₘI)`. -/
private lemma exists_upperTriangular_of_minpoly_prod :
    ∀ (m : ℕ) (W : Type u) (_ : AddCommGroup W),
      ∀ (_ : Module F W) (_ : Module.Finite F W) (T : W →ₗ[F] W)
        (γ : Fin m → F),
        minpoly F T = (∏ k, (Polynomial.X - Polynomial.C (γ k))) →
        ∃ (n : ℕ) (w : Fin n → W) (hw : IsBasis F w),
          IsUpperTriangular (matrixOf hw hw T) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro W _ _ _ T γ hfact
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- Base case: the minimal polynomial is the empty product {lit}`1`,
      -- which forces {lit}`W = {0}`; the empty basis works.
      simp only [Finset.univ_eq_empty, Finset.prod_empty] at hfact
      have hid : (1 : W →ₗ[F] W) = 0 := by
        have h1 := minpoly.aeval F T
        rwa [hfact, map_one] at h1
      have hsub : Subsingleton W := by
        constructor
        intro a b
        have ha := LinearMap.congr_fun hid a
        have hb := LinearMap.congr_fun hid b
        rw [Module.End.one_apply, LinearMap.zero_apply] at ha hb
        rw [ha, hb]
      refine ⟨0, Fin.elim0, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
      · show Submodule.span F (Set.range Fin.elim0) = ⊤
        rw [Set.range_eq_empty, Submodule.span_empty, eq_top_iff]
        intro x _
        rw [Subsingleton.elim x 0]
        exact Submodule.zero_mem _
      · intro j _ _
        exact j.elim0
    · -- Inductive step: peel off the last factor {lit}`z − λₘ`.
      set mlast : Fin m := ⟨m - 1, by omega⟩ with hmlast_def
      set gamm : F := γ mlast with hgamm_def
      set f : W →ₗ[F] W := T - gamm • LinearMap.id with hf_def
      have hf_aeval : f = aeval T (Polynomial.X - Polynomial.C gamm) :=
        LinearMap.ext fun x => (aeval_X_sub_C_apply T gamm x).symm
      set U : Submodule F W := range f with hU_def
      have hU_inv : InvariantUnder T U := by
        rw [hU_def, hf_aeval]
        exact range_aeval_invariant T _
      -- The product of the remaining factors annihilates {lit}`T|_U`:
      -- every {lit}`u ∈ U` is {lit}`(T − λₘI)x`, and applying the remaining
      -- factors gives {lit}`p(T)x = 0`.
      have hprod_split : (∏ k ∈ Finset.univ.erase mlast,
          (Polynomial.X - Polynomial.C (γ k))) *
            (Polynomial.X - Polynomial.C gamm) = minpoly F T := by
        rw [hfact, hgamm_def]
        exact Finset.prod_erase_mul _ _ (Finset.mem_univ mlast)
      have hdvd : minpoly F hU_inv.restrict ∣
          ∏ k ∈ Finset.univ.erase mlast,
            (Polynomial.X - Polynomial.C (γ k)) := by
        rw [← aeval_eq_zero_iff_minpoly_dvd]
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        rw [aeval_restrict_coe hU_inv _ u]
        obtain ⟨x, hx⟩ := LinearMap.mem_range.mp u.2
        rw [← hx, hf_aeval, ← LinearMap.comp_apply, ← aeval_mul_eq_comp,
          hprod_split, minpoly.aeval, LinearMap.zero_apply,
          LinearMap.zero_apply, ZeroMemClass.coe_zero]
      have hprod_ne : (∏ k ∈ Finset.univ.erase mlast,
          (Polynomial.X - Polynomial.C (γ k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => Polynomial.X_sub_C_ne_zero (γ k)
      -- The minimal polynomial of {lit}`T|_U` is a product of fewer than
      -- {lit}`m` monic linear factors.
      have hsplits : (minpoly F hU_inv.restrict).Splits :=
        Polynomial.Splits.of_dvd
          (Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _)
          hprod_ne hdvd
      obtain ⟨m', lam', hfact', hm'_deg⟩ := monic_splits_eq_prod_fin
        (minpoly.monic (Algebra.IsIntegral.isIntegral hU_inv.restrict))
        hsplits
      have hm'_lt : m' < m := by
        have hle := Polynomial.natDegree_le_of_dvd hdvd hprod_ne
        have hdeg_prod : (∏ k ∈ Finset.univ.erase mlast,
            (Polynomial.X - Polynomial.C (γ k))).natDegree = m - 1 := by
          rw [Polynomial.natDegree_prod _ _
            (fun k _ => Polynomial.X_sub_C_ne_zero (γ k))]
          simp [Finset.card_erase_of_mem]
        omega
      -- Induction: an upper-triangular basis {lit}`u₁, …, u_M` for
      -- {lit}`T|_U`…
      obtain ⟨M, u', hu', hA'⟩ := ih m' hm'_lt U inferInstance inferInstance
        inferInstance hU_inv.restrict lam' hfact'
      -- …whose image in {lit}`W` we extend to a basis of {lit}`W`.
      set uW : Fin M → W := fun i => (u' i : W) with huW_def
      have huW_li : LinearIndependent F uW :=
        hu'.1.map' U.subtype (Submodule.ker_subtype U)
      obtain ⟨n, w, hMn, hw, hpre⟩ :=
        LADR.Section_2B.exists_basis_extending uW huW_li
      refine ⟨n, w, hw, ?_⟩
      -- It remains to verify 5.39(c) for the extended basis.
      have h31 := (tfae_upperTriangular hw T).out 2 0
      apply h31.mp
      have hT_decomp : ∀ x : W, T x = f x + gamm • x := by
        intro x
        rw [hf_def, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, sub_add_cancel]
      have hU_le : U ≤ Submodule.span F (w '' {i : Fin n | (i : ℕ) < M}) := by
        have hU_span : U = Submodule.span F (Set.range uW) := by
          have h1 : Submodule.map U.subtype ⊤ = U := Submodule.map_subtype_top U
          have h2 : Submodule.span F (Set.range u') = ⊤ := hu'.2
          rw [← h1, ← h2, Submodule.map_span, ← Set.range_comp]
          rfl
        rw [hU_span]
        apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        apply Submodule.subset_span
        exact ⟨Fin.castLE hMn i, by
          simp only [Set.mem_setOf_eq, Fin.val_castLE]
          exact i.isLt, hpre i⟩
      intro k
      by_cases hkM : (k : ℕ) < M
      · -- {lit}`wₖ` lies in {lit}`U`; use the upper-triangular structure of
        -- {lit}`T|_U`.
        set k' : Fin M := ⟨(k : ℕ), hkM⟩ with hk'_def
        have hwk : w k = uW k' := by
          have h := hpre k'
          rwa [show Fin.castLE hMn k' = k from Fin.ext rfl] at h
        have h302 := (tfae_upperTriangular hu' hU_inv.restrict).out 0 2
        have hres := h302.mp hA' k'
        have hTwk : T (w k) = ((hU_inv.restrict (u' k') : U) : W) := by
          rw [hwk]
          exact (hU_inv.restrict_apply (u' k')).symm
        rw [hTwk]
        have hcoe : ((hU_inv.restrict (u' k') : U) : W) ∈
            Submodule.span F (⇑U.subtype '' (u' '' {i | i ≤ k'})) := by
          rw [← Submodule.map_span]
          exact Submodule.mem_map_of_mem hres
        refine Submodule.span_mono ?_ hcoe
        rintro x ⟨y, ⟨i, hi, rfl⟩, rfl⟩
        refine ⟨Fin.castLE hMn i, ?_, (hpre i).symm ▸ rfl⟩
        rw [Set.mem_setOf_eq, Fin.le_def]
        simp only [Fin.val_castLE]
        exact Fin.le_def.mp hi
      · -- {lit}`k ≥ M`: write {lit}`Twₖ = (T − γₘI)wₖ + γₘwₖ`, with the
        -- first summand in {lit}`U ⊆ span(w₁, …, w_M)`.
        rw [hT_decomp (w k)]
        apply Submodule.add_mem
        · refine Submodule.span_mono ?_
            (hU_le (LinearMap.mem_range_self f (w k)))
          rintro x ⟨i, hi, rfl⟩
          refine ⟨i, ?_, rfl⟩
          rw [Set.mem_setOf_eq, Fin.le_def]
          rw [Set.mem_setOf_eq] at hi
          omega
        · exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨k, le_refl k, rfl⟩)

theorem exists_upperTriangular_iff_minpoly_eq_prod [Finite F V]
    (T : V →ₗ[F] V) :
    (∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T)) ↔
    ∃ (m : ℕ) (γ : Fin m → F),
      minpoly F T = ∏ k, (Polynomial.X - Polynomial.C (γ k)) := by
  constructor
  · -- 5.40 gives {lit}`q(T) = 0` for the product of diagonal factors; thus
    -- the minimal polynomial divides a split polynomial, hence splits.
    rintro ⟨n, v, hv, hA⟩
    have hdvd : minpoly F T ∣ ∏ k, (Polynomial.X -
        Polynomial.C (matrixOf hv hv T k k)) :=
      (aeval_eq_zero_iff_minpoly_dvd T _).mp (aeval_prod_diag_eq_zero hv T hA)
    have hprod_ne : (∏ k, (Polynomial.X -
        Polynomial.C (matrixOf hv hv T k k))) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k _
      exact Polynomial.X_sub_C_ne_zero _
    have hsplits : (minpoly F T).Splits :=
      Polynomial.Splits.of_dvd
        (Polynomial.Splits.prod fun k _ => Polynomial.Splits.X_sub_C _)
        hprod_ne hdvd
    obtain ⟨m, lam, hfact, -⟩ := monic_splits_eq_prod_fin
      (minpoly.monic (Algebra.IsIntegral.isIntegral T)) hsplits
    exact ⟨m, lam, hfact⟩
  · rintro ⟨m, lam, hfact⟩
    exact exists_upperTriangular_of_minpoly_prod m V inferInstance
      inferInstance inferInstance T lam hfact

/-! 5.47 If {lit}`F = ℂ`, then every operator on {lit}`V` has an
upper-triangular matrix with respect to some basis of {lit}`V` (5.44 plus
the fundamental theorem of algebra). -/

theorem exists_upperTriangular_complex {V : Type u} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      IsUpperTriangular (matrixOf hv hv T) := by
  rw [exists_upperTriangular_iff_minpoly_eq_prod]
  obtain ⟨m, γ, hfact, -⟩ := monic_splits_eq_prod_fin
    (minpoly.monic (Algebra.IsIntegral.isIntegral T))
    (IsAlgClosed.splits (k := ℂ) _)
  exact ⟨m, γ, hfact⟩

/-! # Exercises -/

/-- 5C.1 Prove or give a counterexample: if {lit}`T²` has an upper-triangular
matrix with respect to some basis, then so does {lit}`T`.
(Stated on {lit}`ℝ²`.) -/
def exercise_5C_1 :
    Decidable (∀ T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ),
      (∃ (v : Fin 2 → (Fin 2 → ℝ)) (hv : IsBasis ℝ v),
        IsUpperTriangular (matrixOf hv hv (T ∘ₗ T))) →
      ∃ (v : Fin 2 → (Fin 2 → ℝ)) (hv : IsBasis ℝ v),
        IsUpperTriangular (matrixOf hv hv T)) := by
  -- use T = ((0, -1), (1, 0)) — rotation by 90° — so T² = -I, which is upper
  -- triangular, while T itself has no real eigenvalue.
  apply isFalse
  intro h
  -- {lit}`T² = −I` is diagonal in the standard basis, hence upper triangular.
  have hsq : ∃ (v : Fin 2 → (Fin 2 → ℝ)) (hv : IsBasis ℝ v),
      IsUpperTriangular (matrixOf hv hv
        (LADR.Section_5A.T_5_9 ℝ ∘ₗ LADR.Section_5A.T_5_9 ℝ)) := by
    refine ⟨_, isBasis_stdBasis 2, ?_⟩
    intro j k hkj
    rw [matrixOf_apply, isBasis_stdBasis_repr]
    fin_cases j <;> fin_cases k <;> simp_all [LADR.Section_5A.T_5_9]
  obtain ⟨v, hv, hupper⟩ := h _ hsq
  -- The first column of an upper-triangular matrix is {lit}`(A₀₀, 0)`, so
  -- {lit}`v₀` is an eigenvector of {lit}`T` with eigenvalue {lit}`A₀₀`.
  set c := matrixOf hv hv (LADR.Section_5A.T_5_9 ℝ) 0 0 with hc
  have hT0 : LADR.Section_5A.T_5_9 ℝ (v 0) = c • v 0 := by
    rw [matrixOf_spec hv hv _ 0, Fin.sum_univ_two, hupper 1 0 (by decide)]
    simp [hc]
  -- Its coordinates read {lit}`−(v₀)₁ = c (v₀)₀` and {lit}`(v₀)₀ = c (v₀)₁`,
  -- forcing {lit}`(1 + c²) v₀ = 0`, i.e. {lit}`v₀ = 0` — impossible for a
  -- basis vector.
  have h0 : -(v 0) 1 = c * (v 0) 0 := by
    simpa [LADR.Section_5A.T_5_9] using congrFun hT0 0
  have h1 : (v 0) 0 = c * (v 0) 1 := by
    simpa [LADR.Section_5A.T_5_9] using congrFun hT0 1
  have h2 : (1 + c ^ 2) * (v 0) 0 = 0 := by linear_combination h1 - c * h0
  have h3 : (1 + c ^ 2) * (v 0) 1 = 0 := by linear_combination -h0 - c * h1
  have hpos : (0 : ℝ) < 1 + c ^ 2 := by positivity
  apply hv.1.ne_zero 0
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp h2).resolve_left (ne_of_gt hpos)
  · exact (mul_eq_zero.mp h3).resolve_left (ne_of_gt hpos)


/-- 5C.2 (a) -/
theorem exercise_5C_2a {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hA : IsUpperTriangular A) (hB : IsUpperTriangular B) :
    IsUpperTriangular (A + B) ∧ ∀ k, (A + B) k k = A k k + B k k := by
  constructor
  · intro i j h
    rw [IsUpperTriangular] at hA hB
    specialize hA i j h
    specialize hB i j h
    simp [hA, hB]
  · intro k
    rfl

/-- 5C.2 (b) -/
theorem exercise_5C_2b {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hA : IsUpperTriangular A) (hB : IsUpperTriangular B) :
    IsUpperTriangular (A * B) ∧ ∀ k, (A * B) k k = A k k * B k k := by
  constructor
  · intro i j h
    -- the entry is row i · column j, but row i is zero below i, and column j is zero above j
    -- with h, that gives 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with hl | hl
    · rw [hA i l hl, zero_mul]
    · rw [hB l j (lt_of_lt_of_le h hl), mul_zero]
  · intro k
    -- row k · column k, but row k is zero below k, and col k is zero above k
    -- so only k contributes to the dot product
    rw [Matrix.mul_apply, Finset.sum_eq_single k]
    · intro l _ hlk
      rcases lt_or_gt_of_ne hlk with hl | hl
      · rw [hA k l hl, zero_mul]
      · rw [hB l k hl, mul_zero]
    · exact fun hk => absurd (Finset.mem_univ k) hk

/-- 5C.3 -/
theorem exercise_5C_3 [Finite F V] {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (T : V →ₗ[F] V) (hT : IsInvertible T)
    (hA : IsUpperTriangular (matrixOf hv hv T)) :
    IsUpperTriangular (matrixOf hv hv hT.inv) ∧
      ∀ k, matrixOf hv hv hT.inv k k = (matrixOf hv hv T k k)⁻¹ := by
  -- each diagonal entry is non-zero otherwise contra
  -- by induction on j
  -- base case - the first column of T is a, 0, 0,..., so, the first column
  -- of the inverse has to be also 0, except for the first entry which is 1/a.
  -- by induction, for each next column, since T j column is zero below j,
  -- only first j entries contribute to the j-th column of the inverse.
  -- but by induction we have proven that all entries below the diagonal in the previous cols are zero
  -- so again the contribution is only zero

  -- altertnative proof - translate to min poly split,
  -- min poly of inverse is obtained by substituting X⁻¹ into the min poly of T.
  -- which still splits - thus the inverse is also upper triangular. Then by 2 b)
  -- diagonal entries have to be inverses.

  -- {lit}`T` is injective, so no diagonal entry vanishes: by 5.41 a zero on
  -- the diagonal would make {lit}`0` an eigenvalue of {lit}`T`.
  have hTinj : Function.Injective T := by
    intro x y hxy
    have hx := LinearMap.congr_fun hT.inv_comp x
    have hy := LinearMap.congr_fun hT.inv_comp y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
    rw [← hx, ← hy, hxy]
  have hne : ∀ k, matrixOf hv hv T k k ≠ 0 := by
    intro k hk
    obtain ⟨x, hx0, hTx⟩ := Module.End.hasEigenvalue_iff_exists.mp
      ((isEigenvalue_iff_diag hv T hA 0).mpr ⟨k, hk⟩)
    exact hx0 (hTinj (by simpa using hTx))
  -- {lit}`ℳ(T⁻¹) ℳ(T) = ℳ(T⁻¹T) = I`.
  have hid : matrixOf hv hv (LinearMap.id : V →ₗ[F] V) = 1 := by
    simp [matrixOf]
  have hCA : matrixOf hv hv hT.inv * matrixOf hv hv T = 1 := by
    rw [← LADR.Section_3C.matrixOf_comp hv hv hv, hT.inv_comp, hid]
  have hCupper : IsUpperTriangular (matrixOf hv hv hT.inv) := by
    -- Induction on the column {lit}`j`, as sketched above.
    have main : ∀ m : ℕ, ∀ j : Fin n, j.val = m → ∀ i : Fin n, j < i →
        matrixOf hv hv hT.inv i j = 0 := by
      intro m
      induction m using Nat.strongRecOn with
      | _ m ih =>
        rintro j rfl i hji
        -- Entry {lit}`(i, j)` of {lit}`ℳ(T⁻¹) ℳ(T) = I` is {lit}`0`, and only
        -- {lit}`l = j` contributes to it: the terms with {lit}`l > j` have
        -- {lit}`ℳ(T)_{l j} = 0`, and those with {lit}`l < j` have
        -- {lit}`ℳ(T⁻¹)_{i l} = 0` by the induction hypothesis.
        have hrow :
            ∑ l, matrixOf hv hv hT.inv i l * matrixOf hv hv T l j = 0 := by
          rw [← Matrix.mul_apply, hCA,
            Matrix.one_apply_ne (Ne.symm (ne_of_lt hji))]
        have hsingle :
            ∑ l, matrixOf hv hv hT.inv i l * matrixOf hv hv T l j =
              matrixOf hv hv hT.inv i j * matrixOf hv hv T j j := by
          refine Finset.sum_eq_single j ?_ fun h => absurd (Finset.mem_univ j) h
          intro l _ hlj
          rcases lt_or_gt_of_ne hlj with hl | hl
          · rw [ih l.val hl l rfl i (lt_trans hl hji), zero_mul]
          · rw [hA l j hl, mul_zero]
        rw [hsingle] at hrow
        exact (mul_eq_zero.mp hrow).resolve_right (hne j)
    exact fun i j hji => main j.val j rfl i hji
  refine ⟨hCupper, fun k => ?_⟩
  -- Both factors are upper triangular, so 5C.2(b) reads off the diagonal of
  -- {lit}`ℳ(T⁻¹) ℳ(T) = I`: {lit}`(T⁻¹)ₖₖ Tₖₖ = 1`.
  have hdiag := (exercise_5C_2b _ _ hCupper hA).2 k
  rw [hCA, Matrix.one_apply_eq] at hdiag
  exact eq_inv_of_mul_eq_one_left hdiag.symm

/-- The swap {lit}`(x, y) ↦ (y, x)`, used for 5C.4. -/
def T_5C_4 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![x 1, x 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' c x := by funext i; fin_cases i <;> simp

/-- 5C.4 -/
theorem exercise_5C_4 :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : Finite ℝ V)
      (T : V →ₗ[ℝ] V),
      (∃ (v : Fin (finrank ℝ V) → V) (hv : IsBasis ℝ v),
        ∀ k, matrixOf hv hv T k k = 0) ∧ IsInvertible T := by
    -- use (0,1),(1,0), which is self-inverse
    refine ⟨Fin 2 → ℝ, inferInstance, inferInstance, inferInstance, T_5C_4, ?_, ?_⟩
    · have hrank : finrank ℝ (Fin 2 → ℝ) = 2 := by simp
      rw [hrank]
      refine ⟨_, isBasis_stdBasis 2, fun k => ?_⟩
      rw [matrixOf_apply, isBasis_stdBasis_repr]
      fin_cases k <;> simp [T_5C_4]
    · exact ⟨T_5C_4, by ext x i; fin_cases i <;> simp [T_5C_4],
        by ext x i; fin_cases i <;> simp [T_5C_4]⟩

/-- The operator {lit}`(x, y) ↦ (x + y, x + y)`, used for 5C.5. -/
def T_5C_5 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![x 0 + x 1, x 0 + x 1]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by funext i; fin_cases i <;> simp <;> ring

/-- 5C.5 -/
theorem exercise_5C_5 :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : Finite ℝ V)
      (T : V →ₗ[ℝ] V),
      (∃ (v : Fin (finrank ℝ V) → V) (hv : IsBasis ℝ v),
        ∀ k, matrixOf hv hv T k k ≠ 0) ∧ ¬ IsInvertible T := by
  -- use ((1,1),(1,1)), which is not injective as it maps everything to (x,x)
  refine ⟨Fin 2 → ℝ, inferInstance, inferInstance, inferInstance, T_5C_5, ?_, ?_⟩
  · have hrank : finrank ℝ (Fin 2 → ℝ) = 2 := by simp
    rw [hrank]
    refine ⟨_, isBasis_stdBasis 2, fun k => ?_⟩
    rw [matrixOf_apply, isBasis_stdBasis_repr]
    fin_cases k <;> simp [T_5C_5]
  · -- {lit}`T (1, −1) = 0`, so {lit}`T` is not injective.
    rintro ⟨S, hS, -⟩
    have h := LinearMap.congr_fun hS ![1, -1]
    have hzero : T_5C_5 ![1, -1] = 0 := by
      funext i; fin_cases i <;> simp [T_5C_5]
    rw [LinearMap.comp_apply, hzero, map_zero, LinearMap.id_apply] at h
    have := congrFun h 0
    norm_num at this

/-- 5C.6 For {lit}`F = ℂ`: invariant subspaces of every dimension
{lit}`k ≤ dim V` exist. -/
theorem exercise_5C_6 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (k : ℕ) (hk : k ≤ finrank ℂ V) :
    ∃ U : Submodule ℂ V, InvariantUnder T U ∧ finrank ℂ U = k := by
  -- use that under C, every matrix has an upper triangular form
  -- with some basis, now take the first k vectors of that basis
  -- by theorem above, upper triangular is equivalent with span of
  -- the first k basis vectors forming an invariant subspace
  obtain ⟨n, v, hv, hupper⟩ := exists_upperTriangular_complex T
  have hn : n = finrank ℂ V := LADR.Section_2C.isBasis_card_eq_finrank v hv
  have hkn : k ≤ n := by rw [hn]; exact hk
  set w : Fin k → V := fun i => v (Fin.castLE hkn i) with hwdef
  have hwli : LinearIndependent ℂ w := hv.1.comp _ (Fin.castLE_injective hkn)
  refine ⟨Submodule.span ℂ (Set.range w), ?_, ?_⟩
  · rw [LADR.Section_5A.invariantUnder_iff_map_le, Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    -- {lit}`T wᵢ ∈ span(v₀, …, v_{castLE i})`, and all those vectors are
    -- among {lit}`w₀, …, w_{k−1}`.
    have h3 := (tfae_upperTriangular hv T).out 0 2
    refine Submodule.span_mono ?_ (h3.mp hupper (Fin.castLE hkn i))
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨⟨j.val, lt_of_le_of_lt (Fin.le_def.mp hj) i.isLt⟩, rfl⟩
  · rw [finrank_span_eq_card hwli, Fintype.card_fin]

/-- A nonzero polynomial that annihilates {lit}`v` can be rescaled to a monic
one of the same degree. -/
private lemma exists_monic_annihilator (T : V →ₗ[F] V) (v : V)
    {s : Polynomial F} (hs : s ≠ 0) (hann : aeval T s v = 0) :
    ∃ r : Polynomial F, r.Monic ∧ aeval T r v = 0 ∧ r.degree = s.degree := by
  refine ⟨s * Polynomial.C s.leadingCoeff⁻¹,
    Polynomial.monic_mul_leadingCoeff_inv hs, ?_,
    Polynomial.degree_mul_leadingCoeff_inv s hs⟩
  rw [mul_comm, aeval_mul_eq_comp]
  simp [hann]

/-- 5C.7 (a) For each {lit}`v ∈ V` there is a unique monic polynomial
{lit}`p_v` of smallest degree with {lit}`p_v(T)v = 0`. -/
theorem exercise_5C_7a [Finite F V] (T : V →ₗ[F] V) (v : V) :
    ∃! p : Polynomial F, p.Monic ∧ aeval T p v = 0 ∧
      ∀ q : Polynomial F, q.Monic → aeval T q v = 0 →
        p.degree ≤ q.degree := by
  -- take v, Tv, T^2v, ... until you get a linearly dependent set
  -- by construction, the degree is minimal and the coeff of highest
  -- degree term is non-zero so we can normalize to 1.
  -- for uniqueness, assume q is another, then p - q has smaller degree
  -- and also annihilates v, leading to a contradiction.
  classical
  -- Monic annihilators of {lit}`v` exist — the minimal polynomial of
  -- {lit}`T` is one — so there is one of least degree.
  have hex : ∃ d : ℕ, ∃ p : Polynomial F, p.Monic ∧ aeval T p v = 0 ∧
      p.natDegree = d := by
    refine ⟨(minpoly F T).natDegree, minpoly F T,
      minpoly.monic (Algebra.IsIntegral.isIntegral T), ?_, rfl⟩
    rw [minpoly.aeval F T]
    simp
  obtain ⟨p, hpm, hpa, hpd⟩ := Nat.find_spec hex
  have hmin : ∀ q : Polynomial F, q.Monic → aeval T q v = 0 →
      Nat.find hex ≤ q.natDegree := by
    intro q hqm hqa
    by_contra hlt
    exact Nat.find_min hex (not_le.mp hlt) ⟨q, hqm, hqa, rfl⟩
  have hdeg : ∀ q : Polynomial F, q.Monic → aeval T q v = 0 →
      p.degree ≤ q.degree := by
    intro q hqm hqa
    rw [Polynomial.degree_eq_natDegree hpm.ne_zero,
      Polynomial.degree_eq_natDegree hqm.ne_zero, Nat.cast_le, hpd]
    exact hmin q hqm hqa
  refine ⟨p, ⟨hpm, hpa, hdeg⟩, ?_⟩
  rintro q ⟨hqm, hqa, hqdeg⟩
  by_contra hne
  have hdegeq : q.degree = p.degree :=
    le_antisymm (hqdeg p hpm hpa) (hdeg q hqm hqa)
  have hlt : (q - p).degree < p.degree := by
    rw [← hdegeq]
    exact Polynomial.degree_sub_lt hdegeq hqm.ne_zero
      (by rw [hqm.leadingCoeff, hpm.leadingCoeff])
  have hann : aeval T (q - p) v = 0 := by
    rw [map_sub]
    simp [hqa, hpa]
  obtain ⟨r, hrm, hra, hrd⟩ :=
    exists_monic_annihilator T v (sub_ne_zero.mpr hne) hann
  exact absurd (hdeg r hrm hra) (by rw [hrd]; exact not_le.mpr hlt)

/-- The monic polynomial {lit}`p_v` of smallest degree with {lit}`p_v(T)v = 0`,
chosen from the existence-and-uniqueness statement {name}`exercise_5C_7a`. -/
noncomputable def p_v [Finite F V] (T : V →ₗ[F] V) (v : V) : Polynomial F :=
  (exercise_5C_7a T v).exists.choose

/-- Defining properties of {lit}`p_v`: it is monic, annihilates {lit}`v`, and
has smallest degree among monic polynomials that annihilate {lit}`v`. -/
theorem p_v_spec [Finite F V] (T : V →ₗ[F] V) (v : V) :
    (p_v T v).Monic ∧ aeval T (p_v T v) v = 0 ∧
      ∀ q : Polynomial F, q.Monic → aeval T q v = 0 →
        (p_v T v).degree ≤ q.degree :=
  (exercise_5C_7a T v).exists.choose_spec

/-- 5C.7 (b) The minimal polynomial of {lit}`T` is a polynomial multiple of
{lit}`p_v` for each {lit}`v`. -/
theorem exercise_5C_7b [Finite F V] (T : V →ₗ[F] V) (v : V) :
    p_v T v ∣ minpoly F T := by
  -- by definition, deg minpoly ≥ deg p_v, otherwise p_v would not be minimal.
  -- then minpoly = q * p_v + r, by division algo
  -- but r must be 0, otherwise it would contradict the minimality of p_v too.
  obtain ⟨hpm, hpa, hpmin⟩ := p_v_spec T v
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hpm]
  by_contra hr
  -- {lit}`minpoly = p_v · (minpoly /ₘ p_v) + r`, and both {lit}`minpoly` and
  -- the product annihilate {lit}`v`, hence so does the remainder {lit}`r`.
  have hrann : aeval T (minpoly F T %ₘ p_v T v) v = 0 := by
    have hdecomp := Polynomial.modByMonic_add_div (minpoly F T) (p_v T v)
    have hm : aeval T (minpoly F T) v = 0 := by rw [minpoly.aeval F T]; simp
    have hprod : aeval T (p_v T v * (minpoly F T /ₘ p_v T v)) v = 0 := by
      rw [mul_comm, aeval_mul_eq_comp]
      simp [hpa]
    have hsum := congrArg (fun q : Polynomial F => aeval T q v) hdecomp
    simp only [map_add, LinearMap.add_apply] at hsum
    rw [hprod, add_zero, hm] at hsum
    exact hsum
  -- rescaled to monic, {lit}`r` would beat {lit}`p_v` in degree.
  obtain ⟨r, hrm, hra, hrd⟩ := exists_monic_annihilator T v hr hrann
  exact absurd (hrd ▸ hpmin r hrm hra)
    (not_le.mpr (Polynomial.degree_modByMonic_lt _ hpm))

/-- The divisibility behind 5C.7(b), for an arbitrary polynomial annihilating
{lit}`v`: the same division-algorithm argument. -/
private lemma p_v_dvd [Finite F V] (T : V →ₗ[F] V) (v : V) {q : Polynomial F}
    (hq : aeval T q v = 0) : p_v T v ∣ q := by
  obtain ⟨hpm, hpa, hpmin⟩ := p_v_spec T v
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hpm]
  by_contra hr
  have hrann : aeval T (q %ₘ p_v T v) v = 0 := by
    have hdecomp := Polynomial.modByMonic_add_div q (p_v T v)
    have hprod : aeval T (p_v T v * (q /ₘ p_v T v)) v = 0 := by
      rw [mul_comm, aeval_mul_eq_comp]
      simp [hpa]
    have hsum := congrArg (fun s : Polynomial F => aeval T s v) hdecomp
    simp only [map_add, LinearMap.add_apply] at hsum
    rw [hprod, add_zero, hq] at hsum
    exact hsum
  obtain ⟨r, hrm, hra, hrd⟩ := exists_monic_annihilator T v hr hrann
  exact absurd (hrd ▸ hpmin r hrm hra)
    (not_le.mpr (Polynomial.degree_modByMonic_lt _ hpm))

/-- The relation {lit}`T²v + 2Tv = −2v` of 5C.8 says that {lit}`X² + 2X + 2`
annihilates {lit}`v`, so {lit}`p_v` is a nonconstant divisor of it. -/
private lemma p_v_quadratic [Finite F V] (T : V →ₗ[F] V) (v : V) (hv : v ≠ 0)
    (h : T (T v) + 2 • T v = -(2 • v)) :
    p_v T v ∣ Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X + Polynomial.C 2 ∧
      (p_v T v).degree ≠ 0 := by
  have hq : aeval T ((Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X +
      Polynomial.C 2 : Polynomial F)) v = 0 := by
    have h0 : T (T v) + 2 • T v + 2 • v = 0 := by rw [h]; simp
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      LinearMap.add_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      pow_two]
    simpa [two_smul] using h0
  refine ⟨p_v_dvd T v hq, fun hdeg => hv ?_⟩
  -- a monic annihilator of degree {lit}`0` is {lit}`1`, which forces
  -- {lit}`v = 0`.
  have h1 : p_v T v = 1 :=
    ((p_v_spec T v).1.degree_le_zero_iff_eq_one).mp (le_of_eq hdeg)
  have h2 := (p_v_spec T v).2.1
  rw [h1] at h2
  simpa using h2

/-- 5C.8 (a) If {lit}`F = ℝ` and {lit}`T²v + 2Tv = −2v` for some
{lit}`v ≠ 0`, then {lit}`T` has no upper-triangular matrix with respect to
any basis. -/
theorem exercise_5C_8a {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (T : V →ₗ[ℝ] V) (v : V) (hv : v ≠ 0)
    (h : T (T v) + 2 • T v = -(2 • v)) :
    ¬ ∃ (n : ℕ) (w : Fin n → V) (hw : IsBasis ℝ w),
      IsUpperTriangular (matrixOf hw hw T) := by
  -- p = T^2 + 2T + 2, b^ - 4 a c < 0, so no real roots.
  -- hence it is p_v, since p_v will have to divide it, but it has no divisors.
  -- then p | minpoly ot T, and again since it doesn't split minpoly doesn't split
  -- so no upper-triangular matrix can exist for T.
  intro hupper
  obtain ⟨hdvd, hdeg⟩ := p_v_quadratic T v hv h
  -- an upper-triangular matrix makes the minimal polynomial split (5.44), so
  -- its divisor {lit}`p_v` splits too.
  obtain ⟨m, γ, hfact⟩ := (exists_upperTriangular_iff_minpoly_eq_prod T).mp hupper
  have hsplit : (minpoly ℝ T).Splits := by
    rw [hfact]
    exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
  have hpsplit : (p_v T v).Splits :=
    hsplit.of_dvd (minpoly.ne_zero (Algebra.IsIntegral.isIntegral T))
      (exercise_5C_7b T v)
  -- so {lit}`p_v` has a real root, which is then a root of {lit}`X² + 2X + 2`.
  obtain ⟨γ₀, hγ₀⟩ := hpsplit.exists_eval_eq_zero hdeg
  have hroot := Polynomial.IsRoot.dvd hγ₀ hdvd
  have hq : γ₀ ^ 2 + 2 * γ₀ + 2 = 0 := by simpa [Polynomial.IsRoot] using hroot
  nlinarith [sq_nonneg (γ₀ + 1)]

/-- 5C.8 (b) If {lit}`F = ℂ` and the same relation holds, then every
upper-triangular matrix of {lit}`T` has {lit}`−1 + i` or {lit}`−1 − i` on
its diagonal. -/
theorem exercise_5C_8b {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (v : V) (hv : v ≠ 0)
    (h : T (T v) + 2 • T v = -(2 • v))
    {n : ℕ} {w : Fin n → V} (hw : IsBasis ℂ w)
    (hA : IsUpperTriangular (matrixOf hw hw T)) :
    ∃ k, matrixOf hw hw T k k = -1 + Complex.I ∨
      matrixOf hw hw T k k = -1 - Complex.I := by
  -- but over C p = (x + 1 - i) * (x + 1 + i) (can be checked)
  -- p_v is either (x + 1 - i) or (x + 1 + i) or both
  -- so p_v has a root which is either -1 + i or -1 - i.
  -- but p_v | minpoly, so either of those is root of minpoly,
  -- which is same as saying γ₀ is an eigenvalue of T.
  -- same as saying γ₀ appears on the diagonal of any upper-triangular matrix of T.
  obtain ⟨hdvd, hdeg⟩ := p_v_quadratic T v hv h
  -- {lit}`ℂ` is algebraically closed, so {lit}`p_v` has a root {lit}`γ₀`;
  -- it is a root of {lit}`X² + 2X + 2`, hence {lit}`−1 ± i`.
  obtain ⟨γ₀, hγ₀⟩ := IsAlgClosed.exists_root (p_v T v) hdeg
  have hroot := Polynomial.IsRoot.dvd hγ₀ hdvd
  have hq : γ₀ ^ 2 + 2 * γ₀ + 2 = 0 := by simpa [Polynomial.IsRoot] using hroot
  -- {lit}`γ₀` is also a root of the minimal polynomial, hence an eigenvalue,
  -- hence a diagonal entry (5.41).
  have hev : HasEigenvalue T γ₀ :=
    (isEigenvalue_iff_isRoot T γ₀).mpr (Polynomial.IsRoot.dvd hγ₀ (exercise_5C_7b T v))
  obtain ⟨k, hk⟩ := (isEigenvalue_iff_diag hw T hA γ₀).mp hev
  refine ⟨k, ?_⟩
  have hfac : (γ₀ - (-1 + Complex.I)) * (γ₀ - (-1 - Complex.I)) = 0 := by
    linear_combination hq - Complex.I_sq
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact Or.inl (hk.trans (sub_eq_zero.mp h1))
  · exact Or.inr (hk.trans (sub_eq_zero.mp h1))

/-- 5C.9 Every square matrix with complex entries is similar to an
upper-triangular matrix. -/
theorem exercise_5C_9 {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, IsUnit A ∧
      IsUpperTriangular (A⁻¹ * B * A) := by
  -- there exists lin tr. T s.t. with respect to standard basis e its matrix is B.
  -- then find another basis v, s.t. the matrix of T with respect to this new basis is upper-triangular.
  -- now A is the matrix of the identity tr, w.r.t, e and v
  -- and Ainv is the matrix of the identity tr, w.r.t, v and e
  -- by definition A and Ainv are inverses of each other
  -- by transfomation Ainv B A is the matrix for I T I = T with respect to the new basis v.
  -- hence upper triangular.
  classical
  set b := (isBasis_stdBasis (F := ℂ) n).toModuleBasis with hb
  set T := Matrix.toLin b b B with hT
  obtain ⟨m, v, hv, hupper⟩ := exists_upperTriangular_complex T
  have hm : m = n := by
    have hcard := LADR.Section_2C.isBasis_card_eq_finrank v hv
    simpa using hcard
  subst hm
  -- {lit}`A` is the matrix of the identity from the basis {lit}`v` to the
  -- standard basis; its inverse is the matrix the other way round.
  haveI : Invertible (b.toMatrix ⇑hv.toModuleBasis) :=
    b.invertibleToMatrix hv.toModuleBasis
  refine ⟨b.toMatrix ⇑hv.toModuleBasis, isUnit_of_invertible _, ?_⟩
  have hinv : (b.toMatrix ⇑hv.toModuleBasis)⁻¹ = hv.toModuleBasis.toMatrix ⇑b :=
    Matrix.inv_eq_left_inv (Module.Basis.toMatrix_mul_toMatrix_flip _ _)
  have hB : LinearMap.toMatrix b b T = B := by rw [hT, LinearMap.toMatrix_toLin]
  rw [hinv, ← hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  exact hupper

/-- A square matrix is *lower triangular* if all entries above the diagonal
are {lit}`0`. -/
def IsLowerTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ j k, j < k → A j k = 0

/-- The reversed list {lit}`vₙ, …, v₁` is again a basis. -/
private lemma isBasis_rev {n : ℕ} {v : Fin n → V} (hv : IsBasis F v) :
    IsBasis F (fun i => v i.rev) := by
  refine ⟨hv.1.comp _ Fin.rev_involutive.injective, ?_⟩
  have hrange : Set.range (fun i : Fin n => v i.rev) = Set.range v := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.rev, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.rev, by simp⟩
  show Submodule.span F (Set.range fun i : Fin n => v i.rev) = ⊤
  rw [hrange]
  exact hv.2

/-- Reversing the basis reverses both indices of the matrix. -/
private lemma matrixOf_rev {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) (j k : Fin n) :
    matrixOf (isBasis_rev hv) (isBasis_rev hv) T j k =
      matrixOf hv hv T j.rev k.rev := by
  -- Both {lit}`∑ᵢ A'_{i,k} v_{rev i}` and {lit}`∑ᵢ A_{rev i, rev k} v_{rev i}`
  -- equal {lit}`T v_{rev k}` (the second after reindexing by {lit}`rev`), so
  -- linear independence identifies the coefficients.
  have h1 := matrixOf_spec (isBasis_rev hv) (isBasis_rev hv) T k
  have h2 := matrixOf_spec hv hv T k.rev
  have h3 : ∑ i : Fin n, matrixOf hv hv T i.rev k.rev • v i.rev =
      ∑ i, matrixOf hv hv T i k.rev • v i :=
    Fintype.sum_equiv (Fin.revPerm) _ _ fun _ => rfl
  have key : ∑ i : Fin n, matrixOf (isBasis_rev hv) (isBasis_rev hv) T i k • v i.rev =
      ∑ i : Fin n, matrixOf hv hv T i.rev k.rev • v i.rev := by
    rw [← h1, h2, ← h3]
  have hzero : ∑ i : Fin n, (matrixOf (isBasis_rev hv) (isBasis_rev hv) T i k -
      matrixOf hv hv T i.rev k.rev) • v i.rev = 0 := by
    simp only [sub_smul]
    rw [Finset.sum_sub_distrib, key, sub_self]
  exact sub_eq_zero.mp
    (Fintype.linearIndependent_iff.mp (isBasis_rev hv).1 _ hzero j)

/-- Reversing the basis exchanges lower- and upper-triangular. -/
private lemma isLowerTriangular_iff_rev {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) :
    IsLowerTriangular (matrixOf hv hv T) ↔
      IsUpperTriangular (matrixOf (isBasis_rev hv) (isBasis_rev hv) T) := by
  constructor
  · intro hA j k hkj
    rw [matrixOf_rev]
    refine hA _ _ ?_
    have := j.isLt
    have := k.isLt
    simp only [Fin.lt_def, Fin.val_rev] at *
    omega
  · intro hA j k hjk
    have hrev := hA j.rev k.rev ?_
    · rw [matrixOf_rev] at hrev
      simpa using hrev
    · have := j.isLt
      have := k.isLt
      simp only [Fin.lt_def, Fin.val_rev] at *
      omega

/-- …and the other way round. -/
private lemma isUpperTriangular_iff_rev {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) :
    IsUpperTriangular (matrixOf hv hv T) ↔
      IsLowerTriangular (matrixOf (isBasis_rev hv) (isBasis_rev hv) T) := by
  constructor
  · intro hA j k hjk
    rw [matrixOf_rev]
    refine hA _ _ ?_
    have := j.isLt
    have := k.isLt
    simp only [Fin.lt_def, Fin.val_rev] at *
    omega
  · intro hA j k hkj
    have hrev := hA j.rev k.rev ?_
    · rw [matrixOf_rev] at hrev
      simpa using hrev
    · have := j.isLt
      have := k.isLt
      simp only [Fin.lt_def, Fin.val_rev] at *
      omega

/-- The image of an up-set under the reversed basis is the image of the
matching down-set under the original one. -/
private lemma image_rev {n : ℕ} {α : Type*} (v : Fin n → α) (k : Fin n) :
    (fun i : Fin n => v i.rev) '' {i | i ≤ k} = v '' {i | k.rev ≤ i} := by
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i.rev, ?_, rfl⟩
    have := i.isLt
    have := k.isLt
    simp only [Set.mem_setOf_eq, Fin.le_def, Fin.val_rev] at *
    omega
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.rev, ?_, by simp⟩
    have := j.isLt
    have := k.isLt
    simp only [Set.mem_setOf_eq, Fin.le_def, Fin.val_rev] at *
    omega

/-- 5C.10 The lower-triangular analogue of 5.39. -/
theorem exercise_5C_10 {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) :
    [IsLowerTriangular (matrixOf hv hv T),
      ∀ k : Fin n, InvariantUnder T (Submodule.span F (v '' {i | k ≤ i})),
      ∀ k : Fin n, T (v k) ∈ Submodule.span F (v '' {i | k ≤ i})].TFAE := by
  -- create a reversed basis v', v' 0 = v (n - 1), v' 1 = v (n - 2), ..., v' (n - 1) = v 0
  -- then each statement above translates to the corresponding upper-triangular statement
  -- that we have proved already.
  -- (a) {lit}`A` is lower triangular iff {lit}`A'` is upper triangular, since
  -- {lit}`A'_{j,k} = A_{rev j, rev k}` and {lit}`rev` reverses the order.
  have h1 := isLowerTriangular_iff_rev hv T
  -- (b), (c) the sets {lit}`span(vₖ, …, vₙ)` are the sets
  -- {lit}`span(v'₁, …, v'_{rev k})`.
  have h2 : (∀ k : Fin n, InvariantUnder T (Submodule.span F (v '' {i | k ≤ i}))) ↔
      ∀ k : Fin n, InvariantUnder T
        (Submodule.span F ((fun i : Fin n => v i.rev) '' {i | i ≤ k})) := by
    constructor
    · intro h k
      rw [image_rev]
      exact h k.rev
    · intro h k
      have hk := h k.rev
      rw [image_rev, Fin.rev_rev] at hk
      exact hk
  have h3 : (∀ k : Fin n, T (v k) ∈ Submodule.span F (v '' {i | k ≤ i})) ↔
      ∀ k : Fin n, T ((fun i : Fin n => v i.rev) k) ∈
        Submodule.span F ((fun i : Fin n => v i.rev) '' {i | i ≤ k}) := by
    constructor
    · intro h k
      rw [image_rev]
      exact h k.rev
    · intro h k
      have hk := h k.rev
      rw [image_rev, Fin.rev_rev] at hk
      simpa using hk
  rw [h1, h2, h3]
  exact tfae_upperTriangular (isBasis_rev hv) T

/-- 5C.11 For {lit}`F = ℂ`: every operator has a lower-triangular matrix
with respect to some basis. -/
theorem exercise_5C_11 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      IsLowerTriangular (matrixOf hv hv T) := by
  -- take the upper-triangular basis from the complex case and reverse it to get a lower-triangular basis
  obtain ⟨n, v, hv, hupper⟩ := exists_upperTriangular_complex T
  exact ⟨n, _, isBasis_rev hv, (isUpperTriangular_iff_rev hv T).mp hupper⟩

/-- bonus proof exists upper triangular iff exists lower triangular -/
theorem exists_upperTriangular_iff_exists_lowerTriangular [Finite F V] (T : V →ₗ[F] V) :
    (∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T)) ↔
    (∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsLowerTriangular (matrixOf hv hv T)) := by
  -- use classification and reverse the order of the basis
  -- (the reversal alone does it: {lit}`ℳ'(T)_{j,k} = ℳ(T)_{rev j, rev k}`)
  constructor
  · rintro ⟨n, v, hv, h⟩
    exact ⟨n, _, isBasis_rev hv, (isUpperTriangular_iff_rev hv T).mp h⟩
  · rintro ⟨n, v, hv, h⟩
    exact ⟨n, _, isBasis_rev hv, (isLowerTriangular_iff_rev hv T).mp h⟩

/-- 5.44 restated: an upper-triangular matrix exists exactly when the minimal
polynomial splits. -/
private lemma exists_upperTriangular_iff_splits [Finite F V] (T : V →ₗ[F] V) :
    (∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T)) ↔ (minpoly F T).Splits := by
  rw [exists_upperTriangular_iff_minpoly_eq_prod]
  constructor
  · rintro ⟨m, γ, hfact⟩
    rw [hfact]
    exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
  · intro hs
    obtain ⟨m, γ, hfact, -⟩ :=
      monic_splits_eq_prod_fin (minpoly.monic (Algebra.IsIntegral.isIntegral T)) hs
    exact ⟨m, γ, hfact⟩

/-- 5C.12 (a) If {lit}`T` has an upper-triangular matrix with respect to some
basis of {lit}`V` and {lit}`U` is invariant, then {lit}`T|_U` has an
upper-triangular matrix with respect to some basis of {lit}`U`. -/
theorem exercise_5C_12a [Finite F V] (T : V →ₗ[F] V)
    (h : ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T))
    (U : Submodule F V) (hU : InvariantUnder T U) :
    ∃ (n : ℕ) (u : Fin n → U) (hu : IsBasis F u),
      IsUpperTriangular (matrixOf hu hu hU.restrict) := by
  -- upper iff min poly splits
  -- we proved that min poly of restriction | min poly
  -- so the restriction also has an upper-triangular matrix.
  refine (exists_upperTriangular_iff_splits hU.restrict).mpr ?_
  exact ((exists_upperTriangular_iff_splits T).mp h).of_dvd
    (minpoly.monic (Algebra.IsIntegral.isIntegral T)).ne_zero
    (LADR.Section_5B.minpoly_restrict_dvd T U hU)

/-- 5C.12 (b) Under the same hypotheses, the quotient operator {lit}`T/U`
has an upper-triangular matrix with respect to some basis of {lit}`V/U`. -/
theorem exercise_5C_12b [Finite F V] (T : V →ₗ[F] V)
    (h : ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T))
    (U : Submodule F V) (hU : InvariantUnder T U) :
    ∃ (n : ℕ) (w : Fin n → V ⧸ U) (hw : IsBasis F w),
      IsUpperTriangular (matrixOf hw hw
        (exercise_5A_38_quotient_op T U hU)) := by
  -- same as a) for the quotient operator.
  refine (exists_upperTriangular_iff_splits _).mpr ?_
  exact ((exists_upperTriangular_iff_splits T).mp h).of_dvd
    (minpoly.monic (Algebra.IsIntegral.isIntegral T)).ne_zero
    (LADR.Section_5B.exercise_5B_25a T U hU)

/-- 5C.13 Conversely: if {lit}`T|_U` and {lit}`T/U` both have
upper-triangular matrices, then so does {lit}`T`. -/
theorem exercise_5C_13 [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U)
    (h1 : ∃ (n : ℕ) (u : Fin n → U) (hu : IsBasis F u),
      IsUpperTriangular (matrixOf hu hu hU.restrict))
    (h2 : ∃ (n : ℕ) (w : Fin n → V ⧸ U) (hw : IsBasis F w),
      IsUpperTriangular (matrixOf hw hw
        (exercise_5A_38_quotient_op T U hU))) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T) := by
  -- same as 12, we proved minpoly | minpoly restriction * minpoly quotient
  -- so split carries over, so T also has an upper-triangular matrix.
  have hs1 := (exists_upperTriangular_iff_splits hU.restrict).mp h1
  have hs2 := (exists_upperTriangular_iff_splits _).mp h2
  refine (exists_upperTriangular_iff_splits T).mpr ?_
  refine (hs1.mul hs2).of_dvd ?_ (LADR.Section_5B.exercise_5B_25b T U hU)
  exact mul_ne_zero (minpoly.monic (Algebra.IsIntegral.isIntegral _)).ne_zero
    (minpoly.monic (Algebra.IsIntegral.isIntegral _)).ne_zero

/-- Any upper-triangular basis has {lit}`dim V` vectors, so the two phrasings
of "some basis" agree. -/
private lemma exists_upperTriangular_iff_finrank [Finite F V] (T : V →ₗ[F] V)
    {N : ℕ} (hN : N = finrank F V) :
    (∃ (v : Fin N → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T)) ↔
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T) := by
  subst hN
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨_, v, hv, h⟩
  · rintro ⟨n, v, hv, h⟩
    have hn : n = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v hv
    subst hn
    exact ⟨v, hv, h⟩

/-- 5C.14 {lit}`T` has an upper-triangular matrix with respect to some basis
of {lit}`V` iff the dual operator {lit}`T′` has an upper-triangular matrix
with respect to some basis of {lit}`V′`. -/
theorem exercise_5C_14 [Finite F V] (T : V →ₗ[F] V) :
    (∃ (v : Fin (finrank F V) → V) (hv : IsBasis F v),
      IsUpperTriangular (matrixOf hv hv T)) ↔
    ∃ (φ : Fin (finrank F V) → Module.Dual F V) (hφ : IsBasis F φ),
      IsUpperTriangular (matrixOf hφ hφ T.dualMap) := by
  -- upper-triangular iff minpoly splits
  -- dual has same minimal poly (5B.28), so it also has upper-triangular to some basis.
  rw [exists_upperTriangular_iff_finrank T rfl,
    exists_upperTriangular_iff_finrank T.dualMap Subspace.dual_finrank_eq.symm,
    exists_upperTriangular_iff_splits, exists_upperTriangular_iff_splits,
    LADR.Section_5B.exercise_5B_28]

end LADR.Section_5C
