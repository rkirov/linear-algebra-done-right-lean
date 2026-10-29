import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import Mathlib.Tactic.TFAE
import LinearAlgebraDoneRightLean.Section_1C
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_5A
import LinearAlgebraDoneRightLean.Section_5B
import LinearAlgebraDoneRightLean.Section_5C
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5D: Diagonalizable Operators
-/

namespace LADR.Section_5D

open LADR.Section_1C (IsDirectSum)
open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis isBasis_stdBasis exists_basis
  exists_basis_of_spans)
open LADR.Section_2C (isBasis_of_linearIndependent_of_card_eq)
open LADR.Section_3C (matrixOf matrixOf_apply matrixOf_spec)
open LADR.Section_3D (IsInvertible)
open Module.End (HasEigenvalue HasEigenvector)
open LADR.Section_5A (InvariantUnder
  eigenvectors_linearIndependent aeval_mul_eq_comp
  exercise_5A_38_quotient_op)
open LADR.Section_5B (aeval_eq_zero_iff_minpoly_dvd isEigenvalue_iff_isRoot
  minpoly_restrict_dvd)
open LADR.Section_5C (IsUpperTriangular)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! Diagonal Matrices -/

/-! 5.48 Definition: diagonal matrix — mathlib's {name}`Matrix.IsDiag`
(zero off the diagonal). -/

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) :
    A.IsDiag ↔ ∀ j k, j ≠ k → A j k = 0 :=
  ⟨fun h _j _k hjk => h hjk, fun h _j _k hjk => h _ _ hjk⟩

/-! 5.49 Example: {lit}`[[8,0,0],[0,5,0],[0,0,5]]` is a diagonal matrix.
Every diagonal matrix is upper triangular. -/

example : (!![8, 0, 0; 0, 5, 0; 0, 0, 5] : Matrix (Fin 3) (Fin 3) F).IsDiag := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;> first | rfl | simp_all

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (h : A.IsDiag) :
    IsUpperTriangular A :=
  fun _j _k hkj => h (ne_of_gt hkj)

/-! 5.50 Definition: diagonalizable -/

/-- An operator on {lit}`V` is *diagonalizable* if it has a diagonal matrix
with respect to some basis of {lit}`V`. -/
def IsDiagonalizable (T : V →ₗ[F] V) : Prop :=
  ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v), (matrixOf hv hv T).IsDiag

/-- If the matrix of {lit}`T` is diagonal, then each basis vector is an
eigenvector ({lit}`T vⱼ = A_{j,j} vⱼ`). -/
theorem apply_eq_smul_of_isDiag {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hA : (matrixOf hv hv T).IsDiag) (j : Fin n) :
    T (v j) = matrixOf hv hv T j j • v j := by
  rw [matrixOf_spec hv hv T j]
  rw [Finset.sum_eq_single j]
  · intro i _ hij
    rw [hA hij, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Conversely, the matrix of {lit}`T` with respect to a basis of
eigenvectors is diagonal. -/
theorem isDiag_matrixOf_of_eigenvectors {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (T : V →ₗ[F] V)
    (h : ∀ j, ∃ mu : F, T (v j) = mu • v j) :
    (matrixOf hv hv T).IsDiag := by
  intro i j hij
  obtain ⟨mu, hmu⟩ := h j
  rw [matrixOf_apply, hmu, map_smul]
  have hbasis : v j = hv.toModuleBasis j := (hv.toModuleBasis_apply j).symm
  rw [hbasis, Module.Basis.repr_self]
  rw [Finsupp.smul_apply, Finsupp.single_apply, if_neg (fun h => hij h.symm),
    smul_zero]

/-- If an operator has a diagonal matrix with respect to some basis, then the
entries on the diagonal are precisely the eigenvalues of the operator. This is
the diagonal analogue of 5.41 (determination of eigenvalues from an
upper-triangular matrix) and follows immediately from it, since every diagonal
matrix is upper triangular. -/
theorem hasEigenvalue_iff_diag [Finite F V] {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (T : V →ₗ[F] V) (hA : (matrixOf hv hv T).IsDiag)
    (lam : F) :
    HasEigenvalue T lam ↔ ∃ k, matrixOf hv hv T k k = lam :=
  Section_5C.isEigenvalue_iff_diag hv T (fun _j _k hkj => hA (ne_of_gt hkj)) lam

/-! 5.51 Example: {lit}`T(x, y) = (41x + 7y, −20x + 74y)` is diagonalizable:
{lit}`T(1, 4) = 69·(1, 4)` and {lit}`T(7, 5) = 46·(7, 5)`, and
{lit}`(1, 4), (7, 5)` is a basis of {lit}`ℝ²` (so the matrix of {lit}`T`
with respect to it is {lit}`[[69, 0], [0, 46]]`). -/

noncomputable def T_5_51 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![41 * x 0 + 7 * x 1, -(20 * x 0) + 74 * x 1]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

example : IsDiagonalizable T_5_51 := by
  set b : Fin 2 → (Fin 2 → ℝ) := ![![1, 4], ![7, 5]] with hb_def
  have hli : LinearIndependent ℝ b := by
    rw [hb_def, LinearIndependent.pair_iff]
    intro s t hst
    have h0 := congrFun hst 0
    have h1 := congrFun hst 1
    simp at h0 h1
    constructor <;> linarith
  have hv : IsBasis ℝ b := by
    apply isBasis_of_linearIndependent_of_card_eq b hli
    simp
  refine ⟨2, _, hv, isDiag_matrixOf_of_eigenvectors hv T_5_51 ?_⟩
  intro j
  fin_cases j
  · exact ⟨69, by funext i; fin_cases i <;> simp [T_5_51, hb_def] <;> norm_num⟩
  · exact ⟨46, by funext i; fin_cases i <;> simp [T_5_51, hb_def] <;> norm_num⟩

/-! 5.52 Definition: eigenspace {lit}`E(λ, T)` — mathlib's
{name}`Module.End.eigenspace`, with
{lit}`E(λ, T) = null(T − λI) = {v : Tv = λv}`. -/

example (T : V →ₗ[F] V) (lam : F) : Submodule F V :=
  Module.End.eigenspace T lam

example (T : V →ₗ[F] V) (lam : F) (v : V) :
    v ∈ Module.End.eigenspace T lam ↔ T v = lam • v :=
  Module.End.mem_eigenspace_iff

-- {lit}`λ` is an eigenvalue of {lit}`T` iff {lit}`E(λ, T) ≠ {0}`.
example (T : V →ₗ[F] V) (lam : F) :
    HasEigenvalue T lam ↔ Module.End.eigenspace T lam ≠ ⊥ :=
  Iff.rfl

/-! 5.53 Example: for the operator with diagonal matrix
{lit}`[[8,0,0],[0,5,0],[0,0,5]]` on {lit}`ℝ³`, the eigenspace {lit}`E(8)`
consists of the vectors {lit}`(x, 0, 0)`, and {lit}`E(5)` of the vectors
{lit}`(0, y, z)`. -/

noncomputable def D_5_53 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![8 * x 0, 5 * x 1, 5 * x 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

example (x : Fin 3 → ℝ) :
    x ∈ Module.End.eigenspace D_5_53 8 ↔ x 1 = 0 ∧ x 2 = 0 := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [D_5_53] at h1 h2
    constructor <;> linarith
  · intro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [D_5_53, h1, h2]

example (x : Fin 3 → ℝ) :
    x ∈ Module.End.eigenspace D_5_53 5 ↔ x 0 = 0 := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [D_5_53] at h0
    linarith
  · intro h0
    funext i
    fin_cases i <;> simp [D_5_53, h0]

/-! 5.54 A sum of eigenspaces (over distinct eigenvalues) is a direct sum;
in the finite-dimensional case the dimensions add up to at most
{lit}`dim V`. -/

/-- The key fact behind 5.54: vectors from eigenspaces with distinct
eigenvalues that sum to {lit}`0` must each be {lit}`0` (via linear
independence of eigenvectors, 5.11). -/
theorem eq_zero_of_sum_eq_zero_of_mem_eigenspaces (T : V →ₗ[F] V) {m : ℕ}
    {lam : Fin m → F} (hlam : Function.Injective lam) (w : Fin m → V)
    (hw : ∀ i, w i ∈ Module.End.eigenspace T (lam i))
    (hsum : ∑ i, w i = 0) : ∀ i, w i = 0 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨i₀, hi₀⟩ := h
  -- The nonzero terms form a linearly independent family of eigenvectors…
  have hli : LinearIndependent F (fun s : {i // w i ≠ 0} => w s) :=
    Module.End.eigenvectors_linearIndependent' T
      (fun s : {i // w i ≠ 0} => lam s)
      (hlam.comp Subtype.val_injective) _
      (fun s => ⟨hw s, s.2⟩)
  -- …but they sum to {lit}`0`, a nontrivial dependence.
  have hsum' : ∑ s : {i // w i ≠ 0}, w s = 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => w i ≠ 0)
      (fun i => by simp) w]
    rw [Finset.sum_filter_of_ne (fun i _ hne => hne)]
    exact hsum
  have h1 := Fintype.linearIndependent_iff.mp hli
    (fun _ => 1) (by simpa using hsum')
  simpa using h1 ⟨i₀, hi₀⟩

theorem eigenspaces_isDirectSum (T : V →ₗ[F] V) {m : ℕ}
    {lam : Fin m → F} (hlam : Function.Injective lam) :
    IsDirectSum (fun k => Module.End.eigenspace T (lam k)) := by
  intro u v huv
  have hsum : ∑ i, ((u i : V) - (v i : V)) = 0 := by
    rw [Finset.sum_sub_distrib, huv, sub_self]
  have hzero := eq_zero_of_sum_eq_zero_of_mem_eigenspaces T hlam
    (fun i => (u i : V) - (v i : V))
    (fun i => Submodule.sub_mem _ (u i).2 (v i).2) hsum
  funext i
  exact Subtype.ext (sub_eq_zero.mp (hzero i))

/-- Dimension of an independent (finite) supremum of subspaces: the
dimensions add. (Used for 5.54 and 5.55; Axler's 3.94.) -/
private lemma finrank_biSup_eq_sum [Finite F V] {m : ℕ}
    (p : Fin m → Submodule F V) (hp : iSupIndep p) (s : Finset (Fin m)) :
    finrank F (⨆ k ∈ s, p k : Submodule F V) = ∑ k ∈ s, finrank F (p k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have hsup : (⨆ k ∈ insert a s, p k : Submodule F V) =
        p a ⊔ ⨆ k ∈ s, p k :=
      Finset.iSup_insert a s p
    have hdisj : Disjoint (p a) (⨆ k ∈ s, p k : Submodule F V) := by
      refine (hp a).mono_right ?_
      exact iSup_le fun k => iSup_le fun hk =>
        le_iSup_of_le k (le_iSup_of_le (fun h => ha (h ▸ hk)) le_rfl)
    have heq := Submodule.finrank_sup_add_finrank_inf_eq (p a)
      (⨆ k ∈ s, p k : Submodule F V)
    rw [disjoint_iff.mp hdisj, finrank_bot] at heq
    rw [hsup]
    omega

/-- The independence of eigenspaces, in mathlib's {name}`iSupIndep` form
({name}`Module.End.eigenspaces_iSupIndep` composed with an injective
enumeration of eigenvalues). -/
private lemma eigenspaces_iSupIndep' (T : V →ₗ[F] V) {m : ℕ}
    {lam : Fin m → F} (hlam : Function.Injective lam) :
    iSupIndep (fun k => Module.End.eigenspace T (lam k)) :=
  (Module.End.eigenspaces_iSupIndep T).comp hlam

private lemma biSup_univ_eq {m : ℕ} (p : Fin m → Submodule F V) :
    (⨆ k ∈ (Finset.univ : Finset (Fin m)), p k) = ⨆ k, p k := by
  simp

theorem sum_finrank_eigenspaces_le [Finite F V] (T : V →ₗ[F] V) {m : ℕ}
    {lam : Fin m → F} (hlam : Function.Injective lam) :
    ∑ k, finrank F (Module.End.eigenspace T (lam k)) ≤ finrank F V := by
  have h := finrank_biSup_eq_sum _ (eigenspaces_iSupIndep' T hlam)
    Finset.univ
  rw [biSup_univ_eq] at h
  rw [← h]
  exact Submodule.finrank_le _

/-! Conditions for Diagonalizability -/

/-- Helper for 5.55 and 5.62: if finitely many eigenspaces fill up
{lit}`V`, then {lit}`V` has a basis of eigenvectors and {lit}`T` is
diagonalizable. The basis is extracted (2.30) from the concatenation of
bases of the eigenspaces. -/
private lemma isDiagonalizable_of_iSup_eigenspace_eq_top [Finite F V]
    (T : V →ₗ[F] V) {m : ℕ} (mu : Fin m → F)
    (htop : (⨆ k, Module.End.eigenspace T (mu k)) = ⊤) :
    IsDiagonalizable T := by
  classical
  -- Choose a basis of each eigenspace.
  have hbases : ∀ k : Fin m, ∃ (M : ℕ)
      (u : Fin M → Module.End.eigenspace T (mu k)), IsBasis F u :=
    fun k => exists_basis
  choose M u hu using hbases
  -- Concatenate them into one spanning family of eigenvectors.
  set w : Fin (∑ k, M k) → V :=
    (fun p : (k : Fin m) × Fin (M k) => ((u p.1 p.2 : _) : V)) ∘
      ⇑finSigmaFinEquiv.symm with hw_def
  have hw_spans : Spans F w := by
    show Submodule.span F (Set.range w) = ⊤
    rw [hw_def, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
    rw [← htop]
    refine iSup_congr fun k => ?_
    have h1 : Submodule.span F
        (Set.range fun i => ((u k i : _) : V)) =
        Submodule.map (Module.End.eigenspace T (mu k)).subtype
          (Submodule.span F (Set.range (u k))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have h2 : Submodule.span F (Set.range (u k)) = ⊤ := (hu k).2
    rw [h1, h2, Submodule.map_subtype_top]
  -- Extract a basis from this spanning family (2.30): its vectors are
  -- still eigenvectors.
  obtain ⟨n, v, hv, hsub⟩ := exists_basis_of_spans w hw_spans
  refine ⟨n, v, hv, isDiag_matrixOf_of_eigenvectors hv T fun j => ?_⟩
  obtain ⟨p, hp⟩ := hsub ⟨j, rfl⟩
  set q := finSigmaFinEquiv.symm p with hq_def
  refine ⟨mu q.1, ?_⟩
  have hmem : v j ∈ Module.End.eigenspace T (mu q.1) := by
    rw [← hp]
    exact (u q.1 q.2).2
  exact Module.End.mem_eigenspace_iff.mp hmem

/-! 5.55 Conditions equivalent to diagonalizability. With
{lit}`λ₁, …, λₘ` the distinct eigenvalues of {lit}`T`, the following are
equivalent: (a) {lit}`T` is diagonalizable; (b) {lit}`V` has a basis of
eigenvectors; (c) {lit}`V = E(λ₁, T) ⊕ ⋯ ⊕ E(λₘ, T)`;
(d) {lit}`dim V = dim E(λ₁, T) + ⋯ + dim E(λₘ, T)`. -/

theorem tfae_isDiagonalizable [Finite F V] (T : V →ₗ[F] V) {m : ℕ}
    (lam : Fin m → F) (hlam : Function.Injective lam)
    (hall : ∀ mu : F, HasEigenvalue T mu ↔ ∃ k, lam k = mu) :
    [IsDiagonalizable T,
      ∃ (n : ℕ) (v : Fin n → V) (_ : IsBasis F v),
        ∀ j, ∃ mu : F, HasEigenvector T mu (v j),
      (⨆ k, Module.End.eigenspace T (lam k)) = ⊤,
      finrank F V =
        ∑ k, finrank F (Module.End.eigenspace T (lam k))].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨n, v, hv, hA⟩
    refine ⟨n, v, hv, fun j => ⟨matrixOf hv hv T j j,
      Module.End.hasEigenvector_iff_and.mpr ⟨?_, ?_⟩⟩⟩
    · exact hv.1.ne_zero j
    · exact apply_eq_smul_of_isDiag hv T hA j
  tfae_have 2 → 3 := by
    rintro ⟨n, v, hv, hev⟩
    rw [eq_top_iff]
    have hspan : Submodule.span F (Set.range v) = ⊤ := hv.2
    rw [← hspan]
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    obtain ⟨mu, hmu⟩ := hev j
    obtain ⟨hmu_ne, hmu_eq⟩ := Module.End.hasEigenvector_iff_and.mp hmu
    have hmu_ev : HasEigenvalue T mu :=
      Module.End.hasEigenvalue_iff_exists.mpr ⟨v j, hmu_ne, hmu_eq⟩
    obtain ⟨k, rfl⟩ := (hall mu).mp hmu_ev
    exact Submodule.mem_iSup_of_mem k
      (Module.End.mem_eigenspace_iff.mpr hmu_eq)
  tfae_have 3 → 1 :=
    fun htop => isDiagonalizable_of_iSup_eigenspace_eq_top T lam htop
  tfae_have 3 → 4 := by
    intro htop
    have h := finrank_biSup_eq_sum _ (eigenspaces_iSupIndep' T hlam)
      Finset.univ
    rw [biSup_univ_eq, htop] at h
    rw [← h, finrank_top]
  tfae_have 4 → 3 := by
    intro hdim
    have h := finrank_biSup_eq_sum _ (eigenspaces_iSupIndep' T hlam)
      Finset.univ
    rw [biSup_univ_eq] at h
    apply Submodule.eq_top_of_finrank_eq
    rw [h, ← hdim]
  tfae_finish

/-! 5.57 Example: {lit}`T(a, b, c) = (b, c, 0)` on {lit}`F³` has {lit}`0` as
its only eigenvalue, with {lit}`E(0, T) = {(a, 0, 0)}`, so conditions (b),
(c), (d) of 5.55 fail and {lit}`T` is not diagonalizable. -/

noncomputable def T_5_57 : (Fin 3 → F) →ₗ[F] (Fin 3 → F) where
  toFun x := ![x 1, x 2, 0]
  map_add' x y := by
    funext i
    fin_cases i <;> simp
  map_smul' c x := by
    funext i
    fin_cases i <;> simp

-- {lit}`0` is the only eigenvalue of {lit}`T`.
theorem hasEigenvalue_T_5_57 (lam : F) :
    HasEigenvalue (T_5_57 (F := F)) lam ↔ lam = 0 := by
  constructor
  · intro hev
    obtain ⟨w, hw_ne, hw_eq⟩ := Module.End.hasEigenvalue_iff_exists.mp hev
    have h0 := congrFun hw_eq 0
    have h1 := congrFun hw_eq 1
    have h2 := congrFun hw_eq 2
    simp [T_5_57] at h0 h1 h2
    by_contra hlam
    apply hw_ne
    -- {lit}`h0 : w 1 = lam * w 0`, {lit}`h1 : w 2 = lam * w 1`,
    -- {lit}`h2 : lam = 0 ∨ w 2 = 0`.
    have hw2 : w 2 = 0 := h2.resolve_left hlam
    have hw1 : w 1 = 0 := by
      have : lam * w 1 = 0 := by rw [← h1]; exact hw2
      exact (mul_eq_zero.mp this).resolve_left hlam
    have hw0 : w 0 = 0 := by
      have : lam * w 0 = 0 := by rw [← h0]; exact hw1
      exact (mul_eq_zero.mp this).resolve_left hlam
    funext i
    fin_cases i <;> simp [hw0, hw1, hw2]
  · rintro rfl
    refine Module.End.hasEigenvalue_iff_exists.mpr ⟨![1, 0, 0], ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · funext i
      fin_cases i <;> simp [T_5_57]

-- {lit}`E(0, T)` consists exactly of the vectors {lit}`(a, 0, 0)`.
theorem mem_eigenspace_T_5_57 (x : Fin 3 → F) :
    x ∈ Module.End.eigenspace (T_5_57 (F := F)) 0 ↔ x 1 = 0 ∧ x 2 = 0 := by
  rw [Module.End.mem_eigenspace_iff]
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [T_5_57] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [T_5_57, h1, h2]

-- Hence condition (c) of 5.55 fails: with {lit}`0` the only eigenvalue,
-- {lit}`E(0, T) ≠ F³` since {lit}`(0, 1, 0) ∉ E(0, T)`. Thus condition (a)
-- also fails, and {lit}`T` is not diagonalizable.
theorem not_isDiagonalizable_T_5_57 :
    ¬ IsDiagonalizable (T_5_57 (F := F)) := by
  have hall : ∀ mu : F, HasEigenvalue (T_5_57 (F := F)) mu ↔
      ∃ k : Fin 1, (fun _ => (0 : F)) k = mu := by
    intro mu
    rw [hasEigenvalue_T_5_57]
    exact ⟨fun h => ⟨0, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  have h := (tfae_isDiagonalizable (T_5_57 (F := F))
    (fun _ : Fin 1 => (0 : F)) (Function.injective_of_subsingleton _)
    hall).out 0 2
  intro hdiag
  have htop := h.mp hdiag
  have hmem : (![0, 1, 0] : Fin 3 → F) ∈
      Module.End.eigenspace (T_5_57 (F := F)) 0 := by
    rw [← ciSup_const (ι := Fin 1)
      (a := Module.End.eigenspace (T_5_57 (F := F)) 0), htop]
    exact Submodule.mem_top
  exact absurd ((mem_eigenspace_T_5_57 _).mp hmem).1 (by simp)

/-! 5.58 Enough eigenvalues implies diagonalizability: an operator with
{lit}`dim V` distinct eigenvalues is diagonalizable. -/

theorem isDiagonalizable_of_card_eigenvalues [Finite F V] (T : V →ₗ[F] V)
    (lam : Fin (finrank F V) → F) (hlam : Function.Injective lam)
    (hev : ∀ k, HasEigenvalue T (lam k)) :
    IsDiagonalizable T := by
  -- Choose an eigenvector for each eigenvalue; the resulting list is
  -- linearly independent (5.11) of length {lit}`dim V`, hence a basis
  -- (2.38), and it consists of eigenvectors.
  simp only [Module.End.hasEigenvalue_iff_exists] at hev
  choose v hv_ne hv_eq using hev
  have hli : LinearIndependent F v :=
    eigenvectors_linearIndependent T lam hlam v
      fun k => Module.End.hasEigenvector_iff_and.mpr ⟨hv_ne k, hv_eq k⟩
  have hv : IsBasis F v :=
    isBasis_of_linearIndependent_of_card_eq v hli rfl
  exact ⟨_, v, hv, isDiag_matrixOf_of_eigenvectors hv T
    fun j => ⟨lam j, hv_eq j⟩⟩

/-- If {lit}`v` is an eigenvector of {lit}`T` with eigenvalue {lit}`μ`, then
{lit}`Tⁿ v = μⁿ v`. This is the identity that makes diagonalization useful for
computing high powers of an operator. -/
private lemma apply_pow_of_apply_eq_smul {T : V →ₗ[F] V} {v : V} {mu : F}
    (h : T v = mu • v) : ∀ n, (T ^ n) v = mu ^ n • v
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, Module.End.mul_apply, h, map_smul,
      apply_pow_of_apply_eq_smul h n, smul_smul, ← pow_succ']

/-! 5.59 Example: using diagonalization to compute {lit}`T¹⁰⁰`. Define
{lit}`T(x, y, z) = (2x + y, 5y + 3z, 8z)` on {lit}`ℝ³`. Its upper-triangular
matrix has diagonal {lit}`2, 5, 8`, so (5.58) it is diagonalizable with
eigenvectors {lit}`(1,0,0), (1,3,0), (1,6,6)`. Writing
{lit}`(0,0,1) = ⅙(1,0,0) − ⅓(1,3,0) + ⅙(1,6,6)` and applying {lit}`Tⁿ` gives a
closed form for {lit}`Tⁿ(0,0,1)`. -/

noncomputable def T_5_59 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![2 * x 0 + x 1, 5 * x 1 + 3 * x 2, 8 * x 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

-- The three eigenvectors of {lit}`T` (for eigenvalues {lit}`2, 5, 8`).
theorem T_5_59_eigen_2 : T_5_59 ![1, 0, 0] = (2 : ℝ) • ![1, 0, 0] := by
  funext i; fin_cases i <;> simp [T_5_59]
theorem T_5_59_eigen_5 : T_5_59 ![1, 3, 0] = (5 : ℝ) • ![1, 3, 0] := by
  funext i; fin_cases i <;> simp [T_5_59]; all_goals norm_num
theorem T_5_59_eigen_8 : T_5_59 ![1, 6, 6] = (8 : ℝ) • ![1, 6, 6] := by
  funext i; fin_cases i <;> simp [T_5_59]; all_goals norm_num

example : IsDiagonalizable T_5_59 := by
  set b : Fin 3 → (Fin 3 → ℝ) := ![![1, 0, 0], ![1, 3, 0], ![1, 6, 6]]
    with hb_def
  have hli : LinearIndependent ℝ b := by
    rw [hb_def, Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    have h2 := congrFun hg 2
    simp [Fin.sum_univ_three] at h0 h1 h2
    -- back-substitute: {lit}`g 2 = 0`, then {lit}`g 1 = 0`, then {lit}`g 0 = 0`
    have hg2 : g 2 = 0 := by linarith
    have hg1 : g 1 = 0 := by rw [hg2] at h1; linarith
    have hg0 : g 0 = 0 := by rw [hg1, hg2] at h0; linarith
    intro i; fin_cases i <;> assumption
  have hv : IsBasis ℝ b :=
    isBasis_of_linearIndependent_of_card_eq b hli (by simp)
  refine ⟨3, _, hv, isDiag_matrixOf_of_eigenvectors hv T_5_59 ?_⟩
  intro j
  fin_cases j
  · exact ⟨2, T_5_59_eigen_2⟩
  · exact ⟨5, T_5_59_eigen_5⟩
  · exact ⟨8, T_5_59_eigen_8⟩

/-- 5.59, the payoff: a closed form for {lit}`Tⁿ(0,0,1)`, obtained by
decomposing {lit}`(0,0,1)` in the eigenbasis. Specializing to {lit}`n = 100`
recovers Axler's {lit}`T¹⁰⁰(0,0,1)`. -/
theorem pow_apply_T_5_59 (n : ℕ) :
    (T_5_59 ^ n) ![0, 0, 1] =
      ![((2:ℝ) ^ n - 2 * 5 ^ n + 8 ^ n) / 6, 8 ^ n - 5 ^ n, 8 ^ n] := by
  have hdecomp : (![0, 0, 1] : Fin 3 → ℝ) =
      (1/6 : ℝ) • ![1, 0, 0] + (-1/3 : ℝ) • ![1, 3, 0] +
      (1/6 : ℝ) • ![1, 6, 6] := by
    funext i; fin_cases i <;> simp; all_goals norm_num
  rw [hdecomp, map_add, map_add, map_smul, map_smul, map_smul,
    apply_pow_of_apply_eq_smul T_5_59_eigen_2 n,
    apply_pow_of_apply_eq_smul T_5_59_eigen_5 n,
    apply_pow_of_apply_eq_smul T_5_59_eigen_8 n]
  funext i; fin_cases i <;> simp; all_goals ring

/-! 5.60–5.61 Examples: an operator can be shown diagonalizable or not via
the minimal-polynomial criterion 5.62 even when its eigenvalues are not
exactly computable. Because these examples *use* 5.62, they are formalized
just after it below. -/

/-! 5.62 Necessary and sufficient condition for diagonalizability:
{lit}`T` is diagonalizable iff its minimal polynomial is
{lit}`(z − λ₁)⋯(z − λₘ)` for *distinct* {lit}`λ₁, …, λₘ`, here encoded by
indexing over a finite set {lit}`s ⊆ F`. -/

private lemma aeval_X_sub_C_eq (T : V →ₗ[F] V) (a : F) :
    aeval T (Polynomial.X - Polynomial.C a) =
      T - algebraMap F (Module.End F V) a := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

/-- A basis of a subspace {lit}`U`, viewed in {lit}`V`, spans {lit}`U`. -/
private lemma span_coe_basis {U : Submodule F V} {n : ℕ} {u : Fin n → U}
    (hu : IsBasis F u) :
    Submodule.span F (Set.range fun i => (u i : V)) = U := by
  have h : Submodule.span F (Set.range fun i => (u i : V)) =
      (Submodule.span F (Set.range u)).map U.subtype := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h, hu.2, Submodule.map_subtype_top]

/-- The reverse direction of 5.62, by induction on {lit}`m` as in the book:
if {lit}`(T − λ₁I)⋯(T − λₘI) = 0` (5.63) for distinct {lit}`λ₁, …, λₘ`, then
{lit}`T` is diagonalizable. The induction is over the finite set
{lit}`{λ₁, …, λₘ}`, with {lit}`λₘ` the newly inserted element. -/
private lemma isDiagonalizable_of_aeval_prod_X_sub_C [Finite F V]
    (T : V →ₗ[F] V) (s : Finset F)
    (hT : aeval T (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) = 0) :
    IsDiagonalizable T := by
  classical
  induction s using Finset.induction_on generalizing V with
  | empty =>
    -- The empty product is {lit}`1`, so {lit}`I = 0` and {lit}`V = {0}`:
    -- any basis consists of eigenvectors. (The book's base case
    -- {lit}`m = 1` is covered by the inductive step.)
    have h0 : ∀ x : V, x = 0 := fun x => by
      simpa using LinearMap.congr_fun hT x
    obtain ⟨n, v, hv⟩ := exists_basis (F := F) (V := V)
    exact ⟨n, v, hv, isDiag_matrixOf_of_eigenvectors hv T fun j =>
      ⟨0, by rw [h0 (v j)]; simp⟩⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at hT
    set p := ∏ b ∈ s, (Polynomial.X - Polynomial.C b) with hp_def
    set N := aeval T (Polynomial.X - Polynomial.C a) with hN_def
    -- {lit}`range(T − λₘI)` is invariant under {lit}`T` (5.18).
    have hR : InvariantUnder T (range N) :=
      Section_5A.range_aeval_invariant T _
    -- 5.64: {lit}`(T − λ₁I)⋯(T − λₘ₋₁I)u = 0` for {lit}`u ∈ range(T − λₘI)`.
    have hpN : ∀ v, aeval T p (N v) = 0 := by
      intro v
      rw [hN_def, ← LinearMap.comp_apply, ← aeval_mul_eq_comp, mul_comm, hT,
        LinearMap.zero_apply]
    -- Nonzero vectors of {lit}`null(T − λₘI)` are eigenvectors for {lit}`λₘ`.
    have hker : ∀ y, N y = 0 → T y = a • y := by
      intro y hy
      rw [hN_def, aeval_X_sub_C_eq, LinearMap.sub_apply,
        Module.algebraMap_end_apply, sub_eq_zero] at hy
      exact hy
    -- Hence (by the induction hypothesis) {lit}`T|_{range(T − λₘI)}` is
    -- diagonalizable.
    have hpR : aeval hR.restrict p = 0 := by
      apply LinearMap.ext
      rintro ⟨_, v, rfl⟩
      apply Subtype.ext
      rw [Section_5B.aeval_restrict_coe, LinearMap.zero_apply, Submodule.coe_zero]
      exact hpN v
    obtain ⟨n, u, hu, hdu⟩ := ih hR.restrict hpR
    -- {lit}`range(T − λₘI) ∩ null(T − λₘI) = {0}`: for such {lit}`u`,
    -- {lit}`0 = (λₘ − λ₁)⋯(λₘ − λₘ₋₁)u` and the scalar is nonzero.
    have hinf : range N ⊓ ker N = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨⟨v, rfl⟩, hx⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
      rw [Submodule.mem_bot]
      by_contra hne
      have hev : HasEigenvector T a (N v) := by
        exact Module.End.hasEigenvector_iff_and.mpr ⟨hne, hker _ hx⟩
      have h := hpN v
      rw [Module.End.aeval_apply_of_hasEigenvector hev, smul_eq_zero] at h
      refine h.elim (fun hp0 => ?_) hne
      rw [hp_def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hp0
      obtain ⟨b, hb, hb0⟩ := hp0
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at hb0
      exact ha (hb0 ▸ hb)
    -- So {lit}`range(T − λₘI) ⊕ null(T − λₘI) = V`, by dimensions (3.21).
    have hdim := Section_2C.finrank_sup_add_finrank_inf_eq (range N) (ker N)
    have hfund := Section_3B.finrank_ker_add_finrank_range N
    rw [hinf, finrank_bot] at hdim
    have hsup : range N ⊔ ker N = ⊤ :=
      Section_2C.subspace_eq_top_of_finrank_eq _ (by omega)
    -- Adjoin to the eigenvector basis of the range a basis of the null
    -- space; this gives a basis of {lit}`V` consisting of eigenvectors.
    obtain ⟨k, w, hw⟩ := exists_basis (F := F) (V := ker N)
    set z : Fin (n + k) → V :=
      Fin.append (fun i => (u i : V)) (fun i => (w i : V)) with hz_def
    have hz_spans : Spans F z := by
      show Submodule.span F (Set.range z) = ⊤
      rw [eq_top_iff, ← hsup]
      refine sup_le ?_ ?_
      · rw [← span_coe_basis hu]
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨Fin.castAdd k i, by simp [hz_def]⟩
      · rw [← span_coe_basis hw]
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        exact ⟨Fin.natAdd n i, by simp [hz_def]⟩
    have hcard : n + k = finrank F V := by
      rw [Section_2C.isBasis_card_eq_finrank u hu,
        Section_2C.isBasis_card_eq_finrank w hw]
      omega
    have hz := Section_2C.isBasis_of_spans_of_card_eq z hz_spans hcard
    refine ⟨n + k, z, hz, isDiag_matrixOf_of_eigenvectors hz T fun j => ?_⟩
    induction j using Fin.addCases with
    | left i =>
      refine ⟨matrixOf hu hu hR.restrict i i, ?_⟩
      simp only [hz_def, Fin.append_left]
      exact congrArg Subtype.val (apply_eq_smul_of_isDiag hu _ hdu i)
    | right i =>
      refine ⟨a, ?_⟩
      simp only [hz_def, Fin.append_right]
      exact hker _ (LinearMap.mem_ker.mp (w i).2)

theorem isDiagonalizable_iff_minpoly_eq_prod_distinct [Finite F V]
    (T : V →ₗ[F] V) :
    IsDiagonalizable T ↔
      ∃ s : Finset F,
        minpoly F T = ∏ a ∈ s, (Polynomial.X - Polynomial.C a) := by
  classical
  constructor
  · -- Diagonalizable ⟹ the minimal polynomial is the product of
    -- {lit}`(z − λ)` over the distinct diagonal entries {lit}`λ`.
    rintro ⟨n, v, hv, hA⟩
    set s : Finset F := Finset.univ.image fun k => matrixOf hv hv T k k
      with hs_def
    refine ⟨s, ?_⟩
    set q : Polynomial F := ∏ a ∈ s, (Polynomial.X - Polynomial.C a)
      with hq_def
    have hq_monic : q.Monic :=
      Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
    -- {lit}`q(T) = 0` because {lit}`q(T)` kills every basis vector.
    have hq_T : aeval T q = 0 := by
      apply hv.toModuleBasis.ext
      intro j
      rw [LinearMap.zero_apply, hv.toModuleBasis_apply]
      have hmem : matrixOf hv hv T j j ∈ s :=
        Finset.mem_image_of_mem _ (Finset.mem_univ j)
      have hsplit : q = (∏ a ∈ s.erase (matrixOf hv hv T j j),
          (Polynomial.X - Polynomial.C a)) *
          (Polynomial.X - Polynomial.C (matrixOf hv hv T j j)) :=
        (Finset.prod_erase_mul _ _ hmem).symm
      rw [hsplit, aeval_mul_eq_comp, LinearMap.comp_apply]
      have hzero : aeval T (Polynomial.X -
          Polynomial.C (matrixOf hv hv T j j)) (v j) = 0 := by
        rw [aeval_X_sub_C_eq, LinearMap.sub_apply,
          Module.algebraMap_end_apply,
          apply_eq_smul_of_isDiag hv T hA j, sub_self]
      rw [hzero, map_zero]
    have h1 : minpoly F T ∣ q := (aeval_eq_zero_iff_minpoly_dvd T q).mp hq_T
    -- Each diagonal entry is an eigenvalue, hence a zero of the minimal
    -- polynomial; the linear factors are pairwise coprime.
    have h2 : q ∣ minpoly F T := by
      rw [hq_def]
      apply Finset.prod_dvd_of_coprime
      · intro a _ b _ hab
        exact Polynomial.pairwise_coprime_X_sub_C Function.injective_id hab
      · intro a ha
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp ha
        have hev : HasEigenvalue T a := by
          refine Module.End.hasEigenvalue_iff_exists.mpr
            ⟨v j, hv.1.ne_zero j, ?_⟩
          rw [← hj]
          exact apply_eq_smul_of_isDiag hv T hA j
        exact Polynomial.dvd_iff_isRoot.mpr
          ((isEigenvalue_iff_isRoot T a).mp hev)
    exact Polynomial.eq_of_monic_of_associated
      (minpoly.monic (Algebra.IsIntegral.isIntegral T)) hq_monic
      (associated_of_dvd_dvd h1 h2)
  · -- Conversely, {lit}`(T − λ₁I)⋯(T − λₘI) = 0` (5.63); induct on
    -- {lit}`m`.
    rintro ⟨s, hfact⟩
    exact isDiagonalizable_of_aeval_prod_X_sub_C T s
      (hfact ▸ minpoly.aeval F T)

/-- The engine behind Examples 5.60/5.61: over an algebraically closed field,
if {lit}`T` is annihilated by a *separable* polynomial (one with distinct
roots), then {lit}`T` is diagonalizable. Indeed the minimal polynomial divides
that polynomial, so it too is separable; over an algebraically closed field it
splits, hence equals a product of distinct linear factors, and 5.62 applies. -/
private lemma isDiagonalizable_of_separable_aeval [Finite F V] [IsAlgClosed F]
    (T : V →ₗ[F] V) (q : Polynomial F) (hsep : q.Separable)
    (haeval : aeval T q = 0) : IsDiagonalizable T := by
  classical
  rw [isDiagonalizable_iff_minpoly_eq_prod_distinct]
  have hdvd : minpoly F T ∣ q := (aeval_eq_zero_iff_minpoly_dvd _ _).mp haeval
  have hmonic : (minpoly F T).Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hnodup : (minpoly F T).roots.Nodup :=
    Polynomial.nodup_roots (hsep.of_dvd hdvd)
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := minpoly F T)
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _))
  rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul] at h
  refine ⟨(minpoly F T).roots.toFinset, ?_⟩
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr hnodup]
  exact h.symm

/-! 5.60 Example: diagonalizable, but with no known exact eigenvalues. Define
{lit}`T(z₁, …, z₅) = (−3z₅, z₁ + 6z₅, z₂, z₃, z₄)` on {lit}`ℂ⁵`. Its minimal
polynomial is {lit}`z⁵ − 6z + 3` (Example 5.26). No exact expression is known
for its zeros, but they are distinct (Axler verifies this numerically), i.e.
the polynomial is separable; so by 5.62 (via the lemma above) {lit}`T` is
diagonalizable. We take separability — the one numerically-checked fact — as a
hypothesis. -/

noncomputable def T_5_60 : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun z := ![-3 * z 4, z 0 + 6 * z 4, z 1, z 2, z 3]
  map_add' z w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c z := by funext i; fin_cases i <;> simp <;> ring

-- {lit}`z⁵ − 6z + 3` annihilates {lit}`T` (its minimal polynomial, 5.26).
theorem aeval_T_5_60 :
    aeval T_5_60 (Polynomial.X ^ 5 - Polynomial.C 6 * Polynomial.X +
      Polynomial.C 3 : Polynomial ℂ) = 0 := by
  simp only [map_add, map_sub, map_pow, map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C]
  apply LinearMap.ext; intro z; funext j
  fin_cases j <;>
    simp [T_5_60, pow_succ, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.add_apply, Module.algebraMap_end_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.vecHead, Matrix.vecTail]
  all_goals ring

/-- 5.60: {lit}`T` is diagonalizable, given that its minimal polynomial
{lit}`z⁵ − 6z + 3` has distinct roots (is separable). -/
theorem isDiagonalizable_T_5_60
    (hsep : (Polynomial.X ^ 5 - Polynomial.C 6 * Polynomial.X +
      Polynomial.C 3 : Polynomial ℂ).Separable) :
    IsDiagonalizable T_5_60 :=
  isDiagonalizable_of_separable_aeval T_5_60 _ hsep aeval_T_5_60

/-! 5.61 Example: showing that an operator is not diagonalizable. Define
{lit}`T(z₁, z₂, z₃) = (6z₁ + 3z₂ + 4z₃, 6z₂ + 2z₃, 7z₃)` on {lit}`ℂ³`. Its
upper-triangular matrix has diagonal {lit}`6, 6, 7`, so {lit}`(T − 6I)²(T − 7I)
= 0` while {lit}`(T − 6I)(T − 7I) ≠ 0`; hence the minimal polynomial is
{lit}`(z − 6)²(z − 7)`, which is *not* a product of distinct linear factors, so
by 5.62 {lit}`T` is not diagonalizable. -/

noncomputable def T_5_61 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun x := ![6 * x 0 + 3 * x 1 + 4 * x 2, 6 * x 1 + 2 * x 2, 7 * x 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by funext i; fin_cases i <;> simp <;> ring

theorem not_isDiagonalizable_T_5_61 : ¬ IsDiagonalizable T_5_61 := by
  intro hdiag
  obtain ⟨s, hs⟩ :=
    (isDiagonalizable_iff_minpoly_eq_prod_distinct T_5_61).mp hdiag
  -- {lit}`(T − 6I)²(T − 7I) = 0`, so the minimal polynomial divides
  -- {lit}`(X − 6)²(X − 7)`.
  have hA : aeval T_5_61
      ((Polynomial.X - Polynomial.C (6 : ℂ)) ^ 2 *
        (Polynomial.X - Polynomial.C (7 : ℂ))) = 0 := by
    rw [map_mul, map_pow, aeval_X_sub_C_eq, aeval_X_sub_C_eq]
    apply LinearMap.ext; intro x; funext j
    fin_cases j <;>
      simp [T_5_61, pow_two, Module.End.mul_apply, LinearMap.sub_apply,
        Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.vecHead, Matrix.vecTail]
  have hdvd1 : minpoly ℂ T_5_61 ∣
      (Polynomial.X - Polynomial.C (6 : ℂ)) ^ 2 *
        (Polynomial.X - Polynomial.C (7 : ℂ)) :=
    (aeval_eq_zero_iff_minpoly_dvd _ _).mp hA
  -- {lit}`(T − 6I)(T − 7I) ≠ 0`.
  have hC : aeval T_5_61
      ((Polynomial.X - Polynomial.C (6 : ℂ)) * (Polynomial.X - Polynomial.C (7 : ℂ)))
        ≠ 0 := by
    rw [map_mul, aeval_X_sub_C_eq, aeval_X_sub_C_eq]
    intro h
    have hcoord := congrFun (LinearMap.congr_fun h ![0, 1, 0]) 0
    simp [T_5_61, Module.End.mul_apply, LinearMap.sub_apply,
      Module.algebraMap_end_apply, smul_eq_mul,
      Matrix.vecHead, Matrix.vecTail] at hcoord
    norm_num at hcoord
  -- {lit}`6` and {lit}`7` are eigenvalues of {lit}`T`.
  have h6 : HasEigenvalue T_5_61 6 :=
    Module.End.hasEigenvalue_iff_exists.mpr ⟨![1, 0, 0],
      by intro h; have := congrFun h 0; simp at this,
      by funext i; fin_cases i <;> simp [T_5_61]⟩
  have h7 : HasEigenvalue T_5_61 7 :=
    Module.End.hasEigenvalue_iff_exists.mpr ⟨![10, 2, 1],
      by intro h; have := congrFun h 2; simp at this,
      by funext i; fin_cases i <;> simp [T_5_61]; all_goals norm_num⟩
  -- Every eigenvalue lies in {lit}`s` (it is a root of the minimal
  -- polynomial), and every element of {lit}`s` is a root of
  -- {lit}`(X − 6)²(X − 7)`, hence {lit}`6` or {lit}`7`. So {lit}`s = {6, 7}`.
  have hmem : ∀ a : ℂ, HasEigenvalue T_5_61 a → a ∈ s := by
    intro a ha
    have hr : (∏ b ∈ s, (Polynomial.X - Polynomial.C b)).IsRoot a :=
      hs ▸ (isEigenvalue_iff_isRoot T_5_61 a).mp ha
    rw [Polynomial.IsRoot.def, Polynomial.eval_prod] at hr
    obtain ⟨b, hb, hbe⟩ := Finset.prod_eq_zero_iff.mp hr
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hbe
    subst hbe; exact hb
  have hsub : s ⊆ {6, 7} := by
    intro a ha
    have haroot : (minpoly ℂ T_5_61).IsRoot a := by
      rw [hs, Polynomial.IsRoot.def, Polynomial.eval_prod]
      exact Finset.prod_eq_zero ha (by simp)
    have hroot2 : ((Polynomial.X - Polynomial.C (6 : ℂ)) ^ 2 *
        (Polynomial.X - Polynomial.C (7 : ℂ))).IsRoot a := haroot.dvd hdvd1
    rw [Polynomial.IsRoot.def] at hroot2
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hroot2
    rcases mul_eq_zero.mp hroot2 with hh | hh
    · have ha6 : a - 6 = 0 := (pow_eq_zero_iff (by norm_num)).mp hh
      rw [sub_eq_zero] at ha6; simp [ha6]
    · rw [sub_eq_zero] at hh; simp [hh]
  have hs_eq : s = {6, 7} :=
    Finset.Subset.antisymm hsub (by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hmem 6 h6
      · exact hmem 7 h7)
  have hmin : minpoly ℂ T_5_61 =
      (Polynomial.X - Polynomial.C (6 : ℂ)) * (Polynomial.X - Polynomial.C (7 : ℂ)) := by
    rw [hs, hs_eq, Finset.prod_pair (by norm_num : (6 : ℂ) ≠ 7)]
  exact hC (by rw [← hmin]; exact minpoly.aeval ℂ T_5_61)

/-! 5.65 The restriction of a diagonalizable operator to an invariant
subspace is diagonalizable: the minimal polynomial of {lit}`T|_U` divides
the minimal polynomial of {lit}`T` (5.31), hence is also a product of
distinct linear factors, and 5.62 applies. -/

/-- If the minimal polynomial of {lit}`T` divides a product of distinct
linear factors, then it is itself such a product (its zeros are distinct), so
{lit}`T` is diagonalizable by 5.62. -/
theorem isDiagonalizable_of_minpoly_dvd_prod [Finite F V] (T : V →ₗ[F] V)
    (s : Finset F)
    (hdvd : minpoly F T ∣ ∏ a ∈ s, (Polynomial.X - Polynomial.C a)) :
    IsDiagonalizable T := by
  classical
  rw [isDiagonalizable_iff_minpoly_eq_prod_distinct]
  set q := minpoly F T with hq_def
  have hq_monic : q.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hprod_ne : (∏ a ∈ s, (Polynomial.X - Polynomial.C a)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Polynomial.X_sub_C_ne_zero a
  have hq_splits : q.Splits :=
    Polynomial.Splits.of_dvd (Polynomial.Splits.prod fun a _ =>
      Polynomial.Splits.X_sub_C a) hprod_ne hdvd
  -- The roots of {lit}`q` are distinct because they form a sub-multiset of
  -- the (distinct) roots of the product.
  have hroots_le : q.roots ≤
      (∏ a ∈ s, (Polynomial.X - Polynomial.C a)).roots :=
    Polynomial.roots.le_of_dvd hprod_ne hdvd
  have hroots_prod : (∏ a ∈ s, (Polynomial.X - Polynomial.C a)).roots =
      s.val := Polynomial.roots_prod_X_sub_C s
  have hnodup : q.roots.Nodup := by
    rw [hroots_prod] at hroots_le
    exact Multiset.nodup_of_le hroots_le s.nodup
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := q) (Polynomial.splits_iff_card_roots.mp hq_splits)
  rw [hq_monic.leadingCoeff, Polynomial.C_1, one_mul] at h
  refine ⟨q.roots.toFinset, ?_⟩
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr hnodup]
  exact h.symm

theorem isDiagonalizable_restrict [Finite F V] (T : V →ₗ[F] V)
    (hT : IsDiagonalizable T) (U : Submodule F V)
    (hU : InvariantUnder T U) : IsDiagonalizable hU.restrict := by
  obtain ⟨s, hs⟩ := (isDiagonalizable_iff_minpoly_eq_prod_distinct T).mp hT
  exact isDiagonalizable_of_minpoly_dvd_prod _ s
    (hs ▸ minpoly_restrict_dvd T U hU)

/-! Gershgorin Disk Theorem -/

/-! 5.66 Definition: Gershgorin disks (over {lit}`ℂ`). -/

/-- The {lit}`j`-th *Gershgorin disk* of {lit}`T` with respect to a basis:
the closed disk centered at the diagonal entry {lit}`A_{j,j}` with radius
the sum of the absolute values of the other entries of row {lit}`j`. -/
noncomputable def gershgorinDisk {V : Type*} [AddCommGroup V] [Module ℂ V]
    {n : ℕ} {v : Fin n → V} (hv : IsBasis ℂ v) (T : V →ₗ[ℂ] V) (j : Fin n) :
    Set ℂ :=
  {z | ‖z - matrixOf hv hv T j j‖ ≤
    ∑ k ∈ Finset.univ.erase j, ‖matrixOf hv hv T j k‖}

/-! 5.67 Gershgorin disk theorem: each eigenvalue of {lit}`T` lies in some
Gershgorin disk. (mathlib's matrix version is
{name}`eigenvalue_mem_ball`.) -/

theorem gershgorin {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    {n : ℕ} {v : Fin n → V} (hv : IsBasis ℂ v) (T : V →ₗ[ℂ] V) {lam : ℂ}
    (hlam : HasEigenvalue T lam) :
    ∃ j, lam ∈ gershgorinDisk hv T j := by
  classical
  obtain ⟨w, hw_ne, hw_eq⟩ := Module.End.hasEigenvalue_iff_exists.mp hlam
  -- Write {lit}`c k` for the coefficients of the eigenvector {lit}`w` in
  -- the basis (5.68). Comparing coefficients in {lit}`λw = Tw` (5.69/5.70)
  -- gives {lit}`λ cⱼ = ∑ₖ A_{j,k} cₖ` for every {lit}`j`.
  have hkey : ∀ j, lam * hv.toModuleBasis.repr w j =
      ∑ k, matrixOf hv hv T j k * hv.toModuleBasis.repr w k := by
    intro j
    have hTw : T w = ∑ k, hv.toModuleBasis.repr w k • T (hv.toModuleBasis k) := by
      conv_lhs => rw [← hv.toModuleBasis.sum_repr w]
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => map_smul T _ _
    have h1 : hv.toModuleBasis.repr (T w) j =
        ∑ k, hv.toModuleBasis.repr w k * matrixOf hv hv T j k := by
      rw [hTw, map_sum, Finsupp.finset_sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul, matrixOf_apply,
        hv.toModuleBasis_apply]
    have h3 : hv.toModuleBasis.repr (T w) j =
        lam * hv.toModuleBasis.repr w j := by
      rw [hw_eq, map_smul, Finsupp.smul_apply, smul_eq_mul]
    rw [← h3, h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- Choose {lit}`j` with {lit}`|cⱼ|` maximal; then {lit}`cⱼ ≠ 0` because
  -- {lit}`w ≠ 0`.
  have hc_ne : ∃ k, hv.toModuleBasis.repr w k ≠ 0 := by
    by_contra h
    push Not at h
    apply hw_ne
    have hzero : hv.toModuleBasis.repr w = 0 := Finsupp.ext fun k => h k
    exact (LinearEquiv.map_eq_zero_iff hv.toModuleBasis.repr).mp hzero
  obtain ⟨k₀, hk₀⟩ := hc_ne
  obtain ⟨j, -, hj_max⟩ := Finset.exists_max_image Finset.univ
    (fun k => ‖hv.toModuleBasis.repr w k‖) ⟨k₀, Finset.mem_univ k₀⟩
  have hcj_pos : 0 < ‖hv.toModuleBasis.repr w j‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hk₀) (hj_max k₀ (Finset.mem_univ k₀))
  refine ⟨j, ?_⟩
  rw [gershgorinDisk, Set.mem_setOf_eq]
  -- Subtract {lit}`A_{j,j}cⱼ` from both sides of 5.69 and estimate.
  have hsplit : lam * hv.toModuleBasis.repr w j -
      matrixOf hv hv T j j * hv.toModuleBasis.repr w j =
      ∑ k ∈ Finset.univ.erase j,
        matrixOf hv hv T j k * hv.toModuleBasis.repr w k := by
    rw [hkey j, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    ring
  have hnorm : ‖lam - matrixOf hv hv T j j‖ * ‖hv.toModuleBasis.repr w j‖ ≤
      (∑ k ∈ Finset.univ.erase j, ‖matrixOf hv hv T j k‖) *
        ‖hv.toModuleBasis.repr w j‖ := by
    calc ‖lam - matrixOf hv hv T j j‖ * ‖hv.toModuleBasis.repr w j‖
        = ‖(lam - matrixOf hv hv T j j) * hv.toModuleBasis.repr w j‖ :=
          (norm_mul _ _).symm
      _ = ‖∑ k ∈ Finset.univ.erase j,
            matrixOf hv hv T j k * hv.toModuleBasis.repr w k‖ := by
          rw [sub_mul, hsplit]
      _ ≤ ∑ k ∈ Finset.univ.erase j,
            ‖matrixOf hv hv T j k * hv.toModuleBasis.repr w k‖ :=
          norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.univ.erase j,
            ‖matrixOf hv hv T j k‖ * ‖hv.toModuleBasis.repr w j‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hj_max k (Finset.mem_univ k))
            (norm_nonneg _)
      _ = (∑ k ∈ Finset.univ.erase j, ‖matrixOf hv hv T j k‖) *
            ‖hv.toModuleBasis.repr w j‖ :=
          (Finset.sum_mul _ _ _).symm
  exact le_of_mul_le_mul_right hnorm hcj_pos

/-! # Exercises -/

/-- 5D.1 (a) For {lit}`V` complex: {lit}`T⁴ = I` implies {lit}`T` is
diagonalizable. -/
theorem exercise_5D_1a {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (h : T ^ 4 = LinearMap.id) :
    IsDiagonalizable T := by
  sorry

/-- 5D.1 (b) {lit}`T⁴ = T` also implies diagonalizable. -/
theorem exercise_5D_1b {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (h : T ^ 4 = T) :
    IsDiagonalizable T := by
  sorry

/-- 5D.1 (c) But {lit}`T⁴ = T²` does not. -/
theorem exercise_5D_1c :
    ∃ T : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ),
      T ^ 4 = T ^ 2 ∧ ¬ IsDiagonalizable T := by
  sorry

/-- 5D.2 If {lit}`T` has a diagonal matrix {lit}`A` with respect to some
basis, then {lit}`λ` appears on the diagonal of {lit}`A` exactly
{lit}`dim E(λ, T)` times. -/
theorem exercise_5D_2 [Finite F V] {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (T : V →ₗ[F] V)
    (hA : (matrixOf hv hv T).IsDiag) (lam : F) :
    Nat.card {k : Fin n // matrixOf hv hv T k k = lam} =
      finrank F (Module.End.eigenspace T lam) := by
  sorry

/-- 5D.3 -/
theorem exercise_5D_3 [Finite F V] (T : V →ₗ[F] V)
    (hT : IsDiagonalizable T) : IsCompl (ker T) (range T) := by
  sorry

/-- 5D.4 -/
theorem exercise_5D_4 [Finite F V] (T : V →ₗ[F] V) :
    [IsCompl (ker T) (range T),
      ker T ⊔ range T = ⊤,
      ker T ⊓ range T = ⊥].TFAE := by
  sorry

/-- 5D.5 For {lit}`V` complex: {lit}`T` is diagonalizable iff
{lit}`V = null(T − λI) ⊕ range(T − λI)` for every {lit}`λ ∈ ℂ`. -/
theorem exercise_5D_5 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    IsDiagonalizable T ↔
      ∀ γ : ℂ, IsCompl (ker (T - γ • (LinearMap.id : V →ₗ[ℂ] V)))
        (range (T - γ • (LinearMap.id : V →ₗ[ℂ] V))) := by
  sorry

/-- 5D.6 -/
theorem exercise_5D_6 (T : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ))
    (h : finrank ℝ (Module.End.eigenspace T 8) = 4) :
    IsInvertible (T - 2 • LinearMap.id) ∨
      IsInvertible (T - 6 • LinearMap.id) := by
  sorry

/-- 5D.7 -/
theorem exercise_5D_7 (T : V →ₗ[F] V) (hT : IsInvertible T) (γ : F)
    (hγ : γ ≠ 0) :
    Module.End.eigenspace T γ = Module.End.eigenspace hT.inv γ⁻¹ := by
  sorry

/-- 5D.8 -/
theorem exercise_5D_8 [Finite F V] (T : V →ₗ[F] V) {m : ℕ}
    (lam : Fin m → F) (hlam : Function.Injective lam)
    (hnz : ∀ k, lam k ≠ 0) :
    ∑ k, finrank F (Module.End.eigenspace T (lam k)) ≤
      finrank F (range T) := by
  sorry

/-- 5D.9 -/
theorem exercise_5D_9 [CharZero F] (R T : (Fin 3 → F) →ₗ[F] (Fin 3 → F))
    (hR : ∀ γ : F, HasEigenvalue R γ ↔ γ = 2 ∨ γ = 6 ∨ γ = 7)
    (hT : ∀ γ : F, HasEigenvalue T γ ↔ γ = 2 ∨ γ = 6 ∨ γ = 7) :
    ∃ (S : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) (hS : IsInvertible S),
      R = hS.inv ∘ₗ T ∘ₗ S := by
  sorry

/-- 5D.10 -/
theorem exercise_5D_10 [CharZero F] :
    ∃ R T : (Fin 4 → F) →ₗ[F] (Fin 4 → F),
      (∀ γ : F, HasEigenvalue R γ ↔ γ = 2 ∨ γ = 6 ∨ γ = 7) ∧
      (∀ γ : F, HasEigenvalue T γ ↔ γ = 2 ∨ γ = 6 ∨ γ = 7) ∧
      ¬ ∃ (S : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) (hS : IsInvertible S),
        R = hS.inv ∘ₗ T ∘ₗ S := by
  sorry

/-- 5D.11 -/
theorem exercise_5D_11 :
    ∃ T : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ),
      HasEigenvalue T 6 ∧ HasEigenvalue T 7 ∧ ¬ IsDiagonalizable T := by
  sorry

/-- 5D.12 -/
theorem exercise_5D_12 (T : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ))
    (h6 : HasEigenvalue T 6) (h7 : HasEigenvalue T 7)
    (hnd : ¬ IsDiagonalizable T) :
    ∃ z : Fin 3 → ℂ, T z = ![6 + 8 * z 0, 7 + 8 * z 1, 13 + 8 * z 2] := by
  sorry

/-- 5D.13 -/
theorem exercise_5D_13 {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hA : A.IsDiag) (hdist : Function.Injective fun k => A k k) :
    A * B = B * A ↔ B.IsDiag := by
  sorry

/-- 5D.14 (a) The vector space is part of the example: exhibit *some*
finite-dimensional complex vector space with an operator {lit}`T` such that
{lit}`T²` is diagonalizable but {lit}`T` is not. -/
theorem exercise_5D_14a :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V)
      (T : V →ₗ[ℂ] V),
      IsDiagonalizable (T ∘ₗ T) ∧ ¬ IsDiagonalizable T := by
  sorry

/-- 5D.14 (b) For invertible {lit}`T` on a complex vector space:
{lit}`T` is diagonalizable iff {lit}`Tᵏ` is. -/
theorem exercise_5D_14b {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) (hT : IsInvertible T) (k : ℕ)
    (hk : 0 < k) :
    IsDiagonalizable T ↔ IsDiagonalizable (T ^ k) := by
  sorry

/-- 5D.15 Diagonalizability via the minimal polynomial and its
derivative. -/
theorem exercise_5D_15 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    [IsDiagonalizable T,
      ¬ ∃ γ : ℂ, (Polynomial.X - Polynomial.C γ) ^ 2 ∣ minpoly ℂ T,
      ∀ γ : ℂ, ¬ ((minpoly ℂ T).IsRoot γ ∧
        (minpoly ℂ T).derivative.IsRoot γ),
      IsCoprime (minpoly ℂ T) (minpoly ℂ T).derivative].TFAE := by
  sorry

/-- 5D.16 For diagonalizable {lit}`T` with distinct eigenvalues
{lit}`λ₁, …, λₘ`: a subspace {lit}`U` is invariant under {lit}`T` iff there
exist subspaces {lit}`U₁, …, Uₘ` with {lit}`Uₖ ⊆ E(λₖ, T)` for each {lit}`k`
and {lit}`U = U₁ ⊕ ⋯ ⊕ Uₘ`. -/
theorem exercise_5D_16 [Finite F V] (T : V →ₗ[F] V)
    (hT : IsDiagonalizable T) {m : ℕ} (lam : Fin m → F)
    (hlam : Function.Injective lam)
    (hall : ∀ mu : F, HasEigenvalue T mu ↔ ∃ k, lam k = mu)
    (U : Submodule F V) :
    InvariantUnder T U ↔
      ∃ W : Fin m → Submodule F V,
        (∀ k, W k ≤ Module.End.eigenspace T (lam k)) ∧
        IsDirectSum W ∧ U = ⨆ k, W k := by
  sorry

/-- 5D.17 {lit}`ℒ(V)` has a basis consisting of diagonalizable
operators. -/
theorem exercise_5D_17 [Finite F V] :
    ∃ (N : ℕ) (E : Fin N → (V →ₗ[F] V)) (_ : IsBasis F E),
      ∀ i, IsDiagonalizable (E i) := by
  sorry

/-- 5D.18 If {lit}`T` is diagonalizable and {lit}`U` is invariant under
{lit}`T`, then the quotient operator {lit}`T/U` is diagonalizable. -/
theorem exercise_5D_18 [Finite F V] (T : V →ₗ[F] V)
    (hT : IsDiagonalizable T) (U : Submodule F V)
    (hU : InvariantUnder T U) :
    IsDiagonalizable (exercise_5A_38_quotient_op T U hU) := by
  sorry

/-- 5D.19 Prove or give a counterexample: for a finite-dimensional complex
vector space {lit}`V`, if {lit}`T ∈ ℒ(V)` has an invariant subspace {lit}`U`
with {lit}`T|_U` and {lit}`T/U` both diagonalizable, then {lit}`T` is
diagonalizable. -/
def exercise_5D_19 :
    Decidable (∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
      (T : V →ₗ[ℂ] V) (U : Submodule ℂ V) (hU : InvariantUnder T U),
      IsDiagonalizable hU.restrict →
      IsDiagonalizable (exercise_5A_38_quotient_op T U hU) →
      IsDiagonalizable T) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 5D.20 {lit}`T` is diagonalizable iff the dual operator {lit}`T′` is
diagonalizable. -/
theorem exercise_5D_20 [Finite F V] (T : V →ₗ[F] V) :
    IsDiagonalizable T ↔ IsDiagonalizable T.dualMap := by
  sorry

/-! 5D.21 The Fibonacci sequence and the operator
{lit}`T(x, y) = (y, x + y)` on {lit}`ℝ²`. We use mathlib's
{name}`Nat.fib`. -/

noncomputable def T_fib : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun x := ![x 1, x 0 + x 1]
  map_add' x y := by
    funext i
    fin_cases i
    · simp
    · simp
      ring
  map_smul' c x := by
    funext i
    fin_cases i
    · simp
    · simp
      ring

/-- 5D.21 (a) {lit}`Tⁿ(0, 1) = (Fₙ, F_{n+1})`. -/
theorem exercise_5D_21a (n : ℕ) :
    (T_fib ^ n) ![0, 1] = ![(Nat.fib n : ℝ), (Nat.fib (n + 1) : ℝ)] := by
  sorry

/-- 5D.21 (b) The set of eigenvalues to be found. -/
def eigenvalues_5D_21b : Set ℝ := sorry

/-- 5D.21 (b) Find the eigenvalues of {lit}`T`. -/
theorem exercise_5D_21b (γ : ℝ) :
    HasEigenvalue T_fib γ ↔ γ ∈ eigenvalues_5D_21b := by
  sorry

/-- 5D.21 (c) The basis to be found. -/
def basis_5D_21c : Fin 2 → (Fin 2 → ℝ) := sorry

/-- 5D.21 (c) Find a basis of {lit}`ℝ²` consisting of eigenvectors of
{lit}`T`. -/
theorem exercise_5D_21c :
    IsBasis ℝ basis_5D_21c ∧
      ∀ i, ∃ γ : ℝ, HasEigenvector T_fib γ (basis_5D_21c i) := by
  sorry

/-- 5D.21 (d) Binet's formula. -/
theorem exercise_5D_21d (n : ℕ) :
    (Nat.fib n : ℝ) = (((1 + Real.sqrt 5) / 2) ^ n -
      ((1 - Real.sqrt 5) / 2) ^ n) / Real.sqrt 5 := by
  sorry

/-- 5D.21 (e) {lit}`Fₙ` is the integer nearest to
{lit}`(1/√5)·((1 + √5)/2)ⁿ`. -/
theorem exercise_5D_21e (n : ℕ) :
    |(Nat.fib n : ℝ) - ((1 + Real.sqrt 5) / 2) ^ n / Real.sqrt 5| < 1 / 2 := by
  sorry

/-- 5D.22 Diagonally dominant matrices give invertible operators. -/
theorem exercise_5D_22 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] {n : ℕ} {v : Fin n → V} (hv : IsBasis ℂ v)
    (T : V →ₗ[ℂ] V)
    (h : ∀ j, ∑ k ∈ Finset.univ.erase j, ‖matrixOf hv hv T j k‖ <
      ‖matrixOf hv hv T j j‖) :
    IsInvertible T := by
  sorry

/-- 5D.23 The Gershgorin disk theorem holds with column sums in place of
row sums. -/
theorem exercise_5D_23 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] {n : ℕ} {v : Fin n → V} (hv : IsBasis ℂ v)
    (T : V →ₗ[ℂ] V) {lam : ℂ} (hlam : HasEigenvalue T lam) :
    ∃ j, ‖lam - matrixOf hv hv T j j‖ ≤
      ∑ k ∈ Finset.univ.erase j, ‖matrixOf hv hv T k j‖ := by
  sorry

end LADR.Section_5D
