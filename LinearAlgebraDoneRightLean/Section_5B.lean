import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.PowerBasis
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_3E
import LinearAlgebraDoneRightLean.Chapter_4
import LinearAlgebraDoneRightLean.Section_5A
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5B: The Minimal Polynomial
-/

namespace LADR.Section_5B

open LADR.Section_2B (IsBasis)
open LADR.Section_3D (IsInvertible)
open Module.End (HasEigenvalue HasEigenvector)
open LADR.Section_5A (InvariantUnder
  tfae_isEigenvalue aeval_mul_eq_comp aeval_comp_comm aeval_comm_self
  ker_aeval_invariant range_aeval_invariant)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

universe u

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! Existence of Eigenvalues on Complex Vector Spaces -/

/-! 5.19 Existence of eigenvalues -/

/-- Helper for 5.19: if some nonzero polynomial annihilates a nonzero vector,
then {lit}`T` has an eigenvalue. Induction on the degree, peeling off one
root at a time. -/
private lemma exists_eigenvalue_aux {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) :
    ∀ (n : ℕ) (p : Polynomial ℂ), p.natDegree = n → p ≠ 0 →
      ∀ v : V, v ≠ 0 → aeval T p v = 0 → ∃ lam : ℂ, HasEigenvalue T lam := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hdeg hp v hv hpv
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- A nonzero constant polynomial cannot annihilate {lit}`v ≠ 0`.
      exfalso
      subst h0
      have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hc0 : p.coeff 0 ≠ 0 := fun h => hp (by rw [hC, h, map_zero])
      rw [hC, Polynomial.aeval_C] at hpv
      have hsmul : p.coeff 0 • v = 0 := by
        rwa [Module.algebraMap_end_apply] at hpv
      rcases smul_eq_zero.mp hsmul with h | h
      · exact hc0 h
      · exact hv h
    · -- {lit}`p` has positive degree, so FTA provides a root {lit}`λ`.
      have hdegpos : 0 < p.degree :=
        Polynomial.natDegree_pos_iff_degree_pos.mp (hdeg ▸ hpos)
      obtain ⟨lam, hlam⟩ := Complex.exists_root hdegpos
      obtain ⟨q, hpq⟩ := Polynomial.dvd_iff_isRoot.mpr hlam
      have hq : q ≠ 0 := fun h => hp (by rw [hpq, h, mul_zero])
      have hqdeg : q.natDegree = n - 1 := by
        have hmul := Polynomial.natDegree_mul
          (Polynomial.X_sub_C_ne_zero lam) hq
        rw [← hpq, Polynomial.natDegree_X_sub_C, hdeg] at hmul
        omega
      by_cases hqv : aeval T q v = 0
      · exact ih (n - 1) (by omega) q hqdeg hq v hv hqv
      · -- {lit}`(T − λI)(q(T)v) = p(T)v = 0`, so {lit}`q(T)v` is an
        -- eigenvector for {lit}`λ`.
        refine ⟨lam, Module.End.hasEigenvalue_iff_exists.mpr
          ⟨aeval T q v, hqv, ?_⟩⟩
        rw [hpq, aeval_mul_eq_comp] at hpv
        have h2 : T (aeval T q v) - lam • aeval T q v = 0 := by
          have h3 : aeval T (Polynomial.X - Polynomial.C lam)
              (aeval T q v) = 0 := hpv
          rwa [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
            LinearMap.sub_apply, Module.algebraMap_end_apply] at h3
        rw [sub_eq_zero] at h2
        exact h2

theorem exists_eigenvalue {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] V) :
    ∃ γ : ℂ, HasEigenvalue T γ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set n := finrank ℂ V with hn
  -- {lit}`v, Tv, …, Tⁿv` has length {lit}`n + 1`, hence is linearly
  -- dependent (2.22).
  have hdep : ¬ LinearIndependent ℂ (fun i : Fin (n + 1) => (T ^ (i : ℕ)) v) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, ← hn] at hcard
    omega
  obtain ⟨g, hsum, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  -- Package the dependence as a nonzero polynomial with {lit}`p(T)v = 0`.
  set p : Polynomial ℂ := ∑ i : Fin (n + 1), Polynomial.monomial (i : ℕ) (g i)
    with hp_def
  have hp_coeff : ∀ j : Fin (n + 1), p.coeff (j : ℕ) = g j := by
    intro j
    rw [hp_def, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single j]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro i _ hij
      rw [Polynomial.coeff_monomial, if_neg (fun h => hij (Fin.val_injective h))]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hp_ne : p ≠ 0 := fun h =>
    hi₀ (by rw [← hp_coeff i₀, h, Polynomial.coeff_zero])
  have hpv : aeval T p v = 0 := by
    rw [hp_def, map_sum, LinearMap.sum_apply, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply]
  exact exists_eigenvalue_aux T p.natDegree p rfl hp_ne v hv hpv

/-! 5.20 -/

noncomputable def T_5_20 : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun p := Polynomial.X * p
  map_add' p q := mul_add _ p q
  map_smul' a p := by
    simp only [RingHom.id_apply]
    exact mul_smul_comm a _ p

example : ∀ γ : ℂ, ¬ HasEigenvalue T_5_20 γ := by
  intro γ hev
  obtain ⟨p, hp, hXp⟩ := Module.End.hasEigenvalue_iff_exists.mp hev
  have hXp' : Polynomial.X * p = γ • p := by
    simpa [T_5_20] using hXp
  rcases eq_or_ne γ 0 with rfl | hlam
  · rw [zero_smul] at hXp'
    rcases mul_eq_zero.mp hXp' with h | h
    · exact Polynomial.X_ne_zero h
    · exact hp h
  · have hdeg := congrArg Polynomial.natDegree hXp'
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero hp,
      Polynomial.natDegree_X, Polynomial.smul_eq_C_mul,
      Polynomial.natDegree_C_mul hlam] at hdeg
    omega

/-! Eigenvalues and the Minimal Polynomial -/

/-! 5.21 Definition: monic polynomial — mathlib's {name}`Polynomial.Monic`
(highest-degree coefficient equals {lit}`1`). For example,
{lit}`2 + 9z² + z⁷` is monic. -/

example (p : Polynomial F) : p.Monic ↔ p.leadingCoeff = 1 := Iff.rfl

example : (Polynomial.X ^ 7 + Polynomial.C 9 * Polynomial.X ^ 2 +
    Polynomial.C 2 : Polynomial ℂ).Monic := by
  monicity!

/-! 5.22 Existence, uniqueness, and degree of minimal polynomial.

In mathlib the minimal polynomial of {lit}`T` is {name}`minpoly`
({lit}`minpoly F T`), available because a finite-dimensional {lit}`V` makes
every operator integral over {lit}`F` ({name}`Module.End.isIntegral`). We
record existence and uniqueness here; the degree bound {lit}`deg p ≤ dim V`
is Axler's 5.23, proved below ({lit}`minpoly_natDegree_le`) by induction on
dimension once the restriction {lit}`T|_U` to an invariant subspace is
available. -/

theorem exists_unique_minimal_polynomial [Finite F V] (T : V →ₗ[F] V) :
    ∃! p : Polynomial F, p.Monic ∧ aeval T p = 0 ∧
      ∀ q : Polynomial F, q.Monic → aeval T q = 0 → p.degree ≤ q.degree := by
  have hT : IsIntegral F T := Algebra.IsIntegral.isIntegral T
  refine ⟨minpoly F T,
    ⟨minpoly.monic hT, minpoly.aeval F T, fun q hq hq0 => minpoly.min F T hq hq0⟩,
    ?_⟩
  rintro p ⟨hmonic, haeval, hmin⟩
  exact minpoly.unique F T hmonic haeval hmin

/-! Restriction of an operator to an invariant subspace, and powers and
polynomials of the restriction. -/

theorem restrict_pow_coe {T : V →ₗ[F] V} {U : Submodule F V}
    (h : InvariantUnder T U) (n : ℕ) (u : U) :
    (((h.restrict ^ n) u : U) : V) = (T ^ n) (u : V) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply,
      ih (h.restrict u)]
    congr 1

theorem aeval_restrict_coe {T : V →ₗ[F] V} {U : Submodule F V}
    (h : InvariantUnder T U) (p : Polynomial F) (u : U) :
    (((aeval h.restrict p) u : U) : V) = aeval T p (u : V) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      Submodule.coe_add, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, restrict_pow_coe h n u]

/-! 5.23 Degree of the minimal polynomial: {lit}`deg(minpoly T) ≤ dim V`. -/

/-- Package a coefficient vector {lit}`g : Fin N → F` as the polynomial
{lit}`∑ᵢ gᵢ zⁱ`. -/
private noncomputable def polyOfCoeffs {N : ℕ} (g : Fin N → F) : Polynomial F :=
  ∑ i : Fin N, Polynomial.monomial (i : ℕ) (g i)

private lemma polyOfCoeffs_coeff {N : ℕ} (g : Fin N → F) (j : Fin N) :
    (polyOfCoeffs g).coeff (j : ℕ) = g j := by
  unfold polyOfCoeffs
  rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro i _ hij
    rw [Polynomial.coeff_monomial, if_neg (fun h => hij (Fin.val_injective h))]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma polyOfCoeffs_natDegree_le {N : ℕ} (g : Fin N → F) :
    (polyOfCoeffs g).natDegree ≤ N - 1 := by
  unfold polyOfCoeffs
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  have hi : (i : ℕ) ≤ N - 1 := by have := i.2; omega
  exact le_trans (Polynomial.natDegree_monomial_le (g i)) hi

private lemma polyOfCoeffs_aeval {W : Type*} [AddCommGroup W] [Module F W]
    {N : ℕ} (S : W →ₗ[F] W) (g : Fin N → F) (v : W) :
    aeval S (polyOfCoeffs g) v = ∑ i : Fin N, g i • (S ^ (i : ℕ)) v := by
  unfold polyOfCoeffs
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]

/-- Axler's 5.23, stated for an arbitrary operator on a space of a fixed
dimension {lit}`n` (the induction hypothesis). -/
private lemma minpoly_natDegree_le_aux (n : ℕ) (W : Type u) [AddCommGroup W]
    [Module F W] [Module.Finite F W] (hW : finrank F W = n) (S : W →ₗ[F] W) :
    ∃ p : Polynomial F, p.Monic ∧ aeval S p = 0 ∧ p.natDegree ≤ n := by
  induction n using Nat.strong_induction_on generalizing W with
  | _ n ih =>
    classical
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- {lit}`dim W = 0`: the constant polynomial {lit}`1` annihilates the
      -- (subsingleton) space.
      subst h0
      haveI : Subsingleton W := (Module.finrank_eq_zero_iff_of_free F W).mp hW
      exact ⟨1, Polynomial.monic_one, Subsingleton.elim _ _, by simp⟩
    · haveI : Nontrivial W :=
        Module.nontrivial_of_finrank_pos (R := F) (by omega)
      obtain ⟨u, hu⟩ := exists_ne (0 : W)
      -- A monic polynomial of degree ≤ n annihilates {lit}`u`, from the
      -- linear dependence of {lit}`u, Su, …, Sⁿu` (length {lit}`n + 1`).
      obtain ⟨q0, hq0_monic, hq0_deg, hq0_aeval⟩ :
          ∃ q0 : Polynomial F, q0.Monic ∧ q0.natDegree ≤ n ∧ aeval S q0 u = 0 := by
        have hdep : ¬ LinearIndependent F
            (fun i : Fin (n + 1) => (S ^ (i : ℕ)) u) := by
          intro hli
          have hcard := hli.fintype_card_le_finrank
          rw [Fintype.card_fin, hW] at hcard
          omega
        obtain ⟨g, hsum, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
        have hg_ne : polyOfCoeffs g ≠ 0 := fun h =>
          hi₀ (by rw [← polyOfCoeffs_coeff g i₀, h, Polynomial.coeff_zero])
        have hg_aeval : aeval S (polyOfCoeffs g) u = 0 := by
          rw [polyOfCoeffs_aeval]; exact hsum
        have hg_deg : (polyOfCoeffs g).natDegree ≤ n := by
          have := polyOfCoeffs_natDegree_le g; omega
        refine ⟨polyOfCoeffs g * Polynomial.C (polyOfCoeffs g).leadingCoeff⁻¹,
          Polynomial.monic_mul_leadingCoeff_inv hg_ne, ?_, ?_⟩
        · rw [Polynomial.natDegree_mul hg_ne (Polynomial.C_ne_zero.mpr
            (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg_ne))),
            Polynomial.natDegree_C, add_zero]
          exact hg_deg
        · simp only [map_mul, Module.End.mul_apply, Polynomial.aeval_C,
            Module.algebraMap_end_apply, map_smul, hg_aeval, smul_zero]
      -- The *smallest* degree of a monic annihilator of {lit}`u`.
      have hExists : ∃ d, ∃ q : Polynomial F,
          q.Monic ∧ q.natDegree = d ∧ aeval S q u = 0 :=
        ⟨q0.natDegree, q0, hq0_monic, rfl, hq0_aeval⟩
      set m := Nat.find hExists with hm
      obtain ⟨q, hqmonic, hqdeg, hqu⟩ := Nat.find_spec hExists
      rw [← hm] at hqdeg
      have hm_le : m ≤ n :=
        le_trans (Nat.find_le ⟨q0, hq0_monic, rfl, hq0_aeval⟩) hq0_deg
      -- {lit}`m ≥ 1`: a degree-0 monic is {lit}`1`, which cannot kill {lit}`u`.
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm0 | h
        · exfalso
          have hq1 : q = 1 := (hqmonic.natDegree_eq_zero).mp (by rw [hqdeg, hm0])
          rw [hq1, map_one] at hqu
          simp only [Module.End.one_apply] at hqu
          exact hu hqu
        · exact h
      -- {lit}`q(S)` commutes with powers of {lit}`S`.
      have hcomm : ∀ (j : ℕ) (x : W),
          aeval S q ((S ^ j) x) = (S ^ j) (aeval S q x) := by
        intro j x
        have h := aeval_comp_comm S q (Polynomial.X ^ j)
        rw [map_pow, Polynomial.aeval_X] at h
        exact LinearMap.congr_fun h x
      -- {lit}`u, Su, …, S^{m-1}u` are linearly independent.
      have hli : LinearIndependent F (fun j : Fin m => (S ^ (j : ℕ)) u) := by
        by_contra hdep
        obtain ⟨b, hb_sum, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
        have hb_ne : polyOfCoeffs b ≠ 0 := fun h =>
          hj₀ (by rw [← polyOfCoeffs_coeff b j₀, h, Polynomial.coeff_zero])
        have hb_aeval : aeval S (polyOfCoeffs b) u = 0 := by
          rw [polyOfCoeffs_aeval]; exact hb_sum
        have hb_deg : (polyOfCoeffs b).natDegree < m := by
          have := polyOfCoeffs_natDegree_le b; omega
        have hmon : (polyOfCoeffs b *
            Polynomial.C (polyOfCoeffs b).leadingCoeff⁻¹).Monic :=
          Polynomial.monic_mul_leadingCoeff_inv hb_ne
        have hdeg' : (polyOfCoeffs b *
            Polynomial.C (polyOfCoeffs b).leadingCoeff⁻¹).natDegree =
            (polyOfCoeffs b).natDegree := by
          rw [Polynomial.natDegree_mul hb_ne (Polynomial.C_ne_zero.mpr
            (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hb_ne))),
            Polynomial.natDegree_C, add_zero]
        have haev' : aeval S (polyOfCoeffs b *
            Polynomial.C (polyOfCoeffs b).leadingCoeff⁻¹) u = 0 := by
          simp only [map_mul, Module.End.mul_apply, Polynomial.aeval_C,
            Module.algebraMap_end_apply, map_smul, hb_aeval, smul_zero]
        have hlt : (polyOfCoeffs b *
            Polynomial.C (polyOfCoeffs b).leadingCoeff⁻¹).natDegree < m := by
          rw [hdeg']; exact hb_deg
        exact Nat.find_min hExists hlt
          ⟨_, hmon, rfl, haev'⟩
      -- These {lit}`m` independent vectors lie in {lit}`null q(S)`.
      have hmem : ∀ j : Fin m, (S ^ (j : ℕ)) u ∈ ker (aeval S q) := by
        intro j
        rw [LinearMap.mem_ker, hcomm, hqu, map_zero]
      have hli' : LinearIndependent F
          (fun j : Fin m => (⟨(S ^ (j : ℕ)) u, hmem j⟩ : ker (aeval S q))) := by
        apply LinearIndependent.of_comp (ker (aeval S q)).subtype
        exact hli
      have hm_le_ker : m ≤ finrank F (ker (aeval S q)) := by
        have := hli'.fintype_card_le_finrank
        rwa [Fintype.card_fin] at this
      -- {lit}`U = range q(S)` is invariant with {lit}`dim U ≤ n − m < n`.
      set U := range (aeval S q) with hU
      have hU_inv : InvariantUnder S U := by
        rw [hU]; exact range_aeval_invariant S q
      have hrank := LADR.Section_3B.finrank_ker_add_finrank_range (aeval S q)
      rw [← hU, hW] at hrank
      have hU_lt : finrank F U < n := by omega
      -- Induction on {lit}`U` supplies a monic {lit}`s` with {lit}`s(S|_U)=0`.
      obtain ⟨s, hs_monic, hs_aeval, hs_deg⟩ :=
        ih (finrank F U) hU_lt U rfl hU_inv.restrict
      refine ⟨s * q, hs_monic.mul hqmonic, ?_, ?_⟩
      · -- {lit}`(sq)(S) = 0`.
        rw [aeval_mul_eq_comp]
        apply LinearMap.ext
        intro x
        rw [LinearMap.comp_apply, LinearMap.zero_apply]
        have hxU : aeval S q x ∈ U := by rw [hU]; exact ⟨x, rfl⟩
        have hcoe := aeval_restrict_coe hU_inv s ⟨aeval S q x, hxU⟩
        rw [hs_aeval] at hcoe
        simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at hcoe
        exact hcoe.symm
      · -- {lit}`deg(sq) = deg s + deg q ≤ (n − m) + m = n`.
        rw [Polynomial.Monic.natDegree_mul hs_monic hqmonic, hqdeg]
        omega

theorem minpoly_natDegree_le {V : Type u} [AddCommGroup V] [Module F V]
    [Finite F V] (T : V →ₗ[F] V) :
    (minpoly F T).natDegree ≤ finrank F V := by
  obtain ⟨p, hmonic, haeval, hdeg⟩ :=
    minpoly_natDegree_le_aux (finrank F V) V rfl T
  calc (minpoly F T).natDegree
      ≤ p.natDegree := Polynomial.natDegree_le_natDegree (minpoly.min F T hmonic haeval)
    _ ≤ finrank F V := hdeg

/-! 5.24 Definition: minimal polynomial — mathlib's {name}`minpoly`. It is
monic, annihilates {lit}`T`, and has minimal degree among monic annihilating
polynomials. -/

noncomputable example [Finite F V] (T : V →ₗ[F] V) : Polynomial F :=
  minpoly F T

example [Finite F V] (T : V →ₗ[F] V) : (minpoly F T).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral T)

example [Finite F V] (T : V →ₗ[F] V) : aeval T (minpoly F T) = 0 :=
  minpoly.aeval F T

example [Finite F V] (T : V →ₗ[F] V) (q : Polynomial F) (hq : q.Monic)
    (hq0 : aeval T q = 0) : (minpoly F T).degree ≤ q.degree :=
  minpoly.min F T hq hq0

/-! TODO: add (verified?) computation of minimal polynomial and example 5.26 -/

/-! 5.27 Eigenvalues are the zeros of the minimal polynomial.

(a) is mathlib's {name}`Module.End.hasEigenvalue_iff_isRoot`; we give Axler's
proof. -/

theorem isEigenvalue_iff_isRoot [Finite F V] (T : V →ₗ[F] V) (γ : F) :
    HasEigenvalue T γ ↔ (minpoly F T).IsRoot γ := by
  rw [Module.End.hasEigenvalue_iff_exists]
  constructor
  · -- An eigenvalue is a zero: {lit}`0 = p(T)v = p(λ)v` and {lit}`v ≠ 0`.
    rintro ⟨v, hv, hTv⟩
    have hkey : aeval T (minpoly F T) v = (minpoly F T).eval γ • v :=
      Module.End.aeval_apply_of_hasEigenvector
        (Module.End.hasEigenvector_iff_and.mpr ⟨hv, hTv⟩)
    rw [minpoly.aeval, LinearMap.zero_apply] at hkey
    rcases smul_eq_zero.mp hkey.symm with h | h
    · exact h
    · exact absurd h hv
  · intro hroot
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    have hminne : minpoly F T ≠ 0 :=
      minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    have hqne : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hminne hq
    have hqT : aeval T q ≠ 0 := by
      intro h0
      have hdvd := minpoly.dvd F T h0
      have hle := Polynomial.natDegree_le_of_dvd hdvd hqne
      have hmul := Polynomial.natDegree_mul
        (Polynomial.X_sub_C_ne_zero γ) hqne
      rw [← hq, Polynomial.natDegree_X_sub_C] at hmul
      omega
    obtain ⟨v, hv⟩ : ∃ v, aeval T q v ≠ 0 := by
      by_contra h
      push Not at h
      exact hqT (LinearMap.ext fun v => by rw [h v, LinearMap.zero_apply])
    refine ⟨aeval T q v, hv, ?_⟩
    have h1 : aeval T (minpoly F T) v = 0 := by
      rw [minpoly.aeval, LinearMap.zero_apply]
    rw [hq, aeval_mul_eq_comp, LinearMap.comp_apply] at h1
    have h2 : T (aeval T q v) - γ • aeval T q v = 0 := by
      rwa [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        LinearMap.sub_apply, Module.algebraMap_end_apply] at h1
    rw [sub_eq_zero] at h2
    exact h2

/-- The factorization half of 5.27 (b) over an arbitrary field: whenever the
minimal polynomial splits, it is the product of {lit}`z − λ` over its roots. -/
theorem minpoly_eq_prod_roots_of_splits [Finite F V] (T : V →ₗ[F] V)
    (hsplit : (minpoly F T).Splits) :
    minpoly F T = (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
      (minpoly F T).roots).prod := by
  have hmonic : (minpoly F T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := minpoly F T) (Polynomial.splits_iff_card_roots.mp hsplit)
  rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul] at h
  exact h.symm

/-- 5.27 (b) On a complex vector space the minimal polynomial factors as
{lit}`(z − λ₁)⋯(z − λₘ)` where {lit}`λ₁, …, λₘ` are exactly the eigenvalues
of {lit}`T` (with possible repetitions), encoded via the multiset of roots. -/
theorem minpoly_eq_prod_roots {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    minpoly ℂ T = (Multiset.map (fun a => Polynomial.X - Polynomial.C a)
        (minpoly ℂ T).roots).prod ∧
      ∀ γ : ℂ, γ ∈ (minpoly ℂ T).roots ↔ HasEigenvalue T γ := by
  have hmonic : (minpoly ℂ T).Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral T)
  refine ⟨minpoly_eq_prod_roots_of_splits T (IsAlgClosed.splits _), fun lam => ?_⟩
  rw [Polynomial.mem_roots hmonic.ne_zero, isEigenvalue_iff_isRoot]

/-! 5.28 Example: an operator whose eigenvalues cannot be found exactly. Axler's
operator {lit}`T(z₁,…,z₅) = (−3z₅, z₁+6z₅, z₂, z₃, z₄)` on {lit}`ℂ⁵` satisfies
{lit}`T⁵ − 6T + 3 = 0`; the polynomial {lit}`X⁵ − 6X + 3` is its minimal polynomial
(over {lit}`ℚ` it is Eisenstein-irreducible at {lit}`3`), and Galois theory shows
its roots — the eigenvalues of {lit}`T` — are not expressible in radicals. We
formalize the concrete algebraic content: {lit}`T` annihilates {lit}`X⁵ − 6X + 3`. -/

/-- The operator of Example 5.28 on {lit}`ℂ⁵`. -/
def T_5_28 : (Fin 5 → ℂ) →ₗ[ℂ] (Fin 5 → ℂ) where
  toFun z := ![-3 * z 4, z 0 + 6 * z 4, z 1, z 2, z 3]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

/-- 5.28: {lit}`T` satisfies {lit}`T⁵ − 6T + 3 = 0`. -/
theorem T_5_28_annihilator :
    (T_5_28 ^ 5 : Module.End ℂ (Fin 5 → ℂ)) - (6 : ℂ) • T_5_28 + (3 : ℂ) • 1 = 0 := by
  apply LinearMap.ext; intro z; funext i
  fin_cases i <;> simp [pow_succ, Module.End.mul_apply, T_5_28]; ring

/-! 5.29 {lit}`q(T) = 0` iff {lit}`q` is a polynomial multiple of the minimal
polynomial. Axler's proof uses the division algorithm (4.9); mathlib's
version of the forward direction is {name}`minpoly.dvd`. -/

theorem aeval_eq_zero_iff_minpoly_dvd [Finite F V] (T : V →ₗ[F] V)
    (q : Polynomial F) : aeval T q = 0 ↔ minpoly F T ∣ q := by
  constructor
  · intro hq
    have hp_ne : minpoly F T ≠ 0 :=
      minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    -- Division algorithm: {lit}`q = ps + r` with {lit}`deg r < deg p`.
    obtain ⟨⟨s, r⟩, ⟨hqe, hdeg⟩, -⟩ :=
      LADR.Chapter_4.division_algorithm q (minpoly F T) hp_ne
    -- {lit}`r(T) = q(T) − p(T)s(T) = 0`.
    have hr : aeval T r = 0 := by
      have h := congrArg (aeval T) hqe
      rwa [map_add, map_mul, minpoly.aeval, zero_mul, zero_add, hq, eq_comm]
        at h
    -- If {lit}`r ≠ 0` then dividing by its leading coefficient gives a monic
    -- annihilator of smaller degree than the minimal polynomial.
    rcases eq_or_ne r 0 with rfl | hr0
    · exact ⟨s, by rw [hqe, add_zero]⟩
    · exfalso
      have hmonic : (r * Polynomial.C r.leadingCoeff⁻¹).Monic :=
        Polynomial.monic_mul_leadingCoeff_inv hr0
      have haev : aeval T (r * Polynomial.C r.leadingCoeff⁻¹) = 0 := by
        rw [map_mul, hr, zero_mul]
      have hge := minpoly.min F T hmonic haev
      rw [Polynomial.degree_mul_leadingCoeff_inv r hr0] at hge
      exact absurd hdeg (not_lt.mpr hge)
  · rintro ⟨s, rfl⟩
    rw [map_mul, minpoly.aeval, zero_mul]

/-! 5.31 The minimal polynomial of {lit}`T` is a polynomial multiple of the
minimal polynomial of the restriction {lit}`T|_U` to an invariant
subspace. -/

theorem minpoly_restrict_dvd [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) : minpoly F hU.restrict ∣ minpoly F T := by
  -- {lit}`p(T|_U) = 0` because {lit}`p(T)u = 0` for every {lit}`u ∈ U`,
  -- then apply 5.29 to {lit}`T|_U`.
  rw [← aeval_eq_zero_iff_minpoly_dvd]
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  rw [LinearMap.zero_apply, aeval_restrict_coe hU (minpoly F T) u,
    LinearMap.congr_fun (minpoly.aeval F T) (u : V)]
  simp

/-! 5.32 {lit}`T` is not invertible iff the constant term of its minimal
polynomial is {lit}`0`. -/

theorem not_invertible_iff_minpoly_coeff_zero [Finite F V] (T : V →ₗ[F] V) :
    ¬ IsInvertible T ↔ (minpoly F T).coeff 0 = 0 := by
  -- {lit}`T` not invertible ⟺ {lit}`0` eigenvalue (5.7)
  -- ⟺ {lit}`0` zero of {lit}`p` (5.27) ⟺ constant term {lit}`0`.
  have h0 : T - (0 : F) • (LinearMap.id : V →ₗ[F] V) = T := by
    rw [zero_smul, sub_zero]
  have h2 := (tfae_isEigenvalue T 0).out 0 3
  rw [h0] at h2
  rw [← h2, isEigenvalue_iff_isRoot, Polynomial.IsRoot.def,
    Polynomial.coeff_zero_eq_eval_zero]

/-! Eigenvalues on Odd-Dimensional Real Vector Spaces -/

/-- The quotient operator {lit}`T/U` on {lit}`V/U`, for {lit}`U` invariant
under {lit}`T` (mathlib's {name}`Submodule.mapQ`). The reader meets this
operator in Exercise 5A.38; here we need it (with proofs) for 5.33. -/
def quotOp (T : V →ₗ[F] V) (U : Submodule F V) (hU : InvariantUnder T U) :
    V ⧸ U →ₗ[F] V ⧸ U :=
  Submodule.mapQ U U T hU

theorem quotOp_mkQ (T : V →ₗ[F] V) {U : Submodule F V}
    (hU : InvariantUnder T U) (v : V) :
    quotOp T U hU (U.mkQ v) = U.mkQ (T v) := by
  simp [quotOp, Submodule.mapQ_apply]

theorem quotOp_pow_mkQ (T : V →ₗ[F] V) {U : Submodule F V}
    (hU : InvariantUnder T U) (n : ℕ) (v : V) :
    ((quotOp T U hU) ^ n) (U.mkQ v) = U.mkQ ((T ^ n) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, quotOp_mkQ, ih (T v), pow_succ,
      Module.End.mul_apply]

theorem aeval_quotOp_mkQ (T : V →ₗ[F] V) {U : Submodule F V}
    (hU : InvariantUnder T U) (p : Polynomial F) (v : V) :
    aeval (quotOp T U hU) p (U.mkQ v) = U.mkQ (aeval T p v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, LinearMap.add_apply, hp, hq, LinearMap.add_apply,
      map_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      quotOp_pow_mkQ, map_smul]

/-! 5.33 Even-dimensional null space: if {lit}`F = ℝ` and {lit}`b² < 4c`,
then {lit}`null(T² + bT + cI)` has even dimension.

The proof here is by induction: an operator {lit}`S` satisfying
{lit}`S² + bS + cI = 0` has no (real) eigenvalues, so for {lit}`w ≠ 0` the
subspace {lit}`U = span(w, Sw)` is two-dimensional and invariant; the
quotient operator {lit}`S/U` satisfies the same quadratic, and induction on
dimension finishes. (Axler instead takes {lit}`U` maximal even-dimensional
invariant.) -/

private lemma no_eigenvalue_of_quadratic {W : Type u} [AddCommGroup W]
    [Module ℝ W] {b c : ℝ} (hbc : b ^ 2 < 4 * c) (S : W →ₗ[ℝ] W)
    (hS : aeval S (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c) = 0)
    (lam : ℝ) (v : W) (hv : v ≠ 0) : S v ≠ lam • v := by
  intro heq
  have hev : Module.End.HasEigenvector S lam v :=
    ⟨Module.End.mem_eigenspace_iff.mpr heq, hv⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector
    (p := Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c) hev
  rw [hS, LinearMap.zero_apply] at h1
  have heval : (lam ^ 2 + b * lam + c) • v = 0 := by
    have : (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
        Polynomial.C c).eval lam = lam ^ 2 + b * lam + c := by
      simp
    rw [← this]
    exact h1.symm
  rcases smul_eq_zero.mp heval with h | h
  · nlinarith [sq_nonneg (lam + b / 2)]
  · exact hv h

private lemma even_finrank_of_quadratic_aux {b c : ℝ} (hbc : b ^ 2 < 4 * c)
    (n : ℕ) (W : Type u) [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    (hW : finrank ℝ W = n) (S : W →ₗ[ℝ] W)
    (hS : aeval S (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c) = 0) :
    Even n := by
  induction n using Nat.strong_induction_on generalizing W with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    · have : Nontrivial W := by
        apply Module.nontrivial_of_finrank_pos (R := ℝ)
        omega
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      -- {lit}`U = span(w, Sw)` is two-dimensional…
      set U : Submodule ℝ W := Submodule.span ℝ {w, S w} with hU_def
      have hw_mem : w ∈ U := Submodule.subset_span (by simp)
      have hSw_mem : S w ∈ U := Submodule.subset_span (by simp)
      -- {lit}`S²w = −b·Sw − c·w` from the quadratic relation.
      have hS2 : S (S w) = -(b • S w) - c • w := by
        have h1 := LinearMap.congr_fun hS w
        simp only [map_add, map_mul, Polynomial.aeval_X,
          Polynomial.aeval_C, LinearMap.add_apply, Module.End.mul_apply,
          Module.algebraMap_end_apply, LinearMap.zero_apply, pow_two] at h1
        have h2 : S (S w) + (b • S w + c • w) = 0 := by
          rw [← add_assoc]
          exact h1
        rw [add_eq_zero_iff_eq_neg] at h2
        rw [h2]
        abel
      -- …invariant under {lit}`S`…
      have hU_inv : InvariantUnder S U := by
        intro u hu
        rw [hU_def, Submodule.mem_span_pair] at hu ⊢
        obtain ⟨s, t, rfl⟩ := hu
        refine ⟨-(t * c), s - t * b, ?_⟩
        rw [map_add, map_smul, map_smul, hS2]
        module
      -- …of dimension exactly {lit}`2` because {lit}`S` has no eigenvalues.
      have hli : LinearIndependent ℝ ![w, S w] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        by_cases ht : t = 0
        · subst ht
          rw [zero_smul, add_zero] at hst
          rcases smul_eq_zero.mp hst with h | h
          · exact ⟨h, rfl⟩
          · exact absurd h hw
        · exfalso
          have hSw : S w = (-(t⁻¹ * s)) • w := by
            have h1 : t • S w = -(s • w) := by
              rw [eq_neg_iff_add_eq_zero, add_comm]
              exact hst
            have h2 := congrArg (fun x => t⁻¹ • x) h1
            simp only [smul_smul, inv_mul_cancel₀ ht, one_smul, smul_neg]
              at h2
            rw [← neg_smul] at h2
            exact h2
          exact no_eigenvalue_of_quadratic hbc S hS (-(t⁻¹ * s)) w hw hSw
      have hU_rank : finrank ℝ U = 2 := by
        have hrange : Set.range ![w, S w] = ({w, S w} : Set W) := by
          ext x
          constructor
          · rintro ⟨i, rfl⟩
            fin_cases i <;> simp
          · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            rintro (rfl | rfl)
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩
        rw [hU_def, ← hrange, finrank_span_eq_card hli, Fintype.card_fin]
      -- The quotient operator satisfies the same quadratic…
      have hquot : aeval (quotOp S U hU_inv)
          (Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
            Polynomial.C c) = 0 := by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        rw [aeval_quotOp_mkQ, LinearMap.congr_fun hS v,
          LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
      -- …on a space of dimension {lit}`n − 2`; induction gives evenness.
      have hquot_rank : finrank ℝ (W ⧸ U) = n - 2 := by
        rw [LADR.Section_3E.finrank_quotient U, hW, hU_rank]
      have h2n : 2 ≤ n := by
        rw [← hW, ← hU_rank]
        exact Submodule.finrank_le U
      have heven := ih (n - 2) (by omega) (W ⧸ U) hquot_rank
        (quotOp S U hU_inv) hquot
      obtain ⟨k, hk⟩ := heven
      exact ⟨k + 1, by omega⟩

theorem even_finrank_ker_quadratic {V : Type u} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (T : V →ₗ[ℝ] V) {b c : ℝ} (hbc : b ^ 2 < 4 * c) :
    Even (finrank ℝ (ker (aeval T (Polynomial.X ^ 2 +
      Polynomial.C b * Polynomial.X + Polynomial.C c)))) := by
  -- The null space is invariant under {lit}`T` (5.18); the restriction of
  -- {lit}`T` to it satisfies the quadratic relation, so the helper applies.
  set q : Polynomial ℝ := Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
    Polynomial.C c with hq_def
  have hinv : InvariantUnder T (ker (aeval T q)) := ker_aeval_invariant T q
  have hrestrict : aeval hinv.restrict q = 0 := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    rw [LinearMap.zero_apply, aeval_restrict_coe hinv q u]
    have hu := u.2
    rw [LinearMap.mem_ker] at hu
    rw [hu]
    rfl
  exact even_finrank_of_quadratic_aux hbc _ (ker (aeval T q)) rfl
    hinv.restrict hrestrict

/-! 5.34 Every operator on an odd-dimensional real vector space has an
eigenvalue.

Axler's proof: if the minimal polynomial {lit}`p` had no real zero, then by
4.16 it would be a product of quadratics with negative discriminant; peeling
off one quadratic factor {lit}`x² + bx + c`, minimality forces
{lit}`range(T² + bT + cI) ≠ V`; this range is invariant under {lit}`T`,
and by 5.33 plus the fundamental theorem of linear maps it has odd dimension
smaller than {lit}`dim V` — so induction applies, and the resulting
eigenvalue of the restriction is an eigenvalue of {lit}`T`, contradicting
the assumption that {lit}`p` has no real zero. -/

private lemma exists_eigenvalue_of_odd_aux (n : ℕ) (hodd : Odd n) (W : Type u)
    [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W] (hW : finrank ℝ W = n)
    (T : W →ₗ[ℝ] W) : ∃ lam : ℝ, HasEigenvalue T lam := by
  induction n using Nat.strong_induction_on generalizing W with
  | _ n ih =>
    by_cases hroot : ∃ lam : ℝ, (minpoly ℝ T).IsRoot lam
    · obtain ⟨lam, hlam⟩ := hroot
      exact ⟨lam, (isEigenvalue_iff_isRoot T lam).mpr hlam⟩
    · exfalso
      push Not at hroot
      have hn_pos : 0 < n := hodd.pos
      have hW_nontrivial : Nontrivial W := by
        apply Module.nontrivial_of_finrank_pos (R := ℝ)
        omega
      set p : Polynomial ℝ := minpoly ℝ T with hp_def
      have hp_ne : p ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
      have hp_deg_pos : 0 < p.natDegree :=
        minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral T)
      -- 4.16: {lit}`p` factors into linear and quadratic factors; since
      -- {lit}`p` has no real zero there are no linear factors.
      obtain ⟨c, m, M, lams, bs, cs, hdisc, hfact⟩ :=
        LADR.Chapter_4.real_polynomial_factorization p hp_ne
      have hm : m = 0 := by
        by_contra hm0
        have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        apply hroot (lams ⟨0, hmpos⟩)
        rw [Polynomial.IsRoot.def, hfact]
        rw [Polynomial.eval_mul, Polynomial.eval_mul]
        have : Polynomial.eval (lams ⟨0, hmpos⟩)
            (∏ k, (Polynomial.X - Polynomial.C (lams k))) = 0 := by
          rw [Polynomial.eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hmpos⟩) (by simp)
        rw [this, mul_zero, zero_mul]
      subst hm
      -- {lit}`p = C c · ∏ quadratics`, and {lit}`M ≥ 1` since {lit}`p` is
      -- nonconstant.
      rw [show (∏ k : Fin 0, (Polynomial.X - Polynomial.C (lams k))) = 1 from
        Finset.prod_of_isEmpty _, mul_one] at hfact
      have hM : 0 < M := by
        by_contra hM0
        have : M = 0 := by omega
        subst this
        rw [show (∏ k : Fin 0, (Polynomial.X ^ 2 +
          Polynomial.C (bs k) * Polynomial.X + Polynomial.C (cs k))) = 1 from
          Finset.prod_of_isEmpty _, mul_one] at hfact
        rw [hfact, Polynomial.natDegree_C] at hp_deg_pos
        omega
      -- Peel off the quadratic factor {lit}`q = x² + b₀x + c₀`.
      set k0 : Fin M := ⟨0, hM⟩
      set q : Polynomial ℝ := Polynomial.X ^ 2 +
        Polynomial.C (bs k0) * Polynomial.X + Polynomial.C (cs k0) with hq_def
      have hq_deg : q.natDegree = 2 := by
        rw [hq_def]
        compute_degree!
      have hq_ne : q ≠ 0 := fun h => by
        rw [h, Polynomial.natDegree_zero] at hq_deg
        omega
      obtain ⟨s, hps⟩ : q ∣ p := by
        rw [hfact]
        exact Dvd.dvd.mul_left
          (Finset.dvd_prod_of_mem _ (Finset.mem_univ k0)) _
      have hs_ne : s ≠ 0 := fun h => hp_ne (by rw [hps, h, mul_zero])
      have hs_deg : s.natDegree = p.natDegree - 2 := by
        have := Polynomial.natDegree_mul hq_ne hs_ne
        rw [← hps, hq_deg] at this
        omega
      -- {lit}`U = range q(T)` is a proper invariant subspace…
      set U : Submodule ℝ W := range (aeval T q) with hU_def
      have hU_inv : InvariantUnder T U := range_aeval_invariant T q
      have hU_ne_top : U ≠ ⊤ := by
        intro htop
        -- otherwise {lit}`s(T) = 0`, contradicting minimality of {lit}`p`.
        have hsT : aeval T s = 0 := by
          apply LinearMap.ext
          intro w
          have hw : w ∈ U := by rw [htop]; exact Submodule.mem_top
          obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
          rw [LinearMap.zero_apply, ← hv, ← LinearMap.comp_apply,
            ← aeval_mul_eq_comp, mul_comm s q, ← hps, hp_def,
            minpoly.aeval, LinearMap.zero_apply]
        have hdvd := minpoly.dvd ℝ T hsT
        have hle := Polynomial.natDegree_le_of_dvd hdvd hs_ne
        rw [← hp_def] at hle
        omega
      -- …of odd dimension (5.33 + fundamental theorem of linear maps).
      have hker_even : Even (finrank ℝ (ker (aeval T q))) := by
        rw [hq_def]
        exact even_finrank_ker_quadratic T (by have := hdisc k0; nlinarith)
      have hrank_sum := LADR.Section_3B.finrank_ker_add_finrank_range
        (aeval T q)
      have hU_lt : finrank ℝ U < n := by
        rw [← hW]
        exact Submodule.finrank_lt hU_ne_top
      have hU_odd : Odd (finrank ℝ U) := by
        obtain ⟨j, hj⟩ := hker_even
        obtain ⟨i, hi⟩ := hodd
        rw [← hU_def] at hrank_sum
        rw [hW] at hrank_sum
        exact ⟨i - j, by omega⟩
      -- Induction: {lit}`T|_U` has an eigenvalue, which lifts to {lit}`T`
      -- and is then a real zero of {lit}`p` — contradiction.
      obtain ⟨lam, hlam⟩ :=
        ih (finrank ℝ U) hU_lt hU_odd U rfl hU_inv.restrict
      obtain ⟨u, hu_ne, hu_eq⟩ := Module.End.hasEigenvalue_iff_exists.mp hlam
      have hTlam : HasEigenvalue T lam := by
        refine Module.End.hasEigenvalue_iff_exists.mpr
          ⟨(u : W), fun h => hu_ne (Subtype.ext h), ?_⟩
        have := congrArg (Subtype.val) hu_eq
        rwa [Submodule.coe_smul] at this
      exact hroot lam ((isEigenvalue_iff_isRoot T lam).mp hTlam)

theorem exists_eigenvalue_of_odd_finrank {V : Type u} [AddCommGroup V]
    [Module ℝ V] [Finite ℝ V] (hodd : Odd (finrank ℝ V)) (T : V →ₗ[ℝ] V) :
    ∃ lam : ℝ, HasEigenvalue T lam :=
  exists_eigenvalue_of_odd_aux (finrank ℝ V) hodd V rfl T

/-! # Exercises -/

/-- 5B.1 -/
theorem exercise_5B_1 (T : V →ₗ[F] V) :
    HasEigenvalue (T ^ 2) 9 ↔ HasEigenvalue T 3 ∨ HasEigenvalue T (-3) := by
  -- T ^ 2 x = 9 x iff T T - 9 I x = 0 for some x iff (T - 3 I) (T + 3 I) x = 0 for some x iff T - 3 I x = 0 or T + 3 I x = 0 for some x
  -- iff T + 3 I x = 0 for some x or T - 3 I x = 0 for some x
  constructor
  · intro h
    obtain ⟨x, hx_ne, hx⟩ := Module.End.hasEigenvalue_iff_exists.mp h
    rw [pow_two, Module.End.mul_apply] at hx
    -- Either {lit}`(T + 3 I) x = 0`…
    by_cases hy : T x + (3 : F) • x = 0
    · right
      refine Module.End.hasEigenvalue_iff_exists.mpr ⟨x, hx_ne, ?_⟩
      have : T x = -((3 : F) • x) := by
        rw [eq_neg_iff_add_eq_zero]; exact hy
      rw [this, ← neg_smul]
    -- …or {lit}`(T + 3 I) x` is an eigenvector for {lit}`3`.
    · left
      refine Module.End.hasEigenvalue_iff_exists.mpr ⟨T x + (3 : F) • x, hy, ?_⟩
      rw [map_add, map_smul, hx]
      match_scalars <;> norm_num
  · rintro (h | h) <;>
      obtain ⟨x, hx_ne, hx⟩ := Module.End.hasEigenvalue_iff_exists.mp h <;>
      refine Module.End.hasEigenvalue_iff_exists.mpr ⟨x, hx_ne, ?_⟩ <;>
      rw [pow_two, Module.End.mul_apply, hx, map_smul, hx, smul_smul] <;>
      norm_num

/-- 5B.2 -/
theorem exercise_5B_2 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (h : ∀ γ : ℂ, ¬ HasEigenvalue T γ)
    (U : Submodule ℂ V) (hU : InvariantUnder T U) :
    U = ⊥ ∨ ¬ Module.Finite ℂ U := by
  -- restrict T to U -> since restriction min poly divides min poly of T
  -- If T has no eigenvalue, then its minimal polynomial has no linear factors.
  -- this contradicts 5.19 unless zero or infinite-dimensional.
  by_contra hcon
  push Not at hcon
  obtain ⟨hU_ne, hfin⟩ := hcon
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU_ne
  -- 5.19 applied to {lit}`T|_U`…
  obtain ⟨γ, hγ⟩ := exists_eigenvalue hU.restrict
  obtain ⟨u, hu_ne, hu_eq⟩ := Module.End.hasEigenvalue_iff_exists.mp hγ
  -- …produces an eigenvector of {lit}`T` inside {lit}`U`.
  refine h γ (Module.End.hasEigenvalue_iff_exists.mpr
    ⟨(u : V), fun hv => hu_ne (Subtype.ext hv), ?_⟩)
  have := congrArg (Subtype.val) hu_eq
  rwa [Submodule.coe_smul] at this

/-- 5B.3 {lit}`T(x₁, …, xₙ) = (x₁ + ⋯ + xₙ, …, x₁ + ⋯ + xₙ)`. -/
def T_ex_5B_3 (n : ℕ) : (Fin n → F) →ₗ[F] (Fin n → F) where
  toFun x := fun _ => ∑ k, x k
  map_add' x y := by
    funext j
    simp [Finset.sum_add_distrib]
  map_smul' a x := by
    funext j
    simp [Finset.mul_sum]

@[simp] theorem T_ex_5B_3_apply (n : ℕ) (x : Fin n → F) (j : Fin n) :
    T_ex_5B_3 n x j = ∑ k, x k := rfl

/-- {lit}`T x = γ x` unpacks into the {lit}`n` coordinate equations
{lit}`x₁ + ⋯ + xₙ = γ xⱼ`. -/
private theorem T_ex_5B_3_eq_smul (n : ℕ) (γ : F) (x : Fin n → F) :
    T_ex_5B_3 n x = γ • x ↔ ∀ j, ∑ k, x k = γ * x j := by
  constructor
  · intro h j; simpa using congrFun h j
  · intro h; funext j; simpa using h j

/-- The set of eigenvalues of {lit}`T_ex_5B_3 n` — to be determined by the
solver. -/
-- T^2 = n T, so x^2 - n x = x (x - n) = 0
-- The eigenvalues are 0 and n. and eigenvectors (1, 1, …, 1) for n.
-- (x1, ..., -x1 -x2 -x3...-x_{n-1}) for 0.
def eigenvalues_5B_3 (F : Type*) [Field F] (n : ℕ) : Set F := {0, (n : F)}

/-- 5B.3 (a) Find the eigenvalues of {lit}`T`. -/
theorem exercise_5B_3a (n : ℕ) (hn : 1 < n) (γ : F) :
    HasEigenvalue (T_ex_5B_3 (F := F) n) γ ↔ γ ∈ eigenvalues_5B_3 F n := by
  rw [eigenvalues_5B_3, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨x, hx_ne, hx⟩ := Module.End.hasEigenvalue_iff_exists.mp h
    -- Coordinatewise: {lit}`x₁ + ⋯ + xₙ = γ xⱼ` for every {lit}`j`.
    have hcoord := (T_ex_5B_3_eq_smul n γ x).mp hx
    by_cases hs : ∑ k, x k = 0
    · -- All the {lit}`γ xⱼ` vanish while some {lit}`xⱼ` does not.
      left
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hx_ne (funext hc)
      have := (hcoord j).symm
      rw [hs] at this
      exact (mul_eq_zero.mp this).resolve_right hj
    · -- Summing the {lit}`n` equations gives {lit}`n s = γ s` with {lit}`s ≠ 0`.
      right
      refine (mul_right_cancel₀ hs ?_).symm
      calc (n : F) * ∑ k, x k = ∑ _j : Fin n, ∑ k, x k := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ∑ j, γ * x j := Finset.sum_congr rfl fun j _ => hcoord j
        _ = γ * ∑ k, x k := (Finset.mul_sum _ _ _).symm
  · rintro (rfl | rfl)
    · -- {lit}`(1, -1, 0, …, 0)` is killed by {lit}`T`.
      refine Module.End.hasEigenvalue_iff_exists.mpr
        ⟨Pi.single ⟨0, by omega⟩ 1 - Pi.single ⟨1, by omega⟩ 1, ?_, ?_⟩
      · intro hc
        have := congrFun hc ⟨0, by omega⟩
        simp at this
      · funext j
        simp [Finset.sum_sub_distrib]
    · -- {lit}`(1, …, 1)` is scaled by {lit}`n`.
      refine Module.End.hasEigenvalue_iff_exists.mpr ⟨fun _ => 1, ?_, ?_⟩
      · intro hc
        exact one_ne_zero (congrFun hc ⟨0, by omega⟩)
      · funext j
        simp

/-- The set of eigenvectors of {lit}`T_ex_5B_3 n` for a scalar {lit}`γ` (empty
when {lit}`γ` is not an eigenvalue). The {lit}`0`-eigenvectors are the nonzero
vectors with {lit}`x₁ + ⋯ + xₙ = 0`; the {lit}`n`-eigenvectors are the nonzero
constant vectors, i.e. the nonzero multiples of {lit}`(1, …, 1)`. (When
{lit}`n = 0` in {lit}`F` the two eigenvalues coincide, and the first branch —
the correct answer there — applies.) -/
noncomputable def eigenvectors_5B_3 (F : Type*) [Field F] (n : ℕ) (γ : F) :
    Set (Fin n → F) :=
  open Classical in
  if γ = 0 then {x | ∑ k, x k = 0 ∧ x ≠ 0}
  else if γ = (n : F) then {x | (∃ c : F, x = fun _ => c) ∧ x ≠ 0}
  else ∅

/-- 5B.3 (a) Find the eigenvectors of {lit}`T`. -/
theorem exercise_5B_3a' (n : ℕ) (hn : 1 < n) (γ : F) (x : Fin n → F) :
    HasEigenvector (T_ex_5B_3 (F := F) n) γ x ↔ x ∈ eigenvectors_5B_3 F n γ := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff,
    T_ex_5B_3_eq_smul, eigenvectors_5B_3]
  by_cases h0 : γ = 0
  · -- {lit}`T x = 0` says exactly that the coordinates of {lit}`x` sum to zero.
    subst h0
    simp only [zero_mul]
    exact and_congr_left' ⟨fun h => h ⟨0, by omega⟩, fun h _ => h⟩
  · rw [if_neg h0]
    by_cases hnn : γ = (n : F)
    · -- For {lit}`γ = n ≠ 0` every coordinate equals {lit}`(x₁ + ⋯ + xₙ)/n`.
      subst hnn
      rw [if_pos rfl]
      refine and_congr_left' ⟨fun h => ⟨(∑ k, x k) / (n : F), funext fun j => ?_⟩, ?_⟩
      · rw [eq_div_iff h0, h j, mul_comm]
      · rintro ⟨c, rfl⟩ j
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    · -- Any other {lit}`γ` is not an eigenvalue, by part (a).
      rw [if_neg hnn]
      simp only [Set.mem_empty_iff_false, iff_false, not_and]
      intro h hne
      have hev : HasEigenvalue (T_ex_5B_3 (F := F) n) γ :=
        Module.End.hasEigenvalue_iff_exists.mpr
          ⟨x, hne, (T_ex_5B_3_eq_smul n γ x).mpr h⟩
      rcases (exercise_5B_3a n hn γ).mp hev with h | h
      · exact h0 h
      · exact hnn h

/-- The minimal polynomial of {lit}`T_ex_5B_3 n` — to be determined by the
solver. -/
noncomputable def minpoly_5B_3 (F : Type*) [Field F] (n : ℕ) : Polynomial F :=
  Polynomial.X ^ 2 - Polynomial.C (n : F) * Polynomial.X

/-- If {lit}`T` is not a scalar multiple of the identity, every monic
polynomial annihilating {lit}`T` has degree at least {lit}`2`: a monic
polynomial of degree {lit}`0` is {lit}`1`, which would make the identity zero,
and one of degree {lit}`1` is {lit}`X + c`, which would make {lit}`T` the
scalar {lit}`-c`. -/
private theorem two_le_degree_of_not_scalar {T : V →ₗ[F] V}
    (hscal : ∀ a : F, ¬ (∀ v : V, T v = a • v)) {q : Polynomial F}
    (hq : q.Monic) (hq0 : aeval T q = 0) : 2 ≤ q.degree := by
  by_contra hlt
  push Not at hlt
  have hnat : q.natDegree < 2 :=
    (Polynomial.natDegree_lt_iff_degree_lt hq.ne_zero).mpr hlt
  interval_cases hqd : q.natDegree
  · -- {lit}`q = 1`, so the identity is zero on {lit}`V`.
    rw [hq.natDegree_eq_zero.mp hqd] at hq0
    refine hscal 0 fun v => ?_
    have hv : v = 0 := by
      have := congrArg (fun S => S v) hq0
      simpa using this
    simp [hv]
  · -- {lit}`q = X + c`, so {lit}`T = -c • id`.
    rw [hq.eq_X_add_C hqd] at hq0
    refine hscal (-q.coeff 0) fun v => ?_
    have := congrArg (fun S => S v) hq0
    simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C,
      LinearMap.add_apply, Module.algebraMap_end_apply,
      LinearMap.zero_apply] at this
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact this

/-- 5B.3 (b) Find the minimal polynomial of {lit}`T`. -/
theorem exercise_5B_3b (n : ℕ) (hn : 1 < n) :
    minpoly F (T_ex_5B_3 (F := F) n) = minpoly_5B_3 F n := by
  set T := T_ex_5B_3 (F := F) n with hT
  -- {lit}`T² = n T`, so {lit}`X² - n X` annihilates {lit}`T`.
  have hkey : T * T = (n : F) • T := by
    ext x j
    simp [hT, Module.End.mul_apply, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  have hmonic : (minpoly_5B_3 F n).Monic := by
    rw [minpoly_5B_3]; monicity!
  have haeval : Polynomial.aeval T (minpoly_5B_3 F n) = 0 := by
    rw [minpoly_5B_3]
    simp only [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      ← Algebra.smul_def, pow_two, hkey, sub_self]
  -- {lit}`T` is not a scalar multiple of the identity, so no degree-{lit}`≤ 1`
  -- polynomial annihilates it.
  have hscal : ∀ a : F, ¬ (∀ v : Fin n → F, T v = a • v) := by
    intro a hc
    have := congrFun (hc (Pi.single ⟨0, by omega⟩ 1)) ⟨1, by omega⟩
    rw [hT] at this
    simp at this
  refine (minpoly.unique F T hmonic haeval fun q hq hq0 => ?_).symm
  have hdeg : (minpoly_5B_3 F n).degree = 2 := by
    rw [minpoly_5B_3]; compute_degree!
  rw [hdeg]
  exact two_le_degree_of_not_scalar hscal hq hq0

/-- Helper for 5B.4: if {lit}`q(T)` is not injective and {lit}`q ≠ 0`, then
{lit}`q` has a root that is an eigenvalue of {lit}`T`. Writing
{lit}`q = c (z - x₁) ⋯ (z - xₙ)`, a composition of injective maps is injective,
so some factor {lit}`T - xᵢI` is not injective, i.e. has a nonzero kernel. The
induction below peels the factors off via the division algorithm, so the
factorization never has to be written down — endomorphisms do not commute, so
a {name}`Multiset.prod` of factors is not available. -/
private theorem exists_isRoot_hasEigenvalue {V : Type*} [AddCommGroup V]
    [Module ℂ V] (T : V →ₗ[ℂ] V) (n : ℕ) :
    ∀ q : Polynomial ℂ, q.natDegree = n → q ≠ 0 →
      ¬ Function.Injective (aeval T q) →
      ∃ γ : ℂ, q.IsRoot γ ∧ HasEigenvalue T γ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro q hqn hq0 hqinj
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- A nonzero constant scales by a nonzero scalar, which is injective.
      obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hqn
      rw [← ha] at hq0 hqinj
      refine absurd (fun x y hxy => ?_) hqinj
      rw [Polynomial.aeval_C, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply] at hxy
      exact smul_right_injective V (fun h => hq0 (by rw [h, map_zero])) hxy
    · -- Peel off one root {lit}`a` of {lit}`q`, i.e. {lit}`q = (z - a) q'`.
      obtain ⟨a, ha⟩ := Complex.exists_root (f := q)
        (by rw [Polynomial.degree_eq_natDegree hq0, hqn]; exact_mod_cast hn)
      set q' := q /ₘ (Polynomial.X - Polynomial.C a) with hq'_def
      have hmul : (Polynomial.X - Polynomial.C a) * q' = q :=
        Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ha
      have hq'0 : q' ≠ 0 := fun h => hq0 (by rw [← hmul, h, mul_zero])
      have hq'n : q'.natDegree = n - 1 := by
        rw [hq'_def,
          Polynomial.natDegree_divByMonic q (Polynomial.monic_X_sub_C a), hqn,
          Polynomial.natDegree_X_sub_C]
      rw [← hmul, map_mul] at hqinj
      by_cases hfac : Function.Injective (aeval T q')
      · -- Then the other factor is not injective, so {lit}`a` is an eigenvalue.
        refine ⟨a, ha, ?_⟩
        have hnotinj : ¬ Function.Injective
            (aeval T (Polynomial.X - Polynomial.C a)) := fun h =>
          hqinj (by rw [Module.End.coe_mul]; exact h.comp hfac)
        obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.mp
          (fun h => hnotinj (LinearMap.ker_eq_bot.mp h))
        refine Module.End.hasEigenvalue_iff_exists.mpr ⟨x, hx0, ?_⟩
        have hker := LinearMap.mem_ker.mp hx
        rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
          LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hker
        exact hker
      · -- Otherwise the shorter factor is not injective; recurse on it.
        obtain ⟨γ, hroot, hγ⟩ := ih (n - 1) (by omega) q' hq'n hq'0 hfac
        exact ⟨γ, by rw [← hmul]; simp [Polynomial.IsRoot.def, hroot.eq_zero], hγ⟩

/-- 5B.4 -/
theorem exercise_5B_4 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] V) (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) (α : ℂ) :
    HasEigenvalue (aeval T p) α ↔
      ∃ γ : ℂ, HasEigenvalue T γ ∧ α = p.eval γ := by
  constructor
  -- -> p(T) v = α v
  · intro h
    obtain ⟨v, hv, hTv⟩ := Module.End.hasEigenvalue_iff_exists.mp h
    set q : Polynomial ℂ := p - Polynomial.C α with hq_def
    -- {lit}`q ≠ 0` because {lit}`p` is nonconstant
    have hq_ne : q ≠ 0 := by
      intro hc
      rw [hq_def, sub_eq_zero] at hc
      rw [hc, Polynomial.natDegree_C] at hp
      exact absurd hp (lt_irrefl 0)
    -- (p - α)(T) v = 0, so (p - α)(T) is not injective
    have hqv : (aeval T q) v = 0 := by
      rw [hq_def, map_sub, Polynomial.aeval_C, LinearMap.sub_apply,
        Module.algebraMap_end_apply, hTv, sub_self]
    have hqinj : ¬ Function.Injective (aeval T q) := fun hinj =>
      hv (hinj (by rw [hqv, map_zero]))
    -- (z - x1)(z - x2) ... (z - xn)(T) is not injective, so one of the factors
    -- is not, and that xi is an eigenvalue of T
    obtain ⟨γ, hroot, hγ⟩ :=
      exists_isRoot_hasEigenvalue T q.natDegree q rfl hq_ne hqinj
    -- but then γ is a root of p - α, so p(γ) = α
    refine ⟨γ, hγ, ?_⟩
    rw [Polynomial.IsRoot.def, hq_def, Polynomial.eval_sub, Polynomial.eval_C,
      sub_eq_zero] at hroot
    exact hroot.symm
  -- <- T v = γ v, then expanding p(T) v gives p(γ) v
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨v, hv, hTv⟩ := Module.End.hasEigenvalue_iff_exists.mp hγ
    exact Module.End.hasEigenvalue_iff_exists.mpr ⟨v, hv,
      Module.End.aeval_apply_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hTv, hv⟩⟩

open LADR.Section_5A (T_5_9) in
/-- 5B.5 The previous exercise fails over {lit}`ℝ`. -/
theorem exercise_5B_5 :
    ∃ (T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (p : Polynomial ℝ)
      (_ : 0 < p.natDegree) (α : ℝ),
      ¬ (HasEigenvalue (aeval T p) α ↔
      ∃ γ : ℝ, HasEigenvalue T γ ∧ α = p.eval γ) := by
  -- T^4 = I -> p = x^4, aeval T p = I, so α = 1
  -- but T has no real eigenvalue
  -- T (x, y) = (-y, x) - rotation by 90 degrees
  refine ⟨T_5_9 ℝ, Polynomial.X ^ 4, ?_, 1, ?_⟩
  · rw [Polynomial.natDegree_X_pow]; omega
  intro hiff
  -- {lit}`T² = -I`, hence {lit}`T⁴ = I`.
  have hT2 : (T_5_9 ℝ) ^ 2 = -1 := by
    ext v i
    fin_cases i <;> simp [pow_two, Module.End.mul_apply, T_5_9]
  have hT4 : aeval (T_5_9 ℝ) (Polynomial.X ^ 4 : Polynomial ℝ) = 1 := by
    rw [map_pow, Polynomial.aeval_X, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      hT2, neg_one_sq]
  -- {lit}`1` is an eigenvalue of the identity…
  have hev : HasEigenvalue (aeval (T_5_9 ℝ) (Polynomial.X ^ 4 : Polynomial ℝ)) 1 := by
    rw [hT4]
    exact Module.End.hasEigenvalue_iff_exists.mpr
      ⟨![1, 0], fun h => one_ne_zero (congrFun h 0), by simp⟩
  obtain ⟨γ, hγ, -⟩ := hiff.mp hev
  -- …but {lit}`T` has no real eigenvalue (5.9): the coordinate equations
  -- {lit}`−v₁ = γv₀` and {lit}`v₀ = γv₁` force {lit}`(1 + γ²)v = 0`.
  obtain ⟨v, hv, hTv⟩ := Module.End.hasEigenvalue_iff_exists.mp hγ
  have h0 : -v 1 = γ * v 0 := congrFun hTv 0
  have h1 : v 0 = γ * v 1 := congrFun hTv 1
  have h2 : (1 + γ ^ 2) * v 0 = 0 := by linear_combination h1 - γ * h0
  have h3 : (1 + γ ^ 2) * v 1 = 0 := by linear_combination -h0 - γ * h1
  have hpos : (0 : ℝ) < 1 + γ ^ 2 := by positivity
  apply hv
  funext i
  fin_cases i
  · exact (mul_eq_zero.mp h2).resolve_left (ne_of_gt hpos)
  · exact (mul_eq_zero.mp h3).resolve_left (ne_of_gt hpos)

/-- The minimal polynomial of {lit}`T_5_9` — to be determined by the
solver. -/
-- T2 = -I, so the minimal polynomial should be X^2 + 1.
-- can't be deg 1, because T has no real eigenvalue (see above)
noncomputable def minpoly_5B_6 (F : Type*) [Field F] : Polynomial F :=
  Polynomial.X ^ 2 + 1

open LADR.Section_5A (T_5_9) in
/-- 5B.6 Find the minimal polynomial of {lit}`T(w, z) = (−z, w)`. -/
theorem exercise_5B_6 :
    minpoly F (T_5_9 F) = minpoly_5B_6 F := by
  set T := T_5_9 F with hT
  -- {lit}`T² = -I`, so {lit}`X² + 1` annihilates {lit}`T`.
  have hT2 : T * T = -1 := by
    ext v i
    fin_cases i <;> simp [hT, Module.End.mul_apply, T_5_9]
  have hmonic : (minpoly_5B_6 F).Monic := by
    rw [minpoly_5B_6]; monicity!
  have haeval : Polynomial.aeval T (minpoly_5B_6 F) = 0 := by
    rw [minpoly_5B_6, map_add, map_pow, Polynomial.aeval_X, map_one, pow_two,
      hT2, neg_add_cancel]
  -- {lit}`T` is not a scalar multiple of the identity: it moves
  -- {lit}`(1, 0)` to {lit}`(0, 1)`.
  have hscal : ∀ a : F, ¬ (∀ v : Fin 2 → F, T v = a • v) := by
    intro a hc
    have := congrFun (hc ![1, 0]) 1
    rw [hT] at this
    simp [T_5_9] at this
  refine (minpoly.unique F T hmonic haeval fun q hq hq0 => ?_).symm
  have hdeg : (minpoly_5B_6 F).degree = 2 := by
    rw [minpoly_5B_6]; compute_degree!
  rw [hdeg]
  exact two_le_degree_of_not_scalar hscal hq hq0

/-- 5B.7 (a) {lit}`S(x₁, x₂) = (x₂, 0)`, the matrix {lit}`(0 1; 0 0)`. -/
private def S_ex_5B_7 : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun x := ![x 1, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- 5B.7 (a) {lit}`T(x₁, x₂) = (0, x₂)`, the matrix {lit}`(0 0; 0 1)`. -/
private def T_ex_5B_7 : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun x := ![0, x 1]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

/-- 5B.7 (a) -/
theorem exercise_5B_7a :
    ∃ S T : (Fin 2 → F) →ₗ[F] (Fin 2 → F),
      minpoly F (S ∘ₗ T) ≠ minpoly F (T ∘ₗ S) := by
  -- (0 1; 0 0) * (0 0; 0 1) = (0 1; 0 0) -> ^ 2 = 0, so X^2 is minpoly
  -- (0 0; 0 1) * (0 1; 0 0) = (0 0; 0 0) -> minpoly = X
  refine ⟨S_ex_5B_7, T_ex_5B_7, ?_⟩
  have hST : (S_ex_5B_7 : (Fin 2 → F) →ₗ[F] _) ∘ₗ T_ex_5B_7 = S_ex_5B_7 := by
    ext x i
    fin_cases i <;> simp [S_ex_5B_7, T_ex_5B_7]
  have hTS : (T_ex_5B_7 : (Fin 2 → F) →ₗ[F] _) ∘ₗ S_ex_5B_7 = 0 := by
    ext x i
    fin_cases i <;> simp [S_ex_5B_7, T_ex_5B_7]
  rw [hST, hTS, minpoly.zero]
  -- If {lit}`S` had minimal polynomial {lit}`X` it would be zero, but it is not.
  intro hcon
  have hS0 := minpoly.aeval F (S_ex_5B_7 (F := F))
  rw [hcon, Polynomial.aeval_X] at hS0
  have := congrFun (congrArg (fun A : (Fin 2 → F) →ₗ[F] (Fin 2 → F) =>
    A ![0, 1]) hS0) 0
  simp [S_ex_5B_7] at this

/-- {lit}`S p(TS) = p(ST) S` for every polynomial {lit}`p`: both sides are the
alternating word in {lit}`S` and {lit}`T` starting and ending with {lit}`S`. -/
private theorem mul_aeval_swap (S T : Module.End F V) (p : Polynomial F) :
    S * aeval (T * S) p = aeval (S * T) p * S := by
  have hpow : ∀ n : ℕ, S * (T * S) ^ n = (S * T) ^ n * S := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, pow_succ, mul_assoc, mul_assoc,
        ← mul_assoc S T S]
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C]
    rw [Algebra.commutes]
  | add p q hp hq => rw [map_add, map_add, mul_add, add_mul, hp, hq]
  | monomial n a _ =>
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [← mul_assoc, ← Algebra.commutes, mul_assoc, hpow, ← mul_assoc]

/-- 5B.7 (b) when the invertible map is on the left: {lit}`p(ST) = 0` iff
{lit}`p(TS) = 0`, since {lit}`S p(TS) = p(ST) S` and {lit}`S` cancels. -/
private theorem minpoly_comp_swap [Finite F V] {S T : V →ₗ[F] V}
    (hS : IsInvertible S) : minpoly F (S ∘ₗ T) = minpoly F (T ∘ₗ S) := by
  show minpoly F (S * T) = minpoly F (T * S)
  have hinv : (hS.inv : Module.End F V) * S = 1 := hS.inv_comp
  have hinv' : S * (hS.inv : Module.End F V) = 1 := hS.comp_inv
  -- STST...ST + a_n-1 STS...T + ... an = 0 -- add S on right, S^-1 on left
  have h1 : aeval (T * S) (minpoly F (S * T)) = 0 := by
    have h := mul_aeval_swap S T (minpoly F (S * T))
    rw [minpoly.aeval, zero_mul] at h
    calc aeval (T * S) (minpoly F (S * T))
        = (hS.inv * S) * aeval (T * S) (minpoly F (S * T)) := by rw [hinv, one_mul]
      _ = hS.inv * (S * aeval (T * S) (minpoly F (S * T))) := mul_assoc _ _ _
      _ = 0 := by rw [h, mul_zero]
  -- TS...TS + a_n-1 TST...S + ... S^-1S an = 0
  have h2 : aeval (S * T) (minpoly F (T * S)) = 0 := by
    have h := mul_aeval_swap S T (minpoly F (T * S))
    rw [minpoly.aeval, mul_zero] at h
    calc aeval (S * T) (minpoly F (T * S))
        = aeval (S * T) (minpoly F (T * S)) * (S * hS.inv) := by rw [hinv', mul_one]
      _ = (aeval (S * T) (minpoly F (T * S)) * S) * hS.inv := (mul_assoc _ _ _).symm
      _ = 0 := by rw [← h, zero_mul]
  -- so p(S T) = 0 if and only if p(T S) = 0, so min poly match
  exact Polynomial.eq_of_monic_of_associated
    (minpoly.monic (Algebra.IsIntegral.isIntegral _))
    (minpoly.monic (Algebra.IsIntegral.isIntegral _))
    (associated_of_dvd_dvd (minpoly.dvd F _ h2) (minpoly.dvd F _ h1))

/-- 5B.7 (b) -/
theorem exercise_5B_7b [Finite F V] (S T : V →ₗ[F] V)
    (hST : IsInvertible S ∨ IsInvertible T) :
    minpoly F (S ∘ₗ T) = minpoly F (T ∘ₗ S) := by
  -- wlog S is invertible
  rcases hST with h | h
  · exact minpoly_comp_swap h
  · exact (minpoly_comp_swap h).symm

/-- 5B.8 Find the minimal polynomial of counterclockwise rotation by
{lit}`1°`. -/
noncomputable def T_ex_5B_8 : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![Real.cos (Real.pi / 180) * v 0 - Real.sin (Real.pi / 180) * v 1,
    Real.sin (Real.pi / 180) * v 0 + Real.cos (Real.pi / 180) * v 1]
  map_add' x y := by
    funext i
    fin_cases i
    · simp [mul_add]
      ring
    · simp [mul_add]
      ring
  map_smul' a x := by
    funext i
    fin_cases i
    · simp
      ring
    · simp
      ring

/-- The minimal polynomial of {lit}`T_ex_5B_8` — to be determined by the
solver. -/
-- take v = ![1, 0] and a = pi / 180
-- T v = [cos a, sin a], T^2 v = [cos 2a, sin 2a]
-- the min poly is deg 2 (since deg V is 2 and deg 1 is for scaled identity transformation)
-- x ^ 2 - sin 2a / sin a x + cos a * sin 2a / sin a - cos 2a
-- using double eq it simplifies to
noncomputable def minpoly_5B_8 : Polynomial ℝ :=
  let a := Real.pi / 180
  Polynomial.X ^ 2 - 2 * (Real.cos a) • Polynomial.X + 1

theorem exercise_5B_8 : minpoly ℝ T_ex_5B_8 = minpoly_5B_8 := by
  have hpyth : Real.sin (Real.pi / 180) ^ 2 + Real.cos (Real.pi / 180) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hs : 0 < Real.sin (Real.pi / 180) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  -- {lit}`T² = 2 cos a · T - I`, using {lit}`sin² a + cos² a = 1`.
  have hkey : T_ex_5B_8 * T_ex_5B_8
      = (2 * Real.cos (Real.pi / 180)) • T_ex_5B_8 - 1 := by
    refine LinearMap.ext fun v => funext fun i => ?_
    fin_cases i
    · simp [Module.End.mul_apply, T_ex_5B_8]
      linear_combination (-(v 0)) * hpyth
    · simp [Module.End.mul_apply, T_ex_5B_8]
      linear_combination (-(v 1)) * hpyth
  have hmonic : minpoly_5B_8.Monic := by
    simp only [minpoly_5B_8]; monicity!
  have haeval : Polynomial.aeval T_ex_5B_8 minpoly_5B_8 = 0 := by
    simp only [minpoly_5B_8, map_add, map_sub, map_mul, map_ofNat,
      map_smul, Polynomial.aeval_X, map_one, pow_two, hkey]
    rw [mul_smul, two_smul, two_mul]
    abel
  -- Rotation by {lit}`1°` is not a scalar multiple of the identity: it moves
  -- {lit}`(1, 0)` to {lit}`(cos a, sin a)` and {lit}`sin a ≠ 0`.
  have hscal : ∀ a : ℝ, ¬ (∀ v : Fin 2 → ℝ, T_ex_5B_8 v = a • v) := by
    intro a hc
    have h := congrFun (hc ![1, 0]) 1
    simp [T_ex_5B_8] at h
    exact absurd h (ne_of_gt hs)
  refine (minpoly.unique ℝ _ hmonic haeval fun q hq hq0 => ?_).symm
  have hdeg : minpoly_5B_8.degree = 2 := by
    simp only [minpoly_5B_8]; compute_degree!
  rw [hdeg]
  exact two_le_degree_of_not_scalar hscal hq hq0

/-- Rational matrices that are linearly independent over {lit}`ℚ` stay
independent over {lit}`ℝ`. The Gram matrix {lit}`Gᵢⱼ = ∑ₚ,ᵩ (uᵢ)ₚᵩ (uⱼ)ₚᵩ` of
the standard form is rational, and the form is positive definite over
{lit}`ℚ`, so {lit}`det G ≠ 0`; determinants commute with {lit}`ℚ → ℝ`, so the
real Gram matrix is invertible too and kills only the zero vector. -/
private theorem linearIndependent_matrix_map {n d : ℕ}
    {u : Fin d → Matrix (Fin n) (Fin n) ℚ} (hu : LinearIndependent ℚ u) :
    LinearIndependent ℝ fun i => (u i).map (algebraMap ℚ ℝ) := by
  classical
  set G : Matrix (Fin d) (Fin d) ℚ :=
    Matrix.of fun i j => ∑ pq : Fin n × Fin n, u i pq.1 pq.2 * u j pq.1 pq.2 with hG
  -- Positive definiteness over {lit}`ℚ` makes the Gram determinant nonzero.
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hsq : ∑ pq : Fin n × Fin n, (∑ i, c i * u i pq.1 pq.2) ^ 2 = 0 := by
      calc ∑ pq : Fin n × Fin n, (∑ i, c i * u i pq.1 pq.2) ^ 2
          = ∑ pq : Fin n × Fin n, ∑ i, ∑ j,
              c i * u i pq.1 pq.2 * (c j * u j pq.1 pq.2) :=
            Finset.sum_congr rfl fun pq _ => by rw [sq, Finset.sum_mul_sum]
        _ = ∑ i, ∑ j, ∑ pq : Fin n × Fin n,
              c i * u i pq.1 pq.2 * (c j * u j pq.1 pq.2) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i, c i * Matrix.mulVec G c i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Matrix.mulVec, dotProduct, hG, Matrix.of_apply,
              Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by
              rw [Finset.sum_mul, Finset.mul_sum]
              exact Finset.sum_congr rfl fun pq _ => by ring
        _ = 0 := by rw [hc]; simp
    -- a sum of squares of rationals vanishes only if every entry does
    have hzero : ∀ pq : Fin n × Fin n, ∑ i, c i * u i pq.1 pq.2 = 0 := by
      intro pq
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun pq _ => sq_nonneg (∑ i, c i * u i pq.1 pq.2))).mp hsq pq (Finset.mem_univ _)
      exact sq_eq_zero_iff.mp this
    refine hc0 (funext fun i => Fintype.linearIndependent_iff.mp hu c ?_ i)
    funext p q
    have := hzero (p, q)
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using this
  -- Transport the Gram matrix to {lit}`ℝ`; its determinant is still nonzero.
  have hdetR : (G.map (algebraMap ℚ ℝ)).det ≠ 0 := by
    have hmapdet : (G.map (algebraMap ℚ ℝ)).det = algebraMap ℚ ℝ G.det :=
      ((algebraMap ℚ ℝ).map_det G).symm
    rw [hmapdet]
    exact fun h => hdet ((algebraMap ℚ ℝ).injective (by rw [map_zero]; exact h))
  refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
  have hg' : ∀ pq : Fin n × Fin n,
      ∑ i, g i * algebraMap ℚ ℝ (u i pq.1 pq.2) = 0 := by
    intro pq
    have := congrFun (congrFun hg pq.1) pq.2
    simpa [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
      using this
  have hvec : Matrix.vecMul g (G.map (algebraMap ℚ ℝ)) = 0 := by
    funext j
    calc Matrix.vecMul g (G.map (algebraMap ℚ ℝ)) j
        = ∑ i, g i * algebraMap ℚ ℝ (G i j) := by
          simp [Matrix.vecMul, dotProduct, Matrix.map_apply]
      _ = ∑ i, ∑ pq : Fin n × Fin n, g i * algebraMap ℚ ℝ (u i pq.1 pq.2) *
            algebraMap ℚ ℝ (u j pq.1 pq.2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hG, Matrix.of_apply, map_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun pq _ => by rw [map_mul]; ring
      _ = ∑ pq : Fin n × Fin n, (∑ i, g i * algebraMap ℚ ℝ (u i pq.1 pq.2)) *
            algebraMap ℚ ℝ (u j pq.1 pq.2) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun pq _ => (Finset.sum_mul _ _ _).symm
      _ = 0 := Finset.sum_eq_zero fun pq _ => by rw [hg' pq, zero_mul]
  exact fun i => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdetR hvec) i

/-- The minimal polynomial of a rational matrix does not change when the matrix
is regarded as a real one. -/
private theorem minpoly_map_rat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    minpoly ℝ (A.map (algebraMap ℚ ℝ)) = (minpoly ℚ A).map (algebraMap ℚ ℝ) := by
  have hAmap : A.map (algebraMap ℚ ℝ) = (Algebra.ofId ℚ ℝ).mapMatrix A := rfl
  -- {lit}`p(A) = 0` still holds over {lit}`ℝ`
  have haeval : Polynomial.aeval (A.map (algebraMap ℚ ℝ))
      ((minpoly ℚ A).map (algebraMap ℚ ℝ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, hAmap, Polynomial.aeval_algHom_apply,
      minpoly.aeval, map_zero]
  refine (minpoly.unique ℝ _
    ((minpoly.monic (Algebra.IsIntegral.isIntegral A)).map _) haeval fun q hq hq0 => ?_).symm
  rw [Polynomial.degree_map_eq_of_injective (algebraMap ℚ ℝ).injective]
  -- the powers below the degree of the rational minimal polynomial stay
  -- independent over {lit}`ℝ`, so no smaller monic real polynomial annihilates
  by_contra hlt
  push Not at hlt
  have hnat : q.natDegree < (minpoly ℚ A).natDegree := by
    have hq_ne : q ≠ 0 := hq.ne_zero
    rw [Polynomial.degree_eq_natDegree hq_ne,
      Polynomial.degree_eq_natDegree (minpoly.ne_zero
        (Algebra.IsIntegral.isIntegral A))] at hlt
    exact_mod_cast hlt
  have hind := linearIndependent_matrix_map
    (u := fun i : Fin (minpoly ℚ A).natDegree => A ^ (i : ℕ)) (linearIndependent_pow A)
  have hpow : ∀ i : ℕ, (A.map (algebraMap ℚ ℝ)) ^ i = (A ^ i).map (algebraMap ℚ ℝ) := by
    intro i
    rw [hAmap, ← map_pow]
    rfl
  have hrel : ∑ i : Fin (minpoly ℚ A).natDegree,
      q.coeff (i : ℕ) • ((A ^ (i : ℕ)).map (algebraMap ℚ ℝ)) = 0 := by
    have hsum := Polynomial.aeval_eq_sum_range' hnat (A.map (algebraMap ℚ ℝ))
    rw [hq0] at hsum
    rw [← Finset.sum_range fun i => q.coeff i • ((A ^ i).map (algebraMap ℚ ℝ))]
    calc ∑ i ∈ Finset.range (minpoly ℚ A).natDegree,
          q.coeff i • ((A ^ i).map (algebraMap ℚ ℝ))
        = ∑ i ∈ Finset.range (minpoly ℚ A).natDegree,
            q.coeff i • (A.map (algebraMap ℚ ℝ)) ^ i :=
          Finset.sum_congr rfl fun i _ => by rw [hpow]
      _ = 0 := hsum.symm
  have := Fintype.linearIndependent_iff.mp hind (fun i => q.coeff (i : ℕ)) hrel
    ⟨q.natDegree, hnat⟩
  rw [hq.coeff_natDegree] at this
  exact one_ne_zero this

open LADR.Section_3C (matrixOf) in
/-- 5B.9 If the matrix of {lit}`T` with respect to some basis has rational
entries, then all coefficients of the minimal polynomial are rational. -/
theorem exercise_5B_9 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V]
    {n : ℕ} {v : Fin n → V} (hv : IsBasis ℝ v) (T : V →ₗ[ℝ] V)
    (hrat : ∀ j k, ∃ r : ℚ, matrixOf hv hv T j k = (r : ℝ)) :
    ∀ k, ∃ r : ℚ, (minpoly ℝ T).coeff k = (r : ℝ) := by
  -- the minimal poly is found solving n^2 linear equations over a field.
  classical
  choose A hA using hrat
  have hmat : matrixOf hv hv T = (Matrix.of A).map (algebraMap ℚ ℝ) := by
    funext j k
    rw [hA j k]
    simp [Matrix.map_apply]
  have hminpoly : minpoly ℝ T = minpoly ℝ (matrixOf hv hv T) :=
    (LinearMap.minpoly_toMatrix hv.toModuleBasis T).symm
  intro k
  refine ⟨(minpoly ℚ (Matrix.of A)).coeff k, ?_⟩
  rw [hminpoly, hmat, minpoly_map_rat, Polynomial.coeff_map]
  simp

/-- 5B.10 -/
theorem exercise_5B_10 [Finite F V] (T : V →ₗ[F] V) (v : V) (m : ℕ)
    (hm : finrank F V - 1 ≤ m) :
    Submodule.span F (Set.range fun i : Fin (m + 1) => (T ^ (i : ℕ)) v) =
      Submodule.span F
        (Set.range fun i : Fin (finrank F V) => (T ^ (i : ℕ)) v) := by
  -- we proved the min poly is max deg dim V, so
  -- T ^ dim = poly of deg dim V - 1 at most = p
  -- T ^ m = T ^ j * T ^ dim = T ^ j * p (T) = p' of deg m - 1
  -- by induction for all m >= dim V - 1 , (T^m v) is gened by span up to deg V -1
  -- the result follows.
  set n := finrank F V with hn
  set W := Submodule.span F (Set.range fun i : Fin n => (T ^ (i : ℕ)) v) with hW
  have hgen : ∀ i : Fin n, (T ^ (i : ℕ)) v ∈ W := fun i => Submodule.subset_span ⟨i, rfl⟩
  -- The minimal polynomial has degree {lit}`d ≤ n` (5.22), so {lit}`T ^ d` is a
  -- combination of the lower powers, and {lit}`T ^ n = T ^ (n - d) T ^ d` is a
  -- combination of {lit}`T ^ (n - d + i)` with {lit}`i < d`, all exponents
  -- being smaller than {lit}`n`.
  have hTn : (T ^ n) v ∈ W := by
    set d := (minpoly F T).natDegree with hd
    have hdle : d ≤ n := minpoly_natDegree_le T
    have hcoeff : (minpoly F T).coeff d = 1 :=
      (minpoly.monic (Algebra.IsIntegral.isIntegral T)).coeff_natDegree
    have h0 : Polynomial.aeval T (minpoly F T) = 0 := minpoly.aeval F T
    rw [Polynomial.aeval_eq_sum_range' (n := d + 1) (by omega) T,
      Finset.sum_range_succ, hcoeff, one_smul] at h0
    -- {lit}`T ^ d v = -∑_{i<d} pᵢ T ^ i v`
    have hTdv : (T ^ d) v = -∑ i ∈ Finset.range d, (minpoly F T).coeff i • (T ^ i) v := by
      have h := congrArg (fun S : V →ₗ[F] V => S v) (eq_neg_of_add_eq_zero_right h0)
      simpa [LinearMap.sum_apply, LinearMap.smul_apply] using h
    have hsplit : (T ^ n) v = (T ^ (n - d)) ((T ^ d) v) := by
      rw [← Module.End.mul_apply, ← pow_add]
      congr 2
      omega
    rw [hsplit, hTdv, map_neg, map_sum]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    have hpow : (T ^ (n - d)) ((T ^ i) v) = (T ^ (n - d + i)) v := by
      rw [← Module.End.mul_apply, ← pow_add]
    rw [hpow]
    have := Finset.mem_range.mp hi
    exact hgen ⟨n - d + i, by omega⟩
  -- Hence {lit}`W` is invariant under {lit}`T`…
  have hinv : ∀ w ∈ W, T w ∈ W := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hstep : T ((T ^ (i : ℕ)) v) = (T ^ ((i : ℕ) + 1)) v := by
        rw [pow_succ']; rfl
      rw [hstep]
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt i.isLt) with h | h
      · exact hgen ⟨(i : ℕ) + 1, h⟩
      · have h' : (i : ℕ) + 1 = n := h
        rw [h']; exact hTn
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact W.smul_mem a hx
  -- …so it contains every power of {lit}`T` applied to {lit}`v`.
  have hmem : ∀ i : ℕ, (T ^ i) v ∈ W := by
    intro i
    induction i with
    | zero =>
      rcases Nat.eq_zero_or_pos n with h | h
      · have hv : v = 0 := (finrank_zero_iff_forall_zero.mp (hn ▸ h)) v
        simp [hv]
      · simpa using hgen ⟨0, h⟩
    | succ i ih =>
      have hstep : (T ^ (i + 1)) v = T ((T ^ i) v) := by rw [pow_succ']; rfl
      rw [hstep]
      exact hinv _ ih
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact hmem _
  · rintro x ⟨i, rfl⟩
    have := i.isLt
    exact ⟨⟨(i : ℕ), by omega⟩, rfl⟩

open LADR.Section_3C (matrixOf) in
/-- 5B.11 (a) On a two-dimensional {lit}`V`, with
{lit}`ℳ(T) = (a c; b d)`: {lit}`T² − (a + d)T + (ad − bc)I = 0`. -/
theorem exercise_5B_11a {v : Fin 2 → V} (hv : IsBasis F v) (T : V →ₗ[F] V) :
    T ^ 2 - (matrixOf hv hv T 0 0 + matrixOf hv hv T 1 1) • T +
      (matrixOf hv hv T 0 0 * matrixOf hv hv T 1 1 -
        matrixOf hv hv T 1 0 * matrixOf hv hv T 0 1) • LinearMap.id = 0 := by
  -- {lit}`T v₀ = a v₀ + b v₁` and {lit}`T v₁ = c v₀ + d v₁`; expand both sides
  -- on the basis and compare coefficients.
  have hspec : ∀ k, T (v k) = ∑ j, matrixOf hv hv T j k • v j :=
    LADR.Section_3C.matrixOf_spec hv hv T
  simp only [Fin.sum_univ_two] at hspec
  refine hv.toModuleBasis.ext fun i => ?_
  rw [IsBasis.toModuleBasis_apply]
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply, pow_two,
      Module.End.mul_apply, hspec, map_add, map_smul, smul_add, smul_smul] <;>
    module

open LADR.Section_3C (matrixOf) in
/-- 5B.11 (b), first case: if the matrix is {lit}`aI`, the minimal
polynomial is {lit}`z − a`. -/
theorem exercise_5B_11b1 [Finite F V] {v : Fin 2 → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hb : matrixOf hv hv T 1 0 = 0)
    (hc : matrixOf hv hv T 0 1 = 0)
    (had : matrixOf hv hv T 0 0 = matrixOf hv hv T 1 1) :
    minpoly F T = Polynomial.X - Polynomial.C (matrixOf hv hv T 0 0) := by
  -- the matrix is {lit}`a I`, so {lit}`T` itself is {lit}`a I`
  have hspec : ∀ k, T (v k) = ∑ j, matrixOf hv hv T j k • v j :=
    LADR.Section_3C.matrixOf_spec hv hv T
  simp only [Fin.sum_univ_two] at hspec
  have hT : T = algebraMap F (Module.End F V) (matrixOf hv hv T 0 0) := by
    refine hv.toModuleBasis.ext fun i => ?_
    rw [IsBasis.toModuleBasis_apply, Module.algebraMap_end_apply]
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, hspec, hb, hc, had, zero_smul,
        add_zero, zero_add]
  have : Nontrivial V := ⟨hv.toModuleBasis 0, 0, hv.toModuleBasis.ne_zero 0⟩
  conv_lhs => rw [hT]
  exact minpoly.eq_X_sub_C _ _

open LADR.Section_3C (matrixOf) in
/-- 5B.11 (b), second case: otherwise the minimal polynomial is
{lit}`z² − (a + d)z + (ad − bc)`. -/
theorem exercise_5B_11b2 [Finite F V] {v : Fin 2 → V} (hv : IsBasis F v)
    (T : V →ₗ[F] V)
    (h : ¬ (matrixOf hv hv T 1 0 = 0 ∧ matrixOf hv hv T 0 1 = 0 ∧
      matrixOf hv hv T 0 0 = matrixOf hv hv T 1 1)) :
    minpoly F T = Polynomial.X ^ 2 -
      Polynomial.C (matrixOf hv hv T 0 0 + matrixOf hv hv T 1 1) *
        Polynomial.X +
      Polynomial.C (matrixOf hv hv T 0 0 * matrixOf hv hv T 1 1 -
        matrixOf hv hv T 1 0 * matrixOf hv hv T 0 1) := by
  -- by contradiction
  -- use above that the deg 2 equation holds
  -- so it has to be linear, use (1 0) (0 1) and (1 1), to derive b = c = 0, and a = d
  set p : Polynomial F := Polynomial.X ^ 2 -
      Polynomial.C (matrixOf hv hv T 0 0 + matrixOf hv hv T 1 1) * Polynomial.X +
      Polynomial.C (matrixOf hv hv T 0 0 * matrixOf hv hv T 1 1 -
        matrixOf hv hv T 1 0 * matrixOf hv hv T 0 1) with hp
  -- A scalar operator has matrix {lit}`γ I`, which is the excluded case.
  have hscal : ∀ γ : F, ¬ (∀ x : V, T x = γ • x) := by
    intro γ hγ
    have hM : ∀ j k : Fin 2, matrixOf hv hv T j k = if j = k then γ else 0 := by
      intro j k
      rw [LADR.Section_3C.matrixOf_apply, hγ, map_smul,
        ← IsBasis.toModuleBasis_apply hv k, Module.Basis.repr_self]
      by_cases hjk : j = k <;> simp [hjk]
    exact h ⟨by simp [hM], by simp [hM], by simp [hM]⟩
  refine (minpoly.unique F T ?_ ?_ fun q hq hq0 => ?_).symm
  · rw [hp]; monicity!
  · -- 5B.11 (a) is exactly {lit}`p(T) = 0`
    rw [hp]
    rw [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, Polynomial.aeval_C, ← Algebra.smul_def,
      Algebra.algebraMap_eq_smul_one]
    exact exercise_5B_11a hv T
  · have hdeg : p.degree = 2 := by rw [hp]; compute_degree!
    rw [hdeg]
    exact two_le_degree_of_not_scalar hscal hq hq0

/-- The minimal polynomial of {lit}`T_ex_5A_42 n` — to be determined by the
solver. -/
-- ∏ i : Fin n, (X - C (i + 1))
-- since 1, …, n are the eigenvalues, with the standard basis vectors as
-- eigenvectors, the minimal polynomial is the product of the linear factors
-- corresponding to the eigenvalues
noncomputable def minpoly_5B_12 (n : ℕ) : Polynomial ℝ :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C ((i : ℕ) + 1 : ℝ))

open LADR.Section_5A (T_ex_5A_42 aeval_T_ex_5A_42_apply exercise_5A_42a) in
/-- 5B.12 Find the minimal polynomial of
{lit}`T(x₁, …, xₙ) = (x₁, 2x₂, …, nxₙ)`. -/
theorem exercise_5B_12 (n : ℕ) :
    minpoly ℝ (T_ex_5A_42 n) = minpoly_5B_12 n := by
  classical
  have hmonic : (minpoly_5B_12 n).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hmin_ne : minpoly ℝ (T_ex_5A_42 n) ≠ 0 :=
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  -- the {lit}`n` distinct eigenvalues {lit}`1, …, n`, as a {lit}`Finset`
  have hinj : Function.Injective (fun i : Fin n => ((i : ℕ) + 1 : ℝ)) := by
    intro i j hij
    simp only [add_left_inj, Nat.cast_inj] at hij
    exact Fin.ext hij
  set Z : Finset ℝ := Finset.image (fun i : Fin n => ((i : ℕ) + 1 : ℝ)) Finset.univ with hZ
  have hprodZ : ∏ x ∈ Z, (Polynomial.X - Polynomial.C x) = minpoly_5B_12 n := by
    rw [hZ, Finset.prod_image fun i _ j _ h => hinj h]
    rfl
  have hcardZ : Multiset.card Z.val = n := by
    rw [← Finset.card_def, hZ, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  -- First: {lit}`1, …, n` are eigenvalues of {lit}`T` (5A.42 (a)), hence — by
  -- 5.27 (a) — roots of the minimal polynomial.
  have heig : ∀ i : Fin n, HasEigenvalue (T_ex_5A_42 n) ((i : ℕ) + 1 : ℝ) :=
    fun i => ((exercise_5A_42a n).1 _).mpr ⟨i, rfl⟩
  have hle : Z.val ≤ (minpoly ℝ (T_ex_5A_42 n)).roots := by
    refine Finset.val_le_iff_val_subset.mpr fun x hx => ?_
    simp only [hZ, Finset.mem_val, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (Polynomial.mem_roots hmin_ne).mpr ((isEigenvalue_iff_isRoot _ _).mp (heig i))
  -- Second: the product of those linear factors annihilates {lit}`T`, so the
  -- minimal polynomial divides it — whence it splits and has degree at most
  -- {lit}`n`.
  have hann : aeval (T_ex_5A_42 n) (minpoly_5B_12 n) = 0 := by
    refine LinearMap.ext fun u => funext fun i => ?_
    have hz : Polynomial.eval ((i : ℕ) + 1 : ℝ) (minpoly_5B_12 n) = 0 := by
      rw [minpoly_5B_12, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [aeval_T_ex_5A_42_apply, hz, zero_mul]
    simp
  have hdvd : minpoly ℝ (T_ex_5A_42 n) ∣ minpoly_5B_12 n := minpoly.dvd ℝ _ hann
  have hpsplit : (minpoly_5B_12 n).Splits :=
    Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _
  have hsplit : (minpoly ℝ (T_ex_5A_42 n)).Splits := hpsplit.of_dvd hmonic.ne_zero hdvd
  have hdegle : (minpoly ℝ (T_ex_5A_42 n)).natDegree ≤ n := by
    refine le_trans (Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero) ?_
    rw [minpoly_5B_12, Polynomial.natDegree_prod _ _ fun i _ => Polynomial.X_sub_C_ne_zero _]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_one, le_refl]
  -- So the roots are exactly {lit}`1, …, n`, each simple.
  have hroots : (minpoly ℝ (T_ex_5A_42 n)).roots = Z.val :=
    (Multiset.eq_of_le_of_card_le hle
      (by rw [hcardZ]; exact le_trans (Polynomial.card_roots' _) hdegle)).symm
  -- 5.27 (b): the minimal polynomial is the product of {lit}`z − λ` over its roots.
  rw [minpoly_eq_prod_roots_of_splits _ hsplit, hroots, ← hprodZ,
    Finset.prod_eq_multiset_prod]

/-- 5B.13 -/
theorem exercise_5B_13 [Finite F V] (T : V →ₗ[F] V) (p : Polynomial F) :
    ∃! r : Polynomial F, aeval T r = aeval T p ∧
      r.degree < (minpoly F T).degree := by
  -- polynomial division p = k * minpoly + r
  -- then applying T gives p = r, and r < deg minpoly by division
  have hmonic : (minpoly F T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  have hmod : aeval T (p %ₘ minpoly F T) = aeval T p := by
    conv_rhs => rw [← Polynomial.modByMonic_add_div p (minpoly F T)]
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero]
  refine ⟨p %ₘ minpoly F T, ⟨hmod, Polynomial.degree_modByMonic_lt p hmonic⟩, ?_⟩
  -- Two such remainders differ by a multiple of the minimal polynomial of
  -- smaller degree, hence by zero.
  rintro r ⟨hr, hrdeg⟩
  have hdvd : minpoly F T ∣ r - p %ₘ minpoly F T :=
    minpoly.dvd F T (by rw [map_sub, hr, hmod, sub_self])
  have hdeglt : (r - p %ₘ minpoly F T).degree < (minpoly F T).degree :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt hrdeg (Polynomial.degree_modByMonic_lt p hmonic))
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_dvd_of_degree_lt hdvd hdeglt)

/-- The polynomial {lit}`r` with its first {lit}`k + 1` coefficients reversed:
{lit}`∑ᵢ r_{k−i} zⁱ`. -/
private noncomputable def revPoly (r : Polynomial F) (k : ℕ) : Polynomial F :=
  ∑ i ∈ Finset.range (k + 1), Polynomial.C (r.coeff (k - i)) * Polynomial.X ^ i

private theorem degree_revPoly_le (r : Polynomial F) (k : ℕ) :
    (revPoly r k).degree ≤ (k : ℕ) := by
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun i hi => ?_)
  exact (Polynomial.degree_C_mul_X_pow_le _ _).trans
    (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

private theorem revPoly_coeff_zero (r : Polynomial F) (k : ℕ) :
    (revPoly r k).coeff 0 = r.coeff k := by
  simp [revPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

/-- If {lit}`r` annihilates {lit}`A` and {lit}`B` is a left inverse of
{lit}`A`, then the reversed polynomial annihilates {lit}`B`: multiplying
{lit}`∑ⱼ rⱼ Aʲ = 0` on the left by {lit}`Bᵏ` turns {lit}`Aʲ` into
{lit}`B^{k−j}`. -/
private theorem aeval_revPoly {W : Type*} [AddCommGroup W] [Module F W]
    {A B : Module.End F W} (hBA : B * A = 1) (r : Polynomial F) {k : ℕ}
    (hk : r.natDegree ≤ k) (hr : Polynomial.aeval A r = 0) :
    Polynomial.aeval B (revPoly r k) = 0 := by
  have hpow : ∀ j, B ^ j * A ^ j = 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc B A (A ^ j), hBA, one_mul, ih]
  have hmul : ∀ j ∈ Finset.range (k + 1), B ^ k * A ^ j = B ^ (k - j) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc B ^ k * A ^ j = B ^ (k - j) * B ^ j * A ^ j := by
          rw [← pow_add]; congr 2; omega
      _ = B ^ (k - j) := by rw [mul_assoc, hpow, mul_one]
  calc Polynomial.aeval B (revPoly r k)
      = ∑ i ∈ Finset.range (k + 1), r.coeff (k - i) • B ^ i := by
        simp only [revPoly, map_sum, map_mul, map_pow, Polynomial.aeval_C,
          Polynomial.aeval_X, ← Algebra.smul_def]
    _ = ∑ j ∈ Finset.range (k + 1), r.coeff j • B ^ (k - j) := by
        rw [← Finset.sum_range_reflect (fun j => r.coeff j • B ^ (k - j)) (k + 1)]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 : k + 1 - 1 - i = k - i := by omega
        rw [h1]
        congr 2
        omega
    _ = B ^ k * ∑ j ∈ Finset.range (k + 1), r.coeff j • A ^ j := by
        rw [Finset.mul_sum]
        exact (Finset.sum_congr rfl fun j hj => by
          rw [mul_smul_comm, hmul j hj]).symm
    _ = B ^ k * Polynomial.aeval A r := by
        rw [Polynomial.aeval_eq_sum_range' (n := k + 1) (by omega) A]
    _ = 0 := by rw [hr, mul_zero]

open Polynomial in
/-- The minimal polynomial of {lit}`T⁻¹` in 5B.14, given that of {lit}`T` —
to be determined by the solver. -/
noncomputable def minpoly_5B_14 : Polynomial ℝ :=
  X ^ 5 + (5 / 4 : ℝ) • X ^ 4 - (6 / 4 : ℝ) • X ^ 3 - (7 / 4 : ℝ) • X ^ 2 +
    (2 / 4 : ℝ) • X + (1 / 4 : ℝ) • 1

open Polynomial in
/-- 5B.14 Given the minimal polynomial of an invertible {lit}`T`, find the
minimal polynomial of {lit}`T⁻¹`. -/
theorem exercise_5B_14 {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (T : V →ₗ[ℝ] V) (hT : IsInvertible T)
    (hmin : minpoly ℝ T = 4 + 5 • X - 6 • X ^ 2 - 7 • X ^ 3 + 2 • X ^ 4 + X ^ 5) :
    minpoly ℝ hT.inv = minpoly_5B_14 := by
  -- apply T^-5 to the minpoly equation. by contra smaller deg can't exist
  have hST : hT.inv * T = 1 := hT.inv_comp
  have hTS : T * hT.inv = 1 := hT.comp_inv
  have hpne : minpoly ℝ T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  -- {lit}`compute_degree` prefers {lit}`C a * X ^ n` to {lit}`a • X ^ n`
  have hC : minpoly_5B_14 = X ^ 5 + C (5 / 4) * X ^ 4 - C (6 / 4) * X ^ 3 -
      C (7 / 4) * X ^ 2 + C (2 / 4) * X + C (1 / 4) := by
    simp [minpoly_5B_14, Polynomial.smul_eq_C_mul]
  have hpdeg : (minpoly ℝ T).natDegree = 5 := by
    rw [hmin]
    compute_degree!
    simp [Polynomial.coeff_X]
  -- reversing the coefficients of the minimal polynomial gives {lit}`4 q`
  have hrev : revPoly (minpoly ℝ T) 5 = (4 : ℝ) • minpoly_5B_14 := by
    simp only [revPoly, hmin, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [minpoly_5B_14, Polynomial.coeff_X, Polynomial.smul_eq_C_mul]
    simp only [mul_add, mul_sub, ← mul_assoc, ← Polynomial.C_mul]
    norm_num
    ring
  have hq : aeval hT.inv minpoly_5B_14 = 0 := by
    have h := aeval_revPoly hST (minpoly ℝ T) (k := 5) (by omega) (minpoly.aeval ℝ T)
    rw [hrev, map_smul] at h
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hmonic : minpoly_5B_14.Monic := by rw [hC]; monicity!
  refine (minpoly.unique ℝ _ hmonic hq fun r hr hr0 => ?_).symm
  have hdeg5 : minpoly_5B_14.degree = 5 := by rw [hC]; compute_degree!
  rw [hdeg5]
  by_contra hlt
  push Not at hlt
  have hrnat : r.natDegree < 5 :=
    (Polynomial.natDegree_lt_iff_degree_lt hr.ne_zero).mpr (by exact_mod_cast hlt)
  -- reversing {lit}`r` gives a nonzero polynomial of degree {lit}`< 5`
  -- annihilating {lit}`T`, contradicting minimality of its minimal polynomial
  have h2 := aeval_revPoly hTS r (k := r.natDegree) le_rfl hr0
  have hne : revPoly r r.natDegree ≠ 0 := by
    intro hzero
    have hc := revPoly_coeff_zero r r.natDegree
    rw [hzero, hr.coeff_natDegree, Polynomial.coeff_zero] at hc
    exact zero_ne_one hc
  have hle := minpoly.degree_le_of_ne_zero ℝ T hne h2
  rw [Polynomial.degree_eq_natDegree hpne, hpdeg] at hle
  have h5 : (5 : ℕ) ≤ r.natDegree := by
    exact_mod_cast hle.trans (degree_revPoly_le r r.natDegree)
  omega

/-- 5B.15 -/
theorem exercise_5B_15 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (hV : 0 < finrank ℂ V) (T : V →ₗ[ℂ] V) :
    ¬ Continuous (fun γ : ℂ =>
      (finrank ℂ (range (T - γ • (LinearMap.id : V →ₗ[ℂ] V))) : ℝ)) := by
  -- by contra
  -- if ct, it has to be constant because rank is discrete
  -- but we proved their is at least one eigenvalue, so non inj at that
  -- but there are finitely many eigenvalues, leading to a contradiction
  intro hcont
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hV
  set f : ℂ → ℝ := fun γ =>
    (finrank ℂ (range (T - γ • (LinearMap.id : V →ₗ[ℂ] V))) : ℝ) with hf
  -- at an eigenvalue the map is not injective, so the range is a proper subspace
  obtain ⟨γ₀, hγ₀⟩ := exists_eigenvalue T
  set m := finrank ℂ (range (T - γ₀ • (LinearMap.id : V →ₗ[ℂ] V))) with hm
  have hrank0 : m < finrank ℂ V := by
    refine Submodule.finrank_lt ?_
    intro htop
    obtain ⟨v, hv, hTv⟩ := Module.End.hasEigenvalue_iff_exists.mp hγ₀
    have hinj : Function.Injective (T - γ₀ • (LinearMap.id : V →ₗ[ℂ] V)) :=
      LinearMap.injective_iff_surjective.mpr (LinearMap.range_eq_top.mp htop)
    exact hv (hinj (by simp [LinearMap.sub_apply, hTv]))
  -- away from the finitely many eigenvalues the rank is full
  have hpne : minpoly ℂ T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ : ℂ, ¬ HasEigenvalue T γ := by
    have hsub : {x : ℂ | (minpoly ℂ T).IsRoot x} ⊆ ↑(minpoly ℂ T).roots.toFinset := by
      intro x hx
      simpa [Multiset.mem_toFinset, Polynomial.mem_roots hpne] using hx
    obtain ⟨γ, hγ⟩ := (Set.Finite.infinite_compl
      (Set.Finite.subset (minpoly ℂ T).roots.toFinset.finite_toSet hsub)).nonempty
    exact ⟨γ, fun hc => hγ ((isEigenvalue_iff_isRoot T γ).mp hc)⟩
  have hrank1 : f γ₁ = (finrank ℂ V : ℝ) := by
    have hker : ker (T - γ₁ • (LinearMap.id : V →ₗ[ℂ] V)) = ⊥ := by
      by_contra hbot
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hbot
      refine hγ₁ (Module.End.hasEigenvalue_iff_exists.mpr ⟨v, hv0, ?_⟩)
      have hmem := LinearMap.mem_ker.mp hv
      simpa [LinearMap.sub_apply, sub_eq_zero] using hmem
    -- rank–nullity: the kernel is trivial, so the range is everything
    have hsum := LADR.Section_3B.finrank_ker_add_finrank_range
      (T - γ₁ • (LinearMap.id : V →ₗ[ℂ] V))
    have hkr0 : finrank ℂ (ker (T - γ₁ • (LinearMap.id : V →ₗ[ℂ] V))) = 0 :=
      Submodule.finrank_eq_zero.mpr hker
    rw [hf]
    simp only
    exact_mod_cast (by omega :
      finrank ℂ (range (T - γ₁ • (LinearMap.id : V →ₗ[ℂ] V))) = finrank ℂ V)
  -- a continuous integer-valued function on the connected plane would have to
  -- take the half-integer value {lit}`m + 1/2`
  have hmem : (m : ℝ) + 1 / 2 ∈ Set.Icc (f γ₀) (f γ₁) := by
    have hle : ((m : ℝ) + 1) ≤ (finrank ℂ V : ℝ) := by exact_mod_cast hrank0
    exact ⟨by rw [hf]; simp only [← hm]; linarith, by rw [hrank1]; linarith⟩
  obtain ⟨γ, hγ⟩ := intermediate_value_univ γ₀ γ₁ hcont hmem
  rw [hf] at hγ
  simp only at hγ
  have hcast : ((2 * finrank ℂ (range (T - γ • (LinearMap.id : V →ₗ[ℂ] V))) : ℕ) : ℝ)
      = ((2 * m + 1 : ℕ) : ℝ) := by push_cast; linarith
  have := Nat.cast_injective hcast
  omega

open LADR.Section_3A (fromFnToFm) in
/-- 5B.16 The companion-matrix operator with last column
{lit}`(−a₀, …, −a_{n−1})` has minimal polynomial
{lit}`a₀ + a₁z + ⋯ + a_{n−1}z^{n−1} + zⁿ`; hence every monic polynomial is
the minimal polynomial of some operator. -/
def companionOp {n : ℕ} (a : Fin n → F) : (Fin n → F) →ₗ[F] (Fin n → F) :=
  LADR.Section_3A.fromFnToFm fun j k =>
    if (k : ℕ) = n - 1 then -(a j)
    else if (j : ℕ) = (k : ℕ) + 1 then 1 else 0

theorem exercise_5B_16 {n : ℕ} (hn : 0 < n) (a : Fin n → F) :
    minpoly F (companionOp a) =
      Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) *
        Polynomial.X ^ (i : ℕ) := by
  -- The whole proof rests on one observation: {lit}`Me₀ = e₁, …, Me_{n−2} = e_{n−1}`
  -- and {lit}`Me_{n−1} = −a₀e₀ − ⋯ − a_{n−1}e_{n−1}`, i.e. {lit}`Mⁱe₀ = eᵢ` for
  -- {lit}`i < n`. That gives both {lit}`p(M) = 0` and the minimality of {lit}`p`.
  -- The standard basis of {lit}`Fⁿ`, indexed by {lit}`ℕ` to avoid {lit}`Fin` arithmetic.
  set e : ℕ → (Fin n → F) := fun i j => if (j : ℕ) = i then 1 else 0 with he
  set M := companionOp a with hM
  set p : Polynomial F :=
    Polynomial.X ^ n + ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) with hp
  -- Every vector is a combination of the basis vectors.
  have hexpand : ∀ v : Fin n → F, v = ∑ k : Fin n, v k • e (k : ℕ) := by
    intro v
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [he]
    · intro b _ hb
      have : (j : ℕ) ≠ (b : ℕ) := fun hc => hb (Fin.ext hc).symm
      simp [he, this]
    · simp
  -- The action on a basis vector reads off the corresponding column of the matrix.
  have hcol : ∀ (i : ℕ), i < n → ∀ j : Fin n,
      M (e i) j = (if i = n - 1 then -(a j) else if (j : ℕ) = i + 1 then 1 else 0) := by
    intro i hi j
    simp only [hM, companionOp, LADR.Section_3A.fromFnToFm, LinearMap.coe_mk,
      AddHom.coe_mk, he]
    rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ i := fun hc => hb (Fin.ext hc)
      simp [this]
    · simp
  -- {lit}`Meᵢ = eᵢ₊₁` for {lit}`i + 1 < n`
  have hstep : ∀ i : ℕ, i + 1 < n → M (e i) = e (i + 1) := by
    intro i hi
    funext j
    rw [hcol i (by omega) j, if_neg (by omega)]
  -- {lit}`Me_{n−1} = −a`
  have hlast : M (e (n - 1)) = -a := by
    funext j
    rw [hcol (n - 1) (by omega) j, if_pos rfl]
    simp
  -- {lit}`Mⁱe₀ = eᵢ` for {lit}`i < n`
  have hpow : ∀ i : ℕ, i < n → (M ^ i) (e 0) = e i := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [pow_succ', Module.End.mul_apply, ih (by omega), hstep i hi]
  -- Hence {lit}`p(M)e₀ = Mⁿe₀ + ∑ᵢ aᵢeᵢ = −a + a = 0`.
  have hMn : (M ^ n) (e 0) = -a := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ', Module.End.mul_apply, hpow m (by omega)]
    simpa using hlast
  have hpe0 : (aeval M p) (e 0) = 0 := by
    simp only [hp, map_add, map_sum, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C, ← Algebra.smul_def, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.smul_apply]
    have hrest : ∑ i : Fin n, a i • (M ^ (i : ℕ)) (e 0) = a := by
      conv_rhs => rw [hexpand a]
      exact Finset.sum_congr rfl fun i _ => by rw [hpow i i.isLt]
    rw [hMn, hrest, neg_add_cancel]
  -- {lit}`p(M)` commutes with the powers of {lit}`M`
  have hcomm : ∀ (k : ℕ) (v : Fin n → F),
      (aeval M p) ((M ^ k) v) = (M ^ k) ((aeval M p) v) := by
    intro k v
    have h : (aeval M p) * (M ^ k) = (M ^ k) * (aeval M p) := by
      have h1 : (aeval M p) * (M ^ k) = aeval M (p * Polynomial.X ^ k) := by simp
      have h2 : (M ^ k) * (aeval M p) = aeval M (Polynomial.X ^ k * p) := by simp
      rw [h1, h2, mul_comm]
    rw [← Module.End.mul_apply, h, Module.End.mul_apply]
  -- so {lit}`p(M)eₖ = p(M)Mᵏe₀ = Mᵏp(M)e₀ = 0` on every basis vector
  have hann : aeval M p = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [hexpand v, map_sum, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, ← hpow k k.isLt, hcomm, hpe0, map_zero, smul_zero]
  -- {lit}`p` is monic of degree {lit}`n`
  have hdegsum : (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).degree
      < (n : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i _ => ?_
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
      (WithBot.coe_lt_coe.mpr i.isLt)
  have hmonic : p.Monic := by
    rw [hp]
    refine (Polynomial.monic_X_pow n).add_of_left ?_
    rw [Polynomial.degree_X_pow]
    exact hdegsum
  have hdeg : p.degree = (n : WithBot ℕ) := by
    rw [hp, Polynomial.degree_add_eq_left_of_degree_lt
      (by rw [Polynomial.degree_X_pow]; exact hdegsum), Polynomial.degree_X_pow]
  -- Minimality: a monic {lit}`q` of degree {lit}`< n` would give
  -- {lit}`q(M)e₀ = ∑ᵢ qᵢeᵢ = 0`, forcing all its coefficients to vanish.
  refine (minpoly.unique F M hmonic hann fun q hq hq0 => ?_).symm
  rw [hdeg]
  by_contra hlt
  push Not at hlt
  have hqnat : q.natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hq.ne_zero).mpr hlt
  have h0 : (aeval M q) (e 0) = 0 := by rw [hq0]; simp
  rw [Polynomial.aeval_eq_sum_range' hqnat M] at h0
  have hz : ∀ j : Fin n, q.coeff (j : ℕ) = 0 := by
    intro j
    have hsum2 : (∑ i ∈ Finset.range n, q.coeff i • (M ^ i)) (e 0)
        = ∑ i ∈ Finset.range n, q.coeff i • e i := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
      exact Finset.sum_congr rfl fun i hi => by rw [hpow i (Finset.mem_range.mp hi)]
    rw [hsum2] at h0
    have hj := congrFun h0 j
    simpa [he, Finset.sum_apply, Finset.sum_ite_eq, j.isLt] using hj
  exact one_ne_zero (hq.coeff_natDegree.symm.trans (hz ⟨q.natDegree, hqnat⟩))

/-- 5B.17 -/
theorem exercise_5B_17 [Finite F V] (T : V →ₗ[F] V) (γ : F) :
    minpoly F (T - γ • (LinearMap.id : V →ₗ[F] V)) =
      (minpoly F T).comp (Polynomial.X + γ • 1) := by
  -- (p ∘ q) (T - γ • id) = p(T) where q(X) = X + γ
  -- but p ∘ q = p' ↔ p = p' ∘ q⁻¹, where q⁻¹(X) = X - γ
  -- since the two evals are equivalent the min polys are related
  set S := T - γ • (LinearMap.id : V →ₗ[F] V) with hS
  -- the polynomial API is stated for {lit}`C γ` rather than {lit}`γ • 1`
  rw [show (γ • 1 : Polynomial F) = Polynomial.C γ by
    rw [Polynomial.smul_eq_C_mul, mul_one]]
  -- substituting {lit}`X + γ` turns {lit}`S` back into {lit}`T`, and
  -- substituting {lit}`X − γ` turns {lit}`T` into {lit}`S`
  have hSX : aeval S (Polynomial.X + Polynomial.C γ) = T := by
    rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, hS, Module.End.one_eq_id, sub_add_cancel]
  have hTX : aeval T (Polynomial.X - Polynomial.C γ) = S := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id, hS]
  have hmonicP : (minpoly F T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  have hmonic : ((minpoly F T).comp (Polynomial.X + Polynomial.C γ)).Monic :=
    hmonicP.comp_X_add_C γ
  refine (minpoly.unique F S hmonic ?_ fun q hq hq0 => ?_).symm
  · -- {lit}`p(X + γ)` evaluated at {lit}`S` is {lit}`p` evaluated at {lit}`S + γ = T`
    rw [Polynomial.aeval_comp, hSX, minpoly.aeval]
  · -- conversely {lit}`q(X − γ)` annihilates {lit}`T`, so it is at least as long
    -- as {lit}`p`; composing with a degree-one polynomial preserves the degree
    have h0 : aeval T (q.comp (Polynomial.X - Polynomial.C γ)) = 0 := by
      rw [Polynomial.aeval_comp, hTX, hq0]
    have hle := minpoly.min F T (hq.comp_X_sub_C γ) h0
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hq.ne_zero]
    rw [Polynomial.degree_eq_natDegree hmonicP.ne_zero,
      Polynomial.degree_eq_natDegree (hq.comp_X_sub_C γ).ne_zero,
      Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one] at hle
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    exact hle

/-- Substituting {lit}`c X` into a polynomial and evaluating at {lit}`A` is the
same as evaluating at {lit}`c A`. -/
private theorem aeval_comp_C_mul_X (A : V →ₗ[F] V) (c : F) (r : Polynomial F) :
    aeval A (r.comp (Polynomial.C c * Polynomial.X)) = aeval (c • A) r := by
  rw [Polynomial.aeval_comp, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    ← Algebra.smul_def]

/-- Rescaling the variable by {lit}`c ≠ 0` and renormalizing by the resulting
leading coefficient keeps a polynomial monic and preserves its degree. -/
private theorem monic_scale {p : Polynomial F} (hp : p.Monic) {c : F} (hc : c ≠ 0) :
    ((c ^ p.natDegree)⁻¹ • p.comp (Polynomial.C c * Polynomial.X)).Monic ∧
      ((c ^ p.natDegree)⁻¹ • p.comp (Polynomial.C c * Polynomial.X)).natDegree
        = p.natDegree := by
  have hdeg1 : (Polynomial.C c * Polynomial.X).natDegree = 1 :=
    Polynomial.natDegree_C_mul_X c hc
  have hlc : (Polynomial.C c * Polynomial.X).leadingCoeff = c := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X,
      mul_one]
  have hcomp : (p.comp (Polynomial.C c * Polynomial.X)).natDegree = p.natDegree := by
    rw [Polynomial.natDegree_comp, hdeg1, mul_one]
  have hcl : (p.comp (Polynomial.C c * Polynomial.X)).leadingCoeff = c ^ p.natDegree := by
    rw [Polynomial.leadingCoeff_comp (by rw [hdeg1]; exact one_ne_zero), hp.leadingCoeff,
      one_mul, hlc]
  have hne : (c ^ p.natDegree)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  constructor
  · rw [Polynomial.Monic.def, Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_C, hcl, inv_mul_cancel₀ (pow_ne_zero _ hc)]
  · rw [Polynomial.smul_eq_C_mul, Polynomial.natDegree_mul (by simpa using hne) ?_,
      Polynomial.natDegree_C, zero_add, hcomp]
    intro h0
    rw [h0] at hcl
    simp only [Polynomial.leadingCoeff_zero] at hcl
    exact pow_ne_zero _ hc hcl.symm

/-- 5B.18 -/
theorem exercise_5B_18 [Finite F V] (T : V →ₗ[F] V) (γ : F) (hγ : γ ≠ 0) :
    minpoly F (γ • T) = (γ ^ (minpoly F T).natDegree) • (minpoly F T).comp (γ⁻¹ • Polynomial.X) := by
  -- (p ∘ q) (γ T) = p(T) where q(X) = X / γ
  -- but p ∘ q = p' ↔ p = p' ∘ q⁻¹, where q⁻¹(X) = γ X
  -- finally we need to account for the scalar factor γ^n when relating the minimal polynomials.
  -- so they are both monic.
  have hγi : γ⁻¹ ≠ 0 := inv_ne_zero hγ
  have hpmonic : (minpoly F T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  -- the polynomial API is stated for {lit}`C _ * _` rather than {lit}`_ • _`
  rw [Polynomial.smul_eq_C_mul γ⁻¹ (p := Polynomial.X),
    show (γ ^ (minpoly F T).natDegree) = ((γ⁻¹ ^ (minpoly F T).natDegree)⁻¹) by
      rw [inv_pow, inv_inv]]
  obtain ⟨hmonic, hdeg⟩ := monic_scale hpmonic hγi
  refine (minpoly.unique F (γ • T) hmonic ?_ fun q hq hq0 => ?_).symm
  · -- {lit}`p(X/γ)` evaluated at {lit}`γT` is {lit}`p` evaluated at
    -- {lit}`γ⁻¹ • (γ • T) = T`
    rw [map_smul, aeval_comp_C_mul_X, smul_smul, inv_mul_cancel₀ hγ, one_smul,
      minpoly.aeval, smul_zero]
  · -- conversely {lit}`q(γX)`, renormalized, is monic of the same degree and
    -- annihilates {lit}`T`
    obtain ⟨hmonic', hdeg'⟩ := monic_scale hq hγ
    have h0 : aeval T ((γ ^ q.natDegree)⁻¹ • q.comp (Polynomial.C γ * Polynomial.X))
        = 0 := by
      rw [map_smul, aeval_comp_C_mul_X, hq0, smul_zero]
    have hle := minpoly.min F T hmonic' h0
    rw [Polynomial.degree_eq_natDegree hpmonic.ne_zero,
      Polynomial.degree_eq_natDegree hmonic'.ne_zero, hdeg'] at hle
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hq.ne_zero, hdeg]
    exact_mod_cast hle

/-- 5B.19 -/
theorem exercise_5B_19 [Finite F V] (T : V →ₗ[F] V) :
    finrank F (range (Polynomial.aeval (R := F) T).toLinearMap) =
      (minpoly F T).natDegree := by
  -- let n = deg min poly
  -- 1) 1...X^n-1 linear idp. otherwise contradiction with min poly
  -- 2) X^n and all X^m , m ≥ n, are all in span {1, X, ..., X^(n-1)} by
  -- using the min poly relation
  have hmonic : (minpoly F T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  -- 1) the powers below the degree of the minimal polynomial are independent
  have hli : LinearIndependent F
      (fun i : Fin (minpoly F T).natDegree => T ^ (i : ℕ)) := linearIndependent_pow T
  -- 2) every {lit}`p(T)` lies in their span: divide {lit}`p` by the minimal
  -- polynomial, which leaves a remainder of degree {lit}`< n`
  have hspan : range (Polynomial.aeval (R := F) T).toLinearMap
      = Submodule.span F
        (Set.range fun i : Fin (minpoly F T).natDegree => T ^ (i : ℕ)) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨p, rfl⟩
      have hmod : aeval T (p %ₘ minpoly F T) = aeval T p := by
        conv_rhs => rw [← Polynomial.modByMonic_add_div p (minpoly F T)]
        rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero]
      rw [AlgHom.toLinearMap_apply, ← hmod]
      rcases eq_or_ne (p %ₘ minpoly F T) 0 with h0 | h0
      · rw [h0, map_zero]
        exact Submodule.zero_mem _
      · have hlt : (p %ₘ minpoly F T).natDegree < (minpoly F T).natDegree := by
          refine (Polynomial.natDegree_lt_iff_degree_lt h0).mpr ?_
          rw [← Polynomial.degree_eq_natDegree hmonic.ne_zero]
          exact Polynomial.degree_modByMonic_lt p hmonic
        rw [Polynomial.aeval_eq_sum_range' hlt T]
        refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨Polynomial.X ^ (i : ℕ), by simp⟩
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

open Polynomial in
/-- 5B.20 -/
theorem exercise_5B_20 (T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ))
    (hev : ∀ γ : ℝ, HasEigenvalue T γ ↔ γ = 3 ∨ γ = 5 ∨ γ = 8) :
    ((T - 3 • LinearMap.id) ^ 2) ∘ₗ ((T - 5 • LinearMap.id) ^ 2) ∘ₗ
      ((T - 8 • LinearMap.id) ^ 2) = 0 := by
  -- p = (z - 3)(z - 5)(z - 8) must divide min poly, because
  -- each is eigenvalue.
  -- two options minpoly deg 3 or 4
  -- if deg3 - minpoly = p, so goal poly q = p ^ 2 , so 0 at T
  -- if def4 - minpoly = p(z - a), but a is eigenvalue so 3,5,8
  -- so minpoly still divides q, so 0 at T
  classical
  set m : Polynomial ℝ := (X - C 3) * ((X - C 5) * (X - C 8)) with hm
  have hmmonic : m.Monic := by
    rw [hm]
    exact (monic_X_sub_C _).mul ((monic_X_sub_C _).mul (monic_X_sub_C _))
  have hmdeg : m.natDegree = 3 := by
    rw [hm, (monic_X_sub_C (3 : ℝ)).natDegree_mul
      ((monic_X_sub_C (5 : ℝ)).mul (monic_X_sub_C (8 : ℝ))),
      (monic_X_sub_C (5 : ℝ)).natDegree_mul (monic_X_sub_C (8 : ℝ))]
    simp
  have hpmonic : (minpoly ℝ T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  -- the roots of the minimal polynomial are the eigenvalues {lit}`3, 5, 8` (5.27)
  have hrootiff : ∀ γ : ℝ, (minpoly ℝ T).IsRoot γ ↔ (γ = 3 ∨ γ = 5 ∨ γ = 8) :=
    fun γ => (isEigenvalue_iff_isRoot T γ).symm.trans (hev γ)
  -- they are distinct, so {lit}`m` divides the minimal polynomial
  have hdvdm : m ∣ minpoly ℝ T := by
    have hle : ({3, 5, 8} : Multiset ℝ) ≤ (minpoly ℝ T).roots := by
      refine (Multiset.le_iff_subset (by norm_num)).mpr fun x hx => ?_
      have hx' : x = 3 ∨ x = 5 ∨ x = 8 := by simpa using hx
      exact (mem_roots hpmonic.ne_zero).mpr ((hrootiff x).mpr hx')
    have := (Multiset.prod_X_sub_C_dvd_iff_le_roots hpmonic.ne_zero _).mpr hle
    simpa [hm, mul_assoc] using this
  obtain ⟨g, hg⟩ := hdvdm
  have hgmonic : g.Monic := hmmonic.of_mul_monic_left (hg ▸ hpmonic)
  -- the minimal polynomial has degree at most {lit}`4` (5.24), so {lit}`g` has
  -- degree at most {lit}`1`
  have hgdeg : g.natDegree ≤ 1 := by
    have h4 := minpoly_natDegree_le T
    rw [hg, hmmonic.natDegree_mul hgmonic, hmdeg] at h4
    simp only [Module.finrank_fin_fun] at h4
    omega
  -- {lit}`g` divides {lit}`m`: either {lit}`g = 1`, or {lit}`g = X − a` with
  -- {lit}`a` an eigenvalue, hence one of {lit}`3, 5, 8`
  have hgm : g ∣ m := by
    rcases Nat.lt_or_ge g.natDegree 1 with h1 | h1
    · rw [hgmonic.natDegree_eq_zero.mp (by omega)]
      exact one_dvd _
    · have hdeg1 : g.natDegree = 1 := le_antisymm hgdeg h1
      have hgX : g = X - C (-(g.coeff 0)) := by
        rw [map_neg, sub_neg_eq_add]
        exact hgmonic.eq_X_add_C hdeg1
      have hroot : (minpoly ℝ T).IsRoot (-(g.coeff 0)) := by
        refine (dvd_iff_isRoot).mp ?_
        rw [← hgX, hg]
        exact Dvd.intro_left _ rfl
      rw [hgX]
      rcases (hrootiff _).mp hroot with h | h | h <;> rw [h, hm]
      · exact ⟨(X - C 5) * (X - C 8), rfl⟩
      · exact ⟨(X - C 3) * (X - C 8), by ring⟩
      · exact ⟨(X - C 3) * (X - C 5), by ring⟩
  -- hence the minimal polynomial divides {lit}`m²`, which is the goal polynomial
  have hdvd : minpoly ℝ T ∣ m * m := by
    rw [hg]
    exact mul_dvd_mul_left m hgm
  -- the numerals in the statement are natural-number scalars
  have hns : ∀ n : ℕ, (n • (LinearMap.id : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)))
      = (n : ℝ) • LinearMap.id := fun n => (Nat.cast_smul_eq_nsmul ℝ n _).symm
  have hfac : ∀ c : ℝ, aeval T (X - C c)
      = T - c • (LinearMap.id : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) := by
    intro c
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]
  have hgoal : ((T - 3 • LinearMap.id) ^ 2) ∘ₗ ((T - 5 • LinearMap.id) ^ 2) ∘ₗ
      ((T - 8 • LinearMap.id) ^ 2) = aeval T (m * m) := by
    rw [show m * m = (X - C 3) ^ 2 * ((X - C 5) ^ 2 * (X - C 8) ^ 2) by rw [hm]; ring]
    simp only [map_mul, map_pow, hfac, Module.End.mul_eq_comp, hns, Nat.cast_ofNat]
  obtain ⟨h, hh⟩ := hdvd
  rw [hgoal, hh, map_mul, minpoly.aeval, zero_mul]

/-- 5B.21 -/
theorem exercise_5B_21 [Finite F V] (T : V →ₗ[F] V) :
    (minpoly F T).natDegree ≤ 1 + finrank F (range T) := by
  -- consider T|range T, its minpoly p is <= rank range T.
  -- so p(T) = 0 for all vectors in the range of T
  -- but (p(z)z) T = 0 for all v, since the first z sends to range T
  -- so minpoly | p(z)z -> minpoly.deg ≤ rank range + T
  have hU : InvariantUnder T (range T) := fun u _ => LinearMap.mem_range_self T u
  have hpdeg : (minpoly F hU.restrict).natDegree ≤ finrank F (range T) :=
    minpoly_natDegree_le hU.restrict
  have hpne : minpoly F hU.restrict ≠ 0 :=
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  -- {lit}`p(T)` kills the range of {lit}`T`, so {lit}`p(T) ∘ T = 0` on all of
  -- {lit}`V`
  have hann : aeval T (minpoly F hU.restrict * Polynomial.X) = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply, LinearMap.zero_apply]
    have hcoe := aeval_restrict_coe hU (minpoly F hU.restrict)
      ⟨T v, LinearMap.mem_range_self T v⟩
    rw [minpoly.aeval] at hcoe
    simpa using hcoe.symm
  have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd F T hann)
    (mul_ne_zero hpne Polynomial.X_ne_zero)
  rw [Polynomial.natDegree_mul hpne Polynomial.X_ne_zero, Polynomial.natDegree_X] at hle
  omega

/-- 5B.22 -/
theorem exercise_5B_22 [Finite F V] (T : V →ₗ[F] V) :
    IsInvertible T ↔ LinearMap.id ∈ Submodule.span F
      (Set.range fun i : Fin (finrank F V) => T ^ ((i : ℕ) + 1)) := by
  -- invertable iff a0 in minpoly is nonzero
  -- -> solve for I from minpoly
  -- <- take the lin combination for I, and build a monic p(T) = 0
  -- minpoly | p(T) = 0, if T | minpoly it would divide p(T) as well,
  -- but a₀ ≠ 0, so T cannot divide the minimal polynomial, so T is invertable
  classical
  have hndeg : (minpoly F T).natDegree ≤ finrank F V := minpoly_natDegree_le T
  -- the minimal-polynomial relation with the constant term split off
  have hsum : (∑ i ∈ Finset.range (finrank F V),
        (minpoly F T).coeff (i + 1) • T ^ (i + 1))
      + (minpoly F T).coeff 0 • (1 : Module.End F V) = 0 := by
    have h : ∑ i ∈ Finset.range (finrank F V + 1), (minpoly F T).coeff i • T ^ i = 0 := by
      rw [← Polynomial.aeval_eq_sum_range' (by omega) T, minpoly.aeval]
    rwa [Finset.sum_range_succ' (fun i => (minpoly F T).coeff i • T ^ i)
      (finrank F V), pow_zero] at h
  constructor
  · -- if {lit}`T` is invertible then {lit}`a₀ ≠ 0` (5.32), so the relation
    -- solves for {lit}`I`
    intro hinv
    have ha0 : (minpoly F T).coeff 0 ≠ 0 :=
      fun h => (not_invertible_iff_minpoly_coeff_zero T).mpr h hinv
    have hkey : (∑ i ∈ Finset.range (finrank F V),
        (minpoly F T).coeff (i + 1) • T ^ (i + 1))
        = -((minpoly F T).coeff 0 • (1 : Module.End F V)) :=
      eq_neg_of_add_eq_zero_left hsum
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => -((minpoly F T).coeff 0)⁻¹ * (minpoly F T).coeff ((i : ℕ) + 1), ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i =>
      (-((minpoly F T).coeff 0)⁻¹ * (minpoly F T).coeff (i + 1)) • T ^ (i + 1))]
    simp only [mul_smul]
    rw [← Finset.smul_sum, hkey, neg_smul, smul_neg, neg_neg, smul_smul,
      inv_mul_cancel₀ ha0, one_smul]
    rfl
  · -- conversely, {lit}`I = ∑ cᵢ T^{i+1}` factors as {lit}`T` times something
    intro hmem
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨∑ i : Fin (finrank F V), c i • T ^ (i : ℕ), ?_, ?_⟩
    · rw [← Module.End.mul_eq_comp, Finset.sum_mul, ← hc]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_mul_assoc, ← pow_succ]
    · rw [← Module.End.mul_eq_comp, Finset.mul_sum, ← hc]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, ← pow_succ']

/-- 5B.23 -/
theorem exercise_5B_23 [Finite F V] (T : V →ₗ[F] V) (v : V) :
    InvariantUnder T (Submodule.span F
      (Set.range fun i : Fin (finrank F V) => (T ^ (i : ℕ)) v)) := by
  -- enough to show T maps each generator into the span
  -- T^i v for i < n,
  -- T T ^ i v = T ^ (i + 1) v, for all but i = n - 1, this is trivial
  -- for i = n - 1, we get T ^ n, but minpoly is monic of deg d ≤ n,
  -- so T ^ d rewrites as lower powers; multiply by T ^ (n - d) to get
  -- T ^ n as a combination of T ^ (n-d) ... T ^ (n-1), all still in the span.
  classical
  have hmono : (minpoly F T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  have hnle : (minpoly F T).natDegree ≤ finrank F V := minpoly_natDegree_le T
  have hgen : ∀ m : ℕ, m < finrank F V → (T ^ m) v ∈ Submodule.span F
      (Set.range fun i : Fin (finrank F V) => (T ^ (i : ℕ)) v) :=
    fun m hm => Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
  -- the minimal polynomial rewrites {lit}`Tⁿ v` in terms of lower powers
  have hTn : (T ^ (minpoly F T).natDegree) v
      = -∑ i ∈ Finset.range (minpoly F T).natDegree,
          (minpoly F T).coeff i • (T ^ i) v := by
    have h0 : aeval T (minpoly F T) v = 0 := by rw [minpoly.aeval]; rfl
    rw [Polynomial.aeval_eq_sum_range] at h0
    simp only [LinearMap.sum_apply, LinearMap.smul_apply] at h0
    rw [Finset.sum_range_succ, hmono.coeff_natDegree, one_smul] at h0
    exact eq_neg_of_add_eq_zero_right h0
  -- hence {lit}`T^(dim V) v` lies in the span as well
  have hpow : (T ^ (finrank F V)) v
      = (T ^ (finrank F V - (minpoly F T).natDegree))
          ((T ^ (minpoly F T).natDegree) v) := by
    rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel hnle]
  have hTN : (T ^ (finrank F V)) v ∈ Submodule.span F
      (Set.range fun i : Fin (finrank F V) => (T ^ (i : ℕ)) v) := by
    rw [hpow, hTn, map_neg, map_sum]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [map_smul, ← Module.End.mul_apply, ← pow_add]
    exact Submodule.smul_mem _ _
      (hgen _ (by have := Finset.mem_range.mp hi; omega))
  -- it suffices to check the generators
  rw [LADR.Section_5A.invariantUnder_iff_map_le, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  simp only [SetLike.mem_coe]
  rw [← Module.End.mul_apply, ← pow_succ']
  rcases Nat.lt_or_ge ((i : ℕ) + 1) (finrank F V) with h | h
  · exact hgen _ h
  · rw [show (i : ℕ) + 1 = finrank F V by omega]
    exact hTN

open Polynomial in
/-- 5B.24 -/
theorem exercise_5B_24 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V)
    (hev : ∀ γ : ℂ, HasEigenvalue T γ ↔ γ = 5 ∨ γ = 6) :
    ((T - 5 • LinearMap.id) ^ (finrank ℂ V - 1)) ∘ₗ
      ((T - 6 • LinearMap.id) ^ (finrank ℂ V - 1)) = 0 := by
  -- over C the min poly splits fully to products (z - a)
  -- but a has to be either 5 or 6
  -- so minpoly = (z - 5)^i * (z - 6)^j, where i + j ≤ finrank ℂ V
  -- both 5 and 6 really are eigenvalues, so i ≥ 1 and j ≥ 1, hence
  -- i ≤ finrank - 1 and j ≤ finrank - 1
  -- so the poly in question is divisble by minpoly, so 0 at T
  classical
  have hmonic : (minpoly ℂ T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  have hsplit : (minpoly ℂ T).Splits := IsAlgClosed.splits _
  have hcard : Multiset.card (minpoly ℂ T).roots = (minpoly ℂ T).natDegree :=
    Polynomial.splits_iff_card_roots.mp hsplit
  have hdeg : (minpoly ℂ T).natDegree ≤ finrank ℂ V := minpoly_natDegree_le T
  -- the roots are exactly the eigenvalues, so they lie in {lit}`{5, 6}`
  have hroots : ∀ a ∈ (minpoly ℂ T).roots, a = 5 ∨ a = 6 := by
    intro a ha
    exact (hev a).mp ((isEigenvalue_iff_isRoot T a).mpr
      ((mem_roots hmonic.ne_zero).mp ha))
  have h5 : (5 : ℂ) ∈ (minpoly ℂ T).roots :=
    (mem_roots hmonic.ne_zero).mpr
      ((isEigenvalue_iff_isRoot T 5).mp ((hev 5).mpr (Or.inl rfl)))
  have h6 : (6 : ℂ) ∈ (minpoly ℂ T).roots :=
    (mem_roots hmonic.ne_zero).mpr
      ((isEigenvalue_iff_isRoot T 6).mp ((hev 6).mpr (Or.inr rfl)))
  -- the two multiplicities add up to at most the degree
  have hle : Multiset.replicate ((minpoly ℂ T).roots.count 5) (5 : ℂ)
      + Multiset.replicate ((minpoly ℂ T).roots.count 6) (6 : ℂ)
      ≤ (minpoly ℂ T).roots := by
    refine Multiset.le_iff_count.mpr fun a => ?_
    simp only [Multiset.count_add, Multiset.count_replicate]
    by_cases h1 : (5 : ℂ) = a
    · subst h1
      rw [if_pos rfl, if_neg (by norm_num : ¬((6 : ℂ) = 5))]
      omega
    · by_cases h2 : (6 : ℂ) = a
      · subst h2
        rw [if_neg h1, if_pos rfl]
        omega
      · rw [if_neg h1, if_neg h2]
        omega
  have hsum : (minpoly ℂ T).roots.count 5 + (minpoly ℂ T).roots.count 6
      ≤ finrank ℂ V := by
    have := Multiset.card_le_card hle
    simp only [Multiset.card_add, Multiset.card_replicate] at this
    omega
  have h5pos : 1 ≤ (minpoly ℂ T).roots.count 5 := Multiset.one_le_count_iff_mem.mpr h5
  have h6pos : 1 ≤ (minpoly ℂ T).roots.count 6 := Multiset.one_le_count_iff_mem.mpr h6
  -- hence every root has multiplicity at most {lit}`finrank - 1`
  have hps : (minpoly ℂ T).roots ≤ Multiset.replicate (finrank ℂ V - 1) (5 : ℂ)
      + Multiset.replicate (finrank ℂ V - 1) (6 : ℂ) := by
    refine Multiset.le_iff_count.mpr fun a => ?_
    simp only [Multiset.count_add, Multiset.count_replicate]
    by_cases h1 : (5 : ℂ) = a
    · subst h1
      rw [if_pos rfl, if_neg (by norm_num : ¬((6 : ℂ) = 5))]
      omega
    · by_cases h2 : (6 : ℂ) = a
      · subst h2
        rw [if_neg h1, if_pos rfl]
        omega
      · have hnot : a ∉ (minpoly ℂ T).roots := fun hm => by
          rcases hroots a hm with h | h
          · exact h1 h.symm
          · exact h2 h.symm
        rw [if_neg h1, if_neg h2, Multiset.count_eq_zero.mpr hnot]
  -- so the minimal polynomial divides the goal polynomial
  have hq : ((Multiset.replicate (finrank ℂ V - 1) (5 : ℂ)
        + Multiset.replicate (finrank ℂ V - 1) (6 : ℂ)).map
          (fun a => X - C a)).prod
      = (X - C 5) ^ (finrank ℂ V - 1) * (X - C 6) ^ (finrank ℂ V - 1) := by
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate,
      Multiset.map_replicate, Multiset.prod_replicate, Multiset.prod_replicate]
  have hdvd : minpoly ℂ T
      ∣ (X - C 5) ^ (finrank ℂ V - 1) * (X - C 6) ^ (finrank ℂ V - 1) := by
    rw [← hq, minpoly_eq_prod_roots_of_splits T hsplit]
    exact Multiset.prod_dvd_prod_of_le (Multiset.map_le_map hps)
  -- translate the goal into the polynomial statement
  have hns : ∀ m : ℕ, (m • (LinearMap.id : V →ₗ[ℂ] V)) = (m : ℂ) • LinearMap.id :=
    fun m => (Nat.cast_smul_eq_nsmul ℂ m _).symm
  have hfac : ∀ c : ℂ, aeval T (X - C c) = T - c • (LinearMap.id : V →ₗ[ℂ] V) := by
    intro c
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]
  have hgoal : ((T - 5 • LinearMap.id) ^ (finrank ℂ V - 1)) ∘ₗ
      ((T - 6 • LinearMap.id) ^ (finrank ℂ V - 1))
      = aeval T ((X - C 5 : Polynomial ℂ) ^ (finrank ℂ V - 1)
          * (X - C 6) ^ (finrank ℂ V - 1)) := by
    simp only [map_mul, map_pow, hfac, Module.End.mul_eq_comp, hns, Nat.cast_ofNat]
  obtain ⟨h, hh⟩ := hdvd
  rw [hgoal, hh, map_mul, minpoly.aeval, zero_mul]

open LADR.Section_5A (exercise_5A_38_quotient_op) in
/-- Evaluating a polynomial at the quotient operator commutes with the quotient
map: {lit}`p(T/U)(v + U) = p(T)v + U`. -/
private theorem aeval_quotient_mkQ {T : V →ₗ[F] V} {U : Submodule F V}
    (hU : InvariantUnder T U) (p : Polynomial F) (v : V) :
    aeval (exercise_5A_38_quotient_op T U hU) p (U.mkQ v) = U.mkQ (aeval T p v) := by
  have hqapply : ∀ x, exercise_5A_38_quotient_op T U hU (U.mkQ x) = U.mkQ (T x) := by
    intro x; simp [exercise_5A_38_quotient_op, Submodule.mapQ_apply]
  have hpow : ∀ (n : ℕ) (v : V),
      ((exercise_5A_38_quotient_op T U hU) ^ n) (U.mkQ v) = U.mkQ ((T ^ n) v) := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih, hqapply, ← Module.End.mul_apply,
        ← pow_succ']
  induction p using Polynomial.induction_on' generalizing v with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, map_add]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, hpow, map_smul]

open LADR.Section_5A (exercise_5A_38_quotient_op) in
/-- 5B.25 (a) The minimal polynomial of {lit}`T` is a polynomial multiple of
the minimal polynomial of the quotient operator {lit}`T/U`. -/
theorem exercise_5B_25a [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) :
    minpoly F (exercise_5A_38_quotient_op T U hU) ∣ minpoly F T := by
  -- since p(T) v = 0, then p(T) (v + U) = 0 too, so minpoly quotient | minpoly T
  refine minpoly.dvd F _ (LinearMap.ext fun x => ?_)
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  rw [aeval_quotient_mkQ, LinearMap.congr_fun (minpoly.aeval F T) v]
  simp

open LADR.Section_5A (exercise_5A_38_quotient_op) in
/-- 5B.25 (b) {lit}`(minpoly T|_U) · (minpoly T/U)` is a polynomial multiple
of the minimal polynomial of {lit}`T`. -/
theorem exercise_5B_25b [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) :
    minpoly F T ∣
      minpoly F hU.restrict * minpoly F (exercise_5A_38_quotient_op T U hU) := by
  -- (r * q)(T) v = (r * q)(T) (v + u), where v not in U and u ∈ U
  -- = (r * q)(T) v + (q * r)(T) u = 0 + 0, because q(T) v = 0, and r(T) u = 0
  -- {lit}`r(T) v` lands in {lit}`U`, because {lit}`r` kills the quotient
  -- operator; then {lit}`q(T)` kills it, because {lit}`q` kills {lit}`T|_U`
  refine minpoly.dvd F T (LinearMap.ext fun v => ?_)
  rw [map_mul, Module.End.mul_apply, LinearMap.zero_apply]
  have h0 : U.mkQ (aeval T (minpoly F (exercise_5A_38_quotient_op T U hU)) v) = 0 := by
    rw [← aeval_quotient_mkQ hU, minpoly.aeval, LinearMap.zero_apply]
  have hmem : aeval T (minpoly F (exercise_5A_38_quotient_op T U hU)) v ∈ U := by
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  have hcoe := aeval_restrict_coe hU (minpoly F hU.restrict)
    ⟨aeval T (minpoly F (exercise_5A_38_quotient_op T U hU)) v, hmem⟩
  rw [minpoly.aeval] at hcoe
  simpa using hcoe.symm

open LADR.Section_5A (exercise_5A_38_quotient_op) in
/-- 5B.26 -/
theorem exercise_5B_26 [Finite F V] (T : V →ₗ[F] V) (U : Submodule F V)
    (hU : InvariantUnder T U) (γ : F) :
    HasEigenvalue T γ ↔ HasEigenvalue hU.restrict γ ∨
      HasEigenvalue (exercise_5A_38_quotient_op T U hU) γ := by
  -- p = minpoly, q = restiction and r = quotient minpoly
  -- we have shown q | p, r | p, p | q * r
  -- so linear factors of q or r, are linear factors of p
  -- and linear factors of p are linear factors of either q or r (they are prime)
  have hqp : minpoly F hU.restrict ∣ minpoly F T := minpoly_restrict_dvd T U hU
  have hrp : minpoly F (exercise_5A_38_quotient_op T U hU) ∣ minpoly F T :=
    exercise_5B_25a T U hU
  have hpqr := exercise_5B_25b T U hU
  rw [isEigenvalue_iff_isRoot, isEigenvalue_iff_isRoot, isEigenvalue_iff_isRoot,
    ← Polynomial.dvd_iff_isRoot, ← Polynomial.dvd_iff_isRoot,
    ← Polynomial.dvd_iff_isRoot]
  constructor
  · intro h
    exact (Polynomial.prime_X_sub_C γ).2.2 _ _ (h.trans hpqr)
  · rintro (h | h)
    · exact h.trans hqp
    · exact h.trans hrp

open LADR.Section_1B (Complexification exercise_1B_8) in
open LADR.Section_3B (complexification_map) in
/-- 5B.27 -/
theorem exercise_5B_27 {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (T : V →ₗ[ℝ] V) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    minpoly ℂ (complexification_map T) =
      (minpoly ℝ T).map (algebraMap ℝ ℂ) := by
  -- for real p: p(T_C) (u,v) = (p(T)u, p(T)v), so p(T_C) = 0 iff p(T) = 0.
  -- one direction is then immediate: minpoly R T, viewed over C, kills T_C.
  -- but minpoly C (T_C) is a complex polynomial and could a priori be shorter,
  -- so take monic complex q with q(T_C) = 0 and evaluate at (u, 0):
  -- the real coordinate is qre(T) u, where qre collects the real parts of the
  -- coefficients of q. q monic => qre monic of the same degree, and qre(T) = 0,
  -- so deg (minpoly R T) <= deg q. hence the degrees match and min poly follows.
  letI : Module ℂ (Complexification V) := exercise_1B_8 V
  have hmap : ∀ x : Complexification V,
      complexification_map T x = (T x.1, T x.2) := fun _ => rfl
  have hsmul : ∀ (c : ℂ) (x : Complexification V),
      c • x = (c.re • x.1 - c.im • x.2, c.re • x.2 + c.im • x.1) := fun _ _ => rfl
  have hpow : ∀ (n : ℕ) (x : Complexification V),
      ((complexification_map T) ^ n) x = ((T ^ n) x.1, (T ^ n) x.2) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, ih, hmap, pow_succ']
      simp [Module.End.mul_apply]
  -- a real polynomial acts coordinatewise on the complexification
  have hreal : ∀ (r : Polynomial ℝ) (x : Complexification V),
      aeval (complexification_map T) (r.map (algebraMap ℝ ℂ)) x
        = ((aeval T r) x.1, (aeval T r) x.2) := by
    intro r
    induction r using Polynomial.induction_on' with
    | add p q hp hq =>
      intro x
      simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp, hq, Prod.mk_add_mk]
    | monomial n a =>
      intro x
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply, hpow, hsmul]
      simp
  have hpmonic : (minpoly ℝ T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  have hmonic : ((minpoly ℝ T).map (algebraMap ℝ ℂ)).Monic := hpmonic.map _
  refine (minpoly.unique ℂ (complexification_map T) hmonic ?_ fun q hq hq0 => ?_).symm
  · -- it annihilates the complexification because it annihilates {lit}`T`
    refine LinearMap.ext fun x => ?_
    rw [hreal, LinearMap.congr_fun (minpoly.aeval ℝ T) x.1,
      LinearMap.congr_fun (minpoly.aeval ℝ T) x.2]
    rfl
  · -- conversely, the real part of a monic complex annihilator is a monic real
    -- annihilator of the same degree
    set d := q.natDegree with hd
    set qre : Polynomial ℝ :=
      ∑ i ∈ Finset.range d, Polynomial.C (q.coeff i).re * Polynomial.X ^ i with hqre
    set qim : Polynomial ℝ :=
      ∑ i ∈ Finset.range (d + 1), Polynomial.C (q.coeff i).im * Polynomial.X ^ i with hqim
    have hev : ∀ (c : ℕ → ℝ) (n : ℕ) (u : V),
        (aeval T (∑ i ∈ Finset.range n, Polynomial.C (c i) * Polynomial.X ^ i)) u
          = ∑ i ∈ Finset.range n, c i • ((T ^ i) u) := by
      intro c n u
      simp only [map_sum, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        ← Algebra.smul_def, LinearMap.sum_apply, LinearMap.smul_apply]
    have hsplit : ∀ u : V,
        aeval (complexification_map T) q (u, 0)
          = (((T ^ d) u + (aeval T qre) u), (aeval T qim) u) := by
      intro u
      rw [Polynomial.aeval_eq_sum_range' (n := d + 1) (by omega) (complexification_map T)]
      rw [LinearMap.sum_apply]
      have hterm : ∀ i ∈ Finset.range (d + 1),
          (q.coeff i • (complexification_map T) ^ i) (u, 0)
            = ((q.coeff i).re • ((T ^ i) u), (q.coeff i).im • ((T ^ i) u)) := by
        intro i _
        rw [LinearMap.smul_apply, hpow, hsmul]
        simp
      rw [Finset.sum_congr rfl hterm, Prod.mk.injEq]
      constructor
      · rw [Prod.fst_sum, Finset.sum_range_succ, hev]
        simp only []
        rw [hq.coeff_natDegree]
        simp [add_comm]
      · rw [Prod.snd_sum, hev]
    have hqre0 : aeval T (Polynomial.X ^ d + qre) = 0 := by
      refine LinearMap.ext fun u => ?_
      have h := hsplit u
      rw [hq0] at h
      have h1 : ((T ^ d) u + (aeval T qre) u) = 0 := by
        have := congrArg Prod.fst h
        simpa using this.symm
      simpa [map_add, map_pow, Polynomial.aeval_X] using h1
    have hqredeg : qre.degree < ((d : ℕ) : WithBot ℕ) := by
      rw [hqre]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe d)).mpr fun i hi => ?_
      exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _)
        (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))
    have hXqre : (Polynomial.X ^ d + qre).Monic :=
      (Polynomial.monic_X_pow d).add_of_left (by rw [Polynomial.degree_X_pow]; exact hqredeg)
    have hdegXqre : (Polynomial.X ^ d + qre).degree = (d : WithBot ℕ) := by
      rw [Polynomial.degree_add_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact hqredeg), Polynomial.degree_X_pow]
    have hle := minpoly.min ℝ T hXqre hqre0
    rw [hdegXqre] at hle
    rw [hpmonic.degree_map (algebraMap ℝ ℂ),
      Polynomial.degree_eq_natDegree hq.ne_zero, ← hd]
    exact hle

/-- 5B.28 -/
theorem exercise_5B_28 [Finite F V] (T : V →ₗ[F] V) :
    minpoly F T.dualMap = minpoly F T := by
  -- (p(T') φ) v = φ (p(T) v)
  -- so p(T) = 0 for all v iff p(T') = 0 for all φ, hence minpoly T' = minpoly T
  have hpow : ∀ (n : ℕ) (φ : Module.Dual F V) (v : V),
      ((T.dualMap ^ n) φ) v = φ ((T ^ n) v) := by
    intro n
    induction n with
    | zero => intro φ v; simp
    | succ n ih =>
      intro φ v
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply,
        LinearMap.dualMap_apply]
  have haeval : ∀ (p : Polynomial F) (φ : Module.Dual F V) (v : V),
      (aeval T.dualMap p φ) v = φ (aeval T p v) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      intro φ v
      simp only [map_add, LinearMap.add_apply, hp, hq, map_add]
    | monomial n a =>
      intro φ v
      simp only [Polynomial.aeval_monomial, Module.End.mul_apply,
        Module.algebraMap_end_apply, LinearMap.smul_apply, hpow, map_smul]
  -- the two operators are annihilated by exactly the same polynomials; the
  -- backward step uses that the dual separates points
  have hiff : ∀ p : Polynomial F, aeval T.dualMap p = 0 ↔ aeval T p = 0 := by
    intro p
    constructor
    · intro h
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.zero_apply]
      refine (Module.forall_dual_apply_eq_zero_iff F _).mp fun φ => ?_
      rw [← haeval, h]
      simp
    · intro h
      refine LinearMap.ext fun φ => LinearMap.ext fun v => ?_
      rw [haeval, h]
      simp
  -- both minimal polynomials therefore minimize over the same set
  refine (minpoly.unique F T.dualMap ?_ ?_ ?_).symm
  · exact minpoly.monic (Algebra.IsIntegral.isIntegral T)
  · exact (hiff _).mpr (minpoly.aeval F T)
  · exact fun q hq hq0 => minpoly.min F T hq ((hiff q).mp hq0)

/-- Two independent vectors whose images stay inside their span give a
2-dimensional invariant subspace. -/
private theorem exists_invariant_two {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V →ₗ[ℝ] V) {x y : V}
    (hindep : LinearIndependent ℝ ![x, y])
    (hx : T x ∈ Submodule.span ℝ (Set.range ![x, y]))
    (hy : T y ∈ Submodule.span ℝ (Set.range ![x, y])) :
    ∃ U : Submodule ℝ V, InvariantUnder T U ∧ finrank ℝ U = 2 := by
  refine ⟨Submodule.span ℝ (Set.range ![x, y]), ?_, ?_⟩
  · rw [LADR.Section_5A.invariantUnder_iff_map_le, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · simpa using hx
    · simpa using hy
  · rw [finrank_span_eq_card hindep, Fintype.card_fin]

/-- A monic real polynomial of degree at least 2 has a monic divisor of
degree exactly 2. -/
private theorem exists_monic_degree_two_dvd {p : Polynomial ℝ} (hp : p.Monic)
    (hd : 2 ≤ p.natDegree) :
    ∃ f : Polynomial ℝ, f.Monic ∧ f.natDegree = 2 ∧ f ∣ p := by
  have hdeg : ∀ q : Polynomial ℝ, q.Monic → Irreducible q →
      q.natDegree = 1 ∨ q.natDegree = 2 := by
    intro q hqm hqi
    have h2 : q.natDegree ≤ 2 := Polynomial.natDegree_le_iff_degree_le.mpr hqi.degree_le_two
    have h1 : q.natDegree ≠ 0 := by
      intro h0
      exact hqi.not_isUnit (hqm.natDegree_eq_zero.mp h0 ▸ isUnit_one)
    omega
  have hnu : ¬ IsUnit p := by
    intro h
    have := Polynomial.natDegree_eq_zero_of_isUnit h
    omega
  obtain ⟨f₁, hf₁m, hf₁i, hf₁d⟩ := Polynomial.exists_monic_irreducible_factor p hnu
  rcases hdeg f₁ hf₁m hf₁i with h1 | h1
  swap
  · exact ⟨f₁, hf₁m, h1, hf₁d⟩
  obtain ⟨h, rfl⟩ := hf₁d
  have hhm : h.Monic := hf₁m.of_mul_monic_left hp
  have hhdeg : 1 ≤ h.natDegree := by
    rw [hf₁m.natDegree_mul hhm, h1] at hd
    omega
  have hnu' : ¬ IsUnit h := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨f₂, hf₂m, hf₂i, hf₂d⟩ := Polynomial.exists_monic_irreducible_factor h hnu'
  rcases hdeg f₂ hf₂m hf₂i with h2 | h2
  · refine ⟨f₁ * f₂, hf₁m.mul hf₂m, ?_, mul_dvd_mul_left f₁ hf₂d⟩
    rw [hf₁m.natDegree_mul hf₂m, h1, h2]
  · exact ⟨f₂, hf₂m, h2, hf₂d.trans (Dvd.intro_left _ rfl)⟩

/-- 5B.29 -/
theorem exercise_5B_29 {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Finite ℝ V] (hV : 2 ≤ finrank ℝ V) (T : V →ₗ[ℝ] V) :
    ∃ U : Submodule ℝ V, InvariantUnder T U ∧ finrank ℝ U = 2 := by
  -- 1) deg minpoly ≤ 1 -> T = a I, so any 2 dim space will do
  -- 2) deg minpoly ≥ 2 -> over R the minimal polynomial has a monic degree-2
  --    divisor f = X^2 + aX + b (an irreducible quadratic factor, or a product
  --    of two linear ones); write minpoly = f g
  --    a) f has no real root:
  --       deg g < deg minpoly, so g(T) ≠ 0: pick v with w := g(T) v ≠ 0
  --       f(T) w = f(T) g(T) v = minpoly(T) v = 0, so w ∈ ker f(T)
  --       Tw = c w would give c^2 + ac + b = 0, so Tw is not a multiple of w,
  --       and w, Tw span a 2-dim invariant subspace (T^2 w = -a Tw - b w)
  --    b) f has a real root lam:
  --       deg (X - lam) g < deg minpoly, so pick v off its kernel and set
  --       w := g(T) v; then (T - lam) w ≠ 0, hence w ≠ 0, and f(T) w = 0
  --       i)  Tw not a multiple of w -> w, Tw as in a)
  --       ii) Tw = c w -> c ≠ lam because (T - lam) w ≠ 0; and lam is a root
  --           of f | minpoly, so it is an eigenvalue, with eigenvector u.
  --           u and w are eigenvectors for distinct eigenvalues, so they span
  --           a 2-dim invariant subspace

  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hmonic : (minpoly ℝ T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  -- a nonzero polynomial of degree below the minimal one does not annihilate `T`
  have hnonzero : ∀ q : Polynomial ℝ, q ≠ 0 → q.natDegree < (minpoly ℝ T).natDegree →
      ∃ v : V, aeval T q v ≠ 0 := by
    intro q hq hlt
    by_contra hc
    push Not at hc
    have h0 : aeval T q = 0 := LinearMap.ext fun v => by rw [hc v]; simp
    have hle := minpoly.degree_le_of_ne_zero ℝ T hq h0
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
      Polynomial.degree_eq_natDegree hq] at hle
    exact absurd (by exact_mod_cast hle : (minpoly ℝ T).natDegree ≤ q.natDegree) (by omega)
  by_cases hd : (minpoly ℝ T).natDegree ≤ 1
  · -- `T` is a scalar operator, so every subspace is invariant
    have hd1 : (minpoly ℝ T).natDegree = 1 := by
      have hpos : 0 < (minpoly ℝ T).natDegree :=
        minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral T)
      omega
    have hTscal : ∀ v : V, T v = (-(minpoly ℝ T).coeff 0) • v := by
      intro v
      have heq := hmonic.eq_X_add_C hd1
      have h0 := LinearMap.congr_fun (minpoly.aeval ℝ T) v
      rw [heq, map_add, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one] at h0
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.zero_apply] at h0
      rw [neg_smul, eq_comm, neg_eq_iff_add_eq_zero, add_comm]
      exact h0
    obtain ⟨v₁, hv₁⟩ := exists_ne (0 : V)
    have hspan : Submodule.span ℝ ({v₁} : Set V) ≠ ⊤ := by
      intro h
      have h1 : finrank ℝ (Submodule.span ℝ ({v₁} : Set V)) = 1 := finrank_span_singleton hv₁
      rw [h, finrank_top] at h1
      omega
    obtain ⟨v₂, hv₂⟩ : ∃ v : V, v ∉ Submodule.span ℝ ({v₁} : Set V) := by
      by_contra hc
      push Not at hc
      exact hspan (Submodule.eq_top_iff'.mpr hc)
    refine exists_invariant_two T (x := v₂) (y := v₁) ?_ ?_ ?_
    · refine linearIndependent_fin2.mpr ⟨by simpa using hv₁, fun t ht => hv₂ ?_⟩
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ht
      rw [← ht]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₁)
    · rw [hTscal]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · rw [hTscal]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  · -- take a monic degree-2 divisor of the minimal polynomial
    push Not at hd
    obtain ⟨f, hfm, hfdeg, hfdvd⟩ := exists_monic_degree_two_dvd hmonic (by omega)
    obtain ⟨g, hg⟩ := hfdvd
    set a := f.coeff 1 with ha
    set b := f.coeff 0 with hb
    have hfexp : f = Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b := by
      refine Polynomial.ext fun n => ?_
      match n with
      | 0 => simp [hb]
      | 1 => simp [ha]
      | 2 =>
        have h2 : f.coeff 2 = 1 := by rw [← hfdeg]; exact hfm.coeff_natDegree
        rw [h2]
        simp
      | (m + 3) =>
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp [Polynomial.coeff_X_pow]
    have hfact : ∀ w : V, aeval T f w = (T ^ 2) w + a • T w + b • w := by
      intro w
      rw [hfexp]
      simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        ← Algebra.smul_def, LinearMap.add_apply, LinearMap.smul_apply,
        Module.algebraMap_end_apply]
    have hgmonic : g.Monic := hfm.of_mul_monic_left (hg ▸ hmonic)
    have hgne : g ≠ 0 := hgmonic.ne_zero
    have hgdeg : g.natDegree + 2 = (minpoly ℝ T).natDegree := by
      rw [hg, hfm.natDegree_mul hgmonic, hfdeg]
      omega
    -- the packaged conclusion when `Tw` is not a multiple of `w`
    have hpair : ∀ w : V, w ≠ 0 → aeval T f w = 0 → (∀ c : ℝ, c • w ≠ T w) →
        ∃ U : Submodule ℝ V, InvariantUnder T U ∧ finrank ℝ U = 2 := by
      intro w hw hfw hnc
      refine exists_invariant_two T (x := T w) (y := w) ?_ ?_ ?_
      · exact linearIndependent_fin2.mpr ⟨by simpa using hw, by simpa using hnc⟩
      · have h1 : (T ^ 2) w = -(a • T w + b • w) := by
          rw [hfact w] at hfw
          rw [eq_neg_iff_add_eq_zero, ← add_assoc]
          exact hfw
        rw [show T (T w) = (T ^ 2) w by rw [pow_two, Module.End.mul_apply], h1]
        exact Submodule.neg_mem _ (Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
      · exact Submodule.subset_span ⟨0, rfl⟩
    -- if `Tw = c • w` then `c` is a root of `f`
    have hcroot : ∀ (w : V) (c : ℝ), w ≠ 0 → aeval T f w = 0 → T w = c • w →
        c ^ 2 + a * c + b = 0 := by
      intro w c hw hfw hcw
      have h2 : (T ^ 2) w = (c ^ 2) • w := by
        rw [pow_two, Module.End.mul_apply, hcw, map_smul, hcw, smul_smul, ← pow_two]
      rw [hfact w, h2, hcw, smul_smul] at hfw
      have h3 : (c ^ 2 + a * c + b) • w = 0 := by rw [← hfw]; module
      rcases smul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h hw
    by_cases hroot : ∃ c : ℝ, c ^ 2 + a * c + b = 0
    · obtain ⟨lam, hlam⟩ := hroot
      obtain ⟨v, hv⟩ := hnonzero ((Polynomial.X - Polynomial.C lam) * g)
        (mul_ne_zero (Polynomial.X_sub_C_ne_zero lam) hgne)
        (by
          rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero lam) hgne,
            Polynomial.natDegree_X_sub_C]
          omega)
      set w := aeval T g v with hw
      have hexp : aeval T ((Polynomial.X - Polynomial.C lam) * g) v = T w - lam • w := by
        rw [map_mul, Module.End.mul_apply, ← hw, map_sub, Polynomial.aeval_X,
          Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
        simp
      have hTw : T w - lam • w ≠ 0 := by rw [← hexp]; exact hv
      have hwne : w ≠ 0 := by
        intro h
        apply hTw
        rw [h]
        simp
      have hfw : aeval T f w = 0 := by
        rw [hw, ← Module.End.mul_apply, ← map_mul, ← hg]
        simp
      by_cases hc : ∃ c : ℝ, T w = c • w
      · obtain ⟨c, hcw⟩ := hc
        have hne : c ≠ lam := by
          intro h
          apply hTw
          rw [hcw, h, sub_self]
        -- `lam` is a root of the minimal polynomial, hence an eigenvalue
        have hlamroot : (minpoly ℝ T).IsRoot lam := by
          have hf0 : f.eval lam = 0 := by
            rw [hfexp]
            simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
              Polynomial.eval_mul, Polynomial.eval_C]
            linarith [hlam]
          rw [Polynomial.IsRoot, hg, Polynomial.eval_mul, hf0, zero_mul]
        obtain ⟨u, hune, hu⟩ := Module.End.hasEigenvalue_iff_exists.mp
          ((isEigenvalue_iff_isRoot T lam).mpr hlamroot)
        refine exists_invariant_two T (x := u) (y := w) ?_ ?_ ?_
        · refine linearIndependent_fin2.mpr ⟨by simpa using hwne, ?_⟩
          intro t ht
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at ht
          apply hune
          have h1 : T (t • w) = lam • (t • w) := by rw [ht]; exact hu
          rw [map_smul, hcw, smul_smul, smul_smul] at h1
          have h2 : (t * c - lam * t) • w = 0 := by rw [sub_smul, h1, sub_self]
          rcases smul_eq_zero.mp h2 with h | h
          · have ht0 : t = 0 := by
              rcases mul_eq_zero.mp (by linarith [h] : t * (c - lam) = 0) with h' | h'
              · exact h'
              · exact absurd (sub_eq_zero.mp h') hne
            rw [← ht, ht0, zero_smul]
          · exact absurd h hwne
        · rw [hu]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
        · rw [hcw]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
      · push Not at hc
        exact hpair w hwne hfw (fun c hcc => hc c hcc.symm)
    · -- `f` has no real root, so `Tw` can never be a multiple of `w`
      obtain ⟨v, hv⟩ := hnonzero g hgne (by omega)
      set w := aeval T g v with hw
      have hfw : aeval T f w = 0 := by
        rw [hw, ← Module.End.mul_apply, ← map_mul, ← hg]
        simp
      refine hpair w hv hfw fun c hcc => ?_
      exact hroot ⟨c, hcroot w c hv hfw hcc.symm⟩


end LADR.Section_5B
