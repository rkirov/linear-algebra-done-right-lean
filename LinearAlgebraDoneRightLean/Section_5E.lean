import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_3E
import LinearAlgebraDoneRightLean.Section_5A
import LinearAlgebraDoneRightLean.Section_5B
import LinearAlgebraDoneRightLean.Section_5C
import LinearAlgebraDoneRightLean.Section_5D
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 5E: Commuting Operators
-/

namespace LADR.Section_5E

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis exists_basis exists_basis_of_spans)
open LADR.Section_2C (isBasis_of_linearIndependent_of_card_eq
  isBasis_card_eq_finrank)
open LADR.Section_3C (matrixOf matrixOf_apply matrixOf_spec matrixOf_comp)
open LADR.Section_3D (IsInvertible)
open Module.End (HasEigenvalue HasEigenvector)
open LADR.Section_5A (InvariantUnder
  exercise_5A_38_quotient_op)
open LADR.Section_5C (IsUpperTriangular tfae_upperTriangular
  isEigenvalue_iff_diag)
open LADR.Section_5D (IsDiagonalizable isDiagonalizable_restrict
  apply_eq_smul_of_isDiag isDiag_matrixOf_of_eigenvectors)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval)

universe u

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! 5.71 Definition: commute.

Two operators {lit}`S, T ∈ ℒ(V)` *commute* if {lit}`ST = TS`; two square
matrices {lit}`A, B` commute if {lit}`AB = BA`. In mathlib this is the
general {name}`Commute` (for the multiplication of {name}`Module.End`
resp. of matrices). -/

example (S T : V →ₗ[F] V) : (S ∘ₗ T = T ∘ₗ S) ↔ Commute S T := by
  rw [Commute, SemiconjBy]
  exact Iff.rfl

-- Likewise for square matrices: {lit}`A, B` commute iff {lit}`AB = BA`.
example {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n F) :
    (A * B = B * A) ↔ Commute A B := by
  rw [Commute, SemiconjBy]

-- {lit}`λI` commutes with every operator, and {lit}`p(T)` commutes with
-- {lit}`q(T)` (5.17).
example (T : V →ₗ[F] V) (lam : F) :
    Commute (lam • LinearMap.id : V →ₗ[F] V) T := by
  rw [Commute, SemiconjBy]
  ext v
  simp

example (T : V →ₗ[F] V) (p q : Polynomial F) :
    Commute (aeval T p) (aeval T q) :=
  LADR.Section_5A.aeval_comp_comm T p q

/-! 5.72/5.73 Example: the partial differentiation operators {lit}`∂/∂x` and
{lit}`∂/∂y` commute, since mixed partial derivatives of polynomials agree
(equality of mixed partials, Clairaut). We formalize this on the full
polynomial ring {lit}`ℝ[x, y]` (indices {lit}`0, 1` of
{lit}`MvPolynomial (Fin 2) ℝ`), which subsumes the claim on each finite-degree
subspace {lit}`𝒫ₘ(ℝ²)`. (See Exercise 5E.8.) -/

theorem pderiv_comm {σ : Type*} {R : Type*} [CommSemiring R] (i j : σ)
    (p : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p)
      = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n ih =>
    -- The second partial derivative of a single variable {lit}`Xₙ` vanishes.
    have hX : ∀ a b : σ,
        MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.X n))
          = (0 : MvPolynomial σ R) := by
      intro a b
      rcases eq_or_ne n b with rfl | h
      · rw [MvPolynomial.pderiv_X_self]; simp
      · rw [MvPolynomial.pderiv_X_of_ne h]; simp
    simp only [map_add, MvPolynomial.pderiv_mul, hX, ih, mul_zero, add_zero]
    ring

-- {lit}`∂/∂x` and {lit}`∂/∂y` on {lit}`ℝ[x, y]` commute as operators.
example : Commute
    ((MvPolynomial.pderiv (0 : Fin 2)).toLinearMap :
      MvPolynomial (Fin 2) ℝ →ₗ[ℝ] MvPolynomial (Fin 2) ℝ)
    (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap := by
  rw [Commute, SemiconjBy]
  apply LinearMap.ext
  intro p
  simpa using pderiv_comm (0 : Fin 2) 1 p

/-! 5.74 Commuting operators correspond to commuting matrices. -/

theorem commute_iff_matrixOf_commute {n : ℕ} {v : Fin n → V}
    (hv : IsBasis F v) (S T : V →ₗ[F] V) :
    Commute S T ↔
      Commute (matrixOf hv hv S) (matrixOf hv hv T) := by
  repeat rw [Commute, SemiconjBy]
  constructor
  · intro h
    rw [← matrixOf_comp hv hv hv S T, ← matrixOf_comp hv hv hv T S]
    have : S ∘ₗ T = T ∘ₗ S := by exact h
    rw [this]
  · intro h
    have hinj : Function.Injective
        (LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis) :=
      (LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis).injective
    apply hinj
    have h1 : LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis (S * T) =
        matrixOf hv hv S * matrixOf hv hv T := matrixOf_comp hv hv hv S T
    have h2 : LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis (T * S) =
        matrixOf hv hv T * matrixOf hv hv S := matrixOf_comp hv hv hv T S
    rw [h1, h2, h]

/-! 5.75 Eigenspaces are invariant under commuting operators. -/

theorem eigenspace_invariant_of_commute (S T : V →ₗ[F] V)
    (hcomm : Commute S T) (lam : F) :
    InvariantUnder T (Module.End.eigenspace S lam) := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  -- {lit}`S(Tv) = T(Sv) = T(λv) = λ(Tv)`.
  have h := LinearMap.congr_fun hcomm v
  rw [Module.End.mul_apply, Module.End.mul_apply, hv, map_smul] at h
  exact h

/-! 5.76 Simultaneous diagonalizability is equivalent to commutativity (for
two diagonalizable operators). -/

private lemma mul_comm_of_isDiag {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.IsDiag) (hB : B.IsDiag) : Commute A B := by
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases eq_or_ne i j with rfl | hij
  · refine Finset.sum_congr rfl fun k _ => ?_
    rcases eq_or_ne k i with rfl | hki
    · exact mul_comm _ _
    · rw [hA (Ne.symm hki), hB (Ne.symm hki), zero_mul, zero_mul]
  · have h1 : ∀ k ∈ Finset.univ, A i k * B k j = 0 := by
      intro k _
      rcases eq_or_ne i k with rfl | hik
      · rw [hB hij, mul_zero]
      · rw [hA hik, zero_mul]
    have h2 : ∀ k ∈ Finset.univ, B i k * A k j = 0 := by
      intro k _
      rcases eq_or_ne i k with rfl | hik
      · rw [hA hij, mul_zero]
      · rw [hB hik, zero_mul]
    rw [Finset.sum_eq_zero h1, Finset.sum_eq_zero h2]

theorem commute_iff_simultaneously_diagonalizable [Finite F V]
    (S T : V →ₗ[F] V) (hS : IsDiagonalizable S) (hT : IsDiagonalizable T) :
    Commute S T ↔
      ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
        (matrixOf hv hv S).IsDiag ∧ (matrixOf hv hv T).IsDiag := by
  constructor
  · -- {lit}`V` is the sum of the eigenspaces of {lit}`S` (5.55); each is
    -- invariant under {lit}`T` (5.75), and {lit}`T` restricted there is
    -- diagonalizable (5.65). Concatenating bases of {lit}`T`-eigenvectors
    -- of the eigenspaces of {lit}`S` and extracting a basis (2.30) gives a
    -- basis of simultaneous eigenvectors.
    intro hcomm
    classical
    obtain ⟨nS, vS, hvS, hAS⟩ := hS
    set s : Finset F := Finset.univ.image fun k => matrixOf hvS hvS S k k
      with hs_def
    set mu : Fin s.card → F := fun k => (s.equivFin.symm k : F) with hmu_def
    have htop : (⨆ k, Module.End.eigenspace S (mu k)) = ⊤ := by
      rw [eq_top_iff, ← hvS.2, Submodule.span_le]
      rintro x ⟨j, rfl⟩
      have hj_mem : matrixOf hvS hvS S j j ∈ s :=
        Finset.mem_image_of_mem _ (Finset.mem_univ j)
      refine Submodule.mem_iSup_of_mem (s.equivFin ⟨_, hj_mem⟩) ?_
      have hval : mu (s.equivFin ⟨_, hj_mem⟩) = matrixOf hvS hvS S j j := by
        simp only [hmu_def, Equiv.symm_apply_apply]
      rw [hval]
      exact Module.End.mem_eigenspace_iff.mpr
        (apply_eq_smul_of_isDiag hvS S hAS j)
    have hinv : ∀ k, InvariantUnder T (Module.End.eigenspace S (mu k)) :=
      fun k => eigenspace_invariant_of_commute S T hcomm (mu k)
    have hrestr : ∀ k, IsDiagonalizable (hinv k).restrict :=
      fun k => isDiagonalizable_restrict T hT _ (hinv k)
    choose M u hu hdiag using hrestr
    set w : Fin (∑ k, M k) → V :=
      (fun p : (k : Fin s.card) × Fin (M k) => ((u p.1 p.2 : _) : V)) ∘
        ⇑finSigmaFinEquiv.symm with hw_def
    have hw_spans : Spans F w := by
      show Submodule.span F (Set.range w) = ⊤
      rw [hw_def, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
      rw [Set.range_sigma_eq_iUnion_range, Submodule.span_iUnion]
      rw [← htop]
      refine iSup_congr fun k => ?_
      have h1 : Submodule.span F
          (Set.range fun i => ((u k i : _) : V)) =
          Submodule.map (Module.End.eigenspace S (mu k)).subtype
            (Submodule.span F (Set.range (u k))) := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      have h2 : Submodule.span F (Set.range (u k)) = ⊤ := (hu k).2
      rw [h1, h2, Submodule.map_subtype_top]
    obtain ⟨n, v, hv, hsub⟩ := exists_basis_of_spans w hw_spans
    refine ⟨n, v, hv, isDiag_matrixOf_of_eigenvectors hv S ?_,
      isDiag_matrixOf_of_eigenvectors hv T ?_⟩
    · intro j
      obtain ⟨p, hp⟩ := hsub ⟨j, rfl⟩
      refine ⟨mu (finSigmaFinEquiv.symm p).1, ?_⟩
      have hmem : v j ∈ Module.End.eigenspace S
          (mu (finSigmaFinEquiv.symm p).1) := by
        rw [← hp]
        exact (u _ _).2
      exact Module.End.mem_eigenspace_iff.mp hmem
    · intro j
      obtain ⟨p, hp⟩ := hsub ⟨j, rfl⟩
      refine ⟨matrixOf (hu (finSigmaFinEquiv.symm p).1)
        (hu (finSigmaFinEquiv.symm p).1)
        (hinv (finSigmaFinEquiv.symm p).1).restrict
        (finSigmaFinEquiv.symm p).2 (finSigmaFinEquiv.symm p).2, ?_⟩
      have h1 := apply_eq_smul_of_isDiag (hu (finSigmaFinEquiv.symm p).1)
        (hinv (finSigmaFinEquiv.symm p).1).restrict
        (hdiag (finSigmaFinEquiv.symm p).1) (finSigmaFinEquiv.symm p).2
      have h2 := congrArg Subtype.val h1
      rw [Submodule.coe_smul,
        (hinv (finSigmaFinEquiv.symm p).1).restrict_apply] at h2
      rw [← hp]
      exact h2
  · -- Conversely, diagonal matrices commute, so {lit}`S` and {lit}`T`
    -- commute by 5.74.
    rintro ⟨n, v, hv, hAS, hAT⟩
    rw [commute_iff_matrixOf_commute hv S T]
    exact mul_comm_of_isDiag hAS hAT

/-! 5.78 Common eigenvector for commuting operators: every pair of
commuting operators on a finite-dimensional nonzero complex vector space
has a common eigenvector. -/

theorem exists_common_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (S T : V →ₗ[ℂ] V)
    (hcomm : Commute S T) :
    ∃ v : V, (∃ lam : ℂ, HasEigenvector S lam v) ∧
      ∃ mu : ℂ, HasEigenvector T mu v := by
  -- {lit}`S` has an eigenvalue {lit}`λ` (5.19); the eigenspace
  -- {lit}`E(λ, S)` is invariant under {lit}`T` (5.75), so {lit}`T`
  -- restricted to it has an eigenvector (5.19 again).
  obtain ⟨lam, hlam⟩ := LADR.Section_5B.exists_eigenvalue S
  have hE_ne : Nontrivial (Module.End.eigenspace S lam) := by
    obtain ⟨x, hx_ne, hx_eq⟩ := Module.End.hasEigenvalue_iff_exists.mp hlam
    exact ⟨⟨x, Module.End.mem_eigenspace_iff.mpr hx_eq⟩, 0,
      fun h => hx_ne (by simpa using congrArg Subtype.val h)⟩
  have hinv : InvariantUnder T (Module.End.eigenspace S lam) :=
    eigenspace_invariant_of_commute S T hcomm lam
  obtain ⟨nu, hnu⟩ := LADR.Section_5B.exists_eigenvalue hinv.restrict
  obtain ⟨u, hu_ne, hu_eq⟩ := Module.End.hasEigenvalue_iff_exists.mp hnu
  have hv_ne : (u : V) ≠ 0 := fun h => hu_ne (Subtype.ext h)
  have hTu : T (u : V) = nu • (u : V) := by
    have h := congrArg Subtype.val hu_eq
    rwa [Submodule.coe_smul, hinv.restrict_apply] at h
  exact ⟨(u : V), ⟨lam, u.2, hv_ne⟩,
    ⟨nu, Module.End.mem_eigenspace_iff.mpr hTu, hv_ne⟩⟩

/-! 5.79 Example: the partial differentiation operators on {lit}`𝒫ₘ(ℝ², ℂ)`
have the nonzero constant functions as their common eigenvectors, as promised by
5.78. Each {lit}`∂/∂xᵢ` annihilates a constant, so a nonzero constant is a
common eigenvector with eigenvalue {lit}`0`. -/

example (c : ℂ) (hc : c ≠ 0) :
    HasEigenvector (MvPolynomial.pderiv (0 : Fin 2)).toLinearMap 0
        (MvPolynomial.C c : MvPolynomial (Fin 2) ℂ) ∧
      HasEigenvector (MvPolynomial.pderiv (1 : Fin 2)).toLinearMap 0
        (MvPolynomial.C c : MvPolynomial (Fin 2) ℂ) := by
  constructor <;>
    exact ⟨Module.End.mem_eigenspace_iff.mpr (by simp), by simpa using hc⟩

/-! 5.80 Commuting operators are simultaneously upper triangularizable
(over {lit}`ℂ`). Proof by induction on {lit}`dim V`, following the book: take
a common eigenvector {lit}`v₁` (5.78), a complement {lit}`W` with
{lit}`V = span(v₁) ⊕ W` (2.33), the projection {lit}`P : V → W` along
{lit}`span(v₁)`, and apply the induction hypothesis to the commuting operators
{lit}`Ŝ = P S|_W` and {lit}`T̂ = P T|_W`. -/

private lemma simul_upperTriangular_aux :
    ∀ (N : ℕ) (V : Type u) (_ : AddCommGroup V),
      ∀ (_ : Module ℂ V) (_ : Module.Finite ℂ V), finrank ℂ V = N →
      ∀ S T : V →ₗ[ℂ] V, Commute S T →
      ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
        IsUpperTriangular (matrixOf hv hv S) ∧
          IsUpperTriangular (matrixOf hv hv T) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ _ hV S T hcomm
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · -- {lit}`V = {0}`: the empty basis works.
      have hsub : Subsingleton V := by
        rw [← Module.finrank_zero_iff (R := ℂ)]
        exact hV
      refine ⟨0, Fin.elim0, ⟨linearIndependent_empty_type, ?_⟩, ?_, ?_⟩
      · show Submodule.span ℂ (Set.range Fin.elim0) = ⊤
        rw [Set.range_eq_empty, Submodule.span_empty, eq_top_iff]
        intro x _
        rw [Subsingleton.elim x 0]
        exact Submodule.zero_mem _
      · intro j _ _
        exact j.elim0
      · intro j _ _
        exact j.elim0
    · have : Nontrivial V :=
        Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
      -- Let {lit}`v₁` be any common eigenvector of {lit}`S` and {lit}`T`
      -- (5.78). Hence {lit}`Sv₁, Tv₁ ∈ span(v₁)`.
      obtain ⟨v₁, ⟨lamS, hSv⟩, ⟨lamT, hTv⟩⟩ :=
        exists_common_eigenvector S T hcomm
      have hv₁_ne : v₁ ≠ 0 := hSv.2
      have hlamS : S v₁ = lamS • v₁ := Module.End.mem_eigenspace_iff.mp hSv.1
      have hlamT : T v₁ = lamT • v₁ := Module.End.mem_eigenspace_iff.mp hTv.1
      set U : Submodule ℂ V := Submodule.span ℂ {v₁} with hU_def
      have hU_rank : finrank ℂ U = 1 := finrank_span_singleton hv₁_ne
      have hUS_inv : InvariantUnder S U := by
        intro x hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hlamS, smul_smul]
        exact Submodule.mem_span_singleton.mpr ⟨a * lamS, rfl⟩
      have hUT_inv : InvariantUnder T U := by
        intro x hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hlamT, smul_smul]
        exact Submodule.mem_span_singleton.mpr ⟨a * lamT, rfl⟩
      -- Let {lit}`W` be a subspace with {lit}`V = span(v₁) ⊕ W` (2.33), and
      -- {lit}`P : V → W` the projection {lit}`P(a v₁ + w) = w`.
      obtain ⟨W, hUW⟩ := LADR.Section_2B.exists_isCompl U
      set P : V →ₗ[ℂ] W := W.linearProjOfIsCompl U hUW.symm with hP_def
      have hPw : ∀ w : W, P w = w := W.linearProjOfIsCompl_apply_left hUW.symm
      have hPv₁ : P v₁ = 0 := W.linearProjOfIsCompl_apply_right' hUW.symm _
        (Submodule.mem_span_singleton_self v₁)
      -- {lit}`x − P x ∈ span(v₁)`, i.e. {lit}`x = a v₁ + P x`.
      have hdecomp : ∀ x : V, x - (P x : V) ∈ U := fun x =>
        (W.linearProjOfIsCompl_apply_eq_zero_iff hUW.symm).mp
          (by rw [map_sub, hPw, sub_self])
      -- If {lit}`R(span v₁) ⊆ span v₁`, then {lit}`P(R(P x)) = P(R x)`,
      -- because {lit}`R(x − P x) ∈ span(v₁)` and {lit}`P v₁ = 0`.
      have hPR : ∀ R : V →ₗ[ℂ] V, InvariantUnder R U → ∀ x, P (R (P x)) = P (R x) := by
        intro R hR x
        have h : R x - R (P x) ∈ U := by
          rw [← map_sub]
          exact hR _ (hdecomp x)
        rw [← sub_eq_zero, ← map_sub,
          W.linearProjOfIsCompl_apply_eq_zero_iff hUW.symm]
        rw [← neg_mem_iff, neg_sub]
        exact h
      -- Define {lit}`Ŝ w = P(S w)` and {lit}`T̂ w = P(T w)`; they commute,
      -- since {lit}`(Ŝ T̂) w = P((ST) w)` and {lit}`(T̂ Ŝ) w = P((TS) w)`.
      let hat : (V →ₗ[ℂ] V) → (W →ₗ[ℂ] W) := fun R => P ∘ₗ R ∘ₗ W.subtype
      have hcomm_hat : Commute (hat S) (hat T) := by
        show hat S * hat T = hat T * hat S
        refine LinearMap.ext fun w => ?_
        show P (S (P (T w))) = P (T (P (S w)))
        rw [hPR S hUS_inv, hPR T hUT_inv]
        exact congrArg P (LinearMap.congr_fun hcomm (w : V))
      have hW_rank : finrank ℂ W = N - 1 := by
        have := Submodule.finrank_add_eq_of_isCompl hUW
        omega
      -- By induction, a basis {lit}`v₂, …, vₙ` of {lit}`W` makes {lit}`Ŝ, T̂`
      -- upper triangular.
      obtain ⟨M, wl, hwl, hAS, hAT⟩ := ih (N - 1) (by omega) W
        inferInstance inferInstance inferInstance hW_rank
        (hat S) (hat T) hcomm_hat
      -- The list {lit}`v₁, …, vₙ` is a basis of {lit}`V`.
      set v : Fin (M + 1) → V := Fin.cons v₁ fun i => (wl i : V) with hv_def
      have hM : M = N - 1 := by
        rw [← hW_rank]
        exact isBasis_card_eq_finrank wl hwl
      have hv_li : LinearIndependent ℂ v := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hg' : g 0 • v₁ + ∑ i : Fin M, g i.succ • (wl i : V) = 0 := by
          rw [Fin.sum_univ_succ] at hg
          exact hg
        -- Apply {lit}`P`: the {lit}`wl` coefficients vanish.
        have hq : ∑ i : Fin M, g i.succ • wl i = 0 := by
          have h1 := congrArg P hg'
          rw [map_add, map_smul, hPv₁, smul_zero, zero_add, map_sum,
            map_zero] at h1
          rw [← h1]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hPw]
        have hzero_succ : ∀ i : Fin M, g i.succ = 0 :=
          Fintype.linearIndependent_iff.mp hwl.1 _ hq
        have hzero_0 : g 0 = 0 := by
          rw [Finset.sum_eq_zero (fun i _ => by
            rw [hzero_succ i, zero_smul]), add_zero] at hg'
          rcases smul_eq_zero.mp hg' with h | h
          · exact h
          · exact absurd h hv₁_ne
        intro j
        induction j using Fin.cases with
        | zero => exact hzero_0
        | succ i => exact hzero_succ i
      have hv_basis : IsBasis ℂ v :=
        isBasis_of_linearIndependent_of_card_eq v hv_li (by omega)
      -- Verify condition 5.39(c) for both operators.
      have hmain : ∀ (R : V →ₗ[ℂ] V) (_ : InvariantUnder R U)
          (lamR : ℂ) (_ : R v₁ = lamR • v₁)
          (_ : IsUpperTriangular (matrixOf hwl hwl (hat R))),
          IsUpperTriangular (matrixOf hv_basis hv_basis R) := by
        intro R _ lamR hlamR hAR
        apply ((tfae_upperTriangular hv_basis R).out 2 0).mp
        intro k
        induction k using Fin.cases with
        | zero =>
          -- {lit}`R v₁ = λ v₁ ∈ span(v₁)`.
          have h0 : v 0 = v₁ := rfl
          rw [h0, hlamR]
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨0, le_refl 0, h0⟩)
        | succ i =>
          -- {lit}`R vₖ = a v₁ + R̂ vₖ` with {lit}`R̂ vₖ ∈ span(v₂, …, vₖ)`
          -- (upper-triangularity of {lit}`R̂`).
          have hq30 := (tfae_upperTriangular hwl (hat R)).out 0 2
          have hq3 := hq30.mp hAR i
          have hsucc : v i.succ = wl i := rfl
          have hmem : R (wl i : V) ∈
              U ⊔ Submodule.span ℂ ((fun j => (wl j : V)) '' {j | j ≤ i}) := by
            rw [← sub_add_cancel (R (wl i : V)) (P (R (wl i : V)) : V)]
            refine Submodule.add_mem_sup (hdecomp _) ?_
            have h := Submodule.mem_map_of_mem (f := W.subtype) hq3
            rw [Submodule.map_span, ← Set.image_comp] at h
            exact h
          rw [hsucc]
          -- {lit}`U ⊔ span(v₂, …, vₖ) ⊆ span(v₁, …, vₖ)`.
          have hle : U ⊔ Submodule.span ℂ ((fun j => (wl j : V)) '' {j | j ≤ i}) ≤
              Submodule.span ℂ (v '' {j | j ≤ i.succ}) := by
            apply sup_le
            · rw [hU_def, Submodule.span_le]
              rintro x rfl
              exact Submodule.subset_span ⟨0, Fin.zero_le _, rfl⟩
            · rw [Submodule.span_le]
              rintro x ⟨j, hj, rfl⟩
              refine Submodule.subset_span ⟨j.succ, ?_, rfl⟩
              rw [Set.mem_setOf_eq]
              exact Fin.succ_le_succ_iff.mpr hj
          exact hle hmem
      -- Thus {lit}`S` and {lit}`T` are upper triangular w.r.t. {lit}`v₁, …, vₙ`.
      exact ⟨M + 1, v, hv_basis,
        hmain S hUS_inv lamS hlamS hAS, hmain T hUT_inv lamT hlamT hAT⟩

theorem exists_simultaneous_upperTriangular {V : Type u} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (S T : V →ₗ[ℂ] V)
    (hcomm : Commute S T) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      IsUpperTriangular (matrixOf hv hv S) ∧
        IsUpperTriangular (matrixOf hv hv T) :=
  simul_upperTriangular_aux (finrank ℂ V) V inferInstance inferInstance
    inferInstance rfl S T hcomm

/-! 5.81 Eigenvalues of sums and products of commuting operators (over
{lit}`ℂ`): every eigenvalue of {lit}`S + T` is an eigenvalue of {lit}`S`
plus an eigenvalue of {lit}`T`, and every eigenvalue of {lit}`ST` is an
eigenvalue of {lit}`S` times an eigenvalue of {lit}`T`. -/

private lemma isUpperTriangular_add {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F} (hA : IsUpperTriangular A)
    (hB : IsUpperTriangular B) : IsUpperTriangular (A + B) := by
  intro j k hkj
  rw [Matrix.add_apply, hA j k hkj, hB j k hkj, add_zero]

private lemma isUpperTriangular_mul {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F} (hA : IsUpperTriangular A)
    (hB : IsUpperTriangular B) : IsUpperTriangular (A * B) := by
  intro j k hkj
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hij : i < j
  · rw [hA j i hij, zero_mul]
  · rw [hB i k (lt_of_lt_of_le hkj (le_of_not_gt hij)), mul_zero]

private lemma mul_diag_of_isUpperTriangular {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) F} (hA : IsUpperTriangular A)
    (hB : IsUpperTriangular B) (k : Fin n) :
    (A * B) k k = A k k * B k k := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single k
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with h | h
    · rw [hA k i h, zero_mul]
    · rw [hB i k h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

private lemma matrixOf_add {n : ℕ} {v : Fin n → V} (hv : IsBasis F v)
    (S T : V →ₗ[F] V) :
    matrixOf hv hv (S + T) = matrixOf hv hv S + matrixOf hv hv T :=
  map_add (LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis) S T

theorem eigenvalue_add_of_commute {V : Type u} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (S T : V →ₗ[ℂ] V)
    (hcomm : Commute S T) (alpha : ℂ)
    (h : HasEigenvalue (S + T) alpha) :
    ∃ lam mu : ℂ, HasEigenvalue S lam ∧ HasEigenvalue T mu ∧
      alpha = lam + mu := by
  obtain ⟨n, v, hv, hAS, hAT⟩ := exists_simultaneous_upperTriangular S T hcomm
  have hsum : IsUpperTriangular (matrixOf hv hv (S + T)) := by
    rw [matrixOf_add hv S T]
    exact isUpperTriangular_add hAS hAT
  obtain ⟨k, hk⟩ := (isEigenvalue_iff_diag hv (S + T) hsum alpha).mp h
  rw [matrixOf_add hv S T, Matrix.add_apply] at hk
  exact ⟨matrixOf hv hv S k k, matrixOf hv hv T k k,
    (isEigenvalue_iff_diag hv S hAS _).mpr ⟨k, rfl⟩,
    (isEigenvalue_iff_diag hv T hAT _).mpr ⟨k, rfl⟩, hk.symm⟩

theorem eigenvalue_mul_of_commute {V : Type u} [AddCommGroup V]
    [Module ℂ V] [Finite ℂ V] (S T : V →ₗ[ℂ] V)
    (hcomm : Commute S T) (alpha : ℂ)
    (h : HasEigenvalue (S ∘ₗ T) alpha) :
    ∃ lam mu : ℂ, HasEigenvalue S lam ∧ HasEigenvalue T mu ∧
      alpha = lam * mu := by
  obtain ⟨n, v, hv, hAS, hAT⟩ := exists_simultaneous_upperTriangular S T hcomm
  have hprod_eq : matrixOf hv hv (S ∘ₗ T) =
      matrixOf hv hv S * matrixOf hv hv T := matrixOf_comp hv hv hv S T
  have hprod : IsUpperTriangular (matrixOf hv hv (S ∘ₗ T)) := by
    rw [hprod_eq]
    exact isUpperTriangular_mul hAS hAT
  obtain ⟨k, hk⟩ := (isEigenvalue_iff_diag hv (S ∘ₗ T) hprod alpha).mp h
  rw [hprod_eq, mul_diag_of_isUpperTriangular hAS hAT] at hk
  exact ⟨matrixOf hv hv S k k, matrixOf hv hv T k k,
    (isEigenvalue_iff_diag hv S hAS _).mpr ⟨k, rfl⟩,
    (isEigenvalue_iff_diag hv T hAT _).mpr ⟨k, rfl⟩, hk.symm⟩

/-! # Exercises -/

/-- 5E.1 -/
theorem exercise_5E_1 :
    ∃ S T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ), Commute S T ∧
      (∃ U : Submodule ℝ (Fin 4 → ℝ),
        InvariantUnder S U ∧ ¬ InvariantUnder T U) ∧
      (∃ W : Submodule ℝ (Fin 4 → ℝ),
        InvariantUnder T W ∧ ¬ InvariantUnder S W) := by
  -- take S (x,y,z,w) = (y,x,z,w) and T (x,y,z,w) = (x,y,w,z)
  refine ⟨LinearMap.funLeft ℝ ℝ (Equiv.swap (0 : Fin 4) 1),
    LinearMap.funLeft ℝ ℝ (Equiv.swap (2 : Fin 4) 3), ?_, ?_, ?_⟩
  -- easy to show they commute as ST = TS = (y,x,w,z)
  · ext v i
    fin_cases i <;> rfl
  -- Take U = span{(1,1,0,1)} which is invariant under S but not T
  · refine ⟨Submodule.span ℝ {![1, 1, 0, 1]}, ?_, ?_⟩
    · intro x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul]
      refine Submodule.smul_mem _ c (Submodule.mem_span_singleton.mpr ⟨1, ?_⟩)
      ext i
      fin_cases i <;> simp [LinearMap.funLeft, Equiv.swap_apply_def]
    · intro h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
        (h _ (Submodule.mem_span_singleton_self _))
      have := congrFun hc 2
      simp [LinearMap.funLeft] at this
  -- Take W = span{(1,0,1,1)} which is invariant under T but not S
  · refine ⟨Submodule.span ℝ {![1, 0, 1, 1]}, ?_, ?_⟩
    · intro x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul]
      refine Submodule.smul_mem _ c (Submodule.mem_span_singleton.mpr ⟨1, ?_⟩)
      ext i
      fin_cases i <;> simp [LinearMap.funLeft, Equiv.swap_apply_def]
    · intro h
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
        (h _ (Submodule.mem_span_singleton_self _))
      have := congrFun hc 1
      simp [LinearMap.funLeft] at this

/-- The induction for 5E.2: the common eigenvectors of a family of pairwise
commuting diagonalizable operators span {lit}`V`. Stated for every space of
dimension {lit}`d`, so that the inductive step can be applied to eigenspaces. -/
private lemma span_common_eigenvectors_eq_top (d : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module F V] [Finite F V],
      finrank F V = d → ∀ 𝒮 : Set (V →ₗ[F] V), (∀ E ∈ 𝒮, IsDiagonalizable E) →
      (∀ E ∈ 𝒮, ∀ E' ∈ 𝒮, Commute E E') →
      Submodule.span F {v : V | ∀ E ∈ 𝒮, ∃ mu : F, E v = mu • v} = ⊤ := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V _ _ _ hd 𝒮 hdiag hcomm
  by_cases hscalar : ∀ E ∈ 𝒮, ∃ mu : F, E = mu • LinearMap.id
  · -- every vector is a common eigenvector
    rw [eq_top_iff]
    intro v _
    apply Submodule.subset_span
    intro E hE
    obtain ⟨mu, rfl⟩ := hscalar E hE
    exact ⟨mu, rfl⟩
  · push Not at hscalar
    obtain ⟨E₀, hE₀, hne⟩ := hscalar
    -- {lit}`V` is the sum of the eigenspaces of {lit}`E₀`
    have htop : (⨆ mu : F, Module.End.eigenspace E₀ mu) = ⊤ := by
      obtain ⟨n, v, hv, hA⟩ := hdiag E₀ hE₀
      rw [eq_top_iff, ← hv.2, Submodule.span_le]
      rintro x ⟨j, rfl⟩
      exact Submodule.mem_iSup_of_mem (matrixOf hv hv E₀ j j)
        (Module.End.mem_eigenspace_iff.mpr (apply_eq_smul_of_isDiag hv E₀ hA j))
    rw [eq_top_iff, ← htop, iSup_le_iff]
    intro mu
    set U := Module.End.eigenspace E₀ mu
    have hinv : ∀ E ∈ 𝒮, InvariantUnder E U := fun E hE =>
      eigenspace_invariant_of_commute E₀ E (hcomm E₀ hE₀ E hE) mu
    -- {lit}`U ≠ V`, since otherwise {lit}`E₀ = μI`
    have hlt : finrank F U < d := by
      rw [← hd]
      apply Submodule.finrank_lt
      intro hU
      apply hne mu
      refine LinearMap.ext fun v => ?_
      have hv : v ∈ U := hU ▸ Submodule.mem_top
      exact Module.End.mem_eigenspace_iff.mp hv
    -- the restrictions to {lit}`U` are diagonalizable and pairwise commute
    set 𝒮' : Set (U →ₗ[F] U) := {E' | ∃ E ∈ 𝒮, ∀ u : U, (E' u : V) = E u}
    have hdiag' : ∀ E' ∈ 𝒮', IsDiagonalizable E' := by
      rintro E' ⟨E, hE, hEE'⟩
      have hE' : E' = (hinv E hE).restrict :=
        LinearMap.ext fun u => Subtype.ext (by rw [hEE', (hinv E hE).restrict_apply])
      rw [hE']
      exact isDiagonalizable_restrict E (hdiag E hE) U (hinv E hE)
    have hcomm' : ∀ E₁ ∈ 𝒮', ∀ E₂ ∈ 𝒮', Commute E₁ E₂ := by
      rintro E₁ ⟨E, hE, h₁⟩ E₂ ⟨E', hE', h₂⟩
      show E₁ * E₂ = E₂ * E₁
      refine LinearMap.ext fun u => Subtype.ext ?_
      have h := LinearMap.congr_fun (hcomm E hE E' hE') (u : V)
      simp only [Module.End.mul_apply] at h ⊢
      simp only [h₁, h₂]
      exact h
    -- by induction, the common eigenvectors in {lit}`U` span {lit}`U`; they are
    -- common eigenvectors in {lit}`V`
    have hspan := ih _ hlt (V := U) rfl 𝒮' hdiag' hcomm'
    intro x hx
    have hx' : (⟨x, hx⟩ : U) ∈ Submodule.span F
        {u : U | ∀ E' ∈ 𝒮', ∃ c : F, E' u = c • u} := hspan ▸ Submodule.mem_top
    have hmap := Submodule.mem_map_of_mem (f := U.subtype) hx'
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨u, hu, rfl⟩ E hE
    obtain ⟨c, hc⟩ := hu (hinv E hE).restrict ⟨E, hE, fun w => rfl⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩

/-- 5E.2 A family of diagonalizable operators is simultaneously
diagonalizable iff its members pairwise commute. The set {lit}`𝒮` may be
arbitrary (possibly infinite). We assume {lit}`V` is finite-dimensional,
matching the standing hypothesis of the neighbouring exercise 5E.9. Extends
5.76 (the two-operator case). -/
theorem exercise_5E_2 [Finite F V] (𝒮 : Set (V →ₗ[F] V))
    (hdiag : ∀ E ∈ 𝒮, IsDiagonalizable E) :
    (∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis F v),
      ∀ E ∈ 𝒮, (matrixOf hv hv E).IsDiag) ↔
    (∀ E ∈ 𝒮, ∀ E' ∈ 𝒮, Commute E E') := by
  constructor
  -- => trivially for fixed pair apply the theorem from the chapter
  · rintro ⟨n, v, hv, hall⟩ E hE E' hE'
    exact (commute_iff_simultaneously_diagonalizable E E' (hdiag E hE)
      (hdiag E' hE')).mpr ⟨n, v, hv, hall E hE, hall E' hE'⟩
  -- <= strong induction on dim V, generalizing over V and 𝒮.
  -- case 1) every E ∈ 𝒮 is a multiple of the identity: any basis diagonalizes them all.
  -- case 2) some E₀ ∈ 𝒮 is not a multiple of the identity. V is the direct sum of the
  -- eigenspaces of E₀ (5.55), each of dim < dim V, and each invariant under every E ∈ 𝒮 (5.75).
  -- On each eigenspace U, the restrictions E|_U are diagonalizable (5.65) and pairwise commute,
  -- so by induction one basis of U diagonalizes all of them.
  -- Concatenating these bases gives a basis of V that diagonalizes every E ∈ 𝒮.
  · intro hcomm
    classical
    -- (the induction is `span_common_eigenvectors_eq_top`: common eigenvectors span V)
    have hspan := span_common_eigenvectors_eq_top _ rfl 𝒮 hdiag hcomm
    -- extract a basis consisting of common eigenvectors
    obtain ⟨b, hbC, hbspan, hbli⟩ := exists_linearIndependent F
      {v : V | ∀ E ∈ 𝒮, ∃ mu : F, E v = mu • v}
    haveI : Fintype b := @Fintype.ofFinite b hbli.finite
    set e := Fintype.equivFin b
    have hrange : Set.range (fun j => (e.symm j : V)) = b := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (e.symm j).2
      · intro hx
        exact ⟨e ⟨x, hx⟩, by simp⟩
    refine ⟨Fintype.card b, fun j => (e.symm j : V),
      ⟨hbli.comp _ e.symm.injective, ?_⟩, fun E hE => ?_⟩
    · show Submodule.span F _ = ⊤
      rw [hrange, hbspan, hspan]
    · exact isDiag_matrixOf_of_eigenvectors _ E fun j => hbC (e.symm j).2 E hE

/-- 5E.3 -/
theorem exercise_5E_3 (S T : V →ₗ[F] V) (hcomm : Commute S T)
    (p : Polynomial F) :
    InvariantUnder T (ker (aeval S p)) ∧
      InvariantUnder T (range (aeval S p)) := by
  -- prove a lemma that if S and T commute, p(S) and T also commute
  have hc : Commute (aeval S p) T := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add_left hq
    | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact (Algebra.commute_algebraMap_left a T).mul_left (hcomm.pow_left n)
  have hpT : ∀ v, aeval S p (T v) = T (aeval S p v) := fun v =>
    LinearMap.congr_fun hc v
  constructor
  -- then if v in ker p(S), p(S) v = 0, then P(S) T v = T P(S) v = T 0 = 0
  -- so T v in ker p(S)
  · intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hpT, hv, map_zero]
  -- if w = p(S) v, then P(s) T w = T P(s) w = T p(S) v = T w, so T w is in the range of p(S) too.
  · rintro w ⟨v, rfl⟩
    exact ⟨T v, hpT v⟩

/-- 5E.4 Prove or give a counterexample: if {lit}`A` is diagonal and
{lit}`B` is upper triangular (of the same size), then {lit}`A` and {lit}`B`
commute. Stated for real matrices of arbitrary (unspecified) size. -/
def exercise_5E_4 :
    Decidable (∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
      A.IsDiag → IsUpperTriangular B → Commute A B) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- use [0 0; 0 1] as diag and [0 1; 0 0] as upper triangular
  -- one product is 0, and the other [0 0; 0 1]
  intro h
  have hA : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsDiag := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hB : IsUpperTriangular (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro j k hkj
    fin_cases j <;> fin_cases k <;> simp_all
  have := congrFun (congrFun (h 2 _ _ hA hB) 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

/-- 5E.5 A pair of operators commutes iff their dual operators commute. -/
theorem exercise_5E_5 [Finite F V] (S T : V →ₗ[F] V) :
    Commute S T ↔ Commute S.dualMap T.dualMap := by
  -- pick a basis, and work with matrices
  obtain ⟨n, v, hv⟩ := exists_basis (F := F) (V := V)
  rw [Commute, SemiconjBy, Commute, SemiconjBy,
    ← (LinearMap.toMatrix hv.toModuleBasis hv.toModuleBasis).injective.eq_iff,
    ← (LinearMap.toMatrix hv.toModuleBasis.dualBasis
      hv.toModuleBasis.dualBasis).injective.eq_iff,
    LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul,
    LinearMap.toMatrix_mul]
  -- becomes ST = TS ↔ S^t T^t = T^t S^t
  rw [LADR.Section_3F.toMatrix_dualMap_eq_transpose v v hv hv S,
    LADR.Section_3F.toMatrix_dualMap_eq_transpose v v hv hv T]
  -- but one can show (ST)^t = T^t S^t,
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
  -- so ST = TS ↔ (ST)^t = (TS)^t
  rw [eq_comm (a := Matrix.transpose _)]
  -- which is trivial A = B ↔ A^t = B^t
  exact Matrix.transpose_inj.symm

/-- 5E.6 -/
theorem exercise_5E_6 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (S T : V →ₗ[ℂ] V)
    (hcomm : Commute S T) :
    ∃ α γ : ℂ,
      range (S - α • (LinearMap.id : V →ₗ[ℂ] V)) ⊔
        range (T - γ • (LinearMap.id : V →ₗ[ℂ] V)) ≠ ⊤ := by
  -- by theorem we can find a basis in which both are upper triangular
  obtain ⟨n, v, hv, hS, hT⟩ := exists_simultaneous_upperTriangular S T hcomm
  have hn : 0 < n := by
    have h := Module.finrank_pos (R := ℂ) (M := V)
    rwa [Module.finrank_eq_card_basis hv.toModuleBasis, Fintype.card_fin] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- take a to be the last diagonal entry of S and γ to be the last diagonal entry of T
  refine ⟨matrixOf hv hv S (Fin.last m) (Fin.last m),
    matrixOf hv hv T (Fin.last m) (Fin.last m), ?_⟩
  -- then both S - α • id and T - γ • id have a zeroes in the last row
  have key : ∀ A : V →ₗ[ℂ] V, IsUpperTriangular (matrixOf hv hv A) →
      range (A - matrixOf hv hv A (Fin.last m) (Fin.last m) • LinearMap.id) ≤
        ker (hv.toModuleBasis.coord (Fin.last m)) := by
    intro A hA
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply]
    have hzero : (hv.toModuleBasis.coord (Fin.last m)).comp
        (A - matrixOf hv hv A (Fin.last m) (Fin.last m) • LinearMap.id) = 0 := by
      refine hv.toModuleBasis.ext fun k => ?_
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_sub, map_smul, Module.Basis.coord_apply,
        LinearMap.zero_apply, Module.Basis.repr_self, Finsupp.single_apply]
      rw [hv.toModuleBasis_apply k, ← matrixOf_apply hv hv]
      rcases (Fin.le_last k).lt_or_eq with hk | rfl
      · rw [hA _ _ hk, if_neg hk.ne, smul_zero, sub_zero]
      · rw [if_pos rfl, smul_eq_mul, mul_one, sub_self]
    rw [hzero, LinearMap.zero_apply]
  -- so their range has a zero in the last coordinate, and hence cannot be the whole space
  intro htop
  have hle := sup_le (key S hS) (key T hT)
  rw [htop] at hle
  have h1 := hle (Submodule.mem_top : hv.toModuleBasis (Fin.last m) ∈ ⊤)
  rw [LinearMap.mem_ker, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same] at h1
  exact one_ne_zero h1

/-- 5E.7 If {lit}`S` is diagonalizable and {lit}`T` commutes with {lit}`S`,
then there is a basis with respect to which {lit}`S` is diagonal and
{lit}`T` is upper triangular. -/
theorem exercise_5E_7 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (S T : V →ₗ[ℂ] V) (hS : IsDiagonalizable S)
    (hcomm : Commute S T) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      (matrixOf hv hv S).IsDiag ∧ IsUpperTriangular (matrixOf hv hv T) := by
  -- since S is diag, V = Π eigenspaces of S
  classical
  set s := (Module.End.finite_hasEigenvalue S).toFinset
  set mu : Fin s.card → ℂ := fun k => (s.equivFin.symm k : ℂ)
  have hmu : Function.Injective mu := fun a b h =>
    s.equivFin.symm.injective (Subtype.ext h)
  have hall : ∀ γ : ℂ, HasEigenvalue S γ ↔ ∃ k, mu k = γ := by
    intro γ
    constructor
    · intro hγ
      have hγs : γ ∈ s := (Set.Finite.mem_toFinset _).mpr hγ
      exact ⟨s.equivFin ⟨γ, hγs⟩, by simp [mu]⟩
    · rintro ⟨k, rfl⟩
      exact (Set.Finite.mem_toFinset _).mp (s.equivFin.symm k).2
  -- (5.55)
  have htop : (⨆ k, Module.End.eigenspace S (mu k)) = ⊤ :=
    ((LADR.Section_5D.tfae_isDiagonalizable S mu hmu hall).out 0 2).mp hS
  have hint : DirectSum.IsInternal fun k => Module.End.eigenspace S (mu k) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      ((Module.End.eigenspaces_iSupIndep S).comp hmu) htop
  -- each eigenspace is T-invariant due to commutativity
  have hinv : ∀ k, InvariantUnder T (Module.End.eigenspace S (mu k)) :=
    fun k => eigenspace_invariant_of_commute S T hcomm (mu k)
  -- within each eigenspace, S = λ I, which means it is diag for all bases
  -- so we can pick a basis for each eigenspace to upper triangularize T restricted to it
  -- (by theorem in complex VS)
  choose M u hu htri using fun k =>
    LADR.Section_5C.exists_upperTriangular_complex (hinv k).restrict
  -- then glue the bases back together to form a basis of V
  set b := (hint.collectedBasis fun k => (hu k).toModuleBasis).reindex finSigmaFinEquiv
  have hw : IsBasis ℂ ⇑b := ⟨b.linearIndependent, b.span_eq⟩
  have hb : ∀ p, b (finSigmaFinEquiv p) = (u p.1 p.2 : V) := by
    intro p
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply,
      DirectSum.IsInternal.collectedBasis_coe]
    exact congrArg Subtype.val ((hu p.1).toModuleBasis_apply p.2)
  -- the resulting basis will make S diagonal and T upper triangular
  refine ⟨_, b, hw, isDiag_matrixOf_of_eigenvectors hw S fun j => ?_,
    ((tfae_upperTriangular hw T).out 0 2).mpr fun j => ?_⟩
  · obtain ⟨p, rfl⟩ := finSigmaFinEquiv.surjective j
    rw [hb]
    exact ⟨mu p.1, Module.End.mem_eigenspace_iff.mp (u p.1 p.2).2⟩
  · obtain ⟨⟨k, a⟩, rfl⟩ := finSigmaFinEquiv.surjective j
    have h3 := ((tfae_upperTriangular (hu k) (hinv k).restrict).out 0 2).mp (htri k)
    have h := h3 a
    have h' := Submodule.mem_map_of_mem
      (f := (Module.End.eigenspace S (mu k)).subtype) h
    rw [Submodule.map_span, ← Set.image_comp] at h'
    rw [hb]
    refine Submodule.span_mono ?_ h'
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨finSigmaFinEquiv ⟨k, c⟩, ?_, hb ⟨k, c⟩⟩
    show finSigmaFinEquiv ⟨k, c⟩ ≤ finSigmaFinEquiv ⟨k, a⟩
    rw [Fin.le_def, finSigmaFinEquiv_apply, finSigmaFinEquiv_apply]
    exact Nat.add_le_add_left hc _

/-- Exponents {lit}`(a, b)` of the monomials {lit}`xᵃ yᵇ` in the basis of
5E.8: {lit}`1, x, x², x³, y, xy, x²y, y², xy², y³`. -/
private def exps5E8 : Fin 10 → ℕ × ℕ :=
  ![(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1), (0, 2), (1, 2), (0, 3)]

private noncomputable def mono5E8 (k : Fin 10) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![(exps5E8 k).1, (exps5E8 k).2]

private lemma mono5E8_apply (k : Fin 10) (i : Fin 2) :
    mono5E8 k i = ![(exps5E8 k).1, (exps5E8 k).2] i := rfl

private lemma mono5E8_injective : Function.Injective mono5E8 := by
  intro j k h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp only [mono5E8_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hinj : Function.Injective exps5E8 := by decide
  exact hinj (Prod.ext h0 h1)

private lemma sum_fin_two_exps (n : Fin 2 →₀ ℕ) :
    (n.sum fun _ e => e) = n 0 + n 1 := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]

/-- Every monomial in two variables of degree at most {lit}`3` is in the list. -/
private lemma mono5E8_surj (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 ≤ 3) :
    ∃ k, mono5E8 k = n := by
  obtain ⟨k, hk⟩ : ∃ k, exps5E8 k = (n 0, n 1) := by
    generalize n 0 = a, n 1 = b at hn ⊢
    have ha : a ≤ 3 := by omega
    have hb : b ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> first | omega | decide
  refine ⟨k, Finsupp.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩ <;>
    simp [mono5E8_apply, hk]

/-- Differentiating a basis monomial gives a multiple of the monomial
{lit}`prev k` (or {lit}`0`). -/
private lemma pderiv_mono5E8 (i : Fin 2) (k k' : Fin 10)
    (h : mono5E8 k i = 0 ∨ mono5E8 k' = mono5E8 k - Finsupp.single i 1) :
    MvPolynomial.pderiv i (MvPolynomial.monomial (mono5E8 k) (1 : ℝ)) =
      (mono5E8 k i : ℝ) • MvPolynomial.monomial (mono5E8 k') 1 := by
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.smul_monomial, one_mul, smul_eq_mul,
    mul_one]
  rcases h with h | h
  · simp [h]
  · rw [h]

/-- Reduces the table of predecessors of 5E.8 to a decidable statement about
exponents. -/
private lemma mono5E8_table (i : Fin 2) (prev : Fin 10 → Fin 10)
    (h : ∀ k, ![(exps5E8 k).1, (exps5E8 k).2] i = 0 ∨ (prev k < k ∧
      ∀ i', ![(exps5E8 (prev k)).1, (exps5E8 (prev k)).2] i' =
        ![(exps5E8 k).1, (exps5E8 k).2] i' - if i = i' then 1 else 0))
    (k : Fin 10) :
    mono5E8 k i = 0 ∨
      (prev k < k ∧ mono5E8 (prev k) = mono5E8 k - Finsupp.single i 1) := by
  rcases h k with h | ⟨hlt, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨hlt, Finsupp.ext fun i' => ?_⟩
    rw [Finsupp.coe_tsub, Pi.sub_apply, mono5E8_apply, mono5E8_apply, h,
      Finsupp.single_apply]

/-- 5E.8 A basis of {lit}`𝒫₃(ℝ²)` with respect to which the two partial
differentiation operators both have upper-triangular matrices. (Stated for
any pair of operators implementing {lit}`∂/∂x` and {lit}`∂/∂y` on the space
of polynomials in two variables of total degree at most {lit}`3`.) -/
theorem exercise_5E_8
    (Dx Dy : MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3 →ₗ[ℝ]
      MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3)
    (hDx : ∀ p, (Dx p : MvPolynomial (Fin 2) ℝ) =
      MvPolynomial.pderiv 0 (p : MvPolynomial (Fin 2) ℝ))
    (hDy : ∀ p, (Dy p : MvPolynomial (Fin 2) ℝ) =
      MvPolynomial.pderiv 1 (p : MvPolynomial (Fin 2) ℝ)) :
    ∃ (n : ℕ) (v : Fin n → MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3)
      (hv : IsBasis ℝ v),
      IsUpperTriangular (matrixOf hv hv Dx) ∧
        IsUpperTriangular (matrixOf hv hv Dy) := by
  -- take the basis - const, x, x^2, x^3, y, xy, x^2y, y^2, xy^2, y^3
  have hmem : ∀ k, MvPolynomial.monomial (mono5E8 k) (1 : ℝ) ∈
      MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3 := by
    intro k
    show _ ∈ MvPolynomial.restrictSupport ℝ _
    rw [MvPolynomial.monomial_mem_restrictSupport]
    left
    show (mono5E8 k).sum (fun _ e => e) ≤ 3
    rw [sum_fin_two_exps, mono5E8_apply, mono5E8_apply]
    revert k
    decide
  let v : Fin 10 → MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3 :=
    fun k => ⟨_, hmem k⟩
  have hv : IsBasis ℝ v := by
    constructor
    · apply LinearIndependent.of_comp (MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3).subtype
      have := (MvPolynomial.basisMonomials (Fin 2) ℝ).linearIndependent.comp
        mono5E8 mono5E8_injective
      rw [MvPolynomial.coe_basisMonomials] at this
      exact this
    · show Submodule.span ℝ (Set.range v) = ⊤
      apply Submodule.map_injective_of_injective
        (MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3).injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact hmem k
      · refine le_trans (MvPolynomial.restrictSupport_eq_span (R := ℝ) _).le ?_
        apply Submodule.span_mono
        rintro _ ⟨n, hn, rfl⟩
        obtain ⟨k, rfl⟩ := mono5E8_surj n (by rw [← sum_fin_two_exps]; exact hn)
        exact ⟨k, rfl⟩
  -- easy to see that diff in both x and y for a fixed basis element only contributes
  -- to basis elements that came before it.
  have key : ∀ (D : MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3 →ₗ[ℝ]
      MvPolynomial.restrictTotalDegree (Fin 2) ℝ 3) (i : Fin 2) (prev : Fin 10 → Fin 10),
      (∀ p, (D p : MvPolynomial (Fin 2) ℝ) =
        MvPolynomial.pderiv i (p : MvPolynomial (Fin 2) ℝ)) →
      (∀ k, mono5E8 k i = 0 ∨
        (prev k < k ∧ mono5E8 (prev k) = mono5E8 k - Finsupp.single i 1)) →
      IsUpperTriangular (matrixOf hv hv D) := by
    intro D i prev hD hprev j k hkj
    have hDk : D (v k) = (mono5E8 k i : ℝ) • v (prev k) := by
      apply Subtype.ext
      rw [hD, Submodule.coe_smul]
      exact pderiv_mono5E8 i k (prev k) ((hprev k).imp id And.right)
    -- That translates to the matrices being upper triangular.
    rw [matrixOf_apply, hDk, map_smul, ← hv.toModuleBasis_apply (prev k),
      Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    rcases hprev k with h | ⟨hlt, _⟩
    · simp [h]
    · rw [if_neg (hlt.trans hkj).ne, smul_zero]
  refine ⟨10, v, hv, key Dx 0 ![0, 0, 1, 2, 4, 4, 5, 7, 7, 9] hDx
    (mono5E8_table _ _ (by decide)), key Dy 1 ![0, 0, 0, 0, 0, 1, 2, 4, 5, 7] hDy
    (mono5E8_table _ _ (by decide))⟩

/-- The finite case of 5E.9 (a): {lit}`k` pairwise commuting operators on a
finite-dimensional nonzero complex vector space have a common eigenvector.
By induction on {lit}`k`, generalizing over {lit}`V`. -/
private lemma exists_common_eigenvector_fin (k : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] [Finite ℂ V] [Nontrivial V]
      (E : Fin k → V →ₗ[ℂ] V), (∀ i j, Commute (E i) (E j)) →
      ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ γ : ℂ, E i v = γ • v := by
  induction k with
  | zero =>
    intro V _ _ _ _ E _
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨v, hv, fun i => i.elim0⟩
  | succ k ih =>
    intro V _ _ _ _ E hcomm
    -- take an eigenvector for one op S
    obtain ⟨lam, hlam⟩ := LADR.Section_5B.exists_eigenvalue (E 0)
    haveI hU : Nontrivial (Module.End.eigenspace (E 0) lam) := by
      obtain ⟨x, hx_ne, hx_eq⟩ := Module.End.hasEigenvalue_iff_exists.mp hlam
      exact ⟨⟨x, Module.End.mem_eigenspace_iff.mpr hx_eq⟩, 0,
        fun h => hx_ne (by simpa using congrArg Subtype.val h)⟩
    -- then restrict the other operators to the eigenspace
    have hinv : ∀ i, InvariantUnder (E i) (Module.End.eigenspace (E 0) lam) :=
      fun i => eigenspace_invariant_of_commute (E 0) (E i) (hcomm 0 i) lam
    have hcomm' : ∀ i j : Fin k,
        Commute (hinv i.succ).restrict (hinv j.succ).restrict := by
      intro i j
      show _ * _ = _ * _
      refine LinearMap.ext fun u => Subtype.ext ?_
      exact LinearMap.congr_fun (hcomm i.succ j.succ) (u : V)
    -- use induction to get a common eigenvector
    obtain ⟨u, hu, hEu⟩ := ih (fun i => (hinv i.succ).restrict) hcomm'
    have hu' : (u : V) ≠ 0 := fun h => hu (Subtype.ext h)
    refine ⟨u, hu', fun i => ?_⟩
    -- since we work in the eigenspace it is also eigenvector for the first op.
    induction i using Fin.cases with
    | zero => exact ⟨lam, Module.End.mem_eigenspace_iff.mp u.2⟩
    | succ i =>
      obtain ⟨γ, hγ⟩ := hEu i
      exact ⟨γ, by simpa using congrArg Subtype.val hγ⟩

/-- 5E.9 (a) For a (possibly infinite) family of pairwise commuting
operators on a finite-dimensional nonzero complex vector space, there is a
common eigenvector. -/
theorem exercise_5E_9a {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (𝒮 : Set (V →ₗ[ℂ] V))
    (hcomm : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, Commute S T) :
    ∃ v : V, v ≠ 0 ∧ ∀ S ∈ 𝒮, ∃ γ : ℂ, S v = γ • v := by
  -- for finite collections use induction on the size of S
  -- take an eigenvector for one op S
  -- then restrict the other operators to the eigenspace
  -- use induction to get a common eigenvector
  -- since we work in the eigenspace it is also eigenvector for the first op.
  -- (this is `exists_common_eigenvector_fin`)
  -- to complete for infiite S, notice that dim(L(V)) is finite
  -- take the span of S to a subspace of L(V)
  -- everything in it still commutes (because lin.combs of commuting are commuting)
  have hcommW : ∀ A ∈ Submodule.span ℂ 𝒮, ∀ B ∈ Submodule.span ℂ 𝒮, Commute A B := by
    intro A hA B hB
    induction hA using Submodule.span_induction with
    | mem A hA =>
      induction hB using Submodule.span_induction with
      | mem B hB => exact hcomm A hA B hB
      | zero => exact Commute.zero_right A
      | add B C _ _ hB hC => exact hB.add_right hC
      | smul c B _ hB => exact hB.smul_right c
    | zero => exact Commute.zero_left B
    | add A C _ _ hA hC => exact hA.add_left hC
    | smul c A _ hA => exact hA.smul_left c
  -- now take a basis of it and apply the finite case to get a common eigenvector
  obtain ⟨n, w, hw⟩ := exists_basis (F := ℂ) (V := Submodule.span ℂ 𝒮)
  obtain ⟨v, hv, hwv⟩ := exists_common_eigenvector_fin n
    (fun i => (w i : V →ₗ[ℂ] V)) fun i j => hcommW _ (w i).2 _ (w j).2
  -- it is eigenvector for all linear combinations of elements of S
  refine ⟨v, hv, fun S hS => ?_⟩
  have hSw : S ∈ Submodule.span ℂ (Set.range fun i => (w i : V →ₗ[ℂ] V)) := by
    have h : (⟨S, Submodule.subset_span hS⟩ : Submodule.span ℂ 𝒮) ∈
        Submodule.span ℂ (Set.range w) := hw.2 ▸ Submodule.mem_top
    have h' := Submodule.mem_map_of_mem (f := (Submodule.span ℂ 𝒮).subtype) h
    rwa [Submodule.map_span, ← Set.range_comp] at h'
  clear hS
  induction hSw using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨i, rfl⟩ := hA
    exact hwv i
  | zero => exact ⟨0, by simp⟩
  | add A B _ _ hA hB =>
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    exact ⟨a + b, by rw [LinearMap.add_apply, ha, hb, add_smul]⟩
  | smul c A _ hA =>
    obtain ⟨a, ha⟩ := hA
    exact ⟨c * a, by rw [LinearMap.smul_apply, ha, smul_smul]⟩

/-- The induction for 5E.9 (b): the proof of 5.80 for a whole commuting family,
with the common eigenvector supplied by 5E.9 (a). -/
private lemma simul_upperTriangular_family_aux (N : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] [Finite ℂ V], finrank ℂ V = N →
      ∀ 𝒮 : Set (V →ₗ[ℂ] V), (∀ S ∈ 𝒮, ∀ T ∈ 𝒮, Commute S T) →
      ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
        ∀ S ∈ 𝒮, IsUpperTriangular (matrixOf hv hv S) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ _ hV 𝒮 hcomm
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · -- {lit}`V = {0}`: the empty basis works.
      have hsub : Subsingleton V := by
        rw [← Module.finrank_zero_iff (R := ℂ)]
        exact hV
      refine ⟨0, Fin.elim0, ⟨linearIndependent_empty_type, ?_⟩, fun S _ j _ _ => j.elim0⟩
      show Submodule.span ℂ (Set.range Fin.elim0) = ⊤
      rw [Set.range_eq_empty, Submodule.span_empty, eq_top_iff]
      intro x _
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
    · have : Nontrivial V :=
        Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
      -- start with a common eigenvector {lit}`v₁` for the family (from (a))
      obtain ⟨v₁, hv₁_ne, hev⟩ := exercise_5E_9a 𝒮 hcomm
      set U : Submodule ℂ V := Submodule.span ℂ {v₁} with hU_def
      have hU_rank : finrank ℂ U = 1 := finrank_span_singleton hv₁_ne
      have hinv : ∀ S ∈ 𝒮, InvariantUnder S U := by
        intro S hS x hx
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        obtain ⟨γ, hγ⟩ := hev S hS
        rw [map_smul, hγ, smul_smul]
        exact Submodule.mem_span_singleton.mpr ⟨a * γ, rfl⟩
      -- {lit}`V = span(v₁) ⊕ W` (2.33) and {lit}`P : V → W` the projection.
      obtain ⟨W, hUW⟩ := LADR.Section_2B.exists_isCompl U
      set P : V →ₗ[ℂ] W := W.linearProjOfIsCompl U hUW.symm with hP_def
      have hPw : ∀ w : W, P w = w := W.linearProjOfIsCompl_apply_left hUW.symm
      have hPv₁ : P v₁ = 0 := W.linearProjOfIsCompl_apply_right' hUW.symm _
        (Submodule.mem_span_singleton_self v₁)
      have hdecomp : ∀ x : V, x - (P x : V) ∈ U := fun x =>
        (W.linearProjOfIsCompl_apply_eq_zero_iff hUW.symm).mp
          (by rw [map_sub, hPw, sub_self])
      have hPR : ∀ R : V →ₗ[ℂ] V, InvariantUnder R U → ∀ x, P (R (P x)) = P (R x) := by
        intro R hR x
        have h : R x - R (P x) ∈ U := by
          rw [← map_sub]
          exact hR _ (hdecomp x)
        rw [← sub_eq_zero, ← map_sub,
          W.linearProjOfIsCompl_apply_eq_zero_iff hUW.symm]
        rw [← neg_mem_iff, neg_sub]
        exact h
      -- the family {lit}`Ŝ = P S|_W` for {lit}`S ∈ 𝒮` still commutes
      let hat : (V →ₗ[ℂ] V) → (W →ₗ[ℂ] W) := fun R => P ∘ₗ R ∘ₗ W.subtype
      have hcomm_hat : ∀ A ∈ hat '' 𝒮, ∀ B ∈ hat '' 𝒮, Commute A B := by
        rintro _ ⟨S, hS, rfl⟩ _ ⟨T, hT, rfl⟩
        show hat S * hat T = hat T * hat S
        refine LinearMap.ext fun w => ?_
        show P (S (P (T w))) = P (T (P (S w)))
        rw [hPR S (hinv S hS), hPR T (hinv T hT)]
        exact congrArg P (LinearMap.congr_fun (hcomm S hS T hT) (w : V))
      have hW_rank : finrank ℂ W = N - 1 := by
        have := Submodule.finrank_add_eq_of_isCompl hUW
        omega
      -- by induction on the dimension, a basis {lit}`v₂, …, vₙ` of {lit}`W`
      -- makes every {lit}`Ŝ` upper triangular
      obtain ⟨M, wl, hwl, hA⟩ := ih (N - 1) (by omega) hW_rank (hat '' 𝒮) hcomm_hat
      set v : Fin (M + 1) → V := Fin.cons v₁ fun i => (wl i : V) with hv_def
      have hM : M = N - 1 := by
        rw [← hW_rank]
        exact isBasis_card_eq_finrank wl hwl
      have hv_li : LinearIndependent ℂ v := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hg' : g 0 • v₁ + ∑ i : Fin M, g i.succ • (wl i : V) = 0 := by
          rw [Fin.sum_univ_succ] at hg
          exact hg
        have hq : ∑ i : Fin M, g i.succ • wl i = 0 := by
          have h1 := congrArg P hg'
          rw [map_add, map_smul, hPv₁, smul_zero, zero_add, map_sum,
            map_zero] at h1
          rw [← h1]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hPw]
        have hzero_succ : ∀ i : Fin M, g i.succ = 0 :=
          Fintype.linearIndependent_iff.mp hwl.1 _ hq
        have hzero_0 : g 0 = 0 := by
          rw [Finset.sum_eq_zero (fun i _ => by
            rw [hzero_succ i, zero_smul]), add_zero] at hg'
          rcases smul_eq_zero.mp hg' with h | h
          · exact h
          · exact absurd h hv₁_ne
        intro j
        induction j using Fin.cases with
        | zero => exact hzero_0
        | succ i => exact hzero_succ i
      have hv_basis : IsBasis ℂ v :=
        isBasis_of_linearIndependent_of_card_eq v hv_li (by omega)
      -- the rest follows the proof of 5.80, for each {lit}`S ∈ 𝒮`
      refine ⟨M + 1, v, hv_basis, fun S hS => ?_⟩
      obtain ⟨γ, hγ⟩ := hev S hS
      apply ((tfae_upperTriangular hv_basis S).out 2 0).mp
      intro k
      induction k using Fin.cases with
      | zero =>
        have h0 : v 0 = v₁ := rfl
        rw [h0, hγ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, le_refl 0, h0⟩)
      | succ i =>
        have hq30 := (tfae_upperTriangular hwl (hat S)).out 0 2
        have hq3 := hq30.mp (hA (hat S) ⟨S, hS, rfl⟩) i
        have hsucc : v i.succ = wl i := rfl
        have hmem : S (wl i : V) ∈
            U ⊔ Submodule.span ℂ ((fun j => (wl j : V)) '' {j | j ≤ i}) := by
          rw [← sub_add_cancel (S (wl i : V)) (P (S (wl i : V)) : V)]
          refine Submodule.add_mem_sup (hdecomp _) ?_
          have h := Submodule.mem_map_of_mem (f := W.subtype) hq3
          rw [Submodule.map_span, ← Set.image_comp] at h
          exact h
        rw [hsucc]
        have hle : U ⊔ Submodule.span ℂ ((fun j => (wl j : V)) '' {j | j ≤ i}) ≤
            Submodule.span ℂ (v '' {j | j ≤ i.succ}) := by
          apply sup_le
          · rw [hU_def, Submodule.span_le]
            rintro x rfl
            exact Submodule.subset_span ⟨0, Fin.zero_le _, rfl⟩
          · rw [Submodule.span_le]
            rintro x ⟨j, hj, rfl⟩
            refine Submodule.subset_span ⟨j.succ, ?_, rfl⟩
            rw [Set.mem_setOf_eq]
            exact Fin.succ_le_succ_iff.mpr hj
        exact hle hmem

/-- 5E.9 (b) …and a basis with respect to which every member of the family
has an upper-triangular matrix. -/
theorem exercise_5E_9b {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (𝒮 : Set (V →ₗ[ℂ] V))
    (hcomm : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, Commute S T) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      ∀ S ∈ 𝒮, IsUpperTriangular (matrixOf hv hv S) := by
  -- similar to the two ops case, start with a common eigenvector v for the commuting family (from a)
  -- then operate on W where V = span(v) ⊕ W and use induction on the dimension of V
  -- the rest of the proof follows the two op version, equivalently.
  -- (this is `simul_upperTriangular_family_aux`)
  exact simul_upperTriangular_family_aux _ rfl 𝒮 hcomm

/-- For 5E.10: if the real {lit}`2 × 2` matrix {lit}`[a b; c d]` has an
eigenvalue, then its discriminant {lit}`(a - d)² + 4bc` is non-negative. -/
private lemma disc_nonneg_of_hasEigenvalue (a b c d γ : ℝ)
    (h : HasEigenvalue (Matrix.toLin' !![a, b; c, d]) γ) :
    0 ≤ (a - d) ^ 2 + 4 * b * c := by
  obtain ⟨v, hv, hγ⟩ := Module.End.hasEigenvalue_iff_exists.mp h
  have h0 := congrFun hγ 0
  have h1 := congrFun hγ 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  -- {lit}`det(A - γI) = 0`, since {lit}`(A - γI) v = 0` with {lit}`v ≠ 0`
  have hdet : (a - γ) * (d - γ) - b * c = 0 := by
    by_contra hne
    apply hv
    have hv0 : ((a - γ) * (d - γ) - b * c) * v 0 = 0 := by
      linear_combination (d - γ) * h0 - b * h1
    have hv1 : ((a - γ) * (d - γ) - b * c) * v 1 = 0 := by
      linear_combination (a - γ) * h1 - c * h0
    ext i
    fin_cases i
    · exact (mul_eq_zero.mp hv0).resolve_left hne
    · exact (mul_eq_zero.mp hv1).resolve_left hne
  have hsq : (a - d) ^ 2 + 4 * b * c = (2 * γ - a - d) ^ 2 := by
    linear_combination (-4) * hdet
  rw [hsq]
  positivity

/-- 5E.10 5.81 fails on real vector spaces. -/
theorem exercise_5E_10 :
    ∃ S T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), Commute S T ∧
      (∃ α : ℝ, HasEigenvalue (S + T) α ∧
        ¬ ∃ γ μ : ℝ, HasEigenvalue S γ ∧ HasEigenvalue T μ ∧
          α = γ + μ) ∧
      (∃ β : ℝ, HasEigenvalue (S ∘ₗ T) β ∧
        ¬ ∃ γ μ : ℝ, HasEigenvalue S γ ∧ HasEigenvalue T μ ∧
          β = γ * μ) := by
  -- (lemma) for a real 2x2 matrix [a b; c d ] it has eigenvalues
  -- iff the discriminant (a - d)^2 + 4bc is non-negative

  -- using that we can find some matrices that violate the inequality,
  -- but work when added or multiplied

  -- for addition S = [0 -1; 1 0] and T = [0 1; -1 0] (they commute, T = -S)
  -- have discriminant -4 < 0 so no eigenvalues over ℝ
  -- but S + T = 0 has eigenvalue 0
  have hS : ∀ γ, ¬ HasEigenvalue (Matrix.toLin' !![(0 : ℝ), -1; 1, 0]) γ := by
    intro γ h
    have := disc_nonneg_of_hasEigenvalue _ _ _ _ γ h
    norm_num at this
  refine ⟨Matrix.toLin' !![0, -1; 1, 0], Matrix.toLin' !![0, 1; -1, 0], ?_, ?_, ?_⟩
  · show _ * _ = _ * _
    refine LinearMap.ext fun v => funext fun i => ?_
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨0, Module.End.hasEigenvalue_iff_exists.mpr ⟨![1, 0], ?_, ?_⟩, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · ext i
      fin_cases i <;> simp
    · rintro ⟨γ, μ, hγ, -, -⟩
      exact hS γ hγ
  -- for multiplication the same S, T work: ST = -S² = I has eigenvalue 1
  · refine ⟨1, Module.End.hasEigenvalue_iff_exists.mpr ⟨![1, 0], ?_, ?_⟩, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · rintro ⟨γ, μ, hγ, -, -⟩
      exact hS γ hγ

end LADR.Section_5E
