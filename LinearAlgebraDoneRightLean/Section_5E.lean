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
  sorry

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
  sorry

/-- 5E.3 -/
theorem exercise_5E_3 (S T : V →ₗ[F] V) (hcomm : Commute S T)
    (p : Polynomial F) :
    InvariantUnder T (ker (aeval S p)) ∧
      InvariantUnder T (range (aeval S p)) := by
  sorry

/-- 5E.4 Prove or give a counterexample: if {lit}`A` is diagonal and
{lit}`B` is upper triangular (of the same size), then {lit}`A` and {lit}`B`
commute. Stated for real matrices of arbitrary (unspecified) size. -/
def exercise_5E_4 :
    Decidable (∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
      A.IsDiag → IsUpperTriangular B → Commute A B) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 5E.5 A pair of operators commutes iff their dual operators commute. -/
theorem exercise_5E_5 [Finite F V] (S T : V →ₗ[F] V) :
    Commute S T ↔ Commute S.dualMap T.dualMap := by
  sorry

/-- 5E.6 -/
theorem exercise_5E_6 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (S T : V →ₗ[ℂ] V)
    (hcomm : Commute S T) :
    ∃ α γ : ℂ,
      range (S - α • (LinearMap.id : V →ₗ[ℂ] V)) ⊔
        range (T - γ • (LinearMap.id : V →ₗ[ℂ] V)) ≠ ⊤ := by
  sorry

/-- 5E.7 If {lit}`S` is diagonalizable and {lit}`T` commutes with {lit}`S`,
then there is a basis with respect to which {lit}`S` is diagonal and
{lit}`T` is upper triangular. -/
theorem exercise_5E_7 {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (S T : V →ₗ[ℂ] V) (hS : IsDiagonalizable S)
    (hcomm : Commute S T) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      (matrixOf hv hv S).IsDiag ∧ IsUpperTriangular (matrixOf hv hv T) := by
  sorry

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
  sorry

/-- 5E.9 (a) For a (possibly infinite) family of pairwise commuting
operators on a finite-dimensional nonzero complex vector space, there is a
common eigenvector. -/
theorem exercise_5E_9a {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] [Nontrivial V] (𝒮 : Set (V →ₗ[ℂ] V))
    (hcomm : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, Commute S T) :
    ∃ v : V, v ≠ 0 ∧ ∀ S ∈ 𝒮, ∃ γ : ℂ, S v = γ • v := by
  sorry

/-- 5E.9 (b) …and a basis with respect to which every member of the family
has an upper-triangular matrix. -/
theorem exercise_5E_9b {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (𝒮 : Set (V →ₗ[ℂ] V))
    (hcomm : ∀ S ∈ 𝒮, ∀ T ∈ 𝒮, Commute S T) :
    ∃ (n : ℕ) (v : Fin n → V) (hv : IsBasis ℂ v),
      ∀ S ∈ 𝒮, IsUpperTriangular (matrixOf hv hv S) := by
  sorry

/-- 5E.10 5.81 fails on real vector spaces. -/
theorem exercise_5E_10 :
    ∃ S T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), Commute S T ∧
      (∃ α : ℝ, HasEigenvalue (S + T) α ∧
        ¬ ∃ γ μ : ℝ, HasEigenvalue S γ ∧ HasEigenvalue T μ ∧
          α = γ + μ) ∧
      (∃ β : ℝ, HasEigenvalue (S ∘ₗ T) β ∧
        ¬ ∃ γ μ : ℝ, HasEigenvalue S γ ∧ HasEigenvalue T μ ∧
          β = γ * μ) := by
  sorry

end LADR.Section_5E
