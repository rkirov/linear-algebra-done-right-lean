import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Complex.Basic
import Mathlib.Dynamics.Newton
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import LinearAlgebraDoneRightLean.Section_5D
import LinearAlgebraDoneRightLean.Section_8A
import LinearAlgebraDoneRightLean.Section_8B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 8C: Consequences of Generalized Eigenspace Decomposition
-/

namespace LADR.Section_8C

open LADR.Section_5A (InvariantUnder)
open Module.End (HasEigenvalue maxGenEigenspace)
open LinearMap (ker range)
open Module (Finite finrank)
open Polynomial (aeval X C derivative)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! # Square Roots of Operators -/

/-! Recall (Axler 7.36) that a *square root* of an operator {lit}`T ∈ ℒ(V)` is an
operator {lit}`R ∈ ℒ(V)` with {lit}`R² = T`. Every complex number has a square
root, but not every operator on a complex vector space does — for example
{lit}`T(z₁, z₂, z₃) = (z₂, z₃, 0)` on {lit}`ℂ³` has none (Exercise 1). The
noninvertibility of that operator is no accident: we build square roots first for
{lit}`I + N` with {lit}`N` nilpotent (8.39), then for every invertible operator
over {lit}`ℂ` (8.41). -/

/-! The algebraic core of 8.39, isolated in a commutative ring. If {lit}`2` is a
unit and {lit}`a` is nilpotent, then {lit}`1 + a` is a square. Axler finds the
square root as a truncated Taylor series {lit}`1 + a₁a + a₂a² + ⋯` (see 8.40);
we instead obtain it from Newton's method / Hensel's lemma
({name}`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`): the point
{lit}`1` is an approximate root of {lit}`X² − (1 + a)` (the value there is the
nilpotent {lit}`−a`) and the derivative {lit}`2` is a unit there, so Newton
iteration converges to an exact root. -/

theorem isSquare_one_add_of_isNilpotent {S : Type*} [CommRing S] (h2 : IsUnit (2 : S))
    {a : S} (ha : IsNilpotent a) : ∃ r : S, r ^ 2 = 1 + a := by
  set P : Polynomial S := X ^ 2 - C (1 + a) with hP
  have hval : aeval (1 : S) P = -a := by
    rw [hP]; simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply, one_pow]; ring
  have hnil : IsNilpotent (aeval (1 : S) P) := by rw [hval]; exact ha.neg
  have hder : aeval (1 : S) (derivative P) = 2 := by
    rw [hP]; simp only [Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_X_pow, sub_zero, map_mul, map_pow, Polynomial.aeval_C,
      Polynomial.aeval_X, Algebra.algebraMap_self_apply]; norm_num
  have hunit : IsUnit (aeval (1 : S) (derivative P)) := by rw [hder]; exact h2
  obtain ⟨r, ⟨-, hr⟩, -⟩ :=
    Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero hnil hunit
  refine ⟨r, ?_⟩
  have hexp : aeval r P = r ^ 2 - (1 + a) := by
    rw [hP]; simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply]
  rw [hexp] at hr
  exact sub_eq_zero.mp hr

/-! 8.39 Identity plus nilpotent has a square root.

Suppose {lit}`T ∈ ℒ(V)` is nilpotent. Then {lit}`I + T` has a square root. This
holds over any field in which {lit}`2` is invertible (in particular over
{lit}`ℝ` and {lit}`ℂ`, matching Axler's statement for real and complex vector
spaces). We reduce to {name}`isSquare_one_add_of_isNilpotent` by working inside
the commutative subalgebra {lit}`𝔽[T] = Algebra.adjoin F {T}` (all its elements
are polynomials in {lit}`T`, hence commute), whose {lit}`CommRing` structure is
the mathlib instance {lit}`Polynomial.instCommRingAdjoinSingleton`. -/

theorem isSquare_one_add_of_isNilpotent_End (T : V →ₗ[F] V) (h2 : IsUnit (2 : F))
    (hT : IsNilpotent T) : ∃ R : V →ₗ[F] V, R ^ 2 = 1 + T := by
  have hmem : T ∈ Algebra.adjoin F {T} := Algebra.self_mem_adjoin_singleton F T
  let t : Algebra.adjoin F {T} := ⟨T, hmem⟩
  have hnil : IsNilpotent t := by
    obtain ⟨k, hk⟩ := hT
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero, SubmonoidClass.coe_pow]
    exact hk
  have h2A : IsUnit (2 : Algebra.adjoin F {T}) := by
    have h := h2.map (algebraMap F (Algebra.adjoin F {T}))
    rwa [map_ofNat] at h
  obtain ⟨r, hr⟩ := isSquare_one_add_of_isNilpotent (a := t) h2A hnil
  refine ⟨(r : V →ₗ[F] V), ?_⟩
  have h := congrArg (Subalgebra.val (Algebra.adjoin F {T})) hr
  rw [map_pow, map_add, map_one, Subalgebra.val_apply, Subalgebra.val_apply] at h
  exact h

/-! 8.40 The Taylor series {lit}`√(1 + x) = 1 + a₁x + a₂x² + ⋯` used as
motivation for the construction in 8.39. It is a formal power-series identity
(the coefficients {lit}`a₁ = 1/2`, {lit}`a₂ = −1/8`, … are chosen so that the
square of the truncation matches {lit}`1 + x`); Axler explicitly does not prove
convergence and uses it only heuristically. It is not a theorem to formalize; our
proof of 8.39 above replaces it with Newton's method, which supplies the same
truncated-polynomial square root without reference to the series. -/

open DirectSum in
/-- Build an operator on {lit}`M` from operators on the summands of an internal direct
sum: the glued {lit}`g` acts as {lit}`f i` on each summand {lit}`A i`. -/
theorem glue_endo {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type*}
    [DecidableEq ι] (A : ι → Submodule R M) (hA : DirectSum.IsInternal A)
    (f : ∀ i, A i →ₗ[R] A i) :
    ∃ g : M →ₗ[R] M, ∀ i (x : A i), g (x : M) = (f i x : M) := by
  set e : (⨁ i, A i) ≃ₗ[R] M := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA with he
  set D : (⨁ i, A i) →ₗ[R] (⨁ i, A i) :=
    DirectSum.toModule R ι _ (fun i => (DirectSum.lof R ι (fun i => A i) i) ∘ₗ f i) with hD
  refine ⟨e.toLinearMap ∘ₗ D ∘ₗ e.symm.toLinearMap, fun i x => ?_⟩
  have hex : e.symm (x : M) = DirectSum.lof R ι (fun i => A i) i x := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.ofBijective_apply,
      DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  show e (D (e.symm (x : M))) = (f i x : M)
  rw [hex, hD, DirectSum.toModule_lof, LinearMap.comp_apply, he, LinearEquiv.ofBijective_apply,
    DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]

open DirectSum in
/-- If on each summand of an internal direct sum {lit}`f i ∘ f i` agrees with {lit}`T`, then
gluing the {lit}`f i` produces a square root of {lit}`T`. -/
theorem exists_sqComp_of_forall_restrict {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {ι : Type*} [DecidableEq ι] (A : ι → Submodule R M)
    (hA : DirectSum.IsInternal A) (T : M →ₗ[R] M) (f : ∀ i, A i →ₗ[R] A i)
    (hf : ∀ i (x : A i), (f i (f i x) : M) = T (x : M)) : ∃ R' : M →ₗ[R] M, R' ∘ₗ R' = T := by
  obtain ⟨g, hg⟩ := glue_endo A hA f
  refine ⟨g, ?_⟩
  set e : (⨁ i, A i) ≃ₗ[R] M := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hA with he
  have key : (g ∘ₗ g) ∘ₗ e.toLinearMap = T ∘ₗ e.toLinearMap := by
    refine DirectSum.linearMap_ext _ fun i => LinearMap.ext fun x => ?_
    have hei : e (DirectSum.lof R ι (fun i => A i) i x) = (x : M) := by
      rw [he, LinearEquiv.ofBijective_apply, DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hei]
    rw [hg i x, hg i (f i x)]
    exact hf i x
  ext v
  obtain ⟨w, rfl⟩ := e.surjective v
  exact LinearMap.congr_fun key w

/-- 8.41 Over {lit}`ℂ`, every invertible operator has a square root. Following Axler:
by the generalized eigenspace decomposition `V = ⊕ G(λₖ, T)`, on each `G(λₖ, T)`
one has `T = λₖ(I + Nₖ/λₖ)` with {lit}`Nₖ` nilpotent (`λₖ ≠ 0` since {lit}`T` is invertible),
so `√λₖ · √(I + Nₖ/λₖ)` (the scalar root exists over {lit}`ℂ`, the operator root by 8.39)
squares to the restriction; gluing these along the direct sum gives a square root
of {lit}`T`. -/
theorem exists_sqComp_of_bijective {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : Function.Bijective T) :
    ∃ R : V →ₗ[ℂ] V, R ∘ₗ R = T := by
  classical
  have hmaps : ∀ μ : ℂ, Set.MapsTo (T : Module.End ℂ V)
      (maxGenEigenspace T μ) (maxGenEigenspace T μ) :=
    fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hper : ∀ μ : ℂ, ∃ fμ : (maxGenEigenspace T μ) →ₗ[ℂ] (maxGenEigenspace T μ),
      fμ ∘ₗ fμ = T.restrict (hmaps μ) := by
    intro μ
    by_cases hb : maxGenEigenspace T μ = ⊥
    · haveI : Subsingleton (maxGenEigenspace T μ) := by rw [hb]; infer_instance
      exact ⟨0, Subsingleton.elim _ _⟩
    · have hμ : μ ≠ 0 := by
        rintro rfl
        apply hb
        rw [Submodule.eq_bot_iff]
        intro x hx
        rw [Module.End.mem_maxGenEigenspace] at hx
        obtain ⟨k, hk⟩ := hx
        simp only [zero_smul, sub_zero] at hk
        have hTk : Function.Injective ⇑((T : Module.End ℂ V) ^ k) := by
          rw [Module.End.coe_pow]; exact hT.injective.iterate k
        exact hTk (by rw [hk, map_zero])
      set hN := Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes (T : Module.End ℂ V) μ) μ with hNmaps
      set N : (maxGenEigenspace T μ) →ₗ[ℂ] (maxGenEigenspace T μ) :=
        ((T : Module.End ℂ V) - algebraMap ℂ (Module.End ℂ V) μ).restrict hN with hNval
      have hNnil : IsNilpotent N := LADR.Section_8B.isNilpotent_restrict_sub_algebraMap T μ
      obtain ⟨S, hS⟩ := isSquare_one_add_of_isNilpotent_End (μ⁻¹ • N)
        (isUnit_iff_ne_zero.mpr two_ne_zero) (hNnil.smul μ⁻¹)
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq μ (n := 2) (by norm_num)
      have hSc : S ∘ₗ S = 1 + μ⁻¹ • N := by rw [← Module.End.mul_eq_comp, ← pow_two]; exact hS
      have hTres : T.restrict (hmaps μ) = μ • 1 + N := by
        ext y
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
          Submodule.coe_add, Submodule.coe_smul, hNval, LinearMap.restrict_coe_apply,
          LinearMap.sub_apply, Module.algebraMap_end_apply]
        abel
      refine ⟨z • S, ?_⟩
      rw [hTres, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← pow_two, hz, hSc,
        smul_add, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  choose f hf using hper
  refine exists_sqComp_of_forall_restrict (fun μ : ℂ => maxGenEigenspace T μ)
    (LADR.Section_8B.isInternal_maxGenEigenspace T) T f (fun μ x => ?_)
  rw [← LinearMap.comp_apply, hf μ, LinearMap.restrict_coe_apply]

/-! Axler's closing remark: by imitating the same technique (using {lit}`k`-th
roots of {lit}`I + Tₖ/λₖ` and of the scalars {lit}`λₖ`) one shows that over
{lit}`ℂ` every invertible operator has a {lit}`k`-th root for each positive
integer {lit}`k`. The nilpotent building block generalizes cleanly: for any
field with {lit}`k` invertible, {lit}`I + T` has a {lit}`k`-th root — this is a
{lit}`k`-th-root analogue of 8.39, provable by the same Newton argument with
{lit}`Xᵏ − (1 + a)`. -/

/-! # Jordan Form -/

/-- Axler's Exercise 8A.2, the foundation of the Jordan-basis construction: if
{lit}`Tᵐ u = 0` but {lit}`Tᵐ⁻¹ u ≠ 0`, then the cyclic list {lit}`u, T u, …, Tᵐ⁻¹ u`
is linearly independent. -/
theorem cyclic_list_linearIndependent {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : W →ₗ[ℂ] W) (m : ℕ) (u : W) (hm : (T ^ m) u = 0) (hu : (T ^ (m - 1)) u ≠ 0) :
    LinearIndependent ℂ (fun j : Fin m => (T ^ (j : ℕ)) u) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hvanish : ∀ l, m ≤ l → (T ^ l) u = 0 := fun l hl => by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hl
    rw [add_comm, pow_add, Module.End.mul_apply, hm, map_zero]
  by_contra hne
  push Not at hne
  obtain ⟨j0, hj0⟩ := hne
  set s := Finset.univ.filter (fun j => c j ≠ 0) with hs
  have hsne : s.Nonempty := ⟨j0, by simp [hs, hj0]⟩
  set i := s.min' hsne with hidef
  have hci : c i ≠ 0 := by have := s.min'_mem hsne; simp [hs] at this; exact this
  have hmin' : ∀ j : Fin m, j < i → c j = 0 := fun j hji => by
    by_contra hcj
    exact absurd (s.min'_le j (by simp [hs, hcj])) (not_le.mpr hji)
  have key := congrArg (T ^ (m - 1 - (i : ℕ))) hc
  rw [map_sum, map_zero, Finset.sum_eq_single i] at key
  · rw [map_smul, ← Module.End.mul_apply, ← pow_add,
      Nat.sub_add_cancel (by omega : (i : ℕ) ≤ m - 1)] at key
    rcases smul_eq_zero.mp key with h | h
    · exact hci h
    · exact hu h
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · rw [hmin' j hlt, zero_smul, map_zero]
    · rw [map_smul, ← Module.End.mul_apply, ← pow_add, hvanish _ (by omega), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

section JordanBasis

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Axler's decomposition step for a nilpotent operator. If {lit}`T ^ m = 0` and
{lit}`T ^ (m-1) u ≠ 0`, then the cyclic subspace {lit}`U = span {u, Tu, …, Tᵐ⁻¹u}`
has a {lit}`T`-invariant complement {lit}`W`, with {lit}`dim W + m = dim V`. This is
the heart of the induction proving 8.45: {lit}`U` is a single Jordan block and {lit}`W` is
handled by the inductive hypothesis. -/
theorem nilpotent_cyclic_hasCompl (T : V →ₗ[ℂ] V) (m : ℕ) (hm0 : 0 < m) (u : V)
    (hmop : (T ^ m : V →ₗ[ℂ] V) = 0) (hu : (T ^ (m - 1)) u ≠ 0) :
    ∃ W : Submodule ℂ V, (∀ x ∈ W, T x ∈ W) ∧
      IsCompl (Submodule.span ℂ (Set.range (fun j : Fin m => (T ^ (j : ℕ)) u))) W ∧
      finrank ℂ W + m = finrank ℂ V := by
  classical
  set g : Fin m → V := fun j => (T ^ (j : ℕ)) u with hg
  set U := Submodule.span ℂ (Set.range g) with hU
  have hvanish : ∀ l, m ≤ l → (T ^ l : V →ₗ[ℂ] V) = 0 := fun l hl => by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hl
    rw [add_comm, pow_add, hmop, mul_zero]
  have hUinv : ∀ x ∈ U, T x ∈ U := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨j, rfl⟩
      by_cases hj : (j : ℕ) + 1 < m
      · refine Submodule.subset_span ⟨⟨(j : ℕ) + 1, hj⟩, ?_⟩
        simp only [hg]
        rw [← Module.End.mul_apply, ← pow_succ']
      · have : (j : ℕ) + 1 = m := by omega
        have : T (g j) = 0 := by
          simp only [hg]
          rw [← Module.End.mul_apply, ← pow_succ', this, hmop, LinearMap.zero_apply]
        rw [this]; exact Submodule.zero_mem _
    · simp
    · intro y z _ _ hy hz; rw [map_add]; exact Submodule.add_mem _ hy hz
    · intro a y _ hy; rw [map_smul]; exact Submodule.smul_mem _ _ hy
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ V, φ ((T ^ (m - 1)) u) ≠ 0 := by
    by_contra h; push Not at h
    exact hu ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp h)
  set S : V →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi (fun k : Fin m => φ ∘ₗ (T ^ (k : ℕ))) with hS
  have hSapp : ∀ (x : V) (k : Fin m), S x k = φ ((T ^ (k : ℕ)) x) := by
    intro x k; simp [hS, LinearMap.pi_apply]
  set W := ker S with hW
  have hWinv : ∀ x ∈ W, T x ∈ W := by
    intro x hx
    rw [hW, LinearMap.mem_ker] at hx ⊢
    funext k
    rw [Pi.zero_apply, hSapp]
    have hxk : ∀ j : Fin m, φ ((T ^ (j : ℕ)) x) = 0 := fun j => by
      simpa [hSapp] using congrFun hx j
    have hTk : (T ^ (k : ℕ)) (T x) = (T ^ ((k : ℕ) + 1)) x := by
      rw [← Module.End.mul_apply, ← pow_succ]
    rw [hTk]
    by_cases hk : (k : ℕ) + 1 < m
    · exact hxk ⟨(k : ℕ) + 1, hk⟩
    · have hkm : (k : ℕ) + 1 = m := by omega
      rw [hkm, hvanish m le_rfl, LinearMap.zero_apply, map_zero]
  have hmu : (T ^ m) u = 0 := by rw [hmop, LinearMap.zero_apply]
  have hgLI : LinearIndependent ℂ g := cyclic_list_linearIndependent T m u hmu hu
  have hfU : finrank ℂ U = m := by rw [hU, finrank_span_eq_card hgLI]; simp
  have hdisj : Disjoint U W := by
    rw [Submodule.disjoint_def]
    intro x hxU hxW
    rw [hW, LinearMap.mem_ker] at hxW
    have hSx : ∀ k : Fin m, φ ((T ^ (k : ℕ)) x) = 0 := fun k => by
      simpa [hSapp] using congrFun hxW k
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hxU
    by_contra hx0
    have hne : ∃ j : Fin m, c j ≠ 0 := by
      by_contra h; push Not at h
      exact hx0 (by rw [← hc]; simp [h])
    set sset := Finset.univ.filter (fun j : Fin m => c j ≠ 0) with hsset
    have hsne : sset.Nonempty := by
      obtain ⟨j, hj⟩ := hne; exact ⟨j, by simp [hsset, hj]⟩
    set i := sset.min' hsne with hidef
    have hilt : (i : ℕ) < m := i.isLt
    have hci : c i ≠ 0 := by have := sset.min'_mem hsne; simp [hsset] at this; exact this
    have hmin' : ∀ j : Fin m, j < i → c j = 0 := fun j hji => by
      by_contra hcj
      exact absurd (sset.min'_le j (by simp [hsset, hcj])) (not_le.mpr hji)
    have key : φ ((T ^ (m - 1 - (i : ℕ))) x) = c i * φ ((T ^ (m - 1)) u) := by
      rw [← hc, map_sum, map_sum, Finset.sum_eq_single i]
      · simp only [hg]
        rw [map_smul, map_smul, smul_eq_mul]
        congr 1
        rw [← Module.End.mul_apply, ← pow_add]
        have : m - 1 - (i : ℕ) + (i : ℕ) = m - 1 := by omega
        rw [this]
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hlt | hgt
        · rw [hmin' j hlt]; simp
        · simp only [hg]
          rw [map_smul, map_smul, smul_eq_mul, ← Module.End.mul_apply, ← pow_add,
            hvanish _ (by omega : m ≤ m - 1 - (i : ℕ) + (j : ℕ))]
          simp
      · intro h; exact absurd (Finset.mem_univ i) h
    have hzero : φ ((T ^ (m - 1 - (i : ℕ))) x) = 0 := hSx ⟨m - 1 - (i : ℕ), by omega⟩
    rw [key] at hzero
    rcases mul_eq_zero.mp hzero with h | h
    · exact hci h
    · exact hφ h
  have hrn : finrank ℂ (range S) + finrank ℂ W = finrank ℂ V := by
    rw [hW]; exact LinearMap.finrank_range_add_finrank_ker S
  have hrangele : finrank ℂ (range S) ≤ m := by
    calc finrank ℂ (range S) ≤ finrank ℂ (Fin m → ℂ) := Submodule.finrank_le _
      _ = m := by rw [Module.finrank_pi]; simp
  have hinf0 : finrank ℂ ↥(U ⊓ W) = 0 := by rw [disjoint_iff.mp hdisj]; simp
  have hsup : finrank ℂ ↥(U ⊔ W) = m + finrank ℂ W := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hinf0, hfU] at this; omega
  have hsuple : finrank ℂ ↥(U ⊔ W) ≤ finrank ℂ V := Submodule.finrank_le _
  have hsupeq : finrank ℂ ↥(U ⊔ W) = finrank ℂ V := by omega
  have hcodisj : Codisjoint U W := by
    rw [codisjoint_iff]; exact Submodule.eq_top_of_finrank_eq hsupeq
  exact ⟨W, hWinv, ⟨hdisj, hcodisj⟩, by omega⟩

omit [FiniteDimensional ℂ V] in
/-- Coercion commutes with powers of a restricted operator:
{lit}`↑((T.restrict h) ^ k x) = (T ^ k) ↑x`. -/
theorem coe_restrict_pow {W : Submodule ℂ V} (T : V →ₗ[ℂ] V) (h : ∀ x ∈ W, T x ∈ W) :
    ∀ (k : ℕ) (x : ↥W), (((T.restrict h) ^ k) x : V) = (T ^ k) (x : V) := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply,
      LinearMap.restrict_coe_apply]

/-- A *Jordan basis* for a nilpotent {lit}`T`, stated matrix-free: a finite family
of cyclic chains {lit}`(v i, T (v i), …, Tᴹ⁻¹ (v i))` that together form a basis of
{lit}`V`, with {lit}`Tᴹ (v i) = 0` ending each chain. In the matrix of {lit}`T` with
respect to the concatenated basis this is exactly the block-diagonal nilpotent
Jordan form (8.44): each chain contributes one block with {lit}`1`'s on the
superdiagonal and {lit}`0`'s elsewhere. -/
def HasNilpotentJordanBasis (T : V →ₗ[ℂ] V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (M : ι → ℕ) (v : ι → V),
    (∀ i, 0 < M i) ∧ (∀ i, (T ^ (M i)) (v i) = 0) ∧
    LinearIndependent ℂ (fun p : Σ i, Fin (M i) => (T ^ (p.2 : ℕ)) (v p.1)) ∧
    Submodule.span ℂ (Set.range (fun p : Σ i, Fin (M i) => (T ^ (p.2 : ℕ)) (v p.1))) = ⊤

set_option maxHeartbeats 800000 in
omit [FiniteDimensional ℂ V] in
/-- The gluing step of Axler's Jordan induction: a cyclic block for {lit}`u`
together with a Jordan basis of a {lit}`T`-invariant complement {lit}`W` assemble
into a Jordan basis of the whole space. -/
theorem jordan_glue (T : V →ₗ[ℂ] V) (m : ℕ) (hm0 : 0 < m) (u : V)
    (hmop : (T ^ m : V →ₗ[ℂ] V) = 0) (hu : (T ^ (m - 1)) u ≠ 0)
    {W : Submodule ℂ V} (hWinv : ∀ x ∈ W, T x ∈ W)
    (hcompl : IsCompl (Submodule.span ℂ (Set.range (fun j : Fin m => (T ^ (j : ℕ)) u))) W)
    {ιW : Type} [Fintype ιW] (MW : ιW → ℕ) (vW : ιW → ↥W)
    (hMWpos : ∀ i, 0 < MW i)
    (hMWkill : ∀ i, ((T.restrict hWinv) ^ (MW i)) (vW i) = 0)
    (hLIW : LinearIndependent ℂ
      (fun p : Σ i, Fin (MW i) => ((T.restrict hWinv) ^ (p.2 : ℕ)) (vW p.1)))
    (hspanW : Submodule.span ℂ (Set.range
      (fun p : Σ i, Fin (MW i) => ((T.restrict hWinv) ^ (p.2 : ℕ)) (vW p.1))) = ⊤) :
    HasNilpotentJordanBasis T := by
  set g : Fin m → V := fun j => (T ^ (j : ℕ)) u with hg
  have hgLI : LinearIndependent ℂ g :=
    cyclic_list_linearIndependent T m u (by rw [hmop, LinearMap.zero_apply]) hu
  set gU : (Σ _ : Unit, Fin m) → V := fun p => (T ^ (p.2 : ℕ)) u with hgU
  set hWfam : (Σ i : ιW, Fin (MW i)) → V := fun p => (T ^ (p.2 : ℕ)) ↑(vW p.1) with hWf
  set wfam : (Σ i : ιW, Fin (MW i)) → ↥W :=
    fun p => ((T.restrict hWinv) ^ (p.2 : ℕ)) (vW p.1) with hwfam
  have hWfam_eq : hWfam = (W.subtype : ↥W →ₗ[ℂ] V) ∘ wfam := by
    funext p; show (T ^ (p.2 : ℕ)) ↑(vW p.1) = ↑(wfam p)
    rw [hwfam, coe_restrict_pow T hWinv]
  have hspanhW : Submodule.span ℂ (Set.range hWfam) = W := by
    rw [hWfam_eq, Set.range_comp, Submodule.span_image, hspanW, Submodule.map_top,
      Submodule.range_subtype]
  have hrangeU : Set.range gU = Set.range g := by
    ext x; constructor
    · rintro ⟨p, rfl⟩; exact ⟨p.2, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨⟨(), j⟩, rfl⟩
  have hLIgU : LinearIndependent ℂ gU := by
    show LinearIndependent ℂ (g ∘ (fun p : Σ _ : Unit, Fin m => p.2))
    exact hgLI.comp _ (by rintro ⟨⟨⟩, j⟩ ⟨⟨⟩, k⟩ h; simpa using h)
  have hLIhW : LinearIndependent ℂ hWfam := by
    rw [hWfam_eq]; exact hLIW.map' W.subtype (Submodule.ker_subtype W)
  have hdisjspan : Disjoint (Submodule.span ℂ (Set.range gU))
      (Submodule.span ℂ (Set.range hWfam)) := by
    rw [hrangeU, hspanhW]; exact hcompl.disjoint
  set e := Equiv.sumSigmaDistrib
    (fun o : Unit ⊕ ιW => Fin (Sum.elim (fun _ => m) MW o)) with he
  have hFeq : (fun p : Σ o : Unit ⊕ ιW, Fin (Sum.elim (fun _ => m) MW o) =>
      (T ^ (p.2 : ℕ)) (Sum.elim (fun _ => u) (fun i => (vW i : V)) p.1))
      = Sum.elim gU hWfam ∘ e := by
    funext p; obtain ⟨o, j⟩ := p; cases o with
    | inl a => cases a; rfl
    | inr i => rfl
  refine ⟨Unit ⊕ ιW, inferInstance, Sum.elim (fun _ => m) MW,
    Sum.elim (fun _ => u) (fun i => (vW i : V)), ?_, ?_, ?_, ?_⟩
  · rintro (_ | i)
    · exact hm0
    · exact hMWpos i
  · rintro (⟨⟩ | i)
    · show (T ^ m) u = 0; rw [hmop, LinearMap.zero_apply]
    · show (T ^ (MW i)) ↑(vW i) = 0
      rw [← coe_restrict_pow T hWinv (MW i) (vW i), hMWkill i, Submodule.coe_zero]
  · rw [hFeq]
    exact (LinearIndependent.sum_type hLIgU hLIhW hdisjspan).comp e e.injective
  · have hre : Set.range (Sum.elim gU hWfam ∘ ⇑e) = Set.range (Sum.elim gU hWfam) := by
      ext y; simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨e x, rfl⟩
      · rintro ⟨z, rfl⟩; obtain ⟨x, rfl⟩ := e.surjective z; exact ⟨x, rfl⟩
    rw [hFeq, hre, Set.Sum.elim_range, Submodule.span_union, hrangeU, hspanhW]
    exact hcompl.sup_eq_top

set_option maxHeartbeats 800000 in
/-! **8.45** Every nilpotent operator on a finite-dimensional complex vector space
has a Jordan basis. Axler's proof is by induction on {lit}`dim V`: choosing {lit}`m`
minimal with {lit}`Tᵐ = 0` and {lit}`u` with {lit}`Tᵐ⁻¹u ≠ 0`, the cyclic subspace
{lit}`U = span{u, …, Tᵐ⁻¹u}` is a single Jordan block with a {lit}`T`-invariant
complement {lit}`W` ({name}`LADR.Section_8C.nilpotent_cyclic_hasCompl`); applying the
inductive hypothesis to {lit}`W` and concatenating the chains
({name}`LADR.Section_8C.jordan_glue`) gives a Jordan basis of {lit}`V`. We state the
conclusion matrix-free as {name}`LADR.Section_8C.HasNilpotentJordanBasis` (8.44). -/
theorem hasNilpotentJordanBasis (T : V →ₗ[ℂ] V) (hT : IsNilpotent T) :
    HasNilpotentJordanBasis T := by
  suffices H : ∀ (n : ℕ), ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (T : V →ₗ[ℂ] V), finrank ℂ V = n → IsNilpotent T → HasNilpotentJordanBasis T by
    exact H (finrank ℂ V) T rfl hT
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro V _ _ _ T hdim hnil
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      haveI : Subsingleton V := Module.finrank_zero_iff.mp hdim
      refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun i => i.elim, fun i => i.elim,
        ?_, ?_⟩
      · haveI : IsEmpty (Σ i : Empty, Fin ((Empty.elim : Empty → ℕ) i)) := ⟨fun p => p.1.elim⟩
        exact linearIndependent_empty_type
      · rw [eq_top_iff]; intro x _; rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _
    · classical
      have hex : ∃ k, (T ^ k : V →ₗ[ℂ] V) = 0 := hnil
      set m := Nat.find hex with hm
      have hmop : (T ^ m : V →ₗ[ℂ] V) = 0 := Nat.find_spec hex
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exfalso
          rw [h, pow_zero] at hmop
          have hall : ∀ x : V, x = 0 := fun x => by
            have := LinearMap.congr_fun hmop x; simpa using this
          haveI : Subsingleton V := ⟨fun a b => by rw [hall a, hall b]⟩
          rw [show finrank ℂ V = 0 from Module.finrank_zero_iff.mpr this] at hdim; omega
        · exact h
      have hm1 : (T ^ (m - 1) : V →ₗ[ℂ] V) ≠ 0 :=
        Nat.find_min hex (by rw [← hm]; omega)
      obtain ⟨u, hu⟩ : ∃ u, (T ^ (m - 1)) u ≠ 0 := by
        by_contra h; push Not at h; exact hm1 (LinearMap.ext h)
      obtain ⟨W, hWinv, hcompl, hdimW⟩ := nilpotent_cyclic_hasCompl T m hm0 u hmop hu
      have hWlt : finrank ℂ ↥W < n := by rw [← hdim]; omega
      have hTW : IsNilpotent (T.restrict hWinv) := Module.End.isNilpotent.restrict hWinv hnil
      obtain ⟨ιW, instW, MW, vW, hMWpos, hMWkill, hLIW, hspanW⟩ :=
        IH (finrank ℂ ↥W) hWlt (T.restrict hWinv) rfl hTW
      exact jordan_glue T m hm0 u hmop hu hWinv hcompl MW vW hMWpos hMWkill hLIW hspanW

/-- A *Jordan basis* for {lit}`T` (8.44), stated matrix-free: a finite family of
eigenvalue chains {lit}`(v i, (T − λᵢ)(v i), …)` that together form a basis of
{lit}`V`, with {lit}`(T − λᵢ)ᴹ (v i) = 0` ending each chain. In the concatenated
basis this is exactly the block-diagonal Jordan form — one block per chain, with
eigenvalue {lit}`λᵢ` on the diagonal and {lit}`1`'s directly above it. -/
def HasJordanBasis (T : V →ₗ[ℂ] V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (M : ι → ℕ) (lam : ι → ℂ) (v : ι → V),
    (∀ i, 0 < M i) ∧ (∀ i, ((T - lam i • 1) ^ (M i)) (v i) = 0) ∧
    LinearIndependent ℂ
      (fun p : Σ i, Fin (M i) => ((T - lam p.1 • 1) ^ (p.2 : ℕ)) (v p.1)) ∧
    Submodule.span ℂ (Set.range
      (fun p : Σ i, Fin (M i) => ((T - lam p.1 • 1) ^ (p.2 : ℕ)) (v p.1))) = ⊤

set_option maxHeartbeats 800000 in
/-- **8.46** Every operator on a finite-dimensional complex vector space has a
Jordan basis. Axler's proof applies the nilpotent case 8.45 to each
{lit}`(T − λ)|_{G(λ,T)}` (nilpotent by
{name}`LADR.Section_8B.isNilpotent_restrict_sub_algebraMap`) and assembles the
per-eigenspace bases along the generalized eigenspace decomposition
({name}`LADR.Section_8B.isInternal_maxGenEigenspace`), via
{name}`DirectSum.IsInternal.collectedBasis`; {name}`LADR.Section_8C.coe_restrict_pow`
turns each nilpotent chain into a genuine {lit}`λ`-eigenvalue Jordan chain. -/
theorem hasJordanBasis (T : V →ₗ[ℂ] V) : HasJordanBasis T := by
  classical
  have hInt := LADR.Section_8B.isInternal_maxGenEigenspace T
  set A : ℂ → Submodule ℂ V := fun μ => maxGenEigenspace T μ with hA
  have hmaps : ∀ μ : ℂ,
      Set.MapsTo ((T : Module.End ℂ V) - algebraMap ℂ (Module.End ℂ V) μ) (A μ) (A μ) :=
    fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm
      (Algebra.mul_sub_algebraMap_commutes T μ) μ
  set N : ∀ μ : ℂ, ↥(A μ) →ₗ[ℂ] ↥(A μ) :=
    fun μ => ((T : Module.End ℂ V) - algebraMap ℂ (Module.End ℂ V) μ).restrict (hmaps μ) with hNdef
  have hNnil : ∀ μ, IsNilpotent (N μ) :=
    fun μ => LADR.Section_8B.isNilpotent_restrict_sub_algebraMap T μ
  have hJB : ∀ μ, ∃ (ιμ : Type) (_ : Fintype ιμ) (Mμ : ιμ → ℕ) (vμ : ιμ → ↥(A μ)),
      (∀ i, 0 < Mμ i) ∧ (∀ i, (N μ ^ Mμ i) (vμ i) = 0) ∧
      LinearIndependent ℂ (fun p : Σ i, Fin (Mμ i) => (N μ ^ (p.2 : ℕ)) (vμ p.1)) ∧
      Submodule.span ℂ (Set.range
        (fun p : Σ i, Fin (Mμ i) => (N μ ^ (p.2 : ℕ)) (vμ p.1))) = ⊤ :=
    fun μ => hasNilpotentJordanBasis (N μ) (hNnil μ)
  choose ιμ instμ Mμ vμ hposμ hkillμ hLIμ hspanμ using hJB
  haveI : ∀ μ, Fintype (ιμ μ) := instμ
  set bμ : ∀ μ, Module.Basis (Σ i : ιμ μ, Fin (Mμ μ i)) ℂ ↥(A μ) :=
    fun μ => Module.Basis.mk (hLIμ μ) (hspanμ μ).ge with hbμ
  set B := hInt.collectedBasis bμ with hB
  set e := Equiv.sigmaAssoc (fun (μ : ℂ) (i : ιμ μ) => Fin (Mμ μ i)) with he
  haveI hFin : Fintype ((μ : ℂ) × (i : ιμ μ) × Fin (Mμ μ i)) :=
    FiniteDimensional.fintypeBasisIndex B
  haveI : Fintype (Σ μ : ℂ, ιμ μ) :=
    Fintype.ofSurjective (fun p : (μ : ℂ) × (i : ιμ μ) × Fin (Mμ μ i) => (⟨p.1, p.2.1⟩ : Σ μ, ιμ μ))
      (by rintro ⟨μ, i⟩; exact ⟨⟨μ, i, ⟨0, hposμ μ i⟩⟩, rfl⟩)
  have hbridge : ∀ (μ : ℂ) (i : ιμ μ) (j : ℕ),
      ((T - μ • 1) ^ j) (↑(vμ μ i) : V) = ↑((N μ ^ j) (vμ μ i)) := by
    intro μ i j
    rw [hNdef, coe_restrict_pow, Algebra.algebraMap_eq_smul_one]
  have hFeq : (fun p : Σ a : Σ μ : ℂ, ιμ μ, Fin (Mμ a.1 a.2) =>
      ((T - p.1.1 • 1) ^ (p.2 : ℕ)) (↑(vμ p.1.1 p.1.2) : V))
      = ⇑B ∘ e := by
    funext p; obtain ⟨⟨μ, i⟩, j⟩ := p
    rw [hB, DirectSum.IsInternal.collectedBasis_coe]
    show ((T - μ • 1) ^ (j : ℕ)) (↑(vμ μ i) : V) = ↑(bμ μ ⟨i, j⟩)
    rw [hbμ, Module.Basis.mk_apply, hbridge]
  refine ⟨Σ μ : ℂ, ιμ μ, inferInstance, fun a => Mμ a.1 a.2, fun a => a.1,
    fun a => (↑(vμ a.1 a.2) : V), ?_, ?_, ?_, ?_⟩
  · rintro ⟨μ, i⟩; exact hposμ μ i
  · rintro ⟨μ, i⟩
    show ((T - μ • 1) ^ (Mμ μ i)) (↑(vμ μ i) : V) = 0
    rw [hbridge, hkillμ μ i, Submodule.coe_zero]
  · rw [hFeq]; exact B.linearIndependent.comp e e.injective
  · have hre : Set.range (⇑B ∘ ⇑e) = Set.range ⇑B := by
      ext y; simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨e x, rfl⟩
      · rintro ⟨z, rfl⟩; obtain ⟨x, rfl⟩ := e.surjective z; exact ⟨x, rfl⟩
    rw [hFeq, hre, Module.Basis.span_eq]

end JordanBasis

/-! For every {lit}`T ∈ ℒ(V)` over {lit}`ℂ` there is a basis giving a "nice"
upper-triangular matrix (8.37); the Jordan form does better, producing a matrix
that is {lit}`0` except on the diagonal and the line directly above it. The
constructions and definitions in this subsection (8.44–8.46) are phrased by Axler
in terms of the matrix {lit}`ℳ(T, basis)` of an operator with respect to a basis.
We instead encode them by their eigenvalue chains
({name}`LADR.Section_8C.HasJordanBasis`), which carries the same content without
committing to a block layout, and prove 8.45 and 8.46 in that form. We also record
the two motivating nilpotent examples (8.42, 8.43). -/

/-! 8.42 Example: nilpotent operator with nice matrix.

{lit}`T(z₁, z₂, z₃, z₄) = (0, z₁, z₂, z₃)` on {lit}`ℂ⁴` satisfies {lit}`T⁴ = 0`,
so {lit}`T` is nilpotent. For {lit}`v = (1, 0, 0, 0)` the list
{lit}`T³v, T²v, Tv, v` is a basis (a single Jordan block); its matrix has
{lit}`1`'s on the superdiagonal and {lit}`0`'s elsewhere. We record the operator
and prove {lit}`T⁴ = 0`. -/

def T_8_42 : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun v := ![0, v 0, v 1, v 2]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

theorem T_8_42_isNilpotent : IsNilpotent T_8_42 := by
  refine ⟨4, ?_⟩
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [pow_succ, Module.End.mul_apply, T_8_42]

/-! 8.43 Example: nilpotent operator with a slightly more complicated matrix.

{lit}`T(z₁, …, z₆) = (0, z₁, z₂, 0, z₄, 0)` on {lit}`ℂ⁶` satisfies {lit}`T³ = 0`.
Unlike 8.42 there is no single vector {lit}`v` with {lit}`T⁵v, …, v` a basis;
instead {lit}`v₁ = e₁, v₂ = e₄, v₃ = e₆` give the Jordan basis
{lit}`T²v₁, Tv₁, v₁, Tv₂, v₂, v₃`, whose matrix is block diagonal with a
{lit}`3`-by-{lit}`3`, a {lit}`2`-by-{lit}`2`, and a {lit}`1`-by-{lit}`1` nilpotent
Jordan block. We record the operator and prove {lit}`T³ = 0`. -/

def T_8_43 : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) where
  toFun v := ![0, v 0, v 1, 0, v 3, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

theorem T_8_43_isNilpotent : IsNilpotent T_8_43 := by
  refine ⟨3, ?_⟩
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;> simp [pow_succ, Module.End.mul_apply, T_8_43]

/-! 8.44 Definition: Jordan basis.

A basis of {lit}`V` is a *Jordan basis* for {lit}`T` if the matrix of {lit}`T`
with respect to it is block diagonal with each block {lit}`Aₖ` upper triangular,
having a single eigenvalue {lit}`λₖ` on its diagonal, {lit}`1`'s on the line
directly above the diagonal, and {lit}`0`'s elsewhere. As with the block-diagonal
definition 8.35, this is a statement about {lit}`ℳ(T, basis)`, which is not
developed here; the condition is instead captured matrix-free by
{name}`LADR.Section_8C.HasJordanBasis` (and, in the nilpotent all-{lit}`λₖ = 0`
case, {name}`LADR.Section_8C.HasNilpotentJordanBasis`), whose eigenvalue chains
are exactly the Jordan blocks. -/

/-! 8.45 Every nilpotent operator has a Jordan basis.

**Proved** above as {name}`LADR.Section_8C.hasNilpotentJordanBasis`, following
Axler's induction on {lit}`dim V` (see
{name}`LADR.Section_8C.nilpotent_cyclic_hasCompl` for the cyclic-block/complement
splitting and {name}`LADR.Section_8C.jordan_glue` for the assembly of the chains).
The conclusion is stated matrix-free via
{name}`LADR.Section_8C.HasNilpotentJordanBasis` (8.44). -/

/-! 8.46 Jordan form.

**Proved** above as {name}`LADR.Section_8C.hasJordanBasis`, following Axler:
apply the nilpotent case 8.45 to each nilpotent {lit}`(T − λₖI)|_{G(λₖ,T)}` and
glue the per-eigenspace bases across the generalized eigenspace decomposition
({name}`LADR.Section_8B.isInternal_maxGenEigenspace`) with
{name}`DirectSum.IsInternal.collectedBasis`. The conclusion is stated matrix-free
via {name}`LADR.Section_8C.HasJordanBasis` (8.44): a family of eigenvalue chains
{lit}`(v i, (T − λᵢ)(v i), …)` that together form a basis. -/

/-! The closest formally available analogue is the **Jordan–Chevalley–Dunford
decomposition**: over {lit}`ℂ` (indeed any perfect field) every operator on a
finite-dimensional space is a sum {lit}`T = N + S` of a nilpotent operator and a
semisimple operator, both polynomials in {lit}`T`. This is mathlib's
{name}`Module.End.exists_isNilpotent_isSemisimple`. Over {lit}`ℂ` "semisimple"
coincides with "diagonalizable", so this is the additive counterpart of the
Jordan form (each Jordan block splits as its diagonal part plus its nilpotent
superdiagonal part). We record it as a proved consequence. -/

theorem exists_isNilpotent_isSemisimple {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Finite ℂ V] (T : V →ₗ[ℂ] V) :
    ∃ N S : V →ₗ[ℂ] V, IsNilpotent N ∧ Module.End.IsSemisimple S ∧ T = N + S := by
  obtain ⟨n, -, s, -, hn, hs, hT⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := T)
  exact ⟨n, s, hn, hs, hT⟩

/-! # Exercises -/

/-- 8C.1 {lit}`T(z₁, z₂, z₃) = (z₂, z₃, 0)` on {lit}`ℂ³` has no square root. -/
def T_ex_8C_1 : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) where
  toFun v := ![v 1, v 2, 0]
  map_add' x y := by funext i; fin_cases i <;> simp
  map_smul' a x := by funext i; fin_cases i <;> simp

theorem exercise_8C_1 : ¬ ∃ R : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ), R ^ 2 = T_ex_8C_1 := by
  sorry

/-- 8C.2 {lit}`T(x₁, …, x₅) = (2x₂, 3x₃, −x₄, 4x₅, 0)` on {lit}`F⁵`. -/
def T_ex_8C_2 (F : Type*) [Field F] : (Fin 5 → F) →ₗ[F] (Fin 5 → F) where
  toFun v := ![2 * v 1, 3 * v 2, - v 3, 4 * v 4, 0]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

/-- 8C.2 (a) {lit}`T` is nilpotent. -/
theorem exercise_8C_2a : IsNilpotent (T_ex_8C_2 F) := by
  sorry

/-- 8C.2 (b) {lit}`I + T` has a square root. -/
theorem exercise_8C_2b :
    ∃ R : (Fin 5 → F) →ₗ[F] (Fin 5 → F), R ^ 2 = 1 + T_ex_8C_2 F := by
  sorry

/-- 8C.3 Over {lit}`ℂ`, every invertible operator has a cube root. Invertibility
is encoded via a two-sided inverse {lit}`S`. -/
theorem exercise_8C_3 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T S : V →ₗ[ℂ] V) (hTS : T * S = 1) (hST : S * T = 1) :
    ∃ R : V →ₗ[ℂ] V, R ^ 3 = T := by
  sorry

/-- 8C.4 On a real vector space, {lit}`−I` has a square root iff {lit}`dim V` is
even. -/
theorem exercise_8C_4 {V : Type*} [AddCommGroup V] [Module ℝ V] [Finite ℝ V] :
    (∃ R : V →ₗ[ℝ] V, R ^ 2 = -1) ↔ Even (finrank ℝ V) := by
  sorry

/-- 8C.5 {lit}`T(w, z) = (−w − z, 9w + 5z)` on {lit}`ℂ²`. Its characteristic and
minimal polynomials are {lit}`(z − 2)²`, so {lit}`T` is a single {lit}`2`-by-{lit}`2`
Jordan block; a Jordan basis is any {lit}`v, (T − 2I)v` with {lit}`(T − 2I)v ≠ 0`.
We record the minimal-polynomial computation that pins down the Jordan structure. -/
def T_ex_8C_5 : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![- v 0 - v 1, 9 * v 0 + 5 * v 1]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by funext i; fin_cases i <;> simp <;> ring

theorem exercise_8C_5 : minpoly ℂ T_ex_8C_5 = (X - C 2) ^ 2 := by
  sorry

/-! Exercises 6–13 concern Jordan bases, which 8.44 encodes matrix-free as
{name}`LADR.Section_8C.HasJordanBasis` / {name}`LADR.Section_8C.HasNilpotentJordanBasis`:
eigenvalue chains {lit}`v i, (T − λᵢ)(v i), …` of lengths {lit}`M i`, one per
Jordan block. Exercises 6, 7, 9, 11, 12 and 13 are stated below in that encoding.
Exercises 8 and 10 ("describe the matrix of {lit}`T²`", "describe the matrix of
{lit}`T` in the reversed basis") ask for a description of {lit}`ℳ(T, basis)` for a
Jordan basis, which the chain encoding deliberately does not carry, so they remain
outside this formalization. -/

/-- The vector generating the Jordan chain of 8C.6 — the polynomial to be found by
the solver ({lit}`D⁴ v, …, D v, v` is then the Jordan basis). -/
noncomputable def jordanVector_8C_6 : Polynomial.degreeLT ℝ 5 := sorry

/-- 8C.6 A Jordan basis of {lit}`𝒫₄(ℝ)` for the differentiation operator
{lit}`D p = p′`. Since {lit}`D` is nilpotent with a single Jordan block, a Jordan
basis is one chain: {lit}`v, D v, …, D⁴ v` with {lit}`D⁵ v = 0`. -/
theorem exercise_8C_6 (D : Polynomial.degreeLT ℝ 5 →ₗ[ℝ] Polynomial.degreeLT ℝ 5)
    (hD : ∀ p : Polynomial.degreeLT ℝ 5,
      (D p : Polynomial ℝ) = (p : Polynomial ℝ).derivative) :
    (D ^ 5) jordanVector_8C_6 = 0 ∧
      LADR.Section_2B.IsBasis ℝ (fun k : Fin 5 => (D ^ (k : ℕ)) jordanVector_8C_6) := by
  sorry

/-- 8C.7 For nilpotent {lit}`T` with a Jordan basis, the minimal polynomial is
{lit}`z^{m+1}`, where {lit}`m` is the length of the longest consecutive string of
{lit}`1`'s directly above the diagonal. A block of size {lit}`M i` contributes a
string of {lit}`M i − 1` ones, so {lit}`m + 1` is the largest block size
{lit}`sup M`. -/
theorem exercise_8C_7 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (hT : IsNilpotent T) {ι : Type} [Fintype ι] [Nonempty ι]
    (M : ι → ℕ) (v : ι → V) (hM : ∀ i, 0 < M i) (hkill : ∀ i, (T ^ M i) (v i) = 0)
    (hLI : LinearIndependent ℂ (fun p : Σ i, Fin (M i) => (T ^ (p.2 : ℕ)) (v p.1)))
    (hspan : Submodule.span ℂ
      (Set.range fun p : Σ i, Fin (M i) => (T ^ (p.2 : ℕ)) (v p.1)) = ⊤) :
    minpoly ℂ T = X ^ (Finset.univ.sup M) := by
  sorry

/-- 8C.9 Every nilpotent operator admits vectors {lit}`v₁, …, vₙ` and exponents
{lit}`m₁, …, mₙ` whose chains {lit}`T^{mᵢ} vᵢ, …, T vᵢ, vᵢ` form a basis of
{lit}`V` with {lit}`T^{mᵢ+1} vᵢ = 0`. This is exactly 8.45. -/
theorem exercise_8C_9 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (hT : IsNilpotent T) : HasNilpotentJordanBasis T :=
  hasNilpotentJordanBasis T hT

/-- 8C.11 Every vector of a Jordan basis is a generalized eigenvector: the chain
for {lit}`i` lies in {lit}`G(λᵢ, T)`, which needs only the chain-terminating
condition {lit}`(T − λᵢ)^{M i} (v i) = 0`. -/
theorem exercise_8C_11 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) {ι : Type} [Fintype ι] (M : ι → ℕ) (lam : ι → ℂ) (v : ι → V)
    (hkill : ∀ i, ((T - lam i • 1) ^ M i) (v i) = 0) (p : Σ i, Fin (M i)) :
    ((T - lam p.1 • 1) ^ (p.2 : ℕ)) (v p.1) ∈ maxGenEigenspace T (lam p.1) := by
  sorry

/-- 8C.12 If {lit}`T` is diagonalizable then every Jordan basis for {lit}`T` has
all blocks of size {lit}`1` — equivalently {lit}`ℳ(T)` is diagonal with respect to
it. -/
theorem exercise_8C_12 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (hT : LADR.Section_5D.IsDiagonalizable T) {ι : Type} [Fintype ι]
    (M : ι → ℕ) (lam : ι → ℂ) (v : ι → V) (hM : ∀ i, 0 < M i)
    (hkill : ∀ i, ((T - lam i • 1) ^ M i) (v i) = 0)
    (hLI : LinearIndependent ℂ
      (fun p : Σ i, Fin (M i) => ((T - lam p.1 • 1) ^ (p.2 : ℕ)) (v p.1)))
    (hspan : Submodule.span ℂ
      (Set.range fun p : Σ i, Fin (M i) => ((T - lam p.1 • 1) ^ (p.2 : ℕ)) (v p.1)) = ⊤) :
    ∀ i, M i = 1 := by
  sorry

/-- 8C.13 For nilpotent {lit}`T`, the tops {lit}`T^{M i − 1} (v i)` of the Jordan
chains form a basis of {lit}`null T`. In particular the number of chains is
{lit}`dim null T`, so it depends only on {lit}`T`. -/
theorem exercise_8C_13 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) (hT : IsNilpotent T) {ι : Type} [Fintype ι]
    (M : ι → ℕ) (v : ι → V) (hM : ∀ i, 0 < M i) (hkill : ∀ i, (T ^ M i) (v i) = 0)
    (hLI : LinearIndependent ℂ (fun p : Σ i, Fin (M i) => (T ^ (p.2 : ℕ)) (v p.1)))
    (hspan : Submodule.span ℂ
      (Set.range fun p : Σ i, Fin (M i) => (T ^ (p.2 : ℕ)) (v p.1)) = ⊤) :
    LinearIndependent ℂ (fun i => (T ^ (M i - 1)) (v i)) ∧
      Submodule.span ℂ (Set.range fun i => (T ^ (M i - 1)) (v i)) = ker T := by
  sorry

/-- 8C.14 Over {lit}`ℂ`, there is no decomposition of {lit}`V` into two nonzero
{lit}`T`-invariant subspaces iff the minimal polynomial of {lit}`T` is
{lit}`(z − λ)^{dim V}` for some {lit}`λ`. -/
theorem exercise_8C_14 {V : Type*} [AddCommGroup V] [Module ℂ V] [Finite ℂ V]
    (T : V →ₗ[ℂ] V) :
    (¬ ∃ U W : Submodule ℂ V, U ≠ ⊥ ∧ W ≠ ⊥ ∧
        InvariantUnder T U ∧ InvariantUnder T W ∧ IsCompl U W) ↔
      ∃ lam : ℂ, minpoly ℂ T = (X - C lam) ^ (finrank ℂ V) := by
  sorry

end LADR.Section_8C
