import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3C
import LinearAlgebraDoneRightLean.Section_3D
import LinearAlgebraDoneRightLean.Section_3E
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3F: Duality
-/

namespace LADR.Section_3F

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open Module (Finite finrank Dual)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  {U : Type*} [AddCommGroup U] [Module F U]

/-! 3.108 Definition: linear functional — element of {lit}`V →ₗ[F] F`. -/

example : Type _ := V →ₗ[F] F

/-! 3.109 Examples of linear functionals. -/

/-- {lit}`φ(x, y, z) = 4x − 5y + 2z` on {lit}`ℝ³`. -/
def phi_3_109_a : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := 4 * v 0 - 5 * v 1 + 2 * v 2
  map_add' x y := by simp [Pi.add_apply]; ring
  map_smul' a x := by simp [Pi.smul_apply, smul_eq_mul]; ring

/-- {lit}`φ(x₁, …, xₙ) = c₁x₁ + ⋯ + cₙxₙ`. -/
def phi_3_109_b {n : ℕ} (c : Fin n → F) : (Fin n → F) →ₗ[F] F where
  toFun x := ∑ i, c i * x i
  map_add' x y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.add_apply]; ring
  map_smul' a x := by
    show ∑ i, c i * (a • x) i = a • ∑ i, c i * x i
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    ring

/-- {lit}`φ(p) = 3p″(5) + 7p(4)` on {lit}`𝒫(ℝ)`. -/
noncomputable def phi_3_109_c : Module.Dual ℝ (Polynomial ℝ) where
  toFun p :=
    3 * (Polynomial.derivative (Polynomial.derivative p)).eval 5 + 7 * p.eval 4
  map_add' p q := by
    simp only [Polynomial.derivative_add, Polynomial.eval_add]; ring
  map_smul' a p := by
    simp only [Polynomial.derivative_smul, Polynomial.eval_smul, smul_eq_mul,
      RingHom.id_apply]; ring

/-- {lit}`φ(p) = ∫₀¹ p` on {lit}`𝒫(ℝ)`. -/
noncomputable def phi_3_109_d : Module.Dual ℝ (Polynomial ℝ) where
  toFun p := ∫ x in (0:ℝ)..1, p.eval x
  map_add' p q := by
    simp only [Polynomial.eval_add]
    exact intervalIntegral.integral_add
      ((Polynomial.continuous p).intervalIntegrable 0 1)
      ((Polynomial.continuous q).intervalIntegrable 0 1)
  map_smul' a p := by
    simp only [Polynomial.eval_smul, smul_eq_mul, RingHom.id_apply]
    exact intervalIntegral.integral_const_mul a _

/-! 3.110 Definition: dual space {lit}`V'`.

In mathlib, the dual space of {lit}`V` is {name}`Module.Dual` which unfolds
to {lit}`V →ₗ[F] F`. -/

example : Module.Dual F V = (V →ₗ[F] F) := rfl

/-! 3.111 {lit}`dim V' = dim V` -/

@[avoiding Subspace.dual_finrank_eq]
theorem finrank_dual_eq_finrank [Finite F V] :
    finrank F (Module.Dual F V) = finrank F V := by
  show finrank F (V →ₗ[F] F) = finrank F V
  rw [LADR.Section_3D.finrank_linearMap, Module.finrank_self, mul_one]

/-! 3.112 Definition: dual basis.

In mathlib, given a basis {lit}`v₁, …, vₙ` of {lit}`V`, the dual basis is
provided by {name}`Module.Basis.dualBasis`. -/

noncomputable example {n : ℕ} (v : Fin n → V) (hv : IsBasis F v) :
    Fin n → Module.Dual F V := hv.toModuleBasis.dualBasis

/-- mathlib's {name}`Module.Basis.dualBasis` matches Axler's defining property
of 3.112: each {lit}`φⱼ` is the functional with {lit}`φⱼ(vₖ) = 1` if {lit}`k = j`
and {lit}`φⱼ(vₖ) = 0` if {lit}`k ≠ j`. -/
theorem dualBasis_apply_self {n : ℕ} (v : Fin n → V) (hv : IsBasis F v)
    (j k : Fin n) :
    hv.toModuleBasis.dualBasis j (v k) = if k = j then 1 else 0 := by
  rw [← IsBasis.toModuleBasis_apply hv k, Module.Basis.dualBasis_apply_self]

/-! 3.113 Example: the dual basis of the standard basis of {lit}`Fⁿ`
selects the {lit}`j`-th coordinate. -/

example {n : ℕ} (j : Fin n) (x : Fin n → F) :
    (Pi.basisFun F (Fin n)).dualBasis j x = x j := by
  simp [Pi.basisFun_repr]

/-! 3.114 Dual basis gives coefficients for linear combination -/

theorem dualBasis_gives_coefficients {n : ℕ} (v : Fin n → V) (hv : IsBasis F v)
    (x : V) :
    x = ∑ j, hv.toModuleBasis.dualBasis j x • v j := by
  conv_lhs => rw [← hv.toModuleBasis.sum_repr x]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show hv.toModuleBasis j = v j from IsBasis.toModuleBasis_apply hv j,
    Module.Basis.dualBasis_apply]

/-! 3.116 Dual basis is a basis of the dual space.

Following Axler's proof: {lit}`φ₁, …, φₙ` is linearly independent because
applying {lit}`a₁φ₁ + ⋯ + aₙφₙ = 0` to {lit}`vₖ` yields {lit}`aₖ = 0`; then it
is a basis since it is a linearly independent list of length
{lit}`dim V' = dim V = n` (3.111 and 2.38). -/

theorem isBasis_dualBasis [Finite F V] {n : ℕ} (v : Fin n → V)
    (hv : IsBasis F v) : IsBasis F hv.toModuleBasis.dualBasis := by
  -- Linear independence: if {lit}`∑ⱼ aⱼφⱼ = 0`, evaluate at {lit}`vₖ` to get
  -- {lit}`aₖ = 0`.
  have hli : LinearIndependent F hv.toModuleBasis.dualBasis := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have hk : (∑ j, a j • hv.toModuleBasis.dualBasis j) (v k) = 0 := by
      rw [ha]; rfl
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, dualBasis_apply_self, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at hk
    exact hk
  -- A linearly independent list of length {lit}`dim V' = dim V = n` is a basis.
  have hcard : n = finrank F (Module.Dual F V) := by
    rw [finrank_dual_eq_finrank]
    exact LADR.Section_2C.isBasis_card_eq_finrank v hv
  exact LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq _ hli hcard

/-! 3.118 Definition: dual map {lit}`T'`.

In mathlib, this is {name}`LinearMap.dualMap`. -/

example (T : V →ₗ[F] W) (φ : Module.Dual F W) (v : V) :
    T.dualMap φ v = φ (T v) := T.dualMap_apply φ v

/-! As Axler notes after the definition, {lit}`T'` is itself a linear map from
{lit}`W'` to {lit}`V'`. We verify this directly from {lit}`T'(φ) = φ ∘ T`,
rather than appealing to the fact that mathlib already bundles {lit}`T.dualMap`
as a linear map. -/

/-- {lit}`T'(φ + ψ) = (φ + ψ) ∘ T = φ ∘ T + ψ ∘ T = T'(φ) + T'(ψ)`. -/
example (T : V →ₗ[F] W) (φ ψ : Module.Dual F W) :
    T.dualMap (φ + ψ) = T.dualMap φ + T.dualMap ψ := by
  ext v
  rw [LinearMap.add_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply,
      LinearMap.dualMap_apply, LinearMap.add_apply]

/-- {lit}`T'(λφ) = (λφ) ∘ T = λ(φ ∘ T) = λ T'(φ)`. -/
example (T : V →ₗ[F] W) (γ : F) (φ : Module.Dual F W) :
    T.dualMap (γ • φ) = γ • T.dualMap φ := by
  ext v
  rw [LinearMap.smul_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply,
      LinearMap.smul_apply]

/-! 3.119 Example: the dual map of differentiation. -/

example (φ : Module.Dual ℝ (Polynomial ℝ)) (hφ : ∀ p, φ p = p.eval 3) :
    ∀ p, (Polynomial.derivative.dualMap φ) p = (p.derivative).eval 3 := by
  intro p
  rw [LinearMap.dualMap_apply]
  exact hφ _

/-- Second bullet of 3.119: for {lit}`φ(p) = ∫₀¹ p`, the dual map {lit}`D'(φ)`
takes {lit}`p` to {lit}`p(1) − p(0)`, since
{lit}`(D'(φ))(p) = φ(p') = ∫₀¹ p' = p(1) − p(0)` by the fundamental theorem of
calculus. -/
example (φ : Module.Dual ℝ (Polynomial ℝ))
    (hφ : ∀ p, φ p = ∫ x in (0:ℝ)..1, p.eval x) :
    ∀ p, (Polynomial.derivative.dualMap φ) p = p.eval 1 - p.eval 0 := by
  intro p
  rw [LinearMap.dualMap_apply, hφ]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => p.hasDerivAt x)
    ((Polynomial.continuous p.derivative).intervalIntegrable 0 1)

/-! 3.120 Algebraic properties of dual maps. -/

/-- (a) {lit}`(S + T)' = S' + T'` -/
example (S T : V →ₗ[F] W) : (S + T).dualMap = S.dualMap + T.dualMap := by
  ext phi v
  simp [LinearMap.dualMap_apply]

/-- (b) {lit}`(λT)' = λT'` -/
example (γ : F) (T : V →ₗ[F] W) : (γ • T).dualMap = γ • T.dualMap := by
  ext φ v
  simp [LinearMap.dualMap_apply]

/-- (c) {lit}`(ST)' = T'S'` -/
example (T : U →ₗ[F] V) (S : V →ₗ[F] W) :
    (S ∘ₗ T).dualMap = T.dualMap ∘ₗ S.dualMap := by
  ext φ v
  simp [LinearMap.dualMap_apply]

/-! 3.121 Definition: annihilator {lit}`U⁰`.

In mathlib, this is {name}`Submodule.dualAnnihilator`. -/

example (U : Submodule F V) : Submodule F (Module.Dual F V) :=
  U.dualAnnihilator

example (U : Submodule F V) (φ : Module.Dual F V) :
    φ ∈ U.dualAnnihilator ↔ ∀ u ∈ U, φ u = 0 :=
  Submodule.mem_dualAnnihilator φ

/-! 3.122 Example: an element of an annihilator. Let {lit}`U` be the subspace
of {lit}`𝒫(ℝ)` consisting of polynomial multiples of {lit}`x²`, and let
{lit}`φ(p) = p'(0)`. Then {lit}`φ ∈ U⁰`. -/

/-- {lit}`φ(p) = p'(0)`, a linear functional on {lit}`𝒫(ℝ)`. -/
noncomputable def phi_3_122 : Module.Dual ℝ (Polynomial ℝ) where
  toFun p := (Polynomial.derivative p).eval 0
  map_add' p q := by simp
  map_smul' a p := by simp

/-- {lit}`U` = polynomial multiples of {lit}`x²`, realized as the range of
{lit}`q ↦ q · x²`. -/
example :
    phi_3_122 ∈
      (LinearMap.range
        (LinearMap.mulRight ℝ (Polynomial.X ^ 2 : Polynomial ℝ))).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  rintro u ⟨q, rfl⟩
  simp [phi_3_122, LinearMap.mulRight_apply, Polynomial.derivative_mul]

/-! 3.123 Example: the annihilator of a two-dimensional subspace of {lit}`ℝ⁵`.
Let {lit}`e₁, …, e₅` be the standard basis of {lit}`ℝ⁵` with dual basis
{lit}`φ₁, …, φ₅`, and let {lit}`U = span(e₁, e₂)`. Then
{lit}`U⁰ = span(φ₃, φ₄, φ₅)`. (Lean indices are 0-based, so this reads as
{lit}`span(e₀, e₁)⁰ = span(φ₂, φ₃, φ₄)`.) -/

theorem example_3_123 :
    (Submodule.span ℝ
        {Pi.basisFun ℝ (Fin 5) 0, Pi.basisFun ℝ (Fin 5) 1}).dualAnnihilator =
      Submodule.span ℝ
        {(Pi.basisFun ℝ (Fin 5)).dualBasis 2,
         (Pi.basisFun ℝ (Fin 5)).dualBasis 3,
         (Pi.basisFun ℝ (Fin 5)).dualBasis 4} := by
  set e := Pi.basisFun ℝ (Fin 5) with he
  apply le_antisymm
  · -- {lit}`U⁰ ⊆ span(φ₂, φ₃, φ₄)`: write {lit}`φ = ∑ φ(eⱼ) φⱼ` and drop the
    -- vanishing {lit}`φ(e₀), φ(e₁)` coefficients.
    intro phi hphi
    rw [Submodule.mem_dualAnnihilator] at hphi
    have h0 : phi (e 0) = 0 := hphi _ (Submodule.subset_span (by simp))
    have h1 : phi (e 1) = 0 := hphi _ (Submodule.subset_span (by simp))
    have hrep := e.dualBasis.sum_repr phi
    simp only [Module.Basis.dualBasis_repr] at hrep
    rw [Fin.sum_univ_five, h0, h1] at hrep
    simp only [zero_smul, zero_add] at hrep
    rw [← hrep]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · -- {lit}`span(φ₂, φ₃, φ₄) ⊆ U⁰`: each {lit}`φⱼ` kills {lit}`e₀` and {lit}`e₁`.
    rw [Submodule.span_le, Submodule.coe_dualAnnihilator_span]
    intro psi hpsi x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpsi hx
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    rcases hpsi with rfl | rfl | rfl <;> rcases hx with rfl | rfl <;> simp

/-! 3.124 The annihilator is a subspace. In mathlib this is automatic since
{name}`Submodule.dualAnnihilator` returns a {name}`Submodule`, but we also
verify Axler's three subspace conditions directly. -/

example (U : Submodule F V) : Submodule F (Module.Dual F V) :=
  U.dualAnnihilator

/-- {lit}`0 ∈ U⁰`: the zero functional sends every {lit}`u ∈ U` to {lit}`0`. -/
example (U : Submodule F V) : (0 : Module.Dual F V) ∈ U.dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro u _
  rfl

/-- Closed under addition: if {lit}`φ, ψ ∈ U⁰` then for {lit}`u ∈ U`,
{lit}`(φ + ψ)(u) = φ(u) + ψ(u) = 0 + 0 = 0`. -/
example (U : Submodule F V) (φ ψ : Module.Dual F V)
    (hφ : φ ∈ U.dualAnnihilator) (hψ : ψ ∈ U.dualAnnihilator) :
    φ + ψ ∈ U.dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator] at hφ hψ ⊢
  intro u hu
  rw [LinearMap.add_apply, hφ u hu, hψ u hu, add_zero]

/-- Closed under scalar multiplication: if {lit}`φ ∈ U⁰` then for {lit}`u ∈ U`,
{lit}`(λφ)(u) = λ·φ(u) = λ·0 = 0`. -/
example (U : Submodule F V) (c : F) (φ : Module.Dual F V)
    (hφ : φ ∈ U.dualAnnihilator) : c • φ ∈ U.dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator] at hφ ⊢
  intro u hu
  rw [LinearMap.smul_apply, hφ u hu, smul_zero]

/-! 3.125 Dimension of the annihilator.

Following Axler's proof: let {lit}`i : U → V` be the inclusion map, with dual
{lit}`i' : V' → U'`. The fundamental theorem of linear maps applied to
{lit}`i'` gives {lit}`dim range i' + dim null i' = dim V'`. Here
{lit}`null i' = U⁰`, {lit}`dim V' = dim V` (3.111), and {lit}`i'` is surjective
(every functional on {lit}`U` extends to {lit}`V`), so
{lit}`dim range i' = dim U' = dim U`. Hence {lit}`dim U + dim U⁰ = dim V`. -/

theorem finrank_dualAnnihilator [Finite F V] (U : Submodule F V) :
    finrank F U.dualAnnihilator = finrank F V - finrank F U := by
  -- {lit}`null i' = U⁰`: {lit}`i'(φ) = φ ∘ i` vanishes iff {lit}`φ` kills {lit}`U`.
  have hker : LinearMap.ker U.subtype.dualMap = U.dualAnnihilator := by
    ext φ
    rw [LinearMap.mem_ker, Submodule.mem_dualAnnihilator]
    constructor
    · intro hφ u hu
      have h0 : U.subtype.dualMap φ ⟨u, hu⟩ = 0 := by rw [hφ]; rfl
      rwa [LinearMap.dualMap_apply] at h0
    · intro h
      ext x
      rw [LinearMap.zero_apply, LinearMap.dualMap_apply]
      exact h _ x.2
  -- {lit}`i'` is surjective, since {lit}`i` is injective (functional extension).
  have hsurj : Function.Surjective U.subtype.dualMap :=
    LinearMap.dualMap_surjective_of_injective U.injective_subtype
  -- FTLM for {lit}`i'`, then substitute the pieces.
  have hftl := LADR.Section_3B.finrank_ker_add_finrank_range U.subtype.dualMap
  rw [hker, finrank_dual_eq_finrank, LinearMap.range_eq_top.mpr hsurj,
      finrank_top, finrank_dual_eq_finrank] at hftl
  omega

/-! 3.127 Annihilator equals zero or the whole dual space. -/

theorem dualAnnihilator_eq_bot_iff [Finite F V] (U : Submodule F V) :
    U.dualAnnihilator = ⊥ ↔ U = ⊤ := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  constructor
  · intro hbot
    rw [hbot, finrank_bot] at h
    have h_eq : finrank F U = finrank F V := by omega
    exact LADR.Section_2C.subspace_eq_top_of_finrank_eq U h_eq
  · intro htop; subst htop
    exact Submodule.dualAnnihilator_top

theorem dualAnnihilator_eq_top_iff [Finite F V] (U : Submodule F V) :
    U.dualAnnihilator = ⊤ ↔ U = ⊥ := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  have hdim_dual : finrank F (Module.Dual F V) = finrank F V :=
    finrank_dual_eq_finrank
  constructor
  · intro htop
    have h_top : finrank F U.dualAnnihilator = finrank F V := by
      rw [htop, ← hdim_dual]
      exact Submodule.topEquiv.finrank_eq
    have : finrank F U = 0 := by omega
    rwa [Submodule.finrank_eq_zero] at this
  · intro hbot; subst hbot
    apply LADR.Section_2C.subspace_eq_top_of_finrank_eq
    rw [finrank_dual_eq_finrank]
    have : finrank F (⊥ : Submodule F V) = 0 := finrank_bot F V
    omega

/-! 3.128 The null space of {lit}`T'`. -/

/-- (a) {lit}`null T' = (range T)⁰`. -/
theorem ker_dualMap_eq_range_dualAnnihilator (T : V →ₗ[F] W) :
    LinearMap.ker T.dualMap = (LinearMap.range T).dualAnnihilator := by
  ext phi
  rw [LinearMap.mem_ker, Submodule.mem_dualAnnihilator]
  constructor
  · intro hphi w hw
    obtain ⟨v, rfl⟩ := hw
    have : T.dualMap phi v = 0 := by rw [hphi]; rfl
    rw [LinearMap.dualMap_apply] at this
    exact this
  · intro h
    ext v
    rw [LinearMap.dualMap_apply]
    exact h _ (LinearMap.mem_range_self T v)

/-- (b) {lit}`dim null T' = dim null T + dim W − dim V`. -/
theorem finrank_ker_dualMap [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    finrank F (LinearMap.ker T.dualMap) =
      finrank F (LinearMap.ker T) + finrank F W - finrank F V := by
  rw [ker_dualMap_eq_range_dualAnnihilator T, finrank_dualAnnihilator]
  have h := LADR.Section_3B.finrank_ker_add_finrank_range T
  omega

/-! 3.129 {lit}`T` surjective iff {lit}`T'` injective. -/

theorem surjective_iff_dualMap_injective [Finite F V] [Finite F W]
    (T : V →ₗ[F] W) :
    Function.Surjective T ↔ Function.Injective T.dualMap := by
  rw [LADR.Section_3B.surjective_iff_range_eq_top,
      LADR.Section_3B.injective_iff_ker_eq_bot,
      ker_dualMap_eq_range_dualAnnihilator,
      dualAnnihilator_eq_bot_iff]

/-! 3.130 The range of {lit}`T'`. -/

/-- (a) {lit}`dim range T' = dim range T`. -/
theorem finrank_range_dualMap [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T.dualMap) = finrank F (LinearMap.range T) := by
  -- {lit}`dim range T' = dim W' − dim ker T' = dim W − dim (range T)⁰
  -- = dim W − (dim W − dim range T) = dim range T`.
  have h_FTL := LADR.Section_3B.finrank_ker_add_finrank_range T.dualMap
  rw [ker_dualMap_eq_range_dualAnnihilator, finrank_dualAnnihilator] at h_FTL
  rw [finrank_dual_eq_finrank] at h_FTL
  have h_range_le : finrank F (LinearMap.range T) ≤ finrank F W :=
    LADR.Section_2C.finrank_submodule_le (LinearMap.range T)
  omega

/-- (b) {lit}`range T' = (null T)⁰`. Following Axler: the inclusion
{lit}`range T' ⊆ (null T)⁰` is immediate, and the two subspaces have equal
dimension since {lit}`dim range T' = dim range T = dim V − dim null T
= dim (null T)⁰` (by 3.130(a), the fundamental theorem of linear maps, and
3.125). -/
theorem range_dualMap_eq_ker_dualAnnihilator [Finite F V] [Finite F W]
    (T : V →ₗ[F] W) :
    LinearMap.range T.dualMap = (LinearMap.ker T).dualAnnihilator := by
  -- {lit}`range T' ⊆ (null T)⁰`: if {lit}`φ = T'(ψ)` and {lit}`v ∈ null T`,
  -- then {lit}`φ(v) = ψ(Tv) = ψ(0) = 0`.
  have hsub : LinearMap.range T.dualMap ≤ (LinearMap.ker T).dualAnnihilator := by
    rintro φ ⟨ψ, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro v hv
    rw [LinearMap.dualMap_apply, LinearMap.mem_ker.mp hv, map_zero]
  -- {lit}`dim range T' = dim range T = dim V − dim null T = dim (null T)⁰`.
  have hdim : finrank F (LinearMap.range T.dualMap)
      = finrank F (LinearMap.ker T).dualAnnihilator := by
    rw [finrank_range_dualMap, finrank_dualAnnihilator]
    have h := LADR.Section_3B.finrank_ker_add_finrank_range T
    omega
  exact Submodule.eq_of_le_of_finrank_eq hsub hdim

/-! 3.131 {lit}`T` injective iff {lit}`T'` surjective. -/

theorem injective_iff_dualMap_surjective [Finite F V] [Finite F W]
    (T : V →ₗ[F] W) :
    Function.Injective T ↔ Function.Surjective T.dualMap := by
  rw [LADR.Section_3B.injective_iff_ker_eq_bot,
      LADR.Section_3B.surjective_iff_range_eq_top,
      range_dualMap_eq_ker_dualAnnihilator,
      dualAnnihilator_eq_top_iff]

/-! Matrix of Dual of Linear Map. -/

/-! 3.132 Matrix of {lit}`T'` is the transpose of matrix of {lit}`T`.

Given bases of V and W with their dual bases, the matrix of {lit}`T'` in
the dual bases equals the transpose of the matrix of {lit}`T`. -/

/-- The matrix of {lit}`T'` (computed in the dual bases) equals the
transpose of the matrix of {lit}`T`. Stated using mathlib's
{name}`LinearMap.toMatrix` and {name}`Module.Basis.dualBasis` directly. -/
theorem toMatrix_dualMap_eq_transpose [Finite F V] [Finite F W] {m n : ℕ}
    (v : Fin n → V) (w : Fin m → W) (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) :
    LinearMap.toMatrix hw.toModuleBasis.dualBasis hv.toModuleBasis.dualBasis
      T.dualMap =
        (LinearMap.toMatrix hv.toModuleBasis hw.toModuleBasis T).transpose := by
  ext k j
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  -- LHS: (hv.dualBasis.repr (T'(hw.dualBasis j))) k = (T'(hw.dualBasis j))(hv k)
  --    = (hw.dualBasis j)(T(hv k)) = (hw.repr (T(hv k))) j = RHS.
  rw [← Module.Basis.equivFun_apply, Module.Basis.dualBasis_equivFun,
      LinearMap.dualMap_apply, Module.Basis.dualBasis_apply]

/-! 3.133 Column rank equals row rank. We proved this directly in
{name}`LADR.Section_3C.columnRank_eq_rowRank`. -/

example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    LADR.Section_3C.columnRank A = LADR.Section_3C.rowRank A :=
  LADR.Section_3C.columnRank_eq_rowRank A

/-- The separate proof using duality, as in Axler 3.133. Writing
{lit}`T x = Ax`, we have {lit}`column rank A = dim range T = dim range T'
= column rank Aᵗ = row rank A`, where the middle equality is 3.130(a) and
{lit}`M(T') = Aᵗ` is 3.132 ({name}`Matrix.toLin_transpose`). -/
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    LADR.Section_3C.columnRank A = LADR.Section_3C.rowRank A := by
  classical
  -- {lit}`column rank A = rank A`, and {lit}`row rank A = column rank Aᵗ
  -- = rank Aᵗ`, reducing the goal to {lit}`rank A = rank Aᵗ`.
  rw [← LADR.Section_3C.matrix_rank_eq_columnRank,
      ← LADR.Section_3C.columnRank_transpose A,
      ← LADR.Section_3C.matrix_rank_eq_columnRank]
  -- Axler's duality step: the matrix of {lit}`T'` in the dual bases is
  -- {lit}`Aᵗ` (3.132), and {lit}`dim range T' = dim range T` (3.130(a)).
  rw [A.transpose.rank_eq_finrank_range_toLin (Pi.basisFun F (Fin n)).dualBasis
        (Pi.basisFun F (Fin m)).dualBasis,
      Matrix.toLin_transpose, ← LinearMap.dualMap_def, finrank_range_dualMap,
      ← A.rank_eq_finrank_range_toLin (Pi.basisFun F (Fin m)) (Pi.basisFun F (Fin n))]

/-! # Exercises -/

/-- 3F.1 Every linear functional is either surjective or the zero map. -/
theorem exercise_3F_1 (φ : V →ₗ[F] F) :
    Function.Surjective φ ∨ φ = 0 := by
  sorry

/-- 3F.2 -/
example : ∃ φ₁ φ₂ φ₃ : Module.Dual ℝ (↥(Set.Icc (0:ℝ) 1) → ℝ),
    φ₁ ≠ φ₂ ∧ φ₁ ≠ φ₃ ∧ φ₂ ≠ φ₃ := by sorry

/-- 3F.3 -/
theorem exercise_3F_3 (v : V) (hv : v ≠ 0) :
    ∃ φ : Module.Dual F V, φ v = 1 := by
  sorry

/-- 3F.4 -/
theorem exercise_3F_4 (U : Submodule F V) (hU : U ≠ ⊤) :
    ∃ φ : Module.Dual F V, (∀ u ∈ U, φ u = 0) ∧ φ ≠ 0 := by
  sorry

/-- 3F.5 Suppose {lit}`w₁, …, wₘ` is a basis of {lit}`range T`. Expanding each
{lit}`Tv` in this basis as {lit}`Tv = φ₁(v)w₁ + ⋯ + φₘ(v)wₘ` defines functions
{lit}`φᵢ : V → F`; show that each {lit}`φᵢ` is a linear functional on {lit}`V`. -/
theorem exercise_3F_5 (T : V →ₗ[F] W) {m : ℕ} (w : Fin m → W)
    (hwmem : ∀ i, w i ∈ LinearMap.range T)
    (hw : IsBasis F (fun i => (⟨w i, hwmem i⟩ : LinearMap.range T)))
    (φ : Fin m → V → F) (hφ : ∀ v, T v = ∑ i, φ i v • w i) :
    ∀ i, IsLinearMap F (φ i) := by
  sorry

/-- 3F.6 -/
theorem exercise_3F_6 (φ β : Module.Dual F V) :
    LinearMap.ker φ ≤ LinearMap.ker β ↔
      ∃ c : F, β = c • φ := by
  sorry

/-- 3F.7 -/
theorem exercise_3F_7 {m : ℕ} (Vi : Fin m → Type*)
    [∀ i, AddCommGroup (Vi i)] [∀ i, Module F (Vi i)] :
    Nonempty (Module.Dual F ((i : Fin m) → Vi i) ≃ₗ[F]
              ((i : Fin m) → Module.Dual F (Vi i))) := by
  sorry

/-- 3F.8 The maps {lit}`Γ(u) = (φ₁(u), …, φₙ(u))` and {lit}`Λ(a) = ∑ aᵢvᵢ`
are inverses of each other. -/
theorem exercise_3F_8 {n : ℕ} (v : Fin n → V) (hv : IsBasis F v) :
    let Γ := fun u : V => fun j => hv.toModuleBasis.dualBasis j u
    let Λ := fun a : Fin n → F => ∑ i, a i • v i
    Function.LeftInverse Λ Γ ∧ Function.RightInverse Λ Γ := by
  sorry

/-- 3F.9 The dual basis of {lit}`1, x, …, xᵐ` in {lit}`𝒫ₘ(ℝ)` is given by
{lit}`φₖ(p) = p⁽ᵏ⁾(0)/k!`. Taking these functionals as given, the content of the
exercise is that they form a basis of the dual space. -/
theorem exercise_3F_9 (m : ℕ)
    (φ : Fin (m + 1) → Module.Dual ℝ (Polynomial.degreeLT ℝ (m + 1)))
    (hφ : ∀ (k : Fin (m + 1)) (p : Polynomial.degreeLT ℝ (m + 1)),
      φ k p =
        (Polynomial.derivative^[(k : ℕ)] (p : Polynomial ℝ)).eval 0
          / ((k : ℕ).factorial : ℝ)) :
    IsBasis ℝ φ := by
  sorry

/-- 3F.10 (a) {lit}`1, x − 5, …, (x − 5)ᵐ` is a basis of {lit}`𝒫ₘ(ℝ)`. -/
theorem exercise_3F_10a (m : ℕ)
    (e : Fin (m + 1) → Polynomial.degreeLT ℝ (m + 1))
    (he : ∀ k, (e k : Polynomial ℝ) = (Polynomial.X - 5) ^ (k : ℕ)) :
    IsBasis ℝ e := by
  sorry

/-- 3F.10 (b) The dual basis of the basis {lit}`1, x − 5, …, (x − 5)ᵐ` in (a) is
{lit}`φₖ(p) = p⁽ᵏ⁾(5)/k!` (the same as 3F.9 but with the derivatives evaluated
at {lit}`5` instead of {lit}`0`). -/
theorem exercise_3F_10b (m : ℕ)
    (e : Fin (m + 1) → Polynomial.degreeLT ℝ (m + 1))
    (he : ∀ k, (e k : Polynomial ℝ) = (Polynomial.X - 5) ^ (k : ℕ))
    (hv : IsBasis ℝ e)
    (φ : Fin (m + 1) → Module.Dual ℝ (Polynomial.degreeLT ℝ (m + 1)))
    (hφ : ∀ (k : Fin (m + 1)) (p : Polynomial.degreeLT ℝ (m + 1)),
      φ k p =
        (Polynomial.derivative^[(k : ℕ)] (p : Polynomial ℝ)).eval 5
          / ((k : ℕ).factorial : ℝ)) :
    ∀ k, hv.toModuleBasis.dualBasis k = φ k := by
  sorry

/-- 3F.11 -/
theorem exercise_3F_11 {n : ℕ} (v : Fin n → V) (hv : IsBasis F v)
    (ψ : Module.Dual F V) :
    ψ = ∑ j, ψ (v j) • hv.toModuleBasis.dualBasis j := by
  sorry

/-! 3F.12 (a) and (b) are exactly the algebraic properties of dual maps 3.120
(a) {lit}`(S + T)' = S' + T'` and (b) {lit}`(λT)' = λT'`, already proved above. -/

/-- 3F.13 -/
example : (LinearMap.id : V →ₗ[F] V).dualMap = LinearMap.id := by sorry

/-- 3F.14 -/
theorem exercise_3F_14 (T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (hT : ∀ v, T v =
      ![4 * v 0 + 5 * v 1 + 6 * v 2, 7 * v 0 + 8 * v 1 + 9 * v 2]) :
    let φ := (Pi.basisFun ℝ (Fin 2)).dualBasis
    let ψ := (Pi.basisFun ℝ (Fin 3)).dualBasis
    -- (a) {lit}`T'(φ₁)(x,y,z) = 4x + 5y + 6z`, {lit}`T'(φ₂)(x,y,z) = 7x + 8y + 9z`
    (∀ v, T.dualMap (φ 0) v = 4 * v 0 + 5 * v 1 + 6 * v 2) ∧
    (∀ v, T.dualMap (φ 1) v = 7 * v 0 + 8 * v 1 + 9 * v 2) ∧
    -- (b) the same as linear combinations of the dual basis of {lit}`ℝ³`
    T.dualMap (φ 0) = 4 • ψ 0 + 5 • ψ 1 + 6 • ψ 2 ∧
    T.dualMap (φ 1) = 7 • ψ 0 + 8 • ψ 1 + 9 • ψ 2 := by
  sorry

/-- 3F.15 -/
theorem exercise_3F_15a (T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
    (hT : ∀ p, T p =
      Polynomial.X ^ 2 * p + Polynomial.derivative (Polynomial.derivative p))
    (φ : Module.Dual ℝ (Polynomial ℝ))
    (hφ : ∀ p, φ p = (Polynomial.derivative p).eval 4) :
    ∀ p, T.dualMap φ p =
      8 * p.eval 4 + 16 * (Polynomial.derivative p).eval 4 +
        (Polynomial.derivative (Polynomial.derivative
          (Polynomial.derivative p))).eval 4 := by
  sorry

/-- 3F.15 (b) For {lit}`φ(p) = ∫₀¹ p`, {lit}`(T'(φ))(x³) = 19/6`. -/
theorem exercise_3F_15b (T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
    (hT : ∀ p, T p =
      Polynomial.X ^ 2 * p + Polynomial.derivative (Polynomial.derivative p))
    (φ : Module.Dual ℝ (Polynomial ℝ))
    (hφ : ∀ p, φ p = ∫ x in (0:ℝ)..1, p.eval x) :
    T.dualMap φ (Polynomial.X ^ 3) = 19 / 6 := by
  sorry

/-- 3F.16 -/
theorem exercise_3F_16 [Finite F W] (T : V →ₗ[F] W) :
    T.dualMap = 0 ↔ T = 0 := by
  sorry

/-- 3F.17 -/
theorem exercise_3F_17 [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    LADR.Section_3D.IsInvertible T ↔ LADR.Section_3D.IsInvertible T.dualMap := by
  sorry

/-- 3F.18 -/
theorem exercise_3F_18 [Finite F V] [Finite F W] :
    IsLinearMap F (fun T: V →ₗ[F] W => T.dualMap) ∧
    Function.Bijective (fun T: V →ₗ[F] W => T.dualMap) := by
  sorry

/-- 3F.19 -/
theorem exercise_3F_19 (U : Submodule F V) :
    U.dualAnnihilator = {φ : Module.Dual F V | (U : Set V) ⊆ LinearMap.ker φ} := by
  sorry

/-- 3F.20 -/
theorem exercise_3F_20 [Finite F V] (U : Submodule F V) :
    (U : Set V) =
      {v : V | ∀ φ ∈ U.dualAnnihilator, φ v = 0} := by
  sorry

/-- 3F.21 (a) -/
theorem exercise_3F_21a [Finite F V] (U W : Submodule F V) :
    W.dualAnnihilator ≤ U.dualAnnihilator ↔ U ≤ W := by
  sorry

/-- 3F.21 (b) -/
theorem exercise_3F_21b [Finite F V] (U W : Submodule F V) :
    W.dualAnnihilator = U.dualAnnihilator ↔ U = W := by
  sorry

/-- 3F.22 (a) -/
theorem exercise_3F_22a [Finite F V] (U W : Submodule F V) :
    (U ⊔ W).dualAnnihilator =
      U.dualAnnihilator ⊓ W.dualAnnihilator := by
  sorry

/-- 3F.22 (b) -/
theorem exercise_3F_22b [Finite F V] (U W : Submodule F V) :
    (U ⊓ W).dualAnnihilator =
      U.dualAnnihilator ⊔ W.dualAnnihilator := by
  sorry

/-- 3F.23  -/
theorem exercise_3F_23 [Finite F V] {m : ℕ} (φ : Fin m → Module.Dual F V) :
    Submodule.span F (Set.range φ) = (⨅ i, LinearMap.ker (φ i)).dualAnnihilator ∧
    ((⨅ i, LinearMap.ker (φ i)).dualAnnihilator : Set (Module.Dual F V)) =
        {ψ | (⨅ i, LinearMap.ker (φ i)) ≤ LinearMap.ker ψ} := by
  sorry

/-- 3F.24 -/
theorem exercise_3F_24 [Finite F V] {m : ℕ} (v : Fin m → V) :
    let Γ := fun (φ : Module.Dual F V) (i : Fin m) => φ (v i)
    (Spans F v ↔ Function.Injective Γ) ∧
    (LinearIndependent F v ↔ Function.Surjective Γ) := by
  sorry

/-- 3F.25 -/
theorem exercise_3F_25 [Finite F V] {m : ℕ} (φ : Fin m → Module.Dual F V) :
    let Γ := fun (v : V) (i : Fin m) => φ i v
    (Spans F φ ↔ Function.Injective Γ) ∧
    (LinearIndependent F φ ↔ Function.Surjective Γ) := by
  sorry

/-- 3F.26 The book's inner set {lit}`{v ∈ V : φ(v) = 0 for every φ ∈ Ω}` is, by the
definition of {name}`Submodule.dualCoannihilator` (see
{name}`Submodule.mem_dualCoannihilator`), exactly {lit}`Ω.dualCoannihilator`. -/
example (Ω : Submodule F (Module.Dual F V)) :
    (Ω.dualCoannihilator : Set V) = {v : V | ∀ φ ∈ Ω, φ v = 0} := by
  ext v; exact Submodule.mem_dualCoannihilator v

theorem exercise_3F_26 [Finite F V] (Ω : Submodule F (Module.Dual F V)) :
    Ω = Ω.dualCoannihilator.dualAnnihilator := by
  sorry

/-- 3F.27 -/
theorem exercise_3F_27
    (T : Polynomial.degreeLT ℝ 6 →ₗ[ℝ] Polynomial.degreeLT ℝ 6)
    (φ : Module.Dual ℝ (Polynomial.degreeLT ℝ 6))
    (hφ : ∀ p, φ p = (p : Polynomial ℝ).eval 8)
    (hT : LinearMap.ker T.dualMap = Submodule.span ℝ {φ}) :
    (LinearMap.range T : Set (Polynomial.degreeLT ℝ 6)) =
      {p : Polynomial.degreeLT ℝ 6 | (p : Polynomial ℝ).eval 8 = 0} := by
  sorry

/-- 3F.28 -/
theorem exercise_3F_28 [Finite F V] {m : ℕ} (φ : Fin m → Module.Dual F V)
    (hφ : LinearIndependent F φ) :
    finrank F ↥(⨅ i, LinearMap.ker (φ i)) = finrank F V - m := by
  sorry

/-- 3F.29 (a) -/
theorem exercise_3F_29a [Finite F V] [Finite F W] (T : V →ₗ[F] W)
    (φ : Module.Dual F W) (hφ : LinearMap.ker T.dualMap = Submodule.span F {φ}) :
    LinearMap.range T = LinearMap.ker φ := by
  sorry

/-- 3F.29 (b) -/
theorem exercise_3F_29b [Finite F V] [Finite F W] (T : V →ₗ[F] W)
    (ψ : Module.Dual F V) (hψ : LinearMap.range T.dualMap = Submodule.span F {ψ}) :
    LinearMap.ker T = LinearMap.ker ψ := by
  sorry

/-- 3F.30 -/
theorem exercise_3F_30 [Finite F V] {n : ℕ} (phi : Fin n → Module.Dual F V)
    (hphi : IsBasis F phi) :
    ∃ v : Fin n → V, ∃ hv : IsBasis F v,
      ∀ j, hv.toModuleBasis.dualBasis j = phi j := by
  sorry

/-- 3F.31 (a) For the inclusion {lit}`i : U → V` ({lit}`i(u) = u` in mathlib is
{name}`Submodule.subtype`) -/
theorem exercise_3F_31a (U : Submodule F V) :
    LinearMap.ker U.subtype.dualMap = U.dualAnnihilator := by
  sorry

/-- 3F.31 (b) -/
theorem exercise_3F_31b [Finite F V] (U : Submodule F V) :
    LinearMap.range U.subtype.dualMap = ⊤ := by
  sorry

/-- 3F.31 (c) If {lit}`V` is finite-dimensional, the map {lit}`ī'` that {lit}`i'`
induces on {lit}`V'/U⁰` is an isomorphism onto {lit}`U'`. Here {lit}`ī'` is
{name}`Submodule.liftQ`, lifting {lit}`i'` through the quotient by {lit}`U⁰`; the
required {lit}`U⁰ ≤ null i'` is part (a), {name}`exercise_3F_31a`. -/
theorem exercise_3F_31c [Finite F V] (U : Submodule F V) :
    Function.Bijective
      (U.dualAnnihilator.liftQ U.subtype.dualMap (exercise_3F_31a U).ge) := by
  sorry

/-- 3F.32 (a) {lit}`Λ : V → V''` is linear. -/
def exercise_3F_32_Lambda : V →ₗ[F] Module.Dual F (Module.Dual F V) where
  toFun v := { toFun := fun φ => φ v
               map_add' := sorry
               map_smul' := sorry }
  map_add' u v := by sorry
  map_smul' a v := by sorry

/-- 3F.32 (b) -/
theorem exercise_3F_32b (T : V →ₗ[F] V) :
    T.dualMap.dualMap ∘ₗ exercise_3F_32_Lambda =
      exercise_3F_32_Lambda ∘ₗ T := by
  sorry

/-- 3F.32 (c) {lit}`Λ` is an isomorphism when {lit}`V` is finite-dimensional. -/
theorem exercise_3F_32c [Finite F V] :
    Function.Bijective (exercise_3F_32_Lambda (F := F) (V := V)) := by
  sorry

/-- 3F.33 (a) -/
theorem exercise_3F_33a (U : Submodule F V) :
    Function.Injective U.mkQ.dualMap := by
  sorry

/-- 3F.33 (b) -/
theorem exercise_3F_33b (U : Submodule F V) :
    LinearMap.range U.mkQ.dualMap = U.dualAnnihilator := by
  sorry

/-- 3F.33 (c) -/
theorem exercise_3F_33c (U : Submodule F V) :
    Function.Bijective U.mkQ.dualMap.rangeRestrict := by
  sorry

end LADR.Section_3F
