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
  -- If {lit}`φ ≠ 0` then {lit}`φ v ≠ 0` for some {lit}`v`, and given a target
  -- {lit}`y` linearity gives {lit}`φ ((y / φ v) • v) = (y / φ v) * φ v = y`.
  rcases eq_or_ne φ 0 with h | h
  · exact Or.inr h
  refine Or.inl ?_
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (LinearMap.ext fun x => by simp [hcon x])
  intro y
  exact ⟨(y / φ v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩

/-- 3F.2 -/
example : ∃ φ₁ φ₂ φ₃ : Module.Dual ℝ (↥(Set.Icc (0:ℝ) 1) → ℝ),
    φ₁ ≠ φ₂ ∧ φ₁ ≠ φ₃ ∧ φ₂ ≠ φ₃ := by
  -- Evaluation at {lit}`0`, {lit}`1/2` and {lit}`1`. These three functionals
  -- already differ on the function {lit}`x ↦ x`, whose values at those three
  -- points are {lit}`0`, {lit}`1/2` and {lit}`1`.
  refine ⟨LinearMap.proj ⟨0, by norm_num⟩, LinearMap.proj ⟨1/2, by norm_num⟩,
    LinearMap.proj ⟨1, by norm_num⟩, ?_, ?_, ?_⟩ <;>
  · intro hcon
    have := congrArg (fun ψ : Module.Dual ℝ (↥(Set.Icc (0:ℝ) 1) → ℝ) =>
      ψ (fun x => (x : ℝ))) hcon
    norm_num at this

/-- 3F.3 -/
theorem exercise_3F_3 (v : V) (hv : v ≠ 0) :
    ∃ φ : Module.Dual F V, φ v = 1 := by
  classical
  -- {lit}`{v}` is linearly independent, so it extends to a basis of {lit}`V`;
  -- the dual basis vector at the index {lit}`v` sends {lit}`v` to {lit}`1`.
  have hli : LinearIndepOn F id ({v} : Set V) := (linearIndepOn_singleton_iff F).mpr hv
  have hmem : v ∈ hli.extend (Set.subset_univ _) := Module.Basis.subset_extend hli rfl
  set b := Module.Basis.extend hli with hb
  have hbv : b ⟨v, hmem⟩ = v := Module.Basis.extend_apply_self hli _
  refine ⟨b.coord ⟨v, hmem⟩, ?_⟩
  have hone : b.coord ⟨v, hmem⟩ (b ⟨v, hmem⟩) = 1 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  rwa [hbv] at hone

/-- Separation of a point from a subspace: if {lit}`x ∉ U` there is a functional
vanishing on {lit}`U` with {lit}`φ x = 1`. Take a basis {lit}`s` of {lit}`U`,
adjoin {lit}`x` (still linearly independent, as {lit}`x ∉ U = span s`), extend to
a basis {lit}`b` of {lit}`V`, and take the dual basis vector at the index
{lit}`x`: it kills every element of {lit}`s`, hence all of {lit}`U`, and sends
{lit}`x` to {lit}`1`. This is the construction behind 3F.4 and 3F.20. -/
private lemma exists_dual_apply_eq_one_of_notMem
    (U : Submodule F V) {x : V} (hx : x ∉ U) :
    ∃ φ : Module.Dual F V, (∀ u ∈ U, φ u = 0) ∧ φ x = 1 := by
  classical
  obtain ⟨s, hsU, hspan, hli⟩ := exists_linearIndependent F (U : Set V)
  rw [Submodule.span_eq] at hspan
  have hli' : LinearIndepOn F id s := hli
  have hxs : x ∉ Submodule.span F s := by rw [hspan]; exact hx
  have hins : LinearIndepOn F id (insert x s) :=
    linearIndepOn_id_insert_iff.mpr ⟨hli', fun hmem => absurd hmem hxs⟩
  set b := Module.Basis.extend hins with hb
  have hxmem : x ∈ hins.extend (Set.subset_univ _) :=
    Module.Basis.subset_extend hins (Set.mem_insert _ _)
  have hbx : b ⟨x, hxmem⟩ = x := Module.Basis.extend_apply_self hins _
  refine ⟨b.coord ⟨x, hxmem⟩, ?_, ?_⟩
  · -- {lit}`φ` kills each basis vector of {lit}`U`, hence {lit}`U = span s`.
    have hker : U ≤ LinearMap.ker (b.coord ⟨x, hxmem⟩) := by
      rw [← hspan, Submodule.span_le]
      intro y hy
      have hyE : y ∈ hins.extend (Set.subset_univ _) :=
        Module.Basis.subset_extend hins (Set.mem_insert_of_mem _ hy)
      have hby : b ⟨y, hyE⟩ = y := Module.Basis.extend_apply_self hins _
      have hne : (⟨y, hyE⟩ : hins.extend (Set.subset_univ _)) ≠ ⟨x, hxmem⟩ := by
        intro hEq
        have hyx : y = x := by simpa using congrArg Subtype.val hEq
        exact hx (hyx ▸ hsU hy)
      have hzero : b.coord ⟨x, hxmem⟩ (b ⟨y, hyE⟩) = 0 := by
        rw [Module.Basis.coord_apply, Module.Basis.repr_self,
          Finsupp.single_eq_of_ne (Ne.symm hne)]
      rw [hby] at hzero
      simpa only [SetLike.mem_coe, LinearMap.mem_ker] using hzero
    exact fun u hu => hker hu
  · have hone : b.coord ⟨x, hxmem⟩ (b ⟨x, hxmem⟩) = 1 := by
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
    rwa [hbx] at hone

/-- 3F.4 -/
theorem exercise_3F_4 (U : Submodule F V) (hU : U ≠ ⊤) :
    ∃ φ : Module.Dual F V, (∀ u ∈ U, φ u = 0) ∧ φ ≠ 0 := by
  -- take a basis of U, and extend it to a basis of V.
  -- take the last vector x from the basis (which is not in U)
  -- and use it to define φ from the dual basis.
  -- by construction, φ is zero on U and nonzero on x, so φ ≠ 0.
  obtain ⟨x, hx⟩ : ∃ x : V, x ∉ U := by
    by_contra hcon
    push Not at hcon
    exact hU (eq_top_iff.mpr fun v _ => hcon v)
  obtain ⟨φ, hφU, hφx⟩ := exists_dual_apply_eq_one_of_notMem U hx
  refine ⟨φ, hφU, ?_⟩
  intro h0
  rw [h0] at hφx
  simp at hφx

/-- 3F.5 Suppose {lit}`w₁, …, wₘ` is a basis of {lit}`range T`. Expanding each
{lit}`Tv` in this basis as {lit}`Tv = φ₁(v)w₁ + ⋯ + φₘ(v)wₘ` defines functions
{lit}`φᵢ : V → F`; show that each {lit}`φᵢ` is a linear functional on {lit}`V`. -/
theorem exercise_3F_5 (T : V →ₗ[F] W) {m : ℕ} (w : Fin m → W)
    (hwmem : ∀ i, w i ∈ LinearMap.range T)
    (hw : IsBasis F (fun i => (⟨w i, hwmem i⟩ : LinearMap.range T)))
    (φ : Fin m → V → F) (hφ : ∀ v, T v = ∑ i, φ i v • w i) :
    ∀ i, IsLinearMap F (φ i) := by
  classical
  -- Expansion in a basis is unique, so {lit}`φᵢ v` must be the {lit}`i`-th
  -- coordinate of {lit}`T v` in the basis {lit}`w₁, …, wₘ` of {lit}`range T`;
  -- that is, {lit}`φᵢ = (coordinate i) ∘ equivFun ∘ T`, a composition of linear
  -- maps. Additivity and homogeneity of each {lit}`φᵢ` then follow from those
  -- of {lit}`T`, exactly as in the informal argument: applying uniqueness to
  -- {lit}`T (u + v) = T u + T v` and {lit}`T (c • v) = c • T v`.
  set b := hw.toModuleBasis with hb
  have hbi : ∀ i, ((b i : LinearMap.range T) : W) = w i := fun i => by
    rw [hb, IsBasis.toModuleBasis_apply hw i]
  have key : ∀ (v : V) (i : Fin m), φ i v = b.equivFun (T.rangeRestrict v) i := by
    intro v
    have hsum : b.equivFun.symm (fun i => φ i v) = T.rangeRestrict v := by
      apply Subtype.ext
      rw [Module.Basis.equivFun_symm_apply]
      simp only [Submodule.coe_sum, SetLike.val_smul, hbi]
      exact (hφ v).symm
    intro i
    rw [← hsum, LinearEquiv.apply_symm_apply]
  refine fun i => ⟨fun x y => ?_, fun c x => ?_⟩
  · simp only [key, map_add, Pi.add_apply]
  · simp only [key, map_smul, Pi.smul_apply]

/-- 3F.6 -/
theorem exercise_3F_6 (φ β : Module.Dual F V) :
    LinearMap.ker φ ≤ LinearMap.ker β ↔
      ∃ c : F, β = c • φ := by
  -- The dimension-counting argument needs {lit}`V` finite-dimensional, which
  -- the statement does not assume, so we run the same idea directly. If
  -- {lit}`φ = 0` then {lit}`ker φ = V`, forcing {lit}`β = 0 = 0 • φ`. Otherwise
  -- normalize a vector to {lit}`φ v = 1`; every {lit}`x` splits as
  -- {lit}`x = (x − φ(x)v) + φ(x)v` with the first summand in
  -- {lit}`ker φ ≤ ker β`, so {lit}`β x = φ(x) β v`, i.e. {lit}`β = (β v) • φ`.
  constructor
  · intro h
    rcases eq_or_ne φ 0 with hφ | hφ
    · refine ⟨0, ?_⟩
      ext x
      have hx : x ∈ LinearMap.ker φ := by simp [hφ]
      simpa using h hx
    obtain ⟨v, hv⟩ : ∃ v, φ v = 1 := by
      obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hφ (LinearMap.ext fun x => by simp [hcon x])
      exact ⟨(φ u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
    refine ⟨β v, ?_⟩
    ext x
    have hmem : x - φ x • v ∈ LinearMap.ker φ := by
      simp [LinearMap.mem_ker, map_sub, map_smul, hv]
    have h0 : β x - φ x * β v = 0 := by
      simpa [map_sub, map_smul, smul_eq_mul] using h hmem
    rw [LinearMap.smul_apply, smul_eq_mul, ← sub_eq_zero, ← h0]
    ring
  · rintro ⟨c, rfl⟩ x hx
    rw [LinearMap.mem_ker] at hx
    simp [LinearMap.mem_ker, hx]

/-- 3F.7 -/
theorem exercise_3F_7 {m : ℕ} (Vi : Fin m → Type*)
    [∀ i, AddCommGroup (Vi i)] [∀ i, Module F (Vi i)] :
    Nonempty (Module.Dual F ((i : Fin m) → Vi i) ≃ₗ[F]
              ((i : Fin m) → Module.Dual F (Vi i))) := by
  -- A functional on the product is the sum of its restrictions to the factors,
  -- {lit}`φ(v₁, …, vₘ) = φ₁(v₁) + ⋯ + φₘ(vₘ)`, and this correspondence is a
  -- linear isomorphism: it is {name}`LinearMap.lsum` (read backwards).
  exact ⟨(LinearMap.lsum F Vi F).symm⟩

/-- 3F.8 The maps {lit}`Γ(u) = (φ₁(u), …, φₙ(u))` and {lit}`Λ(a) = ∑ aᵢvᵢ`
are inverses of each other. -/
theorem exercise_3F_8 {n : ℕ} (v : Fin n → V) (hv : IsBasis F v) :
    let Γ := fun u : V => fun j => hv.toModuleBasis.dualBasis j u
    let Λ := fun a : Fin n → F => ∑ i, a i • v i
    Function.LeftInverse Λ Γ ∧ Function.RightInverse Λ Γ := by
  -- compute Γ Λ and Λ Γ directly to show they are I
  intro Γ Λ
  have hvb : ∀ i, hv.toModuleBasis i = v i := IsBasis.toModuleBasis_apply hv
  constructor
  · -- {lit}`Λ(Γ u) = ∑ⱼ φⱼ(u) vⱼ = u` is 3.114.
    intro u
    exact (dualBasis_gives_coefficients v hv u).symm
  · -- {lit}`Γ(Λ a) = a` because the coefficients of a basis expansion are unique.
    intro a
    funext j
    show hv.toModuleBasis.dualBasis j (∑ i, a i • v i) = a j
    have hsum : (∑ i, a i • v i) = hv.toModuleBasis.equivFun.symm a := by
      rw [Module.Basis.equivFun_symm_apply]
      simp only [hvb]
    rw [Module.Basis.dualBasis_apply, hsum, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]

/-- Taylor coefficients as iterated derivatives: {lit}`p⁽ᵏ⁾(r) = k! · aₖ`, where
{lit}`aₖ` is the coefficient of {lit}`(x − r)ᵏ` in the expansion of {lit}`p`
around {lit}`r`, i.e. the {lit}`k`-th coefficient of {name}`Polynomial.taylor`.
This is the computational content of exercises 3F.9 and 3F.10 (b). -/
private lemma taylor_coeff_of_iterate_derivative (p : Polynomial ℝ) (k : ℕ) (r : ℝ) :
    (Polynomial.derivative^[k] p).eval r / (k.factorial : ℝ)
      = (Polynomial.taylor r p).coeff k := by
  have h : Polynomial.derivative^[k] p = (k.factorial) • (Polynomial.hasseDeriv k p) := by
    rw [← Polynomial.factorial_smul_hasseDeriv]; rfl
  have heval : (Polynomial.derivative^[k] p).eval r
      = (k.factorial : ℝ) * (Polynomial.taylor r p).coeff k := by
    rw [h, Polynomial.taylor_coeff]
    simp [nsmul_eq_mul]
  rw [heval]
  field_simp

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
  -- Applying {lit}`φₖ` to {lit}`xⁱ` gives {lit}`1` when {lit}`i = k`, and
  -- {lit}`0` otherwise (for {lit}`i > k` the surviving power vanishes at
  -- {lit}`0`, for {lit}`i < k` the iterated derivative is already {lit}`0`).
  -- Packaged: {lit}`φₖ p = pₖ`, the {lit}`k`-th coefficient of {lit}`p`, so
  -- {lit}`φ` is the dual basis of the monomial basis, hence a basis by 3.116.
  have hdual : φ =
      (LADR.Section_2B.isBasis_polyMono (F := ℝ) (m + 1)).toModuleBasis.dualBasis := by
    funext k
    ext p
    rw [hφ k p, Module.Basis.dualBasis_apply, LADR.Section_2B.isBasis_polyMono_repr,
      taylor_coeff_of_iterate_derivative, Polynomial.taylor_zero]
  rw [hdual]
  exact isBasis_dualBasis _ (LADR.Section_2B.isBasis_polyMono (F := ℝ) (m + 1))

/-- 3F.10 (a) {lit}`1, x − 5, …, (x − 5)ᵐ` is a basis of {lit}`𝒫ₘ(ℝ)`. -/
theorem exercise_3F_10a (m : ℕ)
    (e : Fin (m + 1) → Polynomial.degreeLT ℝ (m + 1))
    (he : ∀ k, (e k : Polynomial ℝ) = (Polynomial.X - 5) ^ (k : ℕ)) :
    IsBasis ℝ e := by
  -- Instead of the degree argument, note that {lit}`p ↦ p(x − 5)` is a linear
  -- automorphism of {lit}`𝒫ₘ(ℝ)` ({name}`Polynomial.taylorLinearEquiv`), and it
  -- carries the monomial basis {lit}`1, x, …, xᵐ` to {lit}`1, x − 5, …,
  -- (x − 5)ᵐ`; the image of a basis under an isomorphism is a basis.
  set B := (Polynomial.degreeLT.basis ℝ (m + 1)).map
    (Polynomial.taylorLinearEquiv (-5 : ℝ) (m + 1)) with hB
  have hBe : ⇑B = e := by
    funext k
    apply Subtype.ext
    have hco : ((B k : Polynomial.degreeLT ℝ (m + 1)) : Polynomial ℝ)
        = Polynomial.taylor (-5 : ℝ)
            ((Polynomial.degreeLT.basis ℝ (m + 1) k : Polynomial ℝ)) := rfl
    have h5 : (Polynomial.C (-5 : ℝ)) = -5 := by
      rw [Polynomial.C_neg, map_ofNat]
    rw [he k, hco, Polynomial.degreeLT.basis_val, Polynomial.taylor_X_pow, h5,
      ← sub_eq_add_neg]
  rw [← hBe]
  exact ⟨B.linearIndependent, B.span_eq⟩

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
  -- Same computation as 3F.9, now centred at {lit}`5`: {lit}`p⁽ᵏ⁾(5)/k!` is the
  -- {lit}`k`-th Taylor coefficient of {lit}`p` at {lit}`5`, and applying it to
  -- {lit}`(x − 5)ʲ` gives {lit}`1` if {lit}`j = k` and {lit}`0` otherwise —
  -- exactly the defining property of the dual basis.
  intro k
  refine Module.Basis.ext hv.toModuleBasis (fun j => ?_)
  rw [Module.Basis.dualBasis_apply_self, LADR.Section_2B.IsBasis.toModuleBasis_apply,
    hφ k (e j), taylor_coeff_of_iterate_derivative, he j]
  rw [show Polynomial.taylor (5 : ℝ) ((Polynomial.X - 5) ^ (j : ℕ)) = Polynomial.X ^ (j : ℕ) by
    simp [Polynomial.taylor_apply, Polynomial.pow_comp, Polynomial.sub_comp, map_ofNat]]
  rw [Polynomial.coeff_X_pow]
  simp [Fin.val_eq_val, eq_comm]

/-- 3F.11 -/
theorem exercise_3F_11 {n : ℕ} (v : Fin n → V) (hv : IsBasis F v)
    (ψ : Module.Dual F V) :
    ψ = ∑ j, ψ (v j) • hv.toModuleBasis.dualBasis j := by
  -- Enough to check both sides on each {lit}`vₖ`:
  -- {lit}`∑ⱼ ψ(vⱼ) φⱼ(vₖ) = ψ(vₖ)`, since {lit}`φⱼ(vₖ) = δⱼₖ`.
  refine Module.Basis.ext hv.toModuleBasis (fun k => ?_)
  rw [LADR.Section_2B.IsBasis.toModuleBasis_apply]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    dualBasis_apply_self, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-! 3F.12 (a) and (b) are exactly the algebraic properties of dual maps 3.120
(a) {lit}`(S + T)' = S' + T'` and (b) {lit}`(λT)' = λT'`, already proved above. -/

/-- 3F.13 -/
example : (LinearMap.id : V →ₗ[F] V).dualMap = LinearMap.id := by
  -- I' φ v = φ (I v) = φ v = (I φ) v
  ext φ v
  rw [LinearMap.dualMap_apply, LinearMap.id_apply, LinearMap.id_apply]

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
  -- direct check: {lit}`T'(φⱼ)(v) = φⱼ(Tv)` is the {lit}`j`-th row of {lit}`T`.
  have hdual : ∀ (n : ℕ) (j : Fin n) (x : Fin n → ℝ),
      (Pi.basisFun ℝ (Fin n)).dualBasis j x = x j := by
    intro n j x
    simp [Pi.basisFun_repr]
  refine ⟨fun v => ?_, fun v => ?_, ?_, ?_⟩
  · rw [LinearMap.dualMap_apply, hdual, hT]; simp
  · rw [LinearMap.dualMap_apply, hdual, hT]; simp
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.dualMap_apply, hdual, hT]
    simp
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.dualMap_apply, hdual, hT]
    simp

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
  -- direct calculation T'φ = φ ∘ T:
  -- {lit}`T'(φ)(p) = φ(Tp) = (x²p + p″)′(4) = (2xp + x²p′ + p‴)(4)`.
  intro p
  rw [LinearMap.dualMap_apply, hφ, hT]
  simp [Polynomial.derivative_mul, mul_comm]
  ring

/-- 3F.15 (b) For {lit}`φ(p) = ∫₀¹ p`, {lit}`(T'(φ))(x³) = 19/6`. -/
theorem exercise_3F_15b (T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ)
    (hT : ∀ p, T p =
      Polynomial.X ^ 2 * p + Polynomial.derivative (Polynomial.derivative p))
    (φ : Module.Dual ℝ (Polynomial ℝ))
    (hφ : ∀ p, φ p = ∫ x in (0:ℝ)..1, p.eval x) :
    T.dualMap φ (Polynomial.X ^ 3) = 19 / 6 := by
  -- direct calculation T'φ = φ ∘ T: {lit}`T(x³) = x⁵ + 6x`, and
  -- {lit}`∫₀¹ (x⁵ + 6x) = 1/6 + 3 = 19/6` by the fundamental theorem of
  -- calculus with the antiderivative {lit}`Q = x⁶/6 + 3x²`.
  set Q : Polynomial ℝ := Polynomial.C (1/6 : ℝ) * Polynomial.X ^ 6 + 3 * Polynomial.X ^ 2 with hQ
  rw [LinearMap.dualMap_apply, hφ, hT]
  rw [intervalIntegral.integral_congr
    (g := fun x => (Polynomial.derivative Q).eval x) (fun x _ => by simp [hQ]; ring)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => Q.hasDerivAt x)
    ((Polynomial.continuous (Polynomial.derivative Q)).intervalIntegrable 0 1)]
  simp [hQ]
  norm_num

/-- 3F.16 -/
theorem exercise_3F_16 [Finite F W] (T : V →ₗ[F] W) :
    T.dualMap = 0 ↔ T = 0 := by
  -- If {lit}`Tv ≠ 0` for some {lit}`v`, exercise 3F.3 gives a functional
  -- {lit}`ξ` with {lit}`ξ(Tv) = 1`, so {lit}`T'(ξ)(v) = 1` and {lit}`T' ≠ 0`.
  -- Conversely {lit}`T = 0` makes {lit}`T'(ξ) = ξ ∘ T = 0` for every {lit}`ξ`.
  constructor
  · intro h
    ext v
    by_contra hv
    obtain ⟨ξ, hξ⟩ := exercise_3F_3 (F := F) (T v) hv
    have h2 : ξ (T v) = 0 := by
      rw [← LinearMap.dualMap_apply, h]; rfl
    rw [hξ] at h2
    exact one_ne_zero h2
  · rintro rfl
    ext ξ v
    simp

/-- 3F.17 -/
theorem exercise_3F_17 [Finite F V] [Finite F W] (T : V →ₗ[F] W) :
    LADR.Section_3D.IsInvertible T ↔ LADR.Section_3D.IsInvertible T.dualMap := by
  -- already proved surj T iff inj T', and for finite dim, inj = suj = inv for both and T and T'
  rw [LADR.Section_3D.isInvertible_iff_bijective,
    LADR.Section_3D.isInvertible_iff_bijective]
  constructor
  · rintro ⟨hinj, hsurj⟩
    exact ⟨(surjective_iff_dualMap_injective T).mp hsurj,
      (injective_iff_dualMap_surjective T).mp hinj⟩
  · rintro ⟨hinj, hsurj⟩
    exact ⟨(injective_iff_dualMap_surjective T).mpr hsurj,
      (surjective_iff_dualMap_injective T).mpr hinj⟩

/-- 3F.18 -/
theorem exercise_3F_18 [Finite F V] [Finite F W] :
    IsLinearMap F (fun T: V →ₗ[F] W => T.dualMap) ∧
    Function.Bijective (fun T: V →ₗ[F] W => T.dualMap) := by
  -- exactly exercise 12 content
  have hlin : IsLinearMap F (fun T : V →ₗ[F] W => T.dualMap) := by
    constructor
    · intro S T
      ext φ v
      simp [LinearMap.dualMap_apply]
    · intro c T
      ext φ v
      simp [LinearMap.dualMap_apply]
  -- since map between fin dim spaces of dim V * dim W, enough to show inj
  -- by 16, the map is injective.
  have hinj : Function.Injective (fun T : V →ₗ[F] W => T.dualMap) := by
    intro S T hST
    have hST' : S.dualMap = T.dualMap := hST
    have h0 : (S - T).dualMap = 0 := by
      ext φ v
      have hv : S.dualMap φ v = T.dualMap φ v := by rw [hST']
      rw [LinearMap.dualMap_apply] at hv
      rw [LinearMap.dualMap_apply] at hv
      simp [LinearMap.dualMap_apply, LinearMap.sub_apply, map_sub, hv]
    exact sub_eq_zero.mp ((exercise_3F_16 (S - T)).mp h0)
  have hdim : finrank F (V →ₗ[F] W)
      = finrank F (Module.Dual F W →ₗ[F] Module.Dual F V) := by
    rw [LADR.Section_3D.finrank_linearMap, LADR.Section_3D.finrank_linearMap,
      finrank_dual_eq_finrank, finrank_dual_eq_finrank, mul_comm]
  exact ⟨hlin, hinj,
    (LADR.Section_3D.injective_iff_surjective hdim (IsLinearMap.mk' _ hlin)).mp hinj⟩

/-- 3F.19 -/
theorem exercise_3F_19 (U : Submodule F V) :
    U.dualAnnihilator = {φ : Module.Dual F V | (U : Set V) ⊆ LinearMap.ker φ} := by
  ext x
  constructor
  · intro h
    simp at h ⊢
    intro u hu
    specialize h u hu
    exact h
  · intro h
    simp at h ⊢
    intro u hu
    exact h hu

/-- 3F.20 -/
theorem exercise_3F_20 [Finite F V] (U : Submodule F V) :
    (U : Set V) =
      {v : V | ∀ φ ∈ U.dualAnnihilator, φ v = 0} := by
  ext x
  constructor
  · intro hx u hu
    simp at hu
    specialize hu x hx
    exact hu
  · intro h
    -- by contra, assume there exists a x ∉ U, s.t. φ x = 0 for all φ in Uo
    -- construct a φ s.t. φ x = 1, and φ U = 0, by taking a basis for U,
    -- extending x, and then construct by sending all but x to 0, thus φ U = 0.
    -- but now φ is in Uo, so φ x = 0, contradiction
    by_contra hx
    have hxU : x ∉ U := by simpa using hx
    obtain ⟨φ, hφU, hφx⟩ := exists_dual_apply_eq_one_of_notMem U hxU
    have h0 : φ x = 0 := h φ ((Submodule.mem_dualAnnihilator φ).mpr hφU)
    rw [hφx] at h0
    exact one_ne_zero h0

/-! The double annihilator. {lit}`U⁰⁰` is a subspace of {lit}`V''`, so it is
compared with {lit}`U` through the evaluation map {lit}`v ↦ (φ ↦ φ v)`: the
result below says {lit}`U⁰⁰` is exactly the image of {lit}`U` under it. Together
with injectivity of evaluation this transports {lit}`≤`, {lit}`⊓` and {lit}`⊔`
between {lit}`V` and {lit}`V''`, which is how 3F.21 (a) and 3F.22 (b) are proved
below. -/

/-- Evaluation is injective: by 3F.3 a nonzero vector is not killed by every
functional. -/
theorem eval_injective : Function.Injective (Module.Dual.eval F V) := by
  intro x y hxy
  by_contra hne
  obtain ⟨φ, hφ⟩ := exercise_3F_3 (F := F) (x - y) (sub_ne_zero.mpr hne)
  have h1 : φ x = φ y := congrArg (fun Ξ : Module.Dual F (Module.Dual F V) => Ξ φ) hxy
  have h2 : φ (x - y) = 0 := by rw [map_sub, h1, sub_self]
  rw [hφ] at h2
  exact one_ne_zero h2

/-- In finite dimensions evaluation is also surjective, since
{lit}`dim V'' = dim V' = dim V` (3.111) and an injective map between spaces of
equal dimension is surjective (3.65). -/
theorem eval_surjective [Finite F V] : Function.Surjective (Module.Dual.eval F V) := by
  have hdim : finrank F V = finrank F (Module.Dual F (Module.Dual F V)) := by
    rw [finrank_dual_eq_finrank, finrank_dual_eq_finrank]
  exact (LADR.Section_3D.injective_iff_surjective hdim
    (Module.Dual.eval F V)).mp eval_injective

/-- {lit}`U⁰⁰` is the image of {lit}`U` under evaluation. The inclusion
{lit}`⊆` is immediate; the reverse one writes {lit}`Ξ ∈ U⁰⁰` as {lit}`Ξ = eval v`
and then uses 3F.20 to place {lit}`v` in {lit}`U`. -/
theorem map_eval_eq_dualAnnihilator_dualAnnihilator [Finite F V] (U : Submodule F V) :
    U.map (Module.Dual.eval F V) = U.dualAnnihilator.dualAnnihilator := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro φ hφ
    exact (Submodule.mem_dualAnnihilator φ).mp hφ v hv
  · intro Ξ hΞ
    obtain ⟨v, rfl⟩ := eval_surjective Ξ
    refine Submodule.mem_map_of_mem ?_
    have hv : v ∈ {v : V | ∀ φ ∈ U.dualAnnihilator, φ v = 0} := by
      intro φ hφ
      exact (Submodule.mem_dualAnnihilator (Module.Dual.eval F V v)).mp hΞ φ hφ
    rw [← exercise_3F_20 U] at hv
    exact hv

/-- 3F.21 (a) -/
theorem exercise_3F_21a [Finite F V] (U W : Submodule F V) :
    W.dualAnnihilator ≤ U.dualAnnihilator ↔ U ≤ W := by
  -- <= obvious
  -- => use double dual: annihilate once more to get {lit}`U⁰⁰ ≤ W⁰⁰`, i.e.
  -- {lit}`eval '' U ≤ eval '' W`, and cancel the injective evaluation map.
  constructor
  · intro h
    have h2 : U.dualAnnihilator.dualAnnihilator ≤ W.dualAnnihilator.dualAnnihilator := by
      intro Ξ hΞ
      rw [Submodule.mem_dualAnnihilator] at hΞ ⊢
      exact fun φ hφ => hΞ φ (h hφ)
    rw [← map_eval_eq_dualAnnihilator_dualAnnihilator U,
      ← map_eval_eq_dualAnnihilator_dualAnnihilator W] at h2
    exact (Submodule.map_le_map_iff_of_injective eval_injective _ _).mp h2
  · intro h φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ ⊢
    exact fun u hu => hφ u (h hu)

/-- 3F.21 (b) -/
theorem exercise_3F_21b [Finite F V] (U W : Submodule F V) :
    W.dualAnnihilator = U.dualAnnihilator ↔ U = W := by
  -- same as a), applied to both inclusions
  constructor
  · intro h
    exact le_antisymm ((exercise_3F_21a U W).mp h.le) ((exercise_3F_21a W U).mp h.ge)
  · rintro rfl
    rfl

/-- 3F.22 (a) -/
theorem exercise_3F_22a [Finite F V] (U W : Submodule F V) :
    (U ⊔ W).dualAnnihilator =
      U.dualAnnihilator ⊓ W.dualAnnihilator := by
  -- φ in (U ⊔ W).dualAnnihilator iff φ(au + bw) = 0
  -- so φ (u) = 0 and φ(w) = 0 iff φ in U.dualAnnihilator and W.dualAnnihilator
  ext φ
  simp only [Submodule.mem_inf, Submodule.mem_dualAnnihilator]
  constructor
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
      fun w hw => h w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨hU, hW⟩ x hx
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hU u hu, hW w hw, add_zero]

/-- 3F.22 (b) -/
theorem exercise_3F_22b [Finite F V] (U W : Submodule F V) :
    (U ⊓ W).dualAnnihilator =
      U.dualAnnihilator ⊔ W.dualAnnihilator := by
  -- Both sides live in {lit}`V'`, so by (b) of 3F.21 applied there it is enough
  -- that they have the same annihilator in {lit}`V''`. By (a) of 3F.22 in
  -- {lit}`V'` that annihilator is {lit}`U⁰⁰ ⊓ W⁰⁰ = eval '' U ⊓ eval '' W`,
  -- which is {lit}`eval '' (U ⊓ W) = (U ⊓ W)⁰⁰` since evaluation is injective.
  refine (exercise_3F_21b (U ⊓ W).dualAnnihilator
    (U.dualAnnihilator ⊔ W.dualAnnihilator)).mp ?_
  rw [exercise_3F_22a U.dualAnnihilator W.dualAnnihilator,
    ← map_eval_eq_dualAnnihilator_dualAnnihilator U,
    ← map_eval_eq_dualAnnihilator_dualAnnihilator W,
    ← map_eval_eq_dualAnnihilator_dualAnnihilator (U ⊓ W),
    Submodule.map_inf _ eval_injective]

/-- 3F.22 (a) for an arbitrary family of subspaces: a functional kills a sum of
subspaces exactly when it kills each summand. -/
theorem dualAnnihilator_iSup {ι : Sort*} (U : ι → Submodule F V) :
    (⨆ i, U i).dualAnnihilator = ⨅ i, (U i).dualAnnihilator := by
  ext ψ
  simp only [Submodule.mem_iInf, Submodule.mem_dualAnnihilator]
  constructor
  · exact fun h i v hv => h v (Submodule.mem_iSup_of_mem i hv)
  · intro h v hv
    have hle : (⨆ i, U i) ≤ LinearMap.ker ψ :=
      iSup_le fun i x hx => LinearMap.mem_ker.mpr (h i x hx)
    exact hle hv

/-- 3F.22 (b) for a nonempty family, by the same argument as the two-subspace
case: cancel annihilators in {lit}`V'` (3F.21 (b)) after computing the
annihilator of the right-hand side in {lit}`V''`. -/
theorem dualAnnihilator_iInf [Finite F V] {ι : Sort*} [Nonempty ι]
    (U : ι → Submodule F V) :
    (⨅ i, U i).dualAnnihilator = ⨆ i, (U i).dualAnnihilator := by
  refine (exercise_3F_21b (⨅ i, U i).dualAnnihilator
    (⨆ i, (U i).dualAnnihilator)).mp ?_
  rw [dualAnnihilator_iSup]
  simp only [← map_eval_eq_dualAnnihilator_dualAnnihilator]
  exact (Submodule.map_iInf _ eval_injective).symm

/-- {lit}`(null φ)⁰ = span(φ)`: a functional vanishing on {lit}`null φ` is a
scalar multiple of {lit}`φ` by 3F.6. -/
theorem dualAnnihilator_ker (φ : Module.Dual F V) :
    (LinearMap.ker φ).dualAnnihilator = Submodule.span F {φ} := by
  apply le_antisymm
  · intro ψ hψ
    rw [Submodule.mem_dualAnnihilator] at hψ
    have hker : LinearMap.ker φ ≤ LinearMap.ker ψ :=
      fun v hv => LinearMap.mem_ker.mpr (hψ v hv)
    obtain ⟨c, rfl⟩ := (exercise_3F_6 φ ψ).mp hker
    exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
  · rw [Submodule.span_le]
    rintro _ rfl
    rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
    intro v hv
    exact hv

/-- 3F.23  -/
theorem exercise_3F_23 [Finite F V] {m : ℕ} (φ : Fin m → Module.Dual F V) :
    Submodule.span F (Set.range φ) = (⨅ i, LinearMap.ker (φ i)).dualAnnihilator ∧
    ((⨅ i, LinearMap.ker (φ i)).dualAnnihilator : Set (Module.Dual F V)) =
        {ψ | (⨅ i, LinearMap.ker (φ i)) ≤ LinearMap.ker ψ} := by
  -- a = b, by applying 22b) and then (nullφ)0 = span φ,
  -- b = c, just exercise 19
  constructor
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [iInf_of_isEmpty]
    · have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
      rw [dualAnnihilator_iInf]
      simp only [dualAnnihilator_ker]
      rw [← Set.iUnion_singleton_eq_range, Submodule.span_iUnion]
  · rw [exercise_3F_19]
    ext ψ
    simp [SetLike.le_def, Set.subset_def, Set.mem_iInter, LinearMap.mem_ker]

/-- 3F.24 -/
theorem exercise_3F_24 [Finite F V] {m : ℕ} (v : Fin m → V) :
    let Γ := fun (φ : Module.Dual F V) (i : Fin m) => φ (v i)
    (Spans F v ↔ Function.Injective Γ) ∧
    (LinearIndependent F v ↔ Function.Surjective Γ) := by
  -- a) span v = V iff (span v)o = Vo = {0} by 21.b)
  -- span v = ∑ span v i , so o takes it to ∩ (span v)o
  -- which is precisely all φ s.t. φ v i = 0 for all i
  -- if empty then such φ ≠ 0 doesn't exist i.e. injective

  -- dim V = n
  -- b) dimension argument
  -- surj iff dim range Γ = m ↔ n - dim ker Γ = m
  -- we showed in a) that ker Γ = (span v)o, so dim ker Γ = n - dim span v
  -- so n - (n - dim span v) = dim span v, thus ↔ dim span v = m
  -- which is same as lin ind.
  intro Γ
  -- bundle {lit}`Γ` as a linear map so that 3.21 and 3.125 apply
  set Γₗ : Module.Dual F V →ₗ[F] (Fin m → F) :=
    { toFun := fun φ i => φ (v i)
      map_add' := by intro φ ψ; funext i; simp
      map_smul' := by intro c φ; funext i; simp } with hΓₗ
  have hΓ : Γ = ⇑Γₗ := rfl
  have hker : LinearMap.ker Γₗ = (Submodule.span F (Set.range v)).dualAnnihilator := by
    ext φ
    rw [LinearMap.mem_ker, Submodule.mem_dualAnnihilator]
    constructor
    · intro h u hu
      have hle : Submodule.span F (Set.range v) ≤ LinearMap.ker φ := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa using congrFun h i
      exact hle hu
    · intro h
      funext i
      simpa using h (v i) (Submodule.subset_span ⟨i, rfl⟩)
  constructor
  · rw [hΓ, LADR.Section_3B.injective_iff_ker_eq_bot, hker,
      dualAnnihilator_eq_bot_iff]
    exact Iff.rfl
  · have hrn := LADR.Section_3B.finrank_ker_add_finrank_range Γₗ
    have hdual := finrank_dualAnnihilator (Submodule.span F (Set.range v))
    have hdimV : finrank F (Module.Dual F V) = finrank F V := finrank_dual_eq_finrank
    have hle : finrank F ↥(Submodule.span F (Set.range v)) ≤ finrank F V :=
      Submodule.finrank_le _
    rw [hker] at hrn
    have hrange : finrank F ↥(LinearMap.range Γₗ)
        = finrank F ↥(Submodule.span F (Set.range v)) := by omega
    rw [hΓ, LADR.Section_3B.surjective_iff_range_eq_top,
      linearIndependent_iff_card_eq_finrank_span]
    constructor
    · intro hind
      refine LADR.Section_2C.subspace_eq_top_of_finrank_eq _ ?_
      rw [hrange, Module.finrank_fin_fun]
      simpa [Set.finrank] using hind.symm
    · intro htop
      have hm : finrank F ↥(LinearMap.range Γₗ) = m := by
        rw [htop, finrank_top, Module.finrank_fin_fun]
      rw [hrange] at hm
      simpa [Set.finrank] using hm.symm

/-- 3F.25 -/
theorem exercise_3F_25 [Finite F V] {m : ℕ} (φ : Fin m → Module.Dual F V) :
    let Γ := fun (v : V) (i : Fin m) => φ i v
    (Spans F φ ↔ Function.Injective Γ) ∧
    (LinearIndependent F φ ↔ Function.Surjective Γ) := by
  -- a) span φ = V' => by 23 (∩ ker φ)o = {0}o
  -- by 21b iff ∩ ker φ = {0}, same as doesn't exist v, s.t. φ i v = 0 for all v
  -- same as injective.

  -- b) similar to 24. dimension argument once we have (ker Γ)o = span φ by a)
  intro Γ
  set Γₗ : V →ₗ[F] (Fin m → F) :=
    { toFun := fun x i => φ i x
      map_add' := by intro x y; funext i; simp
      map_smul' := by intro c x; funext i; simp } with hΓₗ
  have hΓ : Γ = ⇑Γₗ := rfl
  have hker : LinearMap.ker Γₗ = ⨅ i, LinearMap.ker (φ i) := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_iInf]
    constructor
    · intro h i
      simpa using congrFun h i
    · intro h
      funext i
      simpa using h i
  -- 3F.23: {lit}`span(φ₁, …, φₘ) = (null φ₁ ∩ ⋯ ∩ null φₘ)⁰`
  have h23 := (exercise_3F_23 φ).1
  constructor
  · rw [hΓ, LADR.Section_3B.injective_iff_ker_eq_bot, hker]
    show Submodule.span F (Set.range φ) = ⊤ ↔ _
    rw [h23, dualAnnihilator_eq_top_iff]
  · have hrn := LADR.Section_3B.finrank_ker_add_finrank_range Γₗ
    have hdual := finrank_dualAnnihilator (⨅ i, LinearMap.ker (φ i))
    have hspan : finrank F ↥(Submodule.span F (Set.range φ))
        = finrank F V - finrank F ↥(⨅ i, LinearMap.ker (φ i)) := by
      rw [h23]; exact hdual
    have hle : finrank F ↥(⨅ i, LinearMap.ker (φ i)) ≤ finrank F V :=
      Submodule.finrank_le _
    rw [hker] at hrn
    have hrange : finrank F ↥(LinearMap.range Γₗ)
        = finrank F ↥(Submodule.span F (Set.range φ)) := by omega
    rw [hΓ, LADR.Section_3B.surjective_iff_range_eq_top,
      linearIndependent_iff_card_eq_finrank_span]
    constructor
    · intro hind
      refine LADR.Section_2C.subspace_eq_top_of_finrank_eq _ ?_
      rw [hrange, Module.finrank_fin_fun]
      simpa [Set.finrank] using hind.symm
    · intro htop
      have hm : finrank F ↥(LinearMap.range Γₗ) = m := by
        rw [htop, finrank_top, Module.finrank_fin_fun]
      rw [hrange] at hm
      simpa [Set.finrank] using hm.symm

/-- 3F.26 The book's inner set {lit}`{v ∈ V : φ(v) = 0 for every φ ∈ Ω}` is, by the
definition of {name}`Submodule.dualCoannihilator` (see
{name}`Submodule.mem_dualCoannihilator`), exactly {lit}`Ω.dualCoannihilator`. -/
example (Ω : Submodule F (Module.Dual F V)) :
    (Ω.dualCoannihilator : Set V) = {v : V | ∀ φ ∈ Ω, φ v = 0} := by
  ext v; exact Submodule.mem_dualCoannihilator v

theorem exercise_3F_26 [Finite F V] (Ω : Submodule F (Module.Dual F V)) :
    Ω = Ω.dualCoannihilator.dualAnnihilator := by
  -- if we can prove every Ω is Uo for some U, this is just ex.20
  -- we can construct U by Ωo and pushing through the eval map:
  -- {lit}`Ωᶜᵒ` *is* {lit}`Ω⁰` pulled back along evaluation, and evaluation is
  -- surjective, so pushing it forward again returns {lit}`Ω⁰`. That says
  -- {lit}`(Ωᶜᵒ)⁰⁰ = Ω⁰`, and annihilators cancel in {lit}`V'` by 3F.21 (b).
  refine (exercise_3F_21b Ω Ω.dualCoannihilator.dualAnnihilator).mp ?_
  rw [← map_eval_eq_dualAnnihilator_dualAnnihilator Ω.dualCoannihilator]
  exact Submodule.map_comap_eq_of_surjective eval_surjective _

/-- 3F.27 -/
theorem exercise_3F_27
    (T : Polynomial.degreeLT ℝ 6 →ₗ[ℝ] Polynomial.degreeLT ℝ 6)
    (φ : Module.Dual ℝ (Polynomial.degreeLT ℝ 6))
    (hφ : ∀ p, φ p = (p : Polynomial ℝ).eval 8)
    (hT : LinearMap.ker T.dualMap = Submodule.span ℝ {φ}) :
    (LinearMap.range T : Set (Polynomial.degreeLT ℝ 6)) =
      {p : Polynomial.degreeLT ℝ 6 | (p : Polynomial ℝ).eval 8 = 0} := by
  -- same as 29a) just with concrete T and V
  have hrange : LinearMap.range T = LinearMap.ker φ := by
    refine (exercise_3F_21b (LinearMap.range T) (LinearMap.ker φ)).mp ?_
    rw [dualAnnihilator_ker, ← hT, ker_dualMap_eq_range_dualAnnihilator]
  rw [hrange]
  ext p
  simp [LinearMap.mem_ker, hφ]

/-- 3F.28 -/
theorem exercise_3F_28 [Finite F V] {m : ℕ} (φ : Fin m → Module.Dual F V)
    (hφ : LinearIndependent F φ) :
    finrank F ↥(⨅ i, LinearMap.ker (φ i)) = finrank F V - m := by
  -- (⨅ i, LinearMap.ker (φ i))o = span φ i by 23
  -- so (⨅ i, LinearMap.ker (φ i)) = dim V - (⨅ i, LinearMap.ker (φ i))o
  -- = dim V - span φ = dim V - m (because lin ind)
  have h23 := (exercise_3F_23 φ).1
  have hdual := finrank_dualAnnihilator (⨅ i, LinearMap.ker (φ i))
  have hspan : finrank F ↥(Submodule.span F (Set.range φ)) = m := by
    rw [linearIndependent_iff_card_eq_finrank_span] at hφ
    simpa [Set.finrank] using hφ.symm
  rw [h23] at hspan
  have hle : finrank F ↥(⨅ i, LinearMap.ker (φ i)) ≤ finrank F V :=
    Submodule.finrank_le _
  omega

/-- 3F.29 (a) -/
theorem exercise_3F_29a [Finite F V] [Finite F W] (T : V →ₗ[F] W)
    (φ : Module.Dual F W) (hφ : LinearMap.ker T.dualMap = Submodule.span F {φ}) :
    LinearMap.range T = LinearMap.ker φ := by
  -- enough to prove (range T)o = (ker φ)o by ex21
  -- by 23a) (ker φ)o = {φ} and by thoerem in chapter (range T)o = ker T'
  refine (exercise_3F_21b (LinearMap.range T) (LinearMap.ker φ)).mp ?_
  rw [dualAnnihilator_ker, ← hφ, ker_dualMap_eq_range_dualAnnihilator]

/-- 3F.29 (b) -/
theorem exercise_3F_29b [Finite F V] [Finite F W] (T : V →ₗ[F] W)
    (ψ : Module.Dual F V) (hψ : LinearMap.range T.dualMap = Submodule.span F {ψ}) :
    LinearMap.ker T = LinearMap.ker ψ := by
  -- enough to prove (ker T)o = (ker φ)o by ex21
  -- by 23a) (ker φ)o = {φ} and by thoerem in chapter (ker T)o = range T'
  refine (exercise_3F_21b (LinearMap.ker T) (LinearMap.ker ψ)).mp ?_
  rw [dualAnnihilator_ker, ← hψ, range_dualMap_eq_ker_dualAnnihilator]

/-- 3F.30 -/
theorem exercise_3F_30 [Finite F V] {n : ℕ} (phi : Fin n → Module.Dual F V)
    (hphi : IsBasis F phi) :
    ∃ v : Fin n → V, ∃ hv : IsBasis F v,
      ∀ j, hv.toModuleBasis.dualBasis j = phi j := by
  -- use ex 25 with φ, since basis = span + lin ind, Γ is bijection
  -- take v i = Γinv e i, trivially v is basis
  -- φ i (v j) = (Γ (v j))i = (e i) j = 1 iff i = j, thus dual basis
  classical
  set Γₗ : V →ₗ[F] (Fin n → F) :=
    { toFun := fun x i => phi i x
      map_add' := by intro x y; funext i; simp
      map_smul' := by intro c x; funext i; simp } with hΓₗ
  obtain ⟨h25a, h25b⟩ := exercise_3F_25 phi
  have hinj : Function.Injective Γₗ := h25a.mp hphi.2
  have hsurj : Function.Surjective Γₗ := h25b.mp hphi.1
  set E : V ≃ₗ[F] (Fin n → F) := LinearEquiv.ofBijective Γₗ ⟨hinj, hsurj⟩ with hE
  -- {lit}`vₖ = Γ⁻¹ eₖ`, a basis as the image of the standard basis under an iso
  set b : Module.Basis (Fin n) F V := (Pi.basisFun F (Fin n)).map E.symm with hb
  have hv : IsBasis F ⇑b := ⟨b.linearIndependent, b.span_eq⟩
  refine ⟨⇑b, hv, ?_⟩
  intro j
  refine Module.Basis.ext hv.toModuleBasis (fun k => ?_)
  rw [Module.Basis.dualBasis_apply_self, IsBasis.toModuleBasis_apply]
  have hbk : Γₗ (b k) = Pi.single k (1 : F) := by
    rw [hb, Module.Basis.map_apply]
    rw [show (E.symm ((Pi.basisFun F (Fin n)) k)) = E.symm (Pi.single k (1:F)) by
      simp [Pi.basisFun_apply]]
    have hEE : Γₗ (E.symm (Pi.single k (1:F))) = E (E.symm (Pi.single k (1:F))) := rfl
    rw [hEE, LinearEquiv.apply_symm_apply]
  have hval : phi j (b k) = (Pi.single k (1:F) : Fin n → F) j := by
    rw [← hbk]; rfl
  rw [hval, Pi.single_apply]
  simp [eq_comm]

/-- 3F.31 (a) For the inclusion {lit}`i : U → V` ({lit}`i(u) = u` in mathlib is
{name}`Submodule.subtype`) -/
theorem exercise_3F_31a (U : Submodule F V) :
    LinearMap.ker U.subtype.dualMap = U.dualAnnihilator := by
  -- basically the definition i' φ = 0 -> φ i u = 0 for all u in U -> φ u = 0, is Uo
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

/-- 3F.31 (b) -/
theorem exercise_3F_31b [Finite F V] (U : Submodule F V) :
    LinearMap.range U.subtype.dualMap = ⊤ := by
  -- same as surjective, by theorem iff i injective, clearly it is.
  rw [LinearMap.range_eq_top]
  exact (injective_iff_dualMap_surjective U.subtype).mp U.injective_subtype

/-- 3F.31 (c) If {lit}`V` is finite-dimensional, the map {lit}`ī'` that {lit}`i'`
induces on {lit}`V'/U⁰` is an isomorphism onto {lit}`U'`. Here {lit}`ī'` is
{name}`Submodule.liftQ`, lifting {lit}`i'` through the quotient by {lit}`U⁰`; the
required {lit}`U⁰ ≤ null i'` is part (a), {name}`exercise_3F_31a`. -/
theorem exercise_3F_31c [Finite F V] (U : Submodule F V) :
    Function.Bijective
      (U.dualAnnihilator.liftQ U.subtype.dualMap (exercise_3F_31a U).ge) := by
  -- fundamental theorem V / ker iso to range , just use a to replace kernel
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (exercise_3F_31a U).le
  · rw [← LinearMap.range_eq_top, Submodule.range_liftQ]
    exact exercise_3F_31b U

/-- 3F.32 (a) {lit}`Λ : V → V''` is linear. -/
def exercise_3F_32_Lambda : V →ₗ[F] Module.Dual F (Module.Dual F V) where
  toFun v := { toFun := fun φ => φ v
               map_add' := by
                 intro x y
                 simp only [LinearMap.add_apply]
               map_smul' := by
                intro c x
                simp
              }
  map_add' u v := by
    ext z
    simp
  map_smul' a v := by
    ext z
    simp

/-- 3F.32 (b) -/
theorem exercise_3F_32b (T : V →ₗ[F] V) :
    T.dualMap.dualMap ∘ₗ exercise_3F_32_Lambda =
      exercise_3F_32_Lambda ∘ₗ T := by
  -- (T'' Λ)v = (Λ v) T' (when working on V')
  -- test on a random φ
  -- (Λ v) T' φ = (Λ v) φ T = φ (T v) = Λ (T v) φ
  -- so (T'' Λ)v = (Λ T) v as desired
  ext v φ
  rfl

/-- 3F.32 (c) {lit}`Λ` is an isomorphism when {lit}`V` is finite-dimensional. -/
theorem exercise_3F_32c [Finite F V] :
    Function.Bijective (exercise_3F_32_Lambda (F := F) (V := V)) := by
  -- by dimension enough to prove inj
  -- Λ v = 0 means for all φ , φ v = 0, so v ∈ Vo -> v ∈ {0} (previous exercise)
  -- thus injective
  -- This is the evaluation map, so it is exactly {name}`eval_injective` (from
  -- 3F.3) together with {name}`eval_surjective` (the dimension count).
  have h : ⇑(exercise_3F_32_Lambda (F := F) (V := V)) = ⇑(Module.Dual.eval F V) := rfl
  rw [h]
  exact ⟨eval_injective, eval_surjective⟩

/-- 3F.33 (a) -/
theorem exercise_3F_33a (U : Submodule F V) :
    Function.Injective U.mkQ.dualMap := by
  -- assume pi' phi = 0 , then pi' phi v = 0 for all v
  -- so phi pi v = 0 for all v, but pi is surj, so phi u = 0 for all u in V / U
  -- phi is 0, thus inj.
  intro φ ψ h
  ext x
  simpa using congrArg (fun ξ : Module.Dual F V => ξ x) h

/-- 3F.33 (b) -/
theorem exercise_3F_33b (U : Submodule F V) :
    LinearMap.range U.mkQ.dualMap = U.dualAnnihilator := by
  -- =>
  -- phi' = pi' phi
  -- phi' u = phi pi u = phi 0 for all u, by def phi' is in Uo
  -- <=
  -- phi u = 0 for all u in U, for some phi : V -> U
  -- then we can lift to phi' on V/U -> F, s.t. phi' pi = phi
  -- now pi' phi' = phi' pi = phi, so it is in the pi' range
  apply le_antisymm
  · rintro _ ⟨φ, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro u hu
    show φ (U.mkQ u) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr hu, map_zero]
  · intro ψ hψ
    rw [Submodule.mem_dualAnnihilator] at hψ
    have hle : U ≤ LinearMap.ker ψ := fun u hu => LinearMap.mem_ker.mpr (hψ u hu)
    exact ⟨U.liftQ ψ hle, U.liftQ_mkQ ψ hle⟩

/-- 3F.33 (c) -/
theorem exercise_3F_33c (U : Submodule F V) :
    Function.Bijective U.mkQ.dualMap.rangeRestrict := by
  -- a and b show inj and surj
  refine ⟨fun x y h => exercise_3F_33a U (congrArg Subtype.val h),
    U.mkQ.dualMap.surjective_rangeRestrict⟩

end LADR.Section_3F
