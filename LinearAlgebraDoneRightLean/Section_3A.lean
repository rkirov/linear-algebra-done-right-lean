import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3A: Vector Space of Linear Maps
-/

namespace LADR.Section_3A

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open Module (Finite finrank)
open scoped ComplexConjugate

variable {F : Type*} [Field F]
  {U V W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]

/-! 3.1 Definition: linear map

A *linear map* from {lit}`V` to {lit}`W` is a function {lit}`T : V → W`
satisfying additivity and homogeneity. In Lean/mathlib these are bundled as
{lit}`V →ₗ[F] W` (a {name}`LinearMap` over the field {name}`F`),
and we use that throughout. -/

example (T : V →ₗ[F] W) (u v : V) : T (u + v) = T u + T v := T.map_add u v
example (T : V →ₗ[F] W) (γ : F) (v : V) : T (γ • v) = γ • T v :=
  T.map_smul γ v

/-! 3.2 Notation: {lit}`ℒ(V, W)`, {lit}`ℒ(V)`

In mathlib, the set of linear maps from {lit}`V` to {lit}`W` is the type
{lit}`V →ₗ[F] W`. The set {lit}`ℒ(V) = ℒ(V, V)` of linear operators on
{lit}`V` is {lit}`V →ₗ[F] V`. -/

example : Type _ := V →ₗ[F] W
example : Type _ := V →ₗ[F] V

/-! 3.3 Example: linear maps -/

/-- (zero) The zero linear map. The additive identity of {lit}`V →ₗ[F] W`. -/
example : V →ₗ[F] W := 0

/-- The same zero map, with the linearity axioms proved explicitly. -/
example : V →ₗ[F] W where
  toFun _ := 0
  map_add' _ _ := by rw [add_zero]
  map_smul' a _ := by rw [smul_zero]

/-- (identity operator) {lit}`I ∈ ℒ(V)` takes each element to itself. -/
example : V →ₗ[F] V := LinearMap.id

/-- (differentiation) {lit}`D ∈ ℒ(𝒫(ℝ))` is polynomial differentiation,
provided by mathlib as {name}`Polynomial.derivative`. -/
noncomputable example : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ := Polynomial.derivative

/-- (integration) {lit}`T ∈ ℒ(𝒫(ℝ), ℝ)` with {lit}`Tp = ∫₀¹ p`, expressed
coefficient-wise as {lit}`∑ cₖ / (k+1)`. -/
noncomputable def integralOn01 : Polynomial ℝ →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun n =>
    (LinearMap.id (R := ℝ) (M := ℝ)).smulRight ((1 : ℝ) / (n + 1))

/-- (multiplication by {lit}`x²`) {lit}`T ∈ ℒ(𝒫(ℝ))` with
{lit}`(Tp)(x) = x² p(x)`, i.e., {lit}`Tp = X² · p`. -/
noncomputable def multByXSq : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := Polynomial.X ^ 2 * p
  map_add' p q := mul_add _ _ _
  map_smul' a p := by
    show Polynomial.X ^ 2 * (a • p) = a • (Polynomial.X ^ 2 * p)
    rw [mul_smul_comm]

/-- (backward shift) {lit}`T ∈ ℒ(F^∞)` with
{lit}`T(x₁, x₂, x₃, …) = (x₂, x₃, …)`, encoded with {lit}`F^∞ = ℕ → F`. -/
def backwardShift : (ℕ → F) →ₗ[F] (ℕ → F) where
  toFun x := fun i => x (i + 1)
  map_add' x y := by funext i; rfl
  map_smul' a x := by funext i; rfl

/-- (from {lit}`ℝ³` to {lit}`ℝ²`) the concrete linear map
{lit}`T(x, y, z) = (2x − y + 3z, 7x + 5y − 6z)`. -/
noncomputable def fromR3ToR2 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![2 * v 0 - v 1 + 3 * v 2, 7 * v 0 + 5 * v 1 - 6 * v 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- (from {lit}`Fⁿ` to {lit}`Fᵐ`) Every {lit}`m × n` matrix
{lit}`A` of scalars gives a linear map {lit}`Fⁿ → Fᵐ` via
{lit}`(Av)ⱼ = ∑ₖ A_{jk} vₖ`. -/
def fromFnToFm {m n : ℕ} (A : Fin m → Fin n → F) :
    (Fin n → F) →ₗ[F] (Fin m → F) where
  toFun v := fun j => ∑ k, A j k * v k
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros k _
    ring

/-- (composition) For fixed {lit}`q ∈ 𝒫(ℝ)`, the map {lit}`T ∈ ℒ(𝒫(ℝ))`
with {lit}`(Tp)(x) = p(q(x))`, i.e., {lit}`Tp = p.comp q`. -/
noncomputable def polyCompRight (q : Polynomial ℝ) :
    Polynomial ℝ →ₗ[ℝ] Polynomial ℝ where
  toFun p := p.comp q
  map_add' p p' := Polynomial.add_comp
  map_smul' a p := by simp [Polynomial.smul_comp]

/-! 3.4 Linear map lemma

Given a basis {lit}`v₁, …, vₙ` of {lit}`V` and any list {lit}`w₁, …, wₙ ∈ W`,
there is a unique linear map {lit}`T : V → W` with {lit}`T vₖ = wₖ`.

We prove this directly from {name}`LADR.Section_2B.isBasis_iff_unique_combo`
(Axler 2.28), following the book. Mathlib's bundled {name}`Module.Basis`
packages the same data, providing {name}`Module.Basis.constr` (the
construction of {lit}`T`) and {name}`Module.Basis.ext` (the uniqueness step)
as off-the-shelf lemmas; we re-derive both here. -/

theorem linearMap_lemma {n : ℕ} (v : Fin n → V) (hv : IsBasis F v)
    (w : Fin n → W) : ∃! T : V →ₗ[F] W, ∀ k : Fin n, T (v k) = w k := by
  -- *Setup.* By 2.28 every `u : V` has a *unique* coordinate vector
  -- `a : Fin n → F` with `u = ∑ i, a i • v i`. Pick that `a` with `Classical.choose`
  -- and call it `repr u`. We need three properties of `repr`:
  --   `repr_spec`   — the defining equation `∑ i, repr u i • v i = u`,
  --   `repr_unique` — anything else expanding to `u` must equal `repr u`.
  rw [LADR.Section_2B.isBasis_iff_unique_combo] at hv
  classical
  let repr : V → Fin n → F := fun u => (hv u).choose
  have repr_spec : ∀ u, ∑ i, repr u i • v i = u := fun u => (hv u).choose_spec.1
  have repr_unique : ∀ u (a : Fin n → F), ∑ i, a i • v i = u → a = repr u :=
    fun u a ha => (hv u).choose_spec.2 a ha
  -- *Linearity of `repr`.* The trick is `repr_unique`: to show
  -- `repr (u₁ + u₂) = repr u₁ + repr u₂`, exhibit `repr u₁ + repr u₂` as
  -- *some* expansion of `u₁ + u₂`, and uniqueness identifies it with `repr (u₁ + u₂)`.
  have repr_add : ∀ u₁ u₂, repr (u₁ + u₂) = repr u₁ + repr u₂ := by
    intro u₁ u₂
    refine (repr_unique (u₁ + u₂) (repr u₁ + repr u₂) ?_).symm
    simp [add_smul, Finset.sum_add_distrib, repr_spec]
  have repr_smul : ∀ (γ : F) u, repr (γ • u) = γ • repr u := by
    intro γ u
    refine (repr_unique (γ • u) (γ • repr u) ?_).symm
    simp [mul_smul, ← Finset.smul_sum, repr_spec]
  -- The coordinates of `v k` are `Pi.single k 1` (one in slot `k`, zero
  -- elsewhere); uniqueness pins `repr (v k)` to that.
  have repr_vk : ∀ k, repr (v k) = Pi.single k 1 := by
    intro k
    refine (repr_unique (v k) (Pi.single k 1) ?_).symm
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [Pi.single_eq_of_ne hik]
    · intro h; exact absurd (Finset.mem_univ k) h
  -- *Existence.* Axler defines `T u := ∑ i, repr u i • w i`. Additivity and
  -- homogeneity follow from `repr_add` and `repr_smul`.
  refine ⟨{ toFun := fun u => ∑ i, repr u i • w i,
            map_add' := fun u₁ u₂ => by
              simp [repr_add, Pi.add_apply, add_smul, Finset.sum_add_distrib],
            map_smul' := fun γ u => by
              simp [repr_smul, Pi.smul_apply, mul_smul, ← Finset.smul_sum] }, ?_, ?_⟩
  · -- `T (v k) = ∑ i, (Pi.single k 1) i • w i = w k`.
    intro k
    show ∑ i, repr (v k) i • w i = w k
    rw [repr_vk k, Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [Pi.single_eq_of_ne hik]
    · intro h; exact absurd (Finset.mem_univ k) h
  · -- *Uniqueness.* Any linear `T'` with `T' (v k) = w k` agrees with our `T`:
    -- expand `u = ∑ repr u i • v i`, push `T'` through the sum, replace each
    -- `T' (v i)` by `w i`.
    intro T' hT'
    ext u
    show T' u = ∑ i, repr u i • w i
    conv_lhs => rw [← repr_spec u]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [LinearMap.map_smul, hT']

/-! *Same lemma, via the mathlib bridge.* The book's {name}`IsBasis` is just
the {lit}`Prop` "linearly independent and spans"; mathlib's
{name}`Module.Basis` is the bundled structure carrying the
*construction* — coordinate maps and a linear map builder — that the proof
above re-derives by hand. {name}`LADR.Section_2B.IsBasis.toModuleBasis`
turns the former into the latter (using {name}`Module.Basis.mk` under the
hood), with {name}`LADR.Section_2B.IsBasis.toModuleBasis_apply` confirming
{lit}`b k = v k`.

The two mathlib lemmas doing the real work:

- {name}`Module.Basis.constr` — given a basis {lit}`b` and target values
  {lit}`w : ι → W`, returns the linear map {lit}`V →ₗ[F] W` sending each
  {lit}`b k` to {lit}`w k`. This is the {name}`Module.Basis`-packaged form
  of the existence half. {name}`Module.Basis.constr_basis` is its
  defining equation.

- {name}`Module.Basis.ext` — two linear maps that agree on every basis
  vector are equal. This is the {name}`Module.Basis`-packaged form of
  the uniqueness half.

We keep this version available for later sections; the from-scratch proof
above tracks Axler's argument step by step. -/

theorem linearMap_lemma' {n : ℕ} (v : Fin n → V) (hv : IsBasis F v)
    (w : Fin n → W) : ∃! T : V →ₗ[F] W, ∀ k : Fin n, T (v k) = w k := by
  let b := LADR.Section_2B.IsBasis.toModuleBasis hv
  have hbv : ∀ k, b k = v k := LADR.Section_2B.IsBasis.toModuleBasis_apply hv
  refine ⟨b.constr F w, ?_, ?_⟩
  · intro k
    rw [show v k = b k from (hbv k).symm, b.constr_basis (S := F) w k]
  · intro T hT
    refine b.ext (fun k => ?_)
    rw [b.constr_basis (S := F) w k, hbv k, hT k]

/-! 3.5 Definition: addition and scalar multiplication on {lit}`ℒ(V, W)`

In mathlib, addition and scalar multiplication on {lit}`V →ₗ[F] W` are
already defined pointwise. -/

example (S T : V →ₗ[F] W) (v : V) : (S + T) v = S v + T v := LinearMap.add_apply _ _ _
example (γ : F) (T : V →ₗ[F] W) (v : V) : (γ • T) v = γ • T v :=
  LinearMap.smul_apply _ _ _

/-! 3.6 {lit}`ℒ(V, W)` is a vector space (over {lit}`F`).

In mathlib a vector space is the combination of two typeclasses:
{name}`AddCommGroup` (the additive group structure {lit}`+`, {lit}`0`, {lit}`-`)
and {name}`Module` (the scalar action satisfying distributivity, associativity,
and {lit}`1 • v = v`). There is no single {lit}`VectorSpace` class; saying
"{lit}`ℒ(V, W)` is a vector space over {lit}`F`" amounts to providing both. -/

example : AddCommGroup (V →ₗ[F] W) := by
  constructor
  intro x y
  rw [add_comm]
example : Module F (V →ₗ[F] W) := by
  constructor
  · intro a b T
    ext x
    rw [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
    rw [add_smul]
  · intro a
    ext x
    rw [LinearMap.smul_apply]
    rw [zero_smul]
    rfl

/-! 3.7 Definition: product of linear maps

If {lit}`T ∈ ℒ(U, V)` and {lit}`S ∈ ℒ(V, W)`, then the product
{lit}`ST ∈ ℒ(U, W)` is composition {lit}`S ∘ T`. In Lean we write
{lit}`S ∘ₗ T` (or equivalently {lit}`S.comp T`). -/

example (S : V →ₗ[F] W) (T : U →ₗ[F] V) (u : U) : (S ∘ₗ T) u = S (T u) := rfl

/-! 3.8 Algebraic properties of products of linear maps (exercise 3A.6). -/

/-- (associativity) -/
example {X : Type*} [AddCommGroup X] [Module F X]
    (T₁ : V →ₗ[F] W) (T₂ : U →ₗ[F] V) (T₃ : X →ₗ[F] U) :
    (T₁ ∘ₗ T₂) ∘ₗ T₃ = T₁ ∘ₗ (T₂ ∘ₗ T₃) := by
  ext x
  rfl

/-- (identity on the source) -/
example (T : V →ₗ[F] W) : T ∘ₗ (LinearMap.id : V →ₗ[F] V) = T := by
  ext x
  rfl

/-- (identity on the target) -/
example (T : V →ₗ[F] W) : (LinearMap.id : W →ₗ[F] W) ∘ₗ T = T := by
  ext x
  rfl

/-- (distributive properties) -/
example (S₁ S₂ : V →ₗ[F] W) (T : U →ₗ[F] V) :
    (S₁ + S₂) ∘ₗ T = S₁ ∘ₗ T + S₂ ∘ₗ T := by
  ext x
  rfl
example (S : V →ₗ[F] W) (T₁ T₂ : U →ₗ[F] V) :
    S ∘ₗ (T₁ + T₂) = S ∘ₗ T₁ + S ∘ₗ T₂ := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]

/-! 3.9 Example: noncommuting {lit}`D` and {lit}`T` on {lit}`𝒫(ℝ)`

With {lit}`D = Polynomial.derivative` and {lit}`T = multByXSq`, the
products {lit}`T ∘ D` and {lit}`D ∘ T` differ: for {lit}`p = X` we have
{lit}`(T ∘ D) p = X²` while {lit}`(D ∘ T) p = 3 X²`. -/

example :
    (multByXSq ∘ₗ Polynomial.derivative) ≠
      (Polynomial.derivative ∘ₗ multByXSq) := by
  intro h
  have hX := LinearMap.congr_fun h Polynomial.X
  -- (multByXSq ∘ₗ D) X = X² · 1 = X²
  have hLHS : (multByXSq ∘ₗ Polynomial.derivative) Polynomial.X =
      (Polynomial.X ^ 2 : Polynomial ℝ) := by
    change Polynomial.X ^ 2 * Polynomial.derivative Polynomial.X = Polynomial.X ^ 2
    simp
  -- (D ∘ₗ multByXSq) X = D (X² · X) = D X³
  have hRHS : (Polynomial.derivative ∘ₗ multByXSq) Polynomial.X =
      Polynomial.derivative ((Polynomial.X : Polynomial ℝ) ^ 3) := by
    change Polynomial.derivative (Polynomial.X ^ 2 * Polynomial.X) = _
    rfl
  rw [hLHS, hRHS] at hX
  -- Compare coefficients of degree 2: coeff X² 2 = 1, coeff (D X³) 2 = 3.
  have hc := congrArg (Polynomial.coeff · 2) hX
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_X_pow] at hc
  norm_num at hc

/-! 3.10 Linear maps take {lit}`0` to {lit}`0` -/

example (T : V →ₗ[F] W) : T 0 = 0 := T.map_zero

/-! # Exercises -/

theorem exercise_3A_1 (b c : ℝ) :
    (∃ T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ), ∀ v : Fin 3 → ℝ,
      T v = ![2 * v 0 - 4 * v 1 + 3 * v 2 + b, 6 * v 0 + c * v 0 * v 1 * v 2])
    ↔ b = 0 ∧ c = 0 := by
  -- to be linear T(0,0,0) has to be 0,0, so b = 0
  -- 2 * T(1,1,1) = T(2,2,2), in second coord
  -- 2 * (6 + c) = 6 * 2 + c * 8, so c = 0
  constructor
  · rintro ⟨T, hT⟩
    have hb : b = 0 := by
      have hz := congrArg (fun x ↦ x 0) (hT (0 : Fin 3 → ℝ))
      simpa using hz.symm
    have hc : c = 0 := by
      let e : Fin 3 → ℝ := ![1, 1, 1]
      have hs := T.map_smul (2 : ℝ) e
      rw [hT, hT] at hs
      have hs₁ := congrArg (fun x ↦ x 1) hs
      simp [e, Matrix.cons_val_zero, Matrix.cons_val_one] at hs₁
      ring_nf at hs₁
      linarith
    exact ⟨hb, hc⟩
  · rintro ⟨rfl, rfl⟩
    let T : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun v ↦ ![2 * v 0 - 4 * v 1 + 3 * v 2, 6 * v 0]
        map_add' := by
          intro u v
          funext i
          fin_cases i <;> simp <;> ring
        map_smul' := by
          intro a v
          funext i
          fin_cases i <;> simp <;> ring }
    refine ⟨T, ?_⟩
    intro v
    funext i
    fin_cases i <;> simp [T]

theorem exercise_3A_2 (b c : ℝ) :
    (∃ T : Polynomial ℝ →ₗ[ℝ] (Fin 2 → ℝ), ∀ p : Polynomial ℝ,
      T p = ![3 * p.eval 4 + 5 * (Polynomial.derivative p).eval 6
                 + b * p.eval 1 * p.eval 2,
              integralOn01 (Polynomial.X ^ 3 * p) + c * Real.sin (p.eval 0)])
    ↔ b = 0 ∧ c = 0 := by
  -- T(-1) + T(1) = T(0) = 0, so in first coord 3 + b + -3 + b = 0, so b = 0
  -- For `c`, use the constant polynomial `π/2`; its double is the constant `π`.
  constructor
  · rintro ⟨T, hT⟩
    have hb : b = 0 := by
      have hadd := T.map_add (-(1 : Polynomial ℝ)) (1 : Polynomial ℝ)
      rw [hT, hT, hT] at hadd
      have h₀ := congrArg (fun x ↦ x 0) hadd
      norm_num at h₀
      linarith
    have hc : c = 0 := by
      let p : Polynomial ℝ := Polynomial.C (Real.pi / 2)
      have hs := T.map_smul (2 : ℝ) p
      rw [hT, hT] at hs
      have h₁ := congrArg (fun x ↦ x 1) hs
      simp [Matrix.cons_val_one] at h₁
      have hp₀ : p.eval 0 = Real.pi / 2 := by simp [p]
      rw [hp₀] at h₁
      have htwo : 2 * (Real.pi / 2) = Real.pi := by ring
      rw [htwo, Real.sin_pi, Real.sin_pi_div_two] at h₁
      linarith
    exact ⟨hb, hc⟩
  · rintro ⟨rfl, rfl⟩
    let T : Polynomial ℝ →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun p ↦
          ![3 * p.eval 4 + 5 * (Polynomial.derivative p).eval 6,
            integralOn01 (Polynomial.X ^ 3 * p)]
        map_add' := by
          intro p q
          funext i
          fin_cases i <;> simp [mul_add]; ring
        map_smul' := by
          intro a p
          funext i
          fin_cases i <;> simp; ring }
    refine ⟨T, ?_⟩
    intro p
    funext i
    fin_cases i <;> simp [T]

theorem exercise_3A_3 {m n : ℕ} (T : (Fin n → F) →ₗ[F] (Fin m → F)) :
    ∃ A : Fin m → Fin n → F, T = fromFnToFm A := by
  use fun i j => T (Pi.single j 1) i
  ext i j
  simp [fromFnToFm, Pi.single_apply]

theorem exercise_3A_4 {m : ℕ} (T : V →ₗ[F] W) (v : Fin m → V)
    (hTv : LinearIndependent F (T ∘ v)) : LinearIndependent F v := by
  -- ∑ a i v i = 0
  -- T ∑ a i v i = T 0 = 0
  -- Σ T (a i • v i) = 0
  -- Σ a i • T (v i) = 0
  -- by linear independence of T ∘ v, a i = 0 for all i
  rw [Fintype.linearIndependent_iff] at hTv ⊢
  intro a ha
  have hsumT : ∑ i, a i • T (v i) = 0 := by
    simpa using congrArg T ha
  exact hTv a hsumT

/-! 3A.5 {lit}`ℒ(V, W)` is a vector space (3.6) — already proved above. -/

/-! 3A.6 Algebraic properties of products of linear maps (3.8) — already
proved above. -/

theorem exercise_3A_7 [Finite F V] (hV : finrank F V = 1) (T : V →ₗ[F] V) :
    ∃ γ : F, ∀ v : V, T v = γ • v := by
  -- one dim means - V = span v
  -- take T(v) = γ, then T w = T (α v) = α γ v = γ w
 let b : Module.Basis (Fin 1) F V := by
   simpa [hV] using (Module.finBasis F V : Module.Basis (Fin (finrank F V)) F V)
 let γ : F := b.repr (T (b 0)) 0
 have hTb0 : T (b 0) = γ • b 0 := by
   dsimp [γ]
   simpa using (b.sum_repr (T (b 0))).symm
 refine ⟨γ, ?_⟩
 intro v
 let a : F := b.repr v 0
 have hv : v = a • b 0 := by
   dsimp [a]
   simpa using (b.sum_repr v).symm
 calc
   T v = T (a • b 0) := by rw [hv]
   _ = a • T (b 0) := by rw [LinearMap.map_smul]
   _ = a • (γ • b 0) := by rw [hTb0]
   _ = γ • (a • b 0) := by
     simp [smul_smul, mul_comm]
   _ = γ • v := by rw [hv]

def exercise_3A_8 :
   ∃ φ : (Fin 2 → ℝ) → ℝ,
     (∀ a : ℝ, ∀ v : Fin 2 → ℝ, φ (a • v) = a * φ v) ∧
     ¬ ∀ u v : Fin 2 → ℝ, φ (u + v) = φ u + φ v := by
 -- (x, y) = x if y = 0 and 0 otherwise
 -- φ(1,0), φ(0,1) = 1, but φ(1,0) + φ(0,1) = 1 ≠ φ(1,1) = 0
 refine ⟨fun v => if v 1 = 0 then v 0 else 0, ?_, ?_⟩
 · intro a v
   by_cases hv1 : v 1 = 0
   · simp [hv1]
   · by_cases ha : a = 0
     · simp [ha, hv1]
     · have hmul : a * v 1 ≠ 0 := mul_ne_zero ha hv1
       simp [hv1, hmul]
 · intro h
   have h01 := h (![1, 0] : Fin 2 → ℝ) (![0, 1] : Fin 2 → ℝ)
   norm_num at h01

def exercise_3A_9 :
   ∃ φ : ℂ → ℂ,
     (∀ w z : ℂ, φ (w + z) = φ w + φ z) ∧
     ¬ ∀ a z : ℂ, φ (a • z) = a • φ z := by
 -- φ(z) = conj(z)
 -- conj(x + y) = conj(x) + conj(y)
 -- conj(a z) = conj(a) conj(z) ≠ a conj(z)
 refine ⟨conj, ?_, ?_⟩
 · intro w z
   apply Complex.ext <;> simp
 · intro h
   have hI := h Complex.I (1 : ℂ)
   have hIm := congrArg Complex.im hI
   norm_num [Complex.conj_im, Complex.mul_im] at hIm

def exercise_3A_10 :
   Decidable (∀ q : Polynomial ℝ,
     ∃ T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ, ∀ p, T p = q.comp p) := by
   -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  push Not
  use Polynomial.X ^ 2
  intro T
  by_contra
  push Not at this
  have ht := this
  specialize this (Polynomial.X + 1)
  simp at this
  have ht1 := ht Polynomial.X
  have ht2 := ht 1
  rw [ht1, ht2] at this
  simp at this
  -- this : X² + 1 = (X+1)², which is false in ℝ: evaluating at 1 gives 2 = 4
  have h' := congrArg (Polynomial.eval 1) this
  simp at h'
  linarith

theorem exercise_3A_11 [Finite F V] (T : V →ₗ[F] V) :
    (∃ γ : F, T = γ • LinearMap.id) ↔
      ∀ S : V →ₗ[F] V, S ∘ₗ T = T ∘ₗ S := by
  -- => just eval
  constructor
  · intro h
    obtain ⟨γ, hT⟩ := h
    intro S
    rw [hT]
    ext x
    simp only [LinearMap.coe_comp, LinearMap.coe_smul, LinearMap.id_coe, Function.comp_apply,
      Pi.smul_apply, id_eq, map_smul]
  · intro h
    -- <= for each construct linear transformation Sv = {take all basis vectors to v}
    -- Sv T = T Sv
    -- apply v, a v = T v for some a, this true for all v
    -- take two basis vectors, T v1 = a v1, T v2 = b v2
    -- T (v1 + v2) = a v1 + b v2 = T (v1 + v2) = c (v1 + v2) for some c
    -- by uniqueness of coordinates, a = b = c, for all basis vectors
    -- so there is unique a such that T v = a v for all basis vectors
    -- and hence for all v
    classical
    let b := Module.finBasis F V
    by_cases hn : finrank F V = 0
    · refine ⟨0, ?_⟩
      ext v
      have hv : v = 0 := finrank_zero_iff_forall_zero.mp hn v
      rw [hv]
      simp
    · -- Choose one basis vector `b i₀` and let `γ` be its coefficient in
      -- `T (b i₀)` along that same basis vector.
      let i₀ : Fin (finrank F V) := ⟨0, Nat.pos_of_ne_zero hn⟩
      let γ : F := b.repr (T (b i₀)) i₀
      refine ⟨γ, ?_⟩
      ext v
      -- By the linear map lemma, construct `A` taking `b i₀` to the arbitrary
      -- vector `v` and every other basis vector to zero.
      let A : V →ₗ[F] V := b.constr F (Pi.single i₀ v)
      have hcomm := LinearMap.congr_fun (h A) (b i₀)
      have hAb : A (b i₀) = v := by
        simp [A]
      have hATb : A (T (b i₀)) = γ • v := by
        change (b.constr F (Pi.single i₀ v)) (T (b i₀)) = γ • v
        rw [b.constr_apply_fintype F, Finset.sum_eq_single i₀]
        · simp [γ]
        · intro j _ hji
          simp [Pi.single_eq_of_ne hji]
        · intro hi
          exact absurd (Finset.mem_univ i₀) hi
      change A (T (b i₀)) = T (A (b i₀)) at hcomm
      rw [hATb, hAb] at hcomm
      change T v = γ • v
      exact hcomm.symm

theorem exercise_3A_12 (U : Submodule F V) (hU : U ≠ ⊤)
    (S : U →ₗ[F] W) (hS : S ≠ 0) :
    ¬ ∃ T : V →ₗ[F] W,
      (∀ u : U, T (u : V) = S u) ∧ (∀ v : V, v ∉ U → T v = 0) := by
  intro h
  obtain ⟨T, hT1, hT2⟩ := h
  -- take w in V \ U, then T w = 0,
  -- take u in U, s.t. S u ≠ 0, then T u = S u ≠ 0
  -- conside w + u, it has to be ≠ U otherwise w will be in U too.
  -- so T (w + u) = 0, but T (w + u) = T w + T u = 0 + S u ≠ 0, contradiction
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hU)
  have hu : ∃ u : U, S u ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hS
    ext u
    exact hn u
  obtain ⟨u, hu⟩ := hu
  have hvadd : v + (u : V) ∉ U := by
    intro hvu
    apply hv
    rw [← add_sub_cancel_right v (u : V)]
    exact U.sub_mem hvu u.property
  apply hu
  calc
    S u = 0 + S u := (zero_add _).symm
    _ = T v + T (u : V) := by rw [hT2 v hv, hT1 u]
    _ = T (v + (u : V)) := (T.map_add v (u : V)).symm
    _ = 0 := hT2 _ hvadd

theorem exercise_3A_13 [Finite F V] (U : Submodule F V)
    (S : U →ₗ[F] W) :
    ∃ T : V →ₗ[F] W, ∀ u : U, T (u : V) = S u := by
  -- take a basis of U, extend it to V (by 2.34)
  -- map the basis of U - u i to S u i, and the rest to 0
  -- Equivalently, use the complement produced by that basis extension and
  -- project onto `U` before applying `S`.
  obtain ⟨Q, hQ⟩ := LADR.Section_2B.exists_isCompl U
  let T : V →ₗ[F] W := S.comp (U.linearProjOfIsCompl Q hQ)
  refine ⟨T, ?_⟩
  intro u
  simp [T]

theorem exercise_3A_14 [Finite F V] (hV : 0 < finrank F V)
    (hW : ¬ Finite F W) : ¬ Finite F (V →ₗ[F] W) := by
  -- take a basis of V, by theorem we can constuct a linear map
  -- to any set of vectors in W of size finrank V
  -- since W infinite, we cna make infinity many choices.
  -- the construction is injective, different W construct diff maps
  intro hL
  let b := Module.finBasis F V
  let i₀ : Fin (finrank F V) := ⟨0, hV⟩
  -- Evaluation at `b i₀` maps the space of linear maps onto `W`: prescribe
  -- any desired value at that basis vector and zero at all the others.
  let ev : (V →ₗ[F] W) →ₗ[F] W := LinearMap.applyₗ (b i₀)
  have hev : Function.Surjective ev := by
    intro w
    let T : V →ₗ[F] W := b.constr F (Pi.single i₀ w)
    refine ⟨T, ?_⟩
    simp [ev, T]
  apply hW
  exact Module.Finite.of_surjective ev hev

theorem exercise_3A_15 {m : ℕ} (v : Fin m → V)
    (hv : ¬ LinearIndependent F v) (hW : ∃ w : W, w ≠ 0) :
    ∃ w : Fin m → W, ¬ ∃ T : V →ₗ[F] W, ∀ k, T (v k) = w k := by
  -- ∑ ai vi = 0, st. at least one ai ≠ 0 say aj
  -- take w in W s.t. w ≠ 0
  -- take w i = 0 for all i ≠ j, w j = w ≠ 0
  -- assume by contra T exist, st. T vi = wi
  -- 0 = T (∑ ai vi) = ∑ ai T vi = ∑ ai wi = aj w
  -- but aj ≠ 0 and w ≠ 0, contradiction
  rw [Fintype.linearIndependent_iff] at hv
  push Not at hv
  obtain ⟨a, ha, j, haj⟩ := hv
  obtain ⟨w₀, hw₀⟩ := hW
  let w : Fin m → W := Pi.single j w₀
  refine ⟨w, ?_⟩
  rintro ⟨T, hT⟩
  have hsum := congrArg T ha
  simp only [map_sum, map_smul, map_zero, hT] at hsum
  have haw : ∑ i, a i • w i = a j • w₀ := by
    rw [Finset.sum_eq_single j]
    · simp [w]
    · intro i _ hij
      simp [w, Pi.single_eq_of_ne hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [haw] at hsum
  exact (smul_ne_zero haj hw₀) hsum

theorem exercise_3A_16 [Finite F V] (hV : 1 < finrank F V) :
    ∃ S T : V →ₗ[F] V, S ∘ₗ T ≠ T ∘ₗ S := by
  -- take a basis of V, it has at least 2 elements, say v1, v2
  -- S v1 = v2, S v2 = 0, T v1 = v1, T v2 = 0 -- by thorem 3.4
  -- we can construct such linear maps, take other basis to 0
  -- then S T v1 = v2, T S v1 = 0, so S T ≠ T S
  classical
  let b := Module.finBasis F V
  let i₀ : Fin (finrank F V) := ⟨0, Nat.zero_lt_of_lt hV⟩
  let i₁ : Fin (finrank F V) := ⟨1, hV⟩
  have hne : i₁ ≠ i₀ := by
    intro hi
    have := congrArg Fin.val hi
    norm_num [i₀, i₁] at this
  let S : V →ₗ[F] V := b.constr F (Pi.single i₀ (b i₁))
  let T : V →ₗ[F] V := b.constr F (Pi.single i₀ (b i₀))
  refine ⟨S, T, ?_⟩
  intro hcomm
  have heval := LinearMap.congr_fun hcomm (b i₀)
  change S (T (b i₀)) = T (S (b i₀)) at heval
  simp [S, T, hne] at heval
  exact (b.ne_zero i₁) heval

theorem exercise_3A_17 [Finite F V] (E : Submodule F (V →ₗ[F] V))
    (hL : ∀ T : V →ₗ[F] V, ∀ S ∈ E, T ∘ₗ S ∈ E)
    (hR : ∀ T : V →ₗ[F] V, ∀ S ∈ E, S ∘ₗ T ∈ E) :
    E = ⊥ ∨ E = ⊤ := by
  -- assume E ≠ ⊥, then there is a nonzero A ∈ E
  -- take a basis V, then A(b j) ≠ 0 for some basis vector b j
  -- this means A b j = ∑ a k b k, for some nonzero a k
  -- construct L sending b k to (a k)⁻¹ b i and all other basis vectors to 0
  -- so L A b j = b i, and L A ∈ E by left composition
  -- for any q, construct R sending b q to the fixed b j and all other basis vectors to 0
  -- then L A R ∈ E sends b q to b i and all other basis vectors to 0
  -- thus E contains every matrix-unit map (for arbitrary source q and target i)
  -- finally, every linear map is a linear combination of these matrix-unit maps,
  -- so E contains every linear map and hence E = ⊤
  classical
  by_cases hE : E = ⊥
  · exact Or.inl hE
  right
  apply top_unique
  intro T _
  -- Your projection idea in basis form: begin with a nonzero `A ∈ E` and
  -- find one nonzero matrix entry of `A`.
  obtain ⟨A, hAE, hA_bot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hE)
  have hA : A ≠ 0 := by simpa using hA_bot
  let b := Module.finBasis F V
  have hAb : ∃ j, A (b j) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hA
    apply b.ext
    exact hn
  obtain ⟨j, hAbj⟩ := hAb
  have hcoord : ∃ k, b.repr (A (b j)) k ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hAbj
    rw [← b.sum_repr (A (b j))]
    simp [hn]
  obtain ⟨k, hk⟩ := hcoord
  let a : F := b.repr (A (b j)) k
  -- Left composition sends the selected nonzero output component to any `w`.
  let L (w : V) : V →ₗ[F] V := b.constr F (Pi.single k (a⁻¹ • w))
  have hLA (w : V) : L w (A (b j)) = w := by
    change (b.constr F (Pi.single k (a⁻¹ • w))) (A (b j)) = w
    rw [b.constr_apply_fintype F, Finset.sum_eq_single k]
    · simp [a, hk]
    · intro q _ hq
      simp [Pi.single_eq_of_ne hq]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  -- Right composition selects any desired input basis line.
  let R (i : Fin (finrank F V)) : V →ₗ[F] V :=
    b.constr F (Pi.single i (b j))
  have hR_apply (i q : Fin (finrank F V)) :
      R i (b q) = if q = i then b j else 0 := by
    simp [R, Pi.single_apply]
  -- Thus two-sided composition produces every single-column piece of `T`.
  let M (i : Fin (finrank F V)) : V →ₗ[F] V :=
    L (T (b i)) ∘ₗ (A ∘ₗ R i)
  have hM_apply (i q : Fin (finrank F V)) :
      M i (b q) = if q = i then T (b i) else 0 := by
    by_cases hqi : q = i
    · subst q
      simp [M, hR_apply, hLA]
    · simp [M, hR_apply, hqi]
  have hME (i : Fin (finrank F V)) : M i ∈ E := by
    exact hL (L (T (b i))) (A ∘ₗ R i) (hR (R i) A hAE)
  -- This is the missing addition step from the discussion: summing the
  -- elementary pieces recovers the arbitrary operator `T`.
  have hsumE : ∑ i, M i ∈ E := E.sum_mem (fun i _ ↦ hME i)
  have hsum : ∑ i, M i = T := by
    apply b.ext
    intro q
    simp only [LinearMap.sum_apply, hM_apply]
    rw [Finset.sum_eq_single q]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · intro hq
      exact absurd (Finset.mem_univ q) hq
  rw [← hsum]
  exact hsumE

end LADR.Section_3A
