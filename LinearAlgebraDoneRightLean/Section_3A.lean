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

/-! 3.6 {lit}`ℒ(V, W)` is a vector space (over {lit}`F`) (exercise 3A.5).

In mathlib a vector space is the combination of two typeclasses:
{name}`AddCommGroup` (the additive group structure {lit}`+`, {lit}`0`, {lit}`-`)
and {name}`Module` (the scalar action satisfying distributivity, associativity,
and {lit}`1 • v = v`). There is no single {lit}`VectorSpace` class; saying
"{lit}`ℒ(V, W)` is a vector space over {lit}`F`" amounts to providing both. -/

example : AddCommGroup (V →ₗ[F] W) := sorry
example : Module F (V →ₗ[F] W) := sorry

/-! 3.7 Definition: product of linear maps

If {lit}`T ∈ ℒ(U, V)` and {lit}`S ∈ ℒ(V, W)`, then the product
{lit}`ST ∈ ℒ(U, W)` is composition {lit}`S ∘ T`. In Lean we write
{lit}`S ∘ₗ T` (or equivalently {lit}`S.comp T`). -/

example (S : V →ₗ[F] W) (T : U →ₗ[F] V) (u : U) : (S ∘ₗ T) u = S (T u) := rfl

/-! 3.8 Algebraic properties of products of linear maps (exercise 3A.6). -/

/-- (associativity) -/
example {X : Type*} [AddCommGroup X] [Module F X]
    (T₁ : V →ₗ[F] W) (T₂ : U →ₗ[F] V) (T₃ : X →ₗ[F] U) :
    (T₁ ∘ₗ T₂) ∘ₗ T₃ = T₁ ∘ₗ (T₂ ∘ₗ T₃) := sorry

/-- (identity on the source) -/
example (T : V →ₗ[F] W) : T ∘ₗ (LinearMap.id : V →ₗ[F] V) = T := sorry

/-- (identity on the target) -/
example (T : V →ₗ[F] W) : (LinearMap.id : W →ₗ[F] W) ∘ₗ T = T := sorry

/-- (distributive properties) -/
example (S₁ S₂ : V →ₗ[F] W) (T : U →ₗ[F] V) :
    (S₁ + S₂) ∘ₗ T = S₁ ∘ₗ T + S₂ ∘ₗ T := sorry
example (S : V →ₗ[F] W) (T₁ T₂ : U →ₗ[F] V) :
    S ∘ₗ (T₁ + T₂) = S ∘ₗ T₁ + S ∘ₗ T₂ := sorry

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
  sorry

theorem exercise_3A_2 (b c : ℝ) :
    (∃ T : Polynomial ℝ →ₗ[ℝ] (Fin 2 → ℝ), ∀ p : Polynomial ℝ,
      T p = ![3 * p.eval 4 + 5 * (Polynomial.derivative p).eval 6
                 + b * p.eval 1 * p.eval 2,
              integralOn01 (Polynomial.X ^ 3 * p) + c * Real.sin (p.eval 0)])
    ↔ b = 0 ∧ c = 0 := by
  sorry

theorem exercise_3A_3 {m n : ℕ} (T : (Fin n → F) →ₗ[F] (Fin m → F)) :
    ∃ A : Fin m → Fin n → F, T = fromFnToFm A := by
  sorry

theorem exercise_3A_4 {m : ℕ} (T : V →ₗ[F] W) (v : Fin m → V)
    (hTv : LinearIndependent F (T ∘ v)) : LinearIndependent F v := by
  sorry

/-! 3A.5 {lit}`ℒ(V, W)` is a vector space — stated above as 3.6. -/

/-! 3A.6 Algebraic properties of products of linear maps — stated above as
3.8. -/

theorem exercise_3A_7 [Finite F V] (hV : finrank F V = 1) (T : V →ₗ[F] V) :
    ∃ γ : F, ∀ v : V, T v = γ • v := by
  sorry

def exercise_3A_8 :
    ∃ φ : (Fin 2 → ℝ) → ℝ,
      (∀ a : ℝ, ∀ v : Fin 2 → ℝ, φ (a • v) = a * φ v) ∧
      ¬ ∀ u v : Fin 2 → ℝ, φ (u + v) = φ u + φ v := by
  sorry

def exercise_3A_9 :
    ∃ φ : ℂ → ℂ,
      (∀ w z : ℂ, φ (w + z) = φ w + φ z) ∧
      ¬ ∀ a z : ℂ, φ (a • z) = a • φ z := by
  sorry

def exercise_3A_10 :
    Decidable (∀ q : Polynomial ℝ,
      ∃ T : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ, ∀ p, T p = q.comp p) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

theorem exercise_3A_11 [Finite F V] (T : V →ₗ[F] V) :
    (∃ γ : F, T = γ • LinearMap.id) ↔
      ∀ S : V →ₗ[F] V, S ∘ₗ T = T ∘ₗ S := by
  sorry

theorem exercise_3A_12 (U : Submodule F V) (hU : U ≠ ⊤)
    (S : U →ₗ[F] W) (hS : S ≠ 0) :
    ¬ ∃ T : V →ₗ[F] W,
      (∀ u : U, T (u : V) = S u) ∧ (∀ v : V, v ∉ U → T v = 0) := by
  sorry

theorem exercise_3A_13 [Finite F V] (U : Submodule F V)
    (S : U →ₗ[F] W) :
    ∃ T : V →ₗ[F] W, ∀ u : U, T (u : V) = S u := by
  sorry

theorem exercise_3A_14 [Finite F V] (hV : 0 < finrank F V)
    (hW : ¬ Finite F W) : ¬ Finite F (V →ₗ[F] W) := by
  sorry

theorem exercise_3A_15 {m : ℕ} (v : Fin m → V)
    (hv : ¬ LinearIndependent F v) (hW : ∃ w : W, w ≠ 0) :
    ∃ w : Fin m → W, ¬ ∃ T : V →ₗ[F] W, ∀ k, T (v k) = w k := by
  sorry

theorem exercise_3A_16 [Finite F V] (hV : 1 < finrank F V) :
    ∃ S T : V →ₗ[F] V, S ∘ₗ T ≠ T ∘ₗ S := by
  sorry

theorem exercise_3A_17 [Finite F V] (E : Submodule F (V →ₗ[F] V))
    (hL : ∀ T : V →ₗ[F] V, ∀ S ∈ E, T ∘ₗ S ∈ E)
    (hR : ∀ T : V →ₗ[F] V, ∀ S ∈ E, S ∘ₗ T ∈ E) :
    E = ⊥ ∨ E = ⊤ := by
  sorry

end LADR.Section_3A
