import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 9B: Alternating Multilinear Forms
-/

namespace LADR.Section_9B

open LADR.Section_2B (IsBasis)
open Module (Finite finrank)

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]

/-! # Alternating Multilinear Forms

Axler's `V⁽ᵐ⁾` is the space of {lit}`m`-linear forms on {lit}`V`; in mathlib this is
{name}`MultilinearMap` {lit}`F (fun _ : Fin m => V) F`. The alternating {lit}`m`-linear
forms `V⁽ᵐ⁾ₐₗₜ` are mathlib's {name}`AlternatingMap`, written
{lit}`V [⋀^Fin m]→ₗ[F] F`. Throughout, an {lit}`m`-linear form applied to a list
`v₁, …, vₘ` becomes application to a function {lit}`v : Fin m → V`, and Axler's
condition "{lit}`vⱼ = vₖ` for some {lit}`j ≠ k`" is {name}`AlternatingMap.map_eq_zero_of_eq`. -/

/-! 9.26 Example: {lit}`m`-linear forms. The type of {lit}`m`-linear forms is
{name}`MultilinearMap` (9.25). Axler's first example is the product
{lit}`β(v₁, v₂, v₃, v₄) = α(v₁, v₂) ρ(v₃, v₄)` of two bilinear forms {lit}`α, ρ`,
which is a {lit}`4`-linear form. We build it from mathlib combinators: the two
factors act on disjoint pairs of slots, so {lit}`β` is the tensor product
{name}`MultilinearMap.domCoprod` of {lit}`α` and {lit}`ρ` on {lit}`Fin 2 ⊕ Fin 2`, followed by
multiplication {name}`LinearMap.mul'` `F F : F ⊗ F → F`, reindexed along
{name}`finSumFinEquiv` `: Fin 2 ⊕ Fin 2 ≃ Fin 4`. Axler's second example,
{lit}`β(T₁, …, Tₘ) = tr(T₁ ⋯ Tₘ)` on {lit}`ℒ(V)`, is the trace of the ordered
product {name}`MultilinearMap.mkPiAlgebraFin` composed with
{name}`LinearMap.trace`. -/
open scoped Matrix in
/-- 9.26: the product `β(v₁,v₂,v₃,v₄) = α(v₁,v₂)·ρ(v₃,v₄)` of two bilinear forms
is a {lit}`4`-linear form. -/
noncomputable def prodBilinear (α ρ : MultilinearMap F (fun _ : Fin 2 => V) F) :
    MultilinearMap F (fun _ : Fin 4 => V) F :=
  ((LinearMap.mul' F F).compMultilinearMap (α.domCoprod ρ)).domDomCongr finSumFinEquiv

open scoped Matrix in
@[simp] theorem prodBilinear_apply (α ρ : MultilinearMap F (fun _ : Fin 2 => V) F)
    (v : Fin 4 → V) : prodBilinear α ρ v = α ![v 0, v 1] * ρ ![v 2, v 3] := by
  rw [prodBilinear, MultilinearMap.domDomCongr_apply, LinearMap.compMultilinearMap_apply,
    MultilinearMap.domCoprod_apply, LinearMap.mul'_apply]
  congr 1
  · congr 1; funext i; fin_cases i <;> rfl
  · congr 1; funext i; fin_cases i <;> rfl

/-- 9.26: the trace of a product `β(T₁, …, Tₘ) = tr(T₁ ⋯ Tₘ)` of operators is an
{lit}`m`-linear form on {lit}`ℒ(V)` — the ordered algebra product
{name}`MultilinearMap.mkPiAlgebraFin` followed by {name}`LinearMap.trace`. -/
noncomputable def traceForm (m : ℕ) :
    MultilinearMap F (fun _ : Fin m => Module.End F V) F :=
  (LinearMap.trace F V).compMultilinearMap (MultilinearMap.mkPiAlgebraFin F m (Module.End F V))

@[simp] theorem traceForm_apply (m : ℕ) (T : Fin m → Module.End F V) :
    traceForm m T = LinearMap.trace F V (List.ofFn T).prod := by
  simp [traceForm, MultilinearMap.mkPiAlgebraFin_apply]

/-! 9.27 Definition: alternating forms, `V⁽ᵐ⁾ₐₗₜ`

An {lit}`m`-linear form is a {name}`MultilinearMap`; it is *alternating* if it
vanishes whenever two of its inputs are equal, which is exactly the defining
property of a mathlib {name}`AlternatingMap`. -/

/-- An {lit}`m`-linear form on {lit}`V`. -/
example (m : ℕ) : Type _ := MultilinearMap F (fun _ : Fin m => V) F

/-- An alternating {lit}`m`-linear form on {lit}`V`, i.e. {lit}`V⁽ᵐ⁾ₐₗₜ`. -/
example (m : ℕ) : Type _ := V [⋀^Fin m]→ₗ[F] F

example (m : ℕ) : (V [⋀^Fin m]→ₗ[F] F) = AlternatingMap F V F (Fin m) := rfl

/-- The defining property of alternating: {lit}`α(v₁, …, vₘ) = 0` whenever
{lit}`vⱼ = vₖ` for two distinct slots {lit}`j ≠ k`. -/
example (m : ℕ) (α : V [⋀^Fin m]→ₗ[F] F) (v : Fin m → V) {i j : Fin m}
    (h : v i = v j) (hij : i ≠ j) : α v = 0 := α.map_eq_zero_of_eq v h hij

/-- Every alternating form is in particular a multilinear form (an element of
{lit}`V⁽ᵐ⁾`), via the injective coercion {name}`AlternatingMap.toMultilinearMap`. -/
example (m : ℕ) (α : V [⋀^Fin m]→ₗ[F] F) : MultilinearMap F (fun _ : Fin m => V) F :=
  α.toMultilinearMap

/-- {lit}`V⁽ᵐ⁾ₐₗₜ` is a subspace of {lit}`V⁽ᵐ⁾`: mathlib packages it as a module,
so the zero form, sums, and scalar multiples of alternating forms are again
alternating. -/
example (m : ℕ) : Module F (V [⋀^Fin m]→ₗ[F] F) := inferInstance

/-! 9.28 Alternating multilinear forms and linear dependence

If a linearly dependent list is input to an alternating multilinear form, then
the output is {lit}`0`. In mathlib this is {name}`AlternatingMap.map_linearDependent`
(the target field {lit}`F` satisfies {name}`NoZeroSMulDivisors`). -/

theorem map_eq_zero_of_linearDependent {m : ℕ} (α : V [⋀^Fin m]→ₗ[F] F)
    (v : Fin m → V) (h : ¬ LinearIndependent F v) : α v = 0 :=
  α.map_linearDependent v h

/-! 9.29 No nonzero alternating {lit}`m`-linear forms for {lit}`m > dim V`

If {lit}`m > dim V`, then {lit}`0` is the only alternating {lit}`m`-linear form on
{lit}`V`: any list of {lit}`m` vectors is linearly dependent (2.22), so 9.28
forces the form to vanish everywhere. -/

theorem eq_zero_of_dim_lt [Finite F V] {m : ℕ} (hm : finrank F V < m)
    (α : V [⋀^Fin m]→ₗ[F] F) : α = 0 := by
  ext v
  apply α.map_linearDependent v
  intro hli
  have hcard : Fintype.card (Fin m) ≤ finrank F V := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hcard
  omega

/-! # Alternating Multilinear Forms and Permutations -/

/-! 9.30 Swapping input vectors in an alternating multilinear form

Swapping the vectors in any two slots of {lit}`α(v₁, …, vₘ)` changes the value of
{lit}`α` by a factor of {lit}`−1`. In mathlib this is
{name}`AlternatingMap.map_swap`. -/

theorem map_swap_eq_neg {m : ℕ} (α : V [⋀^Fin m]→ₗ[F] F) (v : Fin m → V)
    {i j : Fin m} (hij : i ≠ j) :
    α (v ∘ Equiv.swap i j) = - α v :=
  α.map_swap (v := v) hij

/-! 9.31 Definition: permutation, {lit}`perm m`

A permutation of {lit}`(1, …, m)` is a rearrangement of the first {lit}`m`
positive integers. In mathlib, {lit}`perm m` is {name}`Equiv.Perm` {lit}`(Fin m)`:
a bijection of {lit}`Fin m` with itself. Axler's list {lit}`(j₁, …, jₘ)` is the
function {lit}`σ : Fin m → Fin m` (which is a bijection). -/

example (m : ℕ) : Type _ := Equiv.Perm (Fin m)

/-- For example, {lit}`(2, 3, 4, 5, 1) ∈ perm 5`: the rotation
{name}`finRotate` {lit}`5` sends each entry to the next one (and {lit}`5 ↦ 1`). -/
example : Equiv.Perm (Fin 5) := finRotate 5

/-! 9.32 Definition: sign of a permutation

The sign of a permutation is {lit}`(−1)ᴺ`, where {lit}`N` counts the inversions
(pairs out of their natural order). Equivalently, it is {lit}`1` for an even and
{lit}`−1` for an odd number of transpositions. mathlib's
{name}`Equiv.Perm.sign` is exactly this, valued in {lit}`ℤˣ`. -/

example (m : ℕ) (σ : Equiv.Perm (Fin m)) : ℤˣ := Equiv.Perm.sign σ

/-! 9.33 Example: signs -/

/-- The identity permutation {lit}`(1, …, m)` has sign {lit}`1`. -/
example (m : ℕ) : Equiv.Perm.sign (1 : Equiv.Perm (Fin m)) = 1 :=
  Equiv.Perm.sign_one

/-- The permutation {lit}`(2, 1, 3, 4)` — the transposition of the first two
entries — has sign {lit}`−1`. -/
example : Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1) = -1 :=
  Equiv.Perm.sign_swap (by decide)

/-- The permutation {lit}`(2, 3, …, m, 1)` — the rotation {name}`finRotate`
{lit}`m` — has sign {lit}`(−1)ᵐ⁻¹`. Here {lit}`m = n + 1`. -/
example (n : ℕ) : Equiv.Perm.sign (finRotate (n + 1)) = (-1) ^ n :=
  sign_finRotate n

/-! 9.34 Swapping two entries in a permutation

Swapping two entries in a permutation multiplies its sign by {lit}`−1`. In terms
of {name}`Equiv.Perm.sign` (which is multiplicative, {name}`Equiv.Perm.sign_mul`,
with {name}`Equiv.Perm.sign_swap` giving {lit}`−1` for a transposition): -/

theorem sign_mul_swap {m : ℕ} (σ : Equiv.Perm (Fin m)) {i j : Fin m} (hij : i ≠ j) :
    Equiv.Perm.sign (σ * Equiv.swap i j) = - Equiv.Perm.sign σ := by
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, mul_neg_one]

/-! 9.35 Permutations and alternating multilinear forms

For {lit}`α ∈ V⁽ᵐ⁾ₐₗₜ`,
{lit}`α(v_{j₁}, …, v_{jₘ}) = (sign(j₁, …, jₘ)) α(v₁, …, vₘ)`. In mathlib this is
{name}`AlternatingMap.map_perm`: reindexing the inputs by {lit}`σ` scales the
value by {lit}`sign σ`. -/

theorem map_perm_eq_sign_smul {m : ℕ} (α : V [⋀^Fin m]→ₗ[F] F) (v : Fin m → V)
    (σ : Equiv.Perm (Fin m)) :
    α (v ∘ σ) = Equiv.Perm.sign σ • α v :=
  α.map_perm v σ

/-! 9.36 Formula for {lit}`(dim V)`-linear alternating forms on {lit}`V`

Let {lit}`n = dim V` with basis {lit}`e₁, …, eₙ`. Writing {lit}`vₖ = ∑ⱼ bⱼ,ₖ eⱼ`
(so {lit}`bⱼ,ₖ = eⱼ'(vₖ)` are the basis coordinates), every alternating
{lit}`n`-linear form {lit}`α` satisfies
{lit}`α(v₁, …, vₙ) = α(e₁, …, eₙ) · ∑_{σ ∈ perm n} sign(σ) b_{σ1,1} ⋯ b_{σn,n}`.

mathlib packages the permutation sum as the determinant {name}`Module.Basis.det`
of the coordinate matrix ({name}`Module.Basis.det_apply` and
{name}`Matrix.det_apply`), and the whole statement is
{name}`AlternatingMap.eq_smul_basis_det`: {lit}`α = α(e) • e.det`. -/

theorem alternating_formula {n : ℕ} (e : Fin n → V) (he : IsBasis F e)
    (α : V [⋀^Fin n]→ₗ[F] F) (v : Fin n → V) :
    α v =
      α e •
        ∑ σ : Equiv.Perm (Fin n),
          Equiv.Perm.sign σ • ∏ k, he.toModuleBasis.repr (v k) (σ k) := by
  set b := he.toModuleBasis with hb
  -- {lit}`⇑b = e`, so {lit}`α ⇑b = α e`.
  have hbe : (⇑b : Fin n → V) = e := funext fun k => he.toModuleBasis_apply k
  -- Axler's formula is {name}`AlternatingMap.eq_smul_basis_det` expanded via the
  -- Leibniz formula for {name}`Module.Basis.det`.
  have hexp : b.det v = ∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ∏ k, b.repr (v k) (σ k) := by
    simp only [Module.Basis.det_apply, Matrix.det_apply, Module.Basis.toMatrix_apply]
  have happ := DFunLike.congr_fun (AlternatingMap.eq_smul_basis_det (e := b) α) v
  rw [AlternatingMap.smul_apply] at happ
  rw [happ, hbe, hexp]

/-! 9.37 `dim V⁽ᵈⁱᵐ ⱽ⁾ₐₗₜ = 1`

The vector space of alternating {lit}`(dim V)`-linear forms on {lit}`V` has dimension
one. By 9.36 every such form is a scalar multiple of {name}`Module.Basis.det`,
which is nonzero ({name}`Module.Basis.det_ne_zero`); hence {lit}`{e.det}` is a
basis of a one-dimensional space. -/

theorem finrank_alternating_eq_one [Finite F V] :
    finrank F (V [⋀^Fin (finrank F V)]→ₗ[F] F) = 1 := by
  classical
  let b : Module.Basis (Fin (finrank F V)) F V := Module.finBasis F V
  refine finrank_eq_one b.det b.det_ne_zero (fun α => ⟨α b, ?_⟩)
  exact (AlternatingMap.eq_smul_basis_det (e := b) α).symm

/-! 9.38 A nonzero alternating {lit}`n`-linear form exists

Axler constructs a nonzero alternating {lit}`n`-form directly from the dual basis
(formula 9.38), used above to rule out {lit}`dim V⁽ⁿ⁾ₐₗₜ = 0`. mathlib's
{name}`Module.Basis.det` *is* that form: it is alternating, and 9.38 evaluated at
{lit}`vₖ = eₖ` gives {lit}`α(e₁, …, eₙ) = 1`, which is
{name}`Module.Basis.det_self`. -/

example {n : ℕ} (e : Fin n → V) (he : IsBasis F e) :
    he.toModuleBasis.det he.toModuleBasis = 1 :=
  he.toModuleBasis.det_self

/-! 9.39 Alternating {lit}`(dim V)`-linear forms and linear independence

Let {lit}`n = dim V` and let {lit}`α` be a *nonzero* alternating {lit}`n`-linear form.
Then {lit}`α(e₁, …, eₙ) ≠ 0` if and only if {lit}`e₁, …, eₙ` is linearly
independent. (The forward direction is 9.28; the reverse uses that a linearly
independent list of length {lit}`n = dim V` is a basis (2.38), and that a nonzero
alternating form is nonzero on any basis, {name}`AlternatingMap.map_basis_ne_zero_iff`.) -/

theorem apply_basis_ne_zero_iff_linearIndependent [Finite F V]
    (e : Fin (finrank F V) → V) (α : V [⋀^Fin (finrank F V)]→ₗ[F] F) (hα : α ≠ 0) :
    α e ≠ 0 ↔ LinearIndependent F e := by
  constructor
  · -- If {lit}`α(e) ≠ 0`, then {lit}`e` is linearly independent (else 9.28 gives
    -- {lit}`α(e) = 0`).
    intro he
    by_contra hdep
    exact he (α.map_linearDependent e hdep)
  · -- If {lit}`e` is linearly independent of length {lit}`dim V`, it is a basis,
    -- and a nonzero alternating form is nonzero on a basis.
    intro hli
    have hb : IsBasis F e :=
      LADR.Section_2C.isBasis_of_linearIndependent_of_card_eq e hli rfl
    have hbe : (⇑hb.toModuleBasis : Fin (finrank F V) → V) = e :=
      funext fun k => hb.toModuleBasis_apply k
    have := (AlternatingMap.map_basis_ne_zero_iff hb.toModuleBasis α).mpr hα
    rwa [hbe] at this

/-- 9.40 Definition: {lit}`α_T`. For {lit}`α` an alternating {lit}`m`-linear form
and {lit}`T ∈ ℒ(V)`, Axler defines {lit}`α_T(v₁, …, vₘ) = α(Tv₁, …, Tvₘ)`, the
precomposition of {lit}`α` with {lit}`T` in every slot — mathlib's
{name}`AlternatingMap.compLinearMap`. -/
def altCompOp {m : ℕ} (α : V [⋀^Fin m]→ₗ[F] F) (T : V →ₗ[F] V) : V [⋀^Fin m]→ₗ[F] F :=
  α.compLinearMap T

theorem altCompOp_apply {m : ℕ} (α : V [⋀^Fin m]→ₗ[F] F) (T : V →ₗ[F] V) (v : Fin m → V) :
    altCompOp α T v = α (fun i => T (v i)) :=
  rfl

/-! 9.41 Definition: determinant of an operator, {lit}`det T`. Axler defines
{lit}`det T` as the unique scalar with {lit}`α_T = (det T) · α` for every alternating
{lit}`(dim V)`-form {lit}`α` (well-defined because {lit}`dim V⁽ⁿ⁾ₐₗₜ = 1`, 9.37,
so any two top alternating forms are proportional). This companion uses mathlib's
{name}`LinearMap.det` throughout Section 9C, where its determinant properties
(9.42–9.61) are developed. -/

/-! # Exercises 9B -/

/-- 9B.1 {lit}`dim V⁽ᵐ⁾ = (dim V)ᵐ`: the space of {lit}`m`-linear forms on an
{lit}`n`-dimensional space has dimension {lit}`nᵐ`. -/
theorem exercise_9B_1 [Finite F V] (m : ℕ) :
    finrank F (MultilinearMap F (fun _ : Fin m => V) F) = (finrank F V) ^ m := by
  sorry

/-- 9B.2 For {lit}`n ≥ 3`, the map {lit}`α` on {lit}`Fⁿ × Fⁿ × Fⁿ` given by
{lit}`x₁y₂z₃ − x₂y₁z₃ − x₃y₂z₁ − x₁y₃z₂ + x₃y₁z₂ + x₂y₃z₁` is an alternating
3-linear form. (Indices are 0-based here.) -/
theorem exercise_9B_2 {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ α : (Fin n → F) [⋀^Fin 3]→ₗ[F] F,
      ∀ x y z : Fin n → F,
        α ![x, y, z] =
          x 0 * y 1 * z 2 - x 1 * y 0 * z 2 - x 2 * y 1 * z 0
            - x 0 * y 2 * z 1 + x 2 * y 0 * z 1 + x 1 * y 2 * z 0 := by
  sorry

/-- 9B.3 If an {lit}`m`-linear form vanishes whenever two *adjacent* inputs are equal
({lit}`vⱼ = vⱼ₊₁`), then it is alternating (vanishes whenever any two inputs are
equal). -/
theorem exercise_9B_3 {m : ℕ} (α : MultilinearMap F (fun _ : Fin m => V) F)
    (h : ∀ (v : Fin m → V) (j k : Fin m), (k : ℕ) = (j : ℕ) + 1 → v j = v k → α v = 0) :
    ∀ (v : Fin m → V) (i j : Fin m), v i = v j → i ≠ j → α v = 0 := by
  sorry

/-- 9B.4 Prove or give a counterexample: for {lit}`α ∈ V⁽⁴⁾ₐₗₜ`, the zero set
{lit}`{(v₁, v₂, v₃, v₄) : α(v₁, v₂, v₃, v₄) = 0}` is a subspace of {lit}`V⁴`. This
is *false*; we exhibit an {lit}`α` on {lit}`ℝ⁴` and two {lit}`4`-tuples in the zero set
whose sum is not, so the zero set is not closed under addition. -/
theorem exercise_9B_4 :
    ∃ (α : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ) (a b : Fin 4 → (Fin 4 → ℝ)),
      α a = 0 ∧ α b = 0 ∧ α (a + b) ≠ 0 := by
  sorry

/-- 9B.5 If {lit}`β` is an {lit}`m`-linear form, then
{lit}`α(v₁, …, vₘ) = ∑_{σ ∈ perm m} sign(σ) β(v_{σ1}, …, v_{σm})` is an
*alternating* {lit}`m`-linear form. -/
theorem exercise_9B_5 {m : ℕ} (β : MultilinearMap F (fun _ : Fin m => V) F) :
    ∃ α : V [⋀^Fin m]→ₗ[F] F,
      ∀ v : Fin m → V,
        α v = ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • β (v ∘ σ) := by
  sorry

/-- 9B.6 If {lit}`β` is an {lit}`m`-linear form, then
{lit}`α(v₁, …, vₘ) = ∑_{σ ∈ perm m} β(v_{σ1}, …, v_{σm})` is *symmetric*:
{lit}`α(v_{k₁}, …, v_{kₘ}) = α(v₁, …, vₘ)` for every permutation {lit}`(k₁, …, kₘ)`. -/
theorem exercise_9B_6 {m : ℕ} (β : MultilinearMap F (fun _ : Fin m => V) F) :
    ∃ α : MultilinearMap F (fun _ : Fin m => V) F,
      (∀ v : Fin m → V, α v = ∑ σ : Equiv.Perm (Fin m), β (v ∘ σ)) ∧
      ∀ (v : Fin m → V) (τ : Equiv.Perm (Fin m)), α (v ∘ τ) = α v := by
  sorry

/-- 9B.7 A nonzero alternating 2-linear form {lit}`α` on {lit}`ℝ³` and a linearly
independent list {lit}`v₁, v₂` in {lit}`ℝ³` with {lit}`α(v₁, v₂) = 0`. This shows
9.39 can fail without the hypothesis {lit}`n = dim V` (here {lit}`2 < 3`). -/
theorem exercise_9B_7 :
    ∃ (α : (Fin 3 → ℝ) [⋀^Fin 2]→ₗ[ℝ] ℝ) (v : Fin 2 → (Fin 3 → ℝ)),
      α ≠ 0 ∧ LinearIndependent ℝ v ∧ α v = 0 := by
  sorry

end LADR.Section_9B
