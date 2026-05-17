import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 1C: Subspaces
-/

namespace LADR.Section_1C

/-! Reminder: This is how we say V is a vector space over F in mathlib -/
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! 1.33 Definition: subspace

A subset of {lit}`V` is called a *subspace* of {lit}`V` if it is itself a vector
space with the same additive identity, addition, and scalar multiplication.

In Lean/mathlib the bundled object {name}`Submodule` carries the carrier set
together with the three closure proofs at once. -/

/-! 1.34 Conditions for a subspace

A subset is a subspace iff it contains {lit}`0`, is closed under addition, and is
closed under scalar multiplication. These are exactly the three fields of
{name}`Submodule`. -/

recall Submodule.zero_mem {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) : (0 : M) ∈ p
recall Submodule.add_mem {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) {x y : M} (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p
recall Submodule.smul_mem {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (p : Submodule R M) {x : M} (r : R) (h : x ∈ p) : r • x ∈ p

/-! Conversely, Axler's 1.34 says these three conditions are *enough*: any
subset {lit}`S ⊆ V` containing {lit}`0` and closed under addition and scalar
multiplication is itself a vector space under the operations inherited from
{lit}`V`. We prove every vector-space axiom on the subtype {lit}`↥S` directly
from the three closure assumptions and the corresponding axiom in {lit}`V`. -/

/-! In what follows, {lit}`S : Set V` is an arbitrary subset and {lit}`h0`,
{lit}`hadd`, {lit}`hsmul` are the three closure assumptions of Axler 1.34. -/

/-! The inherited operations on the subtype {lit}`↥S`. Closure under {lit}`0`,
{lit}`+`, {lit}`•` is exactly what lets each operation land back inside
{lit}`S`. The additive inverse uses {lit}`-u = (-1) • u`, which is why we don't
need a fourth closure assumption. -/

def subZero (S : Set V) (h0 : (0 : V) ∈ S) : S := ⟨0, h0⟩

def subAdd (S : Set V) (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S)
    (u w : S) : S := ⟨u.1 + w.1, hadd u.1 w.1 u.2 w.2⟩

def subNeg (S : Set V) (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (u : S) :
    S := ⟨-u.1, by simpa using hsmul (-1) u.1 u.2⟩

def subSMul (S : Set V) (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S)
    (a : F) (u : S) : S := ⟨a • u.1, hsmul a u.1 u.2⟩

/-! Each vector-space axiom on {lit}`↥S` is now a one-line proof: unfold the
inherited operation with {name}`Subtype.ext`, then invoke the corresponding
axiom of {lit}`V`. -/

theorem sub_add_assoc (S : Set V)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S) (u w x : S) :
    subAdd S hadd (subAdd S hadd u w) x = subAdd S hadd u (subAdd S hadd w x) :=
  Subtype.ext (add_assoc u.1 w.1 x.1)

theorem sub_add_comm (S : Set V)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S) (u w : S) :
    subAdd S hadd u w = subAdd S hadd w u :=
  Subtype.ext (add_comm u.1 w.1)

theorem sub_zero_add (S : Set V) (h0 : (0 : V) ∈ S)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S) (u : S) :
    subAdd S hadd (subZero S h0) u = u :=
  Subtype.ext (zero_add u.1)

theorem sub_add_zero (S : Set V) (h0 : (0 : V) ∈ S)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S) (u : S) :
    subAdd S hadd u (subZero S h0) = u :=
  Subtype.ext (add_zero u.1)

theorem sub_neg_add_cancel (S : Set V) (h0 : (0 : V) ∈ S)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (u : S) :
    subAdd S hadd (subNeg S hsmul u) u = subZero S h0 :=
  Subtype.ext (neg_add_cancel u.1)

theorem sub_one_smul (S : Set V)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (u : S) :
    subSMul S hsmul 1 u = u :=
  Subtype.ext (one_smul F u.1)

theorem sub_mul_smul (S : Set V)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (a b : F) (u : S) :
    subSMul S hsmul (a * b) u = subSMul S hsmul a (subSMul S hsmul b u) :=
  Subtype.ext (mul_smul a b u.1)

theorem sub_smul_add (S : Set V)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (a : F) (u w : S) :
    subSMul S hsmul a (subAdd S hadd u w)
      = subAdd S hadd (subSMul S hsmul a u) (subSMul S hsmul a w) :=
  Subtype.ext (smul_add a u.1 w.1)

theorem sub_add_smul (S : Set V)
    (hadd : ∀ (u w : V), u ∈ S → w ∈ S → u + w ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (a b : F) (u : S) :
    subSMul S hsmul (a + b) u
      = subAdd S hadd (subSMul S hsmul a u) (subSMul S hsmul b u) :=
  Subtype.ext (add_smul a b u.1)

theorem sub_zero_smul (S : Set V) (h0 : (0 : V) ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (u : S) :
    subSMul S hsmul 0 u = subZero S h0 :=
  Subtype.ext (zero_smul F u.1)

theorem sub_smul_zero (S : Set V) (h0 : (0 : V) ∈ S)
    (hsmul : ∀ (a : F) (u : V), u ∈ S → a • u ∈ S) (a : F) :
    subSMul S hsmul a (subZero S h0) = subZero S h0 :=
  Subtype.ext (smul_zero a)

/-! In particular every subspace is closed under additive inverses, since
{lit}`-u = (-1) • u`. -/

example (U : Submodule F V) {u : V} (hu : u ∈ U) : -u ∈ U := U.neg_mem hu

/-! 1.35 Example: subspaces / Exercise 1C.2

Verify that the sets in (a)–(e) are subspaces. We give the carrier, the
{lit}`0`-membership proof, and the scalar-closure proof; the additive-closure
{lit}`add_mem'` is left as {lit}`sorry` for the reader. -/

/-! 1.35(a) The set {lit}`{(x₁, x₂, x₃, x₄) ∈ F⁴ : x₃ = 5 x₄ + b}` is a
subspace of {lit}`F⁴` iff {lit}`b = 0` (the {lit}`b = 0` direction is shown
here; both directions are exercise 1C.1 above). -/

example : Submodule F (Fin 4 → F) where
  carrier := {v | v 2 = 5 * v 3}
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    norm_num
  add_mem' := by simp; grind
  smul_mem' := by simp; grind

/-! 1.35(b) Continuous real-valued functions on {lit}`[0, 1]` form a subspace
of {lit}`ℝ^[0,1]`. (Axler uses {lit}`[0, 1]`; we work over all of {lit}`ℝ` —
the closure proofs are identical.) -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' := by
    intro f g hf hg
    simp at *
    fun_prop
  smul_mem' := by
    intro a f hf
    simp at *
    rw [show a • f = (fun x => a * f x) by funext; simp]
    fun_prop


/-! 1.35(c) Differentiable real-valued functions on {lit}`ℝ` form a subspace
of {lit}`ℝ^ℝ`. -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Differentiable ℝ f}
  zero_mem' := differentiable_const 0
  add_mem' := by
    intro f g hf hg
    simp at *
    fun_prop
  smul_mem' := by
    intro a f hf
    simp at *
    rw [show a • f = (fun x => a * f x) by funext; simp]
    fun_prop

/-! 1.35(d) Differentiable real-valued functions on {lit}`(0, 3)` such that
{lit}`f'(2) = 0` form a subspace. We work on all of {lit}`ℝ` and pin the
derivative at {lit}`2`; both addition and scalar multiplication preserve the
derivative being zero at a point. -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Differentiable ℝ f ∧ deriv f 2 = 0}
  zero_mem' := ⟨differentiable_const 0, by simp⟩
  add_mem' := by
    rintro f g ⟨ hf1, hf2 ⟩ ⟨ hg1, hg2 ⟩
    simp at *
    constructor
    · fun_prop
    rw [deriv_add]
    · linarith
    · fun_prop
    · fun_prop
  smul_mem' := by
    rintro a f ⟨ hf1, hf2 ⟩
    simp at *
    constructor
    · fun_prop
    rw [deriv_const_smul]
    rw [hf2]
    simp
    fun_prop

/-! 1.35(e) Sequences of complex numbers with limit {lit}`0` form a subspace
of {lit}`ℂ^∞`. In Lean, "sequence" is {lit}`ℕ → ℂ` and "has limit {lit}`0`" is
{lit}`Filter.Tendsto f Filter.atTop (𝓝 0)`. -/

example : Submodule ℂ (ℕ → ℂ) where
  carrier := {f | Filter.Tendsto f Filter.atTop (nhds 0)}
  zero_mem' := tendsto_const_nhds
  add_mem' := by
    intro f g hf hg
    simp at *
    have := Filter.Tendsto.add hf hg
    simpa
  smul_mem' := by
    intro a f hf
    simp at *
    rw [show a • f = (fun x => a * f x) by funext; simp]
    have := Filter.Tendsto.const_mul a hf
    simpa

/-! Two distinguished subspaces every space has: the trivial subspace {lit}`{0}`
({name}`Bot.bot`) and the whole space {name}`Top.top`. -/

example : Submodule F V := ⊥
example : Submodule F V := ⊤
example (v : V) : v ∈ (⊤ : Submodule F V) := Submodule.mem_top
example (v : V) : v ∈ (⊥ : Submodule F V) ↔ v = 0 := Submodule.mem_bot F

/-! 1.36 Definition: sum of subspaces

For subspaces {lit}`V₁, …, Vₘ` of {lit}`V`, the sum
{lit}`V₁ + ⋯ + Vₘ = {v₁ + ⋯ + vₘ : vₖ ∈ Vₖ}` is the set of all such sums.

For two subspaces, mathlib's lattice supremum {lit}`U ⊔ W` is exactly the sum,
and {lit}`U + W` resolves to the same thing via {name}`Submodule.add_eq_sup`. -/

example (U W : Submodule F V) : Submodule F V := U ⊔ W
example (U W : Submodule F V) : U + W = U ⊔ W := Submodule.add_eq_sup U W

/-! Membership in {lit}`U ⊔ W` is exactly the textbook formula. -/

example (U W : Submodule F V) (x : V) :
    x ∈ U ⊔ W ↔ ∃ y ∈ U, ∃ z ∈ W, y + z = x := Submodule.mem_sup

/-! Axler defines {lit}`V₁ + ⋯ + Vₘ` as a single n-ary operation. To make
sense of an iterated binary {lit}`⊔` we need the binary sum to be associative
and commutative — both inherit from {lit}`Submodule F V` being a lattice.
(These are also exercises 1C.16 and 1C.17 below.) -/

example (U W : Submodule F V) : U ⊔ W = W ⊔ U := sup_comm U W
example (V₁ V₂ V₃ : Submodule F V) : (V₁ ⊔ V₂) ⊔ V₃ = V₁ ⊔ (V₂ ⊔ V₃) :=
  sup_assoc V₁ V₂ V₃

/-! So {lit}`V₁ + V₂ + V₃` is unambiguous: the textbook formula
{lit}`{v₁ + v₂ + v₃ : vₖ ∈ Vₖ}` matches either bracketing. -/

example (V₁ V₂ V₃ : Submodule F V) (x : V) :
    x ∈ V₁ ⊔ V₂ ⊔ V₃ ↔ ∃ v₁ ∈ V₁, ∃ v₂ ∈ V₂, ∃ v₃ ∈ V₃, v₁ + v₂ + v₃ = x := by
  rw [Submodule.mem_sup]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, v₃, hv₃, rfl⟩
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, rfl⟩
  · rintro ⟨v₁, hv₁, v₂, hv₂, v₃, hv₃, rfl⟩
    exact ⟨v₁ + v₂, Submodule.mem_sup.mpr ⟨v₁, hv₁, v₂, hv₂, rfl⟩, v₃, hv₃, rfl⟩

/-! For arbitrary {lit}`m`, mathlib's indexed supremum {lit}`⨆ i, W i` plays
the role of Axler's {lit}`V₁ + ⋯ + Vₘ`. Membership recovers the textbook
formula {lit}`{v₁ + ⋯ + vₘ : vₖ ∈ Vₖ}`. -/

example (m : ℕ) (W : Fin m → Submodule F V) (x : V) :
    x ∈ ⨆ i, W i ↔ ∃ v : (i : Fin m) → W i, ∑ i, ((v i : V)) = x := by
  rw [show (⨆ i, W i) = ⨆ i ∈ (Finset.univ : Finset (Fin m)), W i by simp]
  rw [Submodule.mem_iSup_finset_iff_exists_sum]

/-! 1.37 Example: a sum of subspaces of {lit}`F³`

With {lit}`U = {(x, 0, 0) : x ∈ F}` and {lit}`W = {(0, y, 0) : y ∈ F}`,
{lit}`U + W = {(x, y, 0) : x, y ∈ F}`, i.e. the vectors whose third coordinate
is zero. -/

namespace Example_1_37

def U : Submodule F (Fin 3 → F) where
  carrier := {v | v 1 = 0 ∧ v 2 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

def W : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = 0 ∧ v 2 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

example : (U ⊔ W : Submodule F (Fin 3 → F)) =
    { carrier := {v | v 2 = 0}
      zero_mem' := rfl
      add_mem' := by
        intro u v hu hv
        show u 2 + v 2 = 0
        rw [show u 2 = 0 from hu, show v 2 = 0 from hv, add_zero]
      smul_mem' := by
        intro a v hv
        show a • v 2 = 0
        rw [show v 2 = 0 from hv, smul_zero] } := by
  ext v
  rw [Submodule.mem_sup]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨_, hy2⟩, z, ⟨_, hz2⟩, rfl⟩
    show y 2 + z 2 = 0
    rw [hy2, hz2, add_zero]
  · intro (hv : v 2 = 0)
    refine ⟨![v 0, 0, 0], ⟨rfl, rfl⟩, ![0, v 1, 0], ⟨rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> simp [hv]

end Example_1_37

/-! 1.38/1.39 Example: a sum of subspaces of {lit}`F⁴`

With {lit}`U = {(x, x, y, y) : x, y ∈ F}` and {lit}`W = {(x, x, x, y) : x, y ∈ F}`
we have {lit}`U + W = {(x, x, y, z) : x, y, z ∈ F}` — exactly the vectors whose
first two coordinates are equal. -/

namespace Example_1_38

def U : Submodule F (Fin 4 → F) where
  carrier := {v | v 0 = v 1 ∧ v 2 = v 3}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

def W : Submodule F (Fin 4 → F) where
  carrier := {v | v 0 = v 1 ∧ v 1 = v 2}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

example : (U ⊔ W : Submodule F (Fin 4 → F)) =
    { carrier := {v | v 0 = v 1}
      zero_mem' := rfl
      add_mem' := by
        intro u v hu hv
        show u 0 + v 0 = u 1 + v 1
        rw [show u 0 = u 1 from hu, show v 0 = v 1 from hv]
      smul_mem' := by
        intro a v hv
        show a • v 0 = a • v 1
        rw [show v 0 = v 1 from hv] } := by
  ext v
  rw [Submodule.mem_sup]
  refine ⟨?_, ?_⟩
  · rintro ⟨y, ⟨hy01, _⟩, z, ⟨hz01, _⟩, rfl⟩
    show y 0 + z 0 = y 1 + z 1
    rw [hy01, hz01]
  · intro (hv : v 0 = v 1)
    refine ⟨![0, 0, v 2 - v 0, v 2 - v 0], ⟨rfl, rfl⟩,
            ![v 0, v 0, v 0, v 3 - v 2 + v 0], ⟨rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> simp [hv]

end Example_1_38

/-! 1.40 Sum is the smallest containing subspace.

Axler's argument has three steps:
(i) The sum is itself a subspace — built into the type {lit}`U ⊔ W : Submodule F V`,
    which 1.34 (the {name}`Submodule` constructor) already supplied.
(ii) Each summand is contained in the sum: take {lit}`u = u + 0` and
    {lit}`w = 0 + w` (Axler's "consider sums where all except one are 0").
 -/
example (U W : Submodule F V) : U ≤ U ⊔ W :=
  fun u hu => Submodule.mem_sup.mpr ⟨u, hu, 0, W.zero_mem, add_zero u⟩
example (U W : Submodule F V) : W ≤ U ⊔ W :=
  fun w hw => Submodule.mem_sup.mpr ⟨0, U.zero_mem, w, hw, zero_add w⟩

/-! (iii) Any subspace containing both summands contains the sum, because subspaces
    are closed under addition. -/
example (U W X : Submodule F V) (h₁ : U ≤ X) (h₂ : W ≤ X) : U ⊔ W ≤ X := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  exact X.add_mem (h₁ hy) (h₂ hz)

/-! 1.41 Definition: direct sum, ⊕

The sum {lit}`V₁ + ⋯ + Vₘ` is a *direct sum* if each element has only one
representation as {lit}`v₁ + ⋯ + vₘ` with each {lit}`vₖ ∈ Vₖ`. -/

/-! The property that the collection of subspaces {lit}`W₁, ..., Wₘ` satisfies `W₁ ⊕ ... ⊕ Wₘ = W₁ + ... + Wₘ`. -/
def IsDirectSum {m : ℕ} (W : Fin m → Submodule F V) : Prop :=
  ∀ (u v : (i : Fin m) → W i),
    (∑ i, ((u i : V))) = (∑ i, ((v i : V))) → u = v

/-! 1.42 Example: a direct sum of two subspaces -/

namespace Example_1_42

def U : Submodule F (Fin 3 → F) where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 2 + v 2 = 0; rw [hu, hv, add_zero]
  smul_mem' := by intro a v hv; show a • v 2 = 0; rw [hv, smul_zero]

def W : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = 0 ∧ v 1 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h0, h1⟩ ⟨h0', h1'⟩
    exact ⟨by simp [Pi.add_apply, h0, h0'], by simp [Pi.add_apply, h1, h1']⟩
  smul_mem' := by
    rintro a v ⟨h0, h1⟩
    exact ⟨by simp [Pi.smul_apply, h0], by simp [Pi.smul_apply, h1]⟩

/-! Axler's "F³ = U ⊕ W" splits into two claims: the sum is *direct*
({lit}`IsDirectSum ![U, W]`), and the sum is *all of F³*
({lit}`U ⊔ W = ⊤`). -/

example : IsDirectSum (F := F) ![U, W] := by
  intro f g hfg
  -- f, g : (i : Fin 2) → ![U, W] i. Show f i = g i for i = 0 and i = 1.
  -- The sum equality at coordinates 0, 1, 2 pins down each component.
  funext i
  apply Subtype.ext
  -- Read off the constraints from f 0 ∈ U, f 1 ∈ W (and similarly for g).
  -- f 0 has v 2 = 0, f 1 has v 0 = v 1 = 0; the sum at j gives:
  --   j = 0: (f 0) 0 + 0 = (g 0) 0 + 0  ⟹  (f 0) 0 = (g 0) 0
  --   j = 1: (f 0) 1 + 0 = (g 0) 1 + 0  ⟹  (f 0) 1 = (g 0) 1
  --   j = 2: 0 + (f 1) 2 = 0 + (g 1) 2  ⟹  (f 1) 2 = (g 1) 2
  have hf0 := (f 0).2
  have hf1 := (f 1).2
  have hg0 := (g 0).2
  have hg1 := (g 1).2
  fin_cases i <;> funext j <;> fin_cases j
  · have h := congrFun hfg 0; simpa [Fin.sum_univ_two, hf1.1, hg1.1] using h
  · have h := congrFun hfg 1; simpa [Fin.sum_univ_two, hf1.2, hg1.2] using h
  · exact hf0.trans hg0.symm
  · exact hf1.1.trans hg1.1.symm
  · exact hf1.2.trans hg1.2.symm
  · have h := congrFun hfg 2
    simp only [Fin.sum_univ_two, Pi.add_apply] at h
    rw [hf0, hg0, zero_add, zero_add] at h
    exact h

example : (U : Submodule F (Fin 3 → F)) ⊔ W = ⊤ := by
  rw [eq_top_iff]
  intro v _
  refine Submodule.mem_sup.mpr ⟨![v 0, v 1, 0], rfl,
          ![0, 0, v 2], ⟨rfl, rfl⟩, ?_⟩
  funext i; fin_cases i <;> simp

end Example_1_42

/-! 1.43 Example: a direct sum of multiple subspaces -/

namespace Example_1_43

/-! The subspace of {lit}`Fⁿ` consisting of vectors with 0 at all coordinates except possibly at {lit}`k`. -/
def Axis (n : ℕ) (k : Fin n) : Submodule F (Fin n → F) where
  carrier := {v | ∀ i, i ≠ k → v i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by
    intro u v hu hv i hi
    show u i + v i = 0
    rw [hu i hi, hv i hi, add_zero]
  smul_mem' := by
    intro a v hv i hi
    show a • v i = 0
    rw [hv i hi, smul_zero]

example (n : ℕ) : IsDirectSum (Axis (F := F) n) := by
  intro u v huv
  -- Pick an index k; show u k = v k as functions Fin n → F.
  funext k
  apply Subtype.ext
  funext j
  -- Off-diagonal coords are 0 by membership in Axis n k.
  by_cases hjk : j = k
  · -- At j = k, the sum collapses to (u k) k = (v k) k.
    rw [hjk]
    have hu : (∑ i, ((u i : Fin n → F))) k = (u k : Fin n → F) k := by
      rw [Finset.sum_apply]
      apply Finset.sum_eq_single k
      · intro i _ hik; exact (u i).2 k hik.symm
      · intro h; exact absurd (Finset.mem_univ k) h
    have hv : (∑ i, ((v i : Fin n → F))) k = (v k : Fin n → F) k := by
      rw [Finset.sum_apply]
      apply Finset.sum_eq_single k
      · intro i _ hik; exact (v i).2 k hik.symm
      · intro h; exact absurd (Finset.mem_univ k) h
    have h := congrArg (· k) huv
    simp only at h
    rw [← hu, ← hv, h]
  · rw [(u k).2 j hjk, (v k).2 j hjk]

/-! Sum is everything: every {lit}`v ∈ Fⁿ` decomposes as
{lit}`v = e_1(v) + ⋯ + e_n(v)`. -/

example (n : ℕ) : (⨆ k, Axis (F := F) n k) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  -- e_k(v) := Function.update 0 k (v k), with closure proof inline.
  have h : (∑ k, (⟨Function.update (0 : Fin n → F) k (v k),
            fun i hi => by rw [Function.update_of_ne hi _ _]; rfl⟩
              : Axis (F := F) n k).1) = v := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j
        (fun i _ hij => by
          show Function.update (0 : Fin n → F) i (v i) j = 0
          rw [Function.update_of_ne hij.symm _ _]; rfl)
        (fun h => absurd (Finset.mem_univ j) h)]
    show Function.update (0 : Fin n → F) j (v j) j = v j
    simp
  rw [← h]
  exact Submodule.sum_mem_iSup (fun k => (⟨_, _⟩ : Axis (F := F) n k).2)

end Example_1_43

/-! 1.44 Example: a sum that is *not* a direct sum

In {lit}`F³`, take
{lit}`V₁ = {(x, y, 0)}`, {lit}`V₂ = {(0, 0, z)}`, {lit}`V₃ = {(0, y, y)}`.
Then {lit}`F³ = V₁ + V₂ + V₃` but {lit}`0` has more than one representation, so
the sum is *not* direct. Pairwise intersections are all {lit}`{0}`, which is
why 1.46 below characterizes direct sums only of *two* subspaces. -/

namespace Example_1_44

def V₁ : Submodule F (Fin 3 → F) where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 2 + v 2 = 0; rw [hu, hv, add_zero]
  smul_mem' := by intro a v hv; show a • v 2 = 0; rw [hv, smul_zero]

def V₂ : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = 0 ∧ v 1 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h0, h1⟩ ⟨h0', h1'⟩
    exact ⟨by simp [Pi.add_apply, h0, h0'], by simp [Pi.add_apply, h1, h1']⟩
  smul_mem' := by
    rintro a v ⟨h0, h1⟩
    exact ⟨by simp [Pi.smul_apply, h0], by simp [Pi.smul_apply, h1]⟩

def V₃ : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = 0 ∧ v 1 = v 2}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h0, h12⟩ ⟨h0', h12'⟩
    refine ⟨by simp [Pi.add_apply, h0, h0'], ?_⟩
    show u 1 + v 1 = u 2 + v 2
    rw [h12, h12']
  smul_mem' := by
    rintro a v ⟨h0, h12⟩
    refine ⟨by simp [Pi.smul_apply, h0], ?_⟩
    show a • v 1 = a • v 2
    rw [h12]

/-! Two distinct representations of {lit}`0`:
- the trivial one (all zero),
- {lit}`v₁ = (0, 1, 0) ∈ V₁`, {lit}`v₂ = (0, 0, 1) ∈ V₂`,
  {lit}`v₃ = (0, -1, -1) ∈ V₃`. Their sum is {lit}`(0, 0, 0) = 0`. -/

example : ¬ IsDirectSum (F := F) ![V₁, V₂, V₃] := by
  intro h
  -- The nontrivial witness, packaged member-by-member.
  have m₀ : (![0, 1, 0] : Fin 3 → F) ∈ ![V₁, V₂, V₃] (0 : Fin 3) := rfl
  have m₁ : (![0, 0, 1] : Fin 3 → F) ∈ ![V₁, V₂, V₃] (1 : Fin 3) := ⟨rfl, rfl⟩
  have m₂ : (![0, -1, -1] : Fin 3 → F) ∈ ![V₁, V₂, V₃] (2 : Fin 3) := ⟨rfl, rfl⟩
  let f : (i : Fin 3) → ![V₁, V₂, V₃] i := fun i =>
    match i with
    | ⟨0, _⟩ => ⟨_, m₀⟩
    | ⟨1, _⟩ => ⟨_, m₁⟩
    | ⟨2, _⟩ => ⟨_, m₂⟩
  let g : (i : Fin 3) → ![V₁, V₂, V₃] i := fun i =>
    ⟨(0 : Fin 3 → F), (![V₁, V₂, V₃] i).zero_mem⟩
  have hsum : (∑ i, ((f i : Fin 3 → F))) = (∑ i, ((g i : Fin 3 → F))) := by
    funext j
    fin_cases j <;> simp [f, g, Fin.sum_univ_three]
  have heq : f = g := h f g hsum
  -- f 0 = (0, 1, 0); reading coordinate 1 yields 1 = 0.
  have h1 : (f 0 : Fin 3 → F) 1 = (g 0 : Fin 3 → F) 1 := by rw [heq]
  simp [f, g] at h1

end Example_1_44

/-! Addendum: unit tests for direct sum definition

These unit tests attempt to verify that the definition of {lit}`IsDirectSum` matches the description given in its docstring.

In particular, `IsDirectSum ![W₁, ..., Wₘ]` does not imply that `W₁ + ... + Wₘ = ⊤`.
-/

def a1 := Example_1_43.Axis (F := F) 5 0
def a2 := Example_1_43.Axis (F := F) 5 1

example : IsDirectSum (F := F) ![a1, a2] := by
  intro u v huv
  ext i j
  have h := congrFun huv j
  simp only [Fin.sum_univ_two, Pi.add_apply] at h
  fin_cases i
  · by_cases hj : j = 0
    · subst hj; simpa [(u 1).2 0 (by decide), (v 1).2 0 (by decide)] using h
    · exact ((u 0).2 j hj).trans ((v 0).2 j hj).symm
  · by_cases hj : j = 1
    · subst hj; simpa [(u 0).2 1 (by decide), (v 0).2 1 (by decide)] using h
    · exact ((u 1).2 j hj).trans ((v 1).2 j hj).symm

/-! 1.45 Condition for a direct sum -/

theorem isDirectSum_iff_coeffs_eq_zero_of_eq_zero {m : ℕ} (W : Fin m → Submodule F V) :
    IsDirectSum W ↔ ∀ (u : (i : Fin m) → W i), (∑ i, ((u i : V))) = 0 ↔ u = 0 := by
  refine ⟨fun h u => ⟨fun hu => h u 0 (by simpa using hu), fun hu => by simp [hu]⟩, ?_⟩
  intro h u v huv
  have hzero : u - v = 0 := by
    apply (h _).mp
    simp only [Pi.sub_apply, AddSubgroupClass.coe_sub, Finset.sum_sub_distrib]
    rw [huv, sub_self]
  exact sub_eq_zero.mp hzero

theorem isDirectSum_iff_coeffs_eq_zero_of_eq_zero' {m : ℕ} (W : Fin m → Submodule F V) :
    IsDirectSum W ↔ ∀ (u : (i : Fin m) → W i), (∑ i, ((u i : V))) = 0 → u = 0 := by
  rw [isDirectSum_iff_coeffs_eq_zero_of_eq_zero]
  exact ⟨fun h u hu => (h u).mp hu, fun h u => ⟨h u, fun hu => by simp [hu]⟩⟩

-- specialization for m = 5
theorem isDirectSum5_iff (W₁ W₂ W₃ W₄ W₅ : Submodule F V) : IsDirectSum (F := F) ![W₁, W₂, W₃, W₄, W₅] ↔ ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, ∀ w₃ ∈ W₃, ∀ w₄ ∈ W₄, ∀ w₅ ∈ W₅, (w₁ + w₂ + w₃ + w₄ + w₅ = 0) → (w₁ = 0 ∧ w₂ = 0 ∧ w₃ = 0 ∧ w₄ = 0 ∧ w₅ = 0) := by
  rw [isDirectSum_iff_coeffs_eq_zero_of_eq_zero']
  refine ⟨?_, ?_⟩
  · intro h w₁ hw₁ w₂ hw₂ w₃ hw₃ w₄ hw₄ w₅ hw₅ hsum
    let u : (i : Fin 5) → ![W₁, W₂, W₃, W₄, W₅] i := fun i =>
      match i with
      | ⟨0, _⟩ => ⟨w₁, hw₁⟩
      | ⟨1, _⟩ => ⟨w₂, hw₂⟩
      | ⟨2, _⟩ => ⟨w₃, hw₃⟩
      | ⟨3, _⟩ => ⟨w₄, hw₄⟩
      | ⟨4, _⟩ => ⟨w₅, hw₅⟩
    have hu : u = 0 := h u (by grind [Fin.sum_univ_five])
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := congrFun hu 0; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 1; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 2; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 3; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 4; simpa [u] using congrArg Subtype.val this
  · intro h u hsum
    have hu0 : (u 0 : V) ∈ W₁ := (u 0).2
    have hu1 : (u 1 : V) ∈ W₂ := (u 1).2
    have hu2 : (u 2 : V) ∈ W₃ := (u 2).2
    have hu3 : (u 3 : V) ∈ W₄ := (u 3).2
    have hu4 : (u 4 : V) ∈ W₅ := (u 4).2
    rw [Fin.sum_univ_five] at hsum
    obtain ⟨h0, h1, h2, h3, h4⟩ := h _ hu0 _ hu1 _ hu2 _ hu3 _ hu4 hsum
    funext i
    fin_cases i <;> apply Subtype.ext
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

-- specialization for m = 4
theorem isDirectSum4_iff (W₁ W₂ W₃ W₄ : Submodule F V) : IsDirectSum (F := F) ![W₁, W₂, W₃, W₄] ↔ ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, ∀ w₃ ∈ W₃, ∀ w₄ ∈ W₄, (w₁ + w₂ + w₃ + w₄ = 0) → (w₁ = 0 ∧ w₂ = 0 ∧ w₃ = 0 ∧ w₄ = 0) := by
  rw [isDirectSum_iff_coeffs_eq_zero_of_eq_zero']
  refine ⟨?_, ?_⟩
  · intro h w₁ hw₁ w₂ hw₂ w₃ hw₃ w₄ hw₄ hsum
    let u : (i : Fin 4) → ![W₁, W₂, W₃, W₄] i := fun i =>
      match i with
      | ⟨0, _⟩ => ⟨w₁, hw₁⟩
      | ⟨1, _⟩ => ⟨w₂, hw₂⟩
      | ⟨2, _⟩ => ⟨w₃, hw₃⟩
      | ⟨3, _⟩ => ⟨w₄, hw₄⟩
    have hu : u = 0 := h u (by grind [Fin.sum_univ_four])
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := congrFun hu 0; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 1; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 2; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 3; simpa [u] using congrArg Subtype.val this
  · intro h u hsum
    have hu0 : (u 0 : V) ∈ W₁ := (u 0).2
    have hu1 : (u 1 : V) ∈ W₂ := (u 1).2
    have hu2 : (u 2 : V) ∈ W₃ := (u 2).2
    have hu3 : (u 3 : V) ∈ W₄ := (u 3).2
    rw [Fin.sum_univ_four] at hsum
    obtain ⟨h0, h1, h2, h3⟩ := h _ hu0 _ hu1 _ hu2 _ hu3 hsum
    funext i
    fin_cases i <;> apply Subtype.ext
    · exact h0
    · exact h1
    · exact h2
    · exact h3

-- specialization for m = 3
theorem isDirectSum3_iff (W₁ W₂ W₃ : Submodule F V) : IsDirectSum (F := F) ![W₁, W₂, W₃] ↔ ∀ w₁ ∈ W₁, ∀ w₂ ∈ W₂, ∀ w₃ ∈ W₃, (w₁ + w₂ + w₃ = 0) → (w₁ = 0 ∧ w₂ = 0 ∧ w₃ = 0) := by
  rw [isDirectSum_iff_coeffs_eq_zero_of_eq_zero']
  refine ⟨?_, ?_⟩
  · intro h w₁ hw₁ w₂ hw₂ w₃ hw₃ hsum
    let u : (i : Fin 3) → ![W₁, W₂, W₃] i := fun i =>
      match i with
      | ⟨0, _⟩ => ⟨w₁, hw₁⟩
      | ⟨1, _⟩ => ⟨w₂, hw₂⟩
      | ⟨2, _⟩ => ⟨w₃, hw₃⟩
    have hu : u = 0 := h u (by grind [Fin.sum_univ_three])
    refine ⟨?_, ?_, ?_⟩
    · have := congrFun hu 0; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 1; simpa [u] using congrArg Subtype.val this
    · have := congrFun hu 2; simpa [u] using congrArg Subtype.val this
  · intro h u hsum
    have hu0 : (u 0 : V) ∈ W₁ := (u 0).2
    have hu1 : (u 1 : V) ∈ W₂ := (u 1).2
    have hu2 : (u 2 : V) ∈ W₃ := (u 2).2
    rw [Fin.sum_univ_three] at hsum
    obtain ⟨h0, h1, h2⟩ := h _ hu0 _ hu1 _ hu2 hsum
    funext i
    fin_cases i <;> apply Subtype.ext
    · exact h0
    · exact h1
    · exact h2

/-! 1.46 Direct sum of two subspaces -/

theorem isDirectSum_pair_iff (U W : Submodule F V) :
    IsDirectSum ![U, W] ↔ U ⊓ W = ⊥ := by
  rw [isDirectSum_iff_coeffs_eq_zero_of_eq_zero, Submodule.eq_bot_iff]
  refine ⟨?_, ?_⟩
  · -- direct sum → intersection trivial
    intro h v ⟨hvU, hvW⟩
    have m₀ : v ∈ ![U, W] (0 : Fin 2) := hvU
    have m₁ : (-v) ∈ ![U, W] (1 : Fin 2) := W.neg_mem hvW
    let u : (i : Fin 2) → ![U, W] i := fun i => match i with
      | ⟨0, _⟩ => ⟨v, m₀⟩
      | ⟨1, _⟩ => ⟨-v, m₁⟩
    have hsum : (∑ i, ((u i : V))) = 0 := by simp [u, Fin.sum_univ_two]
    have hu : u = 0 := (h u).mp hsum
    have : (u 0 : V) = (0 : V) := by rw [hu]; rfl
    simpa [u] using this
  · -- intersection trivial → direct sum
    intro hint u
    refine ⟨fun hsum => ?_, fun hu => by simp [hu]⟩
    rw [Fin.sum_univ_two] at hsum
    have h0 : (u 0 : V) = -(u 1 : V) := eq_neg_of_add_eq_zero_left hsum
    have h0W : (u 0 : V) ∈ W := by rw [h0]; exact W.neg_mem (u 1).2
    have h0Z : (u 0 : V) = 0 := hint _ ⟨(u 0).2, h0W⟩
    have h1Z : (u 1 : V) = 0 := by rw [← neg_eq_zero, ← h0, h0Z]
    funext i
    fin_cases i <;> apply Subtype.ext
    · exact h0Z
    · exact h1Z

/-! {lit}`IsCompl`

There are two equivalent ways of saying that {lit}`V = U ⊕ W`, where {lit}`U, W` are subspaces of {lit}`V`.

In Mathlib, this is idiomatically written as {lit}`IsCompl U W`.

Alternatively, {lit}`IsDirectSum ![U, W]` states that {lit}`U ⊕ W = U + W`, and we can add the condition that {lit}`U + W = V`.

We prefer using {lit}`IsCompl` to state exercise 1C.20 and 1C.21.
-/

/-! Equivalent ways of saying that {lit}`V = U ⊕ W`. -/
example (U W : Submodule F V) : (IsDirectSum ![U, W] ∧ U ⊔ W = ⊤) ↔ IsCompl U W := by
  constructor
  · rintro ⟨ h1, h2 ⟩
    constructor
    · rw [disjoint_iff]
      exact (isDirectSum_pair_iff U W).mp h1
    · exact codisjoint_iff.mpr h2
  · intro h
    refine ⟨(isDirectSum_pair_iff U W).mpr ?_, ?_⟩
    · exact disjoint_iff.mp h.disjoint
    · exact codisjoint_iff.mp h.codisjoint


/-! # Helpers for exercises -/

@[simp] lemma eq_v_2 {F : Type*} (v : Fin 2 → F) : ![v 0, v 1] = v := by
  ext i
  fin_cases i <;> simp

@[simp] lemma eq_v_3 {F : Type*} (v : Fin 3 → F) : ![v 0, v 1, v 2] = v := by
  ext i
  fin_cases i <;> simp

@[simp] lemma eq_v_4 {F : Type*} (v : Fin 4 → F) : ![v 0, v 1, v 2, v 3] = v := by
  ext i
  fin_cases i <;> simp

@[simp] lemma eq_v_5 {F : Type*} (v : Fin 5 → F) : ![v 0, v 1, v 2, v 3, v 4] = v := by
  ext i
  fin_cases i <;> simp

/-! # Exercises -/

def exercise_1C_1a_ans : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 + 2 * v 1 + 3 * v 2 = 0}
  add_mem' := by
    rintro f g hf hg
    simp at *
    grind
  zero_mem' := by simp
  smul_mem' := by
    intro a v hv
    simp at *
    grind

/-- 1C.1(a) -/
def exercise_1C_1a :
    Decidable (∃ U : Submodule F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 0}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  use exercise_1C_1a_ans
  simp [exercise_1C_1a_ans]

/-- 1C.1(b) -/
def exercise_1C_1b (hF : (0 : F) ≠ 4):
    Decidable (∃ U : Submodule F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 4}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  rintro ⟨U, hU⟩
  have := U.zero_mem'
  simp [hU] at this
  exact hF this

/-- 1C.1(c) -/
def exercise_1C_1c :
    Decidable (∃ U : Submodule F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 * v 1 * v 2 = 0}) := by
  apply isFalse
  rintro ⟨U, hU⟩
  have h1 : ![1, 0, 0] ∈ U.carrier := by simp [hU]
  have h2 : ![0, 1, 0] ∈ U.carrier := by simp [hU]
  have h3 : ![0, 0, 1] ∈ U.carrier := by simp [hU]
  have := U.add_mem' h1 (U.add_mem' h2 h3)
  simp at this
  have : ![1, 1, 1] ∈ U.carrier := by exact (Submodule.mem_carrier U).mpr this
  simp [hU] at this

def exercise_1C_1d_ans : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = 5 * v 2}
  add_mem' := by
    rintro f g hf hg
    simp at *
    grind
  zero_mem' := by simp
  smul_mem' := by
    intro a v hv
    simp at *
    grind

/-- 1C.1(d) -/
def exercise_1C_1d :
    Decidable (∃ U : Submodule F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 = 5 * v 2}) := by
  apply isTrue
  use exercise_1C_1d_ans
  simp [exercise_1C_1d_ans]

def exercise_1C_3_ans : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | DifferentiableOn ℝ f (Set.Ioo (-4) 4) ∧ deriv f (-1) = 3 * f 2}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨ hf1, hf2 ⟩ ⟨ hg1, hg2 ⟩
    simp at *
    constructor
    · fun_prop
    · rw [← show 3 * f 2 + 3 * g 2 = 3 * (f 2 + g 2) by ring]
      have h1 : DifferentiableAt ℝ f (-1) := by
        apply hf1.differentiableAt
        norm_num [Ioo_mem_nhds]
      have h2 : DifferentiableAt ℝ g (-1) := by
        apply hg1.differentiableAt
        norm_num [Ioo_mem_nhds]
      have := deriv_add h1 h2
      rw [hf2, hg2] at this
      rw [this]
  smul_mem' := by
    intro a v ⟨ hv1, hv2 ⟩
    constructor
    · fun_prop
    · rw [deriv_const_smul]
      rw [hv2]
      simp
      ring
      apply hv1.differentiableAt
      norm_num [Ioo_mem_nhds]

/-- 1C.3 Axler's ambient space is {lit}`ℝ^(-4, 4)`, i.e. the function space
{lit}`Set.Ioo (-4) 4 → ℝ`. We use the larger {lit}`ℝ → ℝ` instead because
mathlib's {name}`Differentiable` requires the source to be a normed space and
the subtype {lit}`↥(Set.Ioo (-4) 4)` isn't one. -/
theorem exercise_1C_3 :
    ∃ U : Submodule ℝ (ℝ → ℝ),
      (U : Set (ℝ → ℝ)) =
        {f | DifferentiableOn ℝ f (Set.Ioo (-4) 4) ∧ deriv f (-1) = 3 * f 2} := by
  use exercise_1C_3_ans
  simp [exercise_1C_3_ans]

theorem ContinuousOn.intervalIntegrable'
  {E : Type u_5} [NormedAddCommGroup E]
  {μ : MeasureTheory.Measure ℝ}
  [MeasureTheory.IsLocallyFiniteMeasure μ]
  {u : ℝ → E} {a b : ℝ}
  (h : a ≤  b)
  (hu : ContinuousOn u (Set.Icc a b)) :
    IntervalIntegrable u μ a b := by
  apply ContinuousOn.intervalIntegrable
  rwa [Set.uIcc_of_le h]

attribute [fun_prop] IntervalIntegrable
attribute [fun_prop] ContinuousOn.intervalIntegrable
attribute [fun_prop] ContinuousOn.intervalIntegrable'

def exercise_1C_4_ans : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ContinuousOn f (Set.Icc 0 1) ∧ ∫ x in (0)..1, f x = 0}
  zero_mem' := by
    simp
    fun_prop
  add_mem' := by
    rintro f g ⟨ hf1, hf2 ⟩ ⟨ hg1, hg2 ⟩
    simp at *
    constructor
    · fun_prop
    · rw [intervalIntegral.integral_add]
      · grind
      · fun_prop (disch := norm_num)
      · fun_prop (disch := norm_num)
  smul_mem' := by
    rintro a f ⟨ hf1, hf2 ⟩
    simp at *
    constructor
    · rw [show a • f = (fun x => a * f x) by funext; simp]
      fun_prop
    · grind

/-- 1C.4 Axler's ambient space is {lit}`ℝ^[0,1]`, i.e. {lit}`Set.Icc 0 1 → ℝ`.
We use {lit}`ℝ → ℝ` instead so the integral reads as the familiar
{lit}`∫ x in (0)..1, f x` via {name}`intervalIntegral`; the faithful subtype
version would need measure theory. -/
theorem exercise_1C_4 (b : ℝ) :
    (∃ U : Submodule ℝ (ℝ → ℝ),
        (U : Set (ℝ → ℝ)) =
          {f | ContinuousOn f (Set.Icc 0 1) ∧ ∫ x in (0)..1, f x = b}) ↔ b = 0 := by
  constructor
  · intro h
    obtain ⟨U, hU⟩ := h
    have : 0 ∈ U.carrier := by
      exact U.zero_mem'
    simp [hU] at this
    grind
  · rintro rfl
    use exercise_1C_4_ans
    simp [exercise_1C_4_ans]


/-- 1C.5 -/
def exercise_1C_5 :
    Decidable (∃ U : Submodule ℂ (Fin 2 → ℂ),
      (U : Set (Fin 2 → ℂ)) = {v | ∀ i, (v i).im = 0}) := by
  apply isFalse
  rintro ⟨U, hU⟩
  have : ![1, 1] ∈ U.carrier := by simp [hU]
  have := U.smul_mem' (Complex.I) this
  rw [show Complex.I • ![1, 1] = ![Complex.I, Complex.I] by simp] at this
  simp [hU] at this

@[simp] lemma eq_of_cube_eq (a b : ℝ) : (a^3 = b^3) ↔ a = b := by
  constructor
  · intro h
    exact (Odd.strictMono_pow ⟨1, rfl⟩).injective h
  · grind

def exercise_1C_6a_ans : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | v 0 = v 1}
  add_mem' := by
    rintro f g hf hg
    simp at *
    grind
  zero_mem' := by simp
  smul_mem' := by
    intro a v hv
    simp at *
    grind

/-- 1C.6(a) -/
def exercise_1C_6a :
    Decidable (∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 ^ 3 = v 1 ^ 3}) := by
  apply isTrue
  simp
  use exercise_1C_6a_ans
  simp [exercise_1C_6a_ans]

lemma exp_int_mul' (z : ℂ) (n : ℕ) : (Complex.exp z) ^ n  = Complex.exp (n * z) := by
  exact Eq.symm (Complex.exp_int_mul z n)

attribute [push ←] Complex.exp_nat_mul

lemma t1 : Complex.exp (2 * ↑Real.pi * Complex.I / 3) ^ 3 = 1 := by
  push (_ ^ _)
  ring_nf
  rw [← Complex.exp_two_pi_mul_I]
  congr 1
  ring


/-- 1C.6(b) -/
def exercise_1C_6b :
    Decidable (∃ U : Submodule ℂ (Fin 3 → ℂ),
      (U : Set (Fin 3 → ℂ)) = {v | v 0 ^ 3 = v 1 ^ 3}) := by
  apply isFalse
  rintro ⟨U, hU⟩
  have h1 : ![1, Complex.exp (2 * Real.pi * Complex.I / 3), 0] ∈ U.carrier := by
    simp [hU]
    exact Eq.symm t1
  have h2 : ![1, Complex.exp (4 * Real.pi * Complex.I / 3), 0] ∈ U.carrier := by
    simp [hU]
    push (_ ^ _)
    ring_nf
    rw [show (1 : ℂ) = 1*1 by ring]
    rw [← Complex.exp_two_pi_mul_I]
    rw [← Complex.exp_add]
    congr 1
    ring
  have := U.add_mem' h1 h2
  simp [hU] at this
  have := congr(Complex.re $this)
  have key : Complex.exp (2 * ↑Real.pi * Complex.I / 3) + Complex.exp (4 * ↑Real.pi * Complex.I / 3)
      = (-1 : ℂ) := by
    have e1 : (2 : ℂ) * Real.pi * Complex.I / 3 = ↑(2 * Real.pi / 3) * Complex.I := by
      push_cast; ring
    have e2 : (4 : ℂ) * Real.pi * Complex.I / 3 = ↑(4 * Real.pi / 3) * Complex.I := by
      push_cast; ring
    rw [e1, e2]
    apply Complex.ext
    · simp [Complex.add_re, Complex.exp_re]
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring]
      rw [show (4 * Real.pi / 3 : ℝ) = Real.pi / 3 + Real.pi by ring]
      rw [Real.cos_pi_sub, Real.cos_add_pi, Real.cos_pi_div_three]
      ring
    · simp [Complex.add_im, Complex.exp_im]
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring]
      rw [show (4 * Real.pi / 3 : ℝ) = Real.pi / 3 + Real.pi by ring]
      rw [Real.sin_pi_sub, Real.sin_add_pi, Real.sin_pi_div_three]
      ring
  rw [key] at this
  norm_num at this



/-- 1C.7 -/
def exercise_1C_7 :
    Decidable (∀ U : Set (Fin 2 → ℝ),
      U.Nonempty →
      (∀ u ∈ U, ∀ v ∈ U, u + v ∈ U) →
      (∀ u ∈ U, -u ∈ U) →
      ∃ S : Submodule ℝ (Fin 2 → ℝ), (S : Set (Fin 2 → ℝ)) = U) := by
  apply isFalse
  push Not
  use { z | z : ℤ }
  constructor
  · use 0
    simp
    use 0
    norm_num
  and_intros
  · simp
    intro x y
    use x + y
    norm_num
  · intro x hx
    simp at *
    obtain ⟨ x, rfl ⟩ := hx
    use -x
    simp
  · by_contra h
    push Not at h
    obtain ⟨ S, hS ⟩ := h
    have : 1 ∈ S.carrier := by
      simp [hS]
      use 1
      norm_num
    have := S.smul_mem' (1/2 : ℝ) this
    simp [hS] at this
    obtain ⟨ z, hz ⟩ := this
    have := congr($hz 0)
    simp at this
    have := congr($this*2)
    norm_num at this
    norm_cast at this
    grind

/-- 1C.8 -/
theorem exercise_1C_8 :
    ∃ U : Set (Fin 2 → ℝ),
      U.Nonempty ∧
      (∀ (a : ℝ) (u), u ∈ U → a • u ∈ U) ∧
      ¬ ∃ S : Submodule ℝ (Fin 2 → ℝ), (S : Set (Fin 2 → ℝ)) = U := by
  letI := { ![(z : ℝ), 0] | z : ℝ } ∪ { ![0, (z : ℝ)] | z : ℝ }
  dsimp at this
  use this
  and_intros
  · simp [this]
    left
    use 0
    simp
  · simp [this]
    intro r u hu
    obtain ⟨ z, rfl ⟩ | ⟨ z, rfl ⟩ := hu
    · left
      use r*z
      simp
    · right
      use r*z
      simp
  · rintro ⟨ S, hS ⟩
    simp [this] at hS
    have h1 : ![1, 0] ∈ S.carrier := by simp [hS]
    have h2 : ![0, 1] ∈ S.carrier := by simp [hS]
    have := S.add_mem' h1 h2
    simp [hS] at this

def Periodic (f : ℝ → ℝ) : Prop := ∃ p > 0, ∀ x, f x = f (x + p)

lemma sin_periodic : Periodic Real.sin := by
  use 2 * Real.pi
  norm_num
  positivity

noncomputable abbrev sin' (x : ℝ) := Real.sin (√2 * x)


lemma sin'_periodic : Periodic sin' := by
  unfold sin'
  use 2 * Real.pi / √2
  norm_num
  constructor
  · positivity
  intro x
  ring_nf
  -- tactic to cancel inverses
  rw [
    show √2 * x + √2 * Real.pi * (√2)⁻¹ * 2 = √2 * x + Real.pi *(√2 * (√2)⁻¹ * 2) by ring
  ]
  simp
  rw [mul_comm _ 2]
  rw [Real.sin_add_two_pi]

noncomputable abbrev cos' (x : ℝ) := Real.cos (√2 * x)

@[simp] lemma cos'_zero : cos' 0 = 1 := by simp [cos']

lemma cos_periodic : Periodic Real.cos := by
  use 2 * Real.pi
  norm_num [Real.pi_pos]

lemma cos'_periodic : Periodic cos' := by
  unfold cos'
  use 2 * Real.pi / √2
  norm_num [Real.pi_pos]
  intro x
  field_simp
  simp [Real.cos_add_two_pi]

/-- 1C.9 -/
def exercise_1C_9 :
    Decidable (∃ U : Submodule ℝ (ℝ → ℝ), (U : Set (ℝ → ℝ)) = {f | Periodic f}) := by
  apply isFalse
  push Not
  rintro U
  simp
  push Not
  intro h
  have h1 : Real.cos ∈ U.carrier := by
    simp [h, cos_periodic]
  have h2 : cos' ∈ U.carrier := by
    simp [h, cos'_periodic]
  have := U.add_mem' h1 h2

  simp [h] at this

  obtain ⟨P, hp_pos, hp_eq⟩ := this
  have := hp_eq 0
  simp at this

  have h1 : Real.cos P ≤ 1 := Real.cos_le_one _
  have h2 : cos' P ≤ 1 := Real.cos_le_one _

  have h1 : Real.cos P = 1 := by linarith
  have h2 : cos' P = 1 := by linarith

  rw [Real.cos_eq_one_iff] at h1
  rw [cos', Real.cos_eq_one_iff] at h2

  obtain ⟨ n, hn ⟩ := h1

  have npos : 0 < (n : ℝ) := by
    have : (n : ℝ) = P / (2 * Real.pi) := by
      rw [← hn]
      field_simp
    rw [this]
    positivity

  obtain ⟨ m, hm ⟩ := h2

  have mpos : 0 < (m : ℝ) := by
    have : (m : ℝ) = (√2 * P) / (2 * Real.pi) := by
      rw [← hm]
      field_simp
    rw [this]
    positivity

  rw [← hn] at hm
  field_simp at hm

  have : √2 = (m : ℝ) / n := by
    rw [hm]
    field_simp

  exact irrational_sqrt_two.ne_rational _ _ this

def intersection (U W : Submodule F V) : Submodule F V where
  carrier := {v | v ∈ U.carrier ∧ v ∈ W.carrier}
  zero_mem' := by
    simp
  add_mem' := by
    rintro u v ⟨hu, hv⟩ ⟨hu', hv'⟩
    simp at *
    constructor
    · exact (Submodule.add_mem_iff_right U hu).mpr hu'
    · exact (Submodule.add_mem_iff_right W hv).mpr hv'
  smul_mem' := by
    rintro a v ⟨hu, hv⟩
    simp at *
    constructor
    exact Submodule.smul_mem U a hu
    exact Submodule.smul_mem W a hv

/-- 1C.10 The intersection of two subspaces is a subspace. The student must
build a {name}`Submodule` whose carrier is {lit}`(U : Set V) ∩ (W : Set V)`,
i.e. prove the three closure axioms hold for the intersection. (In mathlib
this submodule is the lattice infimum {lit}`U ⊓ W`, which the
{name}`SemilatticeInf` instance on {name}`Submodule` produces automatically;
the exercise is to do that construction by hand.) -/
theorem exercise_1C_10 (U W : Submodule F V) :
    ∃ S : Submodule F V, (S : Set V) = (U : Set V) ∩ (W : Set V) := by
  -- use U ⊓ W; simp -- works, need to ban
  use intersection U W
  simp [intersection]
  ext i
  simp

def intersection' (𝒞 : Set (Submodule F V)) : Submodule F V where
  carrier := {v | ∀ U ∈ 𝒞, v ∈ U.carrier}
  zero_mem' := by
    simp
  add_mem' := by
    intro u v hU hV
    simp at *
    intro C hC
    specialize hU C hC
    specialize hV C hC
    exact (Submodule.add_mem_iff_right C hU).mpr hV
  smul_mem' := by
    intro a x hx
    simp at *
    intro C hC
    exact Submodule.smul_mem C a (hx C hC)


/-- 1C.11 The intersection of *any* collection of subspaces of {lit}`V` is a
subspace. The student must build a {name}`Submodule` whose carrier is the
intersection {lit}`⋂ U ∈ 𝒞, (U : Set V)`, i.e. prove the three closure axioms
hold for an arbitrary intersection. (In mathlib this submodule is the lattice
infimum {name}`sInf` (or {name}`iInf` for an indexed family), which the
{name}`CompleteLattice` instance on {name}`Submodule` produces automatically;
the exercise is to do that construction by hand.) -/
theorem exercise_1C_11 (𝒞 : Set (Submodule F V)) :
    ∃ S : Submodule F V, (S : Set V) = ⋂ U ∈ 𝒞, (U : Set V) := by
  use intersection' 𝒞
  simp [intersection']
  ext i
  simp

/-- 1C.12 Union of two subspaces is a subspace if and only if one is contained in the other. -/
@[avoiding Submodule.union_eq_iff_le_or_le]
theorem exercise_1C_12 (U W : Submodule F V) :
    (∃ S : Submodule F V, (S : Set V) = (U : Set V) ∪ (W : Set V)) ↔
      U ≤ W ∨ W ≤ U := by
  constructor
  · rintro ⟨S, hS⟩
    by_contra h
    simp at h
    obtain ⟨ h1, h2 ⟩ := h
    rw [show (U ≤ W) ↔ (U.carrier ⊆ W.carrier) from Eq.to_iff rfl] at h1
    rw [show (W ≤ U) ↔ (W.carrier ⊆ U.carrier) from Eq.to_iff rfl] at h2
    obtain ⟨ u, hu1, hu2 ⟩ : ∃ u : V, u ∈ U.carrier ∧ u ∉ W.carrier := by grind
    obtain ⟨ w, hw1, hw2 ⟩ : ∃ w : V, w ∈ W.carrier ∧ w ∉ U.carrier := by grind

    have hu1' : u ∈ (S : Set V) := by grind [(Submodule.mem_carrier U).mp hu1]
    simp at hu1'
    have hw1' : w ∈ (S : Set V) := by grind [(Submodule.mem_carrier W).mp hw1]
    simp at hw1'
    have := S.add_mem' hu1' hw1'
    have : u + w ∈ U ∨ u + w ∈ W := by
      rw [show S.carrier = (S : Set V) from rfl] at this
      rw [hS] at this
      simp_all
    obtain h | h := this
    · simp at hu1
      have hu1 := U.smul_mem' (-1) hu1
      rw [show (-1 : F) • u = -u by exact neg_one_smul F u] at hu1
      simp only [Submodule.carrier_eq_coe, SetLike.mem_coe] at hu1
      have := U.add_mem' h hu1
      simp at this
      simp at hw2
      grind
    · simp at hw1
      have hw1 := W.smul_mem' (-1) hw1
      rw [show (-1 : F) • w = -w by exact neg_one_smul F w] at hw1
      simp only [Submodule.carrier_eq_coe, SetLike.mem_coe] at hw1
      have := W.add_mem' h hw1
      simp at this
      simp at hu2
      grind
  · intro h
    obtain h | h := h
    · use W
      rw [Set.union_eq_self_of_subset_left h]
    · use U
      rw [Set.union_eq_self_of_subset_right h]

/-- 1C.13 - The union of three subspaces is a subspace iff one of the subspaces contains the other two. -/
theorem exercise_1C_13 (U W X : Submodule F V) (_hF : ∃ a : F, a ≠ 0 ∧ a ≠ 1) :
    (∃ S : Submodule F V, (S : Set V) = (U : Set V) ∪ W ∪ X) ↔
      (W ≤ U ∧ X ≤ U) ∨ (U ≤ W ∧ X ≤ W) ∨ (U ≤ X ∧ W ≤ X) := by
  sorry

/-- 1C.14 The student fills in the predicate (replacing the {lit}`sorry` in
the right-hand side) and proves the equality. -/
def exercise_1C_14_U : Submodule F (Fin 3 → F) where
  carrier := {v | ∃ x : F, v = ![x, -x, 2 * x]}
  zero_mem' := ⟨0, by funext i; fin_cases i <;> simp⟩
  add_mem' := by
    rintro u v ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    funext i; fin_cases i <;> simp <;> ring
  smul_mem' := by
    rintro a v ⟨x, rfl⟩
    refine ⟨a * x, ?_⟩
    funext i; fin_cases i <;> simp [smul_eq_mul] ; ring

def exercise_1C_14_W : Submodule F (Fin 3 → F) where
  carrier := {v | ∃ x : F, v = ![x, x, 2 * x]}
  zero_mem' := ⟨0, by funext i; fin_cases i <;> simp⟩
  add_mem' := by
    rintro u v ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    funext i; fin_cases i <;> simp ; ring
  smul_mem' := by
    rintro a v ⟨x, rfl⟩
    refine ⟨a * x, ?_⟩
    funext i; fin_cases i <;> simp [smul_eq_mul] ; ring

/- describe U + W (fill in the sorry) -/
theorem exercise_1C_14 (h : (2 : F) ≠ 0) :
    ((exercise_1C_14_U (F := F) ⊔ exercise_1C_14_W : Submodule F (Fin 3 → F))
      : Set (Fin 3 → F)) = {v | v 0 * 2 = v 2 } := by
  ext v
  simp
  constructor
  · intro hv
    rw [Submodule.mem_sup] at hv
    obtain ⟨ x, hx, y, hy, rfl ⟩ := hv
    dsimp
    simp [exercise_1C_14_U, exercise_1C_14_W] at hx hy
    obtain ⟨ x, rfl ⟩ := hx
    obtain ⟨ y, rfl ⟩ := hy
    simp
    ring
  · intro hv
    rw [Submodule.mem_sup]
    use ![(v 0 - v 1) / 2, (v 1 - v 0) / 2, (v 0 - v 1)]
    constructor
    · simp [exercise_1C_14_U]
      field_simp
      simp
    use ![(v 0 + v 1) / 2, (v 0 + v 1) / 2, (v 0 + v 1)]
    constructor
    · simp [exercise_1C_14_W]
      field_simp
    simp
    ring_nf
    field_simp
    rw [hv]
    exact List.ofFn_inj.mp rfl

/-- 1C.15 -/
@[avoiding sup_idem, sup_self]
theorem exercise_1C_15 (U : Submodule F V) : U ⊔ U = U := by
  ext u
  constructor
  · intro hu
    rw [Submodule.mem_sup] at hu
    obtain ⟨ x, hx, y, hy, rfl ⟩ := hu
    exact (Submodule.add_mem_iff_right U hx).mpr hy
  · intro hu
    rw [Submodule.mem_sup]
    use u, hu, 0, (Submodule.zero_mem U)
    simp

/-- 1C.16 -/
@[avoiding sup_comm]
def exercise_1C_16 :
    Decidable (∀ U W : Submodule F V, U ⊔ W = W ⊔ U) := by
  apply isTrue
  intro U W
  ext v
  constructor
  · intro hv
    rw [Submodule.mem_sup] at *
    obtain ⟨ x, hx, y, hy, rfl ⟩ := hv
    use y, hy, x, hx
    grind
  · intro hv
    rw [Submodule.mem_sup] at *
    obtain ⟨ x, hx, y, hy, rfl ⟩ := hv
    use y, hy, x, hx
    grind

/-- 1C.17 -/
@[avoiding sup_assoc]
def exercise_1C_17 :
    Decidable (∀ V₁ V₂ V₃ : Submodule F V, (V₁ ⊔ V₂) ⊔ V₃ = V₁ ⊔ (V₂ ⊔ V₃)) := by
  apply isTrue
  -- order --need to ban
  intro V1 V2 V3
  ext v
  simp [Submodule.mem_sup]
  constructor
  · rintro ⟨ x, hx, y, hy, z, hz, h⟩
    use x, hx, y, hy, z, hz
    grind
  · rintro ⟨ x, hx, y, hy, z, hz, h⟩
    use x, hx, y, hy, z, hz
    grind

variable (V1 V2 V3 : Submodule F V) in
example : V1 ⊔ V2 = V1 + V2 := by
  simp [Submodule.add_eq_sup]

/-- 1C.18(a) - does there exist a subspace E such that for all subspaces U, U ⊔ E = U, i.e., E is the additive identity? -/
@[avoiding bot_sup_eq, sup_bot_eq]
def exercise_1C_18_id :
    Decidable (∃ E : Submodule F V, ∀ U : Submodule F V, U ⊔ E = U) := by
  apply isTrue
  use ⊥
  intro U
  ext v
  constructor
  · intro h
    rw [Submodule.mem_sup] at h
    obtain ⟨ y, hy, z, hz, rfl ⟩ := h
    simp at hz
    subst hz
    grind
  · -- simp -- need to ban
    intro hv
    rw [Submodule.mem_sup]
    use v, hv, 0
    simp


/-- 1C.18(b) *Which subspaces have an additive inverse under sum?* (i.e., for
which {lit}`U` does there exist {lit}`W` with {lit}`U + W = ⊥`?) Fill in the
right-hand side {lit}`sorry` with the conjectured characterization
of {lit}`U`, and then then proves the equivalence. -/
theorem exercise_1C_18_inv (U : Submodule F V) :
    (∃ W : Submodule F V, U ⊔ W = ⊥) ↔ U = ⊥ := by
  -- need to ban `simp`
  constructor
  · rintro ⟨W, hW⟩
    ext v
    simp
    constructor
    · rintro hv
      have : v ∈ U ⊔ W := by
        rw [Submodule.mem_sup]
        use v, hv, 0, (Submodule.zero_mem W)
        grind
      rw [hW] at this
      simp_all
    · rintro rfl
      exact Submodule.zero_mem U
  · rintro rfl
    use ⊥
    simp

def y_axis : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v | v 0 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp_all
  smul_mem' := by
    intro a v hv
    simp_all

/-- 1C.19 -/
def exercise_1C_19 :
    Decidable (∀ V₁ V₂ U : Submodule ℝ (Fin 2 → ℝ),
      V₁ ⊔ U = V₂ ⊔ U → V₁ = V₂) := by
  apply isFalse
  push Not
  use y_axis
  use ⊤
  use ⊤
  simp
  intro h
  have : ![1, 0] ∈ y_axis := by
    rw [h]
    simp
  simp [y_axis] at this

/-- 1C.20 -/
def exercise_1C_20_U : Submodule F (Fin 4 → F) where
  carrier := {v | v 0 = v 1 ∧ v 2 = v 3}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by simp [Pi.add_apply, h1, h1'], by simp [Pi.add_apply, h2, h2']⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

  def exercise_1C_20_W : Submodule F (Fin 4 → F) where
    carrier := {v | v 0 = 0 ∧ v 2 = 0}
    zero_mem' := ⟨rfl, rfl⟩
    add_mem' := by
      rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
      exact ⟨by simp [Pi.add_apply, h1, h1'], by simp [Pi.add_apply, h2, h2']⟩
    smul_mem' := by
      rintro a v ⟨h1, h2⟩
      exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

theorem exercise_1C_20 :
    ∃ W : Submodule F (Fin 4 → F), IsCompl (exercise_1C_20_U (F := F)) W := by
  use exercise_1C_20_W
  rw [isCompl_iff]
  constructor
  · intro S h1 h2
    simp
    ext v
    simp
    constructor
    · intro hv
      have hv1 := hv
      grw [h1] at hv1
      have hv2 := hv
      grw [h2] at hv2
      simp [exercise_1C_20_U] at hv1
      simp [exercise_1C_20_W] at hv2
      ext i
      fin_cases i <;> simp <;> grind
    · rintro rfl
      simp
  · intro V h1 h2
    simp
    ext v
    simp
    have h3 : ![v 0, v 0, v 2, v 2] ∈ V := by
      grw [← h1]
      simp [exercise_1C_20_U]
    have h4 : ![0, v 1 - v 0, 0, v 3 - v 2] ∈ V := by
      grw [← h2]
      simp [exercise_1C_20_W]
    have := V.add_mem' h3 h4
    simp_all

/-- 1C.21 -/
def exercise_1C_21_U : Submodule F (Fin 5 → F) where
  carrier := {v | v 2 = v 0 + v 1 ∧ v 3 = v 0 - v 1 ∧ v 4 = 2 * v 0}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' := by
    rintro u v ⟨h2, h3, h4⟩ ⟨h2', h3', h4'⟩
    refine ⟨?_, ?_, ?_⟩
    · show u 2 + v 2 = (u 0 + v 0) + (u 1 + v 1); rw [h2, h2']; ring
    · show u 3 + v 3 = (u 0 + v 0) - (u 1 + v 1); rw [h3, h3']; ring
    · show u 4 + v 4 = 2 * (u 0 + v 0); rw [h4, h4']; ring
  smul_mem' := by
    rintro a v ⟨h2, h3, h4⟩
    refine ⟨?_, ?_, ?_⟩
    · show a • v 2 = a • v 0 + a • v 1; simp only [smul_eq_mul]; rw [h2]; ring
    · show a • v 3 = a • v 0 - a • v 1; simp only [smul_eq_mul]; rw [h3]; ring
    · show a • v 4 = 2 * (a • v 0); simp only [smul_eq_mul]; rw [h4]; ring

def exercise_1C_21_W : Submodule F (Fin 5 → F) where
  carrier := {v | v 0 = 0 ∧ v 1 = 0 }
  zero_mem' := by simp
  add_mem' := by simp_all
  smul_mem' := by simp_all

theorem exercise_1C_21 :
    ∃ W : Submodule F (Fin 5 → F), IsCompl (exercise_1C_21_U (F := F)) W := by
  use exercise_1C_21_W
  rw [isCompl_iff]
  constructor
  · intro S h1 h2
    simp
    ext v
    simp
    constructor
    · intro hv
      have hv1 := hv
      grw [h1] at hv1
      have hv2 := hv
      grw [h2] at hv2
      simp [exercise_1C_21_U] at hv1
      simp [exercise_1C_21_W] at hv2
      ext i
      fin_cases i <;> simp <;> grind
    · rintro rfl
      simp
  · intro V h1 h2
    simp
    ext v
    simp
    have h3 : ![v 0, v 1, v 0 + v 1, v 0 - v 1, 2 * v 0] ∈ exercise_1C_21_U := by
      simp [exercise_1C_21_U]
    grw [h1] at h3
    have h4 : ![(0 : F), 0, v 2 - v 0 - v 1, v 3 - v 0 + v 1, v 4 - 2 * v 0] ∈ exercise_1C_21_W := by
      simp [exercise_1C_21_W]
    grw [h2] at h4
    have := V.add_mem' h3 h4
    simp_all

abbrev v (k : Fin 5) : (Fin 5 → F) := fun i => if i = k then 1 else 0

lemma v_in_axis (n : Fin 5) : v n ∈ Example_1_43.Axis (F := F) 5 n := by
  simp [Example_1_43.Axis]

@[simp] lemma axis_ne_bot (n : Fin 5) : Example_1_43.Axis (F := F) 5 n ≠ ⊥ := by
  intro h
  have := v_in_axis (F := F) n
  rw [h] at this
  simp at this
  have := congr($this n)
  simp [v] at this

/-- 1C.22 The direct-sum condition is captured by {name}`IsDirectSum` on the
family {lit}`![U, W₁, W₂, W₃]`; the cover by {lit}`U ⊔ W₁ ⊔ W₂ ⊔ W₃ = ⊤`. -/
theorem exercise_1C_22 :
    ∃ W₁ W₂ W₃ : Submodule F (Fin 5 → F),
      W₁ ≠ ⊥ ∧ W₂ ≠ ⊥ ∧ W₃ ≠ ⊥ ∧
      IsDirectSum ![exercise_1C_21_U, W₁, W₂, W₃] ∧
      exercise_1C_21_U ⊔ W₁ ⊔ W₂ ⊔ W₃ = ⊤ := by
  use (Example_1_43.Axis (F := F) 5 2)
  use (Example_1_43.Axis (F := F) 5 3)
  use (Example_1_43.Axis (F := F) 5 4)
  simp
  constructor
  · rw [isDirectSum4_iff]
    intro w₁ hw₁ w₂ hw₂ w₃ hw₃ w₄ hw₄ hsum
    have := congr($hsum 4)
    simp at this
    simp [exercise_1C_21_U] at hw₁
    rw [hw₂ 4 (by simp)] at this
    rw [hw₃ 4 (by simp)] at this



    sorry
  sorry

def x_axis : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v | v 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp_all
  smul_mem' := by
    intro a v hv
    simp_all

def diagonal : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v | v 0 = v 1}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp_all
  smul_mem' := by
    intro a v hv
    simp_all

lemma isComplement_y_axis_x_axis : IsCompl y_axis x_axis := by
  rw [isCompl_iff]
  constructor
  · intro S h1 h2
    simp
    ext v
    simp
    constructor
    · intro hv
      have hv1 := hv
      grw [h1] at hv1
      have hv2 := hv
      grw [h2] at hv2
      simp [y_axis] at hv1
      simp [x_axis] at hv2
      ext i
      fin_cases i <;> simp <;> grind
    · rintro rfl
      simp
  · intro V h1 h2
    simp
    ext v
    simp
    have h3 : ![v 0, 0] ∈ x_axis := by
      simp [x_axis]
    grw [h2] at h3
    have h4 : ![0, v 1] ∈ y_axis := by
      simp [y_axis]
    grw [h1] at h4
    have := V.add_mem' h3 h4
    simp_all

lemma isComplement_diagonal_x_axis : IsCompl diagonal x_axis := by
  rw [isCompl_iff]
  constructor
  · intro S h1 h2
    simp
    ext v
    simp
    constructor
    · intro hv
      have hv1 := hv
      grw [h1] at hv1
      have hv2 := hv
      grw [h2] at hv2
      simp [diagonal] at hv1
      simp [x_axis] at hv2
      ext i
      fin_cases i <;> simp <;> grind
    · rintro rfl
      simp
  · intro V h1 h2
    simp
    ext v
    simp
    have h3 : ![(v 0 - v 1), 0] ∈ x_axis := by
      simp [x_axis]
    grw [h2] at h3
    have h4 : ![v 1, v 1] ∈ diagonal := by
      simp [diagonal]
    grw [h1] at h4
    have := V.add_mem' h3 h4
    simp_all

/-- 1C.23 -/
def exercise_1C_23 :
    Decidable (∀ V₁ V₂ U : Submodule ℝ (Fin 2 → ℝ), -- no need for (2)
      IsCompl V₁ U → IsCompl V₂ U → V₁ = V₂) := by
  apply isFalse
  push Not
  use y_axis
  use diagonal
  use x_axis
  and_intros
  · exact isComplement_y_axis_x_axis
  · exact isComplement_diagonal_x_axis
  · simp
    intro h
    have : ![0, 1] ∈ y_axis := by
      simp [y_axis]
    rw [h] at this
    simp_all [diagonal]

/-- 1C.24 -/

def IsEven (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = f x
def IsOdd  (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = -f x

def evenFunctions : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsEven f}
  zero_mem' := by
    simp [IsEven]
  add_mem' := by
    intro f g hf hg
    simp at *
    intro x
    simp [hf x, hg x]
  smul_mem' := by
    intro a f hf
    simp at *
    intro x
    simp [hf x]

def oddFunctions : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsOdd f}
  zero_mem' := by simp [IsOdd]
  add_mem' := by
    intro f g hf hg
    simp at *
    intro x
    simp [hf x, hg x]
    ring
  smul_mem' := by
    intro a f hf
    simp at *
    intro x
    simp [hf x]

noncomputable def evenPart (f : ℝ → ℝ) : ℝ → ℝ := fun x => (f x + f (-x)) / 2
noncomputable def oddPart (f : ℝ → ℝ) : ℝ → ℝ := fun x => (f x - f (-x)) / 2

lemma evenPart_add_oddPart (f : ℝ → ℝ) : evenPart f + oddPart f = f := by
  ext x
  simp [evenPart, oddPart]
  ring

lemma isEven_evenPart (f : ℝ → ℝ) : IsEven (evenPart f) := by
  simp [IsEven]
  intro x
  simp [evenPart]
  ring

lemma isOdd_oddPart (f : ℝ → ℝ) : IsOdd (oddPart f) := by
  simp [IsOdd]
  intro x
  simp [oddPart]
  ring

theorem exercise_1C_24 : IsCompl evenFunctions oddFunctions := by
  rw [isCompl_iff]
  constructor
  · intro F h1 h2
    simp
    ext f
    simp
    constructor
    · intro hf
      have h1 : f ∈ evenFunctions := by exact (Submodule.mem_toAddSubgroup evenFunctions).mp (h1 hf)
      have h2 : f ∈ oddFunctions := by exact (Submodule.mem_toAddSubgroup oddFunctions).mp (h2 hf)
      ext x
      simp [evenFunctions] at h1
      simp [oddFunctions] at h2
      specialize h1 x
      specialize h2 x
      ring_nf at h1 h2
      rw [h2] at h1
      simp
      grind
    · rintro rfl
      simp
  · intro F h1 h2
    simp
    ext f
    simp
    have h1 : evenPart f ∈ F := by
      have : evenPart f ∈ evenFunctions := by
        exact (Submodule.mem_toAddSubgroup evenFunctions).mpr (isEven_evenPart f)
      exact (Submodule.mem_toAddSubgroup F).mp (h1 this)
    have h2 : oddPart f ∈ F := by
      have : oddPart f ∈ oddFunctions := by
        exact (Submodule.mem_toAddSubgroup oddFunctions).mpr (isOdd_oddPart f)
      exact (Submodule.mem_toAddSubgroup F).mp (h2 this)
    have := F.add_mem' h1 h2
    rw [evenPart_add_oddPart] at this
    simp_all

end LADR.Section_1C
