import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.Real.Irrational
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

/-! Reminder: This is how we say V is a vector space over F
(and F is like ℝ or ℂ) in mathlib.
 -/
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

Verify that the sets in (a)–(e) are subspaces: the carrier together with the
{lit}`0`-membership, additive-closure, and scalar-closure proofs. -/

/-! 1.35(a) The set {lit}`{(x₁, x₂, x₃, x₄) ∈ F⁴ : x₃ = 5 x₄ + b}` is a
subspace of {lit}`F⁴` iff {lit}`b = 0` (the {lit}`b = 0` direction is shown
here; both directions are exercise 1C.1 above). -/

example : Submodule F (Fin 4 → F) where
  carrier := {v | v 2 = 5 * v 3}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp at ha hb ⊢
    rw [ha, hb]
    ring
  smul_mem' := by
    intro a b hb
    simp at hb ⊢
    rw [hb]
    ring

/-! 1.35(b) Continuous real-valued functions on {lit}`[0, 1]` form a subspace
of {lit}`ℝ^[0,1]`. (Axler uses {lit}`[0, 1]`; we work over all of {lit}`ℝ` —
the closure proofs are identical.) -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := by
    expose_names
    simp at hf hg ⊢
    exact hf.add hg
  smul_mem' a _ hf := by
    expose_names
    simp at hf ⊢
    exact hf.const_smul a

/-! 1.35(c) Differentiable real-valued functions on {lit}`ℝ` form a subspace
of {lit}`ℝ^ℝ`. -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Differentiable ℝ f}
  zero_mem' := differentiable_const 0
  add_mem' hf hg := by
    expose_names
    simp at hf hg ⊢
    exact hf.add hg
  smul_mem' a _ hf := by
    expose_names
    simp at hf ⊢
    exact hf.const_smul a

/-! 1.35(d) Differentiable real-valued functions on {lit}`(0, 3)` such that
{lit}`f'(2) = 0` form a subspace. We work on all of {lit}`ℝ` and pin the
derivative at {lit}`2`; both addition and scalar multiplication preserve the
derivative being zero at a point. -/

example : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | Differentiable ℝ f ∧ deriv f 2 = 0}
  zero_mem' := ⟨differentiable_const 0, by simp⟩
  add_mem' := by
    intro a b ha hb
    simp at ha hb ⊢
    constructor
    · exact ha.1.add hb.1
    · rw [deriv_add (ha.1 2) (hb.1 2), ha.2, hb.2, add_zero]
  smul_mem' := by
    intro a b hb
    simp at hb ⊢
    constructor
    · exact hb.1.const_smul a
    · rw [deriv_const_smul _ (hb.1 2), hb.2, smul_zero]

/-! 1.35(e) Sequences of complex numbers with limit {lit}`0` form a subspace
of {lit}`ℂ^∞`. In Lean, "sequence" is {lit}`ℕ → ℂ` and "has limit {lit}`0`" is
{lit}`Filter.Tendsto f Filter.atTop (𝓝 0)`. -/

example : Submodule ℂ (ℕ → ℂ) where
  carrier := {f | Filter.Tendsto f Filter.atTop (nhds 0)}
  zero_mem' := tendsto_const_nhds
  add_mem' := by
    intro a b ha hb
    simp at ha hb ⊢
    have := Filter.Tendsto.add ha hb
    simp at this
    exact this
  smul_mem' := by
    intro a b hb
    simp at hb ⊢
    have := Filter.Tendsto.const_smul hb a
    simp at this
    exact this

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

/-! 1.45 Condition for a direct sum -/

theorem isDirectSum_iff {m : ℕ} (W : Fin m → Submodule F V) :
    IsDirectSum W ↔ ∀ (u : (i : Fin m) → W i), (∑ i, ((u i : V))) = 0 ↔ u = 0 := by
  refine ⟨fun h u => ⟨fun hu => h u 0 (by simpa using hu), fun hu => by simp [hu]⟩, ?_⟩
  intro h u v huv
  have hzero : u - v = 0 := by
    apply (h _).mp
    simp only [Pi.sub_apply, AddSubgroupClass.coe_sub, Finset.sum_sub_distrib]
    rw [huv, sub_self]
  exact sub_eq_zero.mp hzero

/-! 1.46 Direct sum of two subspaces -/

theorem isDirectSum_pair_iff (U W : Submodule F V) :
    IsDirectSum ![U, W] ↔ U ⊓ W = ⊥ := by
  rw [isDirectSum_iff, Submodule.eq_bot_iff]
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

We prefer using {lit}`IsCompl` to state the condition when they appear in exercises 1C.20 and 1C.21; note that this means {lit}`V` does not appear explicitly, but instead appears as the ambient space of {lit}`U` and {lit}`W`.
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

/-! # Exercises -/

/-- 1C.1(a) -/
def exercise_1C_1a :
    Decidable (∃ U : Submodule F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 0}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  refine ⟨{
    carrier := {v | v 0 + 2 * v 1 + 3 * v 2 = 0}
    zero_mem' := by simp
    add_mem' := ?_
    smul_mem' := ?_ }, rfl⟩
  · intro u v hu hv
    simp only [Set.mem_setOf_eq, Pi.add_apply] at *
    have := congrArg₂ (· + ·) hu hv
    simp at this
    rw [← this]
    ring
  · intro a v hv
    simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
    have key : a * v 0 + 2 * (a * v 1) + 3 * (a * v 2)
        = a * (v 0 + 2 * v 1 + 3 * v 2) := by ring
    rw [key, hv, mul_zero]

/-- 1C.1(b) The set misses {lit}`0`, so it is not a subspace — provided
{lit}`(4 : F) ≠ 0`. We assume {lit}`[CharZero F]`, which forces
{lit}`(n : F) ≠ 0` for every positive {lit}`n` and is satisfied by {lit}`ℝ` and
{lit}`ℂ` (Axler's working fields); over a field of characteristic {lit}`2` the
set is {lit}`{v | v 0 + v 2 = 0}`, which *is* a subspace. -/
def exercise_1C_1b [CharZero F] :
    Decidable (∃ U : Submodule F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 4}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  push Not
  intro U hU
  have h0 : (0 : Fin 3 → F) ∈ (U : Set (Fin 3 → F)) := U.zero_mem
  -- sub hU in this, to get 0 = 4
  rw [hU] at h0
  simp only [Set.mem_setOf_eq, Pi.zero_apply, mul_zero, add_zero] at h0
  norm_num at h0

/-- 1C.1(c) -/
def exercise_1C_1c :
    Decidable (∃ U : Submodule F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 * v 1 * v 2 = 0}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- show (1, 1, 0) and (0, 0, 1) are in, but their sum is not
  push Not
  intro U hU
  have m1 : (![1, 1, 0] : Fin 3 → F) ∈ (U : Set (Fin 3 → F)) := by
    rw [hU]
    simp
  have m2 : (![0, 0, 1] : Fin 3 → F) ∈ (U : Set (Fin 3 → F)) := by
    rw [hU]
    simp
  have m3 : (![1, 1, 0] + ![0, 0, 1] : Fin 3 → F) ∈ (U : Set (Fin 3 → F)) :=
    U.add_mem m1 m2
  rw [hU] at m3
  simp [Fin.isValue] at m3

/-- 1C.1(d) -/
def exercise_1C_1d :
    Decidable (∃ U : Submodule F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 = 5 * v 2}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  refine ⟨{
    carrier := {v | v 0 = 5 * v 2}
    zero_mem' := by simp
    add_mem' := by
      rintro u v hu hv
      simp only [Set.mem_setOf_eq, Pi.add_apply] at *
      rw [hu, hv]
      ring
    smul_mem' := by
      rintro a v hv
      simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
      rw [hv]
      ring
  }, rfl⟩

/-- 1C.3 Axler's ambient space is {lit}`ℝ^(-4, 4)`, i.e. the function space
{lit}`Set.Ioo (-4) 4 → ℝ`. We use the larger {lit}`ℝ → ℝ` instead because
mathlib's {name}`Differentiable` requires the source to be a normed space and
the subtype {lit}`↥(Set.Ioo (-4) 4)` isn't one. -/
theorem exercise_1C_3 :
    ∃ U : Submodule ℝ (ℝ → ℝ),
      (U : Set (ℝ → ℝ)) =
        {f | DifferentiableOn ℝ f (Set.Ioo (-4) 4) ∧ deriv f (-1) = 3 * f 2} := by
  -- `Set.Ioo (-4) 4` is a neighbourhood of `-1`, so differentiability *on* it
  -- upgrades to differentiability *at* `-1`, which is what `deriv_add` needs.
  have hnhds : Set.Ioo (-4 : ℝ) 4 ∈ nhds (-1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  refine ⟨{
    carrier := {f | DifferentiableOn ℝ f (Set.Ioo (-4) 4) ∧ deriv f (-1) = 3 * f 2}
    zero_mem' := by simp
    add_mem' := by
      rintro f g hf hg
      simp only [Set.mem_setOf_eq, Pi.add_apply] at *
      constructor
      · exact DifferentiableOn.add hf.1 hg.1
      · rw [deriv_add (hf.1.differentiableAt hnhds) (hg.1.differentiableAt hnhds)]
        rw [hf.2, hg.2]
        ring
    smul_mem' := by
      rintro a f hf
      simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
      constructor
      · exact DifferentiableOn.const_smul hf.1 a
      · rw [deriv_const_smul a (hf.1.differentiableAt hnhds), hf.2, smul_eq_mul]
        ring
  }, rfl⟩

/-- 1C.4 Axler's ambient space is {lit}`ℝ^[0,1]`, i.e. {lit}`Set.Icc 0 1 → ℝ`.
We use {lit}`ℝ → ℝ` instead so the integral reads as the familiar
{lit}`∫ x in (0)..1, f x` via {name}`intervalIntegral`; the faithful subtype
version would need measure theory. -/
theorem exercise_1C_4 (b : ℝ) :
    (∃ U : Submodule ℝ (ℝ → ℝ),
        (U : Set (ℝ → ℝ)) =
          {f | ContinuousOn f (Set.Icc 0 1) ∧ ∫ x in (0)..1, f x = b}) ↔ b = 0 := by
  have huIcc : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  constructor
  · -- a subspace contains `0`, whose integral is `0`
    rintro ⟨U, hU⟩
    have h0 : (0 : ℝ → ℝ) ∈ (U : Set (ℝ → ℝ)) := U.zero_mem
    rw [hU] at h0
    simpa using h0.2.symm
  · rintro rfl
    refine ⟨{
      carrier := {f | ContinuousOn f (Set.Icc 0 1) ∧ ∫ x in (0)..1, f x = 0}
      zero_mem' := ⟨continuousOn_const, by simp⟩
      add_mem' := ?_
      smul_mem' := ?_ }, rfl⟩
    · rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
      refine ⟨hf.add hg, ?_⟩
      have hfi : IntervalIntegrable f MeasureTheory.volume 0 1 :=
        (huIcc ▸ hf).intervalIntegrable
      have hgi : IntervalIntegrable g MeasureTheory.volume 0 1 :=
        (huIcc ▸ hg).intervalIntegrable
      simp only [Pi.add_apply]
      rw [intervalIntegral.integral_add hfi hgi, hf', hg', add_zero]
    · rintro a f ⟨hf, hf'⟩
      refine ⟨hf.const_smul a, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [intervalIntegral.integral_const_mul, hf', mul_zero]

/-- 1C.5 -/
def exercise_1C_5 :
    Decidable (∃ U : Submodule ℂ (Fin 2 → ℂ),
      (U : Set (Fin 2 → ℂ)) = {v | ∀ i, (v i).im = 0}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse -- not closed under scalar mult, i * 1 = i
  push Not
  intro U hU
  have h1 : (![1, 0] : Fin 2 → ℂ) ∈ (U : Set (Fin 2 → ℂ)) := by
    rw [hU]
    simp
  have h2 : (Complex.I • ![1, 0] : Fin 2 → ℂ) ∈ (U : Set (Fin 2 → ℂ)) :=
    U.smul_mem Complex.I h1
  rw [hU] at h2
  simp at h2

/-- 1C.6(a) -/
def exercise_1C_6a :
    Decidable (∃ U : Submodule ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 ^ 3 = v 1 ^ 3}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  have cube (a b : ℝ) (h : a ^ 3 = b ^ 3) : a = b := ((by decide : Odd 3).pow_inj).mp h
  -- then equivalent to earlier proofs
  refine ⟨{
    carrier := {v | v 0 ^ 3 = v 1 ^ 3}
    zero_mem' := by simp
    add_mem' := by
      rintro u v hu hv
      simp only [Set.mem_setOf_eq, Pi.add_apply] at *
      rw [cube _ _ hu, cube _ _ hv]
    smul_mem' := by
      rintro a v hv
      simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at *
      rw [cube _ _ hv] }, rfl⟩

/-- A primitive cube root of unity, {lit}`ω = (-1 + √3 i) / 2`. Everything we
need follows from {lit}`ω² + ω + 1 = 0`: cubing gives {lit}`ω³ = 1`, and
{lit}`ω + ω² = -1`. -/
noncomputable def omega : ℂ := (-1 + Real.sqrt 3 * Complex.I) / 2

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_cast
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  simp only [omega]
  field_simp
  linear_combination (Complex.I ^ 2) * h3 + (3 : ℂ) * Complex.I_sq

theorem omega_cube : omega ^ 3 = 1 := by
  linear_combination (omega - 1) * omega_sq_add_omega_add_one

/-- 1C.6(b) -/
def exercise_1C_6b :
    Decidable (∃ U : Submodule ℂ (Fin 3 → ℂ),
      (U : Set (Fin 3 → ℂ)) = {v | v 0 ^ 3 = v 1 ^ 3}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  push Not
  intro U hU
  -- show [1, ω, 0] is in the set and [1, ω^2, 0] too,
  -- but their sum is [2, ω + ω^2, 0], which is not in the set since (ω + ω^2)^3 ≠ 2^3.
  -- since ω + ω^2 = -1, and (-1)^3 ≠ 2^3.
  have h1 : (![1, omega, 0] : Fin 3 → ℂ) ∈ (U : Set (Fin 3 → ℂ)) := by
    rw [hU]
    simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -omega_cube
  have h2 : (![1, omega ^ 2, 0] : Fin 3 → ℂ) ∈ (U : Set (Fin 3 → ℂ)) := by
    rw [hU]
    simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (-(omega ^ 3) - 1) * omega_cube
  have h3 : (![1, omega, 0] + ![1, omega ^ 2, 0] : Fin 3 → ℂ) ∈ (U : Set (Fin 3 → ℂ)) :=
    U.add_mem h1 h2
  rw [hU] at h3
  simp only [Set.mem_setOf_eq, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h3
  have hsum : omega + omega ^ 2 = -1 := by linear_combination omega_sq_add_omega_add_one
  rw [hsum] at h3
  norm_num at h3

/-- 1C.7 -/
def exercise_1C_7 :
    Decidable (∀ U : Set (Fin 2 → ℝ),
      U.Nonempty →
      (∀ u ∈ U, ∀ v ∈ U, u + v ∈ U) →
      (∀ u ∈ U, -u ∈ U) →
      ∃ S : Submodule ℝ (Fin 2 → ℝ), (S : Set (Fin 2 → ℝ)) = U) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- take the integer lattice as a counterexample
  let U : Set (Fin 2 → ℝ) := {v | ∀ i, ∃ n : ℤ, v i = n}
  have hU_nonempty : U.Nonempty := ⟨![0, 0], by simp [U]; use 0; simp only [Int.cast_zero]⟩
  have hU_add : ∀ u ∈ U, ∀ v ∈ U, u + v ∈ U := by
    rintro u hu v hv i
    rcases hu i with ⟨n, hn⟩
    rcases hv i with ⟨m, hm⟩
    exact ⟨n + m, by simp [hm, hn]⟩
  have hU_neg : ∀ u ∈ U, -u ∈ U := by
    rintro u hu i
    rcases hu i with ⟨n, hn⟩
    exact ⟨-n, by simp [hn]⟩
  push Not
  use U, hU_nonempty, hU_add, hU_neg
  intro U' hU'
  -- show not closed under smul with 0.5
  have h1 : (![1, 1] : Fin 2 → ℝ) ∈ (U' : Set (Fin 2 → ℝ)) := by
    rw [hU']
    exact fun i => ⟨1, by fin_cases i <;> simp⟩
  have h2 : ((1 / 2 : ℝ) • ![1, 1] : Fin 2 → ℝ) ∈ (U' : Set (Fin 2 → ℝ)) := U'.smul_mem _ h1
  rw [hU'] at h2
  obtain ⟨n, hn⟩ := h2 0
  simp only [Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul, mul_one] at hn
  -- `1 / 2 = n` is impossible for an integer `n`
  have : (1 : ℤ) = 2 * n := by exact_mod_cast (by linarith : (1 : ℝ) = 2 * (n : ℝ))
  omega

/-- 1C.8 -/
theorem exercise_1C_8 :
    ∃ U : Set (Fin 2 → ℝ),
      U.Nonempty ∧
      (∀ (a : ℝ) (u), u ∈ U → a • u ∈ U) ∧
      ¬ ∃ S : Submodule ℝ (Fin 2 → ℝ), (S : Set (Fin 2 → ℝ)) = U := by
  -- take union of x and y axis
  let U : Set (Fin 2 → ℝ) := {v | v 0 = 0} ∪ {v | v 1 = 0}
  refine ⟨U, ⟨0, Or.inl rfl⟩, ?_, ?_⟩
  · rintro a u (h | h) <;> simp only [Set.mem_setOf_eq] at h
    · exact Or.inl (show a * u 0 = 0 by rw [h, mul_zero])
    · exact Or.inr (show a * u 1 = 0 by rw [h, mul_zero])
  -- not closed under addition: (1,0) + (0,1) = (1,1) is not in the union of axes
  · rintro ⟨S, hS⟩
    have h1 : (![1, 0] : Fin 2 → ℝ) ∈ (S : Set (Fin 2 → ℝ)) := by
      rw [hS]
      exact Or.inr rfl
    have h2 : (![0, 1] : Fin 2 → ℝ) ∈ (S : Set (Fin 2 → ℝ)) := by
      rw [hS]
      exact Or.inl rfl
    have h3 : (![1, 0] + ![0, 1] : Fin 2 → ℝ) ∈ (S : Set (Fin 2 → ℝ)) := S.add_mem h1 h2
    rw [hS] at h3
    simp [U] at h3

def Periodic (f : ℝ → ℝ) : Prop := ∃ p > 0, ∀ x, f x = f (x + p)

/-- {lit}`offLattice c x` is {lit}`0` on the lattice {lit}`ℤ c` and {lit}`1`
off it. Taking {lit}`c = 1` and {lit}`c = √2` gives the two functions used to
break 1C.9. -/
noncomputable def offLattice (c : ℝ) : ℝ → ℝ :=
  Set.indicator {x : ℝ | ¬ ∃ n : ℤ, x = n * c} 1

theorem offLattice_of_mem {c x : ℝ} (h : ∃ n : ℤ, x = n * c) : offLattice c x = 0 :=
  Set.indicator_of_notMem (by simpa using h) 1

theorem offLattice_of_notMem {c x : ℝ} (h : ¬ ∃ n : ℤ, x = n * c) : offLattice c x = 1 :=
  Set.indicator_of_mem h 1

/-- Every {lit}`c > 0` is a period of {lit}`offLattice c`: shifting by
{lit}`c` moves the lattice {lit}`ℤ c` onto itself. -/
theorem periodic_offLattice {c : ℝ} (hc : 0 < c) : Periodic (offLattice c) := by
  refine ⟨c, hc, fun x => ?_⟩
  have hiff : (∃ n : ℤ, x = n * c) ↔ (∃ n : ℤ, x + c = n * c) := by
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n + 1, by push_cast; ring⟩
    · rintro ⟨n, hn⟩
      exact ⟨n - 1, by push_cast; linarith⟩
  by_cases h : ∃ n : ℤ, x = n * c
  · rw [offLattice_of_mem h, offLattice_of_mem (hiff.mp h)]
  · rw [offLattice_of_notMem h, offLattice_of_notMem (fun hc => h (hiff.mpr hc))]

/-- 1C.9 -/
def exercise_1C_9 :
    Decidable (∃ U : Submodule ℝ (ℝ → ℝ), (U : Set (ℝ → ℝ)) = {f | Periodic f}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- take f x = if x ∈ Z then 0 else 1
  -- take g x = if x ∈ √2 ℤ then 0 else 1
  -- by contradiction assumed f + g is also periodic with period p
  -- then (f + g) 0 = f 0 + g 0 = 0
  -- but also f p + g p = 0, this can only happen if p = n and p = m √2,
  -- contradiction since √2 is not rational
  push Not
  intro U hU
  have hf : offLattice 1 ∈ (U : Set (ℝ → ℝ)) := by
    rw [hU]; exact periodic_offLattice one_pos
  have hg : offLattice (Real.sqrt 2) ∈ (U : Set (ℝ → ℝ)) := by
    rw [hU]; exact periodic_offLattice (Real.sqrt_pos.mpr (by norm_num))
  have hfg : offLattice 1 + offLattice (Real.sqrt 2) ∈ (U : Set (ℝ → ℝ)) := U.add_mem hf hg
  rw [hU] at hfg
  obtain ⟨p, hp, hper⟩ := hfg
  have h0 : (offLattice 1 + offLattice (Real.sqrt 2)) 0 = 0 := by
    rw [Pi.add_apply, offLattice_of_mem ⟨0, by simp⟩, offLattice_of_mem ⟨0, by simp⟩, add_zero]
  have hpsum : offLattice 1 p + offLattice (Real.sqrt 2) p = 0 := by
    have h := (hper 0).symm
    rw [zero_add, h0] at h
    exact h
  by_cases hA : ∃ n : ℤ, p = n * 1 <;> by_cases hB : ∃ n : ℤ, p = n * Real.sqrt 2
  · -- `p = n` and `p = m √2` with `m ≠ 0`, so `√2 = n / m` is rational
    obtain ⟨n, hn⟩ := hA
    obtain ⟨m, hm⟩ := hB
    have hm0 : (m : ℝ) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hm
      linarith
    refine irrational_sqrt_two ⟨(n : ℚ) / (m : ℚ), ?_⟩
    push_cast
    rw [div_eq_iff hm0, ← mul_one (n : ℝ), ← hn, hm]
    ring
  · rw [offLattice_of_mem hA, offLattice_of_notMem hB] at hpsum
    norm_num at hpsum
  · rw [offLattice_of_notMem hA, offLattice_of_mem hB] at hpsum
    norm_num at hpsum
  · rw [offLattice_of_notMem hA, offLattice_of_notMem hB] at hpsum
    norm_num at hpsum

/-- 1C.10 The intersection of two subspaces is a subspace. The student must
build a {name}`Submodule` whose carrier is {lit}`(U : Set V) ∩ (W : Set V)`,
i.e. prove the three closure axioms hold for the intersection. (In mathlib
this submodule is the lattice infimum {lit}`U ⊓ W`, which the
{name}`SemilatticeInf` instance on {name}`Submodule` produces automatically;
the exercise is to do that construction by hand.) -/
theorem exercise_1C_10 (U W : Submodule F V) :
    ∃ S : Submodule F V, (S : Set V) = (U : Set V) ∩ (W : Set V) := by
  refine ⟨{
    carrier := (U : Set V) ∩ (W : Set V)
    zero_mem' := by simp
    add_mem' := by
      rintro u v ⟨huU, huW⟩ ⟨hvU, hvW⟩
      rw [Set.mem_inter_iff]
      constructor
      · exact U.add_mem huU hvU
      · exact W.add_mem huW hvW
    smul_mem' := by
      rintro a v ⟨hvU, hvW⟩
      simp
      constructor
      · exact U.smul_mem a hvU
      · exact W.smul_mem a hvW
  }, rfl⟩

/-- 1C.11 The intersection of *any* collection of subspaces of {lit}`V` is a
subspace. The student must build a {name}`Submodule` whose carrier is the
intersection {lit}`⋂ U ∈ 𝒞, (U : Set V)`, i.e. prove the three closure axioms
hold for an arbitrary intersection. (In mathlib this submodule is the lattice
infimum {name}`sInf` (or {name}`iInf` for an indexed family), which the
{name}`CompleteLattice` instance on {name}`Submodule` produces automatically;
the exercise is to do that construction by hand.) -/
theorem exercise_1C_11 (𝒞 : Set (Submodule F V)) :
    ∃ S : Submodule F V, (S : Set V) = ⋂ U ∈ 𝒞, (U : Set V) := by
  -- same as above
  refine ⟨{
    carrier := ⋂ U ∈ 𝒞, (U : Set V)
    zero_mem' := by
      simp only [Set.mem_iInter, SetLike.mem_coe, zero_mem, implies_true]
    add_mem' := by
      rintro u v hu hv
      simp at hu hv
      simp
      rintro U hU
      exact U.add_mem (hu U hU) (hv U hU)
    smul_mem' := by
      rintro a v hv
      simp at hv
      simp
      rintro U hU
      exact U.smul_mem a (hv U hU)
  }, rfl⟩

/-- 1C.12 -/
@[avoiding Submodule.union_eq_iff_le_or_le]
theorem exercise_1C_12 (U W : Submodule F V) :
    (∃ S : Submodule F V, (S : Set V) = (U : Set V) ∪ (W : Set V)) ↔
      U ≤ W ∨ W ≤ U := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    -- take u in U \ W and w in W \ U
    obtain ⟨S, hS⟩ := h
    obtain ⟨huw, hwu⟩ := h'
    obtain ⟨u, huU, huW⟩ := SetLike.not_le_iff_exists.mp huw
    obtain ⟨w, hwW, hwU⟩ := SetLike.not_le_iff_exists.mp hwu
    -- then u + w should be in submodule, by additivity
    have hu : u ∈ (S : Set V) := by rw [hS]; exact Or.inl huU
    have hw : w ∈ (S : Set V) := by rw [hS]; exact Or.inr hwW
    have huw' : u + w ∈ (S : Set V) := S.add_mem hu hw
    rw [hS] at huw'
    -- but by negation of W and U additivity, it has to be outside W and U
    -- thus outside the union, contradition
    rcases huw' with h | h
    · exact hwU (by simpa using U.sub_mem h huU)
    · exact huW (by simpa using W.sub_mem h hwW)
  · intro h
    cases h with
    -- the union is the *bigger* of the two subspaces
    | inl h =>
      use W
      exact (Set.union_eq_right.mpr (SetLike.coe_subset_coe.mpr h)).symm
    | inr h =>
      use U
      exact (Set.union_eq_left.mpr (SetLike.coe_subset_coe.mpr h)).symm

/-- 1C.13 To prove this we need a scalar in {lit}`F` other than {lit}`0` and
{lit}`1`; we assume {lit}`[CharZero F]`, which forces {lit}`(n : F) ≠ 0` for
every positive {lit}`n` and is satisfied by {lit}`ℝ` and {lit}`ℂ` (Axler's working fields). -/
theorem exercise_1C_13 [CharZero F] (U W X : Submodule F V) :
    (∃ S : Submodule F V, (S : Set V) = (U : Set V) ∪ W ∪ X) ↔
      (W ≤ U ∧ X ≤ U) ∨ (U ≤ W ∧ X ≤ W) ∨ (U ≤ X ∧ W ≤ X) := by
  constructor
  · rintro ⟨S, hS⟩
    -- if `U ≤ X` or `X ≤ U` the union collapses to two subspaces, so 1C.12 applies
    by_cases hUX : U ≤ X
    · have hSWX : (S : Set V) = (W : Set V) ∪ (X : Set V) := by
        have hsub : (U : Set V) ⊆ (W : Set V) ∪ (X : Set V) :=
          (SetLike.coe_subset_coe.mpr hUX).trans Set.subset_union_right
        rw [hS, Set.union_assoc, Set.union_eq_right.mpr hsub]
      rcases (exercise_1C_12 W X).mp ⟨S, hSWX⟩ with hWX | hXW
      · exact Or.inr (Or.inr ⟨hUX, hWX⟩)
      · exact Or.inr (Or.inl ⟨hUX.trans hXW, hXW⟩)
    by_cases hXU : X ≤ U
    · have hSUW : (S : Set V) = (U : Set V) ∪ (W : Set V) := by
        have hsub : (X : Set V) ⊆ (U : Set V) ∪ (W : Set V) :=
          (SetLike.coe_subset_coe.mpr hXU).trans Set.subset_union_left
        rw [hS, Set.union_eq_left.mpr hsub]
      rcases (exercise_1C_12 U W).mp ⟨S, hSUW⟩ with hUW | hWU
      · exact Or.inr (Or.inl ⟨hUW, hXU.trans hUW⟩)
      · exact Or.inl ⟨hWU, hXU⟩
    -- start with u in U \ X, and x in X \ U
    obtain ⟨u, huU, huX⟩ := SetLike.not_le_iff_exists.mp hUX
    obtain ⟨x, hxX, hxU⟩ := SetLike.not_le_iff_exists.mp hXU
    -- 1 * u + x , can't be in X or U, so W
    -- 2 * u + x , can't be in X or U, so W (need char ≠ 2)
    -- but then u ∈ W by subtracting, and x in W too
    have key : ∀ v ∈ U, v ∉ X → ∀ y ∈ X, y ∉ U → v ∈ W ∧ y ∈ W := by
      intro v hvU hvX y hyX hyU
      have hvS : v ∈ (S : Set V) := by rw [hS]; exact Or.inl (Or.inl hvU)
      have hyS : y ∈ (S : Set V) := by rw [hS]; exact Or.inr hyX
      have hW : ∀ a : F, a ≠ 0 → a • v + y ∈ W := by
        intro a ha
        have hmem : a • v + y ∈ (S : Set V) := S.add_mem (S.smul_mem a hvS) hyS
        rw [hS] at hmem
        rcases hmem with (hu | hw) | hx
        · -- `y = (a • v + y) - a • v ∈ U`
          exact absurd (by simpa using U.sub_mem hu (U.smul_mem a hvU)) hyU
        · exact hw
        · -- `a • v = (a • v + y) - y ∈ X`, hence `v ∈ X`
          have hav : a • v ∈ X := by simpa using X.sub_mem hx hyX
          exact absurd (by simpa [inv_smul_smul₀ ha] using X.smul_mem a⁻¹ hav) hvX
      have h1 : (1 : F) • v + y ∈ W := hW 1 one_ne_zero
      have h2 : (2 : F) • v + y ∈ W := hW 2 (by norm_num)
      have hvW : v ∈ W := by simpa [two_smul] using W.sub_mem h2 h1
      exact ⟨hvW, by simpa using W.sub_mem h1 hvW⟩
    obtain ⟨huW, hxW⟩ := key u huU huX x hxX hxU
    -- every element of `U` and of `X` is now in `W`
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · intro v hvU
      by_cases hvX : v ∈ X
      · -- `v ∈ U ∩ X`: shift by `u` to leave `X`, then subtract `u` again
        have h1 : v + u ∈ U := U.add_mem hvU huU
        have h2 : v + u ∉ X := fun hc => huX (by simpa using X.sub_mem hc hvX)
        have h3 := (key (v + u) h1 h2 x hxX hxU).1
        simpa using W.sub_mem h3 huW
      · exact (key v hvU hvX x hxX hxU).1
    · intro y hyX
      by_cases hyU : y ∈ U
      · have h1 : y + x ∈ X := X.add_mem hyX hxX
        have h2 : y + x ∉ U := fun hc => hxU (by simpa using U.sub_mem hc hyU)
        have h3 := (key u huU huX (y + x) h1 h2).2
        simpa using W.sub_mem h3 hxW
      · exact (key u huU huX y hyX hyU).2
  · intro h
    rcases h with h | h | h
    -- the union is whichever of the three contains the other two;
    -- `union_eq_left` absorbs on the right, `union_eq_right` on the left
    · use U
      have h1 : (U : Set V) = (U : Set V) ∪ (W : Set V) := by
        exact (Set.union_eq_left.mpr (SetLike.coe_subset_coe.mpr h.1)).symm
      have h2: (U : Set V) = (U : Set V) ∪ (X : Set V) := by
        exact (Set.union_eq_left.mpr (SetLike.coe_subset_coe.mpr h.2)).symm
      rw [← h1, ← h2]
    · use W
      have h1 : (W : Set V) = (U : Set V) ∪ (W : Set V) := by
        exact (Set.union_eq_right.mpr (SetLike.coe_subset_coe.mpr h.1)).symm
      have h2 : (W : Set V) = (W : Set V) ∪ (X : Set V) := by
        exact (Set.union_eq_left.mpr (SetLike.coe_subset_coe.mpr h.2)).symm
      rw [← h1, ← h2]
    -- here the goal associates as `(↑U ∪ ↑W) ∪ ↑X`, so absorb both at once
    · use X
      have h1 : (U : Set V) ∪ (W : Set V) ⊆ (X : Set V) :=
        Set.union_subset (SetLike.coe_subset_coe.mpr h.1) (SetLike.coe_subset_coe.mpr h.2)
      exact (Set.union_eq_right.mpr h1).symm

/-- 1C.14 -/
def exercise_1C_14_U : Submodule F (Fin 3 → F) where
  carrier := {v | ∃ x : F, v = ![x, -x, 2 * x]}
  zero_mem' := ⟨0, by
    funext i
    fin_cases i
    · simp
    · simp
    · simp⟩
  add_mem' := by
    rintro u v ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    funext i
    fin_cases i
    · simp
    · simp; ring
    · simp; ring
  smul_mem' := by
    rintro a v ⟨x, rfl⟩
    refine ⟨a * x, ?_⟩
    funext i
    fin_cases i
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]; ring

def exercise_1C_14_W : Submodule F (Fin 3 → F) where
  carrier := {v | ∃ x : F, v = ![x, x, 2 * x]}
  zero_mem' := ⟨0, by
    funext i
    fin_cases i
    · simp
    · simp
    · simp⟩
  add_mem' := by
    rintro u v ⟨x, rfl⟩ ⟨y, rfl⟩
    refine ⟨x + y, ?_⟩
    funext i
    fin_cases i
    · simp
    · simp
    · simp; ring
  smul_mem' := by
    rintro a v ⟨x, rfl⟩
    refine ⟨a * x, ?_⟩
    funext i
    fin_cases i
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]; ring

/-- The sum is the plane {lit}`{v | v 2 = 2 * v 0}` — in words, the vectors
whose third coordinate is twice the first. Splitting an arbitrary such vector
back into a piece of {lit}`U` and a piece of {lit}`W` needs to halve, so we
assume {lit}`[CharZero F]`; in characteristic {lit}`2` we would have
{lit}`U = W = {(x, x, 0)}`, which is strictly smaller than the plane. -/
theorem exercise_1C_14 [CharZero F] :
    ((exercise_1C_14_U ⊔ exercise_1C_14_W : Submodule F (Fin 3 → F))
      : Set (Fin 3 → F)) = {v | v 2 = 2 * v 0} := by
  -- just combining the equations for both lines, are relabeling the coordinates accordingly
  ext v
  simp only [SetLike.mem_coe, Submodule.mem_sup, Set.mem_setOf_eq]
  constructor
  · -- `(x, -x, 2x) + (y, y, 2y) = (x + y, y - x, 2 (x + y))`
    rintro ⟨a, ⟨x, rfl⟩, b, ⟨y, rfl⟩, rfl⟩
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    ring
  · -- read `x` and `y` off `v` by halving: `x = (v 0 - v 1) / 2`, `y = (v 0 + v 1) / 2`
    intro hv
    refine ⟨![(v 0 - v 1) / 2, -((v 0 - v 1) / 2), 2 * ((v 0 - v 1) / 2)], ⟨_, rfl⟩,
      ![(v 0 + v 1) / 2, (v 0 + v 1) / 2, 2 * ((v 0 + v 1) / 2)], ⟨_, rfl⟩, ?_⟩
    funext i
    fin_cases i
    · show (v 0 - v 1) / 2 + (v 0 + v 1) / 2 = v 0
      ring
    · show -((v 0 - v 1) / 2) + (v 0 + v 1) / 2 = v 1
      ring
    · show 2 * ((v 0 - v 1) / 2) + 2 * ((v 0 + v 1) / 2) = v 2
      linear_combination -hv

/-- 1C.15 -/
@[avoiding sup_idem, sup_self]
theorem exercise_1C_15 (U : Submodule F V) : U ⊔ U = U := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨x, hx, y, hy, rfl⟩ := hx
    exact U.add_mem hx hy
  · intro hx
    exact Submodule.mem_sup_left hx

/-- 1C.16 -/
@[avoiding sup_comm]
def exercise_1C_16 :
    Decidable (∀ U W : Submodule F V, U ⊔ W = W ⊔ U) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  intro U W
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_sup] at hx ⊢
    obtain ⟨x, hxU, y, hyW, rfl⟩ := hx
    use y, hyW, x, hxU
    exact add_comm y x
  · intro hx
    rw [Submodule.mem_sup] at hx ⊢
    obtain ⟨x, hxU, y, hyW, rfl⟩ := hx
    use y, hyW, x, hxU
    exact add_comm y x

/-- 1C.17 -/
@[avoiding sup_assoc]
def exercise_1C_17 :
    Decidable (∀ V₁ V₂ V₃ : Submodule F V, (V₁ ⊔ V₂) ⊔ V₃ = V₁ ⊔ (V₂ ⊔ V₃)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  intro V₁ V₂ V₃
  ext x
  constructor
  · intro hx
    simp [Submodule.mem_sup] at hx ⊢
    obtain ⟨x, hxV₁, y, hyV₂, z, hzV₃, rfl⟩ := hx
    use x, hxV₁, y, hyV₂, z, hzV₃
    rw [add_assoc]
  · intro hx
    simp [Submodule.mem_sup] at hx ⊢
    obtain ⟨x, hxV₁, y, hyV₂, z, hzV₃, rfl⟩ := hx
    use x, hxV₁, y, hyV₂, z, hzV₃
    rw [add_assoc]

/-- 1C.18(a) - does there exist a subspace E such that for all subspaces U, U ⊔ E = U, i.e., E is the additive identity? -/
@[avoiding bot_sup_eq, sup_bot_eq]
def exercise_1C_18_id :
    Decidable (∃ E : Submodule F V, ∀ U : Submodule F V, U ⊔ E = U) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isTrue
  use ⊥
  intro U
  -- `U + {0} ⊆ U` because both summands are, and `U ⊆ U + {0}`
  exact le_antisymm (sup_le le_rfl bot_le) le_sup_left

/-- 1C.18(b) *Which subspaces have an additive inverse under sum?* (i.e., for
which {lit}`U` does there exist {lit}`W` with {lit}`U + W = ⊥`?) Only
{lit}`U = ⊥` does. -/
theorem exercise_1C_18_inv (U : Submodule F V) :
    (∃ W : Submodule F V, U ⊔ W = ⊥) ↔ U = ⊥ := by
  constructor
  · intro h
    obtain ⟨W, hW⟩ := h
    -- `U` is one of the summands, so `U ⊆ U + W = ⊥`, and `⊥` is the smallest subspace
    have hle : U ≤ ⊥ := hW ▸ le_sup_left
    exact le_bot_iff.mp hle
  · intro h
    subst U
    use ⊥
    exact sup_bot_eq ⊥

/-- 1C.19 -/
def exercise_1C_19 :
    Decidable (∀ V₁ V₂ U : Submodule ℝ (Fin 2 → ℝ),
      V₁ ⊔ U = V₂ ⊔ U → V₁ = V₂) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- use V₁ = ⊥, V₂ = U = ⊤, for non-trivial V
  push Not
  use ⊥, ⊤, ⊤
  simp only [le_top, sup_of_le_right, Std.le_refl, ne_eq, bot_ne_top,
    not_false_eq_true, and_self]

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
    rintro u v ⟨h0, h2⟩ ⟨h0', h2'⟩
    exact ⟨by simp [Pi.add_apply, h0, h0'], by simp [Pi.add_apply, h2, h2']⟩
  smul_mem' := by
    rintro a v ⟨h0, h2⟩
    exact ⟨by simp [Pi.smul_apply, h0], by simp [Pi.smul_apply, h2]⟩

/-- Vectors in {lit}`exercise_1C_20_U` are determined by their first and third
coordinates, so killing those two coordinates gives a complement. -/
theorem exercise_1C_20 :
    IsCompl (exercise_1C_20_U (F := F)) exercise_1C_20_W := by
  constructor
  · -- `v 0 = v 1` and `v 0 = 0` force the first pair to vanish, likewise the second
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro v ⟨⟨h01, h23⟩, h0, h2⟩
    funext i
    fin_cases i
    · exact h0
    · exact h01.symm.trans h0
    · exact h2
    · exact h23.symm.trans h2
  · -- `v = (v 0, v 0, v 2, v 2) + (0, v 1 - v 0, 0, v 3 - v 2)`
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr ⟨![v 0, v 0, v 2, v 2], ⟨rfl, rfl⟩,
      ![0, v 1 - v 0, 0, v 3 - v 2], ⟨rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> simp

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
  carrier := {v | v 0 = 0 ∧ v 1 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h0, h1⟩ ⟨h0', h1'⟩
    exact ⟨by simp [Pi.add_apply, h0, h0'], by simp [Pi.add_apply, h1, h1']⟩
  smul_mem' := by
    rintro a v ⟨h0, h1⟩
    exact ⟨by simp [Pi.smul_apply, h0], by simp [Pi.smul_apply, h1]⟩

/-- A vector of {lit}`exercise_1C_21_U` is determined by its first two
coordinates, so the subspace where those two vanish is a complement. -/
theorem exercise_1C_21 :
    IsCompl (exercise_1C_21_U (F := F)) exercise_1C_21_W := by
  constructor
  · -- with `v 0 = v 1 = 0` the three defining equations force the rest to vanish
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro v ⟨⟨h2, h3, h4⟩, h0, h1⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · show v 2 = 0; rw [h2, h0, h1, add_zero]
    · show v 3 = 0; rw [h3, h0, h1, sub_zero]
    · show v 4 = 0; rw [h4, h0, mul_zero]
  · -- `v = (x, y, x + y, x - y, 2x) + (0, 0, ⋯)` with `x = v 0`, `y = v 1`
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr
      ⟨![v 0, v 1, v 0 + v 1, v 0 - v 1, 2 * v 0], ⟨rfl, rfl, rfl⟩,
       ![0, 0, v 2 - (v 0 + v 1), v 3 - (v 0 - v 1), v 4 - 2 * v 0], ⟨rfl, rfl⟩, ?_⟩
    funext i
    fin_cases i <;> simp

/-- 1C.22 The three coordinate axes carrying {lit}`v 2`, {lit}`v 3`, {lit}`v 4`
complete {lit}`exercise_1C_21_U` to all of {lit}`F⁵`. -/
def exercise_1C_22_W₁ : Submodule F (Fin 5 → F) := {
  carrier := {v | v 0 = 0 ∧ v 1 = 0 ∧ v 3 = 0 ∧ v 4 = 0},
  zero_mem' := by simp,
  add_mem' := by
    rintro u v ⟨h0, h1, h3, h4⟩ ⟨h0', h1', h3', h4'⟩
    simp [h0, h1, h3, h4, h0', h1', h3', h4'],
  smul_mem' := by
    rintro a v ⟨h0, h1, h3, h4⟩
    simp [h0, h1, h3, h4]
}
def exercise_1C_22_W₂ : Submodule F (Fin 5 → F) := {
    carrier := {v | v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 4 = 0},
    zero_mem' := by simp,
    add_mem' := by
      rintro u v ⟨h0, h1, h2, h4⟩ ⟨h0', h1', h2', h4'⟩
      simp [h0, h1, h2, h4, h0', h1', h2', h4'],
    smul_mem' := by
      rintro a v ⟨h0, h1, h2, h4⟩
      simp [h0, h1, h2, h4]
}
def exercise_1C_22_W₃ : Submodule F (Fin 5 → F) := {
  carrier := {v | v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0},
  zero_mem' := by simp,
  add_mem' := by
    rintro u v ⟨h0, h1, h2, h3⟩ ⟨h0', h1', h2', h3'⟩
    simp [h0, h1, h2, h3, h0', h1', h2', h3'],
  smul_mem' := by
    rintro a v ⟨h0, h1, h2, h3⟩
    simp [h0, h1, h2, h3]
}

/-! Each of the three axes is nonzero: it contains a standard basis vector. -/

theorem exercise_1C_22_W₁_ne_bot : exercise_1C_22_W₁ (F := F) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨![0, 0, 1, 0, 0], ⟨rfl, rfl, rfl, rfl⟩, fun h => by simpa using congrFun h 2⟩

theorem exercise_1C_22_W₂_ne_bot : exercise_1C_22_W₂ (F := F) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨![0, 0, 0, 1, 0], ⟨rfl, rfl, rfl, rfl⟩, fun h => by simpa using congrFun h 3⟩

theorem exercise_1C_22_W₃_ne_bot : exercise_1C_22_W₃ (F := F) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨![0, 0, 0, 0, 1], ⟨rfl, rfl, rfl, rfl⟩, fun h => by simpa using congrFun h 4⟩

/-- The direct-sum condition is captured by {name}`IsDirectSum` on the family
{lit}`![U, W₁, W₂, W₃]`; the cover by {lit}`U ⊔ W₁ ⊔ W₂ ⊔ W₃ = ⊤`. -/
theorem exercise_1C_22 :
      IsDirectSum ![exercise_1C_21_U (F := F), exercise_1C_22_W₁, exercise_1C_22_W₂,
        exercise_1C_22_W₃] ∧
      exercise_1C_21_U (F := F) ⊔ exercise_1C_22_W₁ ⊔ exercise_1C_22_W₂ ⊔ exercise_1C_22_W₃
        = ⊤ := by
  constructor
  · -- directness: a vanishing sum forces all four components to vanish
    rw [isDirectSum_iff]
    intro u
    refine ⟨fun hsum => ?_, fun hu => by simp [hu]⟩
    obtain ⟨e2, e3, e4⟩ : (u 0 : Fin 5 → F) ∈ exercise_1C_21_U := (u 0).2
    obtain ⟨b0, b1, b3, b4⟩ : (u 1 : Fin 5 → F) ∈ exercise_1C_22_W₁ := (u 1).2
    obtain ⟨c0, c1, c2, c4⟩ : (u 2 : Fin 5 → F) ∈ exercise_1C_22_W₂ := (u 2).2
    obtain ⟨d0, d1, d2, d3⟩ : (u 3 : Fin 5 → F) ∈ exercise_1C_22_W₃ := (u 3).2
    have hco : ∀ j, (u 0 : Fin 5 → F) j + (u 1 : Fin 5 → F) j + (u 2 : Fin 5 → F) j
        + (u 3 : Fin 5 → F) j = 0 := by
      intro j
      have h := congrFun hsum j
      simpa [Finset.sum_apply, Fin.sum_univ_four] using h
    -- coordinates 0 and 1 only see the `U`-component, which then vanishes entirely
    have z0 : (u 0 : Fin 5 → F) 0 = 0 := by
      have h := hco 0; rw [b0, c0, d0] at h; simpa using h
    have z1 : (u 0 : Fin 5 → F) 1 = 0 := by
      have h := hco 1; rw [b1, c1, d1] at h; simpa using h
    have hu0 : (u 0 : Fin 5 → F) = 0 := by
      funext j
      fin_cases j
      · exact z0
      · exact z1
      · show (u 0 : Fin 5 → F) 2 = 0; rw [e2, z0, z1, add_zero]
      · show (u 0 : Fin 5 → F) 3 = 0; rw [e3, z0, z1, sub_zero]
      · show (u 0 : Fin 5 → F) 4 = 0; rw [e4, z0, mul_zero]
    have hz : ∀ j, (u 0 : Fin 5 → F) j = 0 := fun j => congrFun hu0 j
    -- each remaining component lives on one axis, and is read off at that coordinate
    have hu1 : (u 1 : Fin 5 → F) = 0 := by
      funext j
      fin_cases j
      · exact b0
      · exact b1
      · show (u 1 : Fin 5 → F) 2 = 0
        have h := hco 2; rw [hz 2, c2, d2] at h; simpa using h
      · exact b3
      · exact b4
    have hu2 : (u 2 : Fin 5 → F) = 0 := by
      funext j
      fin_cases j
      · exact c0
      · exact c1
      · exact c2
      · show (u 2 : Fin 5 → F) 3 = 0
        have h := hco 3; rw [hz 3, b3, d3] at h; simpa using h
      · exact c4
    have hu3 : (u 3 : Fin 5 → F) = 0 := by
      funext j
      fin_cases j
      · exact d0
      · exact d1
      · exact d2
      · exact d3
      · show (u 3 : Fin 5 → F) 4 = 0
        have h := hco 4; rw [hz 4, b4, c4] at h; simpa using h
    funext i
    fin_cases i <;> apply Subtype.ext
    · exact hu0
    · exact hu1
    · exact hu2
    · exact hu3
  · -- cover: split off the `U`-part `(x, y, x + y, x - y, 2x)`, then correct each
    -- of the last three coordinates along its own axis
    rw [eq_top_iff]
    intro v _
    have hv : v = ![v 0, v 1, v 0 + v 1, v 0 - v 1, 2 * v 0]
        + ![0, 0, v 2 - (v 0 + v 1), 0, 0]
        + ![0, 0, 0, v 3 - (v 0 - v 1), 0]
        + ![0, 0, 0, 0, v 4 - 2 * v 0] := by
      funext j
      fin_cases j <;> simp
    rw [hv]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_left ⟨rfl, rfl, rfl⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_sup_right ⟨rfl, rfl, rfl, rfl⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨rfl, rfl, rfl, rfl⟩)
    · exact Submodule.mem_sup_right ⟨rfl, rfl, rfl, rfl⟩

/-- The {lit}`x`-axis {lit}`{(x, 0)}`. -/
def exercise_1C_23_V₁ : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v | v 1 = 0}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 1 + v 1 = 0; rw [hu, hv, add_zero]
  smul_mem' := by intro a v hv; show a • v 1 = 0; rw [hv, smul_zero]

/-- The {lit}`y`-axis {lit}`{(0, y)}`. -/
def exercise_1C_23_V₂ : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v | v 0 = 0}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 0 + v 0 = 0; rw [hu, hv, add_zero]
  smul_mem' := by intro a v hv; show a • v 0 = 0; rw [hv, smul_zero]

/-- The diagonal {lit}`{(x, x)}`. -/
def exercise_1C_23_U : Submodule ℝ (Fin 2 → ℝ) where
  carrier := {v | v 0 = v 1}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 0 + v 0 = u 1 + v 1; rw [hu, hv]
  smul_mem' := by intro a v hv; show a • v 0 = a • v 1; rw [hv]

/-- 1C.23 -/
def exercise_1C_23 :
    Decidable (∀ V₁ V₂ U : Submodule ℝ (Fin 2 → ℝ),
      IsCompl V₁ U → IsCompl V₂ U → V₁ = V₂) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- V₁ - x-axis, V₂ - y-axis, U - the diagonal line y = x
  push Not
  refine ⟨exercise_1C_23_V₁, exercise_1C_23_V₂, exercise_1C_23_U, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · -- on the `x`-axis `v 1 = 0`, on the diagonal `v 0 = v 1`, so `v = 0`
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro v ⟨h1, h01⟩
    funext i
    fin_cases i
    · exact h01.trans h1
    · exact h1
  · -- `v = (v 0 - v 1, 0) + (v 1, v 1)`
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr ⟨![v 0 - v 1, 0], rfl, ![v 1, v 1], rfl, ?_⟩
    funext i
    fin_cases i <;> simp
  · -- on the `y`-axis `v 0 = 0`, on the diagonal `v 0 = v 1`, so `v = 0`
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro v ⟨h0, h01⟩
    funext i
    fin_cases i
    · exact h0
    · exact h01.symm.trans h0
  · -- `v = (0, v 1 - v 0) + (v 0, v 0)`
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr ⟨![0, v 1 - v 0], rfl, ![v 0, v 0], rfl, ?_⟩
    funext i
    fin_cases i <;> simp
  · -- `(1, 0)` is on the `x`-axis but not on the `y`-axis
    intro h
    have hmem : (![1, 0] : Fin 2 → ℝ) ∈ exercise_1C_23_V₁ := rfl
    rw [h] at hmem
    exact one_ne_zero (hmem : (1 : ℝ) = 0)

/-- 1C.24 -/

def IsEven (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = f x
def IsOdd  (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = -f x

def evenFunctions : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsEven f}
  zero_mem' := by
    simp [IsEven]
  add_mem' := by
    intro f g hf hg x
    simp [IsEven] at hg hf ⊢
    specialize hf x
    specialize hg x
    simp [hf, hg]
  smul_mem' := by
    intro a f hf x
    simp [IsEven] at hf ⊢
    specialize hf x
    simp [hf]

def oddFunctions : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | IsOdd f}
  zero_mem' := by
    simp [IsOdd]
  add_mem' := by
    intro f g hf hg x
    simp [IsOdd] at hf hg ⊢
    specialize hf x
    specialize hg x
    simp [hf, hg]
    rw [add_comm]
  smul_mem' := by
    intro a f hf x
    simp [IsOdd] at hf ⊢
    specialize hf x
    simp [hf]

theorem exercise_1C_24 : IsCompl evenFunctions oddFunctions := by
  constructor
  · -- a function that is both even and odd satisfies `f x = -f x`, so `f = 0`
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro f ⟨he, ho⟩
    funext x
    have h : f x = -f x := (he x).symm.trans (ho x)
    show f x = 0
    linarith
  · -- use f_even(x) = f(x) + f(-x) and f_odd(x) = f(x) - f(-x)
    -- prove f_even is even, f_odd is odd
    -- f = 1/2 f_even + 1/2 f_odd
    rw [codisjoint_iff, eq_top_iff]
    intro f _
    refine Submodule.mem_sup.mpr ⟨fun x => (f x + f (-x)) / 2, fun x => ?_,
      fun x => (f x - f (-x)) / 2, fun x => ?_, ?_⟩
    · show (f (-x) + f (- -x)) / 2 = (f x + f (-x)) / 2
      rw [neg_neg]; ring
    · show (f (-x) - f (- -x)) / 2 = -((f x - f (-x)) / 2)
      rw [neg_neg]; ring
    · funext x
      show (f x + f (-x)) / 2 + (f x - f (-x)) / 2 = f x
      ring

end LADR.Section_1C
