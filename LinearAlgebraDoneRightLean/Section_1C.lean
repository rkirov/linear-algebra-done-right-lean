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

In Lean/mathlib the bundled object {name}`Subspace` (an abbreviation for
{name}`Submodule` over a {name}`DivisionRing`) carries the carrier set
together with the three closure proofs at once. -/

/-! 1.34 Conditions for a subspace

A subset is a subspace iff it contains {lit}`0`, is closed under addition, and is
closed under scalar multiplication. These are exactly the three fields of
{name}`Subspace`. -/

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

example (U : Subspace F V) {u : V} (hu : u ∈ U) : -u ∈ U := U.neg_mem hu

/-! 1.35 Example: subspaces / Exercise 1C.2

Verify that the sets in (a)–(e) are subspaces. We give the carrier, the
{lit}`0`-membership proof, and the scalar-closure proof; the additive-closure
{lit}`add_mem'` is left as {lit}`sorry` for the reader. -/

/-! 1.35(a) The set {lit}`{(x₁, x₂, x₃, x₄) ∈ F⁴ : x₃ = 5 x₄ + b}` is a
subspace of {lit}`F⁴` iff {lit}`b = 0` (the {lit}`b = 0` direction is shown
here; both directions are exercise 1C.1 above). -/

example : Subspace F (Fin 4 → F) where
  carrier := {v | v 2 = 5 * v 3}
  zero_mem' := by simp
  add_mem' := by sorry
  smul_mem' := by sorry

/-! 1.35(b) Continuous real-valued functions on {lit}`[0, 1]` form a subspace
of {lit}`ℝ^[0,1]`. (Axler uses {lit}`[0, 1]`; we work over all of {lit}`ℝ` —
the closure proofs are identical.) -/

example : Subspace ℝ (ℝ → ℝ) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := by sorry
  smul_mem' a _ hf := by sorry

/-! 1.35(c) Differentiable real-valued functions on {lit}`ℝ` form a subspace
of {lit}`ℝ^ℝ`. -/

example : Subspace ℝ (ℝ → ℝ) where
  carrier := {f | Differentiable ℝ f}
  zero_mem' := differentiable_const 0
  add_mem' hf hg := by sorry
  smul_mem' a _ hf := by sorry

/-! 1.35(d) Differentiable real-valued functions on {lit}`(0, 3)` such that
{lit}`f'(2) = 0` form a subspace. We work on all of {lit}`ℝ` and pin the
derivative at {lit}`2`; both addition and scalar multiplication preserve the
derivative being zero at a point. -/

example : Subspace ℝ (ℝ → ℝ) where
  carrier := {f | Differentiable ℝ f ∧ deriv f 2 = 0}
  zero_mem' := ⟨differentiable_const 0, by simp⟩
  add_mem' := by sorry
  smul_mem' := by sorry

/-! 1.35(e) Sequences of complex numbers with limit {lit}`0` form a subspace
of {lit}`ℂ^∞`. In Lean, "sequence" is {lit}`ℕ → ℂ` and "has limit {lit}`0`" is
{lit}`Filter.Tendsto f Filter.atTop (𝓝 0)`. -/

example : Subspace ℂ (ℕ → ℂ) where
  carrier := {f | Filter.Tendsto f Filter.atTop (nhds 0)}
  zero_mem' := tendsto_const_nhds
  add_mem' := by sorry
  smul_mem' := by sorry

/-! Two distinguished subspaces every space has: the trivial subspace {lit}`{0}`
({name}`Bot.bot`) and the whole space {name}`Top.top`. -/

example : Subspace F V := ⊥
example : Subspace F V := ⊤
example (v : V) : v ∈ (⊤ : Subspace F V) := Submodule.mem_top
example (v : V) : v ∈ (⊥ : Subspace F V) ↔ v = 0 := Submodule.mem_bot F

/-! 1.36 Definition: sum of subspaces

For subspaces {lit}`V₁, …, Vₘ` of {lit}`V`, the sum
{lit}`V₁ + ⋯ + Vₘ = {v₁ + ⋯ + vₘ : vₖ ∈ Vₖ}` is the set of all such sums.

For two subspaces, mathlib's lattice supremum {lit}`U ⊔ W` is exactly the sum,
and {lit}`U + W` resolves to the same thing via {name}`Submodule.add_eq_sup`. -/

example (U W : Subspace F V) : Subspace F V := U ⊔ W
example (U W : Subspace F V) : U + W = U ⊔ W := Submodule.add_eq_sup U W

/-! Membership in {lit}`U ⊔ W` is exactly the textbook formula. -/

example (U W : Subspace F V) (x : V) :
    x ∈ U ⊔ W ↔ ∃ y ∈ U, ∃ z ∈ W, y + z = x := Submodule.mem_sup

/-! Axler defines {lit}`V₁ + ⋯ + Vₘ` as a single n-ary operation. To make
sense of an iterated binary {lit}`⊔` we need the binary sum to be associative
and commutative — both inherit from {lit}`Subspace F V` being a lattice.
(These are also exercises 1C.16 and 1C.17 below.) -/

example (U W : Subspace F V) : U ⊔ W = W ⊔ U := sup_comm U W
example (V₁ V₂ V₃ : Subspace F V) : (V₁ ⊔ V₂) ⊔ V₃ = V₁ ⊔ (V₂ ⊔ V₃) :=
  sup_assoc V₁ V₂ V₃

/-! So {lit}`V₁ + V₂ + V₃` is unambiguous: the textbook formula
{lit}`{v₁ + v₂ + v₃ : vₖ ∈ Vₖ}` matches either bracketing. -/

example (V₁ V₂ V₃ : Subspace F V) (x : V) :
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

example (m : ℕ) (W : Fin m → Subspace F V) (x : V) :
    x ∈ ⨆ i, W i ↔ ∃ v : (i : Fin m) → W i, ∑ i, ((v i : V)) = x := by
  rw [show (⨆ i, W i) = ⨆ i ∈ (Finset.univ : Finset (Fin m)), W i by simp]
  rw [Submodule.mem_iSup_finset_iff_exists_sum]

/-! 1.37 Example: a sum of subspaces of {lit}`F³`

With {lit}`U = {(x, 0, 0) : x ∈ F}` and {lit}`W = {(0, y, 0) : y ∈ F}`,
{lit}`U + W = {(x, y, 0) : x, y ∈ F}`, i.e. the vectors whose third coordinate
is zero. -/

namespace Example_1_37

def U : Subspace F (Fin 3 → F) where
  carrier := {v | v 1 = 0 ∧ v 2 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

def W : Subspace F (Fin 3 → F) where
  carrier := {v | v 0 = 0 ∧ v 2 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

example : (U ⊔ W : Subspace F (Fin 3 → F)) =
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

def U : Subspace F (Fin 4 → F) where
  carrier := {v | v 0 = v 1 ∧ v 2 = v 3}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

def W : Subspace F (Fin 4 → F) where
  carrier := {v | v 0 = v 1 ∧ v 1 = v 2}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp [Pi.add_apply, h1, h3], by simp [Pi.add_apply, h2, h4]⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

example : (U ⊔ W : Subspace F (Fin 4 → F)) =
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
(i) The sum is itself a subspace — built into the type {lit}`U ⊔ W : Subspace F V`,
    which 1.34 (the {name}`Subspace` constructor) already supplied.
(ii) Each summand is contained in the sum: take {lit}`u = u + 0` and
    {lit}`w = 0 + w` (Axler's "consider sums where all except one are 0").
 -/
example (U W : Subspace F V) : U ≤ U ⊔ W :=
  fun u hu => Submodule.mem_sup.mpr ⟨u, hu, 0, W.zero_mem, add_zero u⟩
example (U W : Subspace F V) : W ≤ U ⊔ W :=
  fun w hw => Submodule.mem_sup.mpr ⟨0, U.zero_mem, w, hw, zero_add w⟩

/-! (iii) Any subspace containing both summands contains the sum, because subspaces
    are closed under addition. -/
example (U W X : Subspace F V) (h₁ : U ≤ X) (h₂ : W ≤ X) : U ⊔ W ≤ X := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  exact X.add_mem (h₁ hy) (h₂ hz)

/-! 1.41 Definition: direct sum, ⊕

The sum {lit}`V₁ + ⋯ + Vₘ` is a *direct sum* if each element has only one
representation as {lit}`v₁ + ⋯ + vₘ` with each {lit}`vₖ ∈ Vₖ`. -/

def IsDirectSum {m : ℕ} (W : Fin m → Subspace F V) : Prop :=
  ∀ (u v : (i : Fin m) → W i),
    (∑ i, ((u i : V))) = (∑ i, ((v i : V))) → u = v

/-! 1.42 Example: a direct sum of two subspaces -/

namespace Example_1_42

def U : Subspace F (Fin 3 → F) where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 2 + v 2 = 0; rw [hu, hv, add_zero]
  smul_mem' := by intro a v hv; show a • v 2 = 0; rw [hv, smul_zero]

def W : Subspace F (Fin 3 → F) where
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

example : (U : Subspace F (Fin 3 → F)) ⊔ W = ⊤ := by
  rw [eq_top_iff]
  intro v _
  refine Submodule.mem_sup.mpr ⟨![v 0, v 1, 0], rfl,
          ![0, 0, v 2], ⟨rfl, rfl⟩, ?_⟩
  funext i; fin_cases i <;> simp

end Example_1_42

/-! 1.43 Example: a direct sum of multiple subspaces -/

namespace Example_1_43

def Axis (n : ℕ) (k : Fin n) : Subspace F (Fin n → F) where
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

def V₁ : Subspace F (Fin 3 → F) where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 2 + v 2 = 0; rw [hu, hv, add_zero]
  smul_mem' := by intro a v hv; show a • v 2 = 0; rw [hv, smul_zero]

def V₂ : Subspace F (Fin 3 → F) where
  carrier := {v | v 0 = 0 ∧ v 1 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h0, h1⟩ ⟨h0', h1'⟩
    exact ⟨by simp [Pi.add_apply, h0, h0'], by simp [Pi.add_apply, h1, h1']⟩
  smul_mem' := by
    rintro a v ⟨h0, h1⟩
    exact ⟨by simp [Pi.smul_apply, h0], by simp [Pi.smul_apply, h1]⟩

def V₃ : Subspace F (Fin 3 → F) where
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
  let W : Fin 3 → Subspace F (Fin 3 → F) := ![V₁, V₂, V₃]
  have m₀ : (![0, 1, 0] : Fin 3 → F) ∈ W 0 := rfl
  have m₁ : (![0, 0, 1] : Fin 3 → F) ∈ W 1 := ⟨rfl, rfl⟩
  have m₂ : (![0, -1, -1] : Fin 3 → F) ∈ W 2 := ⟨rfl, rfl⟩
  let f : (i : Fin 3) → W i := fun i =>
    match i with
    | ⟨0, _⟩ => ⟨_, m₀⟩
    | ⟨1, _⟩ => ⟨_, m₁⟩
    | ⟨2, _⟩ => ⟨_, m₂⟩
  let g : (i : Fin 3) → W i := fun i =>
    ⟨(0 : Fin 3 → F), (W i).zero_mem⟩
  have hsum : (∑ i, ((f i : Fin 3 → F))) = (∑ i, ((g i : Fin 3 → F))) := by
    funext j
    fin_cases j <;> simp [f, g, W, Fin.sum_univ_three]
  have heq : f = g := h f g hsum
  -- f 0 = (0, 1, 0); reading coordinate 1 yields 1 = 0.
  have h1 : (f 0 : Fin 3 → F) 1 = (g 0 : Fin 3 → F) 1 := by rw [heq]
  simp [f, g] at h1

end Example_1_44

/-! 1.45 Condition for a direct sum -/

theorem isDirectSum_iff {m : ℕ} (W : Fin m → Subspace F V) :
    IsDirectSum W ↔ ∀ (u : (i : Fin m) → W i), (∑ i, ((u i : V))) = 0 ↔ u = 0 := by
  refine ⟨fun h u => ⟨fun hu => h u 0 (by simpa using hu), fun hu => by simp [hu]⟩, ?_⟩
  intro h u v huv
  have hzero : u - v = 0 := by
    apply (h _).mp
    simp only [Pi.sub_apply, AddSubgroupClass.coe_sub, Finset.sum_sub_distrib]
    rw [huv, sub_self]
  exact sub_eq_zero.mp hzero

/-! 1.46 Direct sum of two subspaces -/

theorem isDirectSum_pair_iff (U W : Subspace F V) :
    IsDirectSum (F := F) ![U, W] ↔ U ⊓ W = ⊥ := by
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

/-! # Exercises -/

/-- 1C.1(a) -/
def exercise_1C_1a :
    Decidable (∃ U : Subspace F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 0}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.1(b) -/
def exercise_1C_1b :
    Decidable (∃ U : Subspace F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 + 2 * v 1 + 3 * v 2 = 4}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.1(c) -/
def exercise_1C_1c :
    Decidable (∃ U : Subspace F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 * v 1 * v 2 = 0}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.1(d) -/
def exercise_1C_1d :
    Decidable (∃ U : Subspace F (Fin 3 → F),
      (U : Set (Fin 3 → F)) = {v | v 0 = 5 * v 2}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.3 Axler's ambient space is {lit}`ℝ^(-4, 4)`, i.e. the function space
{lit}`Set.Ioo (-4) 4 → ℝ`. We use the larger {lit}`ℝ → ℝ` instead because
mathlib's {name}`Differentiable` requires the source to be a normed space and
the subtype {lit}`↥(Set.Ioo (-4) 4)` isn't one. -/
theorem exercise_1C_3 :
    ∃ U : Subspace ℝ (ℝ → ℝ),
      (U : Set (ℝ → ℝ)) =
        {f | DifferentiableOn ℝ f (Set.Ioo (-4) 4) ∧ deriv f (-1) = 3 * f 2} := by
  sorry

/-- 1C.4 Axler's ambient space is {lit}`ℝ^[0,1]`, i.e. {lit}`Set.Icc 0 1 → ℝ`.
We use {lit}`ℝ → ℝ` instead so the integral reads as the familiar
{lit}`∫ x in (0)..1, f x` via {name}`intervalIntegral`; the faithful subtype
version would need measure theory. -/
theorem exercise_1C_4 (b : ℝ) :
    (∃ U : Subspace ℝ (ℝ → ℝ),
        (U : Set (ℝ → ℝ)) =
          {f | ContinuousOn f (Set.Icc 0 1) ∧ ∫ x in (0)..1, f x = b}) ↔ b = 0 := by
  sorry

/-- 1C.5 -/
def exercise_1C_5 :
    Decidable (∃ U : Subspace ℂ (Fin 2 → ℂ),
      (U : Set (Fin 2 → ℂ)) = {v | ∀ i, (v i).im = 0}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.6(a) -/
def exercise_1C_6a :
    Decidable (∃ U : Subspace ℝ (Fin 3 → ℝ),
      (U : Set (Fin 3 → ℝ)) = {v | v 0 ^ 3 = v 1 ^ 3}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.6(b) -/
def exercise_1C_6b :
    Decidable (∃ U : Subspace ℂ (Fin 3 → ℂ),
      (U : Set (Fin 3 → ℂ)) = {v | v 0 ^ 3 = v 1 ^ 3}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.7 -/
def exercise_1C_7 :
    Decidable (∀ U : Set (Fin 2 → ℝ),
      U.Nonempty →
      (∀ u ∈ U, ∀ v ∈ U, u + v ∈ U) →
      (∀ u ∈ U, -u ∈ U) →
      ∃ S : Subspace ℝ (Fin 2 → ℝ), (S : Set (Fin 2 → ℝ)) = U) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.8 -/
theorem exercise_1C_8 :
    ∃ U : Set (Fin 2 → ℝ),
      U.Nonempty ∧
      (∀ (a : ℝ) (u), u ∈ U → a • u ∈ U) ∧
      ¬ ∃ S : Subspace ℝ (Fin 2 → ℝ), (S : Set (Fin 2 → ℝ)) = U := by
  sorry

def Periodic (f : ℝ → ℝ) : Prop := ∃ p > 0, ∀ x, f x = f (x + p)

/-- 1C.9 -/
def exercise_1C_9 :
    Decidable (∃ U : Subspace ℝ (ℝ → ℝ), (U : Set (ℝ → ℝ)) = {f | Periodic f}) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.10 The intersection of two subspaces is a subspace. The student must
build a {name}`Subspace` whose carrier is {lit}`(U : Set V) ∩ (W : Set V)`,
i.e. prove the three closure axioms hold for the intersection. (In mathlib
this subspace is the lattice infimum {lit}`U ⊓ W`, which the
{name}`SemilatticeInf` instance on {name}`Subspace` produces automatically;
the exercise is to do that construction by hand.) -/
theorem exercise_1C_10 (U W : Subspace F V) :
    ∃ S : Subspace F V, (S : Set V) = (U : Set V) ∩ (W : Set V) := by
  sorry

/-- 1C.11 The intersection of *any* collection of subspaces of {lit}`V` is a
subspace. The student must build a {name}`Subspace` whose carrier is the
intersection {lit}`⋂ U ∈ 𝒞, (U : Set V)`, i.e. prove the three closure axioms
hold for an arbitrary intersection. (In mathlib this subspace is the lattice
infimum {name}`sInf` (or {name}`iInf` for an indexed family), which the
{name}`CompleteLattice` instance on {name}`Subspace` produces automatically;
the exercise is to do that construction by hand.) -/
theorem exercise_1C_11 (𝒞 : Set (Subspace F V)) :
    ∃ S : Subspace F V, (S : Set V) = ⋂ U ∈ 𝒞, (U : Set V) := by
  sorry

/-- 1C.12 -/
@[avoiding Submodule.union_eq_iff_le_or_le]
theorem exercise_1C_12 (U W : Subspace F V) :
    (∃ S : Subspace F V, (S : Set V) = (U : Set V) ∪ (W : Set V)) ↔
      U ≤ W ∨ W ≤ U := by
  sorry

/-- 1C.13 To prove this we need a scalar in {lit}`F` other than {lit}`0` and
{lit}`1`; we assume {lit}`[CharZero F]`, which forces {lit}`(n : F) ≠ 0` for
every positive {lit}`n` and is satisfied by {lit}`ℝ` and {lit}`ℂ` (Axler's working fields). -/
theorem exercise_1C_13 [CharZero F] (U W X : Subspace F V) :
    (∃ S : Subspace F V, (S : Set V) = (U : Set V) ∪ W ∪ X) ↔
      (W ≤ U ∧ X ≤ U) ∨ (U ≤ W ∧ X ≤ W) ∨ (U ≤ X ∧ W ≤ X) := by
  sorry

-- The `<;> ring` finishes the branches that `simp` doesn't close on its own,
-- so the linter's `(simp; ring)` suggestion would fail with "no goals".
/-- 1C.14 The student fills in the predicate (replacing the {lit}`sorry` in
the right-hand side) and proves the equality. -/
def exercise_1C_14_U : Subspace F (Fin 3 → F) where
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

def exercise_1C_14_W : Subspace F (Fin 3 → F) where
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

theorem exercise_1C_14 :
    ((exercise_1C_14_U (F := F) ⊔ exercise_1C_14_W : Subspace F (Fin 3 → F))
      : Set (Fin 3 → F)) = {v | sorry} := by
  sorry

/-- 1C.15 -/
@[avoiding sup_idem, sup_self]
theorem exercise_1C_15 (U : Subspace F V) : U ⊔ U = sorry := by
  sorry

/-- 1C.16 -/
@[avoiding sup_comm]
def exercise_1C_16 :
    Decidable (∀ U W : Subspace F V, U ⊔ W = W ⊔ U) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.17 -/
@[avoiding sup_assoc]
def exercise_1C_17 :
    Decidable (∀ V₁ V₂ V₃ : Subspace F V, (V₁ ⊔ V₂) ⊔ V₃ = V₁ ⊔ (V₂ ⊔ V₃)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.18(a) -/
@[avoiding bot_sup_eq, sup_bot_eq]
def exercise_1C_18_id :
    Decidable (∃ E : Subspace F V, ∀ U : Subspace F V, U ⊔ E = U) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.18(b) *Which subspaces have an additive inverse under sum?* (i.e., for
which {lit}`U` does there exist {lit}`W` with {lit}`U + W = ⊥`?) Fill in the
right-hand side {lit}`sorry` with the conjectured characterization
of {lit}`U`, and then then proves the equivalence. -/
theorem exercise_1C_18_inv (U : Subspace F V) :
    (∃ W : Subspace F V, U ⊔ W = ⊥) ↔ sorry := by
  sorry

/-- 1C.19 -/
def exercise_1C_19 :
    Decidable (∀ V₁ V₂ U : Subspace ℝ (Fin 2 → ℝ),
      V₁ ⊔ U = V₂ ⊔ U → V₁ = V₂) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.20 -/
def exercise_1C_20_U : Subspace F (Fin 4 → F) where
  carrier := {v | v 0 = v 1 ∧ v 2 = v 3}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by simp [Pi.add_apply, h1, h1'], by simp [Pi.add_apply, h2, h2']⟩
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    exact ⟨by simp [Pi.smul_apply, h1], by simp [Pi.smul_apply, h2]⟩

theorem exercise_1C_20 :
    ∃ W : Subspace F (Fin 4 → F), IsCompl (exercise_1C_20_U (F := F)) W := by
  sorry

/-- 1C.21 -/
def exercise_1C_21_U : Subspace F (Fin 5 → F) where
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

theorem exercise_1C_21 :
    ∃ W : Subspace F (Fin 5 → F), IsCompl (exercise_1C_21_U (F := F)) W := by
  sorry

/-- 1C.22 The direct-sum condition is captured by {name}`IsDirectSum` on the
family {lit}`![U, W₁, W₂, W₃]`; the cover by {lit}`U ⊔ W₁ ⊔ W₂ ⊔ W₃ = ⊤`. -/
theorem exercise_1C_22 :
    ∃ W₁ W₂ W₃ : Subspace F (Fin 5 → F),
      W₁ ≠ ⊥ ∧ W₂ ≠ ⊥ ∧ W₃ ≠ ⊥ ∧
      IsDirectSum ![exercise_1C_21_U (F := F), W₁, W₂, W₃] ∧
      exercise_1C_21_U (F := F) ⊔ W₁ ⊔ W₂ ⊔ W₃ = ⊤ := by
  sorry

/-- 1C.23 -/
def exercise_1C_23 :
    Decidable (∀ V₁ V₂ U : Subspace ℝ (Fin 2 → ℝ),
      IsCompl V₁ U → IsCompl V₂ U → V₁ = V₂) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 1C.24 -/

def IsEven (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = f x
def IsOdd  (f : ℝ → ℝ) : Prop := ∀ x, f (-x) = -f x

def evenFunctions : Subspace ℝ (ℝ → ℝ) where
  carrier := {f | IsEven f}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

def oddFunctions : Subspace ℝ (ℝ → ℝ) where
  carrier := {f | IsOdd f}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

theorem exercise_1C_24 : IsCompl evenFunctions oddFunctions := by
  sorry

end LADR.Section_1C
