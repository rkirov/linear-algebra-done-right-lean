import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.PUnit
import Mathlib.Data.Complex.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 1B: Definition of Vector Space
-/

namespace LADR.Section_1B

/-! 1.19–1.20 Definition: addition, scalar multiplication; vector space -/

structure LADRVectorSpace (F : Type*) [Field F] (V : Type*) where
  /-- Definition 1.19: addition -/
  add : V → V → V
  /-- Definition 1.19: scalar multiplication -/
  smul : F → V → V

  /-- Definition 1.20: commutativity -/
  add_comm : ∀ u v, add u v = add v u
  /-- Definition 1.20: associativity (addition) -/
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  /-- Definition 1.20: associativity (scalar multiplication) -/
  mul_smul : ∀ a b v, smul (a * b) v = smul a (smul b v)
  /-- Definition 1.20: additive identity -/
  zero : V
  add_zero : ∀ v, add v zero = v
  /-- Definition 1.20: additive inverse -/
  neg : V → V
  add_neg_cancel : ∀ v, add v (neg v) = zero
  /-- Definition 1.20: multiplicative identity -/
  one_smul : ∀ v, smul (1 : F) v = v
  /-- Definition 1.20: distributive properties -/
  smul_add : ∀ a u v, smul a (add u v) = add (smul a u) (smul a v)
  add_smul : ∀ a b v, smul (a + b) v = add (smul a v) (smul b v)

/-! Instead of using the definition above, we will use mathlib's definition.

As usual, mathlib has a more general definition, but the special case of
{lit}`Module F V` (over {lit}`[AddCommGroup V]`) where {lit}`[Field F]` is exactly
equivalent to Axler's "vector space over {lit}`F`". -/

/-! You will learn what these mean in an abstract algebra course, but
for now, just treat them as a magic incantation that gives us the properties
of vector spaces over a field F that behaves like ℝ and ℂ -/
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! The eight axioms above are derivable from the typeclass methods and
we get to use a nicer notation. -/
recall add_comm {G : Type*} [AddCommMagma G] (a b : G) : a + b = b + a
recall add_assoc {G : Type*} [AddSemigroup G] (a b c : G) : a + b + c = a + (b + c)
recall add_zero {M : Type*} [AddZeroClass M] (a : M) : a + 0 = a
recall add_neg_cancel {G : Type*} [AddGroup G] (a : G) : a + -a = 0
recall one_smul (M : Type*) {α : Type*} [Monoid M] [MulAction M α] (b : α) : (1 : M) • b = b
recall smul_add {M : Type*} {A : Type*} [AddZeroClass A] [DistribSMul M A]
    (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
recall add_smul {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (r s : R) (x : M) : (r + s) • x = r • x + s • x
recall mul_smul {α : Type*} {β : Type*} [Semigroup α] [SemigroupAction α β]
    (x y : α) (b : β) : (x * y) • b = x • y • b

/-! 1.21 Definition: vector, point

Elements {lit}`v : V` are called vectors or points. -/

/-! 1.22 Definition: real vector space, complex vector space

A vector space over {lit}`ℝ` is a real vector space; over {lit}`ℂ`, a complex vector space.
In Lean, whenever we see {lit}`{V : Type*} [AddCommGroup V] [Module ℝ V]`, that is a
real vector space; with {lit}`[Module ℂ V]`, a complex vector space. -/


/-! 1.23 Example: F∞

{lit}`F∞` is the set of all sequences of elements of {lit}`F`; in Lean, {lit}`ℕ → F`. -/

example : AddCommGroup (ℕ → F) := inferInstance
example : Module F (ℕ → F) := inferInstance

example (f g : ℕ → ℝ) (i : ℕ) : (f + g) i = f i + g i := rfl
example (c : ℝ) (f : ℕ → ℝ) (i : ℕ) : (c • f) i = c * f i := rfl

/-! The simplest vector space is the one-element space {lit}`{0}`. In Lean this is
{lit}`PUnit`; mathlib provides the instances automatically. -/

example (F : Type*) [Field F] : Module F PUnit := inferInstance
example (v w : PUnit) : v = w := rfl

/-! 1.24 Notation: F^S

For a set {lit}`S`, {lit}`F^S` denotes the set of functions from {lit}`S` to {lit}`F`. In Lean we
just write {lit}`S → F`. Addition and scalar multiplication are pointwise. -/

example (S : Type*) (f g : S → F) (x : S) : (f + g) x = f x + g x := rfl
example (S : Type*) (c : F) (f : S → F) (x : S) : (c • f) x = c * f x := rfl

/-! 1.25 Example: F^S is a vector space

The additive identity of {lit}`F^S` is the function {lit}`0 : S → F` defined by
{lit}`0 x = 0` for all {lit}`x ∈ S`. For {lit}`f : S → F`, the additive inverse {lit}`-f`
is defined by {lit}`(-f) x = -(f x)` for all {lit}`x ∈ S`. -/

example (S : Type*) : AddCommGroup (S → F) := inferInstance
example (S : Type*) : Module F (S → F) := inferInstance

example (S : Type*) (x : S) : (0 : S → F) x = 0 := rfl
example (S : Type*) (f : S → F) (x : S) : (-f) x = -(f x) := rfl

/-! 1.26 Unique additive identity -/

theorem unique_zero (z : V) (h : ∀ v, v + z = v) : z = 0 :=
  calc z = z + 0     := (add_zero z).symm
    _    = 0 + z     := add_comm z 0
    _    = 0         := h 0

/-! 1.27 Unique additive inverse -/

theorem unique_neg (v w : V) (h : v + w = 0) : w = -v :=
  calc w = w + 0                 := (add_zero w).symm
    _    = w + (v + (-v))        := by rw [add_neg_cancel]
    _    = (w + v) + (-v)        := (add_assoc w v (-v)).symm
    _    = (v + w) + (-v)        := by rw [add_comm w v]
    _    = 0 + (-v)              := by rw [h]
    _    = -v                    := zero_add (-v)

/-! 1.28 Notation: −v, w − v -/

example (v : V) : v + (-v) = 0 := add_neg_cancel v
example (v w : V) : w - v = w + (-v) := sub_eq_add_neg w v

/-! 1.29 Notation: V

For the rest of this section, {lit}`V` denotes a vector space over {lit}`F` (declared
once at the top via {lit}`variable {V : Type*} [AddCommGroup V] [Module F V]`). -/

/-! 1.30 The number 0 times a vector -/

@[avoiding zero_smul]
theorem zero_smul' (v : V) : (0 : F) • v = 0 := by
  have h : (0 : F) • v = (0 : F) • v + (0 : F) • v :=
    calc (0 : F) • v = (0 + 0 : F) • v          := by rw [add_zero]
      _              = (0 : F) • v + (0 : F) • v := add_smul 0 0 v
  -- Add {lit}`-(0 • v)` to both sides of {lit}`h`, then simplify.
  have h2 : (0 : F) • v + -((0 : F) • v) = ((0 : F) • v + (0 : F) • v) + -((0 : F) • v) :=
    congrArg (· + -((0 : F) • v)) h
  rw [add_neg_cancel, add_assoc, add_neg_cancel, add_zero] at h2
  exact h2.symm

/-! 1.31 A number times the vector 0 -/

@[avoiding smul_zero]
theorem smul_zero' (a : F) : a • (0 : V) = 0 := by
  have h : a • (0 : V) = a • 0 + a • 0 :=
    calc a • (0 : V) = a • (0 + 0)         := by rw [add_zero]
      _              = a • 0 + a • 0       := smul_add a 0 0
  -- Add {lit}`-(a • 0)` to both sides of {lit}`h`, then simplify.
  have h2 : a • (0 : V) + -(a • (0 : V)) = (a • 0 + a • 0) + -(a • 0) :=
    congrArg (· + -(a • (0 : V))) h
  rw [add_neg_cancel, add_assoc, add_neg_cancel, add_zero] at h2
  exact h2.symm

/-! 1.32 The number −1 times a vector -/

@[avoiding neg_one_smul]
theorem neg_one_smul' (v : V) : (-1 : F) • v = -v :=
  unique_neg v ((-1 : F) • v) <|
    calc v + (-1 : F) • v
        = (1 : F) • v + (-1 : F) • v   := by rw [one_smul]
      _ = ((1 : F) + (-1 : F)) • v      := (add_smul 1 (-1) v).symm
      _ = (0 : F) • v                   := by rw [show (1 : F) + -1 = 0 from by ring]
      _ = 0                             := zero_smul' v

/-! # Exercises -/

/-- 1B.1 -/
@[avoiding neg_neg]
theorem exercise_1B_1 (v : V) : -(-v) = v := by
  sorry

/-- 1B.2 -/
@[avoiding smul_eq_zero, smul_eq_zero_iff_eq, smul_eq_zero_iff_eq']
theorem exercise_1B_2 (a : F) (v : V) (h : a • v = 0) :
    a = 0 ∨ v = 0 := by
  sorry

/-- 1B.3 The unique {lit}`x` is {lit}`(1/3) • (w - v)`, which requires
{lit}`(3 : F)` to be invertible. We assume {lit}`[CharZero F]`, which forces
{lit}`(n : F) ≠ 0` for every positive {lit}`n` and is satisfied by {lit}`ℝ` and
{lit}`ℂ` (Axler's working fields). -/
theorem exercise_1B_3 [CharZero F] (v w : V) : ∃! x : V, v + (3 : F) • x = w := by
  sorry

/-- 1B.4: We show the failure in the {lit}`AddCommGroup` subcomponent —
the failing axiom lives in the additive structure. -/
theorem exercise_1B_4 : IsEmpty (AddCommGroup Empty) := by
  sorry

/-- The textbook's *alternative* module-side axioms (1B.5): the four standard
smul axioms with {lit}`add_neg_cancel` replaced by {lit}`0 • v = 0`. The
additive part lives in the surrounding {lit}`AddCommMonoid V`. -/
structure AxlerAltModule (F V : Type*) [Field F] [AddCommMonoid V] where
  smul : F → V → V
  one_smul : ∀ v : V, smul 1 v = v
  mul_smul : ∀ (a b : F) (v : V), smul (a * b) v = smul a (smul b v)
  smul_add : ∀ (a : F) (u v : V), smul a (u + v) = smul a u + smul a v
  add_smul : ∀ (a b : F) (v : V), smul (a + b) v = smul a v + smul b v
  zero_smul : ∀ v : V, smul 0 v = 0

/-- 1B.5, ⇐ direction (original ⇒ alt): from {lit}`add_neg_cancel` and the four
standard smul axioms, derive {lit}`0 • v = 0`. This is theorem 1.30 above. -/
example (v : V) : (0 : F) • v = 0 := zero_smul' v

/-- 1B.5, ⇒ direction (alt ⇒ original): given the alt axioms over an
{lit}`AddCommMonoid`, the dropped axiom — additive inverses — must hold. -/
theorem exercise_1B_5 (V : Type*) [AddCommMonoid V] (m : AxlerAltModule F V) :
    ∀ v : V, ∃ w : V, v + w = 0 := by
  sorry

/-! 1B.6
  For this exercise, instead of a custom extended reals definition we will use
  mathlib's {name}`EReal` type, which is `ℝ ∪ {∞, -∞}`.
  In mathlib {lit}`⊤ = ∞` and {lit}`⊥ = -∞`

  However, mathlib's {name}`EReal` addition is not the same as Axler's it
  has {lit}`⊤ + ⊥ = ⊥`, but Axler's convention is {lit}`∞ + (-∞) = 0`.

  So we define a new addition {lit}`addAxler` that agrees with Axler's convention.
-/
noncomputable def addAxler (x y : EReal) : EReal :=
  if (x = ⊤ ∧ y = ⊥) ∨ (x = ⊥ ∧ y = ⊤) then 0 else x + y

/-- with the textbook's operations, {lit}`EReal` is not a vector space
over {lit}`ℝ`. The failure is in the additive structure (associativity fails
for {lit}`addAxler`), so we refute the existence of any {lit}`AddCommGroup`
structure on {lit}`EReal` whose addition is {lit}`addAxler`.

Note: mathlib cannot not provide an {lit}`AddGroup EReal` instance either —
{lit}`EReal` even with its addition definition. -/
theorem exercise_1B_6 : ¬ ∃ g : AddCommGroup EReal, g.add = addAxler := by
  sorry

/-- 1B.7: {lit}`V^S = (S → V)` is a vector space with pointwise operations. We
pick the {lit}`Module F` subcomponent — the {lit}`AddCommGroup` part comes for free
from Pi instances; the reader fills in the scalar-action axioms. -/
@[implicit_reducible,
  avoiding
    Pi.smulZeroClass, Pi.addZeroClass, Pi.distribSMul,
    Pi.Function.module, Pi.instZero, Pi.mulAction
]
def exercise_1B_7 (S : Type*) [Nonempty S] : Module F (S → V) where
  smul a f := fun s => a • f s
  one_smul := by sorry
  mul_smul := by sorry
  smul_zero := by sorry
  zero_smul := by sorry
  smul_add := by sorry
  add_smul := by sorry

/-- The complexification {lit}`V_C = V × V` of a real vector space {lit}`V`. An
element {lit}`(u, v)` is written {lit}`u + i·v` in the textbook. The underlying
additive structure is just the product (mathlib provides it via Pi); the
content of 1B.8 is the *complex* scalar multiplication. -/
abbrev Complexification (W : Type*) := W × W

/-- 1B.8: with the textbook's complex scalar multiplication, the complexification
of a real vector space is a complex vector space. We pick the {lit}`Module ℂ`
subcomponent — the {lit}`AddCommGroup` part comes for free from the product
{lit}`W × W`; the new content is the complex scalar action. -/
@[implicit_reducible]
def exercise_1B_8 (W : Type*) [AddCommGroup W] [Module ℝ W] :
    Module ℂ (Complexification W) where
  smul c x := (c.re • x.1 - c.im • x.2, c.re • x.2 + c.im • x.1)
  one_smul := by sorry
  mul_smul := by sorry
  smul_zero := by sorry
  zero_smul := by sorry
  smul_add := by sorry
  add_smul := by sorry

/-! # Appendix: Axler's prescribed operations on {name}`EReal`

Axler 1B.6 prescribes specific values for {lit}`t · ∞`, {lit}`t · (-∞)`, and the
additive cases involving {lit}`±∞`. Mathlib's existing {name}`EReal` operations
match each of Axler's values *except* for {lit}`∞ + (-∞)` and {lit}`(-∞) + ∞`,
which is exactly what {lit}`addAxler` patches. For scalar multiplication we use
mathlib's {name}`EReal` multiplication via the coercion:
{lit}`t • x := (t : EReal) * x`. -/

/-! Axler's scalar action on {lit}`⊤ = ∞`. -/

theorem axler_smul_top_pos {t : ℝ} (h : 0 < t) : (t : EReal) * ⊤ = ⊤ :=
  EReal.mul_top_of_pos (EReal.coe_pos.mpr h)

theorem axler_smul_top_zero : ((0 : ℝ) : EReal) * ⊤ = 0 := by simp

theorem axler_smul_top_neg {t : ℝ} (h : t < 0) : (t : EReal) * ⊤ = ⊥ :=
  EReal.mul_top_of_neg (EReal.coe_neg'.mpr h)

/-! Axler's scalar action on {lit}`⊥ = -∞`. -/

theorem axler_smul_bot_pos {t : ℝ} (h : 0 < t) : (t : EReal) * ⊥ = ⊥ :=
  EReal.mul_bot_of_pos (EReal.coe_pos.mpr h)

theorem axler_smul_bot_zero : ((0 : ℝ) : EReal) * ⊥ = 0 := by simp

theorem axler_smul_bot_neg {t : ℝ} (h : t < 0) : (t : EReal) * ⊥ = ⊤ :=
  EReal.mul_bot_of_neg (EReal.coe_neg'.mpr h)

/-! Axler's additive cases that *do* match mathlib's {lit}`+`. -/

theorem axler_add_top (t : ℝ) : (t : EReal) + ⊤ = ⊤ := EReal.coe_add_top t
theorem axler_top_add (t : ℝ) : ⊤ + (t : EReal) = ⊤ := by rw [add_comm]; exact EReal.coe_add_top t
theorem axler_top_add_top : (⊤ : EReal) + ⊤ = ⊤ := by simp

theorem axler_add_bot (t : ℝ) : (t : EReal) + ⊥ = ⊥ := by simp
theorem axler_bot_add (t : ℝ) : ⊥ + (t : EReal) = ⊥ := EReal.bot_add t
theorem axler_bot_add_bot : (⊥ : EReal) + ⊥ = ⊥ := by simp

/-! Axler's two non-mathlib additive cases — these are exactly what
{lit}`addAxler` overrides, so we state them about {lit}`addAxler`, not {lit}`+`. -/

theorem axler_top_add_bot : addAxler ⊤ ⊥ = 0 := by unfold addAxler; simp
theorem axler_bot_add_top : addAxler ⊥ ⊤ = 0 := by unfold addAxler; simp

end LADR.Section_1B
