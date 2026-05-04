import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.MinimalAxioms
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

/-! 1.19 Definition: addition, scalar multiplication -/
example (V : Type*) (add : V → V → V) : Add V := ⟨add⟩
example (F V : Type*) (smul : F → V → V) : SMul F V := ⟨smul⟩

/-! 1.20 Definition: vector space

Mathlib splits Axler's eight axioms across two typeclasses:

* the first four (commutativity, associativity, additive identity, additive
  inverse) say that {lit}`+{lit}` makes {lit}`V{lit}` an {name}`AddCommGroup`;
* the remaining four (associativity of {lit}`•{lit}`, the multiplicative
  identity, and the two distributivity laws) say that {lit}`•{lit}` makes
  {lit}`V{lit}` a {name}`Module` over {lit}`F{lit}`. -/

example (V : Type*) [Add V] [Neg V] [Zero V]
    /- Commutativity -/
    (add_comm : ∀ u v : V, u + v = v + u)
    /- Additive associativity -/
    (add_assoc : ∀ u v w : V, (u + v) + w = u + (v + w))
    /- Additive identity -/
    (add_zero : ∀ v : V, v + 0 = v)
    /- Additive inverse -/
    (add_neg_cancel : ∀ v : V, v + -v = 0) : AddCommGroup V :=
  { AddGroup.ofRightAxioms add_assoc add_zero add_neg_cancel with add_comm := add_comm }

example (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [SMul F V]
    /- Multiplicative associativity -/
    (mul_smul : ∀ (a b : F) (v : V), (a * b) • v = a • (b • v))
    /- Multiplicative identity -/
    (one_smul : ∀ v : V, (1 : F) • v = v)
    /- Distributive properties -/
    (smul_add : ∀ (a : F) (u v : V), a • (u + v) = a • u + a • v)
    (add_smul : ∀ (a b : F) (v : V), (a + b) • v = a • v + b • v) : Module F V :=
  Module.ofMinimalAxioms smul_add add_smul mul_smul one_smul

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/- Commutativity -/
example (u v : V) : u + v = v + u := add_comm u v
/- Associativity (addition) -/
example (u v w : V) : (u + v) + w = u + (v + w) := add_assoc u v w
/- Associativity (scalar multiplication) -/
example (a b : F) (v : V) : (a * b) • v = a • b • v := mul_smul a b v
/- Additive identity -/
example (v : V) : v + 0 = v := add_zero v
/- Additive inverse -/
example (v : V) : v + -v = 0 := add_neg_cancel v
/- Multiplicative identity -/
example (v : V) : (1 : F) • v = v := one_smul F v
/- Distributive properties -/
example (a : F) (u v : V) : a • (u + v) = a • u + a • v := smul_add a u v
example (a b : F) (v : V) : (a + b) • v = a • v + b • v := add_smul a b v

/-! 1.21 Definition: vector, point

Elements {lit}`v : V` are called vectors or points. -/

/-! 1.22 Definition: real vector space, complex vector space

A real vector space is a pair {lit}`[AddCommGroup V] [Module ℝ V]{lit}`.
A complex vector space is a pair {lit}`[AddCommGroup V] [Module ℂ V]{lit}`. -/
private class abbrev RealVectorSpace (V : Type*) := AddCommGroup V, Module ℝ V
private class abbrev ComplexVectorSpace (V : Type*) := AddCommGroup V, Module ℂ V

/-! The simplest vector space is the one-element space {lit}`{0}`. In Lean this is {lit}`PUnit`. -/
example : Module F PUnit := inferInstance
example (v : PUnit) : v = 0 := rfl

/-! 1.23 Example: F∞

{lit}`F∞{lit}` is the set of all sequences of elements of {lit}`F{lit}`; in Lean,
{lit}`ℕ → F{lit}`. Addition and scalar multiplication are defined coordinate-wise: -/

/- Coordinate-wise addition and multiplication on F∞ -/
example : Add (ℕ → F) := ⟨fun f g i ↦ f i + g i⟩
example (f g : ℕ → ℝ) (i : ℕ) : (f + g) i = f i + g i := rfl
example : SMul F (ℕ → F) := ⟨fun c f i ↦ c * f i⟩
example (c : ℝ) (f : ℕ → ℝ) (i : ℕ) : (c • f) i = c * f i := rfl

example : AddCommGroup (ℕ → F) := inferInstance
example : Module F (ℕ → F) := inferInstance
/- Additive identity is the sequence of all 0's -/
example : (0 : ℕ → F) = fun _ ↦ 0 := rfl

/-! 1.24 Notation: F^S -/
variable (S : Type*)
example : Add (S → F) := ⟨fun f g i ↦ f i + g i⟩
example (f g : S → F) (x : S) : (f + g) x = f x + g x := rfl
example : SMul F (S → F) := ⟨fun c f i ↦ c * f i⟩
example (c : F) (f : S → F) (x : S) : (c • f) x = c * f x := rfl

/-! 1.25 Example: F^S is a vector space -/
example : AddCommGroup (S → F) := inferInstance
example : Module F (S → F) := inferInstance
/- Additive identity is indentically zero -/
example (x : S) : (0 : S → F) x = 0 := rfl
/- Additive inverse is defined coordinate-wise -/
example (f : S → F) (x : S) : (-f) x = -(f x) := rfl

/-! 1.26 Unique additive identity -/
theorem unique_zero : ∃! z : V, ∀ v, v + z = v := ⟨0, fun v ↦ add_zero v, by
  intro z h
  calc z = z + 0 := (add_zero z).symm
    _    = 0 + z := add_comm z 0
    _    = 0     := h 0⟩

/-! 1.27 Unique additive inverse -/
theorem unique_neg (v : V) : ∃! w : V, w + v = 0 := ⟨-v, neg_add_cancel v, by
  intro w h
  calc w = w + 0           := (add_zero w).symm
    _    = w + (v + (-v))  := by rw [add_neg_cancel]
    _    = (w + v) + (-v)  := (add_assoc w v (-v)).symm
    _    = 0 + (-v)        := by rw [h]
    _    = -v              := zero_add (-v)⟩

/-! 1.28 Notation: −v, w − v -/
example (v w : V) : w - v = w + (-v) := sub_eq_add_neg w v

/-! 1.29 Notation: V

For the rest of this section, {lit}`V{lit}` denotes a vector space over {lit}`F` (declared
once at the top via {lit}`variable {V : Type*} [AddCommGroup V] [Module F V]`). -/

/-! 1.30 The number 0 times a vector -/
@[avoiding zero_smul]
theorem zero_smul' (v : V) : (0 : F) • v = 0 := by
  -- Axler 1.30: 0v = (0 + 0)v = 0v + 0v.
  have h : (0 : F) • v = (0 : F) • v + (0 : F) • v :=
    calc (0 : F) • v
        = (0 + 0 : F) • v             := by rw [add_zero]
      _ = (0 : F) • v + (0 : F) • v   := add_smul 0 0 v
  -- Adding -(0v) to both sides of h and simplifying gives 0v = 0.
  calc (0 : F) • v
      = (0 : F) • v + 0                                := (add_zero _).symm
    _ = (0 : F) • v + ((0 : F) • v + -((0 : F) • v))   := by rw [add_neg_cancel]
    _ = ((0 : F) • v + (0 : F) • v) + -((0 : F) • v)   := (add_assoc _ _ _).symm
    _ = (0 : F) • v + -((0 : F) • v)                   := by rw [← h]
    _ = 0                                              := add_neg_cancel _

/-! 1.31 A number times the vector 0 -/

@[avoiding smul_zero]
theorem smul_zero' (a : F) : a • (0 : V) = 0 := by
  -- Axler 1.31 (parallel to 1.30): a·0 = a·(0 + 0) = a·0 + a·0.
  have h : a • (0 : V) = a • 0 + a • 0 :=
    calc a • (0 : V)
        = a • (0 + 0)        := by rw [add_zero]
      _ = a • 0 + a • 0      := smul_add a 0 0
  -- Adding -(a·0) to both sides of h and simplifying gives a·0 = 0.
  calc a • (0 : V)
      = a • 0 + 0                          := (add_zero _).symm
    _ = a • 0 + (a • 0 + -(a • 0))         := by rw [add_neg_cancel]
    _ = (a • 0 + a • 0) + -(a • 0)         := (add_assoc _ _ _).symm
    _ = a • 0 + -(a • 0)                   := by rw [← h]
    _ = 0                                  := add_neg_cancel _

/-! 1.32 The number −1 times a vector -/

@[avoiding neg_one_smul]
theorem neg_one_smul' (v : V) : (-1 : F) • v = -v := by
  -- Axler 1.32: v + (-1)v = 1v + (-1)v = (1 + (-1))v = 0v = 0.
  have h : v + (-1 : F) • v = 0 :=
    calc v + (-1 : F) • v
        = (1 : F) • v + (-1 : F) • v    := by rw [one_smul]
      _ = ((1 : F) + (-1 : F)) • v      := (add_smul 1 (-1) v).symm
      _ = (0 : F) • v                   := by rw [show (1 : F) + (-1 : F) = 0 by ring]
      _ = 0                             := zero_smul' v
  -- So (-1)v is an additive inverse of v; by uniqueness (Axler 1.27), (-1)v = -v.
  exact (unique_neg v).unique ((add_comm _ _).trans h) (neg_add_cancel v)

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

/-- 1B.3 -/
theorem exercise_1B_3 (v w : V) : ∃! x : V, v + (3 : F) • x = w := by
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
  For this exericise, instead of redefiniting extended reals we will use
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
@[implicit_reducible]
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
