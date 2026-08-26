import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_1B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 2B: Bases
-/

namespace LADR.Section_2B

open LADR.Section_2A (Spans)

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

/-! 2.26 Definition: basis

A *basis* of {lit}`V` is a list of vectors in {lit}`V` that is linearly
independent and spans {lit}`V`. -/

def IsBasis (F : Type*) {V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {m : ℕ} (v : Fin m → V) : Prop :=
  LinearIndependent F v ∧ Spans F v

/-! Bridge to mathlib's bundled {name}`Module.Basis`. The book's {name}`IsBasis`
is a {lit}`Prop` mirroring Axler 2.26 ("linearly independent and spans");
mathlib's {name}`Module.Basis` is the structured datum carrying
{lit}`b.constr`, {lit}`b.repr`, etc. Chapter 3 (e.g. the linear map lemma 3.4)
needs that structure, so we expose a one-liner conversion. -/
noncomputable def IsBasis.toModuleBasis {m : ℕ} {v : Fin m → V}
    (hv : IsBasis F v) : Module.Basis (Fin m) F V :=
  Module.Basis.mk hv.1 (by rw [← hv.2])

@[simp] theorem IsBasis.toModuleBasis_apply {m : ℕ} {v : Fin m → V}
    (hv : IsBasis F v) (k : Fin m) : hv.toModuleBasis k = v k := by
  simp [IsBasis.toModuleBasis]

/-! 2.27 Example: bases -/

/-! (a) The standard basis of {lit}`Fⁿ`:
{lit}`(1, 0, …, 0), (0, 1, …, 0), …, (0, …, 0, 1)`. -/

theorem isBasis_stdBasis (n : ℕ) :
    IsBasis F (fun k : Fin n => (Pi.single k 1 : Fin n → F)) := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro a ha j
    have hj := congrFun ha j
    simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply] at hj
    rw [Finset.sum_eq_single j] at hj
    · simpa using hj
    · intros i _ hij
      rw [if_neg (fun h => hij h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [Spans, eq_top_iff]
    intro v _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨v, ?_⟩
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intros i _ hij
      show v i • (Pi.single i (1 : F) : Fin n → F) j = 0
      simp [hij.symm]
    · intro h; exact absurd (Finset.mem_univ j) h

/-- For the standard basis of {lit}`Fⁿ`, the coordinate of a vector in row
{lit}`i` is just the {lit}`i`-th component. -/
@[simp] theorem isBasis_stdBasis_repr {n : ℕ} (x : Fin n → F) (i : Fin n) :
    (isBasis_stdBasis (F := F) n).toModuleBasis.repr x i = x i := by
  classical
  set b := (isBasis_stdBasis (F := F) n).toModuleBasis
  have hb_apply : ∀ k, b k = Pi.single k (1 : F) :=
    IsBasis.toModuleBasis_apply _
  have hxsum : x = ∑ k, x k • b k := by
    funext j
    simp_rw [hb_apply]
    rw [Finset.sum_apply]
    simp_rw [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intros k _ hkj; rw [Pi.single_eq_of_ne (Ne.symm hkj), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hreprx : b.repr x = ∑ k, x k • Finsupp.single k (1 : F) := by
    conv_lhs => rw [hxsum]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show b.repr (x k • b k) = x k • b.repr (b k) from
      b.repr.map_smul _ _, b.repr_self]
  rw [hreprx, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single i]
  · rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        Finsupp.single_apply, if_pos rfl, mul_one]
  · intros k _ hki
    rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        Finsupp.single_apply, if_neg hki, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The monomial basis {lit}`1, x, …, x^{n-1}` of {lit}`Polynomial.degreeLT F n`
packaged as an {name}`IsBasis`. -/
theorem isBasis_polyMono (n : ℕ) :
    IsBasis F (⇑(Polynomial.degreeLT.basis F n)) :=
  ⟨(Polynomial.degreeLT.basis F n).linearIndependent,
   (Polynomial.degreeLT.basis F n).span_eq⟩

/-- Coordinates in the monomial basis are just polynomial coefficients. -/
theorem isBasis_polyMono_repr (n : ℕ) (P : Polynomial.degreeLT F n) (i : Fin n) :
    (isBasis_polyMono (F := F) n).toModuleBasis.repr P i =
      (P : Polynomial F).coeff i := by
  rw [← Polynomial.degreeLT.basis_repr]
  refine Module.Basis.repr_apply_eq (isBasis_polyMono (F := F) n).toModuleBasis
    (fun P i => (Polynomial.degreeLT.basis F n).repr P i) ?_ ?_ ?_ P i
  · intros x y; ext i; simp
  · intros c x; ext i; simp
  · intro j
    have h : (isBasis_polyMono (F := F) n).toModuleBasis j =
        Polynomial.degreeLT.basis F n j :=
      IsBasis.toModuleBasis_apply _ j
    simp [h, (Polynomial.degreeLT.basis F n).repr_self]

/-! These examples (b)–(g) and the note below are the content of exercise
{lit}`2B.2` ("verify all assertions in Example 2.27"); they are stated and
proved here. -/

/-! (b) The list {lit}`(1, 2), (3, 5)` is a basis of {lit}`F²`. Note its
length is 2, the same as the length of the standard basis of {lit}`F²`; this
is no coincidence (see 2.34). -/

/-- Two vectors in {lit}`F²` form a basis exactly when the determinant of the
{lit}`2 × 2` matrix they form is nonzero; used for (b) and for the note below. -/
private lemma isBasis_pair {a b c d : F} (h : a * d - b * c ≠ 0) :
    IsBasis F (![![a, b], ![c, d]] : Fin 2 → Fin 2 → F) := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp [Fin.sum_univ_two] at h0 h1
    have hg0 : g 0 * (a * d - b * c) = 0 := by linear_combination d * h0 - c * h1
    have hg1 : g 1 * (a * d - b * c) = 0 := by linear_combination a * h1 - b * h0
    fin_cases i
    · exact (mul_eq_zero.1 hg0).resolve_right h
    · exact (mul_eq_zero.1 hg1).resolve_right h
  · rw [Spans, eq_top_iff]
    intro x _
    rw [Submodule.mem_span_range_iff_exists_fun]
    have h' : d * a - c * b ≠ 0 := fun hh => h (by linear_combination hh)
    refine ⟨![(x 0 * d - x 1 * c) / (a * d - b * c),
              (x 1 * a - x 0 * b) / (a * d - b * c)], ?_⟩
    funext j
    fin_cases j <;>
      · simp [Fin.sum_univ_two]
        field_simp
        ring

example : IsBasis F (![![1, 2], ![3, 5]] : Fin 2 → Fin 2 → F) := by
  -- (x, y) = a(1, 2) + b(3, 5) has unique solution a = -5x + 3y, b = 2x - y
  -- also they are lin idp as x(1, 2) + y(3, 5) = 0 has unique solution x = y = 0
  refine isBasis_pair ?_
  norm_num

/-! (c) The list {lit}`(1, 2, -4), (7, -5, 6)` is linearly independent in
{lit}`F³` but is *not* a basis: it fails to span. -/

example [CharZero F] :
    ¬ IsBasis F (![![1, 2, -4], ![7, -5, 6]] : Fin 2 → Fin 3 → F) := by
  -- the list misses `(1, 0, 0)`: the functional `x ↦ -8x₀ - 34x₁ - 19x₂`
  -- kills both vectors but not `(1, 0, 0)`
  rintro ⟨-, hspan⟩
  have hx : (![1, 0, 0] : Fin 3 → F) ∈
      Submodule.span F (Set.range (![![1, 2, -4], ![7, -5, 6]] : Fin 2 → Fin 3 → F)) := by
    rw [hspan]; exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_two] at h0 h1 h2
  have : (8 : F) = 0 := by linear_combination -8 * h0 - 34 * h1 - 19 * h2
  norm_num at this

/-! (d) The list {lit}`(1, 2), (3, 5), (4, 13)` spans {lit}`F²` but is not
a basis: it is linearly dependent. -/
example : ¬ IsBasis F
    (![![1, 2], ![3, 5], ![4, 13]] : Fin 3 → Fin 2 → F) := by
  --   19 * (1, 2) +  (-5) * (3, 5) - (4, 13) = 0
  rintro ⟨hli, -⟩
  rw [Fintype.linearIndependent_iff] at hli
  have h := hli ![19, -5, -1] ?_ 2
  · simp at h
  · funext j
    fin_cases j <;>
      · simp [Fin.sum_univ_three]
        ring

/-! (e) The list {lit}`(1, 1, 0), (0, 0, 1)` is a basis of
{lit}`{(x, x, y) ∈ F³ : x, y ∈ F}`. -/

def U_27e (F : Type*) [Field F] : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 = v 1}
  zero_mem' := rfl
  add_mem' := by intro u v hu hv; show u 0 + v 0 = u 1 + v 1; rw [hu, hv]
  smul_mem' := by intro a v hv; show a • v 0 = a • v 1; rw [hv]

def basisVec_27e : Fin 2 → U_27e F :=
  ![⟨![1, 1, 0], rfl⟩, ⟨![0, 0, 1], rfl⟩]

theorem isBasis_basisVec_27e : IsBasis F (basisVec_27e (F := F)) := by
  -- clearly lin indep, and any (x, x, y) = x(1, 1, 0) + y(0, 0, 1)
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg Subtype.val hg
    rw [Fin.sum_univ_two] at h
    simp only [basisVec_27e, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_add, Submodule.coe_smul, ZeroMemClass.coe_zero] at h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    simp at h0 h2
    fin_cases i
    · exact h0
    · exact h2
  · rw [Spans, eq_top_iff]
    intro u _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![(u : Fin 3 → F) 0, (u : Fin 3 → F) 2], ?_⟩
    have hu : (u : Fin 3 → F) 0 = (u : Fin 3 → F) 1 := u.property
    apply Subtype.ext
    rw [Fin.sum_univ_two]
    simp only [basisVec_27e, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_add, Submodule.coe_smul]
    funext j
    fin_cases j <;> simp [hu]

/-! (f) The list {lit}`(1, -1, 0), (1, 0, -1)` is a basis of
{lit}`{(x, y, z) ∈ F³ : x + y + z = 0}`. -/

def U_27f (F : Type*) [Field F] : Submodule F (Fin 3 → F) where
  carrier := {v | v 0 + v 1 + v 2 = 0}
  zero_mem' := by show (0 : F) + 0 + 0 = 0; ring
  add_mem' := by
    intro u v hu hv
    show (u 0 + v 0) + (u 1 + v 1) + (u 2 + v 2) = 0
    have hu' : u 0 + u 1 + u 2 = 0 := hu
    have hv' : v 0 + v 1 + v 2 = 0 := hv
    have heq : (u 0 + v 0) + (u 1 + v 1) + (u 2 + v 2) =
               (u 0 + u 1 + u 2) + (v 0 + v 1 + v 2) := by ring
    rw [heq, hu', hv', add_zero]
  smul_mem' := by
    intro a v hv
    show a • v 0 + a • v 1 + a • v 2 = 0
    simp only [smul_eq_mul]
    have hv' : v 0 + v 1 + v 2 = 0 := hv
    have heq : a * v 0 + a * v 1 + a * v 2 = a * (v 0 + v 1 + v 2) := by ring
    rw [heq, hv', mul_zero]

def basisVec_27f : Fin 2 → U_27f F :=
  ![⟨![1, -1, 0], by show (1 : F) + (-1) + 0 = 0; ring⟩,
    ⟨![1, 0, -1], by show (1 : F) + 0 + (-1) = 0; ring⟩]

theorem isBasis_basisVec_27f : IsBasis F (basisVec_27f (F := F)) := by
  -- lin ind, a (1, -1, 0) + b (1, 0, -1) = 0 - in y coord -> b = 0, z coord -> a = 0
  -- (x, y, z) with x + y + z = 0
  -- can be written as (x, y, -x - y) = (-y) (1, -1, 0) + (x + y) * (1, 0, -1)
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg Subtype.val hg
    rw [Fin.sum_univ_two] at h
    simp only [basisVec_27f, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_add, Submodule.coe_smul, ZeroMemClass.coe_zero] at h
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp at h1 h2
    fin_cases i
    · exact h1
    · exact h2
  · rw [Spans, eq_top_iff]
    intro u _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![-(u : Fin 3 → F) 1, (u : Fin 3 → F) 0 + (u : Fin 3 → F) 1], ?_⟩
    have hu : (u : Fin 3 → F) 0 + (u : Fin 3 → F) 1 + (u : Fin 3 → F) 2 = 0 := u.property
    apply Subtype.ext
    rw [Fin.sum_univ_two]
    simp only [basisVec_27f, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_add, Submodule.coe_smul]
    funext j
    fin_cases j <;> simp
    linear_combination -hu

/-! (g) The list {lit}`1, z, …, zᵐ` is the *standard basis* of {lit}`Pₘ(F)`. -/

example (m : ℕ) : IsBasis F
    (fun i : Fin (m + 1) =>
      (⟨Polynomial.X ^ (i : ℕ), by
        rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]
        exact_mod_cast i.isLt⟩ : Polynomial.degreeLT F (m + 1))) := by
  -- this list *is* mathlib's `degreeLT.basis`, already packaged above
  have h : (fun i : Fin (m + 1) =>
      (⟨Polynomial.X ^ (i : ℕ), by
        rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]
        exact_mod_cast i.isLt⟩ : Polynomial.degreeLT F (m + 1))) =
      ⇑(Polynomial.degreeLT.basis F (m + 1)) :=
    funext fun i => Subtype.ext (Polynomial.degreeLT.basis_val i).symm
  rw [h]
  exact isBasis_polyMono (m + 1)

/-! Note: {lit}`(7, 5), (-4, 9)` and {lit}`(1, 2), (3, 5)` are both bases of
{lit}`F²`. So {lit}`Fⁿ` has many bases beyond the standard one. (The second
list is example (b) above; the first is recorded here.) -/

example [CharZero F] : IsBasis F (![![7, 5], ![-4, 9]] : Fin 2 → Fin 2 → F) := by
  refine isBasis_pair ?_
  norm_num

/-! 2.28 Criterion for basis

A list {lit}`v₁, …, vₙ` is a basis of {lit}`V` iff every {lit}`v ∈ V` can be
written *uniquely* as {lit}`v = a₁ v₁ + ⋯ + aₙ vₙ` with {lit}`aᵢ ∈ F`. -/

theorem isBasis_iff_unique_combo {m : ℕ} (v : Fin m → V) :
    IsBasis F v ↔ ∀ u : V, ∃! a : Fin m → F, ∑ i, a i • v i = u := by
  constructor
  · rintro ⟨hli, hspan⟩ u
    have hu_in : u ∈ Submodule.span F (Set.range v) := by
      rw [hspan]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hu_in
    obtain ⟨a, ha⟩ := hu_in
    refine ⟨a, ha, ?_⟩
    intro b hb
    rw [Fintype.linearIndependent_iff] at hli
    have h_diff : ∑ i, (b i - a i) • v i = 0 := by
      simp_rw [sub_smul]; rw [Finset.sum_sub_distrib, hb, ha, sub_self]
    have h_zero := hli (fun i => b i - a i) h_diff
    funext i; exact sub_eq_zero.mp (h_zero i)
  · intro huniq
    constructor
    · rw [Fintype.linearIndependent_iff]
      intro a ha
      have h0 : ∑ i : Fin m, (0 : F) • v i = 0 := by simp
      have ha_eq : a = (fun _ => 0) := (huniq 0).unique ha h0
      intro i; exact congrFun ha_eq i
    · rw [Spans, eq_top_iff]
      intro u _
      rw [Submodule.mem_span_range_iff_exists_fun]
      obtain ⟨a, ha, _⟩ := huniq u
      exact ⟨a, ha⟩

/-! 2.30 Every spanning list contains a basis

Every spanning list in a vector space can be reduced to a basis by iterating
the rule "drop {lit}`vₖ` if it lies in the span of {lit}`v₁, …, v_{k-1}`". -/

/-- Strengthened form of 2.30: if the first {lit}`m₀` vectors of {lit}`v` are
already linearly independent, Axler's deletion procedure cannot drop any of
them, so the resulting basis is an *extension* of that LI prefix. -/
theorem exists_basis_of_spans_extending {m : ℕ} (v : Fin m → V) (m₀ : ℕ)
    (hm₀ : m₀ ≤ m)
    (hli : LinearIndependent F (fun i : Fin m₀ => v (Fin.castLE hm₀ i)))
    (hv : Spans F v) :
    ∃ (n : ℕ) (vs : Fin n → V) (hn : m₀ ≤ n), IsBasis F vs ∧
      Set.range vs ⊆ Set.range v ∧
      ∀ i : Fin m₀, vs (Fin.castLE hn i) = v (Fin.castLE hm₀ i) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hLI : LinearIndependent F v
    · exact ⟨m, v, hm₀, ⟨hLI, hv⟩, subset_rfl, fun _ => rfl⟩
    · obtain ⟨k, hk_mem, hspan_eq⟩ :=
        LADR.Section_2A.linearDependence_lemma v hLI
      -- The LI-prefix hypothesis forces {lit}`m₀ ≤ k.val`, else the prefix
      -- would be dependent (since {lit}`v k` lies in the span of earlier
      -- prefix vectors).
      have hkm₀ : m₀ ≤ k.val := by
        by_contra hlt
        push Not at hlt
        have hk_lt : k.val < m₀ := hlt
        let kp : Fin m₀ := ⟨k.val, hk_lt⟩
        have hsubset : (v '' {i | i < k}) ⊆
            (fun i : Fin m₀ => v (Fin.castLE hm₀ i)) '' {kp}ᶜ := by
          rintro x ⟨i, hik : i < k, rfl⟩
          refine ⟨⟨i.val, lt_trans hik hk_lt⟩, ?_, ?_⟩
          · intro hh
            rw [Set.mem_singleton_iff] at hh
            have : i.val = k.val := by
              have := congrArg Fin.val hh
              exact this
            omega
          · apply congrArg v; apply Fin.ext; rfl
        have hvk_in : v (Fin.castLE hm₀ kp) ∈ Submodule.span F
            ((fun i : Fin m₀ => v (Fin.castLE hm₀ i)) '' {kp}ᶜ) := by
          have hvk_eq : v k = v (Fin.castLE hm₀ kp) := by
            apply congrArg v; apply Fin.ext; rfl
          rw [← hvk_eq]
          exact Submodule.span_mono hsubset hk_mem
        exact hli.notMem_span kp hvk_in
      have hm_pos : m ≠ 0 := fun h => (h ▸ k).elim0
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      let w : Fin m' → V := v ∘ k.succAbove
      have hm₀' : m₀ ≤ m' := by
        have hkLt : k.val < m' + 1 := k.isLt
        omega
      have hw_prefix : ∀ i : Fin m₀,
          w (Fin.castLE hm₀' i) = v (Fin.castLE hm₀ i) := by
        intro i
        show v (k.succAbove (Fin.castLE hm₀' i)) = v (Fin.castLE hm₀ i)
        have hLt : ((Fin.castLE hm₀' i : Fin m')).castSucc < k := by
          show (Fin.castLE hm₀' i).val < k.val
          rw [Fin.val_castLE]
          have hi : i.val < m₀ := i.isLt
          omega
        rw [Fin.succAbove_of_castSucc_lt _ _ hLt]
        apply congrArg v; apply Fin.ext; rfl
      have hw_li : LinearIndependent F
          (fun i : Fin m₀ => w (Fin.castLE hm₀' i)) := by
        have heq : (fun i : Fin m₀ => w (Fin.castLE hm₀' i)) =
            (fun i : Fin m₀ => v (Fin.castLE hm₀ i)) := by
          funext i; exact hw_prefix i
        rw [heq]; exact hli
      have hw_range : Set.range w = v '' {i | i ≠ k} := by
        show Set.range (v ∘ k.succAbove) = v '' {i | i ≠ k}
        rw [Set.range_comp, Fin.range_succAbove]
        rfl
      have hw_spans : Spans F w := by
        show Submodule.span F (Set.range w) = ⊤
        rw [hw_range, ← hspan_eq]
        exact hv
      obtain ⟨n, vs, hn, hbasis, hsub, hpres⟩ :=
        ih m' (Nat.lt_succ_self m') w hm₀' hw_li hw_spans
      refine ⟨n, vs, hn, hbasis, ?_, ?_⟩
      · intro x hx
        obtain ⟨i, rfl⟩ := hsub hx
        exact ⟨k.succAbove i, rfl⟩
      · intro i
        rw [hpres i, hw_prefix i]

/-- 2.30: every spanning list contains a basis. Special case of
{name}`exists_basis_of_spans_extending` with empty LI prefix. -/
theorem exists_basis_of_spans {m : ℕ} (v : Fin m → V) (hv : Spans F v) :
    ∃ (n : ℕ) (vs : Fin n → V), IsBasis F vs ∧ Set.range vs ⊆ Set.range v := by
  obtain ⟨n, vs, _, hbasis, hsub, _⟩ :=
    exists_basis_of_spans_extending v 0 (Nat.zero_le _)
      (by rw [Fintype.linearIndependent_iff]; intro a _ i; exact i.elim0) hv
  exact ⟨n, vs, hbasis, hsub⟩

/-! 2.31 Basis of finite-dimensional vector space

Every finite-dimensional vector space has a basis: apply 2.30 to a spanning
list given by finite-dimensionality. -/

theorem exists_basis [Module.Finite F V] :
    ∃ (n : ℕ) (v : Fin n → V), IsBasis F v := by
  obtain ⟨_, w, hw⟩ := Module.Finite.exists_fin (R := F) (M := V)
  obtain ⟨n', vs, hbasis, _⟩ := exists_basis_of_spans w hw
  exact ⟨n', vs, hbasis⟩

/-! 2.32 Every linearly independent list extends to a basis

Every linearly independent list in a finite-dimensional vector space can be
extended (by adjoining further vectors) to a basis of the space. -/

theorem exists_basis_extending [Module.Finite F V] {m : ℕ} (v : Fin m → V)
    (hv : LinearIndependent F v) :
    ∃ (n : ℕ) (w : Fin n → V) (hn : m ≤ n), IsBasis F w ∧
      ∀ i : Fin m, w (Fin.castLE hn i) = v i := by
  -- Append a spanning list to {lit}`v` and apply the strengthened 2.30: the
  -- {lit}`v`-prefix is LI, so none of its entries get dropped.
  obtain ⟨n', ws, hws⟩ := Module.Finite.exists_fin (R := F) (M := V)
  let u : Fin (m + n') → V := Fin.append v ws
  have hm_le : m ≤ m + n' := Nat.le_add_right m n'
  have hu_prefix : ∀ i : Fin m, u (Fin.castLE hm_le i) = v i := by
    intro i; exact Fin.append_left' v ws i
  have hu_li_prefix : LinearIndependent F
      (fun i : Fin m => u (Fin.castLE hm_le i)) := by
    have heq : (fun i : Fin m => u (Fin.castLE hm_le i)) = v := by
      funext i; exact hu_prefix i
    rw [heq]; exact hv
  have hu_spans : Spans F u := by
    show Submodule.span F (Set.range u) = ⊤
    rw [eq_top_iff, ← hws]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨Fin.natAdd m i, Fin.append_right v ws i⟩
  obtain ⟨n, w, hn, hbasis, _, hpres⟩ :=
    exists_basis_of_spans_extending u m hm_le hu_li_prefix hu_spans
  refine ⟨n, w, hn, hbasis, ?_⟩
  intro i; rw [hpres i, hu_prefix i]

/-! 2.33 Every subspace of {lit}`V` is part of a direct sum equal to {lit}`V`

If {lit}`V` is finite-dimensional and {lit}`U` is a subspace of {lit}`V`,
then there is a subspace {lit}`W` of {lit}`V` such that {lit}`V = U ⊕ W`. -/

private lemma sum_prefix_tail {m n : ℕ} (hmn : m ≤ n) {M : Type*} [AddCommMonoid M]
    (f : Fin n → M) :
    ∑ k : Fin n, f k =
      (∑ i : Fin m, f (Fin.castLE hmn i)) +
      (∑ j : Fin (n - m), f ⟨m + j.val, by have := j.isLt; omega⟩) := by
  have heq : m + (n - m) = n := by omega
  rw [← Equiv.sum_comp (finCongr heq) f, Fin.sum_univ_add]
  congr 1

theorem exists_isCompl [Module.Finite F V] (U : Submodule F V) :
    ∃ W : Submodule F V, IsCompl U W := by
  -- Take a basis {lit}`u` of {lit}`U`, view it in {lit}`V`, extend to a basis
  -- {lit}`w` of {lit}`V`, and let {lit}`W` be the span of the appended tail.
  classical
  obtain ⟨m, u, hu_basis⟩ := exists_basis (F := F) (V := U)
  let uV : Fin m → V := fun i => (u i : V)
  have hu_li_V : LinearIndependent F uV :=
    hu_basis.1.map' U.subtype
      (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  obtain ⟨n, w, hmn, hw_basis, hw_prefix⟩ := exists_basis_extending uV hu_li_V
  let W : Submodule F V :=
    Submodule.span F (Set.range (fun j : Fin (n - m) =>
      w ⟨m + j.val, by have := j.isLt; omega⟩))
  have hprefix_eq : ∀ (c : Fin n → F) (i : Fin m),
      c (Fin.castLE hmn i) • w (Fin.castLE hmn i) =
        c (Fin.castLE hmn i) • uV i := by
    intro c i; rw [hw_prefix i]
  refine ⟨W, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v hvU hvW
    have hu_span_U : Submodule.span F (Set.range u) = ⊤ := hu_basis.2
    have hv_in_uU : (⟨v, hvU⟩ : U) ∈ Submodule.span F (Set.range u) := by
      rw [hu_span_U]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hv_in_uU
    obtain ⟨a, ha⟩ := hv_in_uU
    have hv_eq_uV : ∑ i, a i • uV i = v := by
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at this
      convert this using 1
    rw [Submodule.mem_span_range_iff_exists_fun] at hvW
    obtain ⟨b, hb⟩ := hvW
    -- {lit}`c` combines the two expansions into a vanishing relation on the
    -- full basis {lit}`w`: coefficients {lit}`a` on the prefix, {lit}`-b` on
    -- the tail.
    let c : Fin n → F := fun k =>
      if h : k.val < m then a ⟨k.val, h⟩
      else -b ⟨k.val - m, by have := k.isLt; omega⟩
    have hc_prefix : ∀ i : Fin m, c (Fin.castLE hmn i) = a i := by
      intro i
      show (if h : (Fin.castLE hmn i).val < m then a ⟨_, h⟩ else _) = a i
      have hlt : (Fin.castLE hmn i).val < m := by rw [Fin.val_castLE]; exact i.isLt
      rw [dif_pos hlt]
      congr 1
    have hc_tail : ∀ j : Fin (n - m),
        c ⟨m + j.val, by have := j.isLt; omega⟩ = -b j := by
      intro j
      show (if h : _ < m then _ else _) = -b j
      have hge : ¬ m + j.val < m := by omega
      rw [dif_neg hge]
      congr
      show m + j.val - m = j.val
      omega
    have hsum_zero : ∑ k, c k • w k = 0 := by
      rw [sum_prefix_tail hmn (fun k => c k • w k)]
      have hsum1 : ∑ i : Fin m, c (Fin.castLE hmn i) • w (Fin.castLE hmn i) = v := by
        rw [← hv_eq_uV]
        apply Finset.sum_congr rfl
        intro i _; rw [hprefix_eq c i, hc_prefix i]
      have hsum2 : ∑ j : Fin (n - m),
          c ⟨m + j.val, by have := j.isLt; omega⟩ •
            w ⟨m + j.val, by have := j.isLt; omega⟩ = -v := by
        rw [← hb, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _; rw [hc_tail j, neg_smul]
      rw [hsum1, hsum2, add_neg_cancel]
    have hc_zero : ∀ k, c k = 0 := by
      have hli := hw_basis.1
      rw [Fintype.linearIndependent_iff] at hli
      exact hli c hsum_zero
    rw [← hv_eq_uV]
    apply Finset.sum_eq_zero
    intro i _
    have hai : a i = 0 := by rw [← hc_prefix i]; exact hc_zero _
    rw [hai, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hw_span : Submodule.span F (Set.range w) = ⊤ := hw_basis.2
    have hv_in : v ∈ Submodule.span F (Set.range w) := by
      rw [hw_span]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hv_in
    obtain ⟨c, hc⟩ := hv_in
    have hsplit := sum_prefix_tail hmn (fun k => c k • w k)
    rw [hc] at hsplit
    rw [hsplit]
    apply Submodule.add_mem_sup
    · apply Submodule.sum_mem
      intro i _
      rw [hw_prefix i]
      exact U.smul_mem _ (u i).property
    · apply Submodule.sum_mem
      intro j _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-! # Exercises -/

/-- 2B.1: "Find all vector spaces that have exactly one basis." The answer is
{lit}`V = {0}`, whose unique basis is the empty list.

A basis in the book's sense is a *list*, so "a basis of {lit}`V`" is a pair
{lit}`⟨n, v : Fin n → V⟩` and "exactly one basis" is uniqueness of that pair.
The hypothesis {lit}`hF` — some scalar is neither {lit}`0` nor {lit}`1` — holds
for Axler's {lit}`𝐅 = ℝ, ℂ` and is needed: over {lit}`𝔽₂` the space
{lit}`𝔽₂` has {lit}`(1)` as its only basis. -/
theorem exercise_2B_1 (hF : ∃ c : F, c ≠ 0 ∧ c ≠ 1) :
    (∃! p : (n : ℕ) × (Fin n → V), IsBasis F p.2) ↔ Subsingleton V := by
  constructor
  · -- A space with a basis but more than one vector has a second basis: rescale
    -- every vector by a scalar `c ∉ {0, 1}`.
    rintro ⟨⟨n, v⟩, hv, huniq⟩
    replace hv : IsBasis F v := hv
    obtain ⟨c, hc0, hc1⟩ := hF
    by_contra hns
    -- `n = 0` would force `V = {0}`, so some basis vector is nonzero.
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        refine absurd ?_ hns
        constructor
        intro x y
        have hx : ∀ z : V, z = 0 := by
          intro z
          have : z ∈ Submodule.span F (Set.range v) := hv.2 ▸ Submodule.mem_top
          simpa [Set.range_eq_empty] using this
        rw [hx x, hx y]
      · exact h
    set i : Fin n := ⟨0, hn⟩ with hi
    have hvi : v i ≠ 0 := hv.1.ne_zero i
    -- the rescaled list is again a basis
    have hw : IsBasis F (fun k => c • v k) := by
      refine ⟨?_, ?_⟩
      · exact (hv.1.units_smul fun _ => Units.mk0 c hc0)
      · rw [Spans, eq_top_iff, ← hv.2, Submodule.span_le, Set.range_subset_iff]
        intro k
        have hk : v k = c⁻¹ • (c • v k) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hk]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have heq : (⟨n, fun k => c • v k⟩ : (m : ℕ) × (Fin m → V)) = ⟨n, v⟩ := by
      rw [huniq ⟨n, fun k => c • v k⟩ hw, huniq ⟨n, v⟩ hv]
    have : c • v i = v i := congrFun (by simpa using heq) i
    have : (c - 1) • v i = 0 := by rw [sub_smul, one_smul, this, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact hc1 (by linear_combination h)
    · exact hvi h
  · -- `V = {0}`: the empty list is a basis, and no other list is.
    intro hs
    refine ⟨⟨0, Fin.elim0⟩, ⟨linearIndependent_empty_type, ?_⟩, ?_⟩
    · rw [Spans]
      refine Submodule.eq_top_iff'.2 fun x => ?_
      rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _
    · rintro ⟨m, w⟩ hw
      have hm : m = 0 := by
        by_contra hm
        exact hw.1.ne_zero ⟨0, Nat.pos_of_ne_zero hm⟩ (Subsingleton.elim _ _)
      subst hm
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      exact funext fun k => k.elim0

/-! 2B.2: verify the assertions in Example 2.27 (proved as {lit}`example`s
above). -/

/-- 2B.3 -/
def exercise_2B_3_U : Submodule ℝ (Fin 5 → ℝ) where
  carrier := {v | v 0 = 3 * v 1 ∧ v 2 = 7 * v 3}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨?_, ?_⟩
    · show u 0 + v 0 = 3 * (u 1 + v 1); rw [h1, h1']; ring
    · show u 2 + v 2 = 7 * (u 3 + v 3); rw [h2, h2']; ring
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · show a • v 0 = 3 * (a • v 1); simp only [smul_eq_mul]; rw [h1]; ring
    · show a • v 2 = 7 * (a • v 3); simp only [smul_eq_mul]; rw [h2]; ring

/-- 2B.3(a): a basis of {lit}`U` — {lit}`(3, 1, 0, 0, 0)`, {lit}`(0, 0, 7, 1, 0)`,
{lit}`(0, 0, 0, 0, 1)`. -/
def exercise_2B_3a_v : Fin 3 → exercise_2B_3_U :=
  ![⟨![3, 1, 0, 0, 0], by constructor <;> simp⟩,
    ⟨![0, 0, 7, 1, 0], by constructor <;> simp⟩,
    ⟨![0, 0, 0, 0, 1], by constructor <;> simp⟩]

/-- 2B.3(a) -/
theorem exercise_2B_3a : IsBasis ℝ exercise_2B_3a_v := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg Subtype.val hg
    rw [Fin.sum_univ_three] at h
    simp [exercise_2B_3a_v] at h
    obtain ⟨h0, h1, h2⟩ := h
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rw [Spans, eq_top_iff]
    intro u _
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨hu0, hu2⟩ := u.property
    refine ⟨![(u : Fin 5 → ℝ) 1, (u : Fin 5 → ℝ) 3, (u : Fin 5 → ℝ) 4], ?_⟩
    apply Subtype.ext
    rw [Fin.sum_univ_three]
    simp [exercise_2B_3a_v]
    funext j
    fin_cases j <;> simp [hu0, hu2] <;> ring

/-- 2B.3(b): the basis of (a), extended by {lit}`(1, 0, 0, 0, 0)` and
{lit}`(0, 0, 1, 0, 0)` to a basis of {lit}`ℝ⁵`. -/
def exercise_2B_3b_v : Fin 5 → (Fin 5 → ℝ) :=
  ![![3, 1, 0, 0, 0], ![0, 0, 7, 1, 0], ![0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0], ![0, 0, 1, 0, 0]]

/-- 2B.3(b) -/
theorem exercise_2B_3b : IsBasis ℝ exercise_2B_3b_v ∧
    ∀ i : Fin 3, exercise_2B_3b_v (i.castLE (by norm_num)) =
      (exercise_2B_3a_v i : Fin 5 → ℝ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_five] at hg
    simp [exercise_2B_3b_v] at hg
    obtain ⟨h0, h1, h2, h3, h4⟩ := hg
    fin_cases i
    · exact h1
    · exact h3
    · exact h4
    · show g 3 = 0
      linear_combination h0 - 3 * h1
    · show g 4 = 0
      linear_combination h2 - 7 * h3
  · rw [Spans, eq_top_iff]
    intro x _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![x 1, x 3, x 4, x 0 - 3 * x 1, x 2 - 7 * x 3], ?_⟩
    rw [Fin.sum_univ_five]
    simp [exercise_2B_3b_v]
    funext j
    fin_cases j <;> simp <;> ring
  · intro i
    fin_cases i <;> rfl

/-- 2B.3(c): the subspace spanned by {lit}`(1, 0, 0, 0, 0)` and
{lit}`(0, 0, 1, 0, 0)`. -/
def exercise_2B_3c_W : Submodule ℝ (Fin 5 → ℝ) :=
  Submodule.span ℝ (Set.range ![(![1, 0, 0, 0, 0] : Fin 5 → ℝ), ![0, 0, 1, 0, 0]])

/-- 2B.3(c) -/
theorem exercise_2B_3c : IsCompl exercise_2B_3_U exercise_2B_3c_W := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxU, hxW⟩
    obtain ⟨hx0, hx2⟩ := hxU
    rw [SetLike.mem_coe, exercise_2B_3c_W,
      Submodule.mem_span_range_iff_exists_fun] at hxW
    obtain ⟨c, hc⟩ := hxW
    rw [Fin.sum_univ_two] at hc
    have h1 := congrFun hc 1
    have h3 := congrFun hc 3
    have h4 := congrFun hc 4
    simp at h1 h3 h4
    have : x = 0 := by
      funext j
      fin_cases j <;> simp [← h1, ← h3, ← h4, hx0, hx2]
    simpa using this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hU : (![3 * x 1, x 1, 7 * x 3, x 3, x 4] : Fin 5 → ℝ) ∈ exercise_2B_3_U := by
      constructor <;> simp
    have hW : (x - ![3 * x 1, x 1, 7 * x 3, x 3, x 4] : Fin 5 → ℝ) ∈ exercise_2B_3c_W := by
      rw [exercise_2B_3c_W, Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![x 0 - 3 * x 1, x 2 - 7 * x 3], ?_⟩
      rw [Fin.sum_univ_two]
      funext j
      fin_cases j <;> simp
    have hsum := Submodule.add_mem_sup hU hW
    have hx : (![3 * x 1, x 1, 7 * x 3, x 3, x 4] : Fin 5 → ℝ) +
        (x - ![3 * x 1, x 1, 7 * x 3, x 3, x 4]) = x := by abel
    rwa [hx] at hsum

/-- 2B.4 -/
def exercise_2B_4_U : Submodule ℂ (Fin 5 → ℂ) where
  carrier := {v | 6 * v 0 = v 1 ∧ v 2 + 2 * v 3 + 3 * v 4 = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro u v ⟨h1, h2⟩ ⟨h1', h2'⟩
    constructor
    · show 6 * (u 0 + v 0) = u 1 + v 1
      have : 6 * (u 0 + v 0) = 6 * u 0 + 6 * v 0 := by ring
      rw [this, h1, h1']
    · show (u 2 + v 2) + 2 * (u 3 + v 3) + 3 * (u 4 + v 4) = 0
      have heq : (u 2 + v 2) + 2 * (u 3 + v 3) + 3 * (u 4 + v 4) =
                 (u 2 + 2 * u 3 + 3 * u 4) + (v 2 + 2 * v 3 + 3 * v 4) := by ring
      rw [heq, h2, h2', add_zero]
  smul_mem' := by
    rintro a v ⟨h1, h2⟩
    constructor
    · show 6 * (a • v 0) = a • v 1
      simp only [smul_eq_mul]
      have : 6 * (a * v 0) = a * (6 * v 0) := by ring
      rw [this, h1]
    · show a • v 2 + 2 * (a • v 3) + 3 * (a • v 4) = 0
      simp only [smul_eq_mul]
      have heq : a * v 2 + 2 * (a * v 3) + 3 * (a * v 4) =
                 a * (v 2 + 2 * v 3 + 3 * v 4) := by ring
      rw [heq, h2, mul_zero]

/-- 2B.4(a): a basis of {lit}`U` — {lit}`(1, 6, 0, 0, 0)`, {lit}`(0, 0, -2, 1, 0)`,
{lit}`(0, 0, -3, 0, 1)`. -/
def exercise_2B_4a_v : Fin 3 → exercise_2B_4_U :=
  ![⟨![1, 6, 0, 0, 0], by constructor <;> simp⟩,
    ⟨![0, 0, -2, 1, 0], by constructor <;> simp⟩,
    ⟨![0, 0, -3, 0, 1], by constructor <;> simp⟩]

/-- 2B.4(a) -/
theorem exercise_2B_4a : IsBasis ℂ exercise_2B_4a_v := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg Subtype.val hg
    rw [Fin.sum_univ_three] at h
    simp [exercise_2B_4a_v] at h
    obtain ⟨h0, -, h1, h2⟩ := h
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rw [Spans, eq_top_iff]
    intro u _
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨hu1, hu2⟩ := u.property
    refine ⟨![(u : Fin 5 → ℂ) 0, (u : Fin 5 → ℂ) 3, (u : Fin 5 → ℂ) 4], ?_⟩
    apply Subtype.ext
    rw [Fin.sum_univ_three]
    simp [exercise_2B_4a_v]
    funext j
    fin_cases j <;> simp <;>
      first
        | linear_combination hu1
        | linear_combination -hu2

/-- 2B.4(b): the basis of (a), extended by {lit}`(0, 1, 0, 0, 0)` and
{lit}`(0, 0, 1, 0, 0)` to a basis of {lit}`ℂ⁵`. -/
def exercise_2B_4b_v : Fin 5 → (Fin 5 → ℂ) :=
  ![![1, 6, 0, 0, 0], ![0, 0, -2, 1, 0], ![0, 0, -3, 0, 1],
    ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0]]

/-- 2B.4(b) -/
theorem exercise_2B_4b : IsBasis ℂ exercise_2B_4b_v ∧
    ∀ i : Fin 3, exercise_2B_4b_v (i.castLE (by norm_num)) =
      (exercise_2B_4a_v i : Fin 5 → ℂ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_five] at hg
    simp [exercise_2B_4b_v] at hg
    obtain ⟨h0, h1, h2, h3, h4⟩ := hg
    fin_cases i
    · exact h0
    · exact h3
    · exact h4
    · show g 3 = 0
      linear_combination h1 - 6 * h0
    · show g 4 = 0
      linear_combination h2 + 2 * h3 + 3 * h4
  · rw [Spans, eq_top_iff]
    intro x _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![x 0, x 3, x 4, x 1 - 6 * x 0, x 2 + 2 * x 3 + 3 * x 4], ?_⟩
    rw [Fin.sum_univ_five]
    simp [exercise_2B_4b_v]
    funext j
    fin_cases j <;> simp <;> ring
  · intro i
    fin_cases i <;> rfl

/-- 2B.4(c): the subspace spanned by {lit}`(0, 1, 0, 0, 0)` and
{lit}`(0, 0, 1, 0, 0)`. -/
def exercise_2B_4c_W : Submodule ℂ (Fin 5 → ℂ) :=
  Submodule.span ℂ (Set.range ![(![0, 1, 0, 0, 0] : Fin 5 → ℂ), ![0, 0, 1, 0, 0]])

/-- 2B.4(c) -/
theorem exercise_2B_4c : IsCompl exercise_2B_4_U exercise_2B_4c_W := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxU, hxW⟩
    obtain ⟨hx1, hx2⟩ := hxU
    rw [SetLike.mem_coe, exercise_2B_4c_W,
      Submodule.mem_span_range_iff_exists_fun] at hxW
    obtain ⟨c, hc⟩ := hxW
    rw [Fin.sum_univ_two] at hc
    have h0 := congrFun hc 0
    have h3 := congrFun hc 3
    have h4 := congrFun hc 4
    simp at h0 h3 h4
    have : x = 0 := by
      funext j
      fin_cases j <;> simp [← h0, ← h3, ← h4, ← hx1]
      linear_combination hx2 - 2 * h3.symm - 3 * h4.symm
    simpa using this
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hU : (![x 0, 6 * x 0, -2 * x 3 - 3 * x 4, x 3, x 4] : Fin 5 → ℂ) ∈
        exercise_2B_4_U := by
      constructor <;> simp
      ring
    have hW : (x - ![x 0, 6 * x 0, -2 * x 3 - 3 * x 4, x 3, x 4] : Fin 5 → ℂ) ∈
        exercise_2B_4c_W := by
      rw [exercise_2B_4c_W, Submodule.mem_span_range_iff_exists_fun]
      refine ⟨![x 1 - 6 * x 0, x 2 + 2 * x 3 + 3 * x 4], ?_⟩
      rw [Fin.sum_univ_two]
      funext j
      fin_cases j <;> simp
      ring
    have hsum := Submodule.add_mem_sup hU hW
    have hx : (![x 0, 6 * x 0, -2 * x 3 - 3 * x 4, x 3, x 4] : Fin 5 → ℂ) +
        (x - ![x 0, 6 * x 0, -2 * x 3 - 3 * x 4, x 3, x 4]) = x := by abel
    rwa [hx] at hsum

/-- 2B.5 -/
theorem exercise_2B_5 [Module.Finite F V] (U W : Submodule F V) (hUW : U ⊔ W = ⊤) :
    ∃ (n : ℕ) (v : Fin n → V), IsBasis F v ∧
      ∀ i, (v i ∈ U) ∨ (v i ∈ W) := by
  -- A basis of {lit}`U` followed by a basis of {lit}`W` is a list of vectors of
  -- {lit}`U ∪ W` spanning {lit}`U + W = V`; 2.30 extracts a basis from it, and
  -- every vector kept still comes from {lit}`U` or from {lit}`W`.
  obtain ⟨m, u, hu⟩ := exists_basis (F := F) (V := U)
  obtain ⟨k, w, hw⟩ := exists_basis (F := F) (V := W)
  set v : Fin (m + k) → V := Fin.append (fun i => (u i : V)) (fun j => (w j : V)) with hv
  have hvU : ∀ i : Fin m, v (Fin.castAdd k i) = (u i : V) := by
    intro i; rw [hv, Fin.append_left]
  have hvW : ∀ j : Fin k, v (Fin.natAdd m j) = (w j : V) := by
    intro j; rw [hv, Fin.append_right]
  have hmem : ∀ i, v i ∈ U ∨ v i ∈ W := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_)
    · exact Or.inl (hvU i ▸ (u i).property)
    · exact Or.inr (hvW j ▸ (w j).property)
  have hspan : Spans F v := by
    rw [Spans, eq_top_iff, ← hUW, sup_le_iff]
    constructor
    · intro x hx
      have hxU : (⟨x, hx⟩ : U) ∈ Submodule.span F (Set.range u) := by
        rw [hu.2]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxU
      obtain ⟨c, hc⟩ := hxU
      have hx' : x = ∑ i, c i • (u i : V) := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      rw [hx']
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Fin.castAdd k i, hvU i⟩)
    · intro x hx
      have hxW : (⟨x, hx⟩ : W) ∈ Submodule.span F (Set.range w) := by
        rw [hw.2]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxW
      obtain ⟨c, hc⟩ := hxW
      have hx' : x = ∑ j, c j • (w j : V) := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      rw [hx']
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Fin.natAdd m j, hvW j⟩)
  obtain ⟨n, vs, hbasis, hsub⟩ := exists_basis_of_spans v hspan
  refine ⟨n, vs, hbasis, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hsub (Set.mem_range_self i)
  rw [← hj]
  exact hmem j

/-- 2B.6: a counterexample — {lit}`1, X, X³ + X², X³` is a list in
{lit}`P₃(F)` none of whose entries has degree 2. -/
noncomputable def exercise_2B_6_p : Fin 4 → Polynomial.degreeLT F 4 :=
  ![⟨1, by rw [Polynomial.mem_degreeLT, Polynomial.degree_one]; decide⟩,
    ⟨Polynomial.X, by rw [Polynomial.mem_degreeLT, Polynomial.degree_X]; decide⟩,
    ⟨Polynomial.X ^ 3 + Polynomial.X ^ 2, by
      refine Submodule.add_mem _ ?_ ?_ <;>
        · rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]; decide⟩,
    ⟨Polynomial.X ^ 3, by rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]; decide⟩]

/-- None of the four polynomials has degree 2 (their degrees are 0, 1, 3, 3). -/
theorem exercise_2B_6_degree (i : Fin 4) :
    ((exercise_2B_6_p (F := F) i : Polynomial F)).degree ≠ 2 := by
  fin_cases i
  · show (1 : Polynomial F).degree ≠ 2
    rw [Polynomial.degree_one]; decide
  · show (Polynomial.X : Polynomial F).degree ≠ 2
    rw [Polynomial.degree_X]; decide
  · show (Polynomial.X ^ 3 + Polynomial.X ^ 2 : Polynomial F).degree ≠ 2
    have hlt : (Polynomial.X ^ 2 : Polynomial F).degree <
        (Polynomial.X ^ 3 : Polynomial F).degree := by
      rw [Polynomial.degree_X_pow, Polynomial.degree_X_pow]; decide
    rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
    decide
  · show (Polynomial.X ^ 3 : Polynomial F).degree ≠ 2
    rw [Polynomial.degree_X_pow]; decide

/-- The counterexample really is a basis: {lit}`X²` is recovered as
{lit}`(X³ + X²) - X³`. -/
theorem exercise_2B_6_isBasis : IsBasis F (exercise_2B_6_p (F := F)) := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg Subtype.val hg
    rw [Fin.sum_univ_four] at h
    simp only [exercise_2B_6_p, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Submodule.coe_add, Submodule.coe_smul,
      ZeroMemClass.coe_zero] at h
    have h0 := congrArg (fun q : Polynomial F => q.coeff 0) h
    have h1 := congrArg (fun q : Polynomial F => q.coeff 1) h
    have h2 := congrArg (fun q : Polynomial F => q.coeff 2) h
    have h3 := congrArg (fun q : Polynomial F => q.coeff 3) h
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X] at h0 h1 h2 h3
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · show g 3 = 0
      linear_combination h3 - h2
  · rw [Spans, eq_top_iff, ← (isBasis_polyMono (F := F) 4).2, Submodule.span_le,
      Set.range_subset_iff]
    intro i
    rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    fin_cases i
    · exact ⟨![1, 0, 0, 0], by
        apply Subtype.ext
        rw [Fin.sum_univ_four]
        simp [exercise_2B_6_p, Polynomial.degreeLT.basis_val]⟩
    · exact ⟨![0, 1, 0, 0], by
        apply Subtype.ext
        rw [Fin.sum_univ_four]
        simp [exercise_2B_6_p, Polynomial.degreeLT.basis_val]⟩
    · exact ⟨![0, 0, 1, -1], by
        apply Subtype.ext
        rw [Fin.sum_univ_four]
        simp [exercise_2B_6_p, Polynomial.degreeLT.basis_val]⟩
    · exact ⟨![0, 0, 0, 1], by
        apply Subtype.ext
        rw [Fin.sum_univ_four]
        simp [exercise_2B_6_p, Polynomial.degreeLT.basis_val]⟩

/-- 2B.6 -/
def exercise_2B_6 :
    Decidable (∀ (p : Fin 4 → Polynomial.degreeLT F 4),
      (∀ i, (p i : Polynomial F).degree ≠ 2) → ¬ IsBasis F p) := by
  -- false: a list can avoid degree 2 and still produce {lit}`X²` as a
  -- combination, here as {lit}`(X³ + X²) - X³`
  apply isFalse
  intro h
  exact h exercise_2B_6_p exercise_2B_6_degree exercise_2B_6_isBasis

/-- 2B.7 -/
theorem exercise_2B_7 (v : Fin 4 → V) (hv : IsBasis F v) :
    IsBasis F (![v 0 + v 1, v 1 + v 2, v 2 + v 3, v 3] : Fin 4 → V) := by
  -- in terms of the old basis the new list has coefficients
  -- `a 0, a 0 + a 1, a 1 + a 2, a 2 + a 3`, a triangular change of basis
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_four] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hg
    have hli := hv.1
    rw [Fintype.linearIndependent_iff] at hli
    have hsum : ∑ j, (![g 0, g 0 + g 1, g 1 + g 2, g 2 + g 3] : Fin 4 → F) j • v j = 0 := by
      rw [Fin.sum_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      rw [← hg]
      module
    have h := hli _ hsum
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2 h3
    fin_cases i
    · exact h0
    · show g 1 = 0
      linear_combination h1 - h0
    · show g 2 = 0
      linear_combination h2 - h1 + h0
    · show g 3 = 0
      linear_combination h3 - h2 + h1 - h0
  · rw [Spans, eq_top_iff]
    intro x _
    rw [Submodule.mem_span_range_iff_exists_fun]
    have hx : x ∈ Submodule.span F (Set.range v) := by rw [hv.2]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨![a 0, a 1 - a 0, a 2 - a 1 + a 0, a 3 - a 2 + a 1 - a 0], ?_⟩
    rw [Fin.sum_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [← ha, Fin.sum_univ_four]
    module

/-- 2B.8: the subspace {lit}`{x ∈ F⁴ : x₃ = 0}` of the counterexample. -/
def exercise_2B_8_U : Submodule F (Fin 4 → F) where
  carrier := {x | x 3 = 0}
  zero_mem' := rfl
  add_mem' := by intro a b ha hb; show a 3 + b 3 = 0; rw [ha, hb, add_zero]
  smul_mem' := by intro c x hx; show c • x 3 = 0; rw [hx, smul_zero]

/-- 2B.8: the basis {lit}`e₀, e₁, e₂ + e₃, e₃` of {lit}`F⁴`. Its first two
vectors lie in {lit}`U` and its last two do not, yet they miss {lit}`e₂ ∈ U`.
(The variant {lit}`e₂ + e₃, e₂ - e₃` also works, but not in characteristic 2,
where those two vectors coincide.) -/
def exercise_2B_8_v : Fin 4 → (Fin 4 → F) :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 1], ![0, 0, 0, 1]]

theorem exercise_2B_8_isBasis : IsBasis F (exercise_2B_8_v (F := F)) := by
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_four] at hg
    simp [exercise_2B_8_v] at hg
    obtain ⟨h0, h1, h2, h3⟩ := hg
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · show g 3 = 0
      linear_combination h3 - h2
  · rw [Spans, eq_top_iff]
    intro x _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![x 0, x 1, x 2, x 3 - x 2], ?_⟩
    rw [Fin.sum_univ_four]
    simp [exercise_2B_8_v]
    funext j
    fin_cases j <;> simp

theorem exercise_2B_8_mem₀ : exercise_2B_8_v (F := F) 0 ∈ exercise_2B_8_U := by
  show (![1, 0, 0, 0] : Fin 4 → F) 3 = 0
  simp

theorem exercise_2B_8_mem₁ : exercise_2B_8_v (F := F) 1 ∈ exercise_2B_8_U := by
  show (![0, 1, 0, 0] : Fin 4 → F) 3 = 0
  simp

theorem exercise_2B_8_notMem₂ : exercise_2B_8_v (F := F) 2 ∉ exercise_2B_8_U := by
  intro h
  have h' : (![0, 0, 1, 1] : Fin 4 → F) 3 = 0 := h
  simp at h'

theorem exercise_2B_8_notMem₃ : exercise_2B_8_v (F := F) 3 ∉ exercise_2B_8_U := by
  intro h
  have h' : (![0, 0, 0, 1] : Fin 4 → F) 3 = 0 := h
  simp at h'

/-- The first two vectors are not a basis of {lit}`U`: they miss
{lit}`e₂ = (0, 0, 1, 0) ∈ U`. -/
theorem exercise_2B_8_not_isBasis
    (h0 : exercise_2B_8_v (F := F) 0 ∈ exercise_2B_8_U)
    (h1 : exercise_2B_8_v (F := F) 1 ∈ exercise_2B_8_U) :
    ¬ IsBasis F (![⟨exercise_2B_8_v 0, h0⟩, ⟨exercise_2B_8_v 1, h1⟩] :
      Fin 2 → exercise_2B_8_U) := by
  rintro ⟨-, hspan⟩
  have he₂ : (⟨![0, 0, 1, 0], rfl⟩ : exercise_2B_8_U (F := F)) ∈
      Submodule.span F (Set.range
        (![⟨exercise_2B_8_v 0, h0⟩, ⟨exercise_2B_8_v 1, h1⟩] :
          Fin 2 → exercise_2B_8_U)) := by
    rw [hspan]; exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at he₂
  obtain ⟨c, hc⟩ := he₂
  have h := congrArg Subtype.val hc
  rw [Fin.sum_univ_two] at h
  simp [exercise_2B_8_v] at h

universe u in
/-- 2B.8 — the space is quantified (with the section's fixed {lit}`V` the
claim is vacuously true whenever {lit}`dim V ≠ 4`), and the field shares its
universe so that a counterexample in {lit}`K⁴` can instantiate it. -/
def exercise_2B_8 {K : Type u} [Field K] :
    Decidable (∀ (W : Type u) [AddCommGroup W] [Module K W] (v : Fin 4 → W)
      (U : Submodule K W) (_ : IsBasis K v)
      (h0 : v 0 ∈ U) (h1 : v 1 ∈ U) (_ : v 2 ∉ U) (_ : v 3 ∉ U),
      IsBasis K (![⟨v 0, h0⟩, ⟨v 1, h1⟩] : Fin 2 → U)) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- use 4 dim, U is `x 3 = 0` (spanned by e0, e1, e2)
  -- v0 = e0, v1 = e1, but v2 = e2 + e3, v3 = e3,
  -- so v2 and v3 not in U, but v0, v1 don't span U, notably e2 not in it
  intro h
  exact exercise_2B_8_not_isBasis exercise_2B_8_mem₀ exercise_2B_8_mem₁
    (h (Fin 4 → K) exercise_2B_8_v exercise_2B_8_U exercise_2B_8_isBasis
      exercise_2B_8_mem₀ exercise_2B_8_mem₁ exercise_2B_8_notMem₂
      exercise_2B_8_notMem₃)

/-- 2B.9 -/
theorem exercise_2B_9 {m : ℕ} (v : Fin m → V) :
    IsBasis F v ↔
      IsBasis F (fun k : Fin m => ∑ i : Fin (k + 1), v ⟨i, by omega⟩) := by
  -- apply two exercises from 2A showing iff for LI and span.
  constructor
  · rintro ⟨hli, hspan⟩
    refine ⟨(LADR.Section_2A.exercise_2A_14 v).1 hli, ?_⟩
    rw [Spans, ← LADR.Section_2A.exercise_2A_3 v]
    exact hspan
  · rintro ⟨hli, hspan⟩
    refine ⟨(LADR.Section_2A.exercise_2A_14 v).2 hli, ?_⟩
    rw [Spans, LADR.Section_2A.exercise_2A_3 v]
    exact hspan

/-- 2B.10 -/
theorem exercise_2B_10 (U W : Submodule F V) (hUW : IsCompl U W)
    {m n : ℕ} (u : Fin m → U) (w : Fin n → W)
    (hu : IsBasis F u) (hw : IsBasis F w) :
    IsBasis F (Fin.append (fun i => (u i : V)) (fun i => (w i : V))) := by
  -- span is clear, by comp x = u + w, and u and w are spanned by the two bases.
  -- LI is clear, if sum of a_i u_i + sum of b_j w_j = 0
  -- then sum of a_i u_i = - sum of b_j w_j, but LHS is in U, RHS is in W
  -- so both are 0, and then a_i = 0 and b_j = 0 by LI of u and w.
  set v : Fin (m + n) → V :=
    Fin.append (fun i => (u i : V)) (fun i => (w i : V)) with hv
  have hvU : ∀ i : Fin m, v (Fin.castAdd n i) = (u i : V) := by
    intro i; rw [hv, Fin.append_left]
  have hvW : ∀ j : Fin n, v (Fin.natAdd m j) = (w j : V) := by
    intro j; rw [hv, Fin.append_right]
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_add] at hg
    simp only [hvU, hvW] at hg
    set a : V := ∑ i : Fin m, g (Fin.castAdd n i) • (u i : V) with ha
    set b : V := ∑ j : Fin n, g (Fin.natAdd m j) • (w j : V) with hb
    have haU : a ∈ U :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (u i).property
    have hbW : b ∈ W :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (w j).property
    have haW : a ∈ W := by
      rw [eq_neg_of_add_eq_zero_left hg]
      exact Submodule.neg_mem _ hbW
    have ha0 : a = 0 := by
      have hmem : a ∈ U ⊓ W := ⟨haU, haW⟩
      rw [hUW.inf_eq_bot] at hmem
      simpa using hmem
    have hb0 : b = 0 := by rw [ha0, zero_add] at hg; exact hg
    -- transport back into the subspaces, where linear independence lives
    have hu0 : ∑ i : Fin m, g (Fin.castAdd n i) • u i = 0 := by
      apply Subtype.ext
      simpa using ha0
    have hw0 : ∑ j : Fin n, g (Fin.natAdd m j) • w j = 0 := by
      apply Subtype.ext
      simpa using hb0
    have hliu := (Fintype.linearIndependent_iff.1 hu.1) _ hu0
    have hliw := (Fintype.linearIndependent_iff.1 hw.1) _ hw0
    exact Fin.addCases hliu hliw i
  · rw [Spans, eq_top_iff, ← hUW.sup_eq_top, sup_le_iff]
    constructor
    · intro x hx
      have hxU : (⟨x, hx⟩ : U) ∈ Submodule.span F (Set.range u) := by
        rw [hu.2]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxU
      obtain ⟨c, hc⟩ := hxU
      have hx' : x = ∑ i, c i • (u i : V) := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      rw [hx']
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Fin.castAdd n i, hvU i⟩)
    · intro x hx
      have hxW : (⟨x, hx⟩ : W) ∈ Submodule.span F (Set.range w) := by
        rw [hw.2]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hxW
      obtain ⟨c, hc⟩ := hxW
      have hx' : x = ∑ j, c j • (w j : V) := by
        have := congrArg Subtype.val hc
        simpa using this.symm
      rw [hx']
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨Fin.natAdd m j, hvW j⟩)

open LADR.Section_1B (Complexification exercise_1B_8) in
/-- 2B.11 (complexification: see {name}`LADR.Section_1B.exercise_1B_8`) -/
theorem exercise_2B_11 {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (v : Fin n → V) (hv : IsBasis ℝ v) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    IsBasis ℂ (fun i : Fin n => ((v i, 0) : Complexification V)) := by
  -- LI is clear ∑ a_i (v_i, 0) = ∑ (a_i.re • v_i, a_i.im • v_i) = 0, so both components are 0,
  -- and then a_i.re = 0 and a_i.im = 0 by LI of v.
  -- span given (x, y) ∈ V ⊕ V
  -- then x = ∑ a_i v_i, so (x, y) = ∑ a_i (v_i, 0) + (0, y)
  -- then (0, y) = i * (y, 0), but now (y, 0) = ∑ b_i (v_i, 0), so (0, y) = ∑ b_i i * (v_i, 0)
  -- so (x, y) = ∑ (a_i + i * b_i) (v_i, 0), so the new list spans.
  letI : Module ℂ (Complexification V) := exercise_1B_8 V
  -- `c • (u, 0) = (c.re • u, c.im • u)`, so the two components of a complex
  -- combination are the real combinations by `re` and by `im`
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hre : ∑ j, (g j).re • v j = 0 := by
      have h := congrArg Prod.fst hg
      simpa [Prod.fst_sum] using h
    have him : ∑ j, (g j).im • v j = 0 := by
      have h := congrArg Prod.snd hg
      simpa [Prod.snd_sum] using h
    exact Complex.ext (Fintype.linearIndependent_iff.1 hv.1 _ hre i)
      (Fintype.linearIndependent_iff.1 hv.1 _ him i)
  · rw [Spans, eq_top_iff]
    rintro ⟨x, y⟩ -
    rw [Submodule.mem_span_range_iff_exists_fun]
    have hx : x ∈ Submodule.span ℝ (Set.range v) := by rw [hv.2]; exact Submodule.mem_top
    have hy : y ∈ Submodule.span ℝ (Set.range v) := by rw [hv.2]; exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨fun i => (a i : ℂ) + (b i : ℂ) * Complex.I, ?_⟩
    refine Prod.ext ?_ ?_
    · simpa [Prod.fst_sum] using ha
    · simpa [Prod.snd_sum] using hb

end LADR.Section_2B
