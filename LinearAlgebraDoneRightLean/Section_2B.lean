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
{lit}`2B.2`; they are stated here and left as {lit}`sorry`, to be filled in
under that exercise. -/

/-! (b) The list {lit}`(1, 2), (3, 5)` is a basis of {lit}`F²`. Note its
length is 2, the same as the length of the standard basis of {lit}`F²`; this
is no coincidence (see 2.34). -/

example : IsBasis F (![![1, 2], ![3, 5]] : Fin 2 → Fin 2 → F) := by
  sorry  -- exercise 2B.2

/-! (c) The list {lit}`(1, 2, -4), (7, -5, 6)` is linearly independent in
{lit}`F³` but is *not* a basis: it fails to span. -/

example [CharZero F] :
    LinearIndependent F (![![1, 2, -4], ![7, -5, 6]] : Fin 2 → Fin 3 → F) := by
  sorry  -- exercise 2B.2

example [CharZero F] :
    ¬ Spans F (![![1, 2, -4], ![7, -5, 6]] : Fin 2 → Fin 3 → F) := by
  sorry  -- exercise 2B.2

/-! (d) The list {lit}`(1, 2), (3, 5), (4, 13)` spans {lit}`F²` but is not
a basis: it is linearly dependent. -/

example : Spans F (![![1, 2], ![3, 5], ![4, 13]] : Fin 3 → Fin 2 → F) := by
  sorry  -- exercise 2B.2

example : ¬ LinearIndependent F
    (![![1, 2], ![3, 5], ![4, 13]] : Fin 3 → Fin 2 → F) := by
  sorry  -- exercise 2B.2

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
  sorry  -- exercise 2B.2

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
  sorry  -- exercise 2B.2

/-! (g) The list {lit}`1, z, …, zᵐ` is the *standard basis* of {lit}`Pₘ(F)`. -/

example (m : ℕ) : IsBasis F
    (fun i : Fin (m + 1) =>
      (⟨Polynomial.X ^ (i : ℕ), by
        rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]
        exact_mod_cast i.isLt⟩ : Polynomial.degreeLT F (m + 1))) := by
  sorry  -- exercise 2B.2

/-! Note: {lit}`(7, 5), (-4, 9)` and {lit}`(1, 2), (3, 5)` are both bases of
{lit}`F²`. So {lit}`Fⁿ` has many bases beyond the standard one. (The second
list is example (b) above; the first is recorded here.) -/

example [CharZero F] : IsBasis F (![![7, 5], ![-4, 9]] : Fin 2 → Fin 2 → F) := by
  sorry  -- exercise 2B.2

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

/-- 2B.1: "Find all vector spaces that have exactly one basis."

A basis in the book's sense is a *list*, so "a basis of {lit}`V`" is a pair
{lit}`⟨n, v : Fin n → V⟩` and "exactly one basis" is uniqueness of that pair.
Quantifying instead over bases of a *fixed* length would be vacuously true for
an infinite-dimensional {lit}`V`, which has no {lit}`Fin n`-indexed basis at
all. The hypothesis {lit}`hF` — some scalar is neither {lit}`0` nor {lit}`1` —
holds for Axler's {lit}`𝐅 = ℝ, ℂ` and is needed: over {lit}`𝔽₂` the space
{lit}`𝔽₂` has {lit}`(1)` as its only basis. -/
theorem exercise_2B_1 (hF : ∃ c : F, c ≠ 0 ∧ c ≠ 1) :
    (∃! p : (n : ℕ) × (Fin n → V), IsBasis F p.2) ↔ Subsingleton V := by
  sorry

/-! 2B.2: verify the assertions in Example 2.27 (stated as {lit}`example`s
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

/-- 2B.3(a) The student supplies a basis of {lit}`U` (replacing the
{lit}`sorry`) and then proves that it is one. -/
def exercise_2B_3a_v : Fin 3 → exercise_2B_3_U := sorry

/-- 2B.3(a) -/
theorem exercise_2B_3a : IsBasis ℝ exercise_2B_3a_v := by
  sorry

/-- 2B.3(b) The student supplies an extension of the basis from (a) to a
basis of {lit}`ℝ⁵` (replacing the {lit}`sorry`). -/
def exercise_2B_3b_v : Fin 5 → (Fin 5 → ℝ) := sorry

/-- 2B.3(b) -/
theorem exercise_2B_3b : IsBasis ℝ exercise_2B_3b_v ∧
    ∀ i : Fin 3, exercise_2B_3b_v (i.castLE (by norm_num)) =
      (exercise_2B_3a_v i : Fin 5 → ℝ) := by
  sorry

/-- 2B.3(c) The student supplies a complement {lit}`W` of {lit}`U` in
{lit}`ℝ⁵` (replacing the {lit}`sorry`). -/
def exercise_2B_3c_W : Submodule ℝ (Fin 5 → ℝ) := sorry

/-- 2B.3(c) -/
theorem exercise_2B_3c : IsCompl exercise_2B_3_U exercise_2B_3c_W := by
  sorry

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

/-- 2B.4(a) The student supplies a basis of {lit}`U` (replacing the
{lit}`sorry`) and then proves that it is one. -/
def exercise_2B_4a_v : Fin 3 → exercise_2B_4_U := sorry

/-- 2B.4(a) -/
theorem exercise_2B_4a : IsBasis ℂ exercise_2B_4a_v := by
  sorry

/-- 2B.4(b) The student supplies an extension of the basis from (a) to a
basis of {lit}`ℂ⁵` (replacing the {lit}`sorry`). -/
def exercise_2B_4b_v : Fin 5 → (Fin 5 → ℂ) := sorry

/-- 2B.4(b) -/
theorem exercise_2B_4b : IsBasis ℂ exercise_2B_4b_v ∧
    ∀ i : Fin 3, exercise_2B_4b_v (i.castLE (by norm_num)) =
      (exercise_2B_4a_v i : Fin 5 → ℂ) := by
  sorry

/-- 2B.4(c) The student supplies a complement {lit}`W` of {lit}`U` in
{lit}`ℂ⁵` (replacing the {lit}`sorry`). -/
def exercise_2B_4c_W : Submodule ℂ (Fin 5 → ℂ) := sorry

/-- 2B.4(c) -/
theorem exercise_2B_4c : IsCompl exercise_2B_4_U exercise_2B_4c_W := by
  sorry

/-- 2B.5 -/
theorem exercise_2B_5 [Module.Finite F V] (U W : Submodule F V) (hUW : U ⊔ W = ⊤) :
    ∃ (n : ℕ) (v : Fin n → V), IsBasis F v ∧
      ∀ i, (v i ∈ U) ∨ (v i ∈ W) := by
  sorry

/-- 2B.6 -/
def exercise_2B_6 :
    Decidable (∀ (p : Fin 4 → Polynomial.degreeLT F 4),
      (∀ i, (p i : Polynomial F).degree ≠ 2) → ¬ IsBasis F p) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  sorry

/-- 2B.7 -/
theorem exercise_2B_7 (v : Fin 4 → V) (hv : IsBasis F v) :
    IsBasis F (![v 0 + v 1, v 1 + v 2, v 2 + v 3, v 3] : Fin 4 → V) := by
  sorry

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
  sorry

/-- 2B.9 -/
theorem exercise_2B_9 {m : ℕ} (v : Fin m → V) :
    IsBasis F v ↔
      IsBasis F (fun k : Fin m => ∑ i : Fin (k + 1), v ⟨i, by omega⟩) := by
  sorry

/-- 2B.10 -/
theorem exercise_2B_10 (U W : Submodule F V) (hUW : IsCompl U W)
    {m n : ℕ} (u : Fin m → U) (w : Fin n → W)
    (hu : IsBasis F u) (hw : IsBasis F w) :
    IsBasis F (Fin.append (fun i => (u i : V)) (fun i => (w i : V))) := by
  sorry

open LADR.Section_1B (Complexification exercise_1B_8) in
/-- 2B.11 (complexification: see {name}`LADR.Section_1B.exercise_1B_8`) -/
theorem exercise_2B_11 {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (v : Fin n → V) (hv : IsBasis ℝ v) :
    letI : Module ℂ (Complexification V) := exercise_1B_8 V
    IsBasis ℂ (fun i : Fin n => ((v i, 0) : Complexification V)) := by
  sorry

end LADR.Section_2B
