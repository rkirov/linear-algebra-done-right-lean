import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import Mathlib.Tactic.TFAE
import LinearAlgebraDoneRightLean.Section_1C
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3E: Products and Quotients of Vector Spaces
-/

namespace LADR.Section_3E

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open LADR.Section_1C (IsDirectSum)
open Module (Finite finrank)

variable {F : Type*} [Field F]

/-! 3.87 Definition: product of vector spaces

For a family of vector spaces {lit}`V₁, …, Vₘ` over {lit}`F`, the product
{lit}`V₁ × ⋯ × Vₘ` is the set of all {lit}`m`-tuples. In Lean we encode this
as the dependent function type {lit}`(i : Fin m) → V i`, with pointwise
addition and scalar multiplication. -/

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] : Type _ := (i : Fin m) → V i

-- An element of the product is an {lit}`m`-tuple: it picks one component
-- {lit}`V i` for each index {lit}`i`. Here is the zero tuple.
example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] : (i : Fin m) → V i := fun i => (0 : V i)

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] (u v : (i : Fin m) → V i) (i : Fin m) :
    (u + v) i = u i + v i := rfl

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] (γ : F) (v : (i : Fin m) → V i) (i : Fin m) :
    (γ • v) i = γ • v i := rfl

/-! 3.88 Example: product of {lit}`𝒫₅(ℝ)` and {lit}`ℝ³`. -/

-- For a product of just two vector spaces we use Lean's binary product
-- type {lit}`×` ({name}`Prod`) rather than the dependent function type;
-- it likewise carries pointwise {name}`AddCommGroup` and {name}`Module`
-- instances automatically.

open Polynomial in
/-- 3.88, worked. In {lit}`𝒫₅(ℝ) × ℝ³`, the sum
{lit}`(5 − 6x + 4x², (3, 8, 7)) + (x + 9x⁵, (2, 2, 2))`
equals {lit}`(5 − 5x + 4x² + 9x⁵, (5, 10, 9))`. -/
example :
    ((⟨5 - 6 * X + 4 * X ^ 2, by rw [mem_degreeLT]; compute_degree!⟩ :
        degreeLT ℝ 6), (![3, 8, 7] : Fin 3 → ℝ)) +
    (⟨X + 9 * X ^ 5, by rw [mem_degreeLT]; compute_degree!⟩, (![2, 2, 2] : Fin 3 → ℝ))
      = (⟨5 - 5 * X + 4 * X ^ 2 + 9 * X ^ 5, by rw [mem_degreeLT]; compute_degree!⟩,
          (![5, 10, 9] : Fin 3 → ℝ)) := by
  refine Prod.ext ?_ ?_
  · ext1
    simp only [Prod.fst_add, Submodule.coe_add]
    ring
  · funext i; fin_cases i <;> norm_num

open Polynomial in
/-- 3.88, worked (scalar multiple). {lit}`2 · (5 − 6x + 4x², (3, 8, 7))`
equals {lit}`(10 − 12x + 8x², (6, 16, 14))`. -/
example :
    (2 : ℝ) • ((⟨5 - 6 * X + 4 * X ^ 2, by rw [mem_degreeLT]; compute_degree!⟩ :
        degreeLT ℝ 6), (![3, 8, 7] : Fin 3 → ℝ))
      = (⟨10 - 12 * X + 8 * X ^ 2, by rw [mem_degreeLT]; compute_degree!⟩,
          (![6, 16, 14] : Fin 3 → ℝ)) := by
  refine Prod.ext ?_ ?_
  · ext1
    simp only [Prod.smul_fst, SetLike.val_smul, Algebra.smul_def, map_ofNat]
    ring
  · funext i; fin_cases i <;> norm_num

/-! 3.89 The product of vector spaces is a vector space. Mathlib derives
this automatically ({name}`inferInstance`), but to see what is going on we
build the {name}`Module` structure by hand: scalar multiplication is
pointwise, and each axiom reduces to the same axiom on every component
{lit}`V i`. -/

-- A vector space also needs its abelian group. The {name}`Module` class is
-- stated relative to an existing {name}`AddCommGroup`, so the construction
-- below assumes it; mathlib supplies it pointwise ({name}`Pi.addCommGroup`),
-- with negation and zero computed coordinatewise.
example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)] :
    AddCommGroup ((i : Fin m) → V i) := inferInstance

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    (v : (i : Fin m) → V i) (i : Fin m) : (-v) i = -(v i) := rfl

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    (i : Fin m) : (0 : (i : Fin m) → V i) i = 0 := rfl

example {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] : Module F ((i : Fin m) → V i) where
  smul a v := fun i => a • v i
  one_smul v := by funext i; exact one_smul F (v i)
  mul_smul a b v := by funext i; exact mul_smul a b (v i)
  smul_zero a := by funext i; exact smul_zero a
  smul_add a u v := by funext i; exact smul_add a (u i) (v i)
  add_smul a b v := by funext i; exact add_smul a b (v i)
  zero_smul v := by funext i; exact zero_smul F (v i)

/-! 3.90 {lit}`ℝ² × ℝ³ ≠ ℝ⁵` but {lit}`ℝ² × ℝ³ ≃ ℝ⁵` -/

/-- The isomorphism {lit}`ℝ² × ℝ³ ≃ₗ[ℝ] ℝ⁵`, given by concatenating the
two lists via {name}`Fin.append`. -/
def prod_two_three_equiv :
    ((Fin 2 → ℝ) × (Fin 3 → ℝ)) ≃ₗ[ℝ] (Fin 5 → ℝ) where
  toFun x := Fin.append x.1 x.2
  invFun y := (fun i => y (Fin.castAdd 3 i), fun j => y (Fin.natAdd 2 j))
  map_add' x y := by
    funext i
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  map_smul' a x := by
    funext i
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  left_inv x := by
    ext1
    · funext i; exact Fin.append_left x.1 x.2 i
    · funext j; exact Fin.append_right x.1 x.2 j
  right_inv y := by
    funext i
    refine Fin.addCases (fun p => ?_) (fun q => ?_) i
    · exact Fin.append_left _ _ p
    · exact Fin.append_right _ _ q

/-! 3.91 Example: a basis of {lit}`𝒫₂(ℝ) × ℝ²` of length 5. -/

open Polynomial in
/-- The product basis of {lit}`𝒫₂(ℝ) × ℝ²`, obtained from the monomial basis
{lit}`1, x, x²` of {lit}`𝒫₂(ℝ) = degreeLT ℝ 3` and the standard basis of
{lit}`ℝ²`, reindexed by {name}`finSumFinEquiv` to {lit}`Fin 5`. -/
noncomputable def basis_3_91 :
    Module.Basis (Fin 5) ℝ (Polynomial.degreeLT ℝ 3 × (Fin 2 → ℝ)) :=
  ((Polynomial.degreeLT.basis ℝ 3).prod (Pi.basisFun ℝ (Fin 2))).reindex
    finSumFinEquiv

/-- 3.91. The five vectors of {name}`basis_3_91` form a basis in the book's
sense. Its length, 5, is {lit}`dim 𝒫₂(ℝ) + dim ℝ² = 3 + 2`. -/
example : IsBasis ℝ ⇑basis_3_91 :=
  ⟨basis_3_91.linearIndependent, basis_3_91.span_eq⟩

-- The five vectors are exactly Axler's list. The first three come from the
-- polynomial factor: {name}`degreeLT.basis` {lit}`ℝ 3 i` is the monomial
-- {lit}`xⁱ` (see {name}`Polynomial.degreeLT.basis_val`), giving
-- {lit}`(1, 0), (x, 0), (x², 0)`.
open Polynomial in
example (i : Fin 3) :
    basis_3_91 (finSumFinEquiv (m := 3) (n := 2) (Sum.inl i)) =
      (degreeLT.basis ℝ 3 i, 0) := by
  simp [basis_3_91, Module.Basis.prod_apply]

-- The last two come from the {lit}`ℝ²` factor: {name}`Pi.single` {lit}`j 1`
-- are the standard basis vectors, giving {lit}`(0, (1, 0)), (0, (0, 1))`.
open Polynomial in
example (j : Fin 2) :
    basis_3_91 (finSumFinEquiv (m := 3) (n := 2) (Sum.inr j)) =
      (0, Pi.single j 1) := by
  simp [basis_3_91, Module.Basis.prod_apply, Pi.basisFun_apply]

/-! 3.92 The dimension of a product is the sum of dimensions. -/

theorem finrank_prod {m : ℕ} (V : Fin m → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [∀ i, Module.Finite F (V i)] :
    finrank F ((i : Fin m) → V i) = ∑ i, finrank F (V i) := by
  -- Axler 3.92: take a basis of each factor {lit}`V i` and pad it with zeros
  -- in the other slots; together these vectors span and are linearly
  -- independent, hence form a basis of the product. Its size — and so the
  -- dimension — is the sum of the factor dimensions.
  -- A basis of each factor {lit}`V i`, of size {lit}`finrank F (V i)`.
  let B : (i : Fin m) → Module.Basis (Fin (finrank F (V i))) F (V i) := fun i =>
    Module.finBasis F (V i)
  -- The padded vectors: {lit}`v ⟨i, k⟩` is the basis vector {lit}`B i k`
  -- placed in slot {lit}`i`, with zeros in every other slot.
  let v : (Σ i : Fin m, Fin (finrank F (V i))) → ((i : Fin m) → V i) :=
    fun ji => Pi.single ji.1 (B ji.1 ji.2)
  have hvdef : ∀ ji, v ji = Pi.single ji.1 (B ji.1 ji.2) := fun _ => rfl
  -- Reading off slot {lit}`i` of a combination kills every term whose vector
  -- lives in another slot, leaving the combination inside {lit}`V i`.
  have hcoord : ∀ (c : (Σ i : Fin m, Fin (finrank F (V i))) → F) (i : Fin m),
      (∑ jk, c jk • v jk) i = ∑ k, c ⟨i, k⟩ • B i k := by
    intro c i
    rw [Finset.sum_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun i' _ hne => Finset.sum_eq_zero fun k' _ => by
          simp [hvdef, Pi.single_eq_of_ne (Ne.symm hne)])]
    exact Finset.sum_congr rfl fun k' _ => by simp [hvdef, Pi.single_eq_same]
  -- Linear independence: a combination summing to zero is zero in each slot,
  -- and {lit}`B i` is independent.
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc ji
    obtain ⟨i, k⟩ := ji
    have key := (B i).linearIndependent
    rw [Fintype.linearIndependent_iff] at key
    refine key (fun k' => c ⟨i, k'⟩) ?_ k
    have h := hcoord c i
    rw [hc] at h
    simpa using h.symm
  -- Spanning: every {lit}`x` is recovered as the combination given by the
  -- coordinates of each {lit}`x i` in {lit}`B i`.
  have hsp : ⊤ ≤ Submodule.span F (Set.range v) := by
    intro x _
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun ji => (B ji.1).repr (x ji.1) ji.2, ?_⟩
    funext i
    rw [hcoord]
    exact (B i).sum_repr (x i)
  -- These vectors form a basis; counting them gives the result.
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_sigma]
  simp

variable {V : Type*} [AddCommGroup V] [Module F V]

/-! 3.93 The map {lit}`Γ : V₁ × ⋯ × Vₘ → V₁ + ⋯ + Vₘ` sending
{lit}`(v₁, …, vₘ) ↦ v₁ + ⋯ + vₘ`. The sum is a direct sum iff {lit}`Γ` is
injective. -/

/-- The underlying {lit}`V`-valued sum map {lit}`(v₁, …, vₘ) ↦ v₁ + ⋯ + vₘ`.
Its image is the sum subspace (see {lit}`Γ₀_range_eq`); the book's {lit}`Γ`
below is this map with its codomain cut down to that subspace. -/
private def Γ₀ {m : ℕ} (V_sub : Fin m → Submodule F V) :
    ((i : Fin m) → ↥(V_sub i)) →ₗ[F] V where
  toFun u := ∑ i, ((u i : V))
  map_add' u v := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [Pi.add_apply]
  map_smul' a u := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show ((a • u i : V_sub i) : V) = a • (u i : V)
    rw [Submodule.coe_smul_of_tower]

/-- The range of {lit}`Γ₀ V_sub` is the sum of subspaces {lit}`∑ V_sub i`. -/
private theorem Γ₀_range_eq {m : ℕ} (V_sub : Fin m → Submodule F V) :
    LinearMap.range (Γ₀ V_sub) = ∑ i, V_sub i := by
  classical
  apply le_antisymm
  · -- {lit}`range Γ₀ ⊆ ∑ V_sub i`.
    rintro _ ⟨u, rfl⟩
    show (∑ i, ((u i : V))) ∈ (∑ i : Fin m, V_sub i : Submodule F V)
    refine Submodule.sum_mem _ (fun i _ => ?_)
    -- {lit}`(u i : V) ∈ V_sub i ≤ ∑ V_sub i`.
    exact (Finset.single_le_sum (f := V_sub) (fun j _ => bot_le)
      (Finset.mem_univ i)) (u i).property
  · -- {lit}`∑ V_sub i ⊆ range Γ₀`: each {lit}`V_sub i ⊆ range Γ₀`,
    -- and range is a submodule.
    have h_each : ∀ i, V_sub i ≤ LinearMap.range (Γ₀ V_sub) := by
      intro i v hv
      classical
      let u : (j : Fin m) → V_sub j := fun j =>
        if h : j = i then h ▸ (⟨v, hv⟩ : V_sub i) else 0
      refine ⟨u, ?_⟩
      show ∑ j, ((u j : V_sub j) : V) = v
      rw [Finset.sum_eq_single i]
      · show ((u i : V_sub i) : V) = v
        simp [u]
      · intros j _ hji
        show ((u j : V_sub j) : V) = 0
        simp [u, hji]
      · intro h; exact absurd (Finset.mem_univ i) h
    exact Finset.sum_induction (f := V_sub)
      (p := fun U => U ≤ LinearMap.range (Γ₀ V_sub))
      (fun _ _ ha hb => sup_le ha hb) bot_le (fun i _ => h_each i)

/-- The {lit}`Γ` map from Axler 3.93. Following the book, its codomain is the
sum subspace {lit}`V₁ + ⋯ + Vₘ` (a subspace of {lit}`V`), not all of
{lit}`V`. It is the {name}`LinearMap.codRestrict` of {name}`Γ₀` to that
subspace, where each {lit}`(u i : V) ∈ V_sub i ≤ ∑ V_sub i`. -/
def Γ {m : ℕ} (V_sub : Fin m → Submodule F V) :
    ((i : Fin m) → ↥(V_sub i)) →ₗ[F] ↥(∑ i, V_sub i) :=
  LinearMap.codRestrict _ (Γ₀ V_sub) fun u => by
    show (∑ i, ((u i : V))) ∈ ∑ i, V_sub i
    exact Submodule.sum_mem _ fun i _ =>
      (Finset.single_le_sum (f := V_sub) (fun j _ => bot_le)
        (Finset.mem_univ i)) (u i).property

@[avoiding Submodule.directSum_iff_internalDirectSum]
theorem directSum_iff_gamma_injective {m : ℕ}
    (V_sub : Fin m → Submodule F V) :
    IsDirectSum V_sub ↔ Function.Injective (Γ V_sub) := by
  -- {lit}`Γ` and {lit}`Γ₀` have the same fibers (the inclusion of the
  -- subspace is injective), so injectivity is the direct-sum condition.
  constructor
  · intro hds u v huv
    exact hds u v (congrArg Subtype.val huv)
  · intro hinj u v huv
    exact hinj (Subtype.ext huv)

/-! 3.94 A sum is a direct sum iff dimensions add up. -/

/-- {lit}`Γ` is surjective: every element of the sum {lit}`V₁ + ⋯ + Vₘ` is
{lit}`v₁ + ⋯ + vₘ` for some {lit}`vᵢ ∈ Vᵢ`. -/
private theorem Γ_range_top {m : ℕ} (V_sub : Fin m → Submodule F V) :
    LinearMap.range (Γ V_sub) = ⊤ := by
  rw [LinearMap.range_eq_top]
  rintro ⟨w, hw⟩
  rw [← Γ₀_range_eq] at hw
  obtain ⟨u, hu⟩ := hw
  exact ⟨u, Subtype.ext hu⟩

theorem directSum_iff_finrank_add [Finite F V] {m : ℕ}
    (V_sub : Fin m → Submodule F V) [∀ i, Module.Finite F (V_sub i)] :
    IsDirectSum V_sub ↔
      finrank F ↥(∑ i, V_sub i : Submodule F V) =
        ∑ i, finrank F (V_sub i) := by
  -- direct sum ↔ Γ injective ↔ finrank ker Γ = 0. Since Γ is onto the sum
  -- subspace, the rank–nullity identity reads
  -- {lit}`finrank ker Γ + finrank (∑ V_sub) = ∑ finrank (V_sub i)`.
  rw [directSum_iff_gamma_injective]
  rw [LADR.Section_3B.injective_iff_ker_eq_bot]
  have h_FTL := LADR.Section_3B.finrank_ker_add_finrank_range (Γ V_sub)
  rw [Γ_range_top, finrank_top,
    finrank_prod (V := fun i => (V_sub i : Type _))] at h_FTL
  constructor
  · intro hker_bot
    rw [hker_bot, finrank_bot] at h_FTL
    omega
  · intro hdim
    rw [← hdim] at h_FTL
    have : finrank F (LinearMap.ker (Γ V_sub)) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at this
    exact this

/-! Quotient Spaces. -/

/-! 3.95 Notation {lit}`v + U`. For {lit}`v ∈ V` and {lit}`U ⊆ V`, the
translate is the set {lit}`{v + u : u ∈ U}`. -/

/-- The translate {lit}`v + U` as a {lit}`Set V`. -/
def translate (v : V) (U : Set V) : Set V :=
  {w : V | ∃ u ∈ U, v + u = w}

example (v : V) (U : Set V) (x : V) :
    x ∈ translate v U ↔ ∃ u ∈ U, v + u = x := Iff.rfl

/-! 3.96 Example. Let {lit}`U = {(x, 2x) : x ∈ ℝ}`, the line in {lit}`ℝ²`
through the origin with slope 2. Then {lit}`(17, 20) + U` is the line through
{lit}`(17, 20)` with slope 2, i.e. {lit}`{(x, y) : y = 2x − 14}`. -/

/-- The slope-2 line through the origin in {lit}`ℝ²`, {lit}`{(x, 2x)}`, as a
subspace. -/
def slope2 : Submodule ℝ (ℝ × ℝ) where
  carrier := {p | p.2 = 2 * p.1}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add] at *
    rw [ha, hb]; ring
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
    rw [ha]; ring

example : translate ((17, 20) : ℝ × ℝ) (slope2 : Set (ℝ × ℝ)) =
    {p : ℝ × ℝ | p.2 = 2 * p.1 - 14} := by
  ext p
  simp only [translate, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    -- {lit}`u ∈ U` means {lit}`u.2 = 2 * u.1`; read off the second coordinate.
    show 20 + u.2 = 2 * (17 + u.1) - 14
    rw [show u.2 = 2 * u.1 from hu]; ring
  · intro hp
    -- Translate back by {lit}`(17, 20)`: the witness is {lit}`p - (17, 20)`.
    refine ⟨p - (17, 20), ?_, by abel⟩
    show p.2 - 20 = 2 * (p.1 - 17)
    rw [hp]; ring

/-! 3.97 Definition: a translate of {lit}`U` is a set of the form
{lit}`v + U`. -/

def IsTranslate (U : Set V) (A : Set V) : Prop :=
  ∃ v : V, A = translate v U

/-! 3.98 Example: translates. For {lit}`U` the slope-2 line
{lit}`{(x, 2x)}` of 3.96, the translates of {lit}`U` are exactly the lines in
{lit}`ℝ²` of slope 2 — i.e. the sets {lit}`{(x, y) : y = 2x + c}` for
{lit}`c ∈ ℝ`. (More generally, the translates of any line in {lit}`ℝ²` are
the lines parallel to it; the translates of a plane in {lit}`ℝ³` are the
planes parallel to it.) -/

/-- Membership in a translate of {name}`slope2`: {lit}`v + U` is the slope-2
line through {lit}`v`, with intercept {lit}`v.2 − 2·v.1`. -/
private theorem mem_translate_slope2 (v p : ℝ × ℝ) :
    p ∈ translate v (slope2 : Set (ℝ × ℝ)) ↔ p.2 = 2 * p.1 + (v.2 - 2 * v.1) := by
  simp only [translate, SetLike.mem_coe, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, rfl⟩
    show v.2 + u.2 = 2 * (v.1 + u.1) + (v.2 - 2 * v.1)
    rw [show u.2 = 2 * u.1 from hu]; ring
  · intro hp
    refine ⟨p - v, ?_, by abel⟩
    show (p - v).2 = 2 * (p - v).1
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [hp]; ring

example (A : Set (ℝ × ℝ)) :
    IsTranslate (slope2 : Set (ℝ × ℝ)) A ↔
      ∃ c : ℝ, A = {p : ℝ × ℝ | p.2 = 2 * p.1 + c} := by
  constructor
  · -- A translate {lit}`v + U` is the slope-2 line with intercept
    -- {lit}`v.2 − 2·v.1`.
    rintro ⟨v, rfl⟩
    exact ⟨v.2 - 2 * v.1, by ext p; rw [mem_translate_slope2]; rfl⟩
  · -- The slope-2 line of intercept {lit}`c` is the translate by {lit}`(0, c)`.
    rintro ⟨c, rfl⟩
    refine ⟨(0, c), ?_⟩
    ext p
    rw [mem_translate_slope2]
    simp

/-! 3.99 Definition: quotient space {lit}`V/U` — mathlib's {name}`HasQuotient`
provides {lit}`V ⧸ U` as the set of translates. -/

example (U : Submodule F V) : Type _ := V ⧸ U

example (U : Submodule F V) (v : V) : V ⧸ U := U.mkQ v

/-! 3.100 Example: quotient spaces. For {lit}`U = {(x, 2x)}` of 3.96,
{lit}`ℝ²/U` is the set of all lines in {lit}`ℝ²` with slope 2. We exhibit the
bijection between {lit}`ℝ²/U` and those lines. (Likewise, modulo a line resp.
plane through the origin in {lit}`ℝ³`, the quotient is the parallel lines
resp. planes.) -/

/-- The "intercept" functional {lit}`(x, y) ↦ y − 2x`. Its kernel is
{name}`slope2`, so it descends to an isomorphism {lit}`ℝ²/U ≃ ℝ`. -/
def intercept : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun p := p.2 - 2 * p.1
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c a := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

theorem ker_intercept : LinearMap.ker intercept = slope2 := by
  ext p
  rw [LinearMap.mem_ker]
  show p.2 - 2 * p.1 = 0 ↔ p.2 = 2 * p.1
  rw [sub_eq_zero]

theorem intercept_surjective : Function.Surjective intercept :=
  fun c => ⟨(0, c), by simp [intercept]⟩

/-- {lit}`ℝ²/U ≃ₗ ℝ`: each class {lit}`v + U` is determined by its intercept
{lit}`v.2 − 2·v.1` (first isomorphism theorem applied to {name}`intercept`). -/
noncomputable def quot_slope2_equiv_real : ((ℝ × ℝ) ⧸ slope2) ≃ₗ[ℝ] ℝ :=
  (Submodule.quotEquivOfEq slope2 (LinearMap.ker intercept) ker_intercept.symm).trans
    (intercept.quotKerEquivOfSurjective intercept_surjective)

/-- The slope-2 line in {lit}`ℝ²` with intercept {lit}`c`. -/
def lineOf (c : ℝ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 = 2 * p.1 + c}

theorem lineOf_injective : Function.Injective lineOf := by
  intro c d h
  have h0 : ((0 : ℝ), c) ∈ lineOf d := by rw [← h]; show c = 2 * 0 + c; ring
  simpa [lineOf] using h0

/-- 3.100. The bijection {lit}`ℝ²/U ≃ {slope-2 lines}`: each class is sent to
the line {lit}`v + U`, parametrized by its intercept. -/
noncomputable def quot_slope2_equiv_lines :
    ((ℝ × ℝ) ⧸ slope2) ≃ {A : Set (ℝ × ℝ) // ∃ c : ℝ, A = lineOf c} :=
  quot_slope2_equiv_real.toEquiv.trans <|
    (Equiv.ofInjective lineOf lineOf_injective).trans
      (Equiv.setCongr (by
        ext A
        exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩))

/-! 3.101 Two translates of a subspace are equal or disjoint. Axler states
this as a chain of equivalences, which we package as a single
{name}`List.TFAE`: the translates {lit}`v + U` and {lit}`w + U` are equal iff
they meet iff {lit}`v − w ∈ U` iff {lit}`v` and {lit}`w` are equal in the
quotient {lit}`V/U`. -/

theorem translate_tfae (U : Submodule F V) (v w : V) :
    List.TFAE
      [ v - w ∈ U,
        translate v (U : Set V) = translate w U,
        (translate v (U : Set V) ∩ translate w U).Nonempty,
        (U.mkQ v : V ⧸ U) = U.mkQ w ] := by
  tfae_have 1 → 2 := by
    -- {lit}`v − w ∈ U`: every {lit}`v + u` is {lit}`w + ((v − w) + u)` and
    -- vice versa, so the two translates coincide.
    intro hvw
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(v - w) + u, U.add_mem hvw hu, by abel⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(w - v) + u, U.add_mem ?_ hu, by abel⟩
      rw [show w - v = -(v - w) from by abel]
      exact U.neg_mem hvw
  tfae_have 2 → 3 := by
    -- Equal translates obviously meet: both contain {lit}`v`.
    intro h
    exact ⟨v, ⟨0, U.zero_mem, by simp⟩, h ▸ ⟨0, U.zero_mem, by simp⟩⟩
  tfae_have 3 → 1 := by
    -- A common point {lit}`v + u₁ = w + u₂` gives {lit}`v − w = u₂ − u₁ ∈ U`.
    rintro ⟨x, ⟨u₁, hu₁, hxv⟩, ⟨u₂, hu₂, hxw⟩⟩
    have hdiff : v - w = u₂ - u₁ := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm u₂ w]; exact hxv.trans hxw.symm
    rw [hdiff]; exact U.sub_mem hu₂ hu₁
  tfae_have 1 ↔ 4 := (Submodule.Quotient.eq U).symm
  tfae_finish

/-! 3.102 Addition and scalar multiplication on {lit}`V/U`. Axler defines
{lit}`(v + U) + (w + U) = (v + w) + U` and {lit}`λ(v + U) = (λv) + U`; in
mathlib these are the defining equations, true by {name}`rfl`. The real
content is that the operations are *well defined*: the result does not depend
on which representatives are chosen. -/

-- The defining equations (definitional in mathlib).
example (U : Submodule F V) (v w : V) :
    (U.mkQ v + U.mkQ w : V ⧸ U) = U.mkQ (v + w) := rfl

example (U : Submodule F V) (γ : F) (v : V) :
    (γ • (U.mkQ v : V ⧸ U)) = U.mkQ (γ • v) := rfl

-- Well-definedness of addition: replacing {lit}`v, w` by other
-- representatives {lit}`v', w'` of the same cosets leaves {lit}`(v + w) + U`
-- unchanged. With the quotient map {name}`Submodule.mkQ` this is just its
-- additivity combined with {lit}`v + U = v' + U` and {lit}`w + U = w' + U`.
example (U : Submodule F V) (v v' w w' : V)
    (hv : (U.mkQ v : V ⧸ U) = U.mkQ v') (hw : (U.mkQ w : V ⧸ U) = U.mkQ w') :
    (U.mkQ (v + w) : V ⧸ U) = U.mkQ (v' + w') := by
  rw [map_add, map_add, hv, hw]

-- Well-definedness of scalar multiplication: homogeneity of {name}`Submodule.mkQ`.
example (U : Submodule F V) (γ : F) (v v' : V)
    (hv : (U.mkQ v : V ⧸ U) = U.mkQ v') :
    (U.mkQ (γ • v) : V ⧸ U) = U.mkQ (γ • v') := by
  rw [map_smul, map_smul, hv]

/-! 3.103 {lit}`V/U` is a vector space (automatic in mathlib). -/

example (U : Submodule F V) : Module F (V ⧸ U) := inferInstance

/-! 3.104 Definition: quotient map {lit}`π : V → V/U`, {lit}`v ↦ v + U`.
Mathlib packages it as {name}`Submodule.mkQ`; here we build it by hand to
exhibit its linearity — both axioms hold by {name}`rfl`, since the quotient
operations are defined on representatives (3.102). -/

def quotientMap (U : Submodule F V) : V →ₗ[F] V ⧸ U where
  toFun := Submodule.Quotient.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

example (U : Submodule F V) : quotientMap U = U.mkQ := rfl

/-! 3.105 Dimension of the quotient space. -/

@[avoiding Submodule.finrank_quotient, finrank_quotient_add_finrank]
theorem finrank_quotient [Finite F V] (U : Submodule F V) :
    finrank F (V ⧸ U) = finrank F V - finrank F U := by
  -- Axler 3.105: apply the fundamental theorem of linear maps to the quotient
  -- map {lit}`π = U.mkQ`. Its kernel is {lit}`U` ({name}`Submodule.ker_mkQ`)
  -- and it is surjective ({name}`Submodule.range_mkQ`), so rank–nullity reads
  -- {lit}`dim U + dim (V/U) = dim V`.
  have h := LADR.Section_3B.finrank_ker_add_finrank_range U.mkQ
  rw [Submodule.ker_mkQ, Submodule.range_mkQ, finrank_top] at h
  omega

/-! 3.106 Notation {lit}`T̃ : V/(null T) → W`. Mathlib's {name}`Submodule.liftQ`
is more general: for *any* submodule {lit}`U ≤ ker T` it factors {lit}`T`
through the quotient as {lit}`V/U →ₗ W` (the hypothesis {lit}`U ≤ ker T` is
exactly what makes the lift well defined). Axler's {lit}`T̃` is the special
case {lit}`U = ker T`, so we must pass the kernel explicitly -/

variable {W : Type*} [AddCommGroup W] [Module F W]

noncomputable def Ttilde (T : V →ₗ[F] W) : V ⧸ LinearMap.ker T →ₗ[F] W :=
  Submodule.liftQ (LinearMap.ker T) T (le_refl _)

example (T : V →ₗ[F] W) (v : V) :
    Ttilde T ((LinearMap.ker T).mkQ v) = T v := rfl

-- Well-definedness of {lit}`T̃`: the rule {lit}`v + null T ↦ T v` is
-- independent of the representative. If {lit}`v, v'` give the same coset then
-- {lit}`v − v' ∈ null T`, so {lit}`T v = T v'`. (This is exactly the side
-- condition that {name}`Submodule.liftQ` discharges when building {name}`Ttilde`.)
example (T : V →ₗ[F] W) (v v' : V)
    (h : (LinearMap.ker T).mkQ v = (LinearMap.ker T).mkQ v') : T v = T v' := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  -- h : v − v' ∈ null T
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  exact h

/-! 3.107 Properties of {lit}`T̃`. -/

/-- (a) {lit}`T̃ ∘ π = T`. -/
theorem Ttilde_comp_mkQ (T : V →ₗ[F] W) :
    Ttilde T ∘ₗ (LinearMap.ker T).mkQ = T := by
  ext v; rfl

/-- (b) {lit}`T̃` is injective. -/
theorem Ttilde_injective (T : V →ₗ[F] W) : Function.Injective (Ttilde T) := by
  rw [LADR.Section_3B.injective_iff_ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hTv : T v = 0 := hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr hTv

/-- (c) {lit}`range T̃ = range T`. -/
theorem Ttilde_range (T : V →ₗ[F] W) :
    LinearMap.range (Ttilde T) = LinearMap.range T := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(LinearMap.ker T).mkQ v, rfl⟩

/-- (d) {lit}`V/(null T)` and {lit}`range T` are isomorphic. Built from the
properties above: {name}`Ttilde` is injective (b), so it is an isomorphism
onto its range ({name}`LinearEquiv.ofInjective`); and that range is
{lit}`range T` (c), giving the isomorphism after transporting along the
equality. -/
noncomputable def quotKer_equiv_range (T : V →ₗ[F] W) :
    (V ⧸ LinearMap.ker T) ≃ₗ[F] LinearMap.range T :=
  (LinearEquiv.ofInjective (Ttilde T) (Ttilde_injective T)).trans
    (LinearEquiv.ofEq _ _ (Ttilde_range T))

/-! # Exercises -/

/-- 3E.1 -/
theorem exercise_3E_1 {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (T : V → W) :
    (∃ S : V →ₗ[F] W, ∀ v, S v = T v) ↔
      ∃ (U : Submodule F (V × W)),
        (U : Set (V × W)) = {p | p.2 = T p.1} := by
  sorry

/-- 3E.2 -/
theorem exercise_3E_2 {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] [Finite F ((i : Fin m) → V i)] (i : Fin m) :
    Finite F (V i) := by
  sorry

/-- 3E.3 -/
theorem exercise_3E_3 {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] (W : Type*) [AddCommGroup W] [Module F W] :
    Nonempty ((((i : Fin m) → V i) →ₗ[F] W) ≃ₗ[F]
              ((i : Fin m) → (V i →ₗ[F] W))) := by
  sorry

/-- 3E.4 -/
theorem exercise_3E_4 {m : ℕ} (W : Fin m → Type*) [∀ i, AddCommGroup (W i)]
    [∀ i, Module F (W i)] (V : Type*) [AddCommGroup V] [Module F V] :
    Nonempty ((V →ₗ[F] ((i : Fin m) → W i)) ≃ₗ[F]
              ((i : Fin m) → (V →ₗ[F] W i))) := by
  sorry

/-- 3E.5 -/
theorem exercise_3E_5 (m : ℕ) :
    Nonempty ((Fin m → V) ≃ₗ[F] ((Fin m → F) →ₗ[F] V)) := by
  sorry

/-- 3E.6 -/
theorem exercise_3E_6 (v x : V) (U W : Submodule F V)
    (h : translate v U = translate x W) : U = W := by
  sorry

/-- 3E.7 -/
def exercise_3E_7_U : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | 2 * v 0 + 3 * v 1 + 5 * v 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    show 2 * (u + v) 0 + 3 * (u + v) 1 + 5 * (u + v) 2 = 0
    have hu' : 2 * u 0 + 3 * u 1 + 5 * u 2 = 0 := hu
    have hv' : 2 * v 0 + 3 * v 1 + 5 * v 2 = 0 := hv
    simp only [Pi.add_apply]; linarith
  smul_mem' := by
    intro a v hv
    show 2 * (a • v) 0 + 3 * (a • v) 1 + 5 * (a • v) 2 = 0
    have hv' : 2 * v 0 + 3 * v 1 + 5 * v 2 = 0 := hv
    simp only [Pi.smul_apply, smul_eq_mul]; linear_combination a * hv'

theorem exercise_3E_7 (A : Set (Fin 3 → ℝ)) :
    IsTranslate exercise_3E_7_U A ↔
      ∃ c : ℝ, A = {v : Fin 3 → ℝ | 2 * v 0 + 3 * v 1 + 5 * v 2 = c} := by
  sorry

/-- 3E.8 (a) -/
theorem exercise_3E_8a (T : V →ₗ[F] W) (c : W) :
    {x : V | T x = c} = ∅ ∨ IsTranslate (LinearMap.ker T) {x : V | T x = c} := by
  sorry

/-- 3E.9. The book's {lit}`F` is {lit}`ℝ` or {lit}`ℂ`; the {lit}`⇐` direction
uses {lit}`γ = 1/2`, so we assume {lit}`[CharZero F]`. (Over {lit}`𝔽₂` the only
scalars are {lit}`0, 1`, so every nonempty set satisfies the condition.) -/
theorem exercise_3E_9 [CharZero F] (A : Set V) (hA : A.Nonempty) :
    (∃ U : Submodule F V, IsTranslate U A) ↔
      ∀ v ∈ A, ∀ w ∈ A, ∀ γ : F, γ • v + (1 - γ) • w ∈ A := by
  sorry

/-- 3E.10 -/
theorem exercise_3E_10 (A₁ A₂ : Set V) (U₁ U₂ : Submodule F V)
    (v w : V) (hA₁ : A₁ = translate v U₁) (hA₂ : A₂ = translate w U₂) :
    A₁ ∩ A₂ = ∅ ∨ ∃ U : Submodule F V, IsTranslate U (A₁ ∩ A₂) := by
  sorry

/-- 3E.11 (a) -/
def exercise_3E_11_U : Submodule F (ℕ → F) where
  -- {lit}`∀ᶠ k in atTop, x k = 0` says {lit}`x k = 0` for all large enough
  -- {lit}`k`, i.e. {lit}`x` is eventually zero — equivalently, {lit}`x` has
  -- only finitely many nonzero entries. The `filter_upward` tactic is useful for
  -- working with this condition.
  carrier := {x | ∀ᶠ k in Filter.atTop, x k = 0}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-- 3E.11 (b) -/
theorem exercise_3E_11b : ¬ Finite F ((ℕ → F) ⧸ exercise_3E_11_U (F := F)) := by
  sorry

/-- The set {lit}`A` of affine combinations of {lit}`v₁, …, vₘ`, namely
{lit}`{λ₁v₁ + ⋯ + λₘvₘ : λ₁ + ⋯ + λₘ = 1}` (shared by the parts of 3E.12). -/
def affineCombSet {m : ℕ} (v : Fin m → V) : Set V :=
  {x : V | ∃ γ : Fin m → F, (∑ i, γ i) = 1 ∧ x = ∑ i, γ i • v i}

/-- 3E.12 (a) The affine combinations {lit}`{∑ λᵢ vᵢ : ∑ λᵢ = 1}` form a
translate of a subspace. -/
theorem exercise_3E_12a {m : ℕ} (hm : 0 < m) (v : Fin m → V) :
    (∃ U : Submodule F V, IsTranslate U (affineCombSet (F := F) v)) := by
  sorry

/-- 3E.12 (b) That translate {lit}`A` is the smallest such: any translate
{lit}`B` of a subspace containing all the {lit}`vᵢ` contains {lit}`A`. -/
theorem exercise_3E_12b {m : ℕ} (v : Fin m → V) (B : Set V)
    (hB : ∃ W : Submodule F V, IsTranslate W B) (hvB : ∀ i, v i ∈ B) :
    affineCombSet (F := F) v ⊆ B := by
  sorry

/-- 3E.12 (c) {lit}`A` is a translate of a subspace of dimension less than
{lit}`m`. -/
theorem exercise_3E_12c {m : ℕ} (hm : 0 < m) (v : Fin m → V) :
    (∃ U : Submodule F V, IsTranslate U (affineCombSet (F := F) v) ∧ finrank F U < m) := by
  sorry

/-- 3E.13 -/
theorem exercise_3E_13 (U : Submodule F V) [Finite F (V ⧸ U)] :
    Nonempty (V ≃ₗ[F] U × (V ⧸ U)) := by
  sorry

/-- 3E.14 -/
theorem exercise_3E_14 (U W : Submodule F V) (hUW : IsCompl U W) {m : ℕ}
    (w : Fin m → W) (hw : IsBasis F w) :
    IsBasis F (fun i => (U.mkQ (w i : V) : V ⧸ U)) := by
  sorry

/-- 3E.15 -/
theorem exercise_3E_15 (U : Submodule F V) {m n : ℕ}
    (v : Fin m → V) (hv : IsBasis F (fun i => (U.mkQ (v i) : V ⧸ U)))
    (u : Fin n → U) (hu : IsBasis F u) :
    IsBasis F (Fin.append v (fun i => (u i : V))) := by
  sorry

/-- 3E.16 -/
theorem exercise_3E_16 (φ : V →ₗ[F] F) (hφ : φ ≠ 0) :
    finrank F (V ⧸ LinearMap.ker φ) = 1 := by
  sorry

/-- 3E.17 -/
theorem exercise_3E_17 (U : Submodule F V) (h : finrank F (V ⧸ U) = 1) :
    ∃ φ : V →ₗ[F] F, LinearMap.ker φ = U := by
  sorry

/-- 3E.18 (a) -/
theorem exercise_3E_18a (U : Submodule F V) [Finite F (V ⧸ U)]
    (W : Submodule F V) [Finite F W] (hUW : U ⊔ W = ⊤) :
    finrank F W ≥ finrank F (V ⧸ U) := by
  sorry

/-- 3E.18 (b) -/
theorem exercise_3E_18b (U : Submodule F V) [Finite F (V ⧸ U)] :
    ∃ W : Submodule F V, Finite F W ∧
      finrank F W = finrank F (V ⧸ U) ∧ IsCompl U W := by
  sorry

/-- 3E.19 -/
theorem exercise_3E_19 (T : V →ₗ[F] W) (U : Submodule F V) :
    (∃ S : V ⧸ U →ₗ[F] W, T = S ∘ₗ U.mkQ) ↔ U ≤ LinearMap.ker T := by
  sorry

end LADR.Section_3E
