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
import LinearAlgebraDoneRightLean.Section_3D
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
  -- (v, Tv) + (w, Tw) = (v + w, Tv + Tw), for this to be a submodule
  -- we need Tv + Tw = T(v + w), is the linearity condition for T
  -- (av, T(av)) is submodule iff T(av) = aT(v), which is the other
  -- condition for submodule.
  -- so the two conditions match on both sides.
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨{ carrier := {p | p.2 = T p.1}, add_mem' := ?_, zero_mem' := ?_,
              smul_mem' := ?_ }, rfl⟩
    · rintro ⟨v, _⟩ ⟨w, _⟩ (rfl : _ = T v) (rfl : _ = T w)
      show T v + T w = T (v + w)
      rw [← hS, ← hS, ← hS, map_add]
    · show (0 : W) = T 0
      rw [← hS, map_zero]
    · rintro a ⟨v, _⟩ (rfl : _ = T v)
      show a • T v = T (a • v)
      rw [← hS, ← hS, map_smul]
  · rintro ⟨U, hU⟩
    have mem : ∀ v, (v, T v) ∈ U := fun v => by
      rw [← SetLike.mem_coe, hU]; rfl
    refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro v w
      have h := U.add_mem (mem v) (mem w)
      rw [← SetLike.mem_coe, hU] at h
      exact h.symm
    · intro a v
      have h := U.smul_mem a (mem v)
      rw [← SetLike.mem_coe, hU] at h
      exact h.symm

/-- 3E.2 -/
theorem exercise_3E_2 {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] [Finite F ((i : Fin m) → V i)] (i : Fin m) :
    Finite F (V i) := by
  -- lemma (might be proven earlier) - if a VS injects into a fin.dim one
  -- it is also fin.dim - proof goes that the basis of the injected one
  -- is LI in the larger, but by fin.dim. the basis has to be finite.
  -- then apply using the natural injection of Vi into the product,
  -- sending vi to the tuple with vi in the i-th position and zeros elsewhere.
  have finite_of_injective : ∀ {U X : Type _} [AddCommGroup U] [Module F U]
      [AddCommGroup X] [Module F X] [Finite F X] (S : U →ₗ[F] X),
      Function.Injective S → Finite F U := by
    intro U X _ _ _ _ _ S hS
    let b := Module.Free.chooseBasis F U
    have hli : LinearIndependent F (S ∘ b) :=
      b.linearIndependent.map' S (LinearMap.ker_eq_bot_of_injective hS)
    have : _root_.Finite (Module.Free.ChooseBasisIndex F U) := hli.finite
    exact Module.Finite.of_basis b
  exact @finite_of_injective _ _ _ _ _ _ ‹_› (LinearMap.single F V i) (Pi.single_injective i)

/-- 3E.3 -/
theorem exercise_3E_3 {m : ℕ} (V : Fin m → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module F (V i)] (W : Type*) [AddCommGroup W] [Module F W] :
    Nonempty ((((i : Fin m) → V i) →ₗ[F] W) ≃ₗ[F]
              ((i : Fin m) → (V i →ₗ[F] W))) := by
  -- take T : ((i : Fin m) → V i) →ₗ[F] W
  -- and define maps Ti : V i →ₗ[F] W by Ti(vi) = T(..., 0, vi, 0, ...)
  -- clearly these are linear by linearity of T, so need to show inj, and surj.
  -- (inj) assume Ti v = 0 for all i and v, then T(..., 0, vi, 0, ...) = 0 for all i and vi
  -- but T(v) = ∑ T(..., 0, vi, 0, ...) over the components, so T(v) = 0, showing injectivity.
  -- (surj) given a family of linear maps Ti : V i →ₗ[F] W, define T by T(v) = ∑ Ti(vi) over the components.
  -- This is linear and clearly maps to the given family, showing surjectivity.
  let Φ : (((i : Fin m) → V i) →ₗ[F] W) →ₗ[F] ((i : Fin m) → (V i →ₗ[F] W)) :=
    { toFun := fun T i => T ∘ₗ LinearMap.single F V i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofBijective Φ ⟨?_, ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    have hTi : ∀ i (vi : V i), T (Pi.single i vi) = 0 := fun i vi =>
      LinearMap.congr_fun (congr_fun hT i) vi
    apply LinearMap.ext
    intro v
    rw [← Finset.univ_sum_single v, map_sum]
    simp [hTi]
  · intro Ts
    refine ⟨∑ i, Ts i ∘ₗ LinearMap.proj i, ?_⟩
    funext i
    ext vi
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      LinearMap.coe_single, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_proj,
      Function.eval]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero])
      (by simp), Pi.single_eq_same]

/-- 3E.4 -/
theorem exercise_3E_4 {m : ℕ} (W : Fin m → Type*) [∀ i, AddCommGroup (W i)]
    [∀ i, Module F (W i)] (V : Type*) [AddCommGroup V] [Module F V] :
    Nonempty ((V →ₗ[F] ((i : Fin m) → W i)) ≃ₗ[F]
              ((i : Fin m) → (V →ₗ[F] W i))) := by
  -- map T : V →ₗ[F] ((i : Fin m) → W i)
  -- to the family of linear maps Ti : V →ₗ[F] W i by Ti(v) = T(v)_i
  -- clearly these are linear by linearity of T, so need to show inj, and surj.
  -- (inj) assume Ti = 0 for all i, then T(v)_i = 0 for all i, so T(v) = 0
  -- (surj) given a family of linear maps Ti : V →ₗ[F] W i, define T by T(v)_i = Ti(v)
  -- This is linear and clearly maps to the given family, showing surjectivity.
  let Φ : (V →ₗ[F] ((i : Fin m) → W i)) →ₗ[F] ((i : Fin m) → (V →ₗ[F] W i)) :=
    { toFun := fun T i => LinearMap.proj i ∘ₗ T
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofBijective Φ ⟨?_, ?_⟩⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    apply LinearMap.ext
    intro v
    funext i
    exact LinearMap.congr_fun (congr_fun hT i) v
  · intro Ts
    exact ⟨LinearMap.pi Ts, rfl⟩

/-- Helper for 3E.5: isomorphisms {lit}`Uᵢ ≅ Xᵢ` of the factors give an
isomorphism {lit}`U₁ × ⋯ × Uₘ ≅ X₁ × ⋯ × Xₘ` of the products, acting
componentwise. -/
def piCongr {m : ℕ} {U X : Fin m → Type*} [∀ i, AddCommGroup (U i)]
    [∀ i, Module F (U i)] [∀ i, AddCommGroup (X i)] [∀ i, Module F (X i)]
    (e : ∀ i, U i ≃ₗ[F] X i) : ((i : Fin m) → U i) ≃ₗ[F] ((i : Fin m) → X i) where
  toFun u i := e i (u i)
  invFun x i := (e i).symm (x i)
  map_add' u w := by funext i; simp
  map_smul' a u := by funext i; simp
  left_inv u := by funext i; simp
  right_inv x := by funext i; simp

/-- 3E.5 -/
theorem exercise_3E_5 (m : ℕ) :
    Nonempty ((Fin m → V) ≃ₗ[F] ((Fin m → F) →ₗ[F] V)) := by
  -- map v : Fin m → V to the linear map T_v : (Fin m → F) →ₗ[F] V
  -- defined on ei by T_v(ei) = v_i, extend linearly to a map on F^n
  -- show the map is linear
  -- (inj) if T_v = 0 then v_i = T_v(ei) = 0 for all i, so v = 0
  -- (surj) given T, take v_i = T(ei); then T_v and T agree on the basis ei,
  -- so T_v = T.
  -- (alternative proof) - use ex3 and L(F, V) iso to V (proven earlier)
  -- need a lemma that isos of products make an iso
  obtain ⟨e3⟩ := exercise_3E_3 (F := F) (fun _ : Fin m => F) V
  exact ⟨(piCongr fun _ => (LADR.Section_3D.exercise_3D_18 (F := F) (V := V)).some).trans
    e3.symm⟩

/-- 3E.6 -/
theorem exercise_3E_6 (v x : V) (U W : Submodule F V)
    (h : translate v U = translate x W) : U = W := by
  -- take u ∈ U, then exists w ∈ W s.t. v + u = x + w
  -- also exists w' ∈ W s.t. v + 0 = x + w' (because 0 in U)
  -- subtract the two eq. get u = w - w' ∈ W, so U ⊆ W.
  -- by symmetry, W ⊆ U, so U = W.
  have key : ∀ (v x : V) (U W : Submodule F V),
      translate v (U : Set V) = translate x W → U ≤ W := by
    intro v x U W h u hu
    obtain ⟨w, hw, hw_eq⟩ : v + u ∈ translate x (W : Set V) := h ▸ ⟨u, hu, rfl⟩
    obtain ⟨w', hw', hw'_eq⟩ : v + 0 ∈ translate x (W : Set V) := h ▸ ⟨0, U.zero_mem, rfl⟩
    have : u = w - w' :=
      calc u = (v + u) - (v + 0) := by abel
        _ = (x + w) - (x + w') := by rw [hw_eq, hw'_eq]
        _ = w - w' := by abel
    rw [this]
    exact W.sub_mem hw hw'
  exact le_antisymm (key v x U W h) (key x v W U h.symm)

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
  -- translate means exists v s.t. A = v + U for the given U
  -- x ∈ A ↔ x - v ∈ U ↔ 2 * (x - v) 0 + 3 * (x - v) 1 + 5 * (x - v) 2 = 0
  -- ↔ 2 * x 0 + 3 * x 1 + 5 * x 2 = 2 * v 0 + 3 * v 1 + 5 * v 2
  -- so c = 2 * v 0 + 3 * v 1 + 5 * v 2
  have key : ∀ v : Fin 3 → ℝ, translate v (exercise_3E_7_U : Set (Fin 3 → ℝ)) =
      {x | 2 * x 0 + 3 * x 1 + 5 * x 2 = 2 * v 0 + 3 * v 1 + 5 * v 2} := by
    intro v
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : 2 * u 0 + 3 * u 1 + 5 * u 2 = 0 := hu
      show 2 * (v + u) 0 + 3 * (v + u) 1 + 5 * (v + u) 2 = _
      simp only [Pi.add_apply]; linarith
    · intro hx
      have hx' : 2 * x 0 + 3 * x 1 + 5 * x 2 = 2 * v 0 + 3 * v 1 + 5 * v 2 := hx
      refine ⟨x - v, ?_, by abel⟩
      show 2 * (x - v) 0 + 3 * (x - v) 1 + 5 * (x - v) 2 = 0
      simp only [Pi.sub_apply]; linarith
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨_, key v⟩
  · rintro ⟨c, rfl⟩
    -- any v on the plane works, e.g. v = (c/2, 0, 0)
    refine ⟨![c / 2, 0, 0], ?_⟩
    rw [key]
    simp [mul_div_cancel₀ c two_ne_zero]

/-- 3E.8 (a) -/
theorem exercise_3E_8a (T : V →ₗ[F] W) (c : W) :
    {x : V | T x = c} = ∅ ∨ IsTranslate (LinearMap.ker T) {x : V | T x = c} := by
  -- assume non-empty, so v in {x : V | T x = c} for some v
  -- then iff v' in {x : V | T x = c}, by linearity Tv' - Tv = c - c = 0,
  -- so v' ∈ v + ker T
  -- for the other direction, if v' ∈ v + ker T, then v' = v + u for some u ∈ ker T, so T v' = T v + T u = c + 0 = c, hence v' ∈ {x : V | T x = c}
  -- so {x : V | T x = c} = v + ker T.
  -- part b) is just the observation that each system of equations is
  -- a linear map from F^n to F^m, so above applies.
  rcases Set.eq_empty_or_nonempty {x : V | T x = c} with h | ⟨v, hv⟩
  · exact Or.inl h
  right
  refine ⟨v, ?_⟩
  ext v'
  constructor
  · intro hv'
    refine ⟨v' - v, ?_, by abel⟩
    show T (v' - v) = 0
    rw [map_sub, hv', hv, sub_self]
  · rintro ⟨u, hu, rfl⟩
    show T (v + u) = c
    rw [map_add, hv, LinearMap.mem_ker.mp hu, add_zero]

/-- 3E.9. The book's {lit}`F` is {lit}`ℝ` or {lit}`ℂ`; the {lit}`⇐` direction
uses {lit}`γ = 1/2`, so we assume {lit}`[CharZero F]`. (Over {lit}`𝔽₂` the only
scalars are {lit}`0, 1`, so every nonempty set satisfies the condition.) -/
theorem exercise_3E_9 [CharZero F] (A : Set V) (hA : A.Nonempty) :
    (∃ U : Submodule F V, IsTranslate U A) ↔
      ∀ v ∈ A, ∀ w ∈ A, ∀ γ : F, γ • v + (1 - γ) • w ∈ A := by
  -- => v = a + x, w = a + y, for x, y in U a subspace
  -- γv + (1-γ)w = γ(a + x) + (1-γ)(a + y) = a + (γx + (1-γ)y)
  -- the second part is in U, by subspace rules, so we have γv + (1-γ)w ∈ A.
  -- <= pick v in A (as it is non-empty)
  -- we will show that A - v is a subspace (so A is a translate).
  -- assume w in A - v so w = w' - v for w' in A, will show a w is in A - v too for any a.
  -- suffices to show a w + v ∈ A
  -- a w + v = a w' - a v + v = a w' + (1 - a) v in A since w' and v are in A
  -- thus a w + v ∈ A, so a w ∈ A - v, showing closure under scalar multiplication.
  -- then if w₁ and w₂ in A - v, say w₁ = w₁' - v and w₂ = w₂' - v for w₁', w₂' in A
  -- w₁ + w₂ = (w₁' - v) + (w₂' - v) = (w₁' + w₂' - v) - v, so
  -- need to show w₁' + w₂' - v ∈ A, when w₁', w₂' ∈ A and v ∈ A
  -- we know 2w₁ - v in A, 2w₂ - v in A, using γ = 2
  -- then apply γ = 1/2 to those two
  -- then (1/2)(2w₁ - v) + (1/2)(2w₂ - v) = w₁ + w₂ - v ∈ A, as desired.
  constructor
  · rintro ⟨U, a, rfl⟩ v ⟨x, hx, rfl⟩ w ⟨y, hy, rfl⟩ γ
    refine ⟨γ • x + (1 - γ) • y, U.add_mem (U.smul_mem γ hx) (U.smul_mem _ hy), ?_⟩
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, add_sub_cancel, one_smul]
  · intro hconv
    obtain ⟨v, hv⟩ := hA
    -- {lit}`U = A - v`, i.e. {lit}`w ∈ U ↔ w + v ∈ A`
    have smul_mem : ∀ a : F, ∀ w, w + v ∈ A → a • w + v ∈ A := by
      intro a w hw
      have := hconv _ hw v hv a
      convert this using 1
      rw [smul_add, sub_smul, one_smul]; abel
    let U : Submodule F V :=
      { carrier := {w | w + v ∈ A}
        zero_mem' := by simpa using hv
        smul_mem' := fun a w hw => smul_mem a w hw
        add_mem' := by
          intro w₁ w₂ hw₁ hw₂
          -- 2w₁' - v and 2w₂' - v are in A (γ = 2), then average them (γ = 1/2)
          have h₁ := smul_mem 2 w₁ hw₁
          have h₂ := smul_mem 2 w₂ hw₂
          have := hconv _ h₁ _ h₂ (1 / 2)
          show w₁ + w₂ + v ∈ A
          convert this using 1
          have h2 : (2 : F) ≠ 0 := two_ne_zero
          rw [smul_add, smul_add, smul_smul, smul_smul]
          have e : (1 - 1 / 2 : F) = 1 / 2 := by field_simp; norm_num
          rw [e, one_div, inv_mul_cancel₀ h2, one_smul, one_smul]
          rw [show w₁ + (2 : F)⁻¹ • v + (w₂ + (2 : F)⁻¹ • v)
              = w₁ + w₂ + (2 * (2 : F)⁻¹) • v by rw [two_mul, add_smul]; abel,
            mul_inv_cancel₀ h2, one_smul] }
    refine ⟨U, v, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨x - v, show x - v + v ∈ A by simpa using hx, by abel⟩
    · rintro ⟨u, hu, rfl⟩
      have hu : u + v ∈ A := hu
      rwa [add_comm]

/-- 3E.10. -/
theorem exercise_3E_10 (A₁ A₂ : Set V) (U₁ U₂ : Submodule F V)
    (v w : V) (hA₁ : A₁ = translate v U₁) (hA₂ : A₂ = translate w U₂) :
    A₁ ∩ A₂ = ∅ ∨ ∃ U : Submodule F V, IsTranslate U (A₁ ∩ A₂) := by
  -- assume x in A₁ ∩ A₂
  -- (x - v) ∈ U₁ and (x - w) ∈ U₂
  -- by 3.101, then A₁ = x + U₁ and A₂ = x + U₂
  -- so A₁ ∩ A₂ = x + (U₁ ∩ U₂), which is a translate of the submodule U₁ ∩ U₂
  rcases Set.eq_empty_or_nonempty (A₁ ∩ A₂) with h | ⟨x, hx₁, hx₂⟩
  · exact Or.inl h
  right
  rw [hA₁] at hx₁
  rw [hA₂] at hx₂
  obtain ⟨u₁, hu₁, rfl⟩ := hx₁
  obtain ⟨u₂, hu₂, hx⟩ := hx₂
  have hxv : (v + u₁) - v ∈ U₁ := by rwa [add_sub_cancel_left]
  have hxw : (v + u₁) - w ∈ U₂ := by rw [← hx, add_sub_cancel_left]; exact hu₂
  have e₁ : translate (v + u₁) (U₁ : Set V) = translate v U₁ :=
    ((translate_tfae U₁ _ v).out 0 1).mp hxv
  have e₂ : translate (v + u₁) (U₂ : Set V) = translate w U₂ :=
    ((translate_tfae U₂ _ w).out 0 1).mp hxw
  refine ⟨U₁ ⊓ U₂, v + u₁, ?_⟩
  rw [hA₁, hA₂, ← e₁, ← e₂]
  ext y
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    obtain rfl : b = a := add_left_cancel hab
    exact ⟨b, ⟨ha, hb⟩, rfl⟩
  · rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩
    exact ⟨⟨a, ha₁, rfl⟩, ⟨a, ha₂, rfl⟩⟩

/-- 3E.11 (a) -/
def exercise_3E_11_U : Submodule F (ℕ → F) where
  -- {lit}`∀ᶠ k in atTop, x k = 0` says {lit}`x k = 0` for all large enough
  -- {lit}`k`, i.e. {lit}`x` is eventually zero — equivalently, {lit}`x` has
  -- only finitely many nonzero entries. The `filter_upward` tactic is useful for
  -- working with this condition.
  carrier := {x | ∀ᶠ k in Filter.atTop, x k = 0}
  zero_mem' := by simp only [Filter.eventually_atTop, ge_iff_le, Set.mem_setOf_eq, Pi.zero_apply,
    implies_true, exists_const]
  add_mem' := by
    intro x y hx hy
    simp at hx hy ⊢
    obtain ⟨M, hM⟩ := hx
    obtain ⟨N, hN⟩ := hy
    use max M N
    intro b hb
    have h1 := le_max_left M N
    have h2 := le_max_right M N
    specialize hM b (h1.trans hb)
    specialize hN b (h2.trans hb)
    rw [hM, hN]
    simp only [add_zero]
  smul_mem' := by
    intro c x hx
    simp at hx ⊢
    obtain ⟨M, hM⟩ := hx
    use M
    intro b hb
    specialize hM b hb
    rw [hM]
    right
    rfl

/-- 3E.11 (b) -/
theorem exercise_3E_11b : ¬ Finite F ((ℕ → F) ⧸ exercise_3E_11_U (F := F)) := by
  -- will show there is an infinite LI set in the quotient (thus there can't be finite basis)
  -- consider the sequences xi j = 1 if j % (prime i) == 0 else 0
  -- we will show that in the quotient, these sequences are LI.
  -- assume there is some subset S s.t. ∑_{i ∈ S} ai xi = 0 in the quotient.
  -- then means as sequences
  -- ∑_{i ∈ S} ai xi = u for some u ∈ U
  -- for each i in S, pick an index (prime i)^k for some k s.t. the index is
  -- larger than the biggest non-zero index of u.
  -- at that index the RHS is 0, and LHS is ai * 1 = ai, so that ai must be 0.
  -- repeat to get all ai = 0, showing the set of xi is linearly independent in the quotient.
  -- since xi is infinite LI in the quotient, it cannot have a finite basis.
  intro hfin
  let x : {p : ℕ // p.Prime} → (ℕ → F) := fun p j => if (p : ℕ) ∣ j then 1 else 0
  have : Infinite {p : ℕ // p.Prime} := Nat.infinite_setOf_prime.to_subtype
  apply Module.Finite.not_linearIndependent_of_infinite (R := F)
    (fun p => Submodule.Quotient.mk (p := exercise_3E_11_U (F := F)) (x p))
  rw [linearIndependent_iff']
  intro S a hsum i hi
  -- ∑_{i ∈ S} ai xi = u for some u ∈ U
  have hU : ∑ p ∈ S, a p • x p ∈ exercise_3E_11_U (F := F) := by
    have h : (exercise_3E_11_U (F := F)).mkQ (∑ p ∈ S, a p • x p) = 0 := by
      rw [map_sum]
      simpa using hsum
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hU
  -- the index (prime i)^(N+1) lies past N, where u is zero
  have hlt : N + 1 < (i : ℕ) ^ (N + 1) := Nat.lt_pow_self i.2.one_lt
  have h := hN ((i : ℕ) ^ (N + 1)) (by omega)
  rw [Finset.sum_apply, Finset.sum_eq_single i] at h
  · -- LHS is ai * 1 = ai
    simpa [x, dvd_pow_self _ (Nat.succ_ne_zero N)] using h
  · -- a different prime doesn't divide (prime i)^(N+1)
    intro j _ hji
    have hndvd : ¬ (j : ℕ) ∣ (i : ℕ) ^ (N + 1) := fun hdvd =>
      hji (Subtype.ext ((Nat.prime_dvd_prime_iff_eq j.2 i.2).mp (j.2.dvd_of_dvd_pow hdvd)))
    simp [x, hndvd]
  · exact fun h => absurd hi h

/-- The set {lit}`A` of affine combinations of {lit}`v₁, …, vₘ`, namely
{lit}`{λ₁v₁ + ⋯ + λₘvₘ : λ₁ + ⋯ + λₘ = 1}` (shared by the parts of 3E.12). -/
def affineCombSet {m : ℕ} (v : Fin m → V) : Set V :=
  {x : V | ∃ γ : Fin m → F, (∑ i, γ i) = 1 ∧ x = ∑ i, γ i • v i}

/-- The construction behind 3E.12 (a): with {lit}`γₘ = 1 - ∑_{i < m} γᵢ`, the set
{lit}`A - vₘ` is the range of {lit}`γ ↦ ∑_{i < m} γᵢ (vᵢ - vₘ)` on {lit}`F^(m-1)`. -/
theorem affineCombSet_eq_translate {n : ℕ} (v : Fin (n + 1) → V) :
    affineCombSet (F := F) v = translate (v (Fin.last n))
      (LinearMap.range (Fintype.linearCombination F
        (fun i : Fin n => v i.castSucc - v (Fin.last n)))) := by
  ext x
  simp only [affineCombSet, translate, Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_range,
    Fintype.linearCombination_apply]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [Fin.sum_univ_castSucc] at hγ
    -- γm = 1 - ∑_{i < m} γi
    have hlast : γ (Fin.last n) = 1 - ∑ i : Fin n, γ i.castSucc := by
      rw [← hγ]; ring
    refine ⟨_, ⟨fun i => γ i.castSucc, rfl⟩, ?_⟩
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul, one_smul]
    abel
  · rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
    refine ⟨Fin.snoc γ (1 - ∑ i, γ i), ?_, ?_⟩
    · simp [Fin.sum_univ_castSucc]
    · simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, smul_sub,
        Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul, one_smul]
      abel

/-- 3E.12 (a) The affine combinations {lit}`{∑ λᵢ vᵢ : ∑ λᵢ = 1}` form a
translate of a subspace. -/
theorem exercise_3E_12a {m : ℕ} (hm : 0 < m) (v : Fin m → V) :
    (∃ U : Submodule F V, IsTranslate U (affineCombSet (F := F) v)) := by
  -- plug in γm = 1 - ∑_{i < m-1} γi to express the last coefficient in terms of the others.
  -- now consider A - ∨m, we can show it is the range of a linear map
  -- from F^(m-1) to V, whose range is exactly A - vₘ.
  -- thus A is a translate of a subspace.
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact ⟨_, _, affineCombSet_eq_translate v⟩

/-- 3E.12 (b) That translate {lit}`A` is the smallest such: any translate
{lit}`B` of a subspace containing all the {lit}`vᵢ` contains {lit}`A`. -/
theorem exercise_3E_12b {m : ℕ} (v : Fin m → V) (B : Set V)
    (hB : ∃ W : Submodule F V, IsTranslate W B) (hvB : ∀ i, v i ∈ B) :
    affineCombSet (F := F) v ⊆ B := by
  -- say B = U + t for some submodule U and translation t.
  -- then vi - t ∈ U for all i
  -- say γi s.t. ∑ γi = 1, then ∑ γi (vi - t) ∈ U too
  -- so ∑ γi vi - t ∈ U, and hence ∑ γi vi ∈ B, so any member of A is in B.
  -- so A ⊆ B.
  obtain ⟨U, t, rfl⟩ := hB
  -- then vi - t ∈ U for all i
  have hv : ∀ i, v i - t ∈ U := fun i => by
    obtain ⟨u, hu, hui⟩ := hvB i
    rw [← hui, add_sub_cancel_left]
    exact hu
  rintro _ ⟨γ, hγ, rfl⟩
  -- ∑ γi (vi - t) ∈ U, and t + ∑ γi (vi - t) = ∑ γi vi
  refine ⟨∑ i, γ i • (v i - t), U.sum_mem fun i _ => U.smul_mem _ (hv i), ?_⟩
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hγ, one_smul]
  abel

/-- 3E.12 (c) {lit}`A` is a translate of a subspace of dimension less than
{lit}`m`. -/
theorem exercise_3E_12c {m : ℕ} (hm : 0 < m) (v : Fin m → V) :
    (∃ U : Submodule F V, IsTranslate U (affineCombSet (F := F) v) ∧ finrank F U < m) := by
  -- we already showed in part (a) that A is a translate of a subspace of dimension at most m - 1.
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨_, ⟨_, affineCombSet_eq_translate v⟩, ?_⟩
  calc finrank F (LinearMap.range _) ≤ finrank F (Fin n → F) := LinearMap.finrank_range_le _
    _ = n := Module.finrank_fin_fun F
    _ < n + 1 := Nat.lt_succ_self n

/-- 3E.13 -/
theorem exercise_3E_13 (U : Submodule F V) [Finite F (V ⧸ U)] :
    Nonempty (V ≃ₗ[F] U × (V ⧸ U)) := by
  -- we will construct an explicit map as follows
  -- fix a basis for V/U and fix representatives vi ∈ V , vi + U is basis.
  -- define f: V -> U, to be ai(v) is the coefficient for vi + U for v + U
  -- f(v) = v - ∑ ai(v) vi
  -- since v + U = ∑ ai (vi + U), f(v) is in U
  -- F : V → U × (V ⧸ U) given by v ↦ (f(v), v + U)
  -- we need to show that this map is linear first
  -- the second component is just the quotient map which is linear
  -- the first one follows after showing ai are linear maps to F
  -- but they are compositions of the quotient map + coordinate projections (previously shown?), hence linear composition.
  -- finally we need to show
  -- (inj) assume F(v) = 0, so ∨ in U by second component being zero
  -- but then ai(v) = 0 for all i (unique representation in the basis), so v = 0 too.
  -- (surj) take (u, v + U) for some u ∈ U and v + U in V/U
  -- take a representative v ∈ V for v + U
  -- F(v - f(v) + u) = (f(v - f(v) + u), v - f(v) + u + U) =
  -- =(f(v) - f(v) + u, v + U) = (u, v + U) because f(v) and u ∈ U, and f(u) = u
  -- and v + (-f(v)) + u + U = v + U
  let b := Module.finBasis F (V ⧸ U)
  choose w hw using fun i => Submodule.Quotient.mk_surjective U (b i)
  -- g(v) = ∑ ai(v) vi, where ai = (coordinate i) ∘ (quotient map) is linear
  let g : V →ₗ[F] V := ∑ i, (b.coord i ∘ₗ U.mkQ).smulRight (w i)
  have hg : ∀ v, g v = ∑ i, b.coord i (U.mkQ v) • w i := fun v => by simp [g]
  -- since v + U = ∑ ai (vi + U), f(v) = v - g(v) is in U
  have hmem : ∀ v, v - g v ∈ U := fun v => by
    rw [← Submodule.Quotient.eq]
    have : U.mkQ (g v) = U.mkQ v := by
      simp only [hg, map_sum, map_smul, Submodule.mkQ_apply, hw, Module.Basis.coord_apply,
        Module.Basis.sum_repr]
    exact this.symm
  let f : V →ₗ[F] U := (LinearMap.id - g).codRestrict U hmem
  have hf : ∀ v, (f v : V) = v - g v := fun v => rfl
  -- f(u) = u for u ∈ U: u + U = 0, so all ai(u) = 0
  have hfU : ∀ u ∈ U, (f u : V) = u := fun u hu => by
    have : U.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero U).mpr hu
    simp [hf, hg, this]
  let T : V →ₗ[F] U × (V ⧸ U) := f.prod U.mkQ
  refine ⟨LinearEquiv.ofBijective T ⟨?_, ?_⟩⟩
  · -- (inj)
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : f v = 0 := congrArg Prod.fst hv
    have h2 : U.mkQ v = 0 := congrArg Prod.snd hv
    have hvU : v ∈ U := (Submodule.Quotient.mk_eq_zero U).mp h2
    -- f(v) = v since v ∈ U, and f(v) = 0
    rw [← hfU v hvU, h1, Submodule.coe_zero]
  · -- (surj)
    rintro ⟨u, q⟩
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U q
    refine ⟨v - f v + u, Prod.ext (Subtype.ext ?_) ?_⟩
    · change (f (v - f v + u) : V) = u
      rw [map_add, map_sub, Submodule.coe_add, Submodule.coe_sub, hfU _ (f v).2, hfU _ u.2]
      abel
    · change U.mkQ (v - f v + u) = Submodule.Quotient.mk v
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      have : v - (f v : V) + u - v = u - f v := by abel
      rw [this]
      exact U.sub_mem u.2 (f v).2

/-- 3E.14 -/
theorem exercise_3E_14 (U W : Submodule F V) (hUW : IsCompl U W) {m : ℕ}
    (w : Fin m → W) (hw : IsBasis F w) :
    IsBasis F (fun i => (U.mkQ (w i : V) : V ⧸ U)) := by
  -- by definition every v can be written as v = u + ∑ ai wi, for
  -- unique choice of ai and u.
  -- take random element v + U from V / U
  -- using a representative v, it can be writen as u + ∑ ai wi
  -- thus wi + U span V / U
  -- for LI, suppose ∑ ai (wi + U) = 0
  -- then ∑ ai wi + (- u) = 0 for some u ∈ U, but
  -- by uniquess, the solution can only be ai = 0 for all i (and u = 0)
  -- this LI
  set b := hw.toModuleBasis
  refine ⟨?_, ?_⟩
  · -- (LI) suppose ∑ ai (wi + U) = 0
    rw [Fintype.linearIndependent_iff]
    intro a ha
    -- then x = ∑ ai wi ∈ U, and also x ∈ W
    set x : V := ∑ i, a i • (w i : V)
    have hxU : x ∈ U := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      simpa [x, map_sum] using ha
    have hxW : x ∈ W := W.sum_mem fun i _ => W.smul_mem _ (w i).2
    -- by uniqueness (U ∩ W = 0), x = 0, so ∑ ai wi = 0 in W
    have hx : x = 0 := (Submodule.disjoint_def.mp hUW.disjoint) x hxU hxW
    have hsum : ∑ i, a i • w i = 0 := Subtype.ext (by simpa [x] using hx)
    exact Fintype.linearIndependent_iff.mp hw.1 a hsum
  · -- (spans) take v + U, write the representative as v = u + w' with u ∈ U, w' ∈ W
    rw [Spans, eq_top_iff]
    rintro q -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U q
    have hv : v ∈ U ⊔ W := hUW.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    -- w' = ∑ ai wi
    have hw'sum : w' = ∑ i, b.repr ⟨w', hw'⟩ i • (w i : V) := by
      have := congrArg Subtype.val (b.sum_repr ⟨w', hw'⟩)
      simpa [b] using this.symm
    -- so u + w' + U = ∑ ai (wi + U)
    have : Submodule.Quotient.mk (p := U) (u + w') =
        ∑ i, b.repr ⟨w', hw'⟩ i • U.mkQ (w i : V) := by
      rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero U).mpr hu, zero_add]
      calc Submodule.Quotient.mk w'
          = U.mkQ (∑ i, b.repr ⟨w', hw'⟩ i • (w i : V)) := by
            rw [Submodule.mkQ_apply, ← hw'sum]
        _ = _ := by simp only [map_sum, map_smul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- 3E.15 -/
theorem exercise_3E_15 (U : Submodule F V) {m n : ℕ}
    (v : Fin m → V) (hv : IsBasis F (fun i => (U.mkQ (v i) : V ⧸ U)))
    (u : Fin n → U) (hu : IsBasis F u) :
    IsBasis F (Fin.append v (fun i => (u i : V))) := by
  -- by ex. 13 everything is finite dim and dim match, so enough to
  -- show only spanning, since linear independence will follow from the dimension count
  -- take v ∈ V, exists ∑ ai (v i + U) = v + U
  -- this means v = u + ∑ ai (v i) for some u ∈ U
  -- now u = ∑ bi ui, so ui and vi together span v
  set bv := hv.toModuleBasis
  set bu := hu.toModuleBasis
  -- by ex. 13 everything is finite dim and dim match
  haveI : Finite F (V ⧸ U) := Module.Finite.of_basis bv
  haveI : Finite F U := Module.Finite.of_basis bu
  obtain ⟨e⟩ := exercise_3E_13 U
  haveI : Finite F V := Module.Finite.equiv e.symm
  have hdim : m + n = finrank F V := by
    rw [e.finrank_eq, Module.finrank_prod,
      ← LADR.Section_2C.isBasis_card_eq_finrank _ hu,
      ← LADR.Section_2C.isBasis_card_eq_finrank _ hv, add_comm]
  -- so enough to show only spanning (2.42)
  refine LADR.Section_2C.isBasis_of_spans_of_card_eq _ ?_ hdim
  rw [Spans, eq_top_iff]
  rintro x -
  set S := Set.range (Fin.append v (fun i => (u i : V)))
  have hvS : ∀ i, v i ∈ Submodule.span F S := fun i =>
    Submodule.subset_span ⟨Fin.castAdd n i, Fin.append_left _ _ _⟩
  have huS : ∀ j, (u j : V) ∈ Submodule.span F S := fun j =>
    Submodule.subset_span ⟨Fin.natAdd m j, Fin.append_right _ _ _⟩
  -- take v ∈ V, exists ∑ ai (v i + U) = v + U
  set a := bv.repr (U.mkQ x)
  have hxa : U.mkQ x = ∑ i, a i • U.mkQ (v i) := by
    conv_lhs => rw [← bv.sum_repr (U.mkQ x)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bv, LADR.Section_2B.IsBasis.toModuleBasis_apply]
    rfl
  -- this means v = u + ∑ ai (v i) for some u ∈ U
  have hyU : x - ∑ i, a i • v i ∈ U := by
    rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hxa]
    simp only [map_sum, map_smul]
  set y : U := ⟨x - ∑ i, a i • v i, hyU⟩
  have hx : x = ∑ i, a i • v i + (y : V) := by simp [y]
  -- now u = ∑ bi ui
  have hy : (y : V) = ∑ j, bu.repr y j • (u j : V) := by
    have := congrArg Subtype.val (bu.sum_repr y)
    simpa [bu] using this.symm
  rw [hx, hy]
  exact add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvS i))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (huS j))

/-- 3E.16 -/
theorem exercise_3E_16 (φ : V →ₗ[F] F) (hφ : φ ≠ 0) :
    finrank F (V ⧸ LinearMap.ker φ) = 1 := by
  -- dim range φ = 1 (since φ ≠ 0), and we proved that T/ker T is iso to range T
  rw [(quotKer_equiv_range φ).finrank_eq]
  -- range φ is a nonzero subspace of F, so it is all of F
  have hrange : LinearMap.range φ = ⊤ :=
    (eq_bot_or_eq_top (LinearMap.range φ)).resolve_left (LinearMap.range_eq_bot.not.mpr hφ)
  rw [hrange, finrank_top, Module.finrank_self]

/-- 3E.17 -/
theorem exercise_3E_17 (U : Submodule F V) (h : finrank F (V ⧸ U) = 1) :
    ∃ φ : V →ₗ[F] F, LinearMap.ker φ = U := by
  -- take quotient map V → V/U and compose with an isomorphism V/U ≃ F to get φ
  haveI : Finite F (V ⧸ U) := Module.finite_of_finrank_pos (by omega)
  let e : (V ⧸ U) ≃ₗ[F] F := LinearEquiv.ofFinrankEq _ _ (by rw [h, Module.finrank_self])
  refine ⟨e.toLinearMap ∘ₗ U.mkQ, ?_⟩
  rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

/-- 3E.18 (a) -/
theorem exercise_3E_18a (U : Submodule F V) [Finite F (V ⧸ U)]
    (W : Submodule F V) [Finite F W] (hUW : U ⊔ W = ⊤) :
    finrank F W ≥ finrank F (V ⧸ U) := by
  -- restrict the quotient map V → V/U to W, giving a linear map W → V/U.
  -- the quotient map is surjective, but U is in the kernel, and U ⊔ W = ⊤,
  -- so the restricted map W → V/U is also surjective.
  -- thus the dimension of W is at least the dimension of V/U.
  let π : W →ₗ[F] V ⧸ U := U.mkQ ∘ₗ W.subtype
  have hsurj : LinearMap.range π = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective U q
    -- v = u + w with u ∈ U, w ∈ W, and v + U = w + U
    have hv : v ∈ U ⊔ W := hUW ▸ Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨w, hw⟩, ?_⟩
    simp only [π, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero U).mpr hu, zero_add]
  calc finrank F (V ⧸ U) = finrank F (LinearMap.range π) := by rw [hsurj, finrank_top]
    _ ≤ finrank F W := LinearMap.finrank_range_le π

/-- 3E.18 (b) -/
theorem exercise_3E_18b (U : Submodule F V) [Finite F (V ⧸ U)] :
    ∃ W : Submodule F V, Finite F W ∧
      finrank F W = finrank F (V ⧸ U) ∧ IsCompl U W := by
  -- take representative vectors for vi + U of a basis of V/U
  -- then one can show vi are LI in V too (consequence of quotient map linear)
  -- take w = span {vi} then dim W = dim V/U
  -- also W ∩ U = {0}, assume v = ∑ ai vi ∈ W and also in U, then ∑ ai (vi + U) = 0 in V/U, by basis
  -- ai = 0 for all i, showing that v = 0 and hence W ∩ U = {0}.
  -- and W + U = V, proven by taking any v ∈ V, writing v + U as a linear combination of the basis of V/U
  -- thus v = ∑ ai vi + u for some u ∈ U, showing that V = W + U.
  let b := Module.finBasis F (V ⧸ U)
  choose v hv using fun i => Submodule.Quotient.mk_surjective U (b i)
  have hvb : ∀ i, U.mkQ (v i) = b i := hv
  -- mapping ∑ ai vi to V/U gives ∑ ai (vi + U)
  have hmk : ∀ a : Fin _ → F, U.mkQ (∑ i, a i • v i) = ∑ i, a i • b i := fun a => by
    simp only [map_sum, map_smul, hvb]
  -- vi are LI in V
  have hli : LinearIndependent F v := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have : ∑ i, a i • b i = 0 := by rw [← hmk, ha, map_zero]
    exact Fintype.linearIndependent_iff.mp b.linearIndependent a this
  refine ⟨Submodule.span F (Set.range v),
    Module.Finite.span_of_finite F (Set.finite_range v), ?_, ?_⟩
  · -- dim W = dim V/U
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  refine isCompl_iff.mpr ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff.mpr ?_⟩
  · -- W ∩ U = {0}
    intro x hxU hxW
    obtain ⟨a, rfl⟩ := Submodule.mem_span_range_iff_exists_fun F |>.mp hxW
    have h0 : ∑ i, a i • b i = 0 := by
      rw [← hmk]
      exact (Submodule.Quotient.mk_eq_zero U).mpr hxU
    have ha := Fintype.linearIndependent_iff.mp b.linearIndependent a h0
    simp [ha]
  · -- W + U = V
    rw [eq_top_iff]
    rintro x -
    set a := b.repr (U.mkQ x)
    have hxU : x - ∑ i, a i • v i ∈ U := by
      rw [← Submodule.Quotient.eq, ← Submodule.mkQ_apply, ← Submodule.mkQ_apply, hmk,
        b.sum_repr]
    exact Submodule.mem_sup.mpr ⟨_, hxU, _, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), sub_add_cancel _ _⟩

/-- 3E.19 -/
theorem exercise_3E_19 (T : V →ₗ[F] W) (U : Submodule F V) :
    (∃ S : V ⧸ U →ₗ[F] W, T = S ∘ₗ U.mkQ) ↔ U ≤ LinearMap.ker T := by
  -- => assume v in U, then T v = S (U.mk v) = S 0 = 0, so v ∈ ker T
  -- <= assume U ⊆ ker T, define S on V/U by S(v + U) = T v
  -- for any representative v + U of a coset in V/U.
  -- show that choice doesn't matter, by assumption, v - v' ∈ U ⊆ ker T,
  -- so T v = T v'.
  -- show that S is linear (follows from linearity of T)
  -- finally, verify that T = S ∘ₗ U.mkQ by construction
  constructor
  · -- (=>)
    rintro ⟨S, rfl⟩ v hv
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero U).mpr hv, map_zero]
  · -- (<=) S(v + U) = T v; the choice of representative doesn't matter
    intro h
    let s : V ⧸ U → W := Quotient.lift T fun a b hab => by
      -- a - b ∈ U ⊆ ker T, so T a = T b
      have hker := h ((Submodule.quotientRel_def U).mp hab)
      rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at hker
    have hs : ∀ v, s (Submodule.Quotient.mk v) = T v := fun v => rfl
    -- S is linear, from linearity of T
    let S : V ⧸ U →ₗ[F] W :=
      { toFun := s
        map_add' := by
          intro x y
          obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective U x
          obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective U y
          rw [← Submodule.Quotient.mk_add, hs, hs, hs, map_add]
        map_smul' := by
          intro c x
          obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective U x
          rw [← Submodule.Quotient.mk_smul, hs, hs, map_smul, RingHom.id_apply] }
    -- T = S ∘ₗ U.mkQ by construction
    exact ⟨S, LinearMap.ext fun v => rfl⟩

end LADR.Section_3E
