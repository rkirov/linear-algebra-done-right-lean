import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linter.Style
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Dual.Basis
import LinearAlgebraDoneRightLean.L2Interval
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 6C: Orthogonal Complements and Minimization Problems
-/

namespace LADR.Section_6C

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module (finrank)

/-- The intervals {lit}`[-1,1]` and {lit}`[-π,π]` are nondegenerate, so {lit}`C[-1,1]`/`C[-π,π]`
carry the `L²` inner product (see `L2Interval.lean`). -/
instance : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩
instance : Fact (-Real.pi < Real.pi) := ⟨neg_lt_self Real.pi_pos⟩

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-! # Orthogonal Complements -/

/-! 6.46 Definition: orthogonal complement, {lit}`U⟂`

The orthogonal complement of a subset {lit}`U` of {lit}`V` is the set of all
vectors orthogonal to every vector in {lit}`U`. For a subspace {lit}`U`, this is
mathlib's {name}`Submodule.orthogonal`, written {lit}`Uᗮ`. -/

example (U : Submodule 𝕜 V) (v : V) : v ∈ Uᗮ ↔ ∀ u ∈ U, ⟪u, v⟫_𝕜 = 0 :=
  Submodule.mem_orthogonal U v

/-! Axler defines {lit}`U⟂` for an arbitrary *subset* {lit}`U` of {lit}`V`,
whereas {name}`Submodule.orthogonal` takes a subspace. The first two bullets of
6.47 take the orthogonal complement of a set that is not a subspace, so we also
define the subset version. -/

/-- The orthogonal complement of a subset {lit}`S` of {lit}`V`: the set of
vectors orthogonal to every element of {lit}`S`. It is a subspace (6.48(a))
whether or not {lit}`S` is, so we bundle it as a {name}`Submodule`. -/
def setOrthogonal (S : Set V) : Submodule 𝕜 V where
  carrier := {v | ∀ u ∈ S, ⟪u, v⟫_𝕜 = 0}
  zero_mem' u _ := inner_zero_right u
  add_mem' hv hw u hu := by rw [inner_add_right, hv u hu, hw u hu, add_zero]
  smul_mem' c v hv u hu := by rw [inner_smul_right, hv u hu, mul_zero]

@[simp] theorem mem_setOrthogonal {S : Set V} {v : V} :
    v ∈ setOrthogonal (𝕜 := 𝕜) S ↔ ∀ u ∈ S, ⟪u, v⟫_𝕜 = 0 := Iff.rfl

/-- On a subspace the two definitions agree. -/
theorem setOrthogonal_coe (U : Submodule 𝕜 V) : setOrthogonal (U : Set V) = Uᗮ := rfl

/-- A vector is orthogonal to every element of {lit}`S` exactly when it is
orthogonal to {lit}`span S`, so {lit}`S⟂ = (span S)⟂`. -/
theorem setOrthogonal_eq_span_orthogonal (S : Set V) :
    setOrthogonal (𝕜 := 𝕜) S = (Submodule.span 𝕜 S)ᗮ := by
  ext v
  rw [mem_setOrthogonal, ← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le,
    Submodule.isOrtho_comm, Submodule.isOrtho_span]
  simp

/-! 6.47 Example: orthogonal complements -/

/-- The plane {lit}`{(x, y, z) ∈ ℝ³ : 2x + 3y + 5z = 0}`. -/
def plane235 : Set (EuclideanSpace ℝ (Fin 3)) := {v | 2 * v 0 + 3 * v 1 + 5 * v 2 = 0}

/-- The line {lit}`{(2t, 3t, 5t) : t ∈ ℝ}`. -/
def line235 : Set (EuclideanSpace ℝ (Fin 3)) := {v | ∃ t : ℝ, v = !₂[2 * t, 3 * t, 5 * t]}

/-- If {lit}`V = ℝ³` and {lit}`U` is the subset consisting of the single point
{lit}`(2, 3, 5)`, then {lit}`U⟂` is the plane
{lit}`{(x, y, z) ∈ ℝ³ : 2x + 3y + 5z = 0}`. -/
theorem setOrthogonal_singleton_235 :
    (setOrthogonal (𝕜 := ℝ) ({!₂[2, 3, 5]} : Set (EuclideanSpace ℝ (Fin 3))) : Set _) =
      plane235 := by
  ext v
  rw [SetLike.mem_coe, mem_setOrthogonal]
  simp only [Set.mem_singleton_iff, forall_eq, plane235, Set.mem_setOf_eq]
  rw [show ⟪(!₂[2, 3, 5] : EuclideanSpace ℝ (Fin 3)), v⟫_ℝ = 2 * v 0 + 3 * v 1 + 5 * v 2 by
    simp [PiLp.inner_apply, Fin.sum_univ_three, real_inner_eq_re_inner ℝ]; ring]

/-- The line {lit}`{(2t, 3t, 5t)}` is {lit}`span((2, 3, 5))`. -/
theorem line235_eq_span : line235 = (ℝ ∙ (!₂[2, 3, 5] : EuclideanSpace ℝ (Fin 3)) : Set _) := by
  ext v
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by ext i; fin_cases i <;> simp <;> ring⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by ext i; fin_cases i <;> simp <;> ring⟩

/-- If {lit}`V = ℝ³` and {lit}`U` is the plane
{lit}`{(x, y, z) ∈ ℝ³ : 2x + 3y + 5z = 0}`, then {lit}`U⟂` is the line
{lit}`{(2t, 3t, 5t) : t ∈ ℝ}`. -/
theorem setOrthogonal_plane235 :
    (setOrthogonal (𝕜 := ℝ) plane235 : Set (EuclideanSpace ℝ (Fin 3))) = line235 := by
  have hplane : plane235 =
      (((ℝ ∙ (!₂[2, 3, 5] : EuclideanSpace ℝ (Fin 3)))ᗮ : Submodule ℝ _) : Set _) := by
    rw [← setOrthogonal_singleton_235, setOrthogonal_eq_span_orthogonal]
  rw [hplane, setOrthogonal_coe, Submodule.orthogonal_orthogonal, line235_eq_span]

/-- More generally, if {lit}`U` is a plane in {lit}`ℝ³` containing the origin,
then {lit}`U⟂` is a line containing the origin (perpendicular to {lit}`U` by
definition of the orthogonal complement). -/
theorem finrank_orthogonal_eq_one (U : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : finrank ℝ U = 2) : finrank ℝ Uᗮ = 1 := by
  have := U.finrank_add_finrank_orthogonal (𝕜 := ℝ)
  simp [h] at this ⊢
  omega

/-- If {lit}`U` is a line in {lit}`ℝ³` containing the origin, then {lit}`U⟂` is a
plane containing the origin. -/
theorem finrank_orthogonal_eq_two (U : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (h : finrank ℝ U = 1) : finrank ℝ Uᗮ = 2 := by
  have := U.finrank_add_finrank_orthogonal (𝕜 := ℝ)
  simp [h] at this ⊢
  omega

/-- If {lit}`V = 𝔽⁵` and {lit}`U = {(a, b, 0, 0, 0) ∈ 𝔽⁵}`, then
{lit}`U⟂ = {(0, 0, x, y, z) ∈ 𝔽⁵}`. Here {lit}`U` is the span of the first two
standard basis vectors. -/
theorem setOrthogonal_e01 :
    (setOrthogonal (𝕜 := 𝕜) ({EuclideanSpace.single 0 1, EuclideanSpace.single 1 1} :
        Set (EuclideanSpace 𝕜 (Fin 5))) : Set _) =
      {v : EuclideanSpace 𝕜 (Fin 5) | v 0 = 0 ∧ v 1 = 0} := by
  ext v
  simp [EuclideanSpace.inner_single_left]

/-- If {lit}`e₁, …, e_m, f₁, …, f_n` is an orthonormal basis of {lit}`V`, then
{lit}`(span(e₁, …, e_m))⟂ = span(f₁, …, f_n)`. The two blocks of the basis are
indexed here by the two summands of {lit}`α ⊕ β`. -/
theorem orthogonal_span_range_inl {α β : Type*} [Fintype α] [Fintype β]
    (b : OrthonormalBasis (α ⊕ β) 𝕜 V) :
    (Submodule.span 𝕜 (Set.range (b ∘ Sum.inl)))ᗮ
      = Submodule.span 𝕜 (Set.range (b ∘ Sum.inr)) := by
  refine le_antisymm (fun v hv => ?_) ?_
  · have hzero : ∀ a : α, ⟪b (Sum.inl a), v⟫_𝕜 = 0 := fun a =>
      hv _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [← b.sum_repr' v, Fintype.sum_sum_type]
    have h1 : ∑ a : α, ⟪b (Sum.inl a), v⟫_𝕜 • b (Sum.inl a) = 0 := by simp [hzero]
    rw [h1, zero_add]
    exact Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  · refine Submodule.IsOrtho.le (Submodule.IsOrtho.symm (Submodule.isOrtho_span.mpr ?_))
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
    exact b.orthonormal.2 (by simp)

/-! 6.48 Properties of orthogonal complement

Parts (a), (d), (e) are stated in the book for arbitrary *subsets* of {lit}`V`,
so we state them for {name}`setOrthogonal`; each specializes to the subspace
version, recorded afterwards as the mathlib idiom. -/

/-- (a) If {lit}`U` is a subset of {lit}`V`, then {lit}`U⟂` is a subspace of
{lit}`V` — for {name}`setOrthogonal` that is true by construction, and mathlib's
{name}`Submodule.orthogonal` is a {name}`Submodule` for the same reason. -/
example (S : Set V) : Submodule 𝕜 V := setOrthogonal S

example (U : Submodule 𝕜 V) : Submodule 𝕜 V := Uᗮ

/-- (b) {lit}`{0}⟂ = V`. -/
theorem setOrthogonal_zero : setOrthogonal ({0} : Set V) = (⊤ : Submodule 𝕜 V) := by
  ext v
  simp

theorem bot_orthogonal : (⊥ : Submodule 𝕜 V)ᗮ = ⊤ := Submodule.bot_orthogonal_eq_top

/-- (c) {lit}`V⟂ = {0}`. -/
theorem setOrthogonal_univ : setOrthogonal (Set.univ : Set V) = (⊥ : Submodule 𝕜 V) := by
  rw [Submodule.eq_bot_iff]
  exact fun v hv => inner_self_eq_zero.mp (hv v (Set.mem_univ v))

theorem top_orthogonal : (⊤ : Submodule 𝕜 V)ᗮ = ⊥ := Submodule.top_orthogonal_eq_bot

/-- (d) If {lit}`U` is a subset of {lit}`V`, then {lit}`U ∩ U⟂ ⊆ {0}` (only
{lit}`⊆`, since {lit}`0` need not belong to {lit}`U`). -/
theorem inter_setOrthogonal_subset (S : Set V) :
    S ∩ (setOrthogonal (𝕜 := 𝕜) S : Set V) ⊆ {0} := by
  rintro v ⟨hvS, hv⟩
  exact inner_self_eq_zero.mp (hv v hvS)

/-- For a subspace this sharpens to {lit}`U ∩ U⟂ = {0}`. -/
theorem inf_orthogonal_eq_bot (U : Submodule 𝕜 V) : U ⊓ Uᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x ⟨hxU, hxU'⟩
  exact inner_self_eq_zero.mp (hxU' x hxU)

/-- (e) If {lit}`G` and {lit}`H` are subsets of {lit}`V` and {lit}`G ⊆ H`, then
{lit}`H⟂ ⊆ G⟂`. -/
theorem setOrthogonal_le {G H : Set V} (h : G ⊆ H) :
    setOrthogonal (𝕜 := 𝕜) H ≤ setOrthogonal (𝕜 := 𝕜) G :=
  fun _ hv u hu => hv u (h hu)

theorem orthogonal_le {G H : Submodule 𝕜 V} (h : G ≤ H) : Hᗮ ≤ Gᗮ :=
  Submodule.orthogonal_le h

/-! 6.49 Direct sum of a subspace and its orthogonal complement

If {lit}`U` is a finite-dimensional subspace of {lit}`V`, then
{lit}`V = U ⊕ U⟂`. In mathlib this is {name}`IsCompl`.

The proof below follows the book rather than calling mathlib's
{name}`Submodule.isCompl_orthogonal_of_hasOrthogonalProjection`: pick an
orthonormal basis {lit}`e₁, …, e_m` of {lit}`U` and split each {lit}`v` as in
6.50,
{lit}`v = (⟨v, e₁⟩e₁ + ⋯ + ⟨v, e_m⟩e_m) + (v − ⟨v, e₁⟩e₁ − ⋯ − ⟨v, e_m⟩e_m)`,
where the first summand lies in {lit}`U` and the second is orthogonal to every
{lit}`e_k`, hence to {lit}`U`. That gives {lit}`V = U + U⟂`; with
{lit}`U ∩ U⟂ = {0}` from 6.48(d) the sum is direct. (Axler's {lit}`⟨v, e_k⟩` is
mathlib's {lit}`⟪e_k, v⟫`.) -/

/-! 6.50 is the decomposition used in that proof: if {lit}`e₁, …, e_m` is an
orthonormal basis of {lit}`U` and {lit}`v ∈ V`, then
{lit}`v = (⟨v, e₁⟩e₁ + ⋯ + ⟨v, e_m⟩e_m) + (v − ⟨v, e₁⟩e₁ − ⋯ − ⟨v, e_m⟩e_m)`
with the first summand in {lit}`U` and the second in {lit}`U⟂`. It is stated
separately because 6.57(i) needs it again. -/

theorem sum_inner_smul_mem (U : Submodule 𝕜 V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 U) (v : V) :
    ∑ k, ⟪(b k : V), v⟫_𝕜 • (b k : V) ∈ U :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2

theorem sub_sum_inner_smul_mem_orthogonal (U : Submodule 𝕜 V) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 U) (v : V) :
    v - ∑ k, ⟪(b k : V), v⟫_𝕜 • (b k : V) ∈ Uᗮ := by
  -- the basis of `U`, viewed inside `V`, is orthonormal and spans `U`
  have hortho : Orthonormal 𝕜 (fun k => ((b k : V))) :=
    b.orthonormal.comp_linearIsometry U.subtypeₗᵢ
  have hspan : Submodule.span 𝕜 (Set.range fun k => ((b k : V))) = U := by
    have h1 : Submodule.span 𝕜 (Set.range (b : ι → U)) = ⊤ := b.toBasis.span_eq
    have h2 := congrArg (Submodule.map U.subtype) h1
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      Submodule.range_subtype] at h2
  -- so being orthogonal to `U` is being orthogonal to each `e k`
  have key : v - ∑ k, ⟪(b k : V), v⟫_𝕜 • (b k : V)
      ∈ (Submodule.span 𝕜 (Set.range fun k => ((b k : V))))ᗮ := by
    rw [← setOrthogonal_eq_span_orthogonal, mem_setOrthogonal]
    rintro _ ⟨j, rfl⟩
    rw [inner_sub_right, hortho.inner_right_fintype, sub_self]
  rwa [hspan] at key

theorem isCompl_orthogonal (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    IsCompl U Uᗮ := by
  refine ⟨?_, ?_⟩
  · -- `U ∩ U⟂ = {0}`, i.e. 6.48(d)
    rw [disjoint_iff]
    exact inf_orthogonal_eq_bot U
  · -- `V = U + U⟂`, splitting `v` as in 6.50
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    set b := stdOrthonormalBasis 𝕜 U with hb
    have hv : v = (∑ k, ⟪(b k : V), v⟫_𝕜 • (b k : V))
        + (v - ∑ k, ⟪(b k : V), v⟫_𝕜 • (b k : V)) := by abel
    rw [hv]
    exact Submodule.add_mem_sup (sum_inner_smul_mem U b v)
      (sub_sum_inner_smul_mem_orthogonal U b v)

/-! 6.51 Dimension of orthogonal complement

If {lit}`V` is finite-dimensional, then {lit}`dim U⟂ = dim V − dim U`. -/

theorem finrank_orthogonal [FiniteDimensional 𝕜 V] (U : Submodule 𝕜 V) :
    finrank 𝕜 Uᗮ = finrank 𝕜 V - finrank 𝕜 U := by
  have := U.finrank_add_finrank_orthogonal (𝕜 := 𝕜)
  omega

/-! 6.52 Orthogonal complement of the orthogonal complement

If {lit}`U` is a finite-dimensional subspace, then {lit}`U = (U⟂)⟂`.

Again the proof follows the book rather than mathlib's
{name}`Submodule.orthogonal_orthogonal`. One inclusion is 6.53:
{lit}`u ∈ U` is orthogonal to every {lit}`w ∈ U⟂`, so {lit}`u ∈ (U⟂)⟂`. For the
other, given {lit}`v ∈ (U⟂)⟂` write {lit}`v = u + w` with {lit}`u ∈ U` and
{lit}`w ∈ U⟂` (6.49); then {lit}`w = v − u` lies in {lit}`(U⟂)⟂` as well, so
{lit}`w ∈ U⟂ ∩ (U⟂)⟂ = {0}` by 6.48(d) and {lit}`v = u ∈ U`. -/

theorem orthogonal_orthogonal (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    Uᗮᗮ = U := by
  -- 6.53: `U ⊆ (U⟂)⟂`
  have h53 : U ≤ Uᗮᗮ := by
    intro u hu w hw
    rw [← inner_conj_symm, hw u hu, map_zero]
  refine le_antisymm (fun v hv => ?_) h53
  -- write `v = u + w` with `u ∈ U` and `w ∈ U⟂`, using 6.49
  have hmem : v ∈ U ⊔ Uᗮ := by rw [(isCompl_orthogonal U).sup_eq_top]; trivial
  obtain ⟨u, huU, w, hwU, rfl⟩ := Submodule.mem_sup.mp hmem
  have hw' : w ∈ Uᗮᗮ := by
    have hsub : w = u + w - u := by abel
    rw [hsub]
    exact Submodule.sub_mem _ hv (h53 huU)
  -- `w ∈ U⟂ ∩ (U⟂)⟂ = {0}` by 6.48(d)
  have hzero : w = 0 :=
    (Submodule.mem_bot 𝕜).mp (by rw [← inf_orthogonal_eq_bot Uᗮ]; exact ⟨hwU, hw'⟩)
  rw [hzero, add_zero]
  exact huU

/-! 6.54 {lit}`U⟂ = {0} ⟺ U = V` (for a finite-dimensional subspace). -/

theorem orthogonal_eq_bot_iff (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    Uᗮ = ⊥ ↔ U = ⊤ :=
  U.orthogonal_eq_bot_iff

/-! # Orthogonal projection -/

/-! 6.55 Definition: orthogonal projection, {lit}`P_U`

For a finite-dimensional subspace {lit}`U`, the orthogonal projection of
{lit}`V` onto {lit}`U` sends {lit}`v = u + w` (with {lit}`u ∈ U`, {lit}`w ∈ U⟂`)
to {lit}`u`. mathlib's {name}`Submodule.starProjection` {lit}`U : V →L[𝕜] V` is
this operator {lit}`P_U`. -/

/-- {lit}`P_U v ∈ U` for every {lit}`v`. -/
example (U : Submodule 𝕜 V) [U.HasOrthogonalProjection] (v : V) :
    U.starProjection v ∈ U :=
  U.starProjection_apply_mem v

/-! 6.56 Example: orthogonal projection onto a one-dimensional subspace.
For {lit}`u ≠ 0` and {lit}`U = span(u)`, {lit}`P_U v = (⟨v, u⟩ / ‖u‖²) u`
(reading Axler's {lit}`⟨v, u⟩` as mathlib's {lit}`⟪u, v⟫`). -/

example (u v : V) :
    (𝕜 ∙ u).starProjection v = (⟪u, v⟫_𝕜 / ((‖u‖ ^ 2 : ℝ) : 𝕜)) • u :=
  Submodule.starProjection_singleton 𝕜 v

/-! 6.57 Properties of orthogonal projection {lit}`P_U`

Suppose {lit}`U` is a finite-dimensional subspace of {lit}`V`. -/

variable (U : Submodule 𝕜 V) [U.HasOrthogonalProjection]

/-- (a) {lit}`P_U ∈ ℒ(V)`: the orthogonal projection is a linear map on
{lit}`V` — in mathlib it is by construction a (continuous) linear map. -/
noncomputable example : V →L[𝕜] V := U.starProjection

/-- (b) {lit}`P_U u = u` for {lit}`u ∈ U`; and more precisely {lit}`P_U v = v ↔
v ∈ U`. -/
theorem starProjection_eq_self_iff (v : V) : U.starProjection v = v ↔ v ∈ U :=
  Submodule.starProjection_eq_self_iff

/-- (f) {lit}`v − P_U v ∈ U⟂` for every {lit}`v`. -/
theorem sub_starProjection_mem_orthogonal (v : V) :
    v - U.starProjection v ∈ Uᗮ :=
  U.sub_starProjection_mem_orthogonal v

/-- (g) {lit}`P_U² = P_U`. -/
theorem starProjection_idem : U.starProjection ∘L U.starProjection = U.starProjection :=
  (Submodule.isIdempotentElem_starProjection U)

/-- (h) {lit}`‖P_U v‖ ≤ ‖v‖` for every {lit}`v`. -/
theorem norm_starProjection_le (v : V) : ‖U.starProjection v‖ ≤ ‖v‖ :=
  U.norm_starProjection_apply_le v

variable {U}

/-- (c) {lit}`P_U w = 0` for {lit}`w ∈ U⟂`. -/
theorem starProjection_eq_zero_of_mem_orthogonal {w : V} (hw : w ∈ Uᗮ) :
    U.starProjection w = 0 := by
  have h1 : U.starProjection w ∈ U := U.starProjection_apply_mem w
  have h2 : U.starProjection w ∈ Uᗮ := by
    have heq : U.starProjection w = w - (w - U.starProjection w) := by abel
    rw [heq]
    exact Uᗮ.sub_mem hw (U.sub_starProjection_mem_orthogonal w)
  have hbot := inf_orthogonal_eq_bot U
  rw [Submodule.eq_bot_iff] at hbot
  exact hbot _ ⟨h1, h2⟩

/-- (d) {lit}`range P_U = U`: the inclusion {lit}`⊆` is the definition of
{lit}`P_U`, and {lit}`⊇` is (b). -/
theorem range_starProjection : LinearMap.range (U.starProjection : V →ₗ[𝕜] V) = U := by
  refine le_antisymm ?_ fun u hu => ⟨u, (starProjection_eq_self_iff U u).mpr hu⟩
  rintro _ ⟨v, rfl⟩
  exact U.starProjection_apply_mem v

/-- (e) {lit}`null P_U = U⟂`: the inclusion {lit}`⊇` is (c), and {lit}`⊆` holds
because {lit}`P_U v = 0` makes {lit}`v = v − P_U v`, which lies in {lit}`U⟂`
by (f). -/
theorem ker_starProjection : LinearMap.ker (U.starProjection : V →ₗ[𝕜] V) = Uᗮ := by
  refine le_antisymm (fun v hv => ?_) fun w hw =>
    LinearMap.mem_ker.mpr (starProjection_eq_zero_of_mem_orthogonal hw)
  have h := sub_starProjection_mem_orthogonal U v
  have h0 : U.starProjection v = 0 := LinearMap.mem_ker.mp hv
  rwa [h0, sub_zero] at h

/-- (i) If {lit}`e₁, …, e_m` is an orthonormal basis of {lit}`U`, then
{lit}`P_U v = ⟨v, e₁⟩e₁ + ⋯ + ⟨v, e_m⟩e_m` — that is, {lit}`P_U v` is the
{lit}`U`-summand of the decomposition 6.50. -/
theorem starProjection_eq_sum_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 U)
    (v : V) : U.starProjection v = ∑ k, ⟪(b k : V), v⟫_𝕜 • (b k : V) :=
  Submodule.eq_starProjection_of_mem_orthogonal (sum_inner_smul_mem U b v)
    (sub_sum_inner_smul_mem_orthogonal U b v)

/-! 6.58 Riesz representation theorem, revisited

Suppose {lit}`V` is finite-dimensional. For {lit}`v ∈ V` define
{lit}`φ_v ∈ V'` by {lit}`φ_v(u) = ⟨u, v⟩`; then {lit}`v ↦ φ_v` is a one-to-one
map of {lit}`V` onto {lit}`V'`. Reading Axler's {lit}`⟨u, v⟩` as mathlib's
{lit}`⟪v, u⟫`, the map is {lit}`v ↦ innerₛₗ 𝕜 v` (a *conjugate*-linear map when
{lit}`𝕜 = ℂ`, as the book's caution notes, which is why it is stated here as a
bijection of underlying sets rather than a linear isomorphism).

This restates {lit}`LADR.Section_6B.riesz_representation` (6.42), and the proof
below is Axler's second one: it uses orthogonal complements instead of an
orthonormal basis. Given {lit}`φ ≠ 0`, {lit}`null φ ≠ V`, so
{lit}`(null φ)⟂ ≠ {0}` by 6.54; pick {lit}`w ≠ 0` in it and rescale to
{lit}`v = (φ(w)‾/‖w‖²)w`, which satisfies {lit}`φ(v) = ‖v‖²`. Every {lit}`u`
then splits as {lit}`u = (u − (φ(u)/φ(v))v) + (φ(u)/φ(v))v` with the first term
in {lit}`null φ`, hence orthogonal to {lit}`v`, and taking the inner product
with {lit}`v` gives {lit}`⟨u, v⟩ = φ(u)`. -/

theorem riesz_bijective [FiniteDimensional 𝕜 V] :
    Function.Bijective (fun v : V => (innerₛₗ 𝕜 v : V →ₗ[𝕜] 𝕜)) := by
  constructor
  · -- one-to-one, as in 6.42
    intro v v' h
    have hu : ∀ u : V, ⟪v, u⟫_𝕜 = ⟪v', u⟫_𝕜 := fun u =>
      congrArg (fun f : V →ₗ[𝕜] 𝕜 => f u) h
    have hzero : ⟪v - v', v - v'⟫_𝕜 = 0 := by
      rw [inner_sub_left, hu (v - v'), sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  · intro φ
    by_cases hφ : φ = 0
    · exact ⟨0, by simp [hφ]⟩
    -- `null φ ≠ V`, so `(null φ)⟂ ≠ {0}` by 6.54
    have hker : LinearMap.ker φ ≠ ⊤ := by
      intro h
      exact hφ (by ext u; exact LinearMap.mem_ker.mp (h ▸ Submodule.mem_top))
    have hbot : (LinearMap.ker φ)ᗮ ≠ ⊥ := fun h =>
      hker ((orthogonal_eq_bot_iff _).mp h)
    obtain ⟨w, hw_mem, hw0⟩ := Submodule.ne_bot_iff _ |>.mp hbot
    -- `w ∉ null φ`, since `null φ ∩ (null φ)⟂ = {0}` by 6.48(d)
    have hφw : φ w ≠ 0 := by
      intro h
      refine hw0 ?_
      have hmem : w ∈ LinearMap.ker φ ⊓ (LinearMap.ker φ)ᗮ :=
        ⟨LinearMap.mem_ker.mpr h, hw_mem⟩
      rw [inf_orthogonal_eq_bot] at hmem
      exact hmem
    set r : 𝕜 := ((‖w‖ ^ 2 : ℝ) : 𝕜) with hr
    have hr0 : r ≠ 0 := by
      rw [hr, ne_eq, RCLike.ofReal_eq_zero, pow_eq_zero_iff (two_ne_zero), norm_eq_zero]
      exact hw0
    -- 6.59: rescale `w`
    set v : V := (conj (φ w) / r) • w with hv
    have hww : ⟪w, w⟫_𝕜 = r := by
      rw [hr, inner_self_eq_norm_sq_to_K]
      push_cast
      ring
    have hv_mem : v ∈ (LinearMap.ker φ)ᗮ := Submodule.smul_mem _ _ hw_mem
    -- `φ(v) = ‖v‖²`
    have hvφ : φ v = ⟪v, v⟫_𝕜 := by
      rw [hv, map_smul, inner_smul_left, inner_smul_right, hww, smul_eq_mul, map_div₀,
        RCLike.conj_conj, hr, RCLike.conj_ofReal]
      field_simp
    have hv0 : v ≠ 0 := by
      rw [hv]
      exact smul_ne_zero (div_ne_zero (by simpa using hφw) hr0) hw0
    have hφv : φ v ≠ 0 := by
      rw [hvφ]
      exact inner_self_ne_zero.mpr hv0
    refine ⟨v, ?_⟩
    ext u
    -- `u = (u − (φu/φv)v) + (φu/φv)v`, the first term lying in `null φ`
    have hdecomp : u - (φ u / φ v) • v ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hφv, sub_self]
    have horth : ⟪v, u - (φ u / φ v) • v⟫_𝕜 = 0 := by
      have h0 := hv_mem _ hdecomp
      rw [← inner_conj_symm, h0, map_zero]
    have hsplit : ⟪v, u⟫_𝕜 = ⟪v, u - (φ u / φ v) • v⟫_𝕜 + (φ u / φ v) * ⟪v, v⟫_𝕜 := by
      rw [inner_sub_right, inner_smul_right]
      ring
    show ⟪v, u⟫_𝕜 = φ u
    rw [hsplit, horth, zero_add, ← hvφ, div_mul_cancel₀ _ hφv]

/-- The Riesz vector of a linear functional: by 6.58 there is exactly one
{lit}`w ∈ V` with {lit}`φ(u) = ⟨u, w⟩` for all {lit}`u` (Axler's {lit}`⟨u, w⟩`
being mathlib's {lit}`⟪w, u⟫`), and this names it. -/
noncomputable def rieszVector [FiniteDimensional 𝕜 V] (φ : V →ₗ[𝕜] 𝕜) : V :=
  (riesz_bijective.existsUnique φ).choose

@[simp] theorem innerₛₗ_rieszVector [FiniteDimensional 𝕜 V] (φ : V →ₗ[𝕜] 𝕜) :
    innerₛₗ 𝕜 (rieszVector φ) = φ :=
  (riesz_bijective.existsUnique φ).choose_spec.1

/-- {lit}`φ(u) = ⟨u, rieszVector φ⟩` for every {lit}`u`. -/
theorem rieszVector_spec [FiniteDimensional 𝕜 V] (φ : V →ₗ[𝕜] 𝕜) (u : V) :
    φ u = ⟪rieszVector φ, u⟫_𝕜 := by
  conv_lhs => rw [← innerₛₗ_rieszVector φ]
  rfl

/-- …and it is the only such vector. -/
theorem rieszVector_unique [FiniteDimensional 𝕜 V] {φ : V →ₗ[𝕜] 𝕜} {w : V}
    (hw : ∀ u : V, φ u = ⟪w, u⟫_𝕜) : rieszVector φ = w :=
  ((riesz_bijective.existsUnique φ).choose_spec.2 w (by ext u; exact (hw u).symm)).symm

/-! 6.61 Minimizing distance to a subspace

If {lit}`U` is finite-dimensional, {lit}`v ∈ V`, and {lit}`u ∈ U`, then
{lit}`‖v − P_U v‖ ≤ ‖v − u‖`, with equality iff {lit}`u = P_U v`. Thus
{lit}`P_U v` is the point of {lit}`U` closest to {lit}`v`. -/

theorem minimizing_distance (v : V) (u : V) (hu : u ∈ U) :
    ‖v - U.starProjection v‖ ≤ ‖v - u‖ := by
  have hmem : U.starProjection v - u ∈ U :=
    U.sub_mem (U.starProjection_apply_mem v) hu
  have horth : ⟪v - U.starProjection v, U.starProjection v - u⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal' U _).mp (U.sub_starProjection_mem_orthogonal v) _ hmem
  have hpyth : ‖v - u‖ ^ 2 =
      ‖v - U.starProjection v‖ ^ 2 + ‖U.starProjection v - u‖ ^ 2 := by
    have hsum : v - u = (v - U.starProjection v) + (U.starProjection v - u) := by abel
    rw [hsum]; simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  nlinarith [norm_nonneg (v - U.starProjection v), norm_nonneg (v - u),
    sq_nonneg ‖U.starProjection v - u‖, hpyth]


/-! # Pseudoinverse -/

section Pseudoinverse

open scoped Pointwise

variable [FiniteDimensional 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]

/-! 6.63 Example: approximating the sine function. The degree-{lit}`≤ 5` polynomial
{lit}`u` minimizing {lit}`∫₋π^π |sin x − u(x)|² dx` is the orthogonal projection of
{lit}`sin` onto {lit}`𝒫₅` in the {lit}`L²` inner product on `C[-π,π]` — the content
of the minimization theorem 6.61. (Axler's explicit numeric {lit}`u` merely replaces the
π's of the exact projection with decimals.) We formalize the mathematical claim:
the projection is the best degree-≤5 `L²`-approximation to {lit}`sin`. Building the exact
numeric {lit}`u` is Exercise 6C.18. -/

section Example_6_63

/-- Monomials {lit}`x^k` as elements of `C[-π,π]`. -/
noncomputable def monoL2 (k : ℕ) : L2C (-Real.pi) Real.pi := ⟨fun x => (x : ℝ) ^ k, by fun_prop⟩

/-- The degree-{lit}`≤ 5` polynomial subspace {lit}`𝒫₅` of `C[-π,π]`. -/
noncomputable def polyDegLE5 : Submodule ℝ (L2C (-Real.pi) Real.pi) :=
  Submodule.span ℝ (Set.range (fun k : Fin 6 => monoL2 k))

instance : FiniteDimensional ℝ polyDegLE5 :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- {lit}`sin` as an element of `C[-π,π]`. -/
noncomputable def sinL2 : L2C (-Real.pi) Real.pi := ⟨fun x => Real.sin x, by fun_prop⟩

/-- 6.63: the orthogonal projection of {lit}`sin` onto {lit}`𝒫₅` is the best degree-{lit}`≤ 5`
`L²`-approximation to {lit}`sin` on {lit}`[-π,π]`: for every polynomial {lit}`u ∈ 𝒫₅`,
`‖sin − P_{𝒫₅} sin‖ ≤ ‖sin − u‖` (equivalently `∫₋π^π|sin − P|² ≤ ∫₋π^π|sin − u|²`).
This is 6.61 instantiated at `V = C[-π,π]`, {lit}`U = 𝒫₅`, {lit}`v = sin`. -/
theorem sin_best_approx (u : L2C (-Real.pi) Real.pi) (hu : u ∈ polyDegLE5) :
    ‖sinL2 - polyDegLE5.starProjection sinL2‖ ≤ ‖sinL2 - u‖ :=
  minimizing_distance sinL2 u hu

end Example_6_63

/-! 6.67 The restriction of {lit}`T` to {lit}`(null T)⟂` is an injective map of
{lit}`(null T)⟂` onto {lit}`range T`. -/

/-- {lit}`T` restricted to {lit}`(null T)⟂`, with codomain {lit}`range T`. -/
noncomputable def restr (T : V →ₗ[𝕜] W) : (Submodule.orthogonal (LinearMap.ker T)) →ₗ[𝕜] (LinearMap.range T) :=
  LinearMap.codRestrict (LinearMap.range T) (T ∘ₗ (Submodule.orthogonal (LinearMap.ker T)).subtype)
    (fun x => ⟨x, rfl⟩)

omit [FiniteDimensional 𝕜 V] in
@[simp] theorem restr_coe (T : V →ₗ[𝕜] W) (x : (Submodule.orthogonal (LinearMap.ker T))) :
    (restr T x : W) = T (x : V) := rfl

omit [FiniteDimensional 𝕜 V] in
theorem restr_injective (T : V →ₗ[𝕜] W) : Function.Injective (restr T) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hx0 : T (x : V) = 0 := by have := congrArg (Subtype.val) hx; simpa using this
  have : (x : V) ∈ LinearMap.ker T ⊓ (Submodule.orthogonal (LinearMap.ker T)) := ⟨hx0, x.2⟩
  rw [Submodule.inf_orthogonal_eq_bot] at this
  ext; simpa using this

theorem restr_surjective (T : V →ₗ[𝕜] W) : Function.Surjective (restr T) := by
  rintro ⟨w, v, rfl⟩
  have hsup : (LinearMap.ker T) ⊔ (Submodule.orthogonal (LinearMap.ker T)) = ⊤ :=
    ((LinearMap.ker T).isCompl_orthogonal_of_hasOrthogonalProjection).sup_eq_top
  have hv : v ∈ (LinearMap.ker T) ⊔ (Submodule.orthogonal (LinearMap.ker T)) := hsup ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at hv
  obtain ⟨u, hu, x, hx, rfl⟩ := hv
  refine ⟨⟨x, hx⟩, ?_⟩
  ext
  simp [LinearMap.mem_ker.mp hu]

/-- The isomorphism {lit}`(null T)⟂ ≃ range T` induced by {lit}`T`. -/
noncomputable def restrEquiv (T : V →ₗ[𝕜] W) : (Submodule.orthogonal (LinearMap.ker T)) ≃ₗ[𝕜] (LinearMap.range T) :=
  LinearEquiv.ofBijective (restr T) ⟨restr_injective T, restr_surjective T⟩

@[simp] theorem restrEquiv_coe (T : V →ₗ[𝕜] W) (x) : (restrEquiv T) x = restr T x := rfl

/-! 6.68 Definition: pseudoinverse, {lit}`T†`. For {lit}`T ∈ ℒ(V, W)`,
{lit}`T† w = (T|_(null T)⟂)⁻¹ (P_(range T) w)`. -/

/-- The pseudoinverse {lit}`T† ∈ ℒ(W, V)`. -/
noncomputable def pinv (T : V →ₗ[𝕜] W) : W →ₗ[𝕜] V :=
  (Submodule.orthogonal (LinearMap.ker T)).subtype ∘ₗ (restrEquiv T).symm.toLinearMap ∘ₗ
    ((LinearMap.range T).orthogonalProjection : W →L[𝕜] (LinearMap.range T))

@[inherit_doc] scoped postfix:max "†" => pinv

/-- 6.69 (a) If {lit}`T` is invertible then {lit}`T† = T⁻¹`. Axler's proof reads
this straight off the definition: {lit}`null T = {0}` gives
{lit}`(null T)⟂ = V`, so {lit}`T|_(null T)⟂ = T`, and {lit}`range T = W` makes
{lit}`P_(range T)` the identity on {lit}`W`. -/
theorem pinv_eq_symm (e : V ≃ₗ[𝕜] W) : (e : V →ₗ[𝕜] W)† = (e.symm : W →ₗ[𝕜] V) := by
  ext w
  -- `(null T)⟂ = V`, so `e.symm w` lies in it
  have hmem : e.symm w ∈ Submodule.orthogonal (LinearMap.ker (e : V →ₗ[𝕜] W)) := by
    rw [LinearMap.ker_eq_bot.mpr e.injective, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  -- `range T = W`, so `P_(range T)` fixes `w`
  have hw : w ∈ LinearMap.range (e : V →ₗ[𝕜] W) := ⟨e.symm w, by simp⟩
  have hproj : (LinearMap.range (e : V →ₗ[𝕜] W)).orthogonalProjection w =
      (⟨w, hw⟩ : LinearMap.range (e : V →ₗ[𝕜] W)) :=
    Submodule.orthogonalProjection_mem_subspace_eq_self
      (⟨w, hw⟩ : LinearMap.range (e : V →ₗ[𝕜] W))
  -- and `T|_(null T)⟂` sends `e.symm w` to `w`, so its inverse sends `w` back
  have hrestr : restrEquiv (e : V →ₗ[𝕜] W) ⟨e.symm w, hmem⟩ = ⟨w, hw⟩ := by
    apply Subtype.ext
    simp
  show ((restrEquiv (e : V →ₗ[𝕜] W)).symm
    ((LinearMap.range (e : V →ₗ[𝕜] W)).orthogonalProjection w) : V) = e.symm w
  rw [hproj, ← hrestr, LinearEquiv.symm_apply_apply]

/-- 6.69 (b) {lit}`T T† = P_(range T)`. -/
theorem T_comp_pinv (T : V →ₗ[𝕜] W) :
    T ∘ₗ T† = ((LinearMap.range T).starProjection : W →ₗ[𝕜] W) := by
  ext w
  simp only [LinearMap.comp_apply, pinv, Submodule.coe_subtype,
    ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe]
  rw [← restr_coe, ← restrEquiv_coe, LinearEquiv.apply_symm_apply,
    Submodule.starProjection_apply]

/-- 6.69 (c) {lit}`T† T = P_(null T)⟂`. -/
theorem pinv_comp_T (T : V →ₗ[𝕜] W) :
    T† ∘ₗ T = ((Submodule.orthogonal (LinearMap.ker T)).starProjection : V →ₗ[𝕜] V) := by
  ext v
  simp only [LinearMap.comp_apply, pinv, Submodule.coe_subtype,
    ContinuousLinearMap.coe_coe, LinearEquiv.coe_coe]
  set x := (Submodule.orthogonal (LinearMap.ker T)).orthogonalProjection v with hx
  have hTx : T ((x : V)) = T v := by
    have hmem : v - (x : V) ∈ LinearMap.ker T := by
      have h1 : (x : V) = (Submodule.orthogonal (LinearMap.ker T)).starProjection v :=
        (Submodule.starProjection_apply _ v).symm
      rw [h1]
      have h2 := (LinearMap.ker T).starProjection_add_starProjection_orthogonal v
      have h3 : v - (Submodule.orthogonal (LinearMap.ker T)).starProjection v = (LinearMap.ker T).starProjection v := by
        rw [eq_comm, eq_sub_iff_add_eq]; exact h2
      rw [h3]; exact (LinearMap.ker T).starProjection_apply_mem v
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem
    exact hmem.symm
  have hproj : (LinearMap.range T).orthogonalProjection (T v) = restr T x := by
    apply Subtype.ext
    rw [restr_coe, hTx]
    exact congrArg Subtype.val
      (Submodule.orthogonalProjection_mem_subspace_eq_self (⟨T v, ⟨v, rfl⟩⟩ : LinearMap.range T))
  rw [hproj, ← restrEquiv_coe, LinearEquiv.symm_apply_apply, Submodule.starProjection_apply]


omit [FiniteDimensional 𝕜 V] in
/-- Membership in the coset {lit}`a + p` of a subspace {lit}`p`, written with
mathlib's pointwise {lit}`+ᵥ`. -/
theorem mem_vadd_coe_iff {p : Submodule 𝕜 V} {a v : V} :
    v ∈ a +ᵥ (p : Set V) ↔ v - a ∈ p := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨v - a, h, by simp⟩

/-- 6.70 (a) {lit}`T† w` is a *best approximate solution* of {lit}`T v = w`:
{lit}`‖T (T† w) − w‖ ≤ ‖T v − w‖` for every {lit}`v`, with equality exactly when
{lit}`v ∈ T†w + null T`. Axler's proof: split
{lit}`T v − w = (T v − T T†w) + (T T†w − w)`, whose first term lies in
{lit}`range T` and whose second lies in {lit}`(range T)⟂` because
{lit}`T T† = P_(range T)` (6.69(b)); the Pythagorean theorem then gives the
inequality, with equality iff the first term vanishes. -/
theorem pinv_best_approx (T : V →ₗ[𝕜] W) (w : W) (v : V) :
    ‖T (T† w) - w‖ ≤ ‖T v - w‖ ∧
      (‖T (T† w) - w‖ = ‖T v - w‖ ↔ v ∈ T† w +ᵥ (LinearMap.ker T : Set V)) := by
  have hproj : T (T† w) = (LinearMap.range T).starProjection w := by
    have := LinearMap.congr_fun (T_comp_pinv T) w; simpa using this
  -- `T v − T T†w ∈ range T` and `T T†w − w ∈ (range T)⟂`
  have hmem : T v - T (T† w) ∈ LinearMap.range T := by
    refine Submodule.sub_mem _ ⟨v, rfl⟩ ?_
    rw [hproj]
    exact (LinearMap.range T).starProjection_apply_mem w
  have hperp : T (T† w) - w ∈ (LinearMap.range T)ᗮ := by
    rw [hproj, ← neg_sub w]
    exact Submodule.neg_mem _ ((LinearMap.range T).sub_starProjection_mem_orthogonal w)
  have horth : ⟪T v - T (T† w), T (T† w) - w⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal _ _).mp hperp _ hmem
  have hpyth : ‖T v - w‖ ^ 2 = ‖T v - T (T† w)‖ ^ 2 + ‖T (T† w) - w‖ ^ 2 := by
    have hsum : T v - w = (T v - T (T† w)) + (T (T† w) - w) := by abel
    rw [hsum]; simp only [pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [norm_nonneg (T (T† w) - w), norm_nonneg (T v - w),
      sq_nonneg ‖T v - T (T† w)‖, hpyth]
  · -- equality forces `T v = T T†w`, i.e. `v − T†w ∈ null T`
    intro heq
    have h0 : ‖T v - T (T† w)‖ ^ 2 = 0 := by rw [← heq] at hpyth; linarith
    have hz : T v - T (T† w) = 0 :=
      norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
    rw [mem_vadd_coe_iff, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact sub_eq_zero.mp hz
  · intro hv
    have hker : v - T† w ∈ LinearMap.ker T := mem_vadd_coe_iff.mp hv
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hker
    rw [hker]

/-- 6.70 (b) Among the vectors {lit}`v ∈ T†w + null T` — exactly those making
{lit}`‖T v − w‖` as small as possible, by (a) — the solution {lit}`T†w` has the
smallest norm: {lit}`‖T†w‖ ≤ ‖v‖`, with equality only for {lit}`v = T†w`. -/
theorem pinv_minimal_norm (T : V →ₗ[𝕜] W) (w : W) (v : V)
    (hv : v ∈ T† w +ᵥ (LinearMap.ker T : Set V)) (hne : v ≠ T† w) : ‖T† w‖ < ‖v‖ := by
  -- T†w ∈ (null T)⟂ and v − T†w ∈ null T, so they are orthogonal
  have hpinv_mem : T† w ∈ Submodule.orthogonal (LinearMap.ker T) := by
    show ((restrEquiv T).symm ((LinearMap.range T).orthogonalProjection w) : V) ∈ _
    exact SetLike.coe_mem _
  have hsub_mem : v - T† w ∈ LinearMap.ker T := mem_vadd_coe_iff.mp hv
  have horth : ⟪T† w, v - T† w⟫_𝕜 = 0 := by
    rw [inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ _).mp hpinv_mem _ hsub_mem
  have hadd : T† w + (v - T† w) = v := by abel
  have hnorm : ‖v‖ ^ 2 = ‖T† w‖ ^ 2 + ‖v - T† w‖ ^ 2 := by
    rw [pow_two, pow_two, pow_two]
    conv_lhs => rw [← hadd]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (T† w) (v - T† w) horth
  have hpos : 0 < ‖v - T† w‖ ^ 2 := by
    have : v - T† w ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hlt : ‖T† w‖ ^ 2 < ‖v‖ ^ 2 := by rw [hnorm]; linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt

/-! 6.72 {lit}`T† w = (T|_(null T)⟂)⁻¹ (P_(range T) w)` — for us that *is* the
definition of {name}`pinv`. What makes it usable for computing, as in 6.71, is
the characterization it expresses: {lit}`T† w` is *the* vector
{lit}`v ∈ (null T)⟂` with {lit}`T v = P_(range T) w`. -/

theorem pinv_apply (T : V →ₗ[𝕜] W) (w : W) :
    T† w = ((restrEquiv T).symm ((LinearMap.range T).orthogonalProjection w) : V) := rfl

theorem pinv_mem_orthogonal (T : V →ₗ[𝕜] W) (w : W) :
    T† w ∈ Submodule.orthogonal (LinearMap.ker T) := by
  rw [pinv_apply]
  exact SetLike.coe_mem _

theorem pinv_eq_of (T : V →ₗ[𝕜] W) {w : W} {v : V}
    (hmem : v ∈ Submodule.orthogonal (LinearMap.ker T))
    (hT : T v = (LinearMap.range T).starProjection w) : T† w = v := by
  have h1 : T (T† w) = (LinearMap.range T).starProjection w := by
    have := LinearMap.congr_fun (T_comp_pinv T) w; simpa using this
  have hsub : T† w - v ∈ LinearMap.ker T := by
    rw [LinearMap.mem_ker, map_sub, h1, hT, sub_self]
  have hsub' : T† w - v ∈ Submodule.orthogonal (LinearMap.ker T) :=
    Submodule.sub_mem _ (pinv_mem_orthogonal T w) hmem
  have hbot := inf_orthogonal_eq_bot (LinearMap.ker T)
  rw [Submodule.eq_bot_iff] at hbot
  exact sub_eq_zero.mp (hbot _ ⟨hsub, hsub'⟩)

/-! 6.71 Example: pseudoinverse of a linear map from {lit}`𝔽⁴` to {lit}`𝔽³` -/

/-- {lit}`T(a, b, c, d) = (a + b + c, 2c + d, 0)`, which is neither injective nor
surjective. -/
def T671 : EuclideanSpace 𝕜 (Fin 4) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 3) where
  toFun v := !₂[v 0 + v 1 + v 2, 2 * v 2 + v 3, 0]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

/-- {lit}`null T = {(a, b, c, d) : a + b + c = 0 and 2c + d = 0}`, which is
spanned by {lit}`(−1, 1, 0, 0)`, {lit}`(−1, 0, 1, −2)`. -/
theorem ker_T671 : LinearMap.ker (T671 (𝕜 := 𝕜)) =
    Submodule.span 𝕜 {!₂[-1, 1, 0, 0], !₂[-1, 0, 1, -2]} := by
  apply le_antisymm
  · intro u hu
    rw [LinearMap.mem_ker] at hu
    have h0 : u 0 + u 1 + u 2 = 0 := by
      have := congrArg (fun z : EuclideanSpace 𝕜 (Fin 3) => z 0) hu
      simpa [T671] using this
    have h1 : 2 * u 2 + u 3 = 0 := by
      have := congrArg (fun z : EuclideanSpace 𝕜 (Fin 3) => z 1) hu
      simpa [T671] using this
    refine Submodule.mem_span_pair.mpr ⟨u 1, u 2, ?_⟩
    ext i
    fin_cases i <;> simp <;>
      first
        | linear_combination -h0
        | linear_combination -h1
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl) <;>
      · rw [SetLike.mem_coe, LinearMap.mem_ker]
        ext i
        fin_cases i <;> simp [T671]

/-- {lit}`range T = {(x, y, 0)}`, so {lit}`P_(range T)(x, y, z) = (x, y, 0)`. -/
theorem starProjection_range_T671 (v : EuclideanSpace 𝕜 (Fin 3)) :
    (LinearMap.range (T671 (𝕜 := 𝕜))).starProjection v = !₂[v 0, v 1, 0] := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ⟨!₂[v 0, 0, 0, v 1], ?_⟩ ?_
  · ext i; fin_cases i <;> simp [T671]
  · rintro _ ⟨u, rfl⟩
    simp [T671, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three]

/-- 6.71 Hence {lit}`T†(x, y, z) = (5x − 2y, 5x − 2y, x + 4y, −2x + 3y)/11`. -/
theorem pinv_T671 (v : EuclideanSpace 𝕜 (Fin 3)) :
    (T671 (𝕜 := 𝕜))† v = (11 : 𝕜)⁻¹ •
      !₂[5 * v 0 - 2 * v 1, 5 * v 0 - 2 * v 1, v 0 + 4 * v 1, -2 * v 0 + 3 * v 1] := by
  have h11 : (11 : 𝕜) ≠ 0 := by norm_num
  refine pinv_eq_of _ ?_ ?_
  · -- the answer is orthogonal to `null T`
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have h0 : u 0 + u 1 + u 2 = 0 := by
      have := congrArg (fun z : EuclideanSpace 𝕜 (Fin 3) => z 0) hu
      simpa [T671] using this
    have h1 : 2 * u 2 + u 3 = 0 := by
      have := congrArg (fun z : EuclideanSpace 𝕜 (Fin 3) => z 1) hu
      simpa [T671] using this
    have h0' : conj (u 0) + conj (u 1) + conj (u 2) = 0 := by
      rw [← map_add, ← map_add, h0, map_zero]
    have h1' : 2 * conj (u 2) + conj (u 3) = 0 := by
      simpa [map_ofNat] using congrArg (starRingEnd 𝕜) h1
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_four, PiLp.smul_apply,
      smul_eq_mul, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    linear_combination (5 * v 0 - 2 * v 1) * h0' + (-2 * v 0 + 3 * v 1) * h1'
  · -- and `T` sends it to `P_(range T) v`
    rw [starProjection_range_T671]
    ext i
    fin_cases i <;> simp [T671] <;> field_simp <;> ring

end Pseudoinverse

/-! # Exercises 6C -/

/-- 6C.1 {lit}`{v₁, …, vₘ}⟂ = (span(v₁, …, vₘ))⟂`, the orthogonal complement on
the left being that of the *set* {lit}`{v₁, …, vₘ}` ({name}`setOrthogonal`). -/
theorem exercise_6C_1 {m : ℕ} (v : Fin m → V) :
    setOrthogonal (𝕜 := 𝕜) (Set.range v) = (Submodule.span 𝕜 (Set.range v))ᗮ := by
  sorry

/-- 6C.2 If a basis of {lit}`V` extends a basis {lit}`u₁, …, uₘ` of {lit}`U`, then
Gram–Schmidt produces {lit}`e₁, …, eₘ, f₁, …, fₙ` with {lit}`e₁, …, eₘ` spanning
{lit}`U` and {lit}`f₁, …, fₙ` spanning {lit}`U⟂`. -/
theorem exercise_6C_2 [FiniteDimensional 𝕜 V] {m n : ℕ}
    (b : Module.Basis (Fin (m + n)) 𝕜 V)
    (h : finrank 𝕜 V = Fintype.card (Fin (m + n)))
    (U : Submodule 𝕜 V)
    (hU : U = Submodule.span 𝕜 (Set.range fun i : Fin m => b (Fin.castAdd n i))) :
    let e := InnerProductSpace.gramSchmidtOrthonormalBasis h (b : Fin (m + n) → V)
    Submodule.span 𝕜 (Set.range fun i : Fin m => (e (Fin.castAdd n i) : V)) = U ∧
      Submodule.span 𝕜 (Set.range fun j : Fin n => (e (Fin.natAdd m j) : V)) = Uᗮ := by
  sorry

/-- 6C.3 The subspace {lit}`U = span((1,2,3,−4), (−5,4,3,2))` of {lit}`ℝ⁴`. -/
noncomputable def U6C3 : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) :=
  Submodule.span ℝ {!₂[1, 2, 3, -4], !₂[-5, 4, 3, 2]}

/-- 6C.3 answer: an orthonormal basis of {lit}`U` — two concrete vectors to be
supplied. -/
noncomputable def onb6C3 : Fin 2 → EuclideanSpace ℝ (Fin 4) := sorry

/-- 6C.3 answer: an orthonormal basis of {lit}`U⟂`. -/
noncomputable def onb6C3perp : Fin 2 → EuclideanSpace ℝ (Fin 4) := sorry

/-- 6C.3 In {lit}`ℝ⁴`, with {lit}`U = span((1,2,3,−4), (−5,4,3,2))`, find an
orthonormal basis of {lit}`U` and an orthonormal basis of {lit}`U⟂`. -/
theorem exercise_6C_3 :
    (Orthonormal ℝ onb6C3 ∧ Submodule.span ℝ (Set.range onb6C3) = U6C3) ∧
      (Orthonormal ℝ onb6C3perp ∧ Submodule.span ℝ (Set.range onb6C3perp) = U6C3ᗮ) := by
  sorry

/-- 6C.4 Converse to 6.30(b): if {lit}`‖eₖ‖ = 1` for each {lit}`k` and Parseval's
equality {lit}`‖v‖² = ∑ |⟨v, eₖ⟩|²` holds for all {lit}`v`, then {lit}`e₁, …, eₙ`
is an orthonormal basis. -/
theorem exercise_6C_4 [FiniteDimensional 𝕜 V] {n : ℕ} (e : Fin n → V)
    (hnorm : ∀ k, ‖e k‖ = 1)
    (hpar : ∀ v : V, ‖v‖ ^ 2 = ∑ k, ‖⟪e k, v⟫_𝕜‖ ^ 2) :
    Orthonormal 𝕜 e ∧ Submodule.span 𝕜 (Set.range e) = ⊤ := by
  sorry

/-- 6C.5 {lit}`P_(U⟂) = I − P_U`. -/
theorem exercise_6C_5 (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    Uᗮ.starProjection = 1 - U.starProjection := by
  sorry

/-- 6C.6 If {lit}`V` is finite-dimensional and {lit}`T ∈ ℒ(V, W)`, then
{lit}`T = T P_(null T)⟂ = P_(range T) T`. -/
theorem exercise_6C_6 [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    T = T ∘ₗ ((Submodule.orthogonal (LinearMap.ker T)).starProjection : V →ₗ[𝕜] V) ∧
      T = ((LinearMap.range T).starProjection : W →ₗ[𝕜] W) ∘ₗ T := by
  sorry

/-- 6C.7 For finite-dimensional subspaces {lit}`X, Y`, {lit}`P_X P_Y = 0` iff
{lit}`⟨x, y⟩ = 0` for all {lit}`x ∈ X`, {lit}`y ∈ Y`. -/
theorem exercise_6C_7 (X Y : Submodule 𝕜 V) [FiniteDimensional 𝕜 X]
    [FiniteDimensional 𝕜 Y] :
    X.starProjection ∘L Y.starProjection = 0 ↔
      ∀ x ∈ X, ∀ y ∈ Y, ⟪x, y⟫_𝕜 = 0 := by
  sorry

/-- 6C.8 Let {lit}`φ(u) = ⟨u, v⟩` be the linear functional on a finite-dimensional
subspace {lit}`U`, i.e. {lit}`φ = ⟪v, ·⟫` restricted to {lit}`U`, and let
{lit}`w ∈ U` be *the* vector representing it given by the Riesz representation
theorem applied to {lit}`U` (6.58 here, 6.42 in the book — the bijection
{lit}`w ↦ φ_w` supplies both existence and uniqueness). Then {lit}`w = P_U v`. -/
theorem exercise_6C_8 (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] (v : V) :
    ((rieszVector (V := U) ((innerₛₗ 𝕜 v).comp U.subtype) : U) : V) =
      U.starProjection v := by
  sorry

/-- 6C.9 If {lit}`P² = P` and {lit}`null P ⟂ range P`, then {lit}`P = P_U` for
some subspace {lit}`U`. -/
theorem exercise_6C_9 [FiniteDimensional 𝕜 V] (P : V →ₗ[𝕜] V) (hP : P ∘ₗ P = P)
    (horth : ∀ x ∈ LinearMap.ker P, ∀ y ∈ LinearMap.range P, ⟪x, y⟫_𝕜 = 0) :
    ∃ U : Submodule 𝕜 V, (U.starProjection : V →ₗ[𝕜] V) = P := by
  sorry

/-- 6C.10 If {lit}`V` is finite-dimensional, {lit}`P² = P`, and {lit}`‖Pv‖ ≤ ‖v‖`
for every {lit}`v`, then {lit}`P = P_U` for some subspace {lit}`U`. -/
theorem exercise_6C_10 [FiniteDimensional 𝕜 V] (P : V →ₗ[𝕜] V)
    (hP : P ∘ₗ P = P) (hnorm : ∀ v, ‖P v‖ ≤ ‖v‖) :
    ∃ U : Submodule 𝕜 V, (U.starProjection : V →ₗ[𝕜] V) = P := by
  sorry

/-- 6C.11 For {lit}`T ∈ ℒ(V)` and a finite-dimensional subspace {lit}`U`,
{lit}`U` is invariant under {lit}`T` iff {lit}`P_U T P_U = T P_U`. -/
theorem exercise_6C_11 (T : V →ₗ[𝕜] V) (U : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 U] :
    (∀ u ∈ U, T u ∈ U) ↔
      (U.starProjection : V →ₗ[𝕜] V) ∘ₗ T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) =
        T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) := by
  sorry

/-- 6C.12 For finite-dimensional {lit}`V`, {lit}`T ∈ ℒ(V)`, and a subspace
{lit}`U`: both {lit}`U` and {lit}`U⟂` are invariant under {lit}`T` iff
{lit}`P_U T = T P_U`. -/
theorem exercise_6C_12 [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V)
    (U : Submodule 𝕜 V) :
    ((∀ u ∈ U, T u ∈ U) ∧ ∀ w ∈ Uᗮ, T w ∈ Uᗮ) ↔
      (U.starProjection : V →ₗ[𝕜] V) ∘ₗ T = T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) := by
  sorry

/-- 6C.13 For {lit}`𝔽 = ℝ`, the map {lit}`v ↦ φ_v` with {lit}`φ_v(u) = ⟨u, v⟩`
(mathlib's {lit}`⟪v, u⟫`). Over {lit}`ℝ` it is genuinely linear — over {lit}`ℂ`
it would only be conjugate-linear, as the caution accompanying 6.58 notes. -/
noncomputable def phi6C13 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    V →ₗ[ℝ] Module.Dual ℝ V where
  toFun v := innerₛₗ ℝ v
  map_add' u v := by ext w; simp
  map_smul' c v := by ext w; simp

/-- 6C.13 (a) {lit}`v ↦ φ_v` is an injective linear map from {lit}`V` to
{lit}`V′`. -/
theorem exercise_6C_13a {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Function.Injective (phi6C13 (V := V)) := by
  sorry

/-- 6C.13 (b) With (a) and a dimension count, {lit}`v ↦ φ_v` is an isomorphism of
{lit}`V` onto {lit}`V′`. (This is an alternative proof of Riesz for
{lit}`𝔽 = ℝ`, so 6.42/6.58 may not be used here.) -/
theorem exercise_6C_13b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Function.Bijective (phi6C13 (V := V)) := by
  sorry

/-- 6C.14 If {lit}`e₁, …, eₙ` is an orthonormal basis of {lit}`V`, then its dual
basis is {lit}`e₁, …, eₙ` under the Riesz identification: {lit}`εᵢ(eⱼ) = ⟨eᵢ, eⱼ⟩`. -/
theorem exercise_6C_14 [FiniteDimensional 𝕜 V] {n : ℕ}
    (e : OrthonormalBasis (Fin n) 𝕜 V) (i j : Fin n) :
    e.toBasis.dualBasis i (e j) = ⟪e i, e j⟫_𝕜 := by
  sorry

/-- 6C.15 The subspace {lit}`U = span((1,1,0,0), (1,1,1,2))` of {lit}`ℝ⁴`. -/
noncomputable def U6C15 : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) :=
  Submodule.span ℝ {!₂[1, 1, 0, 0], !₂[1, 1, 1, 2]}

/-- 6C.15 answer: the {lit}`u ∈ U` minimizing {lit}`‖u − (1,2,3,4)‖` — a concrete
vector to be supplied (it is {lit}`P_U (1,2,3,4)`, by 6.61). -/
noncomputable def min6C15 : EuclideanSpace ℝ (Fin 4) := sorry

/-- 6C.15 In {lit}`ℝ⁴`, with {lit}`U = span((1,1,0,0), (1,1,1,2))`, find
{lit}`u ∈ U` minimizing {lit}`‖u − (1,2,3,4)‖`. -/
theorem exercise_6C_15 :
    min6C15 ∈ U6C15 ∧
      ∀ u ∈ U6C15, ‖min6C15 - !₂[1, 2, 3, 4]‖ ≤ ‖u - !₂[1, 2, 3, 4]‖ := by
  sorry

/-- 6C.16 (a) On {lit}`C[−1, 1]` with {lit}`⟨f, g⟩ = ∫₋₁¹ fg` (the space
{name}`L2C` {lit}`(−1) 1`), the subspace {lit}`U = {f : f(0) = 0}` has
{lit}`U⟂ = {0}`. -/
theorem exercise_6C_16a (U : Submodule ℝ (L2C (-1) 1))
    (hU : ∀ f, f ∈ U ↔
      (L2C.toCont f) ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ = 0) :
    Uᗮ = ⊥ := by
  sorry

/-- 6C.16 (b) Hence 6.49 and 6.52 fail without the finite-dimensionality
hypothesis: {lit}`V ≠ U ⊕ U⟂` (indeed {lit}`U + U⟂ = U ≠ V`) and
{lit}`(U⟂)⟂ = V ≠ U`. -/
theorem exercise_6C_16b (U : Submodule ℝ (L2C (-1) 1))
    (hU : ∀ f, f ∈ U ↔
      (L2C.toCont f) ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ = 0) :
    ¬ IsCompl U Uᗮ ∧ Uᗮᗮ ≠ U := by
  sorry

/-- 6C.17 answer: the minimizing {lit}`p ∈ 𝒫₃(ℝ)` — a concrete polynomial to be
supplied. -/
noncomputable def p6C17 : Polynomial ℝ := sorry

/-- 6C.17 Find {lit}`p ∈ 𝒫₃(ℝ)` with {lit}`p(0) = 0` and {lit}`p′(0) = 0`
minimizing {lit}`∫₀¹ |2 + 3x − p(x)|²`. -/
theorem exercise_6C_17 :
    p6C17.degree ≤ 3 ∧ p6C17.eval 0 = 0 ∧
      (Polynomial.derivative p6C17).eval 0 = 0 ∧
      ∀ q : Polynomial ℝ, q.degree ≤ 3 → q.eval 0 = 0 →
        (Polynomial.derivative q).eval 0 = 0 →
        (∫ x in (0 : ℝ)..1, |2 + 3 * x - p6C17.eval x| ^ 2) ≤
          (∫ x in (0 : ℝ)..1, |2 + 3 * x - q.eval x| ^ 2) := by
  sorry

/-- 6C.18 answer: the minimizing {lit}`p ∈ 𝒫₅(ℝ)`. -/
noncomputable def p6C18 : Polynomial ℝ := sorry

/-- 6C.18 Find {lit}`p ∈ 𝒫₅(ℝ)` minimizing {lit}`∫₋ₚᵢᵖⁱ |sin x − p(x)|²`. -/
theorem exercise_6C_18 :
    p6C18.degree ≤ 5 ∧
      ∀ q : Polynomial ℝ, q.degree ≤ 5 →
        (∫ x in (-Real.pi)..Real.pi, |Real.sin x - p6C18.eval x| ^ 2) ≤
          (∫ x in (-Real.pi)..Real.pi, |Real.sin x - q.eval x| ^ 2) := by
  sorry

/-- 6C.19 If {lit}`V` is finite-dimensional and {lit}`P` is the orthogonal
projection onto a subspace {lit}`U`, then {lit}`P† = P`. -/
theorem exercise_6C_19 [FiniteDimensional 𝕜 V] (U : Submodule 𝕜 V) :
    (U.starProjection : V →ₗ[𝕜] V)† = (U.starProjection : V →ₗ[𝕜] V) := by
  sorry

/-- 6C.20 If {lit}`V` is finite-dimensional and {lit}`T ∈ ℒ(V, W)`, then
{lit}`null T† = (range T)⟂` and {lit}`range T† = (null T)⟂`. -/
theorem exercise_6C_20 [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    LinearMap.ker T† = (LinearMap.range T)ᗮ ∧
      LinearMap.range T† = (LinearMap.ker T)ᗮ := by
  sorry

/-- 6C.21 {lit}`T ∈ ℒ(𝔽³, 𝔽²)`, {lit}`T(a, b, c) = (a + b + c, 2b + 3c)`. -/
def T6C21 : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) where
  toFun v := !₂[v 0 + v 1 + v 2, 2 * v 1 + 3 * v 2]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

/-- 6C.21 (a) answer: a formula for {lit}`T†(x, y)` — a concrete vector of
{lit}`𝔽³`, to be supplied. -/
noncomputable def pinv6C21 (v : EuclideanSpace 𝕜 (Fin 2)) : EuclideanSpace 𝕜 (Fin 3) :=
  sorry

/-- 6C.21 (a) For {lit}`(x, y) ∈ 𝔽²`, find a formula for {lit}`T†(x, y)`. -/
theorem exercise_6C_21a (v : EuclideanSpace 𝕜 (Fin 2)) :
    (T6C21 (𝕜 := 𝕜))† v = pinv6C21 v := by
  sorry

/-- 6C.21 (b) Verify {lit}`T T† = P_(range T)` (6.69(b)) for that formula. -/
theorem exercise_6C_21b :
    T6C21 ∘ₗ (T6C21 (𝕜 := 𝕜))† =
      ((LinearMap.range (T6C21 (𝕜 := 𝕜))).starProjection :
        EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] _) := by
  sorry

/-- 6C.21 (c) Verify {lit}`T† T = P_(null T)⟂` (6.69(c)) for that formula. -/
theorem exercise_6C_21c :
    (T6C21 (𝕜 := 𝕜))† ∘ₗ T6C21 =
      ((Submodule.orthogonal (LinearMap.ker (T6C21 (𝕜 := 𝕜)))).starProjection :
        EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] _) := by
  sorry

/-- 6C.22 If {lit}`V` is finite-dimensional and {lit}`T ∈ ℒ(V, W)`, then
{lit}`T T† T = T` and {lit}`T† T T† = T†`. -/
theorem exercise_6C_22 [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    T ∘ₗ T† ∘ₗ T = T ∧ T† ∘ₗ T ∘ₗ T† = T† := by
  sorry

/-- 6C.23 If {lit}`V` and {lit}`W` are finite-dimensional and {lit}`T ∈ ℒ(V, W)`,
then {lit}`(T†)† = T`. -/
theorem exercise_6C_23 [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    T†† = T := by
  sorry

end LADR.Section_6C
