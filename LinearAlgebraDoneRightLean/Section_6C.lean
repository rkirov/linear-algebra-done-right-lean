module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linter.Style
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import LinearAlgebraDoneRightLean.L2Interval
public import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 6C: Orthogonal Complements and Minimization Problems
-/

@[expose] public section

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
  simp only [Set.mem_singleton_iff, forall_eq, plane235, Set.mem_ofPred_eq]
  rw [show ⟪(!₂[2, 3, 5] : EuclideanSpace ℝ (Fin 3)), v⟫_ℝ = 2 * v 0 + 3 * v 1 + 5 * v 2 by
    simp [PiLp.inner_apply, Fin.sum_univ_three]; ring]

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
    rw [← setOrthogonal_singleton_235]
    ext v
    simp [Submodule.mem_orthogonal_singleton_iff_inner_right]
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

@[avoiding Submodule.bot_orthogonal_eq_top]
theorem bot_orthogonal : (⊥ : Submodule 𝕜 V)ᗮ = ⊤ := by
  rw [← setOrthogonal_coe, Submodule.bot_coe, setOrthogonal_zero]

/-- (c) {lit}`V⟂ = {0}`. -/
theorem setOrthogonal_univ : setOrthogonal (Set.univ : Set V) = (⊥ : Submodule 𝕜 V) := by
  rw [Submodule.eq_bot_iff]
  exact fun v hv => inner_self_eq_zero.mp (hv v (Set.mem_univ v))

@[avoiding Submodule.top_orthogonal_eq_bot]
theorem top_orthogonal : (⊤ : Submodule 𝕜 V)ᗮ = ⊥ := by
  rw [← setOrthogonal_coe, Submodule.top_coe, setOrthogonal_univ]

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

@[avoiding Submodule.orthogonal_le]
theorem orthogonal_le {G H : Submodule 𝕜 V} (h : G ≤ H) : Hᗮ ≤ Gᗮ :=
  setOrthogonal_le (𝕜 := 𝕜) (G := (G : Set V)) (H := (H : Set V)) h

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
    rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le,
      Submodule.isOrtho_comm, Submodule.isOrtho_span]
    rintro _ ⟨j, rfl⟩ _ rfl
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

If {lit}`V` is finite-dimensional, then {lit}`dim U⟂ = dim V − dim U`. As in the
book, this follows from {lit}`V = U ⊕ U⟂` (6.49): the dimension of a direct sum
is the sum of the dimensions. -/

@[avoiding Submodule.finrank_add_finrank_orthogonal]
theorem finrank_orthogonal [FiniteDimensional 𝕜 V] (U : Submodule 𝕜 V) :
    finrank 𝕜 Uᗮ = finrank 𝕜 V - finrank 𝕜 U := by
  have := Submodule.finrank_add_eq_of_isCompl (isCompl_orthogonal U)
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

/-! 6.54 {lit}`U⟂ = {0} ⟺ U = V` (for a finite-dimensional subspace).

If {lit}`U⟂ = {0}`, then {lit}`U = (U⟂)⟂ = {0}⟂ = V` by 6.52 and 6.48(b).
Conversely, if {lit}`U = V` then {lit}`U⟂ = V⟂ = {0}` by 6.48(c). -/

@[avoiding Submodule.orthogonal_eq_bot_iff]
theorem orthogonal_eq_bot_iff (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    Uᗮ = ⊥ ↔ U = ⊤ := by
  constructor
  · intro h
    rw [← orthogonal_orthogonal U, h, bot_orthogonal]
  · intro h
    rw [h, top_orthogonal]

/-! # Orthogonal projection -/

/-! 6.55 Definition: orthogonal projection, {lit}`P_U`

For a finite-dimensional subspace {lit}`U`, the orthogonal projection of
{lit}`V` onto {lit}`U` sends {lit}`v = u + w` (with {lit}`u ∈ U`, {lit}`w ∈ U⟂`)
to {lit}`u`. mathlib's {name}`Submodule.starProjection` {lit}`U : V →L[𝕜] V` is
this operator {lit}`P_U`.

Where Axler assumes {lit}`U` is finite-dimensional, the statements below assume
{lit}`[U.HasOrthogonalProjection]` instead. That class says exactly that every
{lit}`v` splits as {lit}`u + w` with {lit}`u ∈ U` and {lit}`w ∈ U⟂`, which is
what {lit}`P_U` needs in order to exist. It is not automatic: in an
infinite-dimensional {lit}`V` a subspace can have {lit}`U ⊕ U⟂ ≠ V` (Exercise
6C.16). It is strictly more general than the book's hypothesis: instance search
derives it from {lit}`[FiniteDimensional 𝕜 U]` (this is 6.49), so every result
here applies verbatim to Axler's finite-dimensional {lit}`U`, and it also covers
complete subspaces such as closed subspaces of a Hilbert space. -/

/-- {lit}`P_U v ∈ U` for every {lit}`v`. -/
example (U : Submodule 𝕜 V) [U.HasOrthogonalProjection] (v : V) :
    U.starProjection v ∈ U :=
  U.starProjection_apply_mem v

/-- …and {lit}`v − P_U v ∈ U⟂`. These two facts are the definition: they say
{lit}`v = P_U v + (v − P_U v)` is the decomposition of 6.49. -/
example (U : Submodule 𝕜 V) [U.HasOrthogonalProjection] (v : V) :
    v - U.starProjection v ∈ Uᗮ :=
  U.sub_starProjection_mem_orthogonal v

/-- The decomposition {lit}`v = u + w` with {lit}`u ∈ U`, {lit}`w ∈ U⟂` is unique,
so whenever {lit}`u ∈ U` and {lit}`v − u ∈ U⟂` we have {lit}`P_U v = u`: the
difference {lit}`P_U v − u = (v − u) − (v − P_U v)` lies in
{lit}`U ∩ U⟂ = {0}` (6.48(d)). -/
@[avoiding Submodule.eq_starProjection_of_mem_orthogonal]
theorem starProjection_eq_of_mem (U : Submodule 𝕜 V) [U.HasOrthogonalProjection]
    {v u : V} (hu : u ∈ U) (hvu : v - u ∈ Uᗮ) : U.starProjection v = u := by
  have h1 : U.starProjection v - u ∈ U := U.sub_mem (U.starProjection_apply_mem v) hu
  have h2 : U.starProjection v - u ∈ Uᗮ := by
    have heq : U.starProjection v - u = (v - u) - (v - U.starProjection v) := by abel
    rw [heq]
    exact Uᗮ.sub_mem hvu (U.sub_starProjection_mem_orthogonal v)
  have hbot := inf_orthogonal_eq_bot U
  rw [Submodule.eq_bot_iff] at hbot
  exact sub_eq_zero.mp (hbot _ ⟨h1, h2⟩)

/-! 6.56 Example: orthogonal projection onto a one-dimensional subspace.
For {lit}`u ≠ 0` and {lit}`U = span(u)`, {lit}`P_U v = (⟨v, u⟩ / ‖u‖²) u`
(reading Axler's {lit}`⟨v, u⟩` as mathlib's {lit}`⟪u, v⟫`). As in the book,
this is the decomposition {lit}`v = (⟨v, u⟩/‖u‖²) u + (v − (⟨v, u⟩/‖u‖²) u)` of
6.13: the first term lies in {lit}`span(u)` and the second is orthogonal to
{lit}`u`, hence to {lit}`span(u)`. (For {lit}`u = 0` both sides are {lit}`0`.) -/

@[avoiding Submodule.starProjection_singleton]
example (u v : V) :
    (𝕜 ∙ u).starProjection v = (⟪u, v⟫_𝕜 / ((‖u‖ ^ 2 : ℝ) : 𝕜)) • u := by
  refine starProjection_eq_of_mem _
    (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)) ?_
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right]
  rcases eq_or_ne u 0 with hu | hu
  · rw [hu, inner_zero_left, inner_zero_left, mul_zero, sub_zero]
  · rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      div_mul_cancel₀ _ (by simpa using hu), sub_self]

/-! 6.57 Properties of orthogonal projection {lit}`P_U`

Suppose {lit}`U` is a finite-dimensional subspace of {lit}`V`. -/

variable (U : Submodule 𝕜 V) [U.HasOrthogonalProjection]

/-- (a) {lit}`P_U ∈ ℒ(V)`: the orthogonal projection is a linear map on
{lit}`V` — in mathlib it is by construction a (continuous) linear map. -/
noncomputable example : V →L[𝕜] V := U.starProjection

/-- (b) {lit}`P_U u = u` for {lit}`u ∈ U` — write {lit}`u = u + 0` with
{lit}`0 ∈ U⟂`; and more precisely {lit}`P_U v = v ↔ v ∈ U`, since
{lit}`P_U v ∈ U`. -/
@[avoiding Submodule.starProjection_eq_self_iff]
theorem starProjection_eq_self_iff (v : V) : U.starProjection v = v ↔ v ∈ U := by
  constructor
  · intro h
    rw [← h]
    exact U.starProjection_apply_mem v
  · intro hv
    exact starProjection_eq_of_mem U hv (by rw [sub_self]; exact Uᗮ.zero_mem)

/-- (f) {lit}`v − P_U v ∈ U⟂` for every {lit}`v` — this is the definition of
{lit}`P_U`. -/
theorem sub_starProjection_mem_orthogonal (v : V) :
    v - U.starProjection v ∈ Uᗮ :=
  U.sub_starProjection_mem_orthogonal v

/-- (g) {lit}`P_U² = P_U`: {lit}`P_U v ∈ U`, so {lit}`P_U (P_U v) = P_U v` by (b). -/
@[avoiding Submodule.isIdempotentElem_starProjection]
theorem starProjection_idem : U.starProjection ∘L U.starProjection = U.starProjection := by
  ext v
  exact (starProjection_eq_self_iff U _).mpr (U.starProjection_apply_mem v)

/-- (h) {lit}`‖P_U v‖ ≤ ‖v‖` for every {lit}`v`: by the Pythagorean theorem
{lit}`‖v‖² = ‖P_U v‖² + ‖v − P_U v‖² ≥ ‖P_U v‖²`, the two terms being
orthogonal by (f). -/
@[avoiding Submodule.norm_starProjection_apply_le]
theorem norm_starProjection_le (v : V) : ‖U.starProjection v‖ ≤ ‖v‖ := by
  have horth : ⟪U.starProjection v, v - U.starProjection v⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal U _).mp (U.sub_starProjection_mem_orthogonal v) _
      (U.starProjection_apply_mem v)
  have hpyth : ‖v‖ * ‖v‖ = ‖U.starProjection v‖ * ‖U.starProjection v‖ +
      ‖v - U.starProjection v‖ * ‖v - U.starProjection v‖ := by
    conv_lhs => rw [show v = U.starProjection v + (v - U.starProjection v) by abel]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  nlinarith [norm_nonneg v, norm_nonneg (U.starProjection v),
    mul_self_nonneg ‖v - U.starProjection v‖]

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
  starProjection_eq_of_mem U (sum_inner_smul_mem U b v)
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
noncomputable def monoL2 (k : ℕ) : L2C (-Real.pi) Real.pi :=
  (⟨fun x => x ^ k, by fun_prop⟩ : C(ℝ, ℝ)).restrict _

/-- The degree-{lit}`≤ 5` polynomial subspace {lit}`𝒫₅` of `C[-π,π]`. -/
noncomputable def polyDegLE5 : Submodule ℝ (L2C (-Real.pi) Real.pi) :=
  Submodule.span ℝ (Set.range (fun k : Fin 6 => monoL2 k))

instance : FiniteDimensional ℝ polyDegLE5 :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- {lit}`sin` as an element of `C[-π,π]`. -/
noncomputable def sinL2 : L2C (-Real.pi) Real.pi :=
  (⟨Real.sin, Real.continuous_sin⟩ : C(ℝ, ℝ)).restrict _

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
  rw [inf_orthogonal_eq_bot] at this
  ext; simpa using this

theorem restr_surjective (T : V →ₗ[𝕜] W) : Function.Surjective (restr T) := by
  rintro ⟨w, v, rfl⟩
  have hsup : (LinearMap.ker T) ⊔ (Submodule.orthogonal (LinearMap.ker T)) = ⊤ :=
    (isCompl_orthogonal (LinearMap.ker T)).sup_eq_top
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
    ((LinearMap.range T).orthogonalProjectionOnto : W →L[𝕜] (LinearMap.range T))

@[inherit_doc] scoped postfix:max "†" => pinv

/-- 6.69 (a) If {lit}`T` is invertible then {lit}`T† = T⁻¹`. Axler's proof reads
this straight off the definition: {lit}`null T = {0}` gives
{lit}`(null T)⟂ = V`, so {lit}`T|_(null T)⟂ = T`, and {lit}`range T = W` makes
{lit}`P_(range T)` the identity on {lit}`W`. -/
theorem pinv_eq_symm (e : V ≃ₗ[𝕜] W) : (e : V →ₗ[𝕜] W)† = (e.symm : W →ₗ[𝕜] V) := by
  ext w
  -- `(null T)⟂ = V`, so `e.symm w` lies in it
  have hmem : e.symm w ∈ Submodule.orthogonal (LinearMap.ker (e : V →ₗ[𝕜] W)) := by
    rw [LinearMap.ker_eq_bot.mpr e.injective, bot_orthogonal]
    exact Submodule.mem_top
  -- `range T = W`, so `P_(range T)` fixes `w`
  have hw : w ∈ LinearMap.range (e : V →ₗ[𝕜] W) := ⟨e.symm w, by simp⟩
  have hproj : (LinearMap.range (e : V →ₗ[𝕜] W)).orthogonalProjectionOnto w =
      (⟨w, hw⟩ : LinearMap.range (e : V →ₗ[𝕜] W)) :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨w, hw⟩ : LinearMap.range (e : V →ₗ[𝕜] W))
  -- and `T|_(null T)⟂` sends `e.symm w` to `w`, so its inverse sends `w` back
  have hrestr : restrEquiv (e : V →ₗ[𝕜] W) ⟨e.symm w, hmem⟩ = ⟨w, hw⟩ := by
    apply Subtype.ext
    simp
  show ((restrEquiv (e : V →ₗ[𝕜] W)).symm
    ((LinearMap.range (e : V →ₗ[𝕜] W)).orthogonalProjectionOnto w) : V) = e.symm w
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
  set x := (Submodule.orthogonal (LinearMap.ker T)).orthogonalProjectionOnto v with hx
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
  have hproj : (LinearMap.range T).orthogonalProjectionOnto (T v) = restr T x := by
    apply Subtype.ext
    rw [restr_coe, hTx]
    exact congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨T v, ⟨v, rfl⟩⟩ : LinearMap.range T))
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
    show ((restrEquiv T).symm ((LinearMap.range T).orthogonalProjectionOnto w) : V) ∈ _
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
    T† w = ((restrEquiv T).symm ((LinearMap.range T).orthogonalProjectionOnto w) : V) := rfl

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
  -- => by linearlity, w in span = ∑ cᵢ vᵢ, so ⟪w, z⟫ = ∑ cᵢ ⟪vᵢ, z⟫ = 0 if all ⟪vᵢ, z⟫ = 0
  -- <= trivial vᵢ beblong to the span
  ext z
  rw [mem_setOrthogonal, Submodule.mem_orthogonal]
  constructor
  · intro hz w hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hw
    rw [sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left, hz _ ⟨i, rfl⟩, mul_zero]
  · intro hz u hu
    exact hz u (Submodule.subset_span hu)

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
  -- ei clearly span U, because they are LI of ui, orthogonal (thus LI) and of the right dimension
  -- fi are ⟪fi, ej⟫ = 0 for all i, j, by construction, so they lie in Uᗮ and dimension matches
  -- since they are also LI they have to span Uᗮ.
  intro e
  -- `b` is linearly independent, so the `eᵢ` are the normalized Gram–Schmidt vectors
  have hne : ∀ i, InnerProductSpace.gramSchmidtNormed 𝕜 b i ≠ 0 := fun i h0 => by
    have h1 := InnerProductSpace.gramSchmidtNormed_unit_length (𝕜 := 𝕜) i b.linearIndependent
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have he : ∀ i, (e i : V) = InnerProductSpace.gramSchmidtNormed 𝕜 b i := fun i =>
    InnerProductSpace.gramSchmidtOrthonormalBasis_apply h (hne i)
  -- each `eᵢ` (`i ≤ m`) is a linear combination of `u₁, …, uᵢ`, so lies in `U`
  have hmemU : ∀ i : Fin m, (e (Fin.castAdd n i) : V) ∈ U := by
    intro i
    rw [he, hU, InnerProductSpace.gramSchmidtNormed]
    refine Submodule.smul_mem _ _ (Submodule.span_mono ?_
      (InnerProductSpace.gramSchmidt_mem_span 𝕜 (b : Fin (m + n) → V)
        (le_refl (Fin.castAdd n i))))
    rintro _ ⟨j, hj, rfl⟩
    have hjm : (j : ℕ) < m := lt_of_le_of_lt (Fin.le_def.mp hj) i.2
    exact ⟨⟨j, hjm⟩, rfl⟩
  -- the `eᵢ` and the `fⱼ` are orthonormal, hence linearly independent
  have hLIe : LinearIndependent 𝕜 fun i : Fin m => (e (Fin.castAdd n i) : V) :=
    e.orthonormal.linearIndependent.comp _ (Fin.castAdd_injective m n)
  have hLIf : LinearIndependent 𝕜 fun j : Fin n => (e (Fin.natAdd m j) : V) :=
    e.orthonormal.linearIndependent.comp _ (Fin.natAdd_injective n m)
  have hfinU : finrank 𝕜 U = m := by
    have hLIu : LinearIndependent 𝕜 fun i : Fin m => b (Fin.castAdd n i) :=
      b.linearIndependent.comp _ (Fin.castAdd_injective m n)
    rw [hU, finrank_span_eq_card hLIu, Fintype.card_fin]
  -- so the `eᵢ` span a subspace of `U` of the right dimension
  have hE : Submodule.span 𝕜 (Set.range fun i : Fin m => (e (Fin.castAdd n i) : V)) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmemU i
    · rw [hfinU, finrank_span_eq_card hLIe, Fintype.card_fin]
  refine ⟨hE, ?_⟩
  -- each `fⱼ` is orthogonal to every `eᵢ`, hence (6C.1) to `U`; the dimensions match
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, ← hE, ← exercise_6C_1, mem_setOrthogonal]
    rintro _ ⟨i, rfl⟩
    refine e.orthonormal.2 fun hij => ?_
    have := congrArg Fin.val hij
    simp at this
    omega
  · have h1 := U.finrank_add_finrank_orthogonal
    rw [finrank_span_eq_card hLIf, Fintype.card_fin]
    rw [Fintype.card_fin] at h
    omega

/-- 6C.3 The subspace {lit}`U = span((1,2,3,−4), (−5,4,3,2))` of {lit}`ℝ⁴`. -/
noncomputable def U6C3 : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) :=
  Submodule.span ℝ {!₂[1, 2, 3, -4], !₂[-5, 4, 3, 2]}

/-- 6C.3 answer: an orthonormal basis of {lit}`U` — two concrete vectors to be
supplied. -/
noncomputable def onb6C3 : Fin 2 → EuclideanSpace ℝ (Fin 4) :=
  -- 1/√30 [1, 2, 3, -4]
  -- <-5,4,3,2> - 2/15 [1, 2, 3, -4] (and then normalize)
  -- that difference is (1/15)·(−77, 56, 39, 38), of norm √12030 / 15
  ![(Real.sqrt 30)⁻¹ • !₂[1, 2, 3, -4], (Real.sqrt 12030)⁻¹ • !₂[-77, 56, 39, 38]]

/-- 6C.3 answer: an orthonormal basis of {lit}`U⟂`. -/
noncomputable def onb6C3perp : Fin 2 → EuclideanSpace ℝ (Fin 4) :=
  -- solving x,y,z,w such that it is orthogonal to both vectors in U
  -- x = (- 3 + 18/7) z + (4 - 18/7) w
  -- y = - 9/7 z + 9/7 w
  -- now apply gram-schmidt to get an orthonormal basis
  -- z = w = 1 gives (1, 0, 1, 1); z = 7, w = 0 gives (−3, −9, 7, 0), and
  -- (−3, −9, 7, 0) − (4/3)·(1, 0, 1, 1) = (1/3)·(−13, −27, 17, −4)
  ![(Real.sqrt 3)⁻¹ • !₂[1, 0, 1, 1], (Real.sqrt 1203)⁻¹ • !₂[-13, -27, 17, -4]]

/-- 6C.3 In {lit}`ℝ⁴`, with {lit}`U = span((1,2,3,−4), (−5,4,3,2))`, find an
orthonormal basis of {lit}`U` and an orthonormal basis of {lit}`U⟂`. -/
theorem exercise_6C_3 :
    (Orthonormal ℝ onb6C3 ∧ Submodule.span ℝ (Set.range onb6C3) = U6C3) ∧
      (Orthonormal ℝ onb6C3perp ∧ Submodule.span ℝ (Set.range onb6C3perp) = U6C3ᗮ) := by
  have h30 : Real.sqrt 30 * Real.sqrt 30 = 30 := Real.mul_self_sqrt (by norm_num)
  have h12030 : Real.sqrt 12030 * Real.sqrt 12030 = 12030 := Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h1203 : Real.sqrt 1203 * Real.sqrt 1203 = 1203 := Real.mul_self_sqrt (by norm_num)
  have h30' : Real.sqrt 30 ≠ 0 := by positivity
  have h12030' : Real.sqrt 12030 ≠ 0 := by positivity
  have h3' : Real.sqrt 3 ≠ 0 := by positivity
  have h1203' : Real.sqrt 1203 ≠ 0 := by positivity
  -- the inner product on `ℝ⁴` in coordinates
  have hin : ∀ x y : EuclideanSpace ℝ (Fin 4),
      ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 := by
    intro x y
    rw [PiLp.inner_apply, Fin.sum_univ_four]
    simp [mul_comm]
  -- both lists are orthonormal: compute the four inner products of each
  have hA : Orthonormal ℝ onb6C3 := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> rw [hin] <;> simp [onb6C3] <;> field_simp <;>
      first | done | nlinarith [h30, h12030]
  have hB : Orthonormal ℝ onb6C3perp := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> rw [hin] <;> simp [onb6C3perp] <;> field_simp <;>
      first | done | nlinarith [h3, h1203]
  -- the first list spans `U`: with `u₁ = (1,2,3,−4)`, `u₂ = (−5,4,3,2)` we have
  -- `(−77,56,39,38) = −2u₁ + 15u₂`, and conversely `u₂ = (2u₁ + (−77,56,39,38))/15`
  have hspanA : Submodule.span ℝ (Set.range onb6C3) = U6C3 := by
    rw [onb6C3, Matrix.range_cons_cons_empty, U6C3]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact Submodule.mem_span_pair.mpr ⟨(Real.sqrt 30)⁻¹, 0, by simp⟩
      · refine Submodule.mem_span_pair.mpr
          ⟨-2 * (Real.sqrt 12030)⁻¹, 15 * (Real.sqrt 12030)⁻¹, ?_⟩
        ext i
        fin_cases i <;> simp <;> ring
    · rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · refine Submodule.mem_span_pair.mpr ⟨Real.sqrt 30, 0, ?_⟩
        ext i
        fin_cases i <;> simp [h30']
      · refine Submodule.mem_span_pair.mpr
          ⟨2 / 15 * Real.sqrt 30, 1 / 15 * Real.sqrt 12030, ?_⟩
        ext i
        fin_cases i <;> simp <;> field_simp <;> ring
  refine ⟨⟨hA, hspanA⟩, hB, ?_⟩
  -- `dim U = 2` since it has an orthonormal (hence independent) spanning list of length 2
  have hfinU : finrank ℝ U6C3 = 2 := by
    rw [← hspanA, finrank_span_eq_card hA.linearIndependent, Fintype.card_fin]
  -- the second list lies in `U⟂` (each vector is orthogonal to `u₁` and `u₂`), and
  -- `dim U⟂ = 4 − 2 = 2` is the dimension of its span
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [← Submodule.isOrtho_iff_le, onb6C3perp, Matrix.range_cons_cons_empty, U6C3,
      Submodule.isOrtho_span]
    rintro _ (rfl | rfl) _ (rfl | rfl) <;> rw [hin] <;> simp <;> ring
  · have h1 := U6C3.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin] at h1
    rw [finrank_span_eq_card hB.linearIndependent, Fintype.card_fin]
    omega

/-- 6C.4 Converse to 6.30(b): if {lit}`‖eₖ‖ = 1` for each {lit}`k` and Parseval's
equality {lit}`‖v‖² = ∑ |⟨v, eₖ⟩|²` holds for all {lit}`v`, then {lit}`e₁, …, eₙ`
is an orthonormal basis. -/
theorem exercise_6C_4 [FiniteDimensional 𝕜 V] {n : ℕ} (e : Fin n → V)
    (hnorm : ∀ k, ‖e k‖ = 1)
    (hpar : ∀ v : V, ‖v‖ ^ 2 = ∑ k, ‖⟪e k, v⟫_𝕜‖ ^ 2) :
    Orthonormal 𝕜 e ∧ Submodule.span 𝕜 (Set.range e) = ⊤ := by
  -- take v = ei, then 1 = ‖ei‖^2 = ‖ei‖^2 + ∑ j≠i |⟪ei, ej⟩|^2,
  -- since all values in the sum are positive they all have to be 0
  -- so ei is orthonormal.
  -- If they don't span the whole V, there exists a nonzero vector in span{ei}ᗮ
  -- but by hpar, it will have norm 0, contradiction.
  have horth : ∀ j k, k ≠ j → ⟪e k, e j⟫_𝕜 = 0 := by
    intro j k hkj
    -- Parseval for `v = eⱼ`, with the `k = j` term split off
    have h := hpar (e j)
    have h1 : ‖⟪e j, e j⟫_𝕜‖ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hnorm]; simp
    rw [hnorm, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1] at h
    have hs : ∑ k ∈ Finset.univ.erase j, ‖⟪e k, e j⟫_𝕜‖ ^ 2 = 0 := by linarith
    -- a sum of nonnegative terms is zero only if every term is
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hs k
      (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)
    simpa using h2
  refine ⟨⟨hnorm, fun k j hkj => horth j k hkj⟩, ?_⟩
  -- by 6.54 it is enough that `(span e)⟂ = {0}`; a `v` there has `‖v‖² = 0` by `hpar`
  rw [← orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
  intro v hv
  have h := hpar v
  have hz : ∑ k, ‖⟪e k, v⟫_𝕜‖ ^ 2 = 0 := Finset.sum_eq_zero fun k _ => by
    rw [hv (e k) (Submodule.subset_span ⟨k, rfl⟩), norm_zero, zero_pow two_ne_zero]
  rw [hz] at h
  simpa using h

/-- 6C.5 {lit}`P_(U⟂) = I − P_U`. -/
theorem exercise_6C_5 (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] :
    Uᗮ.starProjection = 1 - U.starProjection := by
  -- we proved that every v = u + w, where v ∈ V and w ∈ Uᗮ uniquely
  -- thus P_U v = u, P_(Uᗮ) v = w, so I v = P_U v + P_(Uᗮ) v for all v,
  -- giving the desired equality P_(Uᗮ) = I - P_U.
  ext v
  rw [sub_apply, one_apply_eq_self]
  -- `v = (v − P_U v) + P_U v` with `v − P_U v ∈ U⟂` and `P_U v ∈ U ⊆ (U⟂)⟂`;
  -- by uniqueness of the decomposition, `P_(U⟂) v = v − P_U v`
  refine starProjection_eq_of_mem Uᗮ (U.sub_starProjection_mem_orthogonal v) ?_
  rw [sub_sub_cancel]
  exact U.le_orthogonal_orthogonal (U.starProjection_apply_mem v)

/-- 6C.6 If {lit}`V` is finite-dimensional and {lit}`T ∈ ℒ(V, W)`, then
{lit}`T = T P_(null T)⟂ = P_(range T) T`. -/
theorem exercise_6C_6 [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    T = T ∘ₗ ((Submodule.orthogonal (LinearMap.ker T)).starProjection : V →ₗ[𝕜] V) ∧
      T = ((LinearMap.range T).starProjection : W →ₗ[𝕜] W) ∘ₗ T := by
  -- for the first eq, use 5, to write T = T ∘ₗ (P_(null T)ᗮ) = T ∘ₗ (I - P_(null T))
  -- clearly, T following projection to null T gives 0, so T = T ∘ₗ (I - P_(null T)) = T
  -- for the second eq, T already maps into its range, so projection is an id on it.
  constructor
  · ext v
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, exercise_6C_5,
      sub_apply, one_apply_eq_self, map_sub,
      LinearMap.mem_ker.mp ((LinearMap.ker T).starProjection_apply_mem v), sub_zero]
  · ext v
    rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    exact ((starProjection_eq_self_iff _ _).mpr (LinearMap.mem_range_self T v)).symm

/-- 6C.7 For finite-dimensional subspaces {lit}`X, Y`, {lit}`P_X P_Y = 0` iff
{lit}`⟨x, y⟩ = 0` for all {lit}`x ∈ X`, {lit}`y ∈ Y`. -/
theorem exercise_6C_7 (X Y : Submodule 𝕜 V) [FiniteDimensional 𝕜 X]
    [FiniteDimensional 𝕜 Y] :
    X.starProjection ∘L Y.starProjection = 0 ↔
      ∀ x ∈ X, ∀ y ∈ Y, ⟪x, y⟫_𝕜 = 0 := by
  -- => take y in Y, then P_Y y = y, since P_X P_Y = 0, we get P_X y = 0, so ⟪x, y⟫ = 0 for all x ∈ X.
  -- <= equivalent to Y ⊆ Xᗮ, so P_Y v is in Y, and also in Xᗮ, hence P_X P_Y v = 0 for all v.
  constructor
  · intro h x hx y hy
    have hy' : Y.starProjection y = y := (starProjection_eq_self_iff Y y).mpr hy
    have h0 : X.starProjection y = 0 := by
      have h1 := DFunLike.congr_fun h y
      rwa [ContinuousLinearMap.comp_apply, hy', zero_apply] at h1
    -- `y = y − P_X y ∈ X⟂`
    have hyX : y ∈ Xᗮ := by
      have h2 := X.sub_starProjection_mem_orthogonal y
      rwa [h0, sub_zero] at h2
    exact hyX x hx
  · intro h
    ext v
    rw [ContinuousLinearMap.comp_apply, zero_apply]
    exact starProjection_eq_zero_of_mem_orthogonal
      (fun x hx => h x hx _ (Y.starProjection_apply_mem v))

/-- 6C.8 Let {lit}`φ(u) = ⟨u, v⟩` be the linear functional on a finite-dimensional
subspace {lit}`U`, i.e. {lit}`φ = ⟪v, ·⟫` restricted to {lit}`U`, and let
{lit}`w ∈ U` be *the* vector representing it given by the Riesz representation
theorem applied to {lit}`U` (6.58 here, 6.42 in the book — the bijection
{lit}`w ↦ φ_w` supplies both existence and uniqueness). Then {lit}`w = P_U v`. -/
theorem exercise_6C_8 (U : Submodule 𝕜 V) [FiniteDimensional 𝕜 U] (v : V) :
    ((rieszVector (V := U) ((innerₛₗ 𝕜 v).comp U.subtype) : U) : V) =
      U.starProjection v := by
  -- v = P_U v + P_{Uᗮ} v
  -- then ⟪u, v⟫ = ⟪u, P_U v + P_{Uᗮ} v⟫ = ⟪u, P_U v⟫ for all u ∈ U
  have hv : v = U.starProjection v + Uᗮ.starProjection v := by
    rw [exercise_6C_5, sub_apply, one_apply_eq_self,
      add_sub_cancel]
  -- so `P_U v ∈ U` represents `φ`, and by uniqueness in Riesz it is the Riesz vector
  have hw : rieszVector (V := U) ((innerₛₗ 𝕜 v).comp U.subtype) =
      ⟨U.starProjection v, U.starProjection_apply_mem v⟩ := by
    apply rieszVector_unique
    intro u
    have horth : ⟪Uᗮ.starProjection v, (u : V)⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal' U _).mp (Uᗮ.starProjection_apply_mem v) u u.2
    rw [Submodule.coe_inner]
    show ⟪v, (u : V)⟫_𝕜 = ⟪U.starProjection v, (u : V)⟫_𝕜
    conv_lhs => rw [hv, inner_add_left, horth, add_zero]
  rw [hw]

/-- 6C.9 If {lit}`P² = P` and {lit}`null P ⟂ range P`, then {lit}`P = P_U` for
some subspace {lit}`U`. -/
theorem exercise_6C_9 [FiniteDimensional 𝕜 V] (P : V →ₗ[𝕜] V) (hP : P ∘ₗ P = P)
    (horth : ∀ x ∈ LinearMap.ker P, ∀ y ∈ LinearMap.range P, ⟪x, y⟫_𝕜 = 0) :
    ∃ U : Submodule 𝕜 V, (U.starProjection : V →ₗ[𝕜] V) = P := by
  -- by dim ker P + dim range P = dim V,
  -- and ker P ⟂ range P, so ker P is the orthogonal complement of range P.
  -- and we can take U = range P
  -- only thing left to do in definition of P_U is to show that Pv = v when v in range P
  -- but P v = P P w ( since v ∈ range P, v = P w for some w)
  -- = P w = v, so indeed P acts as the identity on range P.
  set U := LinearMap.range P with hU
  -- `null P ⊆ U⟂` by hypothesis, and the dimensions agree
  have hker : LinearMap.ker P = Uᗮ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · intro x hx
      rw [Submodule.mem_orthogonal']
      intro y hy
      exact horth x hx y hy
    · have h1 : finrank 𝕜 U + finrank 𝕜 (LinearMap.ker P) = finrank 𝕜 V :=
        LinearMap.finrank_range_add_finrank_ker P
      have h2 := U.finrank_add_finrank_orthogonal
      omega
  have hid : ∀ v ∈ U, P v = v := by
    rintro _ ⟨w, rfl⟩
    exact LinearMap.congr_fun hP w
  refine ⟨U, ?_⟩
  ext v
  rw [ContinuousLinearMap.coe_coe]
  -- `v = P_U v + (v − P_U v)` with `P_U v ∈ U` and `v − P_U v ∈ U⟂ = null P`
  have hw : v - U.starProjection v ∈ LinearMap.ker P := by
    rw [hker]
    exact U.sub_starProjection_mem_orthogonal v
  have hsplit : P v = P (U.starProjection v) + P (v - U.starProjection v) := by
    rw [← map_add, add_sub_cancel]
  rw [hsplit, hid _ (U.starProjection_apply_mem v), LinearMap.mem_ker.mp hw, add_zero]

/-- 6C.10 If {lit}`V` is finite-dimensional, {lit}`P² = P`, and {lit}`‖Pv‖ ≤ ‖v‖`
for every {lit}`v`, then {lit}`P = P_U` for some subspace {lit}`U`. -/
theorem exercise_6C_10 [FiniteDimensional 𝕜 V] (P : V →ₗ[𝕜] V)
    (hP : P ∘ₗ P = P) (hnorm : ∀ v, ‖P v‖ ≤ ‖v‖) :
    ∃ U : Submodule 𝕜 V, (U.starProjection : V →ₗ[𝕜] V) = P := by
  -- suffices to show that null P is orthogonal to range P and apply ex9.
  -- assume v ∈ null P, then v = w + z, where w ∈ range P and z ∈ (range P)ᗮ
  -- w ∈ range P, so P w = P P w' = P w' = w
  -- so P v = P w + P z = w + P z = 0
  -- so P z = -w
  -- Consider now a w + z for some a ∈ ℝ
  -- ‖a w + z‖² = ‖a w‖² + ‖z‖² by orthogonality
  -- ‖P(a w + z)‖² = ‖a P w + P z‖² = ‖a w - w‖² = |a - 1|² ‖w‖²
  -- by condition ‖P(a w + z)‖² ≤ ‖a w + z‖² for all a
  -- so |a - 1|² ‖w‖² ≤ |a|² ‖w‖² + ‖z‖² for all a
  -- (|a - 1|² - |a|²) ‖w‖² ≤ ‖z‖² for all a, and fixed ‖w‖ and ‖z‖
  -- taking a < 0, we get (1 - 2a) ‖w‖² ≤ ‖z‖² for all a < 0
  -- but as as go to -∞, the left-hand side goes to +∞, which is impossible unless ‖w‖ = 0
  apply exercise_6C_9 P hP
  intro v hv y hy
  set U := LinearMap.range P with hU
  set w := U.starProjection v with hw
  set z := v - w with hz
  have hwU : w ∈ U := U.starProjection_apply_mem v
  have hzU : z ∈ Uᗮ := U.sub_starProjection_mem_orthogonal v
  have hPw : P w = w := by
    obtain ⟨w', hw'⟩ := hwU
    rw [← hw']
    exact LinearMap.congr_fun hP w'
  have hPz : P z = -w := by
    have h0 : P v = 0 := LinearMap.mem_ker.mp hv
    have h1 : P z = P v - P w := by rw [hz, map_sub]
    rw [h1, h0, hPw, zero_sub]
  have hwz : ⟪w, z⟫_𝕜 = 0 := hzU w hwU
  -- the inequality `‖P(a w + z)‖² ≤ ‖a w + z‖²`, expanded
  have key : ∀ a : ℝ, (1 - 2 * a) * ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    intro a
    have h1 := hnorm ((a : 𝕜) • w + z)
    have h2 : P ((a : 𝕜) • w + z) = ((a : 𝕜) - 1) • w := by
      rw [map_add, map_smul, hPw, hPz, sub_smul, one_smul, sub_eq_add_neg]
    have h3 : ‖((a : 𝕜) - 1) • w‖ = |a - 1| * ‖w‖ := by
      rw [norm_smul, ← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
    have h4 : ‖(a : 𝕜) • w + z‖ ^ 2 = a ^ 2 * ‖w‖ ^ 2 + ‖z‖ ^ 2 := by
      have horth : ⟪(a : 𝕜) • w, z⟫_𝕜 = 0 := by rw [inner_smul_left, hwz, mul_zero]
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      rw [pow_two, h, norm_smul, RCLike.norm_ofReal, ← sq_abs a]
      ring
    rw [h2, h3] at h1
    have h5 : (|a - 1| * ‖w‖) ^ 2 ≤ ‖(a : 𝕜) • w + z‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    rw [h4, mul_pow, sq_abs] at h5
    nlinarith
  -- taking `a = −‖z‖²/‖w‖²` gives `‖w‖² + 2‖z‖² ≤ ‖z‖²`, impossible unless `w = 0`
  have hw0 : w = 0 := by
    by_contra hne
    have hpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
    have h1 := key (-(‖z‖ ^ 2 / ‖w‖ ^ 2))
    have h2 : (1 - 2 * -(‖z‖ ^ 2 / ‖w‖ ^ 2)) * ‖w‖ ^ 2 = ‖w‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg ‖z‖]
  -- so `v = z ∈ (range P)⟂`
  have hvz : v = z := by rw [hz, hw0, sub_zero]
  rw [hvz]
  exact (Submodule.mem_orthogonal' U z).mp hzU y hy

/-- 6C.11 For {lit}`T ∈ ℒ(V)` and a finite-dimensional subspace {lit}`U`,
{lit}`U` is invariant under {lit}`T` iff {lit}`P_U T P_U = T P_U`. -/
theorem exercise_6C_11 (T : V →ₗ[𝕜] V) (U : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 U] :
    (∀ u ∈ U, T u ∈ U) ↔
      (U.starProjection : V →ₗ[𝕜] V) ∘ₗ T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) =
        T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) := by
  -- => if u ∈ U, then P_U u = u, then P_U v ∈ U, and T P_U v ∈ U as well
  -- so P_U T P_U v = T P_U v for all v, which is the desired equality.
  -- <= assume there exists u ∈ U, s.t T u ∉ U
  -- then P_U T P_U u ∈ U trivially after P_U
  -- but T P_U u = T u ∉ U, which contradicts the assumed equality.
  constructor
  · intro h
    ext v
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    exact (starProjection_eq_self_iff U _).mpr (h _ (U.starProjection_apply_mem v))
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, hTu⟩ := hcon
    have hPu : U.starProjection u = u := (starProjection_eq_self_iff U u).mpr hu
    have h1 := LinearMap.congr_fun h u
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hPu] at h1
    -- `h1 : P_U (T u) = T u`, and the left side is in `U`
    exact hTu (h1 ▸ U.starProjection_apply_mem (T u))

/-- 6C.12 For finite-dimensional {lit}`V`, {lit}`T ∈ ℒ(V)`, and a subspace
{lit}`U`: both {lit}`U` and {lit}`U⟂` are invariant under {lit}`T` iff
{lit}`P_U T = T P_U`. -/
theorem exercise_6C_12 [FiniteDimensional 𝕜 V] (T : V →ₗ[𝕜] V)
    (U : Submodule 𝕜 V) :
    ((∀ u ∈ U, T u ∈ U) ∧ ∀ w ∈ Uᗮ, T w ∈ Uᗮ) ↔
      (U.starProjection : V →ₗ[𝕜] V) ∘ₗ T = T ∘ₗ (U.starProjection : V →ₗ[𝕜] V) := by
  -- => using 11, P_U T P_U = T P_U and P_{Uᗮ} T P_{Uᗮ} = T P_{Uᗮ}
  --  P_{Uᗮ} = I - P_U
  -- so P_{Uᗮ} T P_{Uᗮ} = (I - P_U) T (I - P_U) = T - T P_U - P_U T + P_U T P_U
  -- = T - T P_U - P_U T + T P_U  -- using P_U T P_U = T P_U ex 11
  -- = T - P_U T = (1 - P_U) T
  -- by ex11 again also = T (1 - P_U)
  -- so P_U T = T P_U
  -- <= again using ex 11
  --   first show P_U T P_U = P_U P_U T = P_U T = T P_U
  --   then (1 - P_U) T (1 - P_U) = T - T P_U - P_U T + T P_U
  -- = T - P_U T = T - T P_U = T (1 - P_U)
  -- so Uᗮ is also invariant under T
  set P : V →ₗ[𝕜] V := (U.starProjection : V →ₗ[𝕜] V) with hPdef
  -- `P_(U⟂) = I − P_U` (6C.5), as linear maps
  have hQ : (Uᗮ.starProjection : V →ₗ[𝕜] V) = 1 - P := by
    rw [exercise_6C_5]
    rfl
  -- 6C.11 for `U` and for `U⟂`
  have h11 : (∀ u ∈ U, T u ∈ U) ↔ P * (T * P) = T * P := exercise_6C_11 T U
  have h11' : (∀ w ∈ Uᗮ, T w ∈ Uᗮ) ↔ (1 - P) * (T * (1 - P)) = T * (1 - P) := by
    have h := exercise_6C_11 T Uᗮ
    rw [hQ] at h
    exact h
  -- `(I − P) T (I − P) = T (I − P) − (P T − P T P)`
  have e : (1 - P) * (T * (1 - P)) = T * (1 - P) - (P * T - P * (T * P)) := by
    noncomm_ring
  have hPP : P * P = P := by
    ext v
    exact (starProjection_eq_self_iff U _).mpr (U.starProjection_apply_mem v)
  rw [h11, h11']
  change _ ↔ P * T = T * P
  constructor
  · rintro ⟨a, b⟩
    rw [e, a, sub_eq_self, sub_eq_zero] at b
    exact b
  · intro h
    have a : P * (T * P) = T * P := by rw [← mul_assoc, h, mul_assoc, hPP]
    refine ⟨a, ?_⟩
    rw [e, a, h, sub_self, sub_zero]

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
  -- assume φ_v = 0, then ⟨u, v⟩ = 0 for all u, pick u = v, ‖v‖² = ⟪v, v⟫ = 0, so v = 0
  -- so the null space of v ↦ φ_v is {0}, and since the map is linear it is injective
  refine (injective_iff_map_eq_zero phi6C13).mpr fun v hv => ?_
  have h : ⟪v, v⟫_ℝ = 0 := LinearMap.congr_fun hv v
  exact inner_self_eq_zero.mp h

/-- 6C.13 (b) With (a) and a dimension count, {lit}`v ↦ φ_v` is an isomorphism of
{lit}`V` onto {lit}`V′`. (This is an alternative proof of Riesz for
{lit}`𝔽 = ℝ`, so 6.42/6.58 may not be used here.) -/
theorem exercise_6C_13b {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] : Function.Bijective (phi6C13 (V := V)) := by
  -- dim V′ = dim V (3.111), and an injective linear map between finite-dimensional
  -- spaces of the same dimension is surjective (3.65), so with (a) it is bijective
  have hdim : finrank ℝ V = finrank ℝ (Module.Dual ℝ V) := Subspace.dual_finrank_eq.symm
  exact ⟨exercise_6C_13a,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp exercise_6C_13a⟩

/-- 6C.14 If {lit}`e₁, …, eₙ` is an orthonormal basis of {lit}`V`, then its dual
basis is {lit}`e₁, …, eₙ` under the Riesz identification: {lit}`εᵢ(eⱼ) = ⟨eᵢ, eⱼ⟩`. -/
theorem exercise_6C_14 [FiniteDimensional 𝕜 V] {n : ℕ}
    (e : OrthonormalBasis (Fin n) 𝕜 V) (i j : Fin n) :
    e.toBasis.dualBasis i (e j) = ⟪e i, e j⟫_𝕜 := by
  -- by definition φi(ej) = 1 if i = j and 0 otherwise
  -- but 1 if i = j and 0 otherwise, which is exactly ⟪e i, e j⟫_𝕜
  have h1 : e.toBasis.dualBasis i (e j) = if j = i then 1 else 0 := by
    have h := e.toBasis.dualBasis_apply_self i j
    rwa [e.coe_toBasis] at h
  have h2 : ⟪e i, e j⟫_𝕜 = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp e.orthonormal i j
  rw [h1, h2]
  simp only [eq_comm]

/-- 6C.15 The subspace {lit}`U = span((1,1,0,0), (1,1,1,2))` of {lit}`ℝ⁴`. -/
noncomputable def U6C15 : Submodule ℝ (EuclideanSpace ℝ (Fin 4)) :=
  Submodule.span ℝ {!₂[1, 1, 0, 0], !₂[1, 1, 1, 2]}

/-- 6C.15 answer: the {lit}`u ∈ U` minimizing {lit}`‖u − (1,2,3,4)‖` — a concrete
vector to be supplied (it is {lit}`P_U (1,2,3,4)`, by 6.61). -/
noncomputable def min6C15 : EuclideanSpace ℝ (Fin 4) :=
  -- first find orthonormal basis of U
  -- 1/√2(1,1,0,0) and 1/√5(0,0,1,2)
  -- then project 1,2,3,4 onto this orthonormal basis
  -- (1/√2(1,1,0,0) · (1,2,3,4)) * 1/√2(1,1,0,0) + (1/√5(0,0,1,2) · (1,2,3,4)) * 1/√5(0,0,1,2)
  -- (3/2, 3/2, 11/5, 22/5)
  !₂[3/2, 3/2, 11/5, 22/5]

/-- 6C.15 In {lit}`ℝ⁴`, with {lit}`U = span((1,1,0,0), (1,1,1,2))`, find
{lit}`u ∈ U` minimizing {lit}`‖u − (1,2,3,4)‖`. -/
theorem exercise_6C_15 :
    min6C15 ∈ U6C15 ∧
      ∀ u ∈ U6C15, ‖min6C15 - !₂[1, 2, 3, 4]‖ ≤ ‖u - !₂[1, 2, 3, 4]‖ := by
  -- the inner product on `ℝ⁴` in coordinates
  have hin : ∀ x y : EuclideanSpace ℝ (Fin 4),
      ⟪x, y⟫_ℝ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 := by
    intro x y
    rw [PiLp.inner_apply, Fin.sum_univ_four]
    simp [mul_comm]
  -- the answer is in `U`: it is `−(7/10)·(1,1,0,0) + (11/5)·(1,1,1,2)`
  have hmem : min6C15 ∈ U6C15 := by
    refine Submodule.mem_span_pair.mpr ⟨-(7 / 10), 11 / 5, ?_⟩
    ext i
    fin_cases i <;> simp [min6C15] <;> norm_num
  -- and `(1,2,3,4) − answer` is orthogonal to both spanning vectors, so lies in `U⟂`
  have hperp : !₂[1, 2, 3, 4] - min6C15 ∈ U6C15ᗮ := by
    rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le, U6C15,
      Submodule.isOrtho_span]
    rintro _ rfl _ (rfl | rfl) <;> rw [hin] <;> simp [min6C15] <;> norm_num
  -- hence the answer is `P_U (1,2,3,4)`, the closest point of `U` by 6.61
  have hproj : U6C15.starProjection !₂[1, 2, 3, 4] = min6C15 :=
    starProjection_eq_of_mem U6C15 hmem hperp
  refine ⟨hmem, fun u hu => ?_⟩
  have h := minimizing_distance (U := U6C15) !₂[1, 2, 3, 4] u hu
  rw [hproj] at h
  rw [norm_sub_rev min6C15, norm_sub_rev u]
  exact h

/-- 6C.16 (a) On {lit}`C[−1, 1]` with {lit}`⟨f, g⟩ = ∫₋₁¹ fg` (the space
{name}`L2C` {lit}`(−1) 1`), the subspace {lit}`U = {f : f(0) = 0}` has
{lit}`U⟂ = {0}`. -/
theorem exercise_6C_16a (U : Submodule ℝ (L2C (-1) 1))
    (hU : ∀ f, f ∈ U ↔
      (L2C.toCont f) ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ = 0) :
    Uᗮ = ⊥ := by
  -- assume ∫₋₁¹ fg = 0 for all f ∈ U
  -- will show g is zero everywhere away from 0
  -- assume there is c s.t. g(c) ≠ 0, by ct. find a small ball away from 0
  -- with same sign of g around c.
  -- take f a small continuous bump function on that ball with zero outside.
  -- then ∫₋₁¹ fg ≠ 0, a contradiction.
  -- finally, g must be zero at zero by continuity, so g = 0.
  rw [Submodule.eq_bot_iff]
  intro g hg
  -- `g` vanishes away from `0`
  have hne : ∀ c : Set.Icc (-1 : ℝ) 1, (c : ℝ) ≠ 0 → g.toCont c = 0 := by
    intro c hc0
    by_contra hgc
    -- a ball around `c` on which `g` has the sign of `g c`
    have hpos : 0 < g.toCont c * g.toCont c := mul_self_pos.mpr hgc
    have hcont : ContinuousAt (fun x => g.toCont c * g.toCont x) c :=
      (continuous_const.mul g.toCont.continuous).continuousAt
    have hev : ∀ᶠ x in nhds c, 0 < g.toCont c * g.toCont x :=
      Filter.Tendsto.eventually hcont (lt_mem_nhds hpos)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    -- shrink it so that it stays away from `0`
    set r : ℝ := min δ |(c : ℝ)| with hr
    have hr0 : 0 < r := lt_min hδ (abs_pos.mpr hc0)
    -- the bump function `max 0 (r − |x − c|)`, scaled by `g c` to fix the sign
    let f : L2C (-1) 1 :=
      (⟨fun x => max 0 (r - |(x : ℝ) - c|) * g.toCont c, by fun_prop⟩ :
        C(Set.Icc (-1 : ℝ) 1, ℝ))
    have hfx : ∀ x, f.toCont x = max 0 (r - |(x : ℝ) - c|) * g.toCont c := fun x => rfl
    -- it vanishes at `0`, so it is in `U`
    have hfU : f ∈ U := by
      rw [hU, hfx]
      have h1 : r - |(0 : ℝ) - c| ≤ 0 := by
        rw [zero_sub, abs_neg]
        exact sub_nonpos.mpr (min_le_right _ _)
      rw [max_eq_left h1, zero_mul]
    -- `∫ f g = 0` since `g ∈ U⟂`
    have hint : ∫ x, f.toCont x * g.toCont x = 0 := hg f hfU
    -- but the integrand is continuous, nonnegative, and positive at `c`
    have hnonneg : 0 ≤ fun x => f.toCont x * g.toCont x := by
      intro x
      simp only [Pi.zero_apply, hfx]
      by_cases hx : |(x : ℝ) - c| < r
      · have hx' : dist x c < δ := lt_of_lt_of_le hx (min_le_left _ _)
        have h2 := hball hx'
        have h3 : 0 ≤ max 0 (r - |(x : ℝ) - c|) := le_max_left _ _
        nlinarith
      · rw [max_eq_left (by linarith), zero_mul, zero_mul]
    have hc : f.toCont c * g.toCont c ≠ 0 := by
      rw [hfx, sub_self, abs_zero, sub_zero, max_eq_right hr0.le]
      exact mul_ne_zero (mul_ne_zero hr0.ne' hgc) hgc
    have hpos' := MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (f := fun x => f.toCont x * g.toCont x)
      (f.toCont.continuous.mul g.toCont.continuous) (L2C.integrable_toCont_mul f g) hnonneg hc
    rw [hint] at hpos'
    exact lt_irrefl _ hpos'
  -- finally `g 0 = 0`: otherwise `g ≠ 0` near `0`, in particular at some point `≠ 0`
  have hall : ∀ c : Set.Icc (-1 : ℝ) 1, g.toCont c = 0 := by
    intro c
    by_cases hc0 : (c : ℝ) = 0
    · by_contra hgc
      obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
        (g.toCont.continuous.continuousAt.eventually_ne hgc)
      have hpos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) (by norm_num)
      have hmem : min (δ / 2) 1 ∈ Set.Icc (-1 : ℝ) 1 :=
        ⟨by linarith, min_le_right _ _⟩
      refine hball (y := ⟨min (δ / 2) 1, hmem⟩) ?_ (hne _ hpos.ne')
      rw [Subtype.dist_eq, hc0, Real.dist_eq, sub_zero, abs_of_pos hpos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · exact hne c hc0
  exact ContinuousMap.ext hall

/-- 6C.16 (b) Hence 6.49 and 6.52 fail without the finite-dimensionality
hypothesis: {lit}`V ≠ U ⊕ U⟂` (indeed {lit}`U + U⟂ = U ≠ V`) and
{lit}`(U⟂)⟂ = V ≠ U`. -/
theorem exercise_6C_16b (U : Submodule ℝ (L2C (-1) 1))
    (hU : ∀ f, f ∈ U ↔
      (L2C.toCont f) ⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩ = 0) :
    ¬ IsCompl U Uᗮ ∧ Uᗮᗮ ≠ U := by
  -- for first part U + Uᗮ ≠ V, all function in the sum vanish at 0, so cannot cover all of V
  -- for second part Uᗮᗮ = V, not U
  have hperp : Uᗮ = ⊥ := exercise_6C_16a U hU
  -- the constant function `1` does not vanish at `0`, so `U ≠ V`
  have hUtop : U ≠ ⊤ := by
    intro h
    let one : L2C (-1) 1 := (ContinuousMap.const _ 1 : C(Set.Icc (-1 : ℝ) 1, ℝ))
    have h1 : one ∈ U := h ▸ Submodule.mem_top
    have h2 := (hU one).mp h1
    exact one_ne_zero h2
  constructor
  · -- `U + U⟂ = U + {0} = U ≠ V`
    intro h
    have h1 := h.sup_eq_top
    rw [hperp, sup_bot_eq] at h1
    exact hUtop h1
  · -- `(U⟂)⟂ = {0}⟂ = V ≠ U`
    rw [hperp, Submodule.bot_orthogonal_eq_top]
    exact fun h => hUtop h.symm

/-! Bridge for 6C.17: polynomials as elements of the inner product space
{lit}`C[a, b]`, so that 6.61 applies to an integral minimization problem. -/

instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- A real polynomial, restricted to {lit}`[a, b]`, as an element of {lit}`C[a, b]`. -/
noncomputable def polyL2 (a b : ℝ) : Polynomial ℝ →ₗ[ℝ] L2C a b where
  toFun p := (⟨fun x : Set.Icc a b => p.eval (x : ℝ),
    p.continuous.comp continuous_subtype_val⟩ : C(Set.Icc a b, ℝ))
  map_add' p q := ContinuousMap.ext fun x => Polynomial.eval_add
  map_smul' c p := ContinuousMap.ext fun x => by
    show Polynomial.eval (x : ℝ) (c • p) = c • Polynomial.eval (x : ℝ) p
    simp

open MeasureTheory in
/-- The inner product of two polynomials in {lit}`C[a, b]` is {lit}`∫ₐᵇ p q`. -/
theorem inner_polyL2 {a b : ℝ} [Fact (a < b)] (p q : Polynomial ℝ) :
    ⟪polyL2 a b p, polyL2 a b q⟫_ℝ = ∫ x in a..b, p.eval x * q.eval x := by
  have hab : a ≤ b := le_of_lt Fact.out
  calc _ = ∫ x : ↥(Set.Icc a b), (fun y => p.eval y * q.eval y) (x : ℝ) := rfl
    _ = ∫ x in Set.Icc a b, p.eval x * q.eval x :=
        integral_subtype_comap measurableSet_Icc (fun y => p.eval y * q.eval y)
    _ = ∫ x in a..b, p.eval x * q.eval x := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- The squared distance between two polynomials in {lit}`C[a, b]` is
{lit}`∫ₐᵇ |p − q|²`. -/
theorem norm_polyL2_sub_sq {a b : ℝ} [Fact (a < b)] (p q : Polynomial ℝ) :
    ‖polyL2 a b p - polyL2 a b q‖ ^ 2 = ∫ x in a..b, |p.eval x - q.eval x| ^ 2 := by
  rw [← map_sub, ← real_inner_self_eq_norm_sq, inner_polyL2]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Polynomial.eval_sub, sq_abs]
  ring

/-- {lit}`∫₀¹ ∑ aᵢ xⁱ = ∑ aᵢ / (i + 1)` for polynomials of degree at most 6. -/
theorem integral_sum_pow_seven (a : Fin 7 → ℝ) :
    ∫ x in (0 : ℝ)..1, ∑ i : Fin 7, a i * x ^ (i : ℕ) = ∑ i : Fin 7, a i / ((i : ℕ) + 1) := by
  rw [intervalIntegral.integral_finsetSum (f := fun (i : Fin 7) (x : ℝ) => a i * x ^ (i : ℕ))
    (fun i _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp [div_eq_mul_inv]

/-- 6C.17 answer: the minimizing {lit}`p ∈ 𝒫₃(ℝ)` — a concrete polynomial to be
supplied. -/
-- to find it
-- 1) define a subspace U of poly satisfying p(0) = 0, p'(0) = 0
--    notice it is spanned by x^2 and x^3 (since 1 and x don't vanish at 0)
-- 2) find an orthonormal basis for U
--    √5 * x^2 and 6√7 * (x^3 - (5/6) * x^2)
--    (∫₀¹ x⁴ = 1/5; ⟨x³, x²⟩/⟨x², x²⟩ = (1/6)/(1/5) = 5/6; ‖x³ − (5/6)x²‖² = 1/252)
-- 3) project 2 + 3x onto this basis to find the minimizing polynomial
--    ∫₀¹ (2 + 3x) * (√5 * x^2) dx and ∫₀¹ (2 + 3x) * (6√7 * (x^3 - (5/6) * x^2)) dx to find the coefficients
--    these are (17/12)·√5 and −(29/360)·6√7, so
--    p = (85/12) x² − (203/10) (x³ − (5/6) x²) = 24 x² − (203/10) x³
noncomputable def p6C17 : Polynomial ℝ :=
  Polynomial.C 24 * Polynomial.X ^ 2 - Polynomial.C (203 / 10) * Polynomial.X ^ 3

/-- 6C.17 Find {lit}`p ∈ 𝒫₃(ℝ)` with {lit}`p(0) = 0` and {lit}`p′(0) = 0`
minimizing {lit}`∫₀¹ |2 + 3x − p(x)|²`. -/
theorem exercise_6C_17 :
    p6C17.degree ≤ 3 ∧ p6C17.eval 0 = 0 ∧
      (Polynomial.derivative p6C17).eval 0 = 0 ∧
      ∀ q : Polynomial ℝ, q.degree ≤ 3 → q.eval 0 = 0 →
        (Polynomial.derivative q).eval 0 = 0 →
        (∫ x in (0 : ℝ)..1, |2 + 3 * x - p6C17.eval x| ^ 2) ≤
          (∫ x in (0 : ℝ)..1, |2 + 3 * x - q.eval x| ^ 2) := by
  open Polynomial in
  refine ⟨?_, by simp [p6C17], by simp [p6C17], ?_⟩
  · unfold p6C17
    compute_degree
  intro q hq hq0 hq1
  -- work in `C[0, 1]`: `v = 2 + 3x`, and `U = span(x², x³)`
  set v : L2C 0 1 := polyL2 0 1 (C 2 + C 3 * X) with hv
  set U : Submodule ℝ (L2C 0 1) := Submodule.span ℝ {polyL2 0 1 (X ^ 2), polyL2 0 1 (X ^ 3)}
    with hUdef
  have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  -- `p ∈ U`
  have hpU : polyL2 0 1 p6C17 ∈ U := by
    refine Submodule.mem_span_pair.mpr ⟨24, -(203 / 10), ?_⟩
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simp [p6C17, Polynomial.smul_eq_C_mul]
    ring
  -- `v − p` is orthogonal to `x²` and `x³`, so lies in `U⟂`
  have hperp : v - polyL2 0 1 p6C17 ∈ Uᗮ := by
    rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le, hUdef,
      Submodule.isOrtho_span]
    rintro _ rfl _ (rfl | rfl)
    · rw [hv, ← map_sub, inner_polyL2, intervalIntegral.integral_congr
        (g := fun x => ∑ i : Fin 7, ![0, 0, 2, 3, -24, 203 / 10, 0] i * x ^ (i : ℕ))
        (fun x _ => by simp [p6C17, Fin.sum_univ_succ]; ring), integral_sum_pow_seven]
      simp [Fin.sum_univ_succ]
      norm_num
    · rw [hv, ← map_sub, inner_polyL2, intervalIntegral.integral_congr
        (g := fun x => ∑ i : Fin 7, ![0, 0, 0, 2, 3, -24, 203 / 10] i * x ^ (i : ℕ))
        (fun x _ => by simp [p6C17, Fin.sum_univ_succ]; ring), integral_sum_pow_seven]
      simp [Fin.sum_univ_succ]
      norm_num
  -- hence `p = P_U v`
  have hproj : U.starProjection v = polyL2 0 1 p6C17 := starProjection_eq_of_mem U hpU hperp
  -- a competitor `q` is `c x² + e x³` (degree `≤ 3`, `q(0) = q′(0) = 0`), so it is in `U` too
  have hnat : q.natDegree < 4 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le hq)
  have hc0 : q.coeff 0 = 0 := by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hq0
  have hc1 : q.coeff 1 = 0 := by
    have h := hq1
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] at h
    simpa using h
  have hqU : polyL2 0 1 q ∈ U := by
    refine Submodule.mem_span_pair.mpr ⟨q.coeff 2, q.coeff 3, ?_⟩
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext n
    have hn : ∀ n, 4 ≤ n → q.coeff n = 0 := fun n hn =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hnat hn)
    simp only [Polynomial.coeff_add, Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul]
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> simp [hc0, hc1]
    · rw [hn n h]
      have h2 : n ≠ 2 := by omega
      have h3 : n ≠ 3 := by omega
      simp [h2, h3]
  -- 6.61: `P_U v` is the closest point of `U` to `v`
  have h := minimizing_distance (U := U) v (polyL2 0 1 q) hqU
  rw [hproj] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [hv, norm_polyL2_sub_sq, norm_polyL2_sub_sq] at h2
  simpa using h2

/-! Bridge for 6C.18: integrating a polynomial against {lit}`sin`, and
{lit}`sin` against polynomials in {lit}`C[−π, π]`. -/

open Polynomial in
/-- Integrating a polynomial of degree at most 5 against {lit}`sin`, by repeated
integration by parts: with {lit}`B = P − P″ + P⁗`, an antiderivative of
{lit}`P sin` is {lit}`B′ sin − B cos`. -/
theorem integral_poly_mul_sin (P : Polynomial ℝ) (hP : derivative^[6] P = 0) (l u : ℝ) :
    ∫ x in l..u, P.eval x * Real.sin x =
      ((derivative (P - derivative^[2] P + derivative^[4] P)).eval u * Real.sin u
          - (P - derivative^[2] P + derivative^[4] P).eval u * Real.cos u) -
        ((derivative (P - derivative^[2] P + derivative^[4] P)).eval l * Real.sin l
          - (P - derivative^[2] P + derivative^[4] P).eval l * Real.cos l) := by
  set B := P - derivative^[2] P + derivative^[4] P with hB
  have hAB : derivative (derivative B) + B = P := by
    have hP' : derivative (derivative (derivative (derivative (derivative (derivative P)))))
        = 0 := hP
    simp only [hB, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
      map_sub, map_add, hP']
    ring
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => (derivative B).eval x * Real.sin x - B.eval x * Real.cos x)
    (fun x _ => ?_) ((P.continuous.mul Real.continuous_sin).intervalIntegrable _ _)
  have h := (((derivative B).hasDerivAt x).mul (Real.hasDerivAt_sin x)).sub
    ((B.hasDerivAt x).mul (Real.hasDerivAt_cos x))
  convert h using 1
  have h2 := congrArg (Polynomial.eval x) hAB
  simp only [eval_add] at h2
  rw [← h2]
  ring

open MeasureTheory in
/-- The inner product of a polynomial with {lit}`sin` in {lit}`C[−π, π]` is
{lit}`∫ q sin`. -/
theorem inner_polyL2_sinL2 (q : Polynomial ℝ) :
    ⟪polyL2 (-Real.pi) Real.pi q, sinL2⟫_ℝ
      = ∫ x in (-Real.pi)..Real.pi, q.eval x * Real.sin x := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  calc _ = ∫ x : ↥(Set.Icc (-Real.pi) Real.pi), (fun y => q.eval y * Real.sin y) (x : ℝ) := rfl
    _ = ∫ x in Set.Icc (-Real.pi) Real.pi, q.eval x * Real.sin x :=
        integral_subtype_comap measurableSet_Icc (fun y => q.eval y * Real.sin y)
    _ = _ := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

open MeasureTheory in
/-- The squared distance from {lit}`sin` to a polynomial in {lit}`C[−π, π]` is
{lit}`∫ |sin − q|²`. -/
theorem norm_sinL2_sub_polyL2_sq (q : Polynomial ℝ) :
    ‖sinL2 - polyL2 (-Real.pi) Real.pi q‖ ^ 2
      = ∫ x in (-Real.pi)..Real.pi, |Real.sin x - q.eval x| ^ 2 := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← real_inner_self_eq_norm_sq]
  calc _ = ∫ x : ↥(Set.Icc (-Real.pi) Real.pi),
          (fun y => (Real.sin y - q.eval y) * (Real.sin y - q.eval y)) (x : ℝ) := rfl
    _ = ∫ x in Set.Icc (-Real.pi) Real.pi, (Real.sin x - q.eval x) * (Real.sin x - q.eval x) :=
        integral_subtype_comap measurableSet_Icc
          (fun y => (Real.sin y - q.eval y) * (Real.sin y - q.eval y))
    _ = ∫ x in (-Real.pi)..Real.pi, (Real.sin x - q.eval x) * (Real.sin x - q.eval x) := by
        rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
    _ = _ := intervalIntegral.integral_congr fun x _ => by simp only [sq_abs]; ring

/-- 6C.18 answer: the minimizing {lit}`p ∈ 𝒫₅(ℝ)`. -/
-- similarly to 17, first we find an orthonormal basis for P₅ by
-- doing gram-schmidt on the standard basis of P₅ - 1,x,x^2,x^3,x^4,x^5
-- The result is (the Legendre polynomials in t = x/π, normalized on [−π, π])
-- p0 = √(1/(2π))
-- p1 = √(3/(2π)) · x/π
-- p2 = √(5/(8π)) · (3x²/π² − 1)
-- p3 = √(7/(8π)) · (5x³/π³ − 3x/π)
-- p4 = √(9/(128π)) · (35x⁴/π⁴ − 30x²/π² + 3)
-- p5 = √(11/(128π)) · (63x⁵/π⁵ − 70x³/π³ + 15x/π)
-- then project sin x onto this basis to find the minimizing polynomial
-- exact integrals over [−π, π] (integration by parts; sin is odd, so even powers give 0):
--   ∫ x sin x = 2π,  ∫ x³ sin x = 2π³ − 12π,  ∫ x⁵ sin x = 2π⁵ − 40π³ + 240π
-- so ⟨sin, p0⟩ = ⟨sin, p2⟩ = ⟨sin, p4⟩ = 0 and
--   ⟨sin, p1⟩ p1 = (3/(2π)) · 2 · x/π
--   ⟨sin, p3⟩ p3 = (7/(8π)) · (4 − 60/π²) · (5x³/π³ − 3x/π)
--   ⟨sin, p5⟩ p5 = (11/(128π)) · (16 − 1680/π² + 15120/π⁴) · (63x⁵/π⁵ − 70x³/π³ + 15x/π)
-- collecting powers of x:
-- p = 105(1485 − 153π² + π⁴)/(8π⁶) · x − 315(1155 − 125π² + π⁴)/(4π⁸) · x³
--       + 693(945 − 105π² + π⁴)/(8π¹⁰) · x⁵
-- numerically 0.987862 x − 0.155271 x³ + 0.00564312 x⁵, which is Axler's 6.65
noncomputable def p6C18 : Polynomial ℝ :=
  Polynomial.C (105 * (1485 - 153 * Real.pi ^ 2 + Real.pi ^ 4) / (8 * Real.pi ^ 6)) * Polynomial.X
    + Polynomial.C (-(315 * (1155 - 125 * Real.pi ^ 2 + Real.pi ^ 4) / (4 * Real.pi ^ 8)))
        * Polynomial.X ^ 3
    + Polynomial.C (693 * (945 - 105 * Real.pi ^ 2 + Real.pi ^ 4) / (8 * Real.pi ^ 10))
        * Polynomial.X ^ 5

/-- 6C.18 Find {lit}`p ∈ 𝒫₅(ℝ)` minimizing {lit}`∫₋ₚᵢᵖⁱ |sin x − p(x)|²`. -/
theorem exercise_6C_18 :
    p6C18.degree ≤ 5 ∧
      ∀ q : Polynomial ℝ, q.degree ≤ 5 →
        (∫ x in (-Real.pi)..Real.pi, |Real.sin x - p6C18.eval x| ^ 2) ≤
          (∫ x in (-Real.pi)..Real.pi, |Real.sin x - q.eval x| ^ 2) := by
  open Polynomial in
  refine ⟨by unfold p6C18; compute_degree, ?_⟩
  intro q hq
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  set a : ℝ := 105 * (1485 - 153 * Real.pi ^ 2 + Real.pi ^ 4) / (8 * Real.pi ^ 6) with ha
  set b : ℝ := -(315 * (1155 - 125 * Real.pi ^ 2 + Real.pi ^ 4) / (4 * Real.pi ^ 8)) with hb
  set c : ℝ := 693 * (945 - 105 * Real.pi ^ 2 + Real.pi ^ 4) / (8 * Real.pi ^ 10) with hc
  have hpx : ∀ x : ℝ, p6C18.eval x = a * x + b * x ^ 3 + c * x ^ 5 := fun x => by
    simp only [p6C18, a, b, c, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  -- work in `C[−π, π]`: `v = sin`, and `U = span(1, x, …, x⁵)`
  set U : Submodule ℝ (L2C (-Real.pi) Real.pi) :=
    Submodule.span ℝ (Set.range fun k : Fin 6 => polyL2 (-Real.pi) Real.pi (X ^ (k : ℕ)))
    with hUdef
  have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hmem : ∀ k : Fin 6, polyL2 (-Real.pi) Real.pi (X ^ (k : ℕ)) ∈ U := fun k =>
    Submodule.subset_span ⟨k, rfl⟩
  -- `p ∈ U`
  have hpU : polyL2 (-Real.pi) Real.pi p6C18 ∈ U := by
    have h : p6C18 = a • X ^ ((1 : Fin 6) : ℕ) + b • X ^ ((3 : Fin 6) : ℕ)
        + c • X ^ ((5 : Fin 6) : ℕ) := by
      simp [p6C18, Polynomial.smul_eq_C_mul, a, b, c]
    rw [h, map_add, map_add, map_smul, map_smul, map_smul]
    exact U.add_mem (U.add_mem (U.smul_mem _ (hmem 1)) (U.smul_mem _ (hmem 3)))
      (U.smul_mem _ (hmem 5))
  -- the exact value of `∫ xᵏ p`
  have hmono : ∀ k : ℕ,
      ∫ x in (-Real.pi)..Real.pi, (X ^ k : Polynomial ℝ).eval x * p6C18.eval x =
      a * ((Real.pi ^ (k + 2) - (-Real.pi) ^ (k + 2)) / (k + 2))
        + b * ((Real.pi ^ (k + 4) - (-Real.pi) ^ (k + 4)) / (k + 4))
        + c * ((Real.pi ^ (k + 6) - (-Real.pi) ^ (k + 6)) / (k + 6)) := by
    intro k
    rw [intervalIntegral.integral_congr
      (g := fun x => a * x ^ (k + 1) + b * x ^ (k + 3) + c * x ^ (k + 5))
      (fun x _ => by simp only [hpx, eval_pow, eval_X]; ring),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
    push_cast
    ring_nf
  -- `sin − p` is orthogonal to `1, x, …, x⁵`, so lies in `U⟂`: for each `k`,
  -- `∫ xᵏ sin x` (exact, by `integral_poly_mul_sin`) equals `∫ xᵏ p`
  have hperp : sinL2 - polyL2 (-Real.pi) Real.pi p6C18 ∈ Uᗮ := by
    rw [← Submodule.span_singleton_le_iff_mem, ← Submodule.isOrtho_iff_le, hUdef,
      Submodule.isOrtho_span]
    rintro _ rfl _ ⟨k, rfl⟩
    rw [real_inner_comm, inner_sub_right, inner_polyL2_sinL2, inner_polyL2, sub_eq_zero, hmono,
      integral_poly_mul_sin _ (Polynomial.iterate_derivative_eq_zero (by
        rw [natDegree_X_pow]; exact k.2))]
    fin_cases k <;>
      simp [Function.iterate_succ, Real.sin_pi, Real.cos_pi] <;>
      simp only [a, b, c] <;>
      field_simp <;>
      ring
  -- hence `p = P_U (sin)`
  have hproj : U.starProjection sinL2 = polyL2 (-Real.pi) Real.pi p6C18 :=
    starProjection_eq_of_mem U hpU hperp
  -- every polynomial of degree `≤ 5` is in `U`
  have hqU : polyL2 (-Real.pi) Real.pi q ∈ U := by
    have hnat : q.natDegree < 6 :=
      Nat.lt_succ_of_le (Polynomial.natDegree_le_of_degree_le hq)
    rw [q.as_sum_range' 6 hnat, map_sum]
    refine U.sum_mem fun i hi => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul, map_smul]
    exact U.smul_mem _ (hmem ⟨i, Finset.mem_range.mp hi⟩)
  -- 6.61: `P_U (sin)` is the closest point of `U` to `sin`
  have h := minimizing_distance (U := U) sinL2 (polyL2 (-Real.pi) Real.pi q) hqU
  rw [hproj] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [norm_sinL2_sub_polyL2_sq, norm_sinL2_sub_polyL2_sq] at h2
  exact h2

/-- 6C.19 If {lit}`V` is finite-dimensional and {lit}`P` is the orthogonal
projection onto a subspace {lit}`U`, then {lit}`P† = P`. -/
theorem exercise_6C_19 [FiniteDimensional 𝕜 V] (U : Submodule 𝕜 V) :
    (U.starProjection : V →ₗ[𝕜] V)† = (U.starProjection : V →ₗ[𝕜] V) := by
  -- pseudo-inverse: (P|(null P)ᗮ)^-1 P_range P
  -- but for projection range P = U and null P = Uᗮ
  -- so null P)ᗮ = U and P|(null P)ᗮ = P|U = id_U
  -- so P† = Id P_U = P
  refine LinearMap.ext fun w => ?_
  -- by 6.72 it suffices that `P w ∈ (null P)⟂` and `P (P w) = P_(range P) w`
  refine pinv_eq_of _ ?_ ?_
  · -- `(null P)⟂ = (U⟂)⟂ = U`, which contains `P w`
    rw [ker_starProjection, Submodule.orthogonal_orthogonal]
    exact U.starProjection_apply_mem w
  · -- `range P = U`, so `P_(range P) w = P w`; and `P` is the identity on `U`
    have hrange : (LinearMap.range (U.starProjection : V →ₗ[𝕜] V)).starProjection w =
        U.starProjection w := by
      refine starProjection_eq_of_mem _ ⟨w, rfl⟩ ?_
      rw [range_starProjection]
      exact U.sub_starProjection_mem_orthogonal w
    rw [hrange, ContinuousLinearMap.coe_coe]
    exact (starProjection_eq_self_iff U _).mpr (U.starProjection_apply_mem w)

/-- 6C.20 If {lit}`V` is finite-dimensional and {lit}`T ∈ ℒ(V, W)`, then
{lit}`null T† = (range T)⟂` and {lit}`range T† = (null T)⟂`. -/
theorem exercise_6C_20 [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    LinearMap.ker T† = (LinearMap.range T)ᗮ ∧
      LinearMap.range T† = (LinearMap.ker T)ᗮ := by
  -- since T† begins with projection onto range T and an isomorphism on that range
  -- the null space of the composition would only be the null of the projection
  -- and it is by definition the orthogonal complement of the range of T
  -- similarly, since T† ends with an isomorphism on the range of T and (ker T)ᗮ
  -- the range of T† would be exactly (ker T)ᗮ as long as the range of the projection
  -- is exactly the range of T, which it is by definition of the projection.
  constructor
  · -- `T† w = 0 ⟺ P_(range T) w = 0` (the isomorphism and the inclusion are injective)
    ext w
    rw [LinearMap.mem_ker]
    show (((restrEquiv T).symm ((LinearMap.range T).orthogonalProjectionOnto w) :
        Submodule.orthogonal (LinearMap.ker T)) : V) = 0 ↔ _
    rw [Submodule.coe_eq_zero, LinearEquiv.map_eq_zero_iff,
      Submodule.orthogonalProjectionOnto_eq_zero_iff]
  · apply le_antisymm
    · -- `T†` lands in `(null T)⟂`
      rintro _ ⟨w, rfl⟩
      exact pinv_mem_orthogonal T w
    · -- each `v ∈ (null T)⟂` is hit: its image `y ∈ range T` under the isomorphism is
      -- fixed by the projection, and the inverse isomorphism sends `y` back to `v`
      intro v hv
      refine ⟨(restrEquiv T ⟨v, hv⟩ : W), ?_⟩
      show (((restrEquiv T).symm ((LinearMap.range T).orthogonalProjectionOnto
        ((restrEquiv T ⟨v, hv⟩ : LinearMap.range T) : W)) :
          Submodule.orthogonal (LinearMap.ker T)) : V) = v
      rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, LinearEquiv.symm_apply_apply]

/-- 6C.21 {lit}`T ∈ ℒ(𝔽³, 𝔽²)`, {lit}`T(a, b, c) = (a + b + c, 2b + 3c)`. -/
def T6C21 : EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin 2) where
  toFun v := !₂[v 0 + v 1 + v 2, 2 * v 1 + 3 * v 2]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

-- null T = {(a, b, c) | a + b + c = 0 ∧ 2b + 3c = 0}: the vectors orthogonal to
-- (1, 1, 1) and (0, 2, 3), so (null T)ᗮ = span((1, 1, 1), (0, 2, 3)).
-- range T is all of 𝔽², since T(x - y/2, y/2, 0) = (x, y), so P_(range T) = I and
-- T†(x, y) is the vector α * (1, 1, 1) + β * (0, 2, 3) that T sends to (x, y).
-- T(α * (1, 1, 1) + β * (0, 2, 3)) = (3α + 5β, 5α + 13β), and solving
-- 3α + 5β = x, 5α + 13β = y gives α = (13x - 5y) / 14, β = (-5x + 3y) / 14.
-- So T†(x, y) = ((13x - 5y) / 14, (3x + y) / 14, (-2x + 4y) / 14).

/-- 6C.21 (a) answer: a formula for {lit}`T†(x, y)` — a concrete vector of
{lit}`𝔽³`, to be supplied. -/
noncomputable def pinv6C21 (v : EuclideanSpace 𝕜 (Fin 2)) : EuclideanSpace 𝕜 (Fin 3) :=
  (14 : 𝕜)⁻¹ • !₂[13 * v 0 - 5 * v 1, 3 * v 0 + v 1, -2 * v 0 + 4 * v 1]

/-- {lit}`T` sends the formula back to {lit}`(x, y)`. -/
theorem T6C21_pinv6C21 (v : EuclideanSpace 𝕜 (Fin 2)) : T6C21 (pinv6C21 v) = v := by
  have h14 : (14 : 𝕜) ≠ 0 := by norm_num
  ext i
  fin_cases i <;> simp [T6C21, pinv6C21] <;> field_simp <;> ring

/-- The formula lies in {lit}`(null T)⟂`: it is
{lit}`α(1, 1, 1) + β(0, 2, 3)`, and {lit}`null T` is cut out by those two vectors. -/
theorem pinv6C21_mem (v : EuclideanSpace 𝕜 (Fin 2)) :
    pinv6C21 v ∈ (LinearMap.ker (T6C21 (𝕜 := 𝕜)))ᗮ := by
  have h14 : (14 : 𝕜) ≠ 0 := by norm_num
  intro u hu
  rw [LinearMap.mem_ker] at hu
  have h0 : u 0 + u 1 + u 2 = 0 := by
    have := congrArg (fun z : EuclideanSpace 𝕜 (Fin 2) => z 0) hu
    simpa [T6C21] using this
  have h1 : 2 * u 1 + 3 * u 2 = 0 := by
    have := congrArg (fun z : EuclideanSpace 𝕜 (Fin 2) => z 1) hu
    simpa [T6C21] using this
  have h0' : conj (u 0) + conj (u 1) + conj (u 2) = 0 := by
    rw [← map_add, ← map_add, h0, map_zero]
  have h1' : 2 * conj (u 1) + 3 * conj (u 2) = 0 := by
    simpa [map_ofNat] using congrArg (starRingEnd 𝕜) h1
  simp only [pinv6C21, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
    PiLp.smul_apply, smul_eq_mul, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  linear_combination (13 * v 0 - 5 * v 1) * h0' + (-5 * v 0 + 3 * v 1) * h1'

/-- {lit}`range T` is all of {lit}`𝔽²`, so {lit}`P_(range T) = I`. -/
theorem starProjection_range_T6C21 (v : EuclideanSpace 𝕜 (Fin 2)) :
    (LinearMap.range (T6C21 (𝕜 := 𝕜))).starProjection v = v :=
  (starProjection_eq_self_iff (LinearMap.range (T6C21 (𝕜 := 𝕜))) v).mpr
    ⟨pinv6C21 v, T6C21_pinv6C21 v⟩

/-- 6C.21 (a) For {lit}`(x, y) ∈ 𝔽²`, find a formula for {lit}`T†(x, y)`. -/
theorem exercise_6C_21a (v : EuclideanSpace 𝕜 (Fin 2)) :
    (T6C21 (𝕜 := 𝕜))† v = pinv6C21 v := by
  -- by 6.72, `T† w` is the vector of `(null T)⟂` that `T` sends to `P_(range T) w`
  refine pinv_eq_of _ (pinv6C21_mem v) ?_
  rw [T6C21_pinv6C21, starProjection_range_T6C21]

/-- 6C.21 (b) Verify {lit}`T T† = P_(range T)` (6.69(b)) for that formula. -/
theorem exercise_6C_21b :
    T6C21 ∘ₗ (T6C21 (𝕜 := 𝕜))† =
      ((LinearMap.range (T6C21 (𝕜 := 𝕜))).starProjection :
        EuclideanSpace 𝕜 (Fin 2) →ₗ[𝕜] _) := by
  -- left side, from the formula: `T (T†(x, y))`
  --   `= ((13x − 5y) + (3x + y) + (−2x + 4y), 2(3x + y) + 3(−2x + 4y)) / 14 = (x, y)`
  -- right side: `range T = 𝔽²`, so `P_(range T)(x, y) = (x, y)`
  have h14 : (14 : 𝕜) ≠ 0 := by norm_num
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, exercise_6C_21a, ContinuousLinearMap.coe_coe,
    starProjection_range_T6C21]
  ext i
  fin_cases i <;> simp [T6C21, pinv6C21] <;> field_simp <;> ring

/-- An explicit formula for {lit}`P_(null T)⟂`: {lit}`null T` is spanned by
{lit}`n = (1, −3, 2)` with {lit}`‖n‖² = 14`, so
{lit}`P_(null T)⟂ (a, b, c) = (a, b, c) − ((a − 3b + 2c)/14)·n`
{lit}`= (13a + 3b − 2c, 3a + 5b + 6c, −2a + 6b + 10c)/14`. -/
theorem starProjection_ker_orthogonal_T6C21 (u : EuclideanSpace 𝕜 (Fin 3)) :
    (Submodule.orthogonal (LinearMap.ker (T6C21 (𝕜 := 𝕜)))).starProjection u =
      (14 : 𝕜)⁻¹ • !₂[13 * u 0 + 3 * u 1 - 2 * u 2, 3 * u 0 + 5 * u 1 + 6 * u 2,
        -2 * u 0 + 6 * u 1 + 10 * u 2] := by
  have h14 : (14 : 𝕜) ≠ 0 := by norm_num
  refine starProjection_eq_of_mem _ ?_ ?_
  · -- the right side is orthogonal to `null T`
    intro k hk
    rw [LinearMap.mem_ker] at hk
    have h0 : k 0 + k 1 + k 2 = 0 := by
      have := congrArg (fun z : EuclideanSpace 𝕜 (Fin 2) => z 0) hk
      simpa [T6C21] using this
    have h1 : 2 * k 1 + 3 * k 2 = 0 := by
      have := congrArg (fun z : EuclideanSpace 𝕜 (Fin 2) => z 1) hk
      simpa [T6C21] using this
    have h0' : conj (k 0) + conj (k 1) + conj (k 2) = 0 := by
      rw [← map_add, ← map_add, h0, map_zero]
    have h1' : 2 * conj (k 1) + 3 * conj (k 2) = 0 := by
      simpa [map_ofNat] using congrArg (starRingEnd 𝕜) h1
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three,
      PiLp.smul_apply, smul_eq_mul, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    linear_combination (13 * u 0 + 3 * u 1 - 2 * u 2) * h0'
      + (-5 * u 0 + u 1 + 4 * u 2) * h1'
  · -- and `u` minus it, a multiple of `(1, −3, 2)`, is in `null T`
    apply Submodule.le_orthogonal_orthogonal
    rw [LinearMap.mem_ker]
    ext i
    fin_cases i <;> simp [T6C21] <;> field_simp <;> ring

/-- 6C.21 (c) Verify {lit}`T† T = P_(null T)⟂` (6.69(c)) for that formula. -/
theorem exercise_6C_21c :
    (T6C21 (𝕜 := 𝕜))† ∘ₗ T6C21 =
      ((Submodule.orthogonal (LinearMap.ker (T6C21 (𝕜 := 𝕜)))).starProjection :
        EuclideanSpace 𝕜 (Fin 3) →ₗ[𝕜] _) := by
  -- left side, from the formula at `(x, y) = T(a, b, c) = (a + b + c, 2b + 3c)`:
  --   `T†(T(a, b, c)) = (13a + 3b − 2c, 3a + 5b + 6c, −2a + 6b + 10c) / 14`
  -- right side: the same vector, by the explicit formula for `P_(null T)⟂`
  refine LinearMap.ext fun u => ?_
  rw [LinearMap.comp_apply, exercise_6C_21a, ContinuousLinearMap.coe_coe,
    starProjection_ker_orthogonal_T6C21]
  ext i
  fin_cases i <;> simp [T6C21, pinv6C21] <;> ring

/-- 6C.22 If {lit}`V` is finite-dimensional and {lit}`T ∈ ℒ(V, W)`, then
{lit}`T T† T = T` and {lit}`T† T T† = T†`. -/
theorem exercise_6C_22 [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    T ∘ₗ T† ∘ₗ T = T ∧ T† ∘ₗ T ∘ₗ T† = T† := by
  -- T T† T = P_{range T} T = T (first by proven theorem, and second since proj into range is id on range)
  -- T† T T† = T† P_range{T} = T† (since T† = S P_range{T} for some S), and P_U^2 = P_U
  constructor
  · refine LinearMap.ext fun v => ?_
    -- `T T† = P_(range T)` (6.69(b)), applied to `T v ∈ range T`
    have h := LinearMap.congr_fun (T_comp_pinv T) (T v)
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at h ⊢
    rw [h]
    exact (starProjection_eq_self_iff (LinearMap.range T) _).mpr ⟨v, rfl⟩
  · refine LinearMap.ext fun w => ?_
    -- `T T† w = P_(range T) w`, and `T† = S P_(range T)` with `P_(range T)² = P_(range T)`
    have h := LinearMap.congr_fun (T_comp_pinv T) w
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at h ⊢
    rw [h, pinv_apply, pinv_apply, Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- 6C.23 If {lit}`V` and {lit}`W` are finite-dimensional and {lit}`T ∈ ℒ(V, W)`,
then {lit}`(T†)† = T`. -/
theorem exercise_6C_23 [FiniteDimensional 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (T : V →ₗ[𝕜] W) :
    T†† = T := by
  -- T†† = (T†|null T†)ᗮ^-1 P_{range T†} =
  -- by earler ex. =  (T†|{range T})^-1 P_{null Tᗮ}
  -- but on range T iso P_{null Tᗮ}, T† and T are inverses
  -- = T|{null Tᗮ} P_{null Tᗮ}
  -- but projection to null Tᗮ is noop when followed by T, because
  -- T maps null T to 0, so T P_{null Tᗮ} = T
  refine LinearMap.ext fun v => ?_
  -- by 6.72 for `T†`: `T v` is the vector of `(null T†)⟂` that `T†` sends to `P_(range T†) v`
  refine pinv_eq_of _ ?_ ?_
  · -- `(null T†)⟂ = ((range T)⟂)⟂ = range T` (6C.20), which contains `T v`
    rw [(exercise_6C_20 T).1, Submodule.orthogonal_orthogonal]
    exact ⟨v, rfl⟩
  · -- `T† (T v) = P_(null T)⟂ v` (6.69(c)), and `range T† = (null T)⟂` (6C.20)
    have h := LinearMap.congr_fun (pinv_comp_T T) v
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at h
    rw [h]
    simp only [(exercise_6C_20 T).2]

end LADR.Section_6C
