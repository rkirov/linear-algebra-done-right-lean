import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Skippable infrastructure: the L² inner product space `C[a,b]`

**A reader of the companion can skip this file entirely.** It contains no Axler
content — it exists only so that the function-space exercises (6C.16, 7A.31,
7C.25, …) and worked examples (6.34, 6.41, 6.63) have an inner product space to be
stated in.

The obstruction it works around: mathlib puts the *supremum* norm on
`C(Set.Icc a b, ℝ)` and provides no measure on the interval subtype, whereas Axler
uses the `L²` inner product `⟨f, g⟩ = ∫ₐᵇ f g`. So we (i) equip the interval
subtype with its Lebesgue measure and (ii) introduce a type synonym `L2C a b`
carrying the `L²` inner product instead of the sup norm.

The inner product space structure is fully proved (no axioms). Positive
definiteness genuinely requires a nondegenerate interval, so the inner product
space instance is gated on `Fact (a < b)` — for the degenerate interval `a = b`
the interval subtype is a single point of Lebesgue measure zero, on which
`⟨f, f⟩ = 0` for every `f`.
-/

open MeasureTheory

noncomputable instance instMeasureSpaceIcc {a b : ℝ} : MeasureSpace (Set.Icc a b) :=
  Measure.Subtype.measureSpace

variable {a b : ℝ}

/-- The interval subtype embeds measurably into `ℝ`. -/
theorem measurableEmbedding_val_Icc :
    MeasurableEmbedding (Subtype.val : ↥(Set.Icc a b) → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Icc

instance instCompactSpaceIcc : CompactSpace ↥(Set.Icc a b) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

instance instIsFiniteMeasureIcc : IsFiniteMeasure (volume : Measure ↥(Set.Icc a b)) := by
  refine ⟨?_⟩
  rw [volume_set_coe_def, measurableEmbedding_val_Icc.comap_apply, Subtype.coe_image_univ,
    Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- On a nondegenerate interval the subtype Lebesgue measure gives every nonempty
open set positive measure. -/
instance instIsOpenPosMeasureIcc [Fact (a < b)] :
    (volume : Measure ↥(Set.Icc a b)).IsOpenPosMeasure := by
  have hab : a < b := Fact.out
  refine ⟨fun U hU hne => ?_⟩
  rw [volume_set_coe_def, measurableEmbedding_val_Icc.comap_apply]
  obtain ⟨V, hVopen, hVU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨x, hxU⟩ := hne
  have hxV : (x : ℝ) ∈ V := by rw [← Set.mem_preimage, hVU]; exact hxU
  have himg : Subtype.val '' U = V ∩ Set.Icc a b := by
    rw [← hVU, Subtype.image_preimage_coe]; exact Set.inter_comm _ _
  rw [himg]
  -- `V ∩ Ioo a b` is a nonempty open subset of `ℝ`, hence of positive volume.
  have hclos : (x : ℝ) ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]; exact x.2
  have hVIoo : (V ∩ Set.Ioo a b).Nonempty := mem_closure_iff.mp hclos V hVopen hxV
  have hposIoo : 0 < volume (V ∩ Set.Ioo a b) :=
    (hVopen.inter isOpen_Ioo).measure_pos volume hVIoo
  have hsub : V ∩ Set.Ioo a b ⊆ V ∩ Set.Icc a b :=
    Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self
  exact (lt_of_lt_of_le hposIoo (measure_mono hsub)).ne'

/-- `C[a, b]` carrying the `L²` inner product — a type synonym for
`C(Set.Icc a b, ℝ)` that avoids mathlib's sup-norm instance. -/
def L2C (a b : ℝ) : Type := C(Set.Icc a b, ℝ)

namespace L2C

instance : AddCommGroup (L2C a b) := inferInstanceAs (AddCommGroup C(Set.Icc a b, ℝ))
noncomputable instance : Module ℝ (L2C a b) := inferInstanceAs (Module ℝ C(Set.Icc a b, ℝ))

/-- View an element of `L2C a b` as an ordinary continuous function. -/
def toCont (f : L2C a b) : C(Set.Icc a b, ℝ) := f

@[simp] theorem toCont_add (f g : L2C a b) : (f + g).toCont = f.toCont + g.toCont := rfl
@[simp] theorem toCont_smul (c : ℝ) (f : L2C a b) : (c • f).toCont = c • f.toCont := rfl

/-- The product of the two continuous functions is integrable (continuous on the
compact interval subtype, which carries a finite measure). -/
theorem integrable_toCont_mul (f g : L2C a b) :
    Integrable (fun x => f.toCont x * g.toCont x) volume := by
  rw [← integrableOn_univ]
  exact (f.toCont.continuous.mul g.toCont.continuous).continuousOn.integrableOn_compact
    isCompact_univ

/-- The `L²` inner product `⟨f, g⟩ = ∫ₐᵇ f g` on `C[a, b]`. -/
noncomputable def core [Fact (a < b)] : InnerProductSpace.Core ℝ (L2C a b) where
  inner f g := ∫ x, f.toCont x * g.toCont x
  conj_inner_symm f g := by
    simp only [RCLike.star_def, starRingEnd_apply, star_trivial]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    exact integral_nonneg (fun x => mul_self_nonneg _)
  add_left f g h := by
    simp only [toCont_add, ContinuousMap.add_apply]
    rw [← integral_add (integrable_toCont_mul f h) (integrable_toCont_mul g h)]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  smul_left f g c := by
    simp only [toCont_smul, ContinuousMap.smul_apply, smul_eq_mul, RCLike.star_def,
      starRingEnd_apply, star_trivial]
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  definite f hf := by
    have hnn : 0 ≤ fun x : ↥(Set.Icc a b) => f.toCont x * f.toCont x :=
      fun x => mul_self_nonneg _
    have hae : (fun x => f.toCont x * f.toCont x) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg hnn (integrable_toCont_mul f f)).mp hf
    have hae0 : (⇑f.toCont : ↥(Set.Icc a b) → ℝ) =ᵐ[volume] 0 := by
      filter_upwards [hae] with x hx using mul_self_eq_zero.mp hx
    have hzero : (⇑f.toCont : ↥(Set.Icc a b) → ℝ) = 0 :=
      (Continuous.ae_eq_iff_eq volume f.toCont.continuous continuous_zero).mp hae0
    have hcont : f.toCont = 0 := by ext x; exact congrFun hzero x
    exact hcont

noncomputable instance [Fact (a < b)] : NormedAddCommGroup (L2C a b) := core.toNormedAddCommGroup
noncomputable instance [Fact (a < b)] : InnerProductSpace ℝ (L2C a b) := InnerProductSpace.ofCore _

end L2C

-- sanity: the orthogonal complement of a subspace is available
noncomputable example {a b : ℝ} [Fact (a < b)] (U : Submodule ℝ (L2C a b)) :
    Submodule ℝ (L2C a b) := Uᗮ
