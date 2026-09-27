import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Ring
import Mathlib.Tactic.TFAE
import LinearAlgebraDoneRightLean.Section_2A
import LinearAlgebraDoneRightLean.Section_2B
import LinearAlgebraDoneRightLean.Section_2C
import LinearAlgebraDoneRightLean.Section_3A
import LinearAlgebraDoneRightLean.Section_3B
import LinearAlgebraDoneRightLean.Section_3C
import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 3D: Invertibility and Isomorphisms
-/

namespace LADR.Section_3D

open LADR.Section_2A (Spans)
open LADR.Section_2B (IsBasis)
open LADR.Section_3C (matrixOf matrixOf_apply matrixOf_spec matrixOf_comp
  columnRank column row)
open Module (Finite finrank)

variable {F : Type*} [Field F]
  {U V W : Type*} [AddCommGroup U] [Module F U]
    [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W]

/-! 3.59 Definition: invertible, inverse

A linear map {lit}`T : V → W` is *invertible* if there exists
{lit}`S : W → V` linear with {lit}`S ∘ T = id_V` and {lit}`T ∘ S = id_W`.

mathlib has no {lit}`Prop`-valued "is invertible" predicate for plain linear
maps. Instead it *bundles* the inverse into the isomorphism
{name}`LinearEquiv` ({lit}`V ≃ₗ[F] W`), and the way to *say* a given
{lit}`T : V →ₗ[F] W` is invertible is {name}`Function.Bijective` {lit}`T`
(then {name}`LinearEquiv.ofBijective` produces the bundled equiv). Our
{lit}`IsInvertible` follows Axler's two-sided-inverse phrasing; the bridge
{lit}`isInvertible_iff_bijective` (3.63 below) connects it to mathlib's
{name}`Function.Bijective` convention.
-/

def IsInvertible (T : V →ₗ[F] W) : Prop :=
  ∃ S : W →ₗ[F] V,
    S ∘ₗ T = LinearMap.id ∧ T ∘ₗ S = LinearMap.id

/-! 3.60 Inverse is unique -/

theorem inv_unique (T : V →ₗ[F] W)
    {S₁ S₂ : W →ₗ[F] V}
    (h₁ : S₁ ∘ₗ T = LinearMap.id ∧ T ∘ₗ S₁ = LinearMap.id)
    (h₂ : S₂ ∘ₗ T = LinearMap.id ∧ T ∘ₗ S₂ = LinearMap.id) :
    S₁ = S₂ := by
  have : S₁ ∘ₗ (T ∘ₗ S₂) = S₁ ∘ₗ LinearMap.id := by rw [h₂.2]
  calc S₁ = S₁ ∘ₗ LinearMap.id := by ext; rfl
    _ = S₁ ∘ₗ (T ∘ₗ S₂) := by rw [h₂.2]
    _ = (S₁ ∘ₗ T) ∘ₗ S₂ := rfl
    _ = LinearMap.id ∘ₗ S₂ := by rw [h₁.1]
    _ = S₂ := by ext; rfl

/-! 3.61 Notation: {lit}`T⁻¹`. We use {name}`Classical.choose` to extract
the inverse from the existential. -/

noncomputable def IsInvertible.inv {T : V →ₗ[F] W} (h : IsInvertible T) :
    W →ₗ[F] V := Classical.choose h

theorem IsInvertible.inv_comp {T : V →ₗ[F] W} (h : IsInvertible T) :
    h.inv ∘ₗ T = LinearMap.id := (Classical.choose_spec h).1

theorem IsInvertible.comp_inv {T : V →ₗ[F] W} (h : IsInvertible T) :
    T ∘ₗ h.inv = LinearMap.id := (Classical.choose_spec h).2

/-! Bridge to mathlib's {name}`LinearEquiv`. -/

noncomputable def IsInvertible.toLinearEquiv {T : V →ₗ[F] W}
    (h : IsInvertible T) : V ≃ₗ[F] W :=
  { T with
    invFun := h.inv
    left_inv := fun v => LinearMap.congr_fun h.inv_comp v
    right_inv := fun w => LinearMap.congr_fun h.comp_inv w }

theorem LinearEquiv.isInvertible (E : V ≃ₗ[F] W) :
    IsInvertible (E : V →ₗ[F] W) :=
  ⟨E.symm, by ext v; simp, by ext w; simp⟩

/-! 3.62 Example: {lit}`T(x, y, z) = (-y, x, 4z)` on {lit}`ℝ³`. -/

noncomputable def T_3_62 : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![-v 1, v 0, 4 * v 2]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring

noncomputable def T_3_62_inv : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := ![v 1, -v 0, v 2 / 4]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  map_smul' a x := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring

example : IsInvertible T_3_62 := by
  refine ⟨T_3_62_inv, ?_, ?_⟩
  · ext v i
    fin_cases i <;> simp [T_3_62, T_3_62_inv,
      Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.coe_mk,
      AddHom.coe_mk]
  · ext v i
    fin_cases i <;> simp [T_3_62, T_3_62_inv,
      Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.coe_mk,
      AddHom.coe_mk]; ring

/-! 3.63 Invertible iff injective and surjective -/

theorem isInvertible_of_bijective (T : V →ₗ[F] W) (hT : Function.Bijective T) :
    IsInvertible T := by
  obtain ⟨hinj, hsurj⟩ := hT
  -- Following Axler: surjectivity lets us pick, for each {lit}`w`, a preimage
  -- {lit}`g w` with {lit}`T (g w) = w`. Injectivity makes it unique, which is
  -- what forces {lit}`g` to be linear.
  let g : W → V := Function.surjInv hsurj
  have hTg : ∀ w, T (g w) = w := Function.surjInv_eq hsurj
  -- {lit}`S` packages {lit}`g` as a linear map; both linearity laws are proved
  -- by applying the injective {lit}`T` and cancelling with {lit}`hTg`.
  let S : W →ₗ[F] V :=
    { toFun := g
      map_add' := by
        intro w₁ w₂
        apply hinj
        rw [map_add, hTg, hTg, hTg]
      map_smul' := by
        intro a w
        apply hinj
        rw [map_smul, hTg, RingHom.id_apply, hTg] }
  refine ⟨S, ?_, ?_⟩
  · -- {lit}`S ∘ T = id`: {lit}`T (S (T v)) = T v`, so injectivity gives
    -- {lit}`S (T v) = v`.
    ext v
    exact hinj (hTg (T v))
  · -- {lit}`T ∘ S = id` is exactly {lit}`hTg`.
    ext w
    exact hTg w

theorem isInvertible_iff_bijective (T : V →ₗ[F] W) :
    IsInvertible T ↔ Function.Bijective T := by
  refine ⟨?_, isInvertible_of_bijective T⟩
  rintro ⟨S, hST, hTS⟩
  refine ⟨?_, ?_⟩
  · intro u v huv
    have h := congrArg S huv
    rw [show S (T u) = u from LinearMap.congr_fun hST u,
        show S (T v) = v from LinearMap.congr_fun hST v] at h
    exact h
  · intro w
    refine ⟨S w, ?_⟩
    exact LinearMap.congr_fun hTS w

/-! 3.64 Example: in infinite dimensions, neither injectivity nor surjectivity
implies invertibility.

- Multiplication by {lit}`X²` on {lit}`𝒫(ℝ)` is injective but not surjective
  (the constant polynomial {lit}`1` is not in its range).
- The backward shift on {lit}`F^∞` is surjective but not injective
  (the unit basis vector {lit}`(1, 0, 0, …)` is in its kernel). -/

example : Function.Injective LADR.Section_3A.multByXSq := by
  intro p q hpq
  have h : (Polynomial.X ^ 2 : Polynomial ℝ) * p = Polynomial.X ^ 2 * q := hpq
  have hX2 : (Polynomial.X ^ 2 : Polynomial ℝ) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.coeff · 2) h
    simp [Polynomial.coeff_X_pow] at this
  exact mul_left_cancel₀ hX2 h

example : ¬ Function.Surjective LADR.Section_3A.multByXSq := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (1 : Polynomial ℝ)
  have h : (Polynomial.X ^ 2 : Polynomial ℝ) * p = 1 := hp
  -- {lit}`(X² · p).coeff 0 = 0 ≠ 1 = (1).coeff 0`.
  have hc : (Polynomial.X ^ 2 * p : Polynomial ℝ).coeff 0 =
      (1 : Polynomial ℝ).coeff 0 := by rw [h]
  rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, Polynomial.coeff_one]
    at hc
  simp at hc

example : Function.Surjective (LADR.Section_3A.backwardShift (F := F)) := by
  intro x
  refine ⟨fun i => if i = 0 then 0 else x (i - 1), ?_⟩
  funext i
  show (if i + 1 = 0 then (0 : F) else x (i + 1 - 1)) = x i
  rw [if_neg (Nat.succ_ne_zero i)]
  simp

example : ¬ Function.Injective (LADR.Section_3A.backwardShift (F := F)) := by
  intro hinj
  let e : ℕ → F := Pi.single (0 : ℕ) (1 : F)
  have hshift : LADR.Section_3A.backwardShift (F := F) e = 0 := by
    funext i
    show e (i + 1) = 0
    show Pi.single (0 : ℕ) (1 : F) (i + 1) = 0
    rw [Pi.single_apply, if_neg (Nat.succ_ne_zero i)]
  have h0 : LADR.Section_3A.backwardShift (F := F) (0 : ℕ → F) = 0 := by
    funext _; rfl
  have heq : LADR.Section_3A.backwardShift (F := F) e =
             LADR.Section_3A.backwardShift (F := F) 0 := by
    rw [hshift, h0]
  have hPi : e = 0 := hinj heq
  have hPi0 : e 0 = (0 : ℕ → F) 0 := congrFun hPi 0
  show False
  have he0 : e 0 = (1 : F) := by
    show e 0 = (1 : F)
    simp [e]
  rw [he0] at hPi0
  exact one_ne_zero hPi0

/-! 3.65 When {lit}`dim V = dim W < ∞`, invertibility, injectivity, and
surjectivity all coincide. We package the equivalences as a single
{name}`List.TFAE`; Axler's 3.65 ({lit}`injective ↔ surjective`) and the two
{lit}`isInvertible ↔ …` statements are then thin corollaries via
{name}`List.TFAE.out`. -/

theorem tfae_isInvertible [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (T : V →ₗ[F] W) :
    [IsInvertible T, Function.Injective T, Function.Surjective T].TFAE := by
  tfae_have 1 → 2 := fun hT => ((isInvertible_iff_bijective T).mp hT).1
  tfae_have 2 → 3 := by
    rw [LADR.Section_3B.injective_iff_ker_eq_bot,
        LADR.Section_3B.surjective_iff_range_eq_top,
        LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank h]
    exact id
  tfae_have 3 → 1 := by
    intro hsurj
    have hinj : Function.Injective T := by
      rw [LADR.Section_3B.injective_iff_ker_eq_bot,
          LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank h,
          ← LADR.Section_3B.surjective_iff_range_eq_top]
      exact hsurj
    exact (isInvertible_iff_bijective T).mpr ⟨hinj, hsurj⟩
  tfae_finish

theorem injective_iff_surjective [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (T : V →ₗ[F] W) :
    Function.Injective T ↔ Function.Surjective T :=
  (tfae_isInvertible h T).out 1 2

theorem isInvertible_iff_injective [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (T : V →ₗ[F] W) :
    IsInvertible T ↔ Function.Injective T :=
  (tfae_isInvertible h T).out 0 1

theorem isInvertible_iff_surjective [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (T : V →ₗ[F] W) :
    IsInvertible T ↔ Function.Surjective T :=
  (tfae_isInvertible h T).out 0 2

/-! 3.67 Example: for every {lit}`q ∈ 𝒫(ℝ)` there exists {lit}`p ∈ 𝒫(ℝ)` with
{lit}`((x² + 5x + 7)·p)'' = q`.

Following Axler: let {lit}`m = deg q` and {lit}`c = x² + 5x + 7`. The map
{lit}`T : 𝒫_m(ℝ) → 𝒫_m(ℝ)`, {lit}`p ↦ (c·p)''`, is well-defined (multiplying
by the degree-2 {lit}`c` then differentiating twice keeps the degree {lit}`≤ m`)
and injective: if {lit}`(c·p)'' = 0` then {lit}`c·p` has degree {lit}`≤ 1`, so
{lit}`p = 0` since otherwise {lit}`deg (c·p) = 2 + deg p ≥ 2`. By 3.65,
injectivity gives surjectivity, so {lit}`q ∈ 𝒫_m(ℝ)` has a preimage. -/

example (q : Polynomial ℝ) :
    ∃ p : Polynomial ℝ,
      ((Polynomial.X ^ 2 + 5 * Polynomial.X + 7) * p).derivative.derivative
        = q := by
  set c : Polynomial ℝ := Polynomial.X ^ 2 + 5 * Polynomial.X + 7 with hc
  have hc2 : c.natDegree = 2 := by rw [hc]; compute_degree!
  have hc0 : c ≠ 0 := by intro h; rw [h] at hc2; simp at hc2
  set m := q.natDegree with hm
  -- {lit}`L p = (c·p)''` as a linear map on all of {lit}`𝒫(ℝ)`.
  set L : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
    Polynomial.derivative ∘ₗ Polynomial.derivative ∘ₗ LinearMap.mulLeft ℝ c
    with hL_def
  have hL : ∀ p, L p = (c * p).derivative.derivative := by
    intro p; simp [hL_def, LinearMap.mulLeft_apply]
  -- {lit}`L` maps {lit}`𝒫_m = degreeLT ℝ (m+1)` into itself.
  have hmaps : ∀ p ∈ Polynomial.degreeLT ℝ (m + 1),
      L p ∈ Polynomial.degreeLT ℝ (m + 1) := by
    intro p hp
    rw [Polynomial.mem_degreeLT] at hp ⊢
    rw [hL]
    have hpd : p.natDegree ≤ m := by
      by_cases hp0 : p = 0
      · simp [hp0]
      · have := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp; omega
    have hmul : (c * p).natDegree ≤ 2 + p.natDegree :=
      le_trans Polynomial.natDegree_mul_le (by rw [hc2])
    have hd1 : (c * p).derivative.natDegree ≤ (c * p).natDegree - 1 :=
      Polynomial.natDegree_derivative_le _
    have hd2 : (c * p).derivative.derivative.natDegree ≤
        (c * p).derivative.natDegree - 1 := Polynomial.natDegree_derivative_le _
    have hfin : (c * p).derivative.derivative.natDegree ≤ m := by omega
    calc (c * p).derivative.derivative.degree
        ≤ ↑(c * p).derivative.derivative.natDegree := Polynomial.degree_le_natDegree
      _ ≤ (↑m : WithBot ℕ) := by exact_mod_cast hfin
      _ < ↑(m + 1) := by exact_mod_cast Nat.lt_succ_self m
  -- The restricted operator {lit}`T : 𝒫_m → 𝒫_m`.
  set T := L.restrict hmaps with hT_def
  have hT_apply : ∀ z : Polynomial.degreeLT ℝ (m + 1),
      (T z : Polynomial ℝ) = (c * (z : Polynomial ℝ)).derivative.derivative := by
    intro z; rw [hT_def, LinearMap.restrict_apply]; exact hL _
  -- {lit}`T` is injective, hence (3.65) surjective.
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz0 : (c * (z : Polynomial ℝ)).derivative.derivative = 0 := by
      have h := Subtype.ext_iff.mp hz; rw [hT_apply] at h; simpa using h
    apply Subtype.ext
    show (z : Polynomial ℝ) = 0
    by_contra hzz
    have hgnd : (c * (z : Polynomial ℝ)).natDegree = 2 + (z : Polynomial ℝ).natDegree := by
      rw [Polynomial.natDegree_mul hc0 hzz, hc2]
    have hnd' : (c * (z : Polynomial ℝ)).derivative.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_derivative_eq_zero hz0
    have h1 : (c * (z : Polynomial ℝ)).derivative.degree =
        ↑((c * (z : Polynomial ℝ)).natDegree - 1) :=
      Polynomial.degree_derivative_eq _ (by omega)
    have h2 : (c * (z : Polynomial ℝ)).derivative.degree ≤
        ↑(c * (z : Polynomial ℝ)).derivative.natDegree := Polynomial.degree_le_natDegree
    rw [hnd', h1] at h2
    have h3 : (c * (z : Polynomial ℝ)).natDegree - 1 ≤ 0 := by exact_mod_cast h2
    omega
  have hTsurj : Function.Surjective T := (injective_iff_surjective rfl T).mp hTinj
  -- {lit}`q ∈ 𝒫_m`, so it has a preimage {lit}`p` with {lit}`(c·p)'' = q`.
  have hqS : q ∈ Polynomial.degreeLT ℝ (m + 1) := by
    rw [Polynomial.mem_degreeLT]
    calc q.degree ≤ (↑m : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ < ↑(m + 1) := by exact_mod_cast Nat.lt_succ_self m
  obtain ⟨z, hz⟩ := hTsurj ⟨q, hqS⟩
  refine ⟨(z : Polynomial ℝ), ?_⟩
  have h := Subtype.ext_iff.mp hz
  rw [hT_apply] at h
  simpa using h

/-! 3.68 {lit}`ST = I ⟺ TS = I` (on vector spaces of the same dimension) -/

theorem mul_eq_id_iff_mul_eq_id [Finite F V] [Finite F W]
    (h : finrank F V = finrank F W) (S : W →ₗ[F] V) (T : V →ₗ[F] W) :
    S ∘ₗ T = LinearMap.id ↔ T ∘ₗ S = LinearMap.id := by
  constructor
  · intro hST
    -- T is injective: if Tv = 0 then v = (ST)v = S(Tv) = S 0 = 0
    have hTinj : Function.Injective T := by
      intro u v huv
      have h₁ : S (T u) = u := LinearMap.congr_fun hST u
      have h₂ : S (T v) = v := LinearMap.congr_fun hST v
      have : S (T u) = S (T v) := congrArg S huv
      rw [h₁, h₂] at this
      exact this
    have hTinv : IsInvertible T :=
      (isInvertible_iff_injective h T).mpr hTinj
    have : S = hTinv.inv := by
      have hSeq : S ∘ₗ T = hTinv.inv ∘ₗ T := by rw [hST, hTinv.inv_comp]
      have : (S ∘ₗ T) ∘ₗ hTinv.inv = (hTinv.inv ∘ₗ T) ∘ₗ hTinv.inv := by
        rw [hSeq]
      simp only [show (S ∘ₗ T) ∘ₗ hTinv.inv = S ∘ₗ (T ∘ₗ hTinv.inv) from rfl,
        show (hTinv.inv ∘ₗ T) ∘ₗ hTinv.inv =
          hTinv.inv ∘ₗ (T ∘ₗ hTinv.inv) from rfl,
        hTinv.comp_inv] at this
      have h1 : S ∘ₗ (LinearMap.id : W →ₗ[F] W) = S := by ext; rfl
      have h2 : hTinv.inv ∘ₗ (LinearMap.id : W →ₗ[F] W) = hTinv.inv := by
        ext; rfl
      rw [h1, h2] at this; exact this
    rw [this, hTinv.comp_inv]
  · intro hTS
    have h' : finrank F W = finrank F V := h.symm
    -- by the forward direction with roles swapped
    have hT : T ∘ₗ S = LinearMap.id := hTS
    -- mirror argument
    have hSinj : Function.Injective S := by
      intro u v huv
      have h₁ : T (S u) = u := LinearMap.congr_fun hTS u
      have h₂ : T (S v) = v := LinearMap.congr_fun hTS v
      have : T (S u) = T (S v) := congrArg T huv
      rw [h₁, h₂] at this
      exact this
    have hSinv : IsInvertible S :=
      (isInvertible_iff_injective h' S).mpr hSinj
    have : T = hSinv.inv := by
      have hTeq : T ∘ₗ S = hSinv.inv ∘ₗ S := by rw [hTS, hSinv.inv_comp]
      have : (T ∘ₗ S) ∘ₗ hSinv.inv = (hSinv.inv ∘ₗ S) ∘ₗ hSinv.inv := by
        rw [hTeq]
      simp only [show (T ∘ₗ S) ∘ₗ hSinv.inv = T ∘ₗ (S ∘ₗ hSinv.inv) from rfl,
        show (hSinv.inv ∘ₗ S) ∘ₗ hSinv.inv =
          hSinv.inv ∘ₗ (S ∘ₗ hSinv.inv) from rfl,
        hSinv.comp_inv] at this
      have h1 : T ∘ₗ (LinearMap.id : V →ₗ[F] V) = T := by ext; rfl
      have h2 : hSinv.inv ∘ₗ (LinearMap.id : V →ₗ[F] V) = hSinv.inv := by
        ext; rfl
      rw [h1, h2] at this; exact this
    rw [this, hSinv.comp_inv]

/-! 3.69 Definition: isomorphism, isomorphic

An *isomorphism* is an invertible linear map; in mathlib this is exactly
{name}`LinearEquiv` (denoted {lit}`V ≃ₗ[F] W`). Two vector spaces are
*isomorphic* if there is an isomorphism between them, which we package as the
{lit}`Prop` below. -/

/-- {lit}`V` and {lit}`W` are *isomorphic*: there exists a linear isomorphism
between them. -/
def IsIsomorphic (F V W : Type*) [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] : Prop :=
  Nonempty (V ≃ₗ[F] W)

/-! 3.70 Dimension shows whether vector spaces are isomorphic -/

@[avoiding FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq]
theorem isomorphic_iff_finrank_eq [Finite F V] [Finite F W] :
    IsIsomorphic F V W ↔ finrank F V = finrank F W := by
  constructor
  · rintro ⟨E⟩
    exact E.finrank_eq
  · intro h
    obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
    obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
    have hn : n = finrank F V :=
      LADR.Section_2C.isBasis_card_eq_finrank v hv
    have hm : m = finrank F W :=
      LADR.Section_2C.isBasis_card_eq_finrank w hw
    have hnm : n = m := by omega
    subst hnm
    obtain ⟨T, hT, _⟩ := LADR.Section_3A.linearMap_lemma v hv w
    have hTbij : Function.Bijective T := by
      refine ⟨?_, ?_⟩
      · rw [LADR.Section_3B.injective_iff_ker_eq_bot, Submodule.eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        have hx_in : x ∈ Submodule.span F (Set.range v) := by
          rw [(hv.2 : _ = ⊤)]; exact Submodule.mem_top
        rw [Submodule.mem_span_range_iff_exists_fun] at hx_in
        obtain ⟨a, ha⟩ := hx_in
        rw [← ha] at hx
        rw [map_sum] at hx
        have hTa : ∑ k, a k • w k = 0 := by
          rw [← hx]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [LinearMap.map_smul, hT]
        have ha_zero : a = 0 := by
          funext i
          exact Fintype.linearIndependent_iff.mp hw.1 a hTa i
        rw [← ha, ha_zero]
        simp
      · intro y
        have hy_in : y ∈ Submodule.span F (Set.range w) := by
          rw [(hw.2 : _ = ⊤)]; exact Submodule.mem_top
        rw [Submodule.mem_span_range_iff_exists_fun] at hy_in
        obtain ⟨a, ha⟩ := hy_in
        refine ⟨∑ k, a k • v k, ?_⟩
        rw [map_sum, ← ha]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [LinearMap.map_smul, hT]
    exact ⟨LinearEquiv.ofBijective T hTbij⟩

/-! 3.71 {lit}`ℒ(V, W)` and {lit}`F^{m,n}` are isomorphic.

Following Axler, we exhibit the isomorphism as the matrix map {lit}`ℳ = matrixOf`
itself, checking the three things the book checks: it is (1) linear, (2)
injective, and (3) surjective. (mathlib would hand us the bundled equiv directly
as {name}`LinearMap.toMatrix`, but here we only borrow its underlying *function*
{name}`matrixOf` and rebuild the equivalence from the bijection.) -/

/-- (1) {lit}`ℳ` as a linear map. Additivity (3.35) and homogeneity (3.38) follow
from {name}`matrixOf_apply` and linearity of the coordinate map. -/
noncomputable def matrixOfₗ {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w) :
    (V →ₗ[F] W) →ₗ[F] Matrix (Fin m) (Fin n) F where
  toFun := matrixOf hv hw
  map_add' S T := by
    ext j k
    simp only [matrixOf_apply, LinearMap.add_apply, map_add, Matrix.add_apply,
      Finsupp.add_apply]
  map_smul' a T := by
    ext j k
    simp only [matrixOf_apply, LinearMap.smul_apply, map_smul, Matrix.smul_apply,
      RingHom.id_apply, Finsupp.smul_apply, smul_eq_mul]

@[simp] theorem matrixOfₗ_apply {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w) (T : V →ₗ[F] W) :
    matrixOfₗ hv hw T = matrixOf hv hw T := rfl

/-- (2) {lit}`ℳ` is injective: if every column of {lit}`ℳ(T)` is zero, then
{lit}`T v_k = 0` for each basis vector (3.76), so {lit}`T = 0`. -/
theorem matrixOfₗ_injective {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w) :
    Function.Injective (matrixOfₗ hv hw) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro T hT
  rw [matrixOfₗ_apply] at hT
  refine hv.toModuleBasis.ext (fun k => ?_)
  rw [LinearMap.zero_apply, IsBasis.toModuleBasis_apply, matrixOf_spec hv hw T k, hT]
  simp

/-- (3) {lit}`ℳ` is surjective: for a matrix {lit}`A`, the linear map sending
{lit}`v_k ↦ ∑ⱼ A_{jk} w_j` (3.4) has matrix {lit}`A`. -/
theorem matrixOfₗ_surjective {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w) :
    Function.Surjective (matrixOfₗ hv hw) := by
  intro A
  obtain ⟨T, hT, _⟩ :=
    LADR.Section_3A.linearMap_lemma v hv (fun k => ∑ i, A i k • w i)
  refine ⟨T, ?_⟩
  rw [matrixOfₗ_apply]
  ext j k
  rw [matrixOf_apply, hT k]
  -- {lit}`ℳ(T)_{jk} = b_W.repr (∑ᵢ A_{ik} w_i) j = A_{jk}`.
  have hrepr : hw.toModuleBasis.repr (∑ i, A i k • w i)
      = ∑ i, A i k • Finsupp.single i (1 : F) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show hw.toModuleBasis.repr (A i k • w i)
        = A i k • hw.toModuleBasis.repr (w i) from hw.toModuleBasis.repr.map_smul _ _,
      show w i = hw.toModuleBasis i from (IsBasis.toModuleBasis_apply hw i).symm,
      hw.toModuleBasis.repr_self]
  rw [hrepr, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single j]
  · rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply,
      if_pos rfl, mul_one]
  · intro i _ hij
    rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply,
      if_neg hij, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The isomorphism {lit}`ℒ(V, W) ≅ F^{m,n}`: a bijective linear map is an
isomorphism (3.69). -/
noncomputable def matrixOfEquiv {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w) :
    (V →ₗ[F] W) ≃ₗ[F] Matrix (Fin m) (Fin n) F :=
  LinearEquiv.ofBijective (matrixOfₗ hv hw)
    ⟨matrixOfₗ_injective hv hw, matrixOfₗ_surjective hv hw⟩

/-! 3.72 {lit}`dim ℒ(V, W) = (dim V)(dim W)` -/

@[avoiding Module.finrank_linearMap]
theorem finrank_linearMap [Finite F V] [Finite F W] :
    finrank F (V →ₗ[F] W) = finrank F V * finrank F W := by
  obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
  obtain ⟨m, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
  have hn : n = finrank F V :=
    LADR.Section_2C.isBasis_card_eq_finrank v hv
  have hm : m = finrank F W :=
    LADR.Section_2C.isBasis_card_eq_finrank w hw
  have h := (matrixOfEquiv hv hw).finrank_eq
  rw [LADR.Section_3C.finrank_matrix] at h
  rw [h, hn, hm, mul_comm]

/-! 3.73 Definition: matrix of a vector {lit}`ℳ(v)` -/

/-- The column vector of coordinates of {lit}`x ∈ V` in basis {lit}`v`. -/
noncomputable def vectorMatrixOf {n : ℕ}
    {v : Fin n → V} (hv : IsBasis F v) (x : V) :
    Matrix (Fin n) (Fin 1) F :=
  fun i _ => hv.toModuleBasis.repr x i

/-! 3.74 Example: matrix of a vector — for {lit}`x ∈ Fⁿ` with the standard
basis, {lit}`ℳ(x)` is the column vector of components.

The proof is more awkward than Axler's because our basis is built through
{name}`LADR.Section_2B.IsBasis.toModuleBasis` rather than mathlib's
{name}`Pi.basisFun`, so we have to compute {lit}`b.repr x` from scratch by
expressing {lit}`x` in the basis and applying {lit}`b.repr` to both sides. -/

example {n : ℕ} (x : Fin n → F) :
    vectorMatrixOf (F := F) (V := Fin n → F)
      (LADR.Section_2B.isBasis_stdBasis n) x = fun i _ => x i := by
  classical
  ext i _
  show (LADR.Section_2B.isBasis_stdBasis (F := F) n).toModuleBasis.repr x i =
    x i
  set hu : IsBasis F (fun k : Fin n => (Pi.single k 1 : Fin n → F)) :=
    LADR.Section_2B.isBasis_stdBasis n with hu_def
  set b := hu.toModuleBasis with b_def
  have hb_apply : ∀ k, b k = Pi.single k (1 : F) :=
    IsBasis.toModuleBasis_apply hu
  -- Express x in the standard basis: x = ∑ k, x k • Pi.single k 1.
  have hxsum_b : x = ∑ k, x k • b k := by
    funext j
    simp_rw [hb_apply]
    rw [Finset.sum_apply]
    simp_rw [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, mul_one]
    · intros k _ hkj; rw [Pi.single_eq_of_ne (Ne.symm hkj), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  -- Apply b.repr to both sides, using b.repr_self.
  have hreprx : b.repr x = ∑ k, x k • Finsupp.single k (1 : F) := by
    conv_lhs => rw [hxsum_b]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show b.repr (x k • b k) = x k • b.repr (b k) from
      b.repr.map_smul _ _, b.repr_self]
  rw [hreprx]
  -- Evaluate the Finsupp sum at index i.
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        Finsupp.single_apply, if_pos rfl, mul_one]
  · intros k _ hki
    rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        Finsupp.single_apply, if_neg hki, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-! Axler's 3.74 example proper: the matrix of the polynomial
{lit}`2 - 7x + 5x³ + x⁴ ∈ 𝒫₄(ℝ)`. In the monomial basis {lit}`1, x, x², x³, x⁴`
its coordinate column {lit}`ℳ(p)` is {lit}`(2, -7, 0, 5, 1)` — by 3.73 the
entries are just the coefficients. -/

example :
    vectorMatrixOf (LADR.Section_2B.isBasis_polyMono (F := ℝ) 5)
      ⟨2 - 7 * Polynomial.X + 5 * Polynomial.X ^ 3 + Polynomial.X ^ 4,
        by rw [Polynomial.mem_degreeLT]; compute_degree!⟩
      = !![2; -7; 0; 5; 1] := by
  ext i j
  show (LADR.Section_2B.isBasis_polyMono (F := ℝ) 5).toModuleBasis.repr _ i = _
  rw [LADR.Section_2B.isBasis_polyMono_repr]
  fin_cases i <;>
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_X]

/-! 3.75 Column {lit}`k` of {lit}`ℳ(T)` equals {lit}`ℳ(T v_k)` -/

theorem matrixOf_column_eq_vectorMatrixOf {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) (k : Fin n) :
    column (matrixOf hv hw T) k = vectorMatrixOf hw (T (v k)) := by
  ext j i
  show matrixOf hv hw T j k = hw.toModuleBasis.repr (T (v k)) j
  rw [matrixOf_apply]

/-! 3.76 Linear maps act like matrix multiplication -/

theorem matrixOf_apply_vectorMatrixOf {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) (x : V) :
    vectorMatrixOf hw (T x) =
      matrixOf hv hw T * vectorMatrixOf hv x := by
  ext j k
  show hw.toModuleBasis.repr (T x) j =
    ∑ r, matrixOf hv hw T j r * hv.toModuleBasis.repr x r
  -- Expand {lit}`x = ∑ r b_V.repr(x) r • v_r`, push T through.
  have hx : x = ∑ r, hv.toModuleBasis.repr x r • v r := by
    have hb := hv.toModuleBasis.sum_repr x
    conv_lhs => rw [← hb]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [IsBasis.toModuleBasis_apply]
  have hTx : T x = ∑ r, hv.toModuleBasis.repr x r • T (v r) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [LinearMap.map_smul]
  rw [hTx, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  -- LHS at index j: {lit}`b_W.repr (a_r • T v_r) j = a_r * b_W.repr (T v_r) j`.
  rw [show hw.toModuleBasis.repr ((hv.toModuleBasis.repr x r) • T (v r)) =
      (hv.toModuleBasis.repr x r) • hw.toModuleBasis.repr (T (v r)) from
      hw.toModuleBasis.repr.map_smul _ _]
  rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, matrixOf_apply, mul_comm]

/-! 3.78 Dimension of {lit}`range T` equals column rank of {lit}`ℳ(T)` -/

theorem finrank_range_eq_columnRank_matrixOf [Finite F V] [Finite F W] {m n : ℕ}
    {v : Fin n → V} {w : Fin m → W}
    (hv : IsBasis F v) (hw : IsBasis F w)
    (T : V →ₗ[F] W) :
    finrank F (LinearMap.range T) = columnRank (matrixOf hv hw T) := by
  classical
  -- The iso {lit}`ψ : W ≃ₗ Fin m → F` via basis {lit}`w`, composed with the
  -- trivial iso to {lit}`Matrix (Fin m) (Fin 1) F`.
  let ψ : W ≃ₗ[F] (Fin m → F) := hw.toModuleBasis.equivFun
  let φ : (Fin m → F) ≃ₗ[F] Matrix (Fin m) (Fin 1) F :=
    { toFun := fun v j _ => v j
      invFun := fun M j => M j 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => by
        ext j i; obtain rfl : i = 0 := Subsingleton.elim _ _; rfl }
  let η : W ≃ₗ[F] Matrix (Fin m) (Fin 1) F := ψ.trans φ
  -- {lit}`range T = span (range (T ∘ v))` (3B.10).
  have hrange : LinearMap.range T =
      Submodule.span F (Set.range (fun k => T (v k))) := by
    have hv2 : Submodule.span F (Set.range v) = ⊤ := hv.2
    conv_lhs => rw [LinearMap.range_eq_map, ← hv2]
    rw [Submodule.map_span]
    congr 1
    exact (Set.range_comp T v).symm
  rw [hrange]
  -- Apply {lit}`η`: finrank is preserved.
  have hη_eq :
      finrank F ↥(Submodule.span F (Set.range (fun k => T (v k)))) =
      finrank F ↥(Submodule.map η.toLinearMap
        (Submodule.span F (Set.range (fun k => T (v k))))) :=
    (Submodule.equivMapOfInjective η.toLinearMap η.injective _).finrank_eq
  rw [hη_eq, Submodule.map_span]
  -- Identify the resulting set of images with the set of columns of ℳ(T).
  have hsetrange :
      η.toLinearMap '' Set.range (fun k => T (v k)) =
        Set.range (column (matrixOf hv hw T)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨k, ?_⟩
      ext j i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      change column (matrixOf hv hw T) k j 0 = ψ (T (v k)) j
      change matrixOf hv hw T j k = ψ (T (v k)) j
      rw [matrixOf_apply]; rfl
    · rintro ⟨k, rfl⟩
      refine ⟨T (v k), ⟨k, rfl⟩, ?_⟩
      ext j i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      change ψ (T (v k)) j = column (matrixOf hv hw T) k j 0
      change ψ (T (v k)) j = matrixOf hv hw T j k
      rw [matrixOf_apply]; rfl
  rw [hsetrange]
  rfl

/-! 3.79 Definition: identity matrix.
mathlib provides this as {lit}`1 : Matrix (Fin n) (Fin n) F`. -/

example (n : ℕ) : Matrix (Fin n) (Fin n) F := 1

example (n : ℕ) (j k : Fin n) :
    (1 : Matrix (Fin n) (Fin n) F) j k = if j = k then 1 else 0 :=
  Matrix.one_apply

/-! 3.80 Definition: invertible matrix.
A square matrix {lit}`A` is invertible if there exists {lit}`B` with
{lit}`A * B = 1 ∧ B * A = 1`. In mathlib, this is {name}`IsUnit`. -/

example (n : ℕ) (A : Matrix (Fin n) (Fin n) F) : Prop := IsUnit A

/-! When {lit}`A` is invertible we write {lit}`A⁻¹` for its inverse (mathlib's
{name}`Matrix.inv`, the nonsingular inverse). For a unit it is a genuine
two-sided inverse: {lit}`A * A⁻¹ = 1` and {lit}`A⁻¹ * A = 1`. -/

example {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (h : IsUnit A) :
    A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 := by
  rw [Matrix.isUnit_iff_isUnit_det] at h
  exact ⟨Matrix.mul_nonsing_inv A h, Matrix.nonsing_inv_mul A h⟩

/-- The inverse of an invertible matrix is unique: any two two-sided inverses
of {lit}`A` are equal. (Hence the notation {lit}`A⁻¹` is unambiguous.) -/
theorem matrix_inv_unique {n : ℕ} (A B C : Matrix (Fin n) (Fin n) F)
    (hB : A * B = 1 ∧ B * A = 1) (hC : A * C = 1 ∧ C * A = 1) : B = C :=
  calc B = B * 1 := (mul_one B).symm
    _ = B * (A * C) := by rw [hC.1]
    _ = (B * A) * C := (mul_assoc B A C).symm
    _ = 1 * C := by rw [hB.2]
    _ = C := one_mul C

/-- {lit}`(A⁻¹)⁻¹ = A` for an invertible matrix. -/
theorem matrix_inv_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (h : IsUnit A) :
    A⁻¹⁻¹ = A :=
  Matrix.nonsing_inv_nonsing_inv A (Matrix.isUnit_iff_isUnit_det A |>.mp h)

/-- {lit}`(AC)⁻¹ = C⁻¹ A⁻¹`. -/
theorem matrix_mul_inv_rev {n : ℕ} (A C : Matrix (Fin n) (Fin n) F) :
    (A * C)⁻¹ = C⁻¹ * A⁻¹ := Matrix.mul_inv_rev A C

/-! 3.81 Matrix of product of linear maps (re-statement of 3.43). -/

example {p m n : ℕ}
    {u : Fin p → U} {v : Fin n → V} {w : Fin m → W}
    (hu : IsBasis F u) (hv : IsBasis F v) (hw : IsBasis F w)
    (S : V →ₗ[F] W) (T : U →ₗ[F] V) :
    matrixOf hu hw (S ∘ₗ T) = matrixOf hv hw S * matrixOf hu hv T :=
  matrixOf_comp hu hv hw S T

/-! 3.82 The matrices {lit}`ℳ(I, u, v)` and {lit}`ℳ(I, v, u)` are mutual
inverses. -/

/-- Helper: the matrix of {lit}`LinearMap.id` with respect to a single
basis is the identity matrix. -/
theorem matrixOf_id_self {n : ℕ} {v : Fin n → V} (hv : IsBasis F v) :
    matrixOf hv hv LinearMap.id = 1 := by
  ext j k
  rw [matrixOf_apply]
  show hv.toModuleBasis.repr ((LinearMap.id : V →ₗ[F] V) (v k)) j =
    (1 : Matrix (Fin n) (Fin n) F) j k
  rw [show ((LinearMap.id : V →ₗ[F] V) (v k)) = v k from rfl]
  rw [show (v k : V) = hv.toModuleBasis k from
      (IsBasis.toModuleBasis_apply hv k).symm]
  rw [Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · rw [if_neg hjk, if_neg (fun heq => hjk heq.symm)]

theorem matrixOf_id_mul_matrixOf_id {n : ℕ}
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v) :
    matrixOf hv hu LinearMap.id * matrixOf hu hv LinearMap.id = 1 := by
  -- By 3.43 applied to {lit}`I ∘ I` going {lit}`u → v → u`.
  have h := matrixOf_comp hu hv hu LinearMap.id LinearMap.id
  have hid_comp : (LinearMap.id : V →ₗ[F] V) ∘ₗ LinearMap.id = LinearMap.id := by
    ext; rfl
  rw [hid_comp, matrixOf_id_self hu] at h
  exact h.symm

/-! 3.83 Example: matrix of the identity operator on {lit}`ℝ²` with respect to
two bases.

For {lit}`u = (4,2), (5,3)` and the standard basis {lit}`v = (1,0), (0,1)`, since
{lit}`I(4,2) = 4(1,0) + 2(0,1)` and {lit}`I(5,3) = 5(1,0) + 3(0,1)`, the {lit}`k`th
column of {lit}`ℳ(I, u, v)` lists the coordinates of {lit}`u_k` in {lit}`v`:
{lit}`ℳ(I, u, v) = [[4,5],[2,3]]`. By 3.82 its inverse is
{lit}`ℳ(I, v, u) = [[3/2, -5/2],[-1, 2]]`. -/

/-- The list {lit}`(4,2), (5,3)` is a basis of {lit}`ℝ²`: the determinant
{lit}`4·3 - 2·5 = 2` is nonzero, so the {lit}`2B.2` criterion applies. -/
theorem isBasis_4253 :
    IsBasis ℝ (![![4, 2], ![5, 3]] : Fin 2 → Fin 2 → ℝ) :=
  LADR.Section_2B.isBasis_pair (by norm_num)

/-- {lit}`ℳ(I, u, v) = [[4,5],[2,3]]`: the {lit}`k`th column lists {lit}`u_k`'s
coordinates in the standard basis. -/
theorem matrixOf_id_4253_std :
    matrixOf isBasis_4253 (LADR.Section_2B.isBasis_stdBasis 2) LinearMap.id
      = !![4, 5; 2, 3] := by
  ext j k
  rw [matrixOf_apply, LinearMap.id_apply, LADR.Section_2B.isBasis_stdBasis_repr]
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The matrix inverse of {lit}`[[4,5],[2,3]]` is {lit}`[[3/2,-5/2],[-1,2]]`. -/
theorem inv_4253 :
    (!![4, 5; 2, 3] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![3/2, -5/2; -1, 2] := by
  apply Matrix.inv_eq_left_inv
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> norm_num

/-- {lit}`ℳ(I, v, u)` two ways. By 3.82 the basis-swapped identity matrix is
the inverse of {lit}`ℳ(I, u, v)`; as a matrix that inverse is
{lit}`[[3/2,-5/2],[-1,2]]`. -/
theorem matrixOf_id_std_4253 :
    matrixOf (LADR.Section_2B.isBasis_stdBasis 2) isBasis_4253 LinearMap.id
      = (matrixOf isBasis_4253 (LADR.Section_2B.isBasis_stdBasis 2) LinearMap.id)⁻¹
    ∧ matrixOf (LADR.Section_2B.isBasis_stdBasis 2) isBasis_4253 LinearMap.id
      = !![3/2, -5/2; -1, 2] := by
  -- "swap basis = matrix inverse" — uniqueness of inverses (3.82, 3.80).
  have hswap : matrixOf (LADR.Section_2B.isBasis_stdBasis 2) isBasis_4253 LinearMap.id
      = (matrixOf isBasis_4253 (LADR.Section_2B.isBasis_stdBasis 2) LinearMap.id)⁻¹ :=
    (Matrix.inv_eq_left_inv
      (matrixOf_id_mul_matrixOf_id isBasis_4253 (LADR.Section_2B.isBasis_stdBasis 2))).symm
  exact ⟨hswap, by rw [hswap, matrixOf_id_4253_std, inv_4253]⟩

/-! 3.84 Change-of-basis formula -/

theorem change_of_basis {n : ℕ}
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v) (T : V →ₗ[F] V)
    (A B C : Matrix (Fin n) (Fin n) F)
    (hA : A = matrixOf hu hu T)
    (hB : B = matrixOf hv hv T)
    (hC : C = matrixOf hu hv LinearMap.id) :
    A = C⁻¹ * B * C := by
  subst hA hB hC
  -- {lit}`C⁻¹ = ℳ(I, v, u)` by 3.82 (uniqueness of the matrix inverse).
  rw [Matrix.inv_eq_left_inv (matrixOf_id_mul_matrixOf_id hu hv)]
  -- Two applications of 3.43: ℳ(T) = ℳ(I ∘ T) and ℳ(T) = ℳ(T ∘ I).
  have h1 : matrixOf hu hv T =
      matrixOf hv hv T * matrixOf hu hv LinearMap.id := by
    have h := matrixOf_comp hu hv hv T LinearMap.id
    have hcomp : T ∘ₗ LinearMap.id = T := by ext; rfl
    rw [hcomp] at h
    exact h
  have h2 : matrixOf hu hu T =
      matrixOf hv hu LinearMap.id * matrixOf hu hv T := by
    have h := matrixOf_comp hu hv hu LinearMap.id T
    have hcomp : (LinearMap.id : V →ₗ[F] V) ∘ₗ T = T := by ext; rfl
    rw [hcomp] at h
    exact h
  rw [h2, h1, mul_assoc]

/-! 3.86 {lit}`ℳ(T⁻¹) = ℳ(T)⁻¹`: the matrix of the inverse is the inverse of
the matrix (with respect to a single basis). Axler leaves the proof as an
exercise: by 3.43, {lit}`ℳ(T⁻¹) ℳ(T) = ℳ(T⁻¹ T) = ℳ(I) = 1`, so {lit}`ℳ(T⁻¹)`
is the (unique) inverse of {lit}`ℳ(T)`. -/

theorem matrixOf_inv {n : ℕ}
    {v : Fin n → V} (hv : IsBasis F v) (T : V →ₗ[F] V)
    (hT : IsInvertible T) :
    matrixOf hv hv hT.inv = (matrixOf hv hv T)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← matrixOf_comp, hT.inv_comp, matrixOf_id_self]

/-! # Exercises -/

/-- 3D.1 {lit}`(T⁻¹)⁻¹ = T` -/
theorem exercise_3D_1 (T : V →ₗ[F] W) (hT : IsInvertible T) :
    ∃ hT' : IsInvertible hT.inv, hT'.inv = T := by
  -- use T
  refine ⟨⟨T, hT.comp_inv, hT.inv_comp⟩, ?_⟩
  -- both `(T⁻¹)⁻¹` and `T` are two-sided inverses of `T⁻¹`, so 3.60 applies
  exact inv_unique hT.inv
    ⟨IsInvertible.inv_comp _, IsInvertible.comp_inv _⟩ ⟨hT.comp_inv, hT.inv_comp⟩

/-- 3D.2 {lit}`S ∘ T` is invertible and {lit}`(ST)⁻¹ = T⁻¹ S⁻¹`. -/
theorem exercise_3D_2 (T : U →ₗ[F] V) (S : V →ₗ[F] W)
    (hT : IsInvertible T) (hS : IsInvertible S) :
    ∃ h : IsInvertible (S ∘ₗ T), h.inv = hT.inv ∘ₗ hS.inv := by
  -- use the fact that (S ∘ T) ∘ (T⁻¹ ∘ S⁻¹) = id and (T⁻¹ ∘ S⁻¹) ∘ (S ∘ T) = id
  have h1 : (hT.inv ∘ₗ hS.inv) ∘ₗ (S ∘ₗ T) = LinearMap.id := by
    ext u
    have hs := LinearMap.congr_fun hS.inv_comp (T u)
    have ht := LinearMap.congr_fun hT.inv_comp u
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hs ht ⊢
    rw [hs, ht]
  have h2 : (S ∘ₗ T) ∘ₗ (hT.inv ∘ₗ hS.inv) = LinearMap.id := by
    ext w
    have ht := LinearMap.congr_fun hT.comp_inv (hS.inv w)
    have hs := LinearMap.congr_fun hS.comp_inv w
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hs ht ⊢
    rw [ht, hs]
  refine ⟨⟨hT.inv ∘ₗ hS.inv, h1, h2⟩, ?_⟩
  exact inv_unique (S ∘ₗ T)
    ⟨IsInvertible.inv_comp _, IsInvertible.comp_inv _⟩ ⟨h1, h2⟩

/-- 3D.3 The following are equivalent: {lit}`T` is invertible; {lit}`T` maps
every basis of {lit}`V` to a basis; {lit}`T` maps some basis to a basis. -/
theorem exercise_3D_3 [Finite F V] (T : V →ₗ[F] V) :
    [IsInvertible T,
     ∀ {n : ℕ} (v : Fin n → V) (_ : IsBasis F v), IsBasis F (fun k => T (v k)),
     ∃ (n : ℕ) (v : Fin n → V) (_ : IsBasis F v), IsBasis F (fun k => T (v k))].TFAE := by
  -- 1 => 2, by fin.dim, enough to show LI fot Tvi, assume by contra ∑ a_i Tvi = 0,
  -- by lin, T (∑ ai vi) = 0, so contradiction with injectivity of T
  -- 2 => 3 is trivial, since exist at least one basis.
  -- 3 => 1, construct the inverse S, mapping Tvi back to vi.
  tfae_have 1 → 2 := by
    intro hT n v hv
    obtain ⟨hinj, hsurj⟩ := (isInvertible_iff_bijective T).mp hT
    obtain ⟨hli, hspan⟩ := hv
    constructor
    · -- a vanishing combination of the {lit}`T vᵢ` gives {lit}`T (∑ aᵢ vᵢ) = 0`
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hsum : T (∑ j, g j • v j) = T 0 := by
        rw [map_sum, map_zero]
        simpa only [map_smul] using hg
      exact (Fintype.linearIndependent_iff.mp hli) g (hinj hsum) i
    · -- {lit}`T` is onto, so the image of a spanning list still spans
      have hrange : (Set.range fun k => T (v k)) = ⇑T '' Set.range v :=
        Set.range_comp ⇑T v
      show Submodule.span F (Set.range fun k => T (v k)) = ⊤
      rw [hrange, Submodule.span_image,
        show Submodule.span F (Set.range v) = ⊤ from hspan, Submodule.map_top,
        LinearMap.range_eq_top.mpr hsurj]
  tfae_have 2 → 3 := by
    intro h
    obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
    exact ⟨n, v, hv, h v hv⟩
  tfae_have 3 → 1 := by
    rintro ⟨n, v, hv, hTv⟩
    -- 3.4 gives the map {lit}`S` sending the basis {lit}`T vᵢ` back to {lit}`vᵢ`
    obtain ⟨S, hS, -⟩ := LADR.Section_3A.linearMap_lemma' _ hTv v
    refine ⟨S, ?_, ?_⟩
    · -- {lit}`S ∘ T = I`: both sides agree on the basis {lit}`v`
      refine hv.toModuleBasis.ext (fun k => ?_)
      simp only [IsBasis.toModuleBasis_apply, LinearMap.comp_apply,
        LinearMap.id_apply]
      exact hS k
    · -- {lit}`T ∘ S = I`: both sides agree on the basis {lit}`T v`
      refine hTv.toModuleBasis.ext (fun k => ?_)
      simp only [IsBasis.toModuleBasis_apply, LinearMap.comp_apply,
        LinearMap.id_apply]
      rw [hS k]
  tfae_finish

/-- 3D.4 -/
theorem exercise_3D_4 [Finite F V] (hV : 1 < finrank F V) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] V)),
      ∀ T : V →ₗ[F] V, T ∈ U ↔ ¬ IsInvertible T := by
  -- take a basis vi,
  -- consider S v0 = v0, and S vi = 0 for i > 0, S is not invertable, because not inj.
  -- also T v i = vi for i > 0, T v0 = 0, T is not invertible, because not inj.
  -- but S + T = id, which is invertible.
  classical
  rintro ⟨U, hU⟩
  let b := Module.finBasis F V
  let i₀ : Fin (finrank F V) := ⟨0, Nat.zero_lt_of_lt hV⟩
  let i₁ : Fin (finrank F V) := ⟨1, hV⟩
  have hne : i₁ ≠ i₀ := by
    intro hi
    have := congrArg Fin.val hi
    norm_num [i₀, i₁] at this
  let S : V →ₗ[F] V := b.constr F (Pi.single i₀ (b i₀))
  let T : V →ₗ[F] V := b.constr F (fun k => if k = i₀ then 0 else b k)
  have hSapp : ∀ k, S (b k) =
      (Pi.single i₀ (b i₀) : Fin (finrank F V) → V) k := by
    intro k; simp only [S, Module.Basis.constr_basis]
  have hTapp : ∀ k, T (b k) = if k = i₀ then 0 else b k := by
    intro k; simp only [T, Module.Basis.constr_basis]
  have hS₀ : S (b i₁) = 0 := by rw [hSapp, Pi.single_eq_of_ne hne]
  have hT₀ : T (b i₀) = 0 := by rw [hTapp, if_pos rfl]
  have hSni : ¬ IsInvertible S := fun hSi =>
    b.ne_zero i₁ (((isInvertible_iff_bijective S).mp hSi).1
      (by rw [hS₀, map_zero]))
  have hTni : ¬ IsInvertible T := fun hTi =>
    b.ne_zero i₀ (((isInvertible_iff_bijective T).mp hTi).1
      (by rw [hT₀, map_zero]))
  -- but {lit}`S + T = I`, and {lit}`U` is closed under addition
  have hsum : S + T = LinearMap.id := by
    refine b.ext (fun k => ?_)
    rw [LinearMap.add_apply, hSapp, hTapp, LinearMap.id_apply, Pi.single_apply]
    by_cases hk : k = i₀
    · subst hk; simp
    · simp [hk]
  have hmem : S + T ∈ U := U.add_mem ((hU S).mpr hSni) ((hU T).mpr hTni)
  refine ((hU (S + T)).mp hmem) ?_
  rw [hsum]
  exact ⟨LinearMap.id, by ext; rfl, by ext; rfl⟩

/-- 3D.5 -/
theorem exercise_3D_5 [Finite F V] (U : Submodule F V) (S : U →ₗ[F] V) :
    (∃ T : V →ₗ[F] V, IsInvertible T ∧ ∀ u : U, T (u : V) = S u) ↔
      Function.Injective S := by
  -- => assume S u = 0 for some u in U, then T u = S u = 0, but T is invertible,
  -- so u = 0, proving that S is injective.
  -- <= take basis for U, and extend it to basis for V
  -- since V is finite-dimensional and S injective,
  -- S vi, for vi in U, forms a linearly independent set.
  -- extend this set to a another basis for V - wi,
  -- define T vi = S vi for vi in U, and T vi = wi for rest.
  -- by definition, T maps to a basis so it is invertible (use 3d.3)
  -- and by construction T agrees with S on U.
  constructor
  · rintro ⟨T, hT, hTU⟩ u₁ u₂ h₁₂
    have hinj := ((isInvertible_iff_bijective T).mp hT).1
    exact Subtype.ext (hinj (by rw [hTU u₁, hTU u₂, h₁₂]))
  · intro hSinj
    obtain ⟨m, u, hu⟩ := LADR.Section_2B.exists_basis (F := F) (V := U)
    -- the basis of {lit}`U`, viewed in {lit}`V`, is linearly independent …
    have huV : LinearIndependent F (fun k => (u k : V)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg k
      have hz : (∑ i, g i • u i : U) = 0 := by
        have hcoe : ((∑ i, g i • u i : U) : V) = ∑ i, g i • (u i : V) := by
          simp
        exact Submodule.coe_eq_zero.mp (by rw [hcoe]; exact hg)
      exact (Fintype.linearIndependent_iff.mp hu.1) g hz k
    -- … and so is its image under the injective {lit}`S`
    have hSu : LinearIndependent F (fun k => S (u k)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg k
      have hz : (∑ i, g i • u i : U) = 0 := by
        refine hSinj ?_
        rw [map_sum, map_zero]
        simpa only [map_smul] using hg
      exact (Fintype.linearIndependent_iff.mp hu.1) g hz k
    -- extend both lists to bases of {lit}`V`; by 2.35 they have the same length
    obtain ⟨n, v, hmn, hvb, hvpre⟩ := LADR.Section_2B.exists_basis_extending _ huV
    obtain ⟨n', w, hmn', hwb, hwpre⟩ := LADR.Section_2B.exists_basis_extending _ hSu
    have hn : n = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v hvb
    have hn' : n' = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank w hwb
    have hnn : n' = n := by omega
    subst hnn
    have hwpre' : ∀ i : Fin m, w (Fin.castLE hmn i) = S (u i) := hwpre
    -- 3.4: send the basis {lit}`v` to the basis {lit}`w`
    obtain ⟨T, hT, -⟩ := LADR.Section_3A.linearMap_lemma' v hvb w
    have hTbasis : IsBasis F (fun k => T (v k)) := by
      rw [show (fun k => T (v k)) = w from funext hT]
      exact hwb
    have hwitness : ∃ (n : ℕ) (v : Fin n → V) (_ : IsBasis F v),
        IsBasis F (fun k => T (v k)) := ⟨_, v, hvb, hTbasis⟩
    refine ⟨T, ((exercise_3D_3 T).out 2 0).mp hwitness, ?_⟩
    -- {lit}`T` and {lit}`S` agree on a basis of {lit}`U`, hence on all of {lit}`U`
    have hext : T ∘ₗ U.subtype = S := by
      refine hu.toModuleBasis.ext (fun i => ?_)
      simp only [IsBasis.toModuleBasis_apply, LinearMap.comp_apply,
        Submodule.subtype_apply]
      rw [← hvpre i, hT (Fin.castLE hmn i), hwpre' i]
    exact fun x => LinearMap.congr_fun hext x

/-- 3D.6 -/
theorem exercise_3D_6 [Finite F W] (S T : V →ₗ[F] W) :
    LinearMap.ker S = LinearMap.ker T ↔
      ∃ E : W →ₗ[F] W, IsInvertible E ∧ S = E ∘ₗ T := by
  -- => apply 3B.25 both ways: S = E₂ T and T = E₁ S.
  -- on range T these are mutually inverse: E₁ (E₂ (T v)) = E₁ (S v) = T v,
  -- and likewise on range S, so E₂ cuts down to an isomorphism
  -- e : range T → range S. (this replaces "send the basis of range T to the
  -- corresponding basis of range S".)
  -- a complement P of range T and a complement Q of range S have equal
  -- dimension, so pick any isomorphism f : P → Q (3.70) -- that is the
  -- "arbitrary permutation of the rest".
  -- E = e ⊕ f on W = range T ⊕ P = range S ⊕ Q is invertible, being a sum
  -- of isomorphisms, and E (T v) = e (T v) = E₂ (T v) = S v.
  -- <= if S v = 0, then E T v = 0, but E inv, so T v = 0,
  -- if T v = 0, S v = E T v = 0, so ker T = ker S.
  classical
  constructor
  · intro hker
    -- 3B.25 both ways: {lit}`S = E₂ T` and {lit}`T = E₁ S`.
    obtain ⟨E₂, hE₂⟩ := (LADR.Section_3B.exercise_3B_25 T S).mp hker.ge
    obtain ⟨E₁, hE₁⟩ := (LADR.Section_3B.exercise_3B_25 S T).mp hker.le
    have hS : ∀ v, E₂ (T v) = S v := fun v => by rw [hE₂]; rfl
    have hT : ∀ v, E₁ (S v) = T v := fun v => by rw [hE₁]; rfl
    -- On the ranges the two are mutually inverse, so they cut down to an
    -- isomorphism {lit}`range T ≃ range S`.
    have hmap₂ : ∀ x ∈ LinearMap.range T, E₂ x ∈ LinearMap.range S := by
      rintro _ ⟨v, rfl⟩; exact ⟨v, (hS v).symm⟩
    have hmap₁ : ∀ x ∈ LinearMap.range S, E₁ x ∈ LinearMap.range T := by
      rintro _ ⟨v, rfl⟩; exact ⟨v, (hT v).symm⟩
    let e : LinearMap.range T ≃ₗ[F] LinearMap.range S :=
      LinearEquiv.ofLinear (E₂.restrict hmap₂) (E₁.restrict hmap₁)
        (by
          refine LinearMap.ext fun y => Subtype.ext ?_
          obtain ⟨v, hv⟩ := y.2
          show E₂ (E₁ (y : W)) = (y : W)
          rw [← hv, hT v, hS v])
        (by
          refine LinearMap.ext fun x => Subtype.ext ?_
          obtain ⟨v, hv⟩ := x.2
          show E₁ (E₂ (x : W)) = (x : W)
          rw [← hv, hS v, hT v])
    -- Complements of the two ranges then have equal dimension, so {lit}`e`
    -- extends to an isomorphism of all of {lit}`W` (3.70 on the complements).
    obtain ⟨P, hP⟩ := (LinearMap.range T).exists_isCompl
    obtain ⟨Q, hQ⟩ := (LinearMap.range S).exists_isCompl
    have hPQ : finrank F P = finrank F Q := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hP
      have h2 := Submodule.finrank_add_eq_of_isCompl hQ
      have h3 := e.finrank_eq
      omega
    let f : P ≃ₗ[F] Q := (isomorphic_iff_finrank_eq.mpr hPQ).some
    let E : W ≃ₗ[F] W :=
      (Submodule.prodEquivOfIsCompl _ _ hP).symm ≪≫ₗ e.prodCongr f ≪≫ₗ
        Submodule.prodEquivOfIsCompl _ _ hQ
    have hE : ∀ x : LinearMap.range T, E (x : W) = (e x : W) := by
      intro x
      show Submodule.prodEquivOfIsCompl _ _ hQ (e.prodCongr f
        ((Submodule.prodEquivOfIsCompl _ _ hP).symm (x : W))) = _
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
      simp [Submodule.coe_prodEquivOfIsCompl']
    refine ⟨(E : W →ₗ[F] W), LinearEquiv.isInvertible E, ?_⟩
    ext v
    calc S v = E₂ (T v) := (hS v).symm
      _ = ((e ⟨T v, ⟨v, rfl⟩⟩ : LinearMap.range S) : W) := rfl
      _ = E (T v) := (hE ⟨T v, ⟨v, rfl⟩⟩).symm
  · rintro ⟨E, hE, rfl⟩
    have hinj := ((isInvertible_iff_bijective E).mp hE).1
    ext v
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact ⟨fun h => hinj (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-- 3D.7 -/
theorem exercise_3D_7 [Finite F V] (S T : V →ₗ[F] W) :
    LinearMap.range S = LinearMap.range T ↔
      ∃ E : V →ₗ[F] V, IsInvertible E ∧ S = T ∘ₗ E := by
  -- => apply 3B.26: S = T E₂, so E₂ already picks, for each v, a
  -- T-preimage of S v (this replaces "for each wi take a preimage").
  -- take CS a complement of ker S and let CT = E₂ CS.
  -- CT is a complement of ker T: if E₂ y ∈ ker T with y ∈ CS then
  -- S y = T (E₂ y) = 0, so y ∈ ker S ∩ CS = 0; and for any v,
  -- T v ∈ range T = range S equals S y for some y ∈ CS, so v - E₂ y ∈ ker T.
  -- the same argument makes E₂ : CS → CT bijective, call it g.
  -- dim ker S = dim ker T by 3.21, so pick any k : ker S → ker T (3.70).
  -- E = k ⊕ g on V = ker S ⊕ CS = ker T ⊕ CT is the change-of-basis map:
  -- it is invertible, and S (x + y) = S y = T (E₂ y) = T (E (x + y)).
  -- <= if w = S v for some v, w = T E v, then w is in the range of T
  -- if w = T v for some v, w = S E⁻¹ v, then w is in the range of S.
  -- so ranges equal.
  classical
  constructor
  · intro hr
    -- 3B.26 gives {lit}`E₂` with {lit}`S = T E₂`: it already picks the
    -- {lit}`T`-preimages of the {lit}`S`-values.
    obtain ⟨E₂, hE₂⟩ := (LADR.Section_3B.exercise_3B_26 S T).mp hr.le
    have hTE : ∀ v, T (E₂ v) = S v := fun v => by rw [hE₂]; rfl
    obtain ⟨CS, hCS⟩ := (LinearMap.ker S).exists_isCompl
    -- the image of {lit}`CS` under {lit}`E₂` is a complement of {lit}`null T`
    let CT : Submodule F V := Submodule.map E₂ CS
    have hCT : IsCompl (LinearMap.ker T) CT := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hxk hxm
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hxm
        have hSy : S y = 0 := by rw [← hTE y]; exact LinearMap.mem_ker.mp hxk
        rw [Submodule.disjoint_def.mp hCS.disjoint y (LinearMap.mem_ker.mpr hSy) hy,
          map_zero]
      · rw [codisjoint_iff, eq_top_iff]
        intro v _
        -- {lit}`T v ∈ range T = range S`, so {lit}`T v = S y` with {lit}`y ∈ CS`
        obtain ⟨u, hu⟩ : T v ∈ LinearMap.range S := by rw [hr]; exact ⟨v, rfl⟩
        obtain ⟨n, hn, y, hy, rfl⟩ := Submodule.mem_sup.mp
          (show u ∈ LinearMap.ker S ⊔ CS by rw [hCS.codisjoint.eq_top]; trivial)
        have hTy : T (E₂ y) = T v := by
          rw [hTE, ← hu, map_add, LinearMap.mem_ker.mp hn, zero_add]
        refine Submodule.mem_sup.mpr ⟨v - E₂ y, ?_, E₂ y, ⟨y, hy, rfl⟩, by abel⟩
        rw [LinearMap.mem_ker, map_sub, hTy, sub_self]
    -- {lit}`E₂` matches {lit}`CS` with {lit}`CT` bijectively
    have hmapCT : ∀ y ∈ CS, E₂ y ∈ CT := fun y hy => ⟨y, hy, rfl⟩
    let g₀ : CS →ₗ[F] CT := E₂.restrict hmapCT
    have hg₀ : Function.Bijective g₀ := by
      constructor
      · intro y y' hyy'
        have hSy : S (y : V) = S (y' : V) := by
          rw [← hTE (y : V), ← hTE (y' : V)]
          exact congrArg (fun z : CT => T (z : V)) hyy'
        have h0 : (y : V) - (y' : V) = 0 :=
          Submodule.disjoint_def.mp hCS.disjoint _
            (LinearMap.mem_ker.mpr (by rw [map_sub, hSy, sub_self]))
            (CS.sub_mem y.2 y'.2)
        exact Subtype.ext (sub_eq_zero.mp h0)
      · rintro ⟨z, hz⟩
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
        exact ⟨⟨y, hy⟩, rfl⟩
    let g : CS ≃ₗ[F] CT := LinearEquiv.ofBijective g₀ hg₀
    have hg : ∀ y : CS, T ((g y : V)) = S (y : V) := fun y => hTE (y : V)
    -- The kernels have equal dimension by the fundamental theorem (3.21),
    -- so they are isomorphic (3.70).
    have hkr : finrank F (LinearMap.ker S) = finrank F (LinearMap.ker T) := by
      have h1 := LADR.Section_3B.finrank_ker_add_finrank_range S
      have h2 := LADR.Section_3B.finrank_ker_add_finrank_range T
      rw [hr] at h1
      omega
    let k : LinearMap.ker S ≃ₗ[F] LinearMap.ker T :=
      (isomorphic_iff_finrank_eq.mpr hkr).some
    let E : V ≃ₗ[F] V :=
      (Submodule.prodEquivOfIsCompl _ _ hCS).symm ≪≫ₗ k.prodCongr g ≪≫ₗ
        Submodule.prodEquivOfIsCompl _ _ hCT
    have hEapp : ∀ (x : LinearMap.ker S) (y : CS),
        E ((x : V) + (y : V)) = ((k x : V) + (g y : V)) := by
      intro x y
      show Submodule.prodEquivOfIsCompl _ _ hCT (k.prodCongr g
        ((Submodule.prodEquivOfIsCompl _ _ hCS).symm ((x : V) + (y : V)))) = _
      rw [show ((x : V) + (y : V))
            = Submodule.prodEquivOfIsCompl _ _ hCS (x, y) from rfl,
        LinearEquiv.symm_apply_apply]
      rfl
    refine ⟨(E : V →ₗ[F] V), LinearEquiv.isInvertible E, ?_⟩
    ext v
    obtain ⟨⟨x, y⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ hCS).surjective v
    show S ((x : V) + (y : V)) = T (E ((x : V) + (y : V)))
    rw [hEapp, map_add, map_add, hg y, LinearMap.mem_ker.mp x.2,
      LinearMap.mem_ker.mp (k x).2, zero_add]
  · rintro ⟨E, hE, rfl⟩
    have hsurj := ((isInvertible_iff_bijective E).mp hE).2
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]

/-- 3D.8 -/
theorem exercise_3D_8 [Finite F V] [Finite F W] (S T : V →ₗ[F] W) :
    (∃ (E₁ : V →ₗ[F] V) (E₂ : W →ₗ[F] W), IsInvertible E₁ ∧ IsInvertible E₂ ∧
      S = E₂ ∘ₗ T ∘ₗ E₁) ↔
      finrank F (LinearMap.ker S) = finrank F (LinearMap.ker T) := by
  -- => S v = 0 <-> E2 T E1 v = 0 -> T (E1 v) = 0 -> E1 v ∈ ker T -> v ∈ E1⁻¹(ker T)
  -- ker S = E1⁻¹(ker T), so same rank
  -- <= same dim so exist iso between ker S and ker T
  -- then extend this iso to an invertible E1 on V
  -- (pair it with an iso between complements of the two kernels, which have
  -- equal dimension too, so E1 maps ker S onto ker T)
  -- then ker (T E1) = ker S, and 3D.6 supplies the invertible E2 on W
  -- with S = E2 (T E1).
  classical
  constructor
  · rintro ⟨E₁, E₂, hE₁, hE₂, rfl⟩
    obtain ⟨hinj₁, hsurj₁⟩ := (isInvertible_iff_bijective E₁).mp hE₁
    have hinj₂ := ((isInvertible_iff_bijective E₂).mp hE₂).1
    -- {lit}`E₁` carries {lit}`null (E₂ T E₁)` isomorphically onto {lit}`null T`
    have hmapK : ∀ v ∈ LinearMap.ker (E₂ ∘ₗ T ∘ₗ E₁), E₁ v ∈ LinearMap.ker T := by
      intro v hv
      have h0 : E₂ (T (E₁ v)) = 0 := hv
      exact LinearMap.mem_ker.mpr (hinj₂ (by rw [h0, map_zero]))
    have hbij : Function.Bijective (E₁.restrict hmapK) := by
      constructor
      · intro a b hab
        exact Subtype.ext (hinj₁ (congrArg Subtype.val hab))
      · rintro ⟨w, hw⟩
        obtain ⟨v, rfl⟩ := hsurj₁ w
        refine ⟨⟨v, ?_⟩, rfl⟩
        show E₂ (T (E₁ v)) = 0
        rw [LinearMap.mem_ker.mp hw, map_zero]
    exact isomorphic_iff_finrank_eq.mp ⟨LinearEquiv.ofBijective _ hbij⟩
  · intro hk
    -- complements of the two kernels also have equal dimension
    obtain ⟨CS, hCS⟩ := (LinearMap.ker S).exists_isCompl
    obtain ⟨CT, hCT⟩ := (LinearMap.ker T).exists_isCompl
    have hC : finrank F CS = finrank F CT := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hCS
      have h2 := Submodule.finrank_add_eq_of_isCompl hCT
      omega
    let k : LinearMap.ker S ≃ₗ[F] LinearMap.ker T :=
      (isomorphic_iff_finrank_eq.mpr hk).some
    let g : CS ≃ₗ[F] CT := (isomorphic_iff_finrank_eq.mpr hC).some
    let E₁ : V ≃ₗ[F] V :=
      (Submodule.prodEquivOfIsCompl _ _ hCS).symm ≪≫ₗ k.prodCongr g ≪≫ₗ
        Submodule.prodEquivOfIsCompl _ _ hCT
    have hEapp : ∀ (x : LinearMap.ker S) (y : CS),
        E₁ ((x : V) + (y : V)) = ((k x : V) + (g y : V)) := by
      intro x y
      show Submodule.prodEquivOfIsCompl _ _ hCT (k.prodCongr g
        ((Submodule.prodEquivOfIsCompl _ _ hCS).symm ((x : V) + (y : V)))) = _
      rw [show ((x : V) + (y : V))
            = Submodule.prodEquivOfIsCompl _ _ hCS (x, y) from rfl,
        LinearEquiv.symm_apply_apply]
      rfl
    -- so {lit}`T E₁` has the same null space as {lit}`S`
    have hkerEq : LinearMap.ker S = LinearMap.ker (T ∘ₗ (E₁ : V →ₗ[F] V)) := by
      ext v
      obtain ⟨⟨x, y⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl _ _ hCS).surjective v
      show S ((x : V) + (y : V)) = 0 ↔ T (E₁ ((x : V) + (y : V))) = 0
      rw [hEapp, map_add, map_add, LinearMap.mem_ker.mp x.2,
        LinearMap.mem_ker.mp (k x).2, zero_add, zero_add]
      constructor
      · intro h
        have hy : (y : V) = 0 :=
          Submodule.disjoint_def.mp hCS.disjoint _ (LinearMap.mem_ker.mpr h) y.2
        rw [show y = 0 from Subtype.ext hy]
        simp
      · intro h
        have hgy : (g y : V) = 0 :=
          Submodule.disjoint_def.mp hCT.disjoint _ (LinearMap.mem_ker.mpr h) (g y).2
        have hy : y = 0 := by
          have : g y = 0 := Subtype.ext hgy
          simpa using congrArg g.symm this
        rw [hy]
        simp
    -- 3D.6 now supplies the invertible {lit}`E₂` on {lit}`W`
    obtain ⟨E₂, hE₂inv, hE₂⟩ := (exercise_3D_6 S (T ∘ₗ (E₁ : V →ₗ[F] V))).mp hkerEq
    exact ⟨(E₁ : V →ₗ[F] V), E₂, LinearEquiv.isInvertible E₁, hE₂inv, hE₂⟩

/-- 3D.9 -/
theorem exercise_3D_9 [Finite F V] (T : V →ₗ[F] W) (hT : Function.Surjective T) :
    ∃ U : Submodule F V,
      ∃ E : U ≃ₗ[F] W, ∀ u : U, E u = T (u : V) := by
  -- take a basis of W and pull by one preimage to vectors in V
  -- possible since T is surjective
  -- now vi are LI, and their span is submodule U of eq dim as W
  -- T on U is surj thus iso.
  classical
  haveI : Finite F W := Module.Finite.of_surjective T hT
  obtain ⟨n, w, hw⟩ := LADR.Section_2B.exists_basis (F := F) (V := W)
  -- one preimage {lit}`v i` of each basis vector {lit}`w i`
  choose v hv using fun i => hT (w i)
  let U : Submodule F V := Submodule.span F (Set.range v)
  have hvU : ∀ i, v i ∈ U := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hinj : Function.Injective (T.domRestrict U) := by
    rw [← LinearMap.ker_eq_bot]
    refine LinearMap.ker_eq_bot'.mpr ?_
    rintro ⟨x, hx⟩ h0
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hx
    -- {lit}`∑ a i • w i = 0`, so all {lit}`a i = 0` by independence of {lit}`w`
    have hsum : ∑ i, a i • w i = 0 := by
      have : T (∑ i, a i • v i) = 0 := h0
      rw [map_sum] at this
      simpa only [map_smul, hv] using this
    have ha : ∀ i, a i = 0 :=
      fun i => (Fintype.linearIndependent_iff.mp hw.1) a hsum i
    exact Subtype.ext (by simp [ha])
  have hsurj : Function.Surjective (T.domRestrict U) := by
    intro y
    have hy : y ∈ Submodule.span F (Set.range w) := by
      rw [show Submodule.span F (Set.range w) = ⊤ from hw.2]; trivial
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hy
    refine ⟨⟨∑ i, a i • v i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvU i)⟩, ?_⟩
    show T (∑ i, a i • v i) = ∑ i, a i • w i
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hv i]
  exact ⟨U, LinearEquiv.ofBijective (T.domRestrict U) ⟨hinj, hsurj⟩, fun _ => rfl⟩

/-- 3D.10 part (a) -/
def exercise_3D_10_E (U : Submodule F V) : Submodule F (V →ₗ[F] W) where
  carrier := {T | (U : Set V) ⊆ LinearMap.ker T}
  zero_mem' := by
    simp only [SetLike.coe_subset_coe, Set.mem_setOf_eq, LinearMap.ker_zero, le_top]
  add_mem' := by
    intro T₁ T₂ hT₁ hT₂
    simp only [SetLike.coe_subset_coe, Set.mem_setOf_eq]
    simp at hT₁ hT₂
    intro u hu
    simp only [LinearMap.mem_ker, LinearMap.add_apply]
    have h1 := hT₁ hu
    have h2 := hT₂ hu
    simp at h1 h2
    simp only [h1, h2, add_zero]
  smul_mem' := by
    rintro c T hT
    simp only [SetLike.coe_subset_coe, Set.mem_setOf_eq]
    simp at hT
    intro u hu
    simp only [LinearMap.mem_ker, LinearMap.smul_apply]
    have h := hT hu
    simp at h
    rw [h]
    simp only [smul_zero]

/-- 3D.10 part (b). We state the formula, but you need to prove it. -/
theorem exercise_3D_10 [Finite F V] [Finite F W] (U : Submodule F V) :
    finrank F (exercise_3D_10_E U (W := W)) =
      (finrank F V - finrank F U) * finrank F W := by
  -- using the hint - consider the map
  -- L(V, W) → L(U, W) given by restriction to U
  -- E is exactly the kernel of this map.
  -- the rank-nullity says L(V, W) = dim E + dim range restriction map
  -- only thing left is to show the restriction is surjective.
  -- take a linear map from U to W, we can extend it trivially to V
  -- take a basis of U and extending to V, and define the map to be zero
  -- on the extension to V.
  -- (equivalently: extend by zero on a complement of U, 2.34.)
  classical
  -- {lit}`E` is the kernel of restriction to {lit}`U`
  have hker : LinearMap.ker
      (LinearMap.domRestrict' U : (V →ₗ[F] W) →ₗ[F] (U →ₗ[F] W))
      = exercise_3D_10_E U (W := W) := by
    ext T
    simp only [LinearMap.mem_ker]
    constructor
    · intro hT u hu
      have h := congrArg (fun f : U →ₗ[F] W => f ⟨u, hu⟩) hT
      simpa [LinearMap.domRestrict'] using h
    · intro hT
      ext u
      have h : (u : V) ∈ LinearMap.ker T := hT u.2
      simpa [LinearMap.domRestrict'] using h
  -- restriction is surjective: extend by zero on a complement of {lit}`U`
  have hsurj : LinearMap.range
      (LinearMap.domRestrict' U : (V →ₗ[F] W) →ₗ[F] (U →ₗ[F] W)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro S
    obtain ⟨C, hC⟩ := U.exists_isCompl
    refine ⟨S ∘ₗ Submodule.linearProjOfIsCompl U C hC, ?_⟩
    ext u
    show S (Submodule.linearProjOfIsCompl U C hC (u : V)) = S u
    rw [Submodule.linearProjOfIsCompl_apply_left]
  -- the fundamental theorem (3.21) plus 3.72 for both spaces
  have hfin : finrank F (exercise_3D_10_E U (W := W)) + finrank F U * finrank F W
      = finrank F V * finrank F W := by
    have h := LADR.Section_3B.finrank_ker_add_finrank_range
      (LinearMap.domRestrict' U : (V →ₗ[F] W) →ₗ[F] (U →ₗ[F] W))
    rw [hker, hsurj, finrank_top, finrank_linearMap, finrank_linearMap] at h
    exact h
  rw [Nat.sub_mul]
  exact Nat.eq_sub_of_add_eq hfin

/-- 3D.11 -/
theorem exercise_3D_11 [Finite F V] (S T : V →ₗ[F] V) :
    IsInvertible (S ∘ₗ T) ↔ IsInvertible S ∧ IsInvertible T := by
  -- => if ST is invertible, it has to be injective and surjective
  -- then T has to be injective as well, hence invertible
  -- and S has to be surjective as well, hence invertible
  -- <= trivial by composing the inverses
  constructor
  · intro hST
    obtain ⟨hinj, hsurj⟩ := (isInvertible_iff_bijective (S ∘ₗ T)).mp hST
    refine ⟨(isInvertible_iff_surjective rfl S).mpr fun w => ?_,
      (isInvertible_iff_injective rfl T).mpr fun a b hab => ?_⟩
    · obtain ⟨v, hv⟩ := hsurj w
      exact ⟨T v, hv⟩
    · refine hinj ?_
      show S (T a) = S (T b)
      rw [hab]
  · rintro ⟨hS, hT⟩
    obtain ⟨h, -⟩ := exercise_3D_2 T S hT hS
    exact h

/-- 3D.12 -/
theorem exercise_3D_12 [Finite F V] (S T U : V →ₗ[F] V)
    (h : S ∘ₗ T ∘ₗ U = LinearMap.id) :
    ∃ hT : IsInvertible T, hT.inv = U ∘ₗ S := by
  -- S T U = I, by one sided inverse = full in finite-dimensional case
  -- U S T = I and T U S = I as well
  -- but with different order of composition, those say T inv is US
  have h1 : T ∘ₗ (U ∘ₗ S) = LinearMap.id :=
    (mul_eq_id_iff_mul_eq_id rfl S (T ∘ₗ U)).mp h
  have h2 : (U ∘ₗ S) ∘ₗ T = LinearMap.id :=
    (mul_eq_id_iff_mul_eq_id rfl T (U ∘ₗ S)).mp h1
  refine ⟨⟨U ∘ₗ S, h2, h1⟩, ?_⟩
  -- the inverse is unique (3.60)
  exact inv_unique T ⟨IsInvertible.inv_comp _, IsInvertible.comp_inv _⟩ ⟨h2, h1⟩

/-- Forward shift on {lit}`F^∞`: {lit}`(x₁, x₂, …) ↦ (0, x₁, x₂, …)`.
The backward shift of 3.3(e) undoes it, which is what 3D.13 needs. -/
private def forwardShift : (ℕ → F) →ₗ[F] (ℕ → F) where
  toFun x := fun i => match i with
    | 0 => 0
    | n + 1 => x n
  map_add' x y := by funext i; cases i <;> simp
  map_smul' a x := by funext i; cases i <;> simp

/-- 3D.13 Such {lit}`S, T, U` exist only on an infinite-dimensional space, so
the witness space {lit}`V` must be supplied as part of the existential (the
statement would be false for a fixed finite-dimensional {lit}`V`, by 3D.12).
The witness lives in the same universe as {lit}`F`: a nonzero {lit}`F`-vector
space cannot be built in a smaller one. -/
theorem exercise_3D_13.{u} {F : Type u} [Field F] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module F V) (S T U : V →ₗ[F] V),
      S ∘ₗ T ∘ₗ U = LinearMap.id ∧ ¬ IsInvertible T := by
  -- take the vector space ℕ → ℝ
  -- U - shift values right
  -- T - shift values left with drop of a0
  -- S - I
  -- now T is not invertable, but S T U = I
  refine ⟨ℕ → F, inferInstance, inferInstance, LinearMap.id,
    LADR.Section_3A.backwardShift, forwardShift, ?_, ?_⟩
  · -- dropping the first entry undoes prepending a zero
    ext x i
    rfl
  · -- the backward shift kills {lit}`(1, 0, 0, …)`, so it is not injective
    intro hT
    have hinj := ((isInvertible_iff_bijective _).mp hT).1
    have h0 : LADR.Section_3A.backwardShift
        (Pi.single (0 : ℕ) (1 : F) : ℕ → F) = 0 := by
      funext i
      show (Pi.single (0 : ℕ) (1 : F) : ℕ → F) (i + 1) = 0
      exact Pi.single_eq_of_ne (Nat.succ_ne_zero i) (1 : F)
    have hsingle : (Pi.single (0 : ℕ) (1 : F) : ℕ → F) = 0 :=
      hinj (by rw [h0, map_zero])
    have h1 := congrFun hsingle 0
    simp at h1

/-- 3D.14 — prove or counterexample: {lit}`RST` surjective ⟹ {lit}`S`
injective (on f.d.). -/
def exercise_3D_14 :
    Decidable (∀ [Finite F V] (R S T : V →ₗ[F] V),
      Function.Surjective (R ∘ₗ S ∘ₗ T) → Function.Injective S) := by
  apply isTrue
  -- surjective in fin.dim L(V) implies invertable
  -- then apply exercise 13 to get inverable S, which implies injective
  intro _ R S T hsurj
  have hinv : IsInvertible (R ∘ₗ S ∘ₗ T) :=
    (isInvertible_iff_surjective rfl _).mpr hsurj
  obtain ⟨-, hST⟩ := (exercise_3D_11 R (S ∘ₗ T)).mp hinv
  obtain ⟨hS, -⟩ := (exercise_3D_11 S T).mp hST
  exact ((isInvertible_iff_bijective S).mp hS).1

/-- 3D.15 -/
theorem exercise_3D_15 [Finite F V] (T : V →ₗ[F] V) {m : ℕ} (v : Fin m → V)
    (hTv : Spans F (fun k => T (v k))) : Spans F v := by
  -- since T vi spans V, it has to be surjective
  -- if we want preimage of w under T, we can take ∑ ai T vi = w
  -- use ∑ ai vi as preimage by linearity
  -- but now that also means T is invertable
  -- so for every w, we can find T w = ∑ ai T vi because T vi span
  -- and apply T⁻¹ to find w = ∑ ai vi, thus vi also span
  have hspanT : Submodule.span F (Set.range fun k => T (v k)) = ⊤ := hTv
  -- the image of {lit}`T` contains a spanning list, so {lit}`T` is onto
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspanT, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨v k, rfl⟩
  -- hence invertible (3.65), in particular injective
  have hinj : Function.Injective T :=
    ((isInvertible_iff_bijective T).mp ((isInvertible_iff_surjective rfl T).mpr hsurj)).1
  show Submodule.span F (Set.range v) = ⊤
  rw [eq_top_iff]
  intro w _
  have hTw : T w ∈ Submodule.span F (Set.range fun k => T (v k)) := by
    rw [hspanT]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hTw
  -- {lit}`T (∑ aᵢ vᵢ) = ∑ aᵢ T vᵢ = T w`, so {lit}`w = ∑ aᵢ vᵢ`
  have hsum : T (∑ i, a i • v i) = T w := by
    rw [map_sum]
    simpa only [map_smul] using ha
  rw [← hinj hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- 3D.16 — Every linear map {lit}`F^{n,1} → F^{m,1}` is matrix multiplication. -/
theorem exercise_3D_16 {m n : ℕ}
    (T : Matrix (Fin n) (Fin 1) F →ₗ[F] Matrix (Fin m) (Fin 1) F) :
    ∃ A : Matrix (Fin m) (Fin n) F, ∀ x, T x = A * x := by
  -- construct it by putting Aij = the i-th coeff of T e_j
  -- the equality should follow by definition.
  classical
  refine ⟨Matrix.of fun i j => T (Matrix.single j 0 1) i 0, fun x => ?_⟩
  -- write {lit}`x = ∑ⱼ xⱼ eⱼ` and push {lit}`T` through the sum
  have hx : x = ∑ j, x j 0 • Matrix.single j 0 (1 : F) := by
    ext i k
    fin_cases k
    simp [Matrix.sum_apply, Matrix.single_apply]
  ext i k
  fin_cases k
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.of_apply, mul_comm]
  rfl

/-- 3D.17 -/
def exercise_3D_17_𝒜 (S : V →ₗ[F] V) : (V →ₗ[F] V) →ₗ[F] (V →ₗ[F] V) where
  toFun T := S ∘ₗ T
  map_add' T₁ T₂ := by ext v; simp
  map_smul' a T := by ext v; simp

/-- 3D.17 (a) -/
theorem exercise_3D_17a [Finite F V] (S : V →ₗ[F] V) :
    finrank F (LinearMap.ker (exercise_3D_17_𝒜 S)) =
      finrank F V * finrank F (LinearMap.ker S) := by
  -- if T is in ker A, the range T must be in ker S.
  -- so every such T can be restricted to a map from V to ker S.
  -- the restriction map is injective, thus the dim of the ker A
  -- is L(V, ker S) = dim V * dim ker S.
  have hker : ∀ T ∈ LinearMap.ker (exercise_3D_17_𝒜 S), ∀ v, T v ∈ LinearMap.ker S := by
    intro T hT v
    have h := congrArg (fun f : V →ₗ[F] V => f v) (LinearMap.mem_ker.mp hT)
    simpa [exercise_3D_17_𝒜] using h
  -- restrict the codomain to {lit}`ker S`
  let φ : LinearMap.ker (exercise_3D_17_𝒜 S) →ₗ[F] (V →ₗ[F] LinearMap.ker S) :=
    { toFun := fun T => LinearMap.codRestrict _ T.1 (hker T.1 T.2)
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl }
  -- injective: the restriction remembers every value {lit}`T v`
  have hinj : Function.Injective φ := by
    intro T₁ T₂ h
    ext v
    exact congrArg Subtype.val (LinearMap.congr_fun h v)
  -- surjective: compose a map into {lit}`ker S` with the inclusion
  have hsurj : Function.Surjective φ := by
    intro R
    refine ⟨⟨(LinearMap.ker S).subtype ∘ₗ R, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker]
      ext v
      simp [exercise_3D_17_𝒜]
    · ext; rfl
  rw [(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, finrank_linearMap]

/-- 3D.17 (b) -/
theorem exercise_3D_17b [Finite F V] (S : V →ₗ[F] V) :
    finrank F (LinearMap.range (exercise_3D_17_𝒜 S)) =
      finrank F V * finrank F (LinearMap.range S) := by
  -- apply rank-nullity to A first and then to S
  have hA := LADR.Section_3B.finrank_ker_add_finrank_range (exercise_3D_17_𝒜 S)
  have hS := LADR.Section_3B.finrank_ker_add_finrank_range S
  rw [exercise_3D_17a, finrank_linearMap] at hA
  -- {lit}`n·n = n·k + dim range 𝒜` and {lit}`n = k + r`, so {lit}`dim range 𝒜 = n·r`
  have h : finrank F V * finrank F V = finrank F V * finrank F (LinearMap.ker S)
      + finrank F V * finrank F (LinearMap.range S) := by
    rw [← mul_add, hS]
  omega

/-- 3D.18 -/
theorem exercise_3D_18 : Nonempty (V ≃ₗ[F] (F →ₗ[F] V)) := by
  -- construct an explicit map from V tot F →ₗ[F] V
  -- v ↦ (fun x: F, x • v)
  -- show it is linear
  -- a) v + w ↦ (fun x, x • (v + w)) = (fun x, x • v + x • w) = (fun x, x • v) + (fun x, x • w)
  -- b) a • v ↦ (fun x, x • (a • v)) = (fun x, (x * a) • v) = (fun x, x • (a • v)) = a • (fun x, x • v)
  -- show it is injective and surjective
  -- a) if fun x, x • v = 0 for all x, then v = 0, so injective
  -- b) for surjective, given f : F →ₗ[F] V, take v = f 1, then the map v ↦ (fun x, x • v) gives f.
  let Φ : V →ₗ[F] (F →ₗ[F] V) :=
    { toFun := fun v =>
        { toFun := fun x => x • v
          map_add' := fun x y => add_smul x y v
          map_smul' := fun a x => by simp [mul_smul] }
      map_add' := fun v w => by ext; simp [smul_add]
      map_smul' := fun a v => by ext; simp [smul_smul, mul_comm] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    -- evaluate at {lit}`x = 1`
    simpa [Φ] using LinearMap.congr_fun hv 1
  have hsurj : Function.Surjective Φ := by
    intro f
    refine ⟨f 1, ?_⟩
    ext
    simp [Φ, ← map_smul]
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩

/-- 3D.19 -/
theorem exercise_3D_19 [Finite F V] (T : V →ₗ[F] V) :
    (∀ {n : ℕ} (u v : Fin n → V) (hu : IsBasis F u) (hv : IsBasis F v),
      matrixOf hu hu T = matrixOf hv hv T) ↔
      ∃ γ : F, T = γ • LinearMap.id := by
  -- => take a fixed basis vi for V
  -- first for any i and j (s.t. i ≠ j), consider the new basis
  -- vi' = vi + vj (with rest the same)
  -- this will give a relation Mii = Mii + Mij, so Mij = 0 for i ≠ j
  -- the matrix will be diagonal with all off-diagonal entries 0
  -- then consider a swapped basis vi' = vj, vj' = vi (with rest the same)
  -- this will give a relation Mii = Mjj, so all diagonal entries are equal
  -- take M00 to be γ and arrive at T = γ • LinearMap.id
  -- <= for any basis v, T vi = γ vi, so Mii = γ and Mij = 0 for i ≠ j.
  classical
  constructor
  · intro h
    obtain ⟨n, v, hv⟩ := LADR.Section_2B.exists_basis (F := F) (V := V)
    have hn : n = finrank F V := LADR.Section_2C.isBasis_card_eq_finrank v hv
    set M := matrixOf hv hv T with hM
    set b := hv.toModuleBasis with hb
    have hbv : ∀ k, b k = v k := IsBasis.toModuleBasis_apply hv
    -- coordinates of {lit}`v l` and {lit}`T (v k)` in the basis {lit}`v`
    have hrepr : ∀ l k, b.repr (v l) k = if l = k then 1 else 0 := by
      intro l k
      rw [← hbv, b.repr_self, Finsupp.single_apply]
    have hcoord : ∀ l k, b.repr (T (v k)) l = M l k := fun l k =>
      (matrixOf_apply hv hv T l k).symm
    -- a list of length {lit}`n = dim V` whose span contains every {lit}`vₖ` is a basis
    have hbasis : ∀ w : Fin n → V,
        (∀ k, v k ∈ Submodule.span F (Set.range w)) → IsBasis F w := by
      intro w hw
      refine LADR.Section_2C.isBasis_of_spans_of_card_eq w ?_ hn
      rw [Spans, eq_top_iff, ← hv.2, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hw k
    have hoff : ∀ i j, i ≠ j → M i j = 0 := by
      intro i j hij
      let v' := Function.update v i (v i + v j)
      have hv'i : v' i = v i + v j := Function.update_self _ _ _
      have hv'l : ∀ l, l ≠ i → v' l = v l := fun l hl => Function.update_of_ne hl _ _
      have hv' : IsBasis F v' := by
        refine hbasis v' fun k => ?_
        by_cases hk : k = i
        · subst hk
          have hvk : v k = v' k - v' j := by rw [hv'i, hv'l j (Ne.symm hij)]; abel
          rw [hvk]
          exact Submodule.sub_mem _ (Submodule.subset_span ⟨k, rfl⟩)
            (Submodule.subset_span ⟨j, rfl⟩)
        · rw [← hv'l k hk]
          exact Submodule.subset_span ⟨k, rfl⟩
      -- {lit}`T (vᵢ + vⱼ) = ∑ₗ Mₗᵢ v'ₗ`; compare the {lit}`vᵢ`-coordinates
      have hspec := matrixOf_spec hv' hv' T i
      rw [← h v v' hv hv', ← hM] at hspec
      have hc := congrArg (fun x => b.repr x i) hspec
      simp only [hv'i, map_add, Finsupp.add_apply, hcoord, map_sum, map_smul,
        Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul] at hc
      rw [Finset.sum_eq_single i (fun l _ hl => by rw [hv'l l hl, hrepr, if_neg hl, mul_zero])
        (by simp), hv'i, map_add, Finsupp.add_apply, hrepr, hrepr, if_pos rfl,
        if_neg (Ne.symm hij)] at hc
      linear_combination hc
    have hdiag : ∀ i j, M i i = M j j := by
      intro i j
      let v' := v ∘ Equiv.swap i j
      have hv' : IsBasis F v' := by
        refine hbasis v' fun k => ?_
        have hvk : v k = v' (Equiv.swap i j k) := by simp [v']
        rw [hvk]
        exact Submodule.subset_span ⟨_, rfl⟩
      -- {lit}`T vⱼ = ∑ₗ Mₗᵢ v_{swap l}`; compare the {lit}`vⱼ`-coordinates
      have hspec := matrixOf_spec hv' hv' T i
      rw [← h v v' hv hv', ← hM] at hspec
      have hc := congrArg (fun x => b.repr x j) hspec
      simp only [v', Function.comp_apply, Equiv.swap_apply_left, hcoord, map_sum, map_smul,
        Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
        hrepr] at hc
      rw [hc, Finset.sum_eq_single i]
      · simp
      · intro l _ hl
        rw [if_neg, mul_zero]
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
        exact hl
      · simp
    -- take M00 as γ; every {lit}`T vₖ = Mₖₖ vₖ = M₀₀ vₖ`
    refine ⟨if h0 : 0 < n then M ⟨0, h0⟩ ⟨0, h0⟩ else 0, b.ext fun k => ?_⟩
    rw [dif_pos (Fin.pos k), hbv, matrixOf_spec hv hv T k, ← hM,
      Finset.sum_eq_single k (fun l _ hl => by rw [hoff l k hl, zero_smul]) (by simp),
      hdiag k ⟨0, Fin.pos k⟩]
    simp
  · rintro ⟨γ, rfl⟩ n u v hu hv
    have hscalar : ∀ {w : Fin n → V} (hw : IsBasis F w),
        matrixOf hw hw (γ • LinearMap.id) = γ • (1 : Matrix (Fin n) (Fin n) F) := by
      intro w hw
      ext j k
      rw [matrixOf_apply, LinearMap.smul_apply, LinearMap.id_apply,
        ← IsBasis.toModuleBasis_apply hw, map_smul, hw.toModuleBasis.repr_self]
      simp [Finsupp.single_apply, Matrix.one_apply, eq_comm]
    rw [hscalar hu, hscalar hv]

/-- 3D.20 -/
theorem exercise_3D_20 (q : Polynomial ℝ) :
    ∃ p : Polynomial ℝ, ∀ x : ℝ,
      q.eval x = (x ^ 2 + x) * (p.derivative.derivative.eval x) +
        2 * x * (p.derivative.eval x) + p.eval 3 := by
  -- similar to one in the chapter
  -- first show (x^2+x)p'' + 2*x*p' + p(3) is a linear operator
  -- more over it respects degree, so it map Pk to Pk for each k
  -- because derivative lowers the degree by 1, but multiplication by x^2+x raises.
  -- the operator is also injective on Pk
  -- consider the highest degree term of p with cooeff a ≠ 0
  -- the operator will transform a x^k to (k(k-1) + 2k) a = k(k+1) a for the highest degree term.
  -- (assuming non-const), so if T p = 0, then the highest degree term must have coefficient 0
  -- which is a contradiction. For constant, p(3) = C must be zero, so also zero.
  -- since the operator is injective on Pk it is also surjective.
  -- finally, apply it to Pk where k is deg q for the given q,
  -- to find the desired solution using surjectivity.
  classical
  set c : Polynomial ℝ := Polynomial.X ^ 2 + Polynomial.X with hc
  -- the operator {lit}`L p = (x² + x) p'' + 2x p' + p(3)` is linear
  set L : Polynomial ℝ →ₗ[ℝ] Polynomial ℝ :=
    LinearMap.mulLeft ℝ c ∘ₗ Polynomial.derivative ∘ₗ Polynomial.derivative
      + LinearMap.mulLeft ℝ (2 * Polynomial.X) ∘ₗ Polynomial.derivative
      + (Polynomial.leval (3 : ℝ)).smulRight (1 : Polynomial ℝ) with hL_def
  have hL : ∀ p, L p = c * p.derivative.derivative + 2 * Polynomial.X * p.derivative
      + Polynomial.C (p.eval 3) := by
    intro p
    simp [hL_def, LinearMap.mulLeft_apply, Polynomial.smul_eq_C_mul, mul_assoc]
  -- {lit}`L` does not raise the degree
  have hdeg : ∀ p : Polynomial ℝ, (L p).natDegree ≤ p.natDegree := by
    intro p
    have h1 : p.derivative.natDegree ≤ p.natDegree - 1 := Polynomial.natDegree_derivative_le _
    have h2 : p.derivative.derivative.natDegree ≤ p.derivative.natDegree - 1 :=
      Polynomial.natDegree_derivative_le _
    have hc2 : c.natDegree ≤ 2 := by rw [hc]; compute_degree
    have hX2 : (2 * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by compute_degree
    rw [hL]
    refine Polynomial.natDegree_add_le_of_degree_le
      (Polynomial.natDegree_add_le_of_degree_le ?_ ?_) (by simp)
    · -- {lit}`deg ((x² + x) p'') ≤ 2 + (deg p - 2)`, and {lit}`p'' = 0` when {lit}`deg p < 2`
      by_cases hd : 2 ≤ p.natDegree
      · exact le_trans Polynomial.natDegree_mul_le (by omega)
      · rw [Polynomial.derivative_of_natDegree_zero (by omega), mul_zero,
          Polynomial.natDegree_zero]
        exact Nat.zero_le _
    · by_cases hd : 1 ≤ p.natDegree
      · exact le_trans Polynomial.natDegree_mul_le (by omega)
      · rw [Polynomial.derivative_of_natDegree_zero (by omega), mul_zero,
          Polynomial.natDegree_zero]
        exact Nat.zero_le _
  -- {lit}`L` is injective
  have hinj : ∀ p, L p = 0 → p = 0 := by
    intro p hp
    by_contra hp0
    set d := p.natDegree with hd
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · -- constant {lit}`p = a`: then {lit}`L p = p(3) = a`
      have hpC := Polynomial.eq_C_of_natDegree_eq_zero hd0
      rw [hL, hpC] at hp
      simp at hp
      exact hp0 (by rw [hpC, hp, Polynomial.C_0])
    · -- the coefficient of {lit}`x^d` in {lit}`L p` is {lit}`d(d+1)·a`
      have hlead : (L p).coeff d = p.coeff d * (d * (d + 1)) := by
        have hnext : p.coeff (d + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        rw [he] at hnext ⊢
        rw [hL, hc]
        rcases e with _ | f
        · simp [add_mul, mul_assoc, Polynomial.coeff_derivative, Polynomial.coeff_X_pow_mul',
            Polynomial.coeff_X_mul, hnext]
          ring
        · simp [add_mul, mul_assoc, Polynomial.coeff_derivative, Polynomial.coeff_X_pow_mul',
            Polynomial.coeff_X_mul, hnext]
          ring
      rw [hp, Polynomial.coeff_zero] at hlead
      have ha : p.coeff d ≠ 0 := by
        rw [hd]; exact mt Polynomial.leadingCoeff_eq_zero.mp hp0
      have hdd : (d : ℝ) * (d + 1) ≠ 0 := by positivity
      exact mul_ne_zero ha hdd hlead.symm
  -- restrict {lit}`L` to {lit}`𝒫_m(ℝ)` with {lit}`m = deg q`
  set m := q.natDegree with hm
  have hmem : ∀ p : Polynomial ℝ,
      p ∈ Polynomial.degreeLT ℝ (m + 1) ↔ p.natDegree ≤ m := by
    intro p
    rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero,
      Polynomial.natDegree_le_iff_coeff_eq_zero]
    exact Iff.rfl
  have hmaps : ∀ p ∈ Polynomial.degreeLT ℝ (m + 1), L p ∈ Polynomial.degreeLT ℝ (m + 1) := by
    intro p hp
    rw [hmem] at hp ⊢
    exact le_trans (hdeg p) hp
  set T := L.restrict hmaps with hT_def
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    exact Subtype.ext (hinj z (congrArg Subtype.val hz))
  -- injective on {lit}`𝒫_m(ℝ)`, hence surjective (3.65)
  have hTsurj : Function.Surjective T := (injective_iff_surjective rfl T).mp hTinj
  obtain ⟨z, hz⟩ := hTsurj ⟨q, (hmem q).mpr le_rfl⟩
  have hLz : L z = q := congrArg Subtype.val hz
  refine ⟨z, fun x => ?_⟩
  rw [← hLz, hL, hc]
  simp

/-- 3D.21 -/
theorem exercise_3D_21 {n : ℕ} (A : Fin n → Fin n → F) :
    (∀ x : Fin n → F, (∀ j, ∑ k, A j k * x k = 0) → x = 0) ↔
      (∀ c : Fin n → F, ∃ x : Fin n → F, ∀ j, ∑ k, A j k * x k = c j) := by
  -- consider linear transformation T for vector space F^n, that has A as a matrix
  -- for the standard ei basis
  -- now this statements is equivalent to injectivity is equivalent to surjectivity of T.
  let T : (Fin n → F) →ₗ[F] (Fin n → F) :=
    { toFun := fun x j => ∑ k, A j k * x k
      map_add' := fun x y => by ext j; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by ext j; simp [Finset.mul_sum, mul_left_comm] }
  have hT : ∀ x j, T x j = ∑ k, A j k * x k := fun _ _ => rfl
  -- the left side says {lit}`T` is injective, the right side that it is surjective
  have hinj : (∀ x : Fin n → F, (∀ j, ∑ k, A j k * x k = 0) → x = 0) ↔
      Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    refine forall_congr' fun x => imp_congr_left ?_
    rw [funext_iff]
    simp only [hT, Pi.zero_apply]
  have hsurj : (∀ c : Fin n → F, ∃ x : Fin n → F, ∀ j, ∑ k, A j k * x k = c j) ↔
      Function.Surjective T := by
    refine forall_congr' fun c => exists_congr fun x => ?_
    rw [funext_iff]
    simp only [hT]
  rw [hinj, hsurj]
  exact injective_iff_surjective rfl T

/-- 3D.22 -/
theorem exercise_3D_22 [Finite F V] {n : ℕ}
    {v : Fin n → V} (hv : IsBasis F v) (T : V →ₗ[F] V) :
    IsUnit (matrixOf hv hv T) ↔ IsInvertible T := by
  -- => if M' is the inverse of M, it gives raise to a transformation T' s.t.
  -- M' * M = 1, hence T' * T = id, so T' is the inverse of T (for finite basis, one side is enough)
  -- <= if T is invertible, consider its inverse T' s.t T' * T = id
  -- then M' is the matrix of T' with respect to the same basis, and M' * M = 1
  -- since matrix multiplication is lin. trans. composition.
  constructor
  · rintro ⟨u, hu⟩
    -- the linear map {lit}`T'` with {lit}`ℳ(T') = M⁻¹`
    obtain ⟨T', hT'⟩ := matrixOfₗ_surjective hv hv (u⁻¹ : (Matrix (Fin n) (Fin n) F)ˣ)
    rw [matrixOfₗ_apply] at hT'
    have hcomp : T' ∘ₗ T = LinearMap.id := by
      apply matrixOfₗ_injective hv hv
      rw [matrixOfₗ_apply, matrixOfₗ_apply, matrixOf_comp hv hv hv, hT', ← hu,
        Units.inv_mul, matrixOf_id_self]
    exact ⟨T', hcomp, (mul_eq_id_iff_mul_eq_id rfl T' T).mp hcomp⟩
  · rintro ⟨S, hST, hTS⟩
    -- {lit}`ℳ(S) ℳ(T) = ℳ(ST) = ℳ(I) = 1`, and symmetrically
    refine ⟨⟨matrixOf hv hv T, matrixOf hv hv S, ?_, ?_⟩, rfl⟩
    · rw [← matrixOf_comp, hTS, matrixOf_id_self]
    · rw [← matrixOf_comp, hST, matrixOf_id_self]

/-- 3D.23 -/
theorem exercise_3D_23 {n : ℕ}
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hT : ∀ k, T (v k) = u k) :
    matrixOf hv hv T = matrixOf hu hv LinearMap.id := by
  -- matrix hv hv T = matrix hv hv (I T) =
  -- matrix hu hv I * matrix hv hu T
  -- but matrix hv hu T by definition is just I
  -- giving the final answer.
  have hTvu : matrixOf hv hu T = 1 := by
    ext j k
    rw [matrixOf_apply, hT, ← IsBasis.toModuleBasis_apply hu, hu.toModuleBasis.repr_self,
      Finsupp.single_apply, Matrix.one_apply]
    simp only [eq_comm]
  rw [show T = LinearMap.id ∘ₗ T from rfl, matrixOf_comp hv hu hv, hTvu, mul_one]

/-- 3D.24 — {lit}`A * B = 1 ⟹ B * A = 1` -/
theorem exercise_3D_24 {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hAB : A * B = 1) : B * A = 1 := by
  -- translate to linear maps for F^n
  -- we already proved for A,B in L(V) with V finite
  -- that invertable just needs one-sided inverse.
  have he := LADR.Section_2B.isBasis_stdBasis (F := F) n
  obtain ⟨S, hS⟩ := matrixOfₗ_surjective he he A
  obtain ⟨T, hT⟩ := matrixOfₗ_surjective he he B
  rw [matrixOfₗ_apply] at hS hT
  -- {lit}`ℳ(ST) = AB = 1 = ℳ(I)`, so {lit}`ST = I`
  have hST : S ∘ₗ T = LinearMap.id := by
    apply matrixOfₗ_injective he he
    rw [matrixOfₗ_apply, matrixOfₗ_apply, matrixOf_comp he he he, hS, hT, hAB,
      matrixOf_id_self]
  -- hence {lit}`TS = I` (3.68), and {lit}`BA = ℳ(TS) = 1`
  have hTS := (mul_eq_id_iff_mul_eq_id rfl S T).mp hST
  rw [← hS, ← hT, ← matrixOf_comp, hTS, matrixOf_id_self]

end LADR.Section_3D
