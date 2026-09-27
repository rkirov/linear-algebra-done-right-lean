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

/-- The list {lit}`(4,2), (5,3)` is a basis of {lit}`ℝ²` (a {lit}`2B.2`-style
fact, left as {lit}`sorry`). -/
theorem isBasis_4253 :
    IsBasis ℝ (![![4, 2], ![5, 3]] : Fin 2 → Fin 2 → ℝ) := by sorry

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
  sorry

/-- 3D.2 {lit}`S ∘ T` is invertible and {lit}`(ST)⁻¹ = T⁻¹ S⁻¹`. -/
theorem exercise_3D_2 (T : U →ₗ[F] V) (S : V →ₗ[F] W)
    (hT : IsInvertible T) (hS : IsInvertible S) :
    ∃ h : IsInvertible (S ∘ₗ T), h.inv = hT.inv ∘ₗ hS.inv := by
  sorry

/-- 3D.3 The following are equivalent: {lit}`T` is invertible; {lit}`T` maps
every basis of {lit}`V` to a basis; {lit}`T` maps some basis to a basis. -/
theorem exercise_3D_3 [Finite F V] (T : V →ₗ[F] V) :
    [IsInvertible T,
     ∀ {n : ℕ} (v : Fin n → V) (_ : IsBasis F v), IsBasis F (fun k => T (v k)),
     ∃ (n : ℕ) (v : Fin n → V) (_ : IsBasis F v), IsBasis F (fun k => T (v k))].TFAE := by
  sorry

/-- 3D.4 -/
theorem exercise_3D_4 [Finite F V] (hV : 1 < finrank F V) :
    ¬ ∃ (U : Submodule F (V →ₗ[F] V)),
      ∀ T : V →ₗ[F] V, T ∈ U ↔ ¬ IsInvertible T := by
  sorry

/-- 3D.5 -/
theorem exercise_3D_5 [Finite F V] (U : Submodule F V) (S : U →ₗ[F] V) :
    (∃ T : V →ₗ[F] V, IsInvertible T ∧ ∀ u : U, T (u : V) = S u) ↔
      Function.Injective S := by
  sorry

/-- 3D.6 -/
theorem exercise_3D_6 [Finite F W] (S T : V →ₗ[F] W) :
    LinearMap.ker S = LinearMap.ker T ↔
      ∃ E : W →ₗ[F] W, IsInvertible E ∧ S = E ∘ₗ T := by
  sorry

/-- 3D.7 -/
theorem exercise_3D_7 [Finite F V] (S T : V →ₗ[F] W) :
    LinearMap.range S = LinearMap.range T ↔
      ∃ E : V →ₗ[F] V, IsInvertible E ∧ S = T ∘ₗ E := by
  sorry

/-- 3D.8 -/
theorem exercise_3D_8 [Finite F V] [Finite F W] (S T : V →ₗ[F] W) :
    (∃ (E₁ : V →ₗ[F] V) (E₂ : W →ₗ[F] W), IsInvertible E₁ ∧ IsInvertible E₂ ∧
      S = E₂ ∘ₗ T ∘ₗ E₁) ↔
      finrank F (LinearMap.ker S) = finrank F (LinearMap.ker T) := by
  sorry

/-- 3D.9 -/
theorem exercise_3D_9 [Finite F V] (T : V →ₗ[F] W) (hT : Function.Surjective T) :
    ∃ U : Submodule F V,
      ∃ E : U ≃ₗ[F] W, ∀ u : U, E u = T (u : V) := by
  sorry

/-- 3D.10 part (a) -/
def exercise_3D_10_E (U : Submodule F V) : Submodule F (V →ₗ[F] W) where
  carrier := {T | (U : Set V) ⊆ LinearMap.ker T}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-- 3D.10 part (b). We state the formula, but you need to prove it. -/
theorem exercise_3D_10 [Finite F V] [Finite F W] (U : Submodule F V) :
    finrank F (exercise_3D_10_E U (W := W)) =
      (finrank F V - finrank F U) * finrank F W := by
  sorry

/-- 3D.11 -/
theorem exercise_3D_11 [Finite F V] (S T : V →ₗ[F] V) :
    IsInvertible (S ∘ₗ T) ↔ IsInvertible S ∧ IsInvertible T := by
  sorry

/-- 3D.12 -/
theorem exercise_3D_12 [Finite F V] (S T U : V →ₗ[F] V)
    (h : S ∘ₗ T ∘ₗ U = LinearMap.id) :
    ∃ hT : IsInvertible T, hT.inv = U ∘ₗ S := by
  sorry

/-- 3D.13 Such {lit}`S, T, U` exist only on an infinite-dimensional space, so
the witness space {lit}`V` must be supplied as part of the existential (the
statement would be false for a fixed finite-dimensional {lit}`V`, by 3D.12).
The witness lives in the same universe as {lit}`F`: a nonzero {lit}`F`-vector
space cannot be built in a smaller one. -/
theorem exercise_3D_13.{u} {F : Type u} [Field F] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module F V) (S T U : V →ₗ[F] V),
      S ∘ₗ T ∘ₗ U = LinearMap.id ∧ ¬ IsInvertible T := by
  sorry

/-- 3D.14 — prove or counterexample: {lit}`RST` surjective ⟹ {lit}`S`
injective (on f.d.). -/
def exercise_3D_14 :
    Decidable (∀ [Finite F V] (R S T : V →ₗ[F] V),
      Function.Surjective (R ∘ₗ S ∘ₗ T) → Function.Injective S) := by
  sorry

/-- 3D.15 -/
theorem exercise_3D_15 [Finite F V] (T : V →ₗ[F] V) {m : ℕ} (v : Fin m → V)
    (hTv : Spans F (fun k => T (v k))) : Spans F v := by
  sorry

/-- 3D.16 — Every linear map {lit}`F^{n,1} → F^{m,1}` is matrix multiplication. -/
theorem exercise_3D_16 {m n : ℕ}
    (T : Matrix (Fin n) (Fin 1) F →ₗ[F] Matrix (Fin m) (Fin 1) F) :
    ∃ A : Matrix (Fin m) (Fin n) F, ∀ x, T x = A * x := by
  sorry

/-- 3D.17 -/
def exercise_3D_17_𝒜 (S : V →ₗ[F] V) : (V →ₗ[F] V) →ₗ[F] (V →ₗ[F] V) where
  toFun T := S ∘ₗ T
  map_add' T₁ T₂ := by ext v; simp
  map_smul' a T := by ext v; simp

/-- 3D.17 (a) -/
theorem exercise_3D_17a [Finite F V] (S : V →ₗ[F] V) :
    finrank F (LinearMap.ker (exercise_3D_17_𝒜 S)) =
      finrank F V * finrank F (LinearMap.ker S) := by
  sorry

/-- 3D.17 (b) -/
theorem exercise_3D_17b [Finite F V] (S : V →ₗ[F] V) :
    finrank F (LinearMap.range (exercise_3D_17_𝒜 S)) =
      finrank F V * finrank F (LinearMap.range S) := by
  sorry

/-- 3D.18 -/
theorem exercise_3D_18 : Nonempty (V ≃ₗ[F] (F →ₗ[F] V)) := by
  sorry

/-- 3D.19 -/
theorem exercise_3D_19 [Finite F V] (T : V →ₗ[F] V) :
    (∀ {n : ℕ} (u v : Fin n → V) (hu : IsBasis F u) (hv : IsBasis F v),
      matrixOf hu hu T = matrixOf hv hv T) ↔
      ∃ γ : F, T = γ • LinearMap.id := by
  sorry

/-- 3D.20 -/
theorem exercise_3D_20 (q : Polynomial ℝ) :
    ∃ p : Polynomial ℝ, ∀ x : ℝ,
      q.eval x = (x ^ 2 + x) * (p.derivative.derivative.eval x) +
        2 * x * (p.derivative.eval x) + p.eval 3 := by
  sorry

/-- 3D.21 -/
theorem exercise_3D_21 {n : ℕ} (A : Fin n → Fin n → F) :
    (∀ x : Fin n → F, (∀ j, ∑ k, A j k * x k = 0) → x = 0) ↔
      (∀ c : Fin n → F, ∃ x : Fin n → F, ∀ j, ∑ k, A j k * x k = c j) := by
  sorry

/-- 3D.22 -/
theorem exercise_3D_22 [Finite F V] {n : ℕ}
    {v : Fin n → V} (hv : IsBasis F v) (T : V →ₗ[F] V) :
    IsUnit (matrixOf hv hv T) ↔ IsInvertible T := by
  sorry

/-- 3D.23 -/
theorem exercise_3D_23 {n : ℕ}
    {u v : Fin n → V} (hu : IsBasis F u) (hv : IsBasis F v)
    (T : V →ₗ[F] V) (hT : ∀ k, T (v k) = u k) :
    matrixOf hv hv T = matrixOf hu hv LinearMap.id := by
  sorry

/-- 3D.24 — {lit}`A * B = 1 ⟹ B * A = 1` -/
theorem exercise_3D_24 {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hAB : A * B = 1) : B * A = 1 := by
  sorry

end LADR.Section_3D
