module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Matrix.Hermitian
public import LinearAlgebraDoneRightLean.Section_7A
public import LinearAlgebraDoneRightLean.Section_6B
public import LinearAlgebraDoneRightLean.Section_6C
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linter.Style
public import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 7B: Spectral Theorem
-/

@[expose] public section

namespace LADR.Section_7B

open scoped InnerProductSpace RealInnerProductSpace ComplexConjugate
open Module (finrank)
open Module.End (HasEigenvalue HasEigenvector)
open LADR.Section_3D (IsInvertible)

variable {𝕜 : Type*} [RCLike 𝕜]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-! # Real Spectral Theorem -/

/-! 7.26 Invertible quadratic expressions

If {lit}`T ∈ ℒ(V)` is self-adjoint and {lit}`b, c ∈ ℝ` satisfy {lit}`b² < 4c`,
then {lit}`T² + bT + cI` is invertible. Axler's proof runs through positivity:
{lit}`⟨(T² + bT + cI)v, v⟩ > 0` for {lit}`v ≠ 0`, which forces injectivity and
hence (in finite dimensions) invertibility. We record the positivity step as
{lit}`quadratic_pos` and the conclusion itself as {lit}`quadratic_isInvertible`. -/

omit [FiniteDimensional 𝕜 V] in
theorem quadratic_pos (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (b c : ℝ)
    (hbc : b ^ 2 < 4 * c) (v : V) (hv : v ≠ 0) :
    0 < RCLike.re ⟪(T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) v,
      v⟫_𝕜 := by
  have hinner : ⟪(T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) v, v⟫_𝕜
      = ((‖T v‖ ^ 2 : ℝ) : 𝕜) + (b : 𝕜) * ⟪T v, v⟫_𝕜 + ((c * ‖v‖ ^ 2 : ℝ) : 𝕜) := by
    rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_left,
      LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      inner_smul_left, inner_smul_left, hT (T v) v, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, RCLike.conj_ofReal, RCLike.conj_ofReal]
    push_cast
    ring
  rw [hinner, map_add, map_add, RCLike.ofReal_re, RCLike.re_ofReal_mul, RCLike.ofReal_re]
  have hcs : RCLike.re ⟪T v, v⟫_𝕜 ^ 2 ≤ ‖T v‖ ^ 2 * ‖v‖ ^ 2 := by
    have h1 : ‖⟪T v, v⟫_𝕜‖ ≤ ‖T v‖ * ‖v‖ := norm_inner_le_norm (T v) v
    have h2 : |RCLike.re ⟪T v, v⟫_𝕜| ≤ ‖T v‖ * ‖v‖ :=
      le_trans (RCLike.abs_re_le_norm _) h1
    nlinarith [sq_abs (RCLike.re ⟪T v, v⟫_𝕜), norm_nonneg (T v), norm_nonneg v,
      abs_nonneg (RCLike.re ⟪T v, v⟫_𝕜)]
  have hs : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith [hcs, hbc, hs, sq_nonneg (‖v‖ ^ 2 * b + 2 * RCLike.re ⟪T v, v⟫_𝕜),
    mul_pos hs hs]

/-- 7.26 If {lit}`T` is self-adjoint and {lit}`b² < 4c`, then {lit}`T² + bT + cI`
is invertible. -/
theorem quadratic_isInvertible (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (b c : ℝ)
    (hbc : b ^ 2 < 4 * c) :
    IsInvertible (T ∘ₗ T + (b : 𝕜) • T + (c : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V)) := by
  refine (Section_3D.isInvertible_iff_injective rfl _).mpr fun x y hxy => ?_
  by_contra hne
  have hpos := quadratic_pos T hT b c hbc (x - y) (sub_ne_zero.mpr hne)
  rw [map_sub, hxy, sub_self, inner_zero_left, map_zero] at hpos
  exact lt_irrefl 0 hpos

/-! 7.27 Minimal polynomial of a self-adjoint operator

If {lit}`T ∈ ℒ(V)` is self-adjoint, then the minimal polynomial of {lit}`T` equals
{lit}`(z − λ₁) ⋯ (z − λₘ)` for some {lit}`λ₁, …, λₘ ∈ ℝ`.

Axler's proof splits on {lit}`𝔽`, and so do we: {name}`RCLike.I_eq_zero_or_im_I_eq_one`
says {lit}`𝕜` is (isomorphic to) {lit}`ℝ` or {lit}`ℂ`.

* {lit}`𝔽 = ℂ`: by the fundamental theorem of algebra (4.13) the minimal polynomial is a
  product of linear factors {lit}`z − λₖ`; each {lit}`λₖ` is a zero of the minimal
  polynomial, hence an eigenvalue (5.27(a)), hence real (7.12).
* {lit}`𝔽 = ℝ`: by 4.16 the minimal polynomial is
  {lit}`c (z − λ₁) ⋯ (z − λₘ)(z² + b₁z + c₁) ⋯ (z² + b_Nz + c_N)` with {lit}`bₖ² < 4cₖ`.
  If {lit}`N > 0`, multiplying {lit}`p(T) = 0` on the right by the inverse of
  {lit}`T² + b_NT + c_NI` (invertible by 7.26) gives a polynomial of smaller degree
  annihilating {lit}`T`, contradicting minimality. So {lit}`N = 0`, and {lit}`c = 1`
  because the minimal polynomial is monic. -/

open Polynomial in
@[avoiding LinearMap.IsSymmetric.eigenvectorBasis, LinearMap.IsSymmetric.eigenvalues]
theorem minpoly_isSymmetric_eq_prod (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) :
    ∃ (m : ℕ) (lams : Fin m → ℝ), minpoly 𝕜 T = ∏ k, (X - C ((lams k : ℝ) : 𝕜)) := by
  set p := minpoly 𝕜 T with hp_def
  have hp_ne : p ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  have hmon : p.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
  · -- 𝔽 = ℝ: factor over ℝ (4.16) and rule out quadratic factors with 7.26.
    set e := RCLike.realRingEquiv hI
    obtain ⟨c, m, M, lams, bs, cs, hdisc, hfact⟩ :=
      LADR.Chapter_4.real_polynomial_factorization (p.map (e : 𝕜 →+* ℝ))
        ((Polynomial.map_ne_zero_iff e.injective).mpr hp_ne)
    have hfact' : p = C (c : 𝕜) * (∏ k, (X - C ((lams k : ℝ) : 𝕜))) *
        ∏ k, (X ^ 2 + C ((bs k : ℝ) : 𝕜) * X + C ((cs k : ℝ) : 𝕜)) := by
      have := congrArg (Polynomial.map (e.symm : ℝ →+* 𝕜)) hfact
      rw [Polynomial.map_map, show ((e.symm : ℝ →+* 𝕜).comp (e : 𝕜 →+* ℝ)) = RingHom.id 𝕜 from
        RingHom.ext e.symm_apply_apply, Polynomial.map_id] at this
      rw [this]
      simp [Polynomial.map_prod, e]
    clear hfact
    have hM : M = 0 := by
      by_contra hM0
      set k0 : Fin M := ⟨0, Nat.pos_of_ne_zero hM0⟩
      set q : 𝕜[X] := X ^ 2 + C ((bs k0 : ℝ) : 𝕜) * X + C ((cs k0 : ℝ) : 𝕜) with hq_def
      obtain ⟨s, hps⟩ : q ∣ p := by
        rw [hfact']
        exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ k0)) _
      have hq_deg : q.natDegree = 2 := by rw [hq_def]; compute_degree!
      have hq_ne : q ≠ 0 := fun h => by rw [h, natDegree_zero] at hq_deg; omega
      have hs_ne : s ≠ 0 := fun h => hp_ne (by rw [hps, h, mul_zero])
      have hqT : aeval T q = T ∘ₗ T + ((bs k0 : ℝ) : 𝕜) • T + ((cs k0 : ℝ) : 𝕜) • LinearMap.id := by
        simp [hq_def, pow_two, Module.End.mul_eq_comp, Algebra.algebraMap_eq_smul_one,
          Module.End.one_eq_id]
      have hinv := quadratic_isInvertible T hT (bs k0) (cs k0) (hdisc k0)
      rw [← hqT] at hinv
      have hsT : aeval T s = 0 := by
        have h0 : aeval T s ∘ₗ aeval T q = 0 := by
          rw [← Module.End.mul_eq_comp, ← map_mul, mul_comm, ← hps, hp_def, minpoly.aeval]
        rw [← LinearMap.comp_id (aeval T s), ← hinv.comp_inv, ← LinearMap.comp_assoc, h0,
          LinearMap.zero_comp]
      have h1 := Polynomial.natDegree_le_of_dvd (minpoly.dvd 𝕜 T hsT) hs_ne
      have h2 := Polynomial.natDegree_mul hq_ne hs_ne
      rw [← hps, hq_deg] at h2
      rw [← hp_def] at h1
      omega
    subst hM
    rw [show (∏ k : Fin 0, (X ^ 2 + C ((bs k : ℝ) : 𝕜) * X + C ((cs k : ℝ) : 𝕜))) = 1 from
      Finset.prod_of_isEmpty _, mul_one] at hfact'
    have hc : (c : 𝕜) = 1 := by
      have := hmon.leadingCoeff
      rw [hfact', leadingCoeff_mul, leadingCoeff_C,
        (monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _).leadingCoeff, mul_one] at this
      exact this
    exact ⟨m, lams, by rw [hfact', hc, C_1, one_mul]⟩
  · -- 𝔽 = ℂ: split by 4.13; the zeros are eigenvalues (5.27(a)), hence real (7.12).
    set e := RCLike.complexRingEquiv hI
    have hsplit : p.Splits := by
      have h := (IsAlgClosed.splits (p.map (e : 𝕜 →+* ℂ))).map (e.symm : ℂ →+* 𝕜)
      rwa [Polynomial.map_map, show ((e.symm : ℂ →+* 𝕜).comp (e : 𝕜 →+* ℂ)) = RingHom.id 𝕜 from
        RingHom.ext e.symm_apply_apply, Polynomial.map_id] at h
    obtain ⟨m, γ, hγ, -⟩ := LADR.Section_5C.monic_splits_eq_prod_fin hmon hsplit
    have hreal : ∀ k, ((RCLike.re (γ k) : ℝ) : 𝕜) = γ k := by
      intro k
      have hroot : p.IsRoot (γ k) := by
        rw [hγ, IsRoot, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
      have hev := (LADR.Section_5B.isEigenvalue_iff_isRoot T (γ k)).mpr hroot
      exact RCLike.conj_eq_iff_re.mp (LADR.Section_7A.eigenvalue_real T hT hev)
    exact ⟨m, fun k => RCLike.re (γ k), by rw [hγ]; simp only [hreal]⟩

/-! Conditions (b) and (c) of the spectral theorems.

Axler states 7.29 and 7.31 as three-way equivalences that differ only in their
first condition (self-adjoint over {lit}`ℝ`, normal over {lit}`ℂ`); conditions
(b) and (c) are identical, so we name them once and reuse them for both. -/

/-- Condition (b) of 7.29/7.31: {lit}`T` has a diagonal matrix with respect to
some orthonormal basis of {lit}`V`. -/
def HasDiagonalMatrix (T : V →ₗ[𝕜] V) : Prop :=
  ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V),
    (LinearMap.toMatrixOrthonormal e T).IsDiag

/-- Condition (c) of 7.29/7.31: {lit}`V` has an orthonormal basis consisting of
eigenvectors of {lit}`T`. -/
def HasOrthonormalEigenbasis (T : V →ₗ[𝕜] V) : Prop :=
  ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V), ∀ i, ∃ μ : 𝕜, HasEigenvector T μ (e i)

omit [FiniteDimensional 𝕜 V] in
/-- A vector of an orthonormal basis satisfying {lit}`T (e i) = μ • e i` really is an
eigenvector: basis vectors are nonzero. -/
theorem hasEigenvector_of_orthonormalBasis {n : ℕ} {T : V →ₗ[𝕜] V}
    (e : OrthonormalBasis (Fin n) 𝕜 V) {μ : 𝕜} {i : Fin n} (h : T (e i) = μ • e i) :
    HasEigenvector T μ (e i) :=
  Module.End.hasEigenvector_iff.mpr
    ⟨Module.End.mem_eigenspace_iff.mpr h, e.orthonormal.ne_zero i⟩

/-- For a *fixed* orthonormal basis, "diagonal matrix" and "basis of eigenvectors"
say the same thing. This is the equivalence of (b) and (c), which Axler notes
"follows from the definitions". -/
theorem isDiag_toMatrixOrthonormal_iff {n : ℕ} (T : V →ₗ[𝕜] V)
    (e : OrthonormalBasis (Fin n) 𝕜 V) :
    (LinearMap.toMatrixOrthonormal e T).IsDiag ↔ ∀ i, ∃ μ : 𝕜, HasEigenvector T μ (e i) := by
  constructor
  · intro hd i
    refine ⟨⟪e i, T (e i)⟫_𝕜, Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr ?_, e.orthonormal.ne_zero i⟩⟩
    conv_lhs => rw [← e.sum_repr' (T (e i))]
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rw [← LinearMap.toMatrixOrthonormal_apply_apply e T j i, hd hji, zero_smul]
  · intro he i j hij
    obtain ⟨μ, hμ⟩ := he j
    rw [LinearMap.toMatrixOrthonormal_apply_apply, hμ.apply_eq_smul, inner_smul_right,
      e.orthonormal.2 hij, mul_zero]

/-- {lit}`HasDiagonalMatrix` and {lit}`HasOrthonormalEigenbasis` are equivalent
over any {lit}`𝕜` — the (b) ⟺ (c) half of both spectral theorems. -/
theorem hasDiagonalMatrix_iff_hasOrthonormalEigenbasis (T : V →ₗ[𝕜] V) :
    HasDiagonalMatrix T ↔ HasOrthonormalEigenbasis T := by
  constructor
  · rintro ⟨n, e, hd⟩
    exact ⟨n, e, (isDiag_toMatrixOrthonormal_iff T e).mp hd⟩
  · rintro ⟨n, e, he⟩
    exact ⟨n, e, (isDiag_toMatrixOrthonormal_iff T e).mpr he⟩

/-- A diagonal matrix, read back through the star-algebra isomorphism
{name}`LinearMap.toMatrixOrthonormal`, is what makes conditions (b) ⟹ (a) work in
both spectral theorems: over {lit}`ℝ` it forces self-adjointness, over {lit}`ℂ`
normality. This is the shared "the matrix is {lit}`diagonal d`" step. -/
theorem exists_diagonal_of_hasDiagonalMatrix {T : V →ₗ[𝕜] V} (h : HasDiagonalMatrix T) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V) (d : Fin n → 𝕜),
      LinearMap.toMatrixOrthonormal e T = Matrix.diagonal d := by
  obtain ⟨n, e, hd⟩ := h
  exact ⟨n, e, _, ((Matrix.isDiag_iff_diagonal_diag _).mp hd).symm⟩

omit [FiniteDimensional 𝕜 V] in
/-- The (a) ⟹ (b) direction of both spectral theorems starts from an orthonormal
basis {lit}`e` for which {lit}`T` is upper-triangular, in the form
{lit}`T eⱼ ∈ span(e₁, …, eⱼ)` (5.39). Orthonormality then makes the entries below
the diagonal vanish: {lit}`⟨eᵢ, T eⱼ⟩ = 0` for {lit}`j < i`. -/
theorem inner_eq_zero_of_upperTriangular {n : ℕ} (T : V →ₗ[𝕜] V)
    (e : OrthonormalBasis (Fin n) 𝕜 V)
    (hUT : ∀ k, T (e k) ∈ Submodule.span 𝕜 (e '' {i | i ≤ k})) {i j : Fin n} (hji : j < i) :
    ⟪e i, T (e j)⟫_𝕜 = 0 := by
  have hle : Submodule.span 𝕜 (e '' {l | l ≤ j}) ≤ (𝕜 ∙ e i)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨l, hlj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact e.orthonormal.2 (fun h => absurd (h ▸ hlj) (not_le.mpr hji))
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp (hle (hUT j))

/-- The (a) ⟹ (b) argument of 7.29: a self-adjoint operator has a diagonal matrix
with respect to some orthonormal basis. By 7.27 and 6.37, {lit}`T` has an
upper-triangular matrix with respect to some orthonormal basis; with respect to that
basis the matrix of {lit}`T*` is the conjugate transpose of the matrix of {lit}`T`, and
{lit}`T* = T`, so the entries above the diagonal vanish as well as those below.

Axler states 7.29 for {lit}`𝔽 = ℝ` (over {lit}`ℂ`, self-adjoint operators are normal and
7.31 applies), but this argument works verbatim over either field, since 7.27 and 6.37
do. We record it over {lit}`𝕜` so later sections can cite "the spectral theorem" for a
self-adjoint operator without splitting on {lit}`𝔽`. -/
@[avoiding LinearMap.IsSymmetric.eigenvectorBasis, LinearMap.IsSymmetric.eigenvalues]
theorem hasDiagonalMatrix_of_isSymmetric (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) :
    HasDiagonalMatrix T := by
  obtain ⟨m, lams, hfact⟩ := minpoly_isSymmetric_eq_prod T hT
  obtain ⟨n, e, he, hUT⟩ := (LADR.Section_6B.exists_orthonormal_upperTriangular_iff_minpoly T).mpr
    ⟨m, fun k => ((lams k : ℝ) : 𝕜), hfact⟩
  have hflag : ∀ k, T (e k) ∈ Submodule.span 𝕜 (e '' {i | i ≤ k}) :=
    ((LADR.Section_5C.tfae_upperTriangular he T).out 1 3).mp hUT
  refine ⟨n, e, fun i j hij => ?_⟩
  show LinearMap.toMatrixOrthonormal e T i j = 0
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  rcases lt_or_gt_of_ne hij with h | h
  · -- above the diagonal: ⟨eᵢ, T eⱼ⟩ = ⟨T eᵢ, eⱼ⟩ = conj ⟨eⱼ, T eᵢ⟩, a below-diagonal entry
    rw [← hT, ← inner_conj_symm, inner_eq_zero_of_upperTriangular T e hflag h, map_zero]
  · exact inner_eq_zero_of_upperTriangular T e hflag h

/-- The spectral theorem for a self-adjoint operator, in the form later sections use:
an orthonormal basis of eigenvectors, with real eigenvalues. The eigenvalue of
{lit}`eᵢ` is the diagonal entry {lit}`⟨eᵢ, T eᵢ⟩`, which is real because {lit}`T` is
self-adjoint. -/
@[avoiding LinearMap.IsSymmetric.eigenvectorBasis, LinearMap.IsSymmetric.eigenvalues]
theorem exists_orthonormalBasis_eigenvectors (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) 𝕜 V) (μ : Fin n → ℝ),
      ∀ i, T (e i) = ((μ i : ℝ) : 𝕜) • e i := by
  obtain ⟨n, e, hd⟩ := hasDiagonalMatrix_of_isSymmetric T hT
  refine ⟨n, e, fun i => RCLike.re ⟪e i, T (e i)⟫_𝕜, fun i => ?_⟩
  have hreal : ((RCLike.re ⟪e i, T (e i)⟫_𝕜 : ℝ) : 𝕜) = ⟪e i, T (e i)⟫_𝕜 :=
    RCLike.conj_eq_iff_re.mp (by rw [inner_conj_symm, hT])
  rw [hreal]
  conv_lhs => rw [← e.sum_repr' (T (e i))]
  refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rw [← LinearMap.toMatrixOrthonormal_apply_apply e T j i, hd hji, zero_smul]

/-- The same, indexed by {lit}`Fin (dim V)` and with the eigenvalues listed in
decreasing order (reorder the basis by a sorting permutation). This is the form in
which 7.65 lists singular values. -/
theorem exists_orthonormalBasis_eigenvectors_antitone (T : V →ₗ[𝕜] V) (hT : T.IsSymmetric) :
    ∃ (e : OrthonormalBasis (Fin (finrank 𝕜 V)) 𝕜 V) (μ : Fin (finrank 𝕜 V) → ℝ),
      Antitone μ ∧ ∀ i, T (e i) = ((μ i : ℝ) : 𝕜) • e i := by
  obtain ⟨n, e, μ, he⟩ := exists_orthonormalBasis_eigenvectors T hT
  have hn : n = finrank 𝕜 V := by
    simpa using (Module.finrank_eq_card_basis e.toBasis).symm
  subst hn
  set σ := Tuple.sort (fun i => -μ i)
  refine ⟨e.reindex σ.symm, μ ∘ σ, fun i j hij => ?_, fun i => ?_⟩
  · have := Tuple.monotone_sort (fun i => -μ i) hij
    simpa using this
  · simp [OrthonormalBasis.reindex_apply, he]

/-! 7.29 Real spectral theorem

For {lit}`𝔽 = ℝ` and {lit}`T ∈ ℒ(V)` the following are equivalent:
(a) {lit}`T` is self-adjoint; (b) {lit}`T` has a diagonal matrix with respect to
some orthonormal basis of {lit}`V`; (c) {lit}`V` has an orthonormal basis
consisting of eigenvectors of {lit}`T`.

Following Axler: (a) ⟹ (b) combines 7.27 and 6.37 to get an orthonormal basis
for which the matrix of {lit}`T` is upper-triangular; since {lit}`T* = T` the matrix
equals its transpose, so the entries above the diagonal vanish too. (b) ⟹ (a) is
the observation that a real diagonal matrix equals its own transpose. (b) ⟺ (c)
follows from the definitions. -/

/-- 7.29 (real spectral theorem) The three-way equivalence. -/
theorem tfae_real_spectral {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) :
    [T.IsSymmetric, HasDiagonalMatrix T, HasOrthonormalEigenbasis T].TFAE := by
  tfae_have 1 → 2 := hasDiagonalMatrix_of_isSymmetric T
  tfae_have 2 ↔ 3 := hasDiagonalMatrix_iff_hasOrthonormalEigenbasis T
  tfae_have 2 → 1 := by
    intro h
    obtain ⟨n, e, d, hdiag⟩ := exists_diagonal_of_hasDiagonalMatrix h
    rw [LinearMap.isSymmetric_iff_isSelfAdjoint, isSelfAdjoint_iff]
    have key : LinearMap.toMatrixOrthonormal e (star T) = LinearMap.toMatrixOrthonormal e T := by
      rw [map_star, hdiag, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        star_trivial]
    exact (LinearMap.toMatrixOrthonormal e).injective key
  tfae_finish

/-- 7.29 (a) ⟹ (c), the direction usually cited on its own: every self-adjoint
operator on a real inner product space has an orthonormal basis of eigenvectors.
Read off the equivalence, following the {name}`LADR.Section_3D.tfae_isInvertible`
pattern. -/
theorem spectral_orthonormal_eigenbasis {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V)
    (hT : T.IsSymmetric) : HasOrthonormalEigenbasis T :=
  ((tfae_real_spectral T).out 1 3).mp hT

/-! # Complex Spectral Theorem -/

/-! 7.30 Example: an orthonormal basis of eigenvectors (real case). For the
self-adjoint operator on {lit}`ℝ³` with matrix {lit}`!![14,-13,8; -13,14,8; 8,8,-7]`,
the vectors {lit}`(1,-1,0), (1,1,1), (1,1,-2)` (normalized by {lit}`√2, √3, √6`)
form an orthonormal basis of eigenvectors, with eigenvalues {lit}`27, 9, -15`. This
illustrates the real spectral theorem 7.29.

We verify all of Axler's claims: the matrix equals its transpose, so {lit}`T` is
self-adjoint ({lit}`A_7_30_isHermitian`, {lit}`A_7_30_isSymmetric`); each
eigenvalue equation, together with the pairwise orthogonality and squared norms of
the three vectors; that the normalized vectors form an orthonormal basis
({lit}`b_7_30`); and that the matrix of {lit}`T` with respect to that basis is the
diagonal matrix {lit}`diag(27, 9, -15)` ({lit}`A_7_30_toMatrixOrthonormal`). -/

section Example_7_30

open scoped Matrix

/-- Real scalar inner product is multiplication (used to compute coordinate inner
products below). -/
private theorem rinner (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by rw [real_inner_comm]; rfl

/-- The self-adjoint matrix of Example 7.30. -/
noncomputable def A_7_30 : Matrix (Fin 3) (Fin 3) ℝ := !![14, -13, 8; -13, 14, 8; 8, 8, -7]

/-- The eigenvector {lit}`(1, -1, 0)` (eigenvalue {lit}`27`). -/
noncomputable def v_7_30_a : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm ![1, -1, 0]
/-- The eigenvector {lit}`(1, 1, 1)` (eigenvalue {lit}`9`). -/
noncomputable def v_7_30_b : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm ![1, 1, 1]
/-- The eigenvector {lit}`(1, 1, -2)` (eigenvalue {lit}`-15`). -/
noncomputable def v_7_30_c : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 _).symm ![1, 1, -2]

theorem A_7_30_eigenvalue_27 : Matrix.toEuclideanLin A_7_30 v_7_30_a = (27 : ℝ) • v_7_30_a := by
  ext i; fin_cases i <;> simp [A_7_30, v_7_30_a, Matrix.toEuclideanLin] <;> norm_num
theorem A_7_30_eigenvalue_9 : Matrix.toEuclideanLin A_7_30 v_7_30_b = (9 : ℝ) • v_7_30_b := by
  ext i; fin_cases i <;> simp [A_7_30, v_7_30_b, Matrix.toEuclideanLin] <;> norm_num
theorem A_7_30_eigenvalue_neg15 :
    Matrix.toEuclideanLin A_7_30 v_7_30_c = (-15 : ℝ) • v_7_30_c := by
  ext i; fin_cases i <;> simp [A_7_30, v_7_30_c, Matrix.toEuclideanLin] <;> norm_num

theorem v_7_30_ortho_ab : ⟪v_7_30_a, v_7_30_b⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]; simp [v_7_30_a, v_7_30_b, Fin.sum_univ_three]
theorem v_7_30_ortho_ac : ⟪v_7_30_a, v_7_30_c⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]; simp [v_7_30_a, v_7_30_c, Fin.sum_univ_three]
theorem v_7_30_ortho_bc : ⟪v_7_30_b, v_7_30_c⟫_ℝ = 0 := by
  rw [PiLp.inner_apply]; simp [v_7_30_b, v_7_30_c, Fin.sum_univ_three]; norm_num
theorem v_7_30_normSq_a : ⟪v_7_30_a, v_7_30_a⟫_ℝ = 2 := by
  rw [PiLp.inner_apply]; simp [v_7_30_a, Fin.sum_univ_three]; norm_num
theorem v_7_30_normSq_b : ⟪v_7_30_b, v_7_30_b⟫_ℝ = 3 := by
  rw [PiLp.inner_apply]; simp [v_7_30_b, Fin.sum_univ_three]; norm_num
theorem v_7_30_normSq_c : ⟪v_7_30_c, v_7_30_c⟫_ℝ = 6 := by
  rw [PiLp.inner_apply]; simp [v_7_30_c, Fin.sum_univ_three]; norm_num

/-- Axler's first claim in 7.30: the matrix has real entries and equals its
transpose, hence is Hermitian. -/
theorem A_7_30_isHermitian : Matrix.IsHermitian A_7_30 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A_7_30]

/-- ... and therefore {lit}`T` is self-adjoint, which is what makes 7.29 apply. -/
theorem A_7_30_isSymmetric : (Matrix.toEuclideanLin A_7_30).IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr A_7_30_isHermitian

/-- The three eigenvectors normalized by {lit}`√2, √3, √6`, as in the book. -/
noncomputable def e_7_30 : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![(Real.sqrt 2)⁻¹ • v_7_30_a, (Real.sqrt 3)⁻¹ • v_7_30_b, (Real.sqrt 6)⁻¹ • v_7_30_c]

theorem e_7_30_orthonormal : Orthonormal ℝ e_7_30 := by
  have s2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have s3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have s6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have n2 : Real.sqrt 2 ≠ 0 := by positivity
  have n3 : Real.sqrt 3 ≠ 0 := by positivity
  have n6 : Real.sqrt 6 ≠ 0 := by positivity
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [e_7_30, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm v_7_30_a v_7_30_b,
      real_inner_comm v_7_30_a v_7_30_c, real_inner_comm v_7_30_b v_7_30_c,
      v_7_30_ortho_ab, v_7_30_ortho_ac, v_7_30_ortho_bc, v_7_30_normSq_a, v_7_30_normSq_b,
      v_7_30_normSq_c] <;>
    norm_num <;> (field_simp; linarith [s2, s3, s6])

/-- The orthonormal basis of eigenvectors of Example 7.30. -/
noncomputable def b_7_30 : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
  (basisOfOrthonormalOfCardEqFinrank e_7_30_orthonormal (by simp)).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact e_7_30_orthonormal)

@[simp] theorem b_7_30_apply (i : Fin 3) : b_7_30 i = e_7_30 i := by
  rw [b_7_30, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

/-- Each basis vector is an eigenvector, with the same eigenvalue as the
unnormalized vector it was scaled from. -/
theorem b_7_30_eigenvector (i : Fin 3) :
    Matrix.toEuclideanLin A_7_30 (b_7_30 i) = (![27, 9, -15] : Fin 3 → ℝ) i • b_7_30 i := by
  have scale : ∀ (c μ : ℝ) (v : EuclideanSpace ℝ (Fin 3)),
      Matrix.toEuclideanLin A_7_30 v = μ • v →
      Matrix.toEuclideanLin A_7_30 (c • v) = μ • (c • v) := by
    intro c μ v hv
    rw [map_smul, hv, smul_comm]
  fin_cases i <;> simp only [b_7_30_apply, e_7_30, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  · exact scale _ _ _ A_7_30_eigenvalue_27
  · exact scale _ _ _ A_7_30_eigenvalue_9
  · exact scale _ _ _ A_7_30_eigenvalue_neg15

/-- Axler's second claim in 7.30: with respect to this orthonormal basis the
matrix of {lit}`T` is the diagonal matrix {lit}`diag(27, 9, -15)`. -/
theorem A_7_30_toMatrixOrthonormal :
    LinearMap.toMatrixOrthonormal b_7_30 (Matrix.toEuclideanLin A_7_30)
      = Matrix.diagonal ![27, 9, -15] := by
  ext i j
  rw [LinearMap.toMatrixOrthonormal_apply_apply, b_7_30_eigenvector j, inner_smul_right,
    orthonormal_iff_ite.mp b_7_30.orthonormal i j, Matrix.diagonal_apply]
  split_ifs with h
  · subst h; ring
  · ring

end Example_7_30

/-! 7.31 Complex spectral theorem

For {lit}`𝔽 = ℂ`, an operator {lit}`T` is normal if and only if {lit}`V` has an
orthonormal basis consisting of eigenvectors of {lit}`T`. Axler's proof runs
through Schur's theorem (6.38, from
{module -checked}`LinearAlgebraDoneRightLean.Section_6B`): a normal operator that
is upper-triangular with respect to an orthonormal basis is in fact diagonal. -/

/-- A normal operator that is upper-triangular with respect to an orthonormal
basis {lit}`e` has a diagonal matrix with respect to {lit}`e`. The proof compares
{lit}`‖T eₖ‖² = ∑ᵢ ‖⟨eᵢ, T eₖ⟩‖²` (column {lit}`k`) with
{lit}`‖T* eₖ‖² = ∑ᵢ ‖⟨eₖ, T eᵢ⟩‖²` (row {lit}`k`); equality (7.20) plus an
induction from the top row forces every strictly-upper entry to vanish. -/
theorem normal_ut_diagonal {n : ℕ} (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (e : OrthonormalBasis (Fin n) 𝕜 V)
    (hUT : ∀ k, T (e k) ∈ Submodule.span 𝕜 (e '' {i | i ≤ k})) :
    (LinearMap.toMatrixOrthonormal e T).IsDiag := by
  set a : Fin n → Fin n → 𝕜 := fun i j => ⟪e i, T (e j)⟫_𝕜 with ha
  have hUTz : ∀ i j : Fin n, j < i → a i j = 0 := fun i j hji =>
    inner_eq_zero_of_upperTriangular T e hUT hji
  have hParsT : ∀ k, ‖T (e k)‖ ^ 2 = ∑ i, ‖a i k‖ ^ 2 := by
    intro k
    simp only [ha]
    exact (OrthonormalBasis.sum_sq_norm_inner_right e (T (e k))).symm
  have hParsA : ∀ k, ‖T† (e k)‖ ^ 2 = ∑ i, ‖a k i‖ ^ 2 := by
    intro k
    rw [← OrthonormalBasis.sum_sq_norm_inner_right e (T† (e k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha]
    rw [LinearMap.adjoint_inner_right]
    congr 1
    exact norm_inner_symm (T (e i)) (e k)
  have hN2 : ∀ v, ‖T v‖ = ‖T† v‖ := (LADR.Section_7A.normal_iff_norm T).mp hN
  have hQaux : ∀ m : ℕ, ∀ k : Fin n, k.val = m → ∀ j : Fin n, k < j → a k j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m IH =>
      intro k hk j hkj
      have IHk : ∀ i : Fin n, i < k → a i k = 0 := fun i hik =>
        IH i.val (by rw [← hk]; exact Fin.lt_def.mp hik) i rfl k hik
      have hcol : ∑ i, ‖a i k‖ ^ 2 = ‖a k k‖ ^ 2 := by
        rw [Finset.sum_eq_single k]
        · intro i _ hik
          rcases lt_or_gt_of_ne hik with h | h
          · rw [IHk i h, norm_zero]; ring
          · rw [hUTz i k h, norm_zero]; ring
        · intro h; exact absurd (Finset.mem_univ k) h
      have hnorm_eq : ∑ i, ‖a i k‖ ^ 2 = ∑ i, ‖a k i‖ ^ 2 := by
        rw [← hParsT k, ← hParsA k, hN2 (e k)]
      have hsum_eq : ∑ i, ‖a k i‖ ^ 2 = ‖a k k‖ ^ 2 := by rw [← hnorm_eq, hcol]
      have hzero : ∑ i ∈ Finset.univ.erase k, ‖a k i‖ ^ 2 = 0 := by
        have hae := Finset.add_sum_erase Finset.univ (fun i => ‖a k i‖ ^ 2) (Finset.mem_univ k)
        rw [hsum_eq] at hae
        linarith
      have hjmem : j ∈ Finset.univ.erase k :=
        Finset.mem_erase.mpr ⟨(ne_of_lt hkj).symm, Finset.mem_univ j⟩
      have hj0 : ‖a k j‖ ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hzero j hjmem
      have hjn : ‖a k j‖ = 0 := by nlinarith [norm_nonneg (a k j)]
      rwa [norm_eq_zero] at hjn
  have hQ : ∀ k : Fin n, ∀ j : Fin n, k < j → a k j = 0 := fun k => hQaux k.val k rfl
  intro i j hij
  rw [LinearMap.toMatrixOrthonormal_apply_apply]
  rcases lt_or_gt_of_ne hij with h | h
  · exact hQ i j h
  · exact hUTz i j h

/-- 7.31 (complex spectral theorem) The three-way equivalence: for {lit}`𝔽 = ℂ`,
{lit}`T` is normal iff it has a diagonal matrix with respect to some orthonormal
basis iff {lit}`V` has an orthonormal basis of eigenvectors of {lit}`T`.
Following Axler: (a) ⟹ (b) applies Schur's theorem (6.38) and then
{name}`normal_ut_diagonal`; (b) ⟹ (a) is the observation that a diagonal matrix
commutes with its conjugate transpose; (b) ⟺ (c) follows from the definitions
({name}`hasDiagonalMatrix_iff_hasOrthonormalEigenbasis`). -/
theorem tfae_complex_spectral {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) :
    [IsStarNormal T, HasDiagonalMatrix T, HasOrthonormalEigenbasis T].TFAE := by
  tfae_have 1 → 2 := by
    intro hN
    obtain ⟨n, e, he, hUT⟩ := LADR.Section_6B.exists_orthonormal_upperTriangular_complex T
    have hflag : ∀ k, T (e k) ∈ Submodule.span ℂ (e '' {i | i ≤ k}) :=
      ((LADR.Section_5C.tfae_upperTriangular he T).out 1 3).mp hUT
    exact ⟨n, e, normal_ut_diagonal T hN e hflag⟩
  tfae_have 2 ↔ 3 := hasDiagonalMatrix_iff_hasOrthonormalEigenbasis T
  tfae_have 2 → 1 := by
    intro h
    obtain ⟨n, e, d, hdiag⟩ := exists_diagonal_of_hasDiagonalMatrix h
    have key : LinearMap.toMatrixOrthonormal e (star T * T)
        = LinearMap.toMatrixOrthonormal e (T * star T) := by
      rw [map_mul, map_mul, map_star, hdiag, Matrix.star_eq_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    exact ⟨(LinearMap.toMatrixOrthonormal e).injective key⟩
  tfae_finish

/-- 7.31 (a) ⟹ (c), the direction usually cited on its own: every normal operator
on a finite-dimensional complex inner product space has an orthonormal basis of
eigenvectors, with the eigenvalue of {lit}`eₖ` the diagonal entry
{lit}`⟨eₖ, T eₖ⟩`. Read off the equivalence. -/
theorem complex_spectral {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : W →ₗ[ℂ] W) (hN : IsStarNormal T) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ W),
      ∀ k, T (e k) = ⟪e k, T (e k)⟫_ℂ • e k := by
  obtain ⟨n, e, hd⟩ := ((tfae_complex_spectral T).out 1 2).mp hN
  refine ⟨n, e, fun k => ?_⟩
  conv_lhs => rw [← e.sum_repr' (T (e k))]
  refine Finset.sum_eq_single k (fun j _ hjk => ?_) (fun h => absurd (Finset.mem_univ k) h)
  rw [← LinearMap.toMatrixOrthonormal_apply_apply e T j k, hd hjk, zero_smul]

/-! 7.33 Example: an orthonormal basis of eigenvectors (complex case). For the
normal operator {lit}`T(w, z) = (2w - 3z, 3w + 2z)` on {lit}`ℂ²` (matrix
{lit}`!![2,-3; 3,2]`), the vectors {lit}`(i, 1), (-i, 1)` (normalized by {lit}`√2`)
form an orthonormal basis of eigenvectors, with eigenvalues {lit}`2 + 3i, 2 - 3i`.
This illustrates the complex spectral theorem 7.31. -/

section Example_7_33

open scoped Matrix

/-- The normal matrix of Example 7.33. -/
noncomputable def A_7_33 : Matrix (Fin 2) (Fin 2) ℂ := !![2, -3; 3, 2]

/-- The eigenvector {lit}`(i, 1)` (eigenvalue {lit}`2 + 3i`). -/
noncomputable def v_7_33_a : EuclideanSpace ℂ (Fin 2) := (WithLp.equiv 2 _).symm ![Complex.I, 1]
/-- The eigenvector {lit}`(-i, 1)` (eigenvalue {lit}`2 - 3i`). -/
noncomputable def v_7_33_b : EuclideanSpace ℂ (Fin 2) := (WithLp.equiv 2 _).symm ![-Complex.I, 1]

theorem A_7_33_eigenvalue_add :
    Matrix.toEuclideanLin A_7_33 v_7_33_a = (2 + 3 * Complex.I) • v_7_33_a := by
  ext i; fin_cases i <;> simp [A_7_33, v_7_33_a, Matrix.toEuclideanLin, Complex.ext_iff]
theorem A_7_33_eigenvalue_sub :
    Matrix.toEuclideanLin A_7_33 v_7_33_b = (2 - 3 * Complex.I) • v_7_33_b := by
  ext i; fin_cases i <;> simp [A_7_33, v_7_33_b, Matrix.toEuclideanLin, Complex.ext_iff]

theorem v_7_33_ortho : ⟪v_7_33_a, v_7_33_b⟫_ℂ = 0 := by
  rw [PiLp.inner_apply]; simp [v_7_33_a, v_7_33_b, Fin.sum_univ_two]
theorem v_7_33_normSq_a : ⟪v_7_33_a, v_7_33_a⟫_ℂ = 2 := by
  rw [PiLp.inner_apply]; simp [v_7_33_a, Fin.sum_univ_two, Complex.ext_iff]; norm_num
theorem v_7_33_normSq_b : ⟪v_7_33_b, v_7_33_b⟫_ℂ = 2 := by
  rw [PiLp.inner_apply]; simp [v_7_33_b, Fin.sum_univ_two, Complex.ext_iff]; norm_num

end Example_7_33

/-! # Exercises 7B -/

/-- 7B.1 A normal operator on a complex inner product space is self-adjoint iff
all its eigenvalues are real. -/
theorem exercise_7B_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    LinearMap.IsSymmetric T ↔ ∀ μ : ℂ, HasEigenvalue T μ → conj μ = μ := by
  -- => Tv = λv, take λ ‖v‖^2 = ⟪λv, v⟫ = ⟪Tv, v⟫ = ⟪v, Tv⟫ = ⟪v, λ v⟫ = conj λ ‖v‖^2, so
  -- so λ = conj λ, i.e., λ is real. (this was proven in chapter 6 ok to import)
  -- <= take a basis of eigenvectors (possible by the spectral theorem for normal operators) and check that T is symmetric on each eigenvector)
  -- If Tei = λi ei, then T*ei = conj λi ei = λi ei (by 7.21e))
  -- since T and T* agree on the basis vectors by linearity, they must be equal on the whole space.
  constructor
  · exact fun hT μ hμ => LADR.Section_7A.eigenvalue_real T hT hμ
  · intro hreal
    obtain ⟨n, e, he⟩ := complex_spectral T hN
    rw [LADR.Section_7A.isSelfAdjoint_iff]
    refine e.toBasis.ext fun k => ?_
    set μ := ⟪e k, T (e k)⟫_ℂ
    have hμ : HasEigenvalue T μ :=
      Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_of_orthonormalBasis e (he k))
    rw [OrthonormalBasis.coe_toBasis, (LADR.Section_7A.eigenvector_adjoint hN (e k) μ).mp (he k),
      hreal μ hμ, ← he k]

/-- 7B.2 A normal operator on a complex inner product space with only one
eigenvalue is a scalar multiple of the identity. -/
theorem exercise_7B_2 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T)
    (μ : ℂ) (hμ : ∀ ν : ℂ, HasEigenvalue T ν ↔ ν = μ) :
    T = μ • LinearMap.id := by
  -- pick an eigenvector basis by spectral theorem for normal operators
  -- T in this basis is a diagonal matrix that has the eigenvalues on the diagonal
  -- since they all equal μ the matrix equals μ times the identity matrix.
  -- if the matrix is I times μ, then T = μ • LinearMap.id
  obtain ⟨n, e, he⟩ := complex_spectral T hN
  refine e.toBasis.ext fun k => ?_
  have hk : ⟪e k, T (e k)⟫_ℂ = μ := (hμ _).mp
    (Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_of_orthonormalBasis e (he k)))
  rw [OrthonormalBasis.coe_toBasis, LinearMap.smul_apply, LinearMap.id_apply, he k, hk]

/-- 7B.3 For normal {lit}`T` on a complex inner product space, the eigenvalues lie
in {lit}`{0, 1}` iff {lit}`T = P_U` for some subspace {lit}`U`. -/
theorem exercise_7B_3 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    (∀ μ : ℂ, HasEigenvalue T μ → μ = 0 ∨ μ = 1) ↔
      ∃ U : Submodule ℂ V, (U.starProjection : V →ₗ[ℂ] V) = T := by
  -- => pick an eigenvector basis ei, and look at the diagonal matrix of eigenvalues
  -- take the U = span{e i | the eigenvalue of e i is 1}
  -- if λi = 1 then ei ∈ U, so P_U ei = ei = T ei;
  -- if λi = 0 then ei ⊥ ej for every ej spanning U, so ei ∈ U⊥ and P_U ei = 0 = T ei.
  -- since P_U agrees with T on the eigenvector basis, T = P_U.
  -- <= if P_U v = λ v with v ≠ 0, then P_U^2 v = P_U v, so λ^2 v = λ v,
  -- hence λ^2 = λ (cancel v ≠ 0), i.e. λ(λ - 1) = 0, so λ = 0 or λ = 1.
  constructor
  · intro h01
    obtain ⟨n, e, he⟩ := complex_spectral T hN
    set μ : Fin n → ℂ := fun k => ⟪e k, T (e k)⟫_ℂ with hμdef
    have hμ01 : ∀ k, μ k = 0 ∨ μ k = 1 := fun k => h01 _
      (Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_of_orthonormalBasis e (he k)))
    set U := Submodule.span ℂ (e '' {k | μ k = 1})
    refine ⟨U, e.toBasis.ext fun k => ?_⟩
    rw [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
    change _ = T (e k)
    rw [he k]
    change _ = μ k • e k
    rcases hμ01 k with h0 | h1
    · -- `e k` is orthogonal to every `e j` with `μ j = 1`, hence to `U`
      have hle : U ≤ (ℂ ∙ e k)ᗮ := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨j, hj, rfl⟩
        have hjk : j ≠ k := by rintro rfl; rw [Set.mem_ofPred_eq, h0] at hj; exact zero_ne_one hj
        exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
          (e.orthonormal.inner_eq_zero hjk)
      have hk : e k ∈ Uᗮ := fun u hu =>
        Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hu)
      rw [h0, zero_smul]
      exact (Submodule.starProjection_apply_eq_zero_iff U).mpr hk
    · rw [h1, one_smul]
      exact Submodule.starProjection_eq_self_iff.mpr (Submodule.subset_span ⟨k, h1, rfl⟩)
  · -- `P_U² = P_U`, so `P_U v = μ v` with `v ≠ 0` forces `μ² = μ`
    rintro ⟨U, rfl⟩ μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hPv : U.starProjection v = μ • v := hv.apply_eq_smul
    have hPP : U.starProjection (U.starProjection v) = U.starProjection v :=
      Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem U v)
    rw [hPv, map_smul, hPv, smul_smul] at hPP
    have hμμ : μ * μ = μ * 1 := by
      rw [mul_one]; exact smul_left_injective ℂ hv.2 hPP
    rcases mul_eq_mul_left_iff.mp hμμ with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- 7B.4 A normal operator on a complex inner product space is skew
({lit}`T* = −T`) iff all its eigenvalues are purely imaginary. -/
theorem exercise_7B_4 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    T† = -T ↔ ∀ μ : ℂ, HasEigenvalue T μ → μ.re = 0 := by
  -- => we shown that if μ eignevalue to T, then conj μ is eigenvalue to T†
  -- if T† = -T, then conj μ = -μ, so μ is purely imaginary
  -- <= by specral theorem, take an eigenvector basis,
  -- T ei = λi ei with λi purely imaginary, so conj λi = -λi.
  -- by 7.21(e), T† ei = conj λi ei = -λi ei = -T ei,
  -- so T† and -T agree on a basis, hence T† = -T.
  constructor
  · intro hadj μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have h1 := (LADR.Section_7A.eigenvector_adjoint hN v μ).mp hv.apply_eq_smul
    rw [hadj, LinearMap.neg_apply, hv.apply_eq_smul, ← neg_smul] at h1
    have h2 : -μ = conj μ := smul_left_injective ℂ hv.2 h1
    have h3 := congrArg Complex.re h2
    rw [Complex.neg_re, Complex.conj_re] at h3
    linarith
  · intro hre
    obtain ⟨n, e, he⟩ := complex_spectral T hN
    refine e.toBasis.ext fun k => ?_
    set μ := ⟪e k, T (e k)⟫_ℂ
    have hμ : HasEigenvalue T μ :=
      Module.End.hasEigenvalue_of_hasEigenvector (hasEigenvector_of_orthonormalBasis e (he k))
    have hconj : conj μ = -μ := Complex.ext (by simp [hre μ hμ]) (by simp)
    rw [OrthonormalBasis.coe_toBasis, (LADR.Section_7A.eigenvector_adjoint hN (e k) μ).mp (he k),
      LinearMap.neg_apply, hconj, neg_smul, he k]

/-- The counterexample for 7B.5: the matrix with rows {lit}`(1/2, 1/2, 0), (0, 1, 0), (0, 0, 2)`. -/
noncomputable def A_7B_5 : Matrix (Fin 3) (Fin 3) ℂ := !![1/2, 1/2, 0; 0, 1, 0; 0, 0, 2]
/-- The operator on {lit}`ℂ³` with matrix {name}`A_7B_5`. -/
noncomputable def T_7B_5 : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
  Matrix.toEuclideanLin A_7B_5
/-- The eigenvector {lit}`(1, 0, 0)` (eigenvalue {lit}`1/2`). -/
noncomputable def u_7B_5 : EuclideanSpace ℂ (Fin 3) := (WithLp.equiv 2 _).symm ![1, 0, 0]
/-- The eigenvector {lit}`(1, 1, 0)` (eigenvalue {lit}`1`). -/
noncomputable def v_7B_5 : EuclideanSpace ℂ (Fin 3) := (WithLp.equiv 2 _).symm ![1, 1, 0]
/-- The eigenvector {lit}`(0, 0, 1)` (eigenvalue {lit}`2`). -/
noncomputable def w_7B_5 : EuclideanSpace ℂ (Fin 3) := (WithLp.equiv 2 _).symm ![0, 0, 1]

theorem T_7B_5_u : T_7B_5 u_7B_5 = (1/2 : ℂ) • u_7B_5 := by
  ext i; fin_cases i <;> simp [T_7B_5, A_7B_5, u_7B_5, Matrix.toEuclideanLin]
theorem T_7B_5_v : T_7B_5 v_7B_5 = (1 : ℂ) • v_7B_5 := by
  ext i; fin_cases i <;> simp [T_7B_5, A_7B_5, v_7B_5, Matrix.toEuclideanLin]; norm_num
theorem T_7B_5_w : T_7B_5 w_7B_5 = (2 : ℂ) • w_7B_5 := by
  ext i; fin_cases i <;> simp [T_7B_5, A_7B_5, w_7B_5, Matrix.toEuclideanLin]
theorem inner_u_v_7B_5 : ⟪u_7B_5, v_7B_5⟫_ℂ = 1 := by
  rw [PiLp.inner_apply]; simp [u_7B_5, v_7B_5, Fin.sum_univ_three]

/-- {name}`T_7B_5` has the three distinct eigenvalues {lit}`1/2, 1, 2 = dim ℂ³`, so it is
diagonalizable by 5.58. -/
theorem isDiagonalizable_T_7B_5 : Section_5D.IsDiagonalizable T_7B_5 := by
  have h3 : finrank ℂ (EuclideanSpace ℂ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hev : ∀ μ : ℂ, ∀ x : EuclideanSpace ℂ (Fin 3), x ≠ 0 → T_7B_5 x = μ • x →
      HasEigenvalue T_7B_5 μ := fun μ x hx h =>
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr h, hx⟩
  have hne : ∀ f : Fin 3 → ℂ, f ≠ 0 →
      (WithLp.equiv 2 _).symm f ≠ (0 : EuclideanSpace ℂ (Fin 3)) :=
    fun f hf h => hf (by simpa using congrArg (WithLp.equiv 2 _) h)
  refine Section_5D.isDiagonalizable_of_card_eigenvalues T_7B_5
    (fun k => ![1/2, 1, 2] (k.cast h3)) ?_ fun k => ?_
  · intro a b hab
    apply Fin.cast_injective h3
    simp only at hab
    generalize a.cast h3 = a' at hab
    generalize b.cast h3 = b' at hab
    fin_cases a' <;> fin_cases b' <;> first | rfl | (exfalso; norm_num at hab)
  · generalize k.cast h3 = j
    fin_cases j
    · exact hev _ _ (hne _ (by simp)) T_7B_5_u
    · exact hev _ _ (hne _ (by simp)) T_7B_5_v
    · exact hev _ _ (hne _ (by simp)) T_7B_5_w

/-- 7B.5 Prove or give a counterexample: if {lit}`T ∈ ℒ(ℂ³)` is diagonalizable,
then {lit}`T` is normal (with respect to the usual inner product). -/
def exercise_7B_5 :
    Decidable (∀ T : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3),
      Section_5D.IsDiagonalizable T → IsStarNormal T) := by
  -- first line should be `apply isTrue` or `apply isFalse`
  apply isFalse
  -- in chapter 5 we characterized diagonalizeble as having a basis of eigenvectors.
  -- and in ch7, normal is characterized by having an orthonormal eigenvector basis.
  -- so construct a matrix with a basis of eigenvectors that is not orthonormal.
  -- take (1,1) and (1, 0) - the matrix (1/2 1/2; 0 1) has both with eigenvalues 1 and 0.5
  -- add a third vector to make it 3x3, for example (0,0,2)
  -- then the matrix with rows (1/2,1/2,0), (0,1,0), (0,0,2) is diagonalizable
  -- since it has E(1) = (1,1,0) and E(0.5) = (1,0,0) and E(2) = (0,0,1) which span V
  -- if it was normal, all it's eigenvectors for distinct eigenvalues would be orthogonal (7.22)
  -- but (1,1,0) and (1,0,0) are not orthogonal, so the matrix is not normal.
  intro h
  have hN := h T_7B_5 isDiagonalizable_T_7B_5
  have h0 := LADR.Section_7A.orthogonal_eigenvectors hN (by norm_num) T_7B_5_u T_7B_5_v
  rw [inner_u_v_7B_5] at h0
  exact one_ne_zero h0

/-- 7B.6 If {lit}`T` is normal on a complex inner product space and {lit}`T⁹ = T⁸`,
then {lit}`T` is self-adjoint and {lit}`T² = T`. -/
theorem exercise_7B_6 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) (h : T ^ 9 = T ^ 8) :
    LinearMap.IsSymmetric T ∧ T ^ 2 = T := by
  -- assume λ is eigenvalue of T, so Tv = λv for some v ≠ 0
  -- then λ^9 v = T^9 v = T^8 v = λ^8 v, which implies λ^9 = λ^8, hence λ = 0 or λ = 1
  -- since eigenvalues are real => self-adjoint (by ex1.)
  -- and T^2 = T follows from the fact that the eigenvalues are 0 or 1
  have hpow : ∀ (ν : ℂ) (v : V), T v = ν • v → ∀ m : ℕ, (T ^ m) v = ν ^ m • v := by
    intro ν v hv m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  -- every eigenvalue satisfies `ν⁹ = ν⁸`, hence is `0` or `1`
  have h01 : ∀ ν : ℂ, HasEigenvalue T ν → ν = 0 ∨ ν = 1 := by
    intro ν hν
    obtain ⟨v, hv⟩ := hν.exists_hasEigenvector
    have h98 : ν ^ 9 • v = ν ^ 8 • v := by
      rw [← hpow ν v hv.apply_eq_smul, ← hpow ν v hv.apply_eq_smul, h]
    have h98' : ν ^ 8 * (ν - 1) = 0 := by
      have := smul_left_injective ℂ hv.2 h98
      linear_combination this
    rcases mul_eq_zero.mp h98' with h0 | h1
    · exact Or.inl (pow_eq_zero_iff (by norm_num) |>.mp h0)
    · exact Or.inr (sub_eq_zero.mp h1)
  refine ⟨(exercise_7B_1 T hN).mpr fun ν hν => ?_, ?_⟩
  · rcases h01 ν hν with rfl | rfl <;> simp
  · obtain ⟨n, e, he⟩ := complex_spectral T hN
    refine e.toBasis.ext fun k => ?_
    set μ := ⟪e k, T (e k)⟫_ℂ
    have hk : T (e k) = μ • e k := he k
    rw [OrthonormalBasis.coe_toBasis, hpow μ _ hk 2, hk]
    rcases h01 μ (Module.End.hasEigenvalue_of_hasEigenvector
      (hasEigenvector_of_orthonormalBasis e hk)) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp

/-- Axler leaves the complex vector space free, so it is part of the answer. Only
its dimension matters — every finite-dimensional complex vector space is
{lit}`ℂⁿ` up to isomorphism — so the answer supplies {lit}`n`. -/
def exercise_7B_7_n : ℕ := 3

/-- The witness operator for 7B.7. -/
noncomputable def exercise_7B_7_sol :
    (Fin exercise_7B_7_n → ℂ) →ₗ[ℂ] (Fin exercise_7B_7_n → ℂ) :=
  -- take T (x, y, z) = (0, x, y)
  -- T^2 = (0, 0, x), so T^2 ≠ T
  -- but T^3 = 0, so T^9 = T^8 = 0
  { toFun := fun x i => if h : (i : ℕ) = 0 then 0 else x ⟨i - 1, by have := i.isLt; omega⟩
    map_add' := fun x y => by funext i; by_cases h : (i : ℕ) = 0 <;> simp [h]
    map_smul' := fun c x => by funext i; by_cases h : (i : ℕ) = 0 <;> simp [h] }

/-- 7B.7 There is an operator on a complex vector space with {lit}`T⁹ = T⁸` but
{lit}`T² ≠ T`. -/
theorem exercise_7B_7 :
    exercise_7B_7_sol ^ 9 = exercise_7B_7_sol ^ 8 ∧
      exercise_7B_7_sol ^ 2 ≠ exercise_7B_7_sol := by
  -- `T³ = 0`: applying the shift three times pushes every coordinate out of `ℂ³`
  have h3 : exercise_7B_7_sol ^ 3 = 0 := by
    refine LinearMap.ext fun x => funext fun i => ?_
    have hi : (i : ℕ) < 3 := i.isLt
    simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, LinearMap.zero_apply,
      Pi.zero_apply, exercise_7B_7_sol, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> first | rfl | (exfalso; omega)
  refine ⟨?_, fun h => ?_⟩
  · rw [show 9 = 3 + 6 from rfl, show 8 = 3 + 5 from rfl, pow_add, pow_add, h3, zero_mul, zero_mul]
  · -- `T e₁ = e₂` but `T² e₁ = e₃`; compare the second coordinate
    have := congrFun (LinearMap.congr_fun h (fun i => if (i : ℕ) = 0 then 1 else 0)) ⟨1, by decide⟩
    simp [pow_two, exercise_7B_7_sol] at this

/-- 7B.8 For {lit}`𝔽 = ℂ`, {lit}`T` is normal iff every eigenvector of {lit}`T` is
also an eigenvector of {lit}`T*`. -/
theorem exercise_7B_8 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔ ∀ (v : V) (μ : ℂ), HasEigenvector T μ v →
      ∃ ν : ℂ, HasEigenvector T† ν v := by
  -- => proven in 7A with conj λ eigenvalue for T†
  -- <=
  sorry

/-- 7B.9 For {lit}`𝔽 = ℂ`, {lit}`T` is normal iff {lit}`T* = p(T)` for some
polynomial {lit}`p ∈ 𝒫(ℂ)`. -/
theorem exercise_7B_9 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔ ∃ p : Polynomial ℂ, T† = Polynomial.aeval T p := by
  sorry

/-- 7B.10 Every normal operator on a complex inner product space has a square
root. -/
theorem exercise_7B_10 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    ∃ S : V →ₗ[ℂ] V, S ^ 2 = T := by
  sorry

/-- 7B.11 Every self-adjoint operator on {lit}`V` has a cube root. -/
theorem exercise_7B_11 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) :
    ∃ S : V →ₗ[𝕜] V, S ^ 3 = T := by
  sorry

/-- 7B.12 (Fuglede) For normal {lit}`T` on a complex inner product space, any
{lit}`S` commuting with {lit}`T` also commutes with {lit}`T*`. -/
theorem exercise_7B_12 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T S : V →ₗ[ℂ] V) (hN : IsStarNormal T)
    (h : S ∘ₗ T = T ∘ₗ S) :
    S ∘ₗ T† = T† ∘ₗ S := by
  sorry

/-- 7B.13 (Via Schur for two commuting operators) Every normal operator on a
complex inner product space has an orthonormal basis of eigenvectors. -/
theorem exercise_7B_13 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V), ∀ k, ∃ μ : ℂ, HasEigenvector T μ (e k) := by
  sorry

/-- 7B.14 For {lit}`𝔽 = ℝ`, {lit}`T` is self-adjoint iff eigenvectors for distinct
eigenvalues are orthogonal and the eigenspaces span {lit}`V`. -/
theorem exercise_7B_14 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) :
    LinearMap.IsSymmetric T ↔
      ((∀ (μ ν : ℝ) (u v : V), μ ≠ ν → HasEigenvector T μ u → HasEigenvector T ν v →
          ⟪u, v⟫_ℝ = 0) ∧
        (⨆ μ : ℝ, Module.End.eigenspace T μ) = ⊤) := by
  sorry

/-- 7B.15 For {lit}`𝔽 = ℂ`, {lit}`T` is normal iff eigenvectors for distinct
eigenvalues are orthogonal and the eigenspaces span {lit}`V`. -/
theorem exercise_7B_15 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔
      ((∀ (μ ν : ℂ) (u v : V), μ ≠ ν → HasEigenvector T μ u → HasEigenvector T ν v →
          ⟪u, v⟫_ℂ = 0) ∧
        (⨆ μ : ℂ, Module.End.eigenspace T μ) = ⊤) := by
  sorry

/-- 7B.16 For {lit}`𝔽 = ℂ` and {lit}`ℰ ⊆ ℒ(V)`, there is an orthonormal basis
diagonalizing every element of {lit}`ℰ` iff all pairs in {lit}`ℰ` are commuting
normal operators. -/
theorem exercise_7B_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ℰ : Set (V →ₗ[ℂ] V)) :
    (∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V),
        ∀ T ∈ ℰ, (LinearMap.toMatrixOrthonormal e T).IsDiag) ↔
      (∀ S ∈ ℰ, ∀ T ∈ ℰ, IsStarNormal S ∧ IsStarNormal T ∧ S ∘ₗ T = T ∘ₗ S) := by
  sorry

/-- 7B.17 For {lit}`𝔽 = ℝ` and {lit}`ℰ ⊆ ℒ(V)`, there is an orthonormal basis
diagonalizing every element of {lit}`ℰ` iff all pairs in {lit}`ℰ` are commuting
self-adjoint operators. -/
theorem exercise_7B_17 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (ℰ : Set (V →ₗ[ℝ] V)) :
    (∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℝ V),
        ∀ T ∈ ℰ, (LinearMap.toMatrixOrthonormal e T).IsDiag) ↔
      (∀ S ∈ ℰ, ∀ T ∈ ℰ,
        LinearMap.IsSymmetric S ∧ LinearMap.IsSymmetric T ∧ S ∘ₗ T = T ∘ₗ S) := by
  sorry

/-- The witness operator for 7B.18. -/
noncomputable def exercise_7B_18_sol_T :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  sorry

/-- The witness coefficient {lit}`b` for 7B.18. It is part of the answer in its own
right — nothing determines it from {lit}`exercise_7B_18_sol_T`. -/
noncomputable def exercise_7B_18_sol_b : ℝ := sorry

/-- The witness coefficient {lit}`c` for 7B.18. -/
noncomputable def exercise_7B_18_sol_c : ℝ := sorry

/-- 7B.18 The self-adjoint hypothesis in 7.26 cannot be dropped: there is a real
inner product space operator {lit}`T` and {lit}`b, c` with {lit}`b² < 4c` making
{lit}`T² + bT + cI` non-invertible. -/
theorem exercise_7B_18 :
    exercise_7B_18_sol_b ^ 2 < 4 * exercise_7B_18_sol_c ∧
      ¬ Function.Bijective (exercise_7B_18_sol_T ∘ₗ exercise_7B_18_sol_T +
        exercise_7B_18_sol_b • exercise_7B_18_sol_T +
        exercise_7B_18_sol_c •
          (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))) := by
  sorry

/-- 7B.19 (a) If {lit}`T` is self-adjoint and {lit}`U` is invariant under
{lit}`T`, then {lit}`U⟂` is invariant under {lit}`T`. -/
theorem exercise_7B_19a (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    ∀ w ∈ Uᗮ, T w ∈ Uᗮ := by
  sorry

/-- 7B.19 (b) {lit}`T|U ∈ ℒ(U)` is self-adjoint. -/
theorem exercise_7B_19b (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    LinearMap.IsSymmetric (T.restrict hU) := by
  sorry

/-- 7B.19 (c) {lit}`T|U⟂ ∈ ℒ(U⟂)` is self-adjoint. The invariance of {lit}`U⟂`
needed to form the restriction is part (a). -/
theorem exercise_7B_19c (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    LinearMap.IsSymmetric (T.restrict (exercise_7B_19a T hT U hU)) := by
  sorry

/-- 7B.20 (a) If {lit}`T` is normal and {lit}`U` is invariant under {lit}`T`, then
{lit}`U⟂` is invariant under {lit}`T`. -/
theorem exercise_7B_20a (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    ∀ w ∈ Uᗮ, T w ∈ Uᗮ := by
  sorry

/-- 7B.20 (b) {lit}`U` is invariant under {lit}`T*`. -/
theorem exercise_7B_20b (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    ∀ u ∈ U, T† u ∈ U := by
  sorry

/-- 7B.20 (c) {lit}`(T|U)* = (T*)|U`. The invariance of {lit}`U` under {lit}`T*`
needed to form the right-hand restriction is part (b). -/
theorem exercise_7B_20c (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    (T.restrict hU)† =
      T†.restrict (exercise_7B_20b T hN U hU) := by
  sorry

/-- 7B.20 (d) Both {lit}`T|U ∈ ℒ(U)` and {lit}`T|U⟂ ∈ ℒ(U⟂)` are normal. -/
theorem exercise_7B_20d (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    IsStarNormal (T.restrict hU) ∧
      IsStarNormal (T.restrict (exercise_7B_20a T hN U hU)) := by
  sorry

/-- 7B.21 If {lit}`T` is self-adjoint with {lit}`2, 3` its only eigenvalues, then
{lit}`T² − 5T + 6I = 0`. -/
theorem exercise_7B_21 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (h : ∀ μ : 𝕜, HasEigenvalue T μ ↔ μ = 2 ∨ μ = 3) :
    T ∘ₗ T - (5 : 𝕜) • T + (6 : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V) = 0 := by
  sorry

/-- The witness for 7B.22. -/
noncomputable def exercise_7B_22_sol :
    EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
  sorry

/-- 7B.22 There is an operator on {lit}`ℂ³` with {lit}`2, 3` its only eigenvalues
but {lit}`T² − 5T + 6I ≠ 0`. -/
theorem exercise_7B_22 :
    (∀ μ : ℂ, HasEigenvalue exercise_7B_22_sol μ ↔ μ = 2 ∨ μ = 3) ∧
      exercise_7B_22_sol ∘ₗ exercise_7B_22_sol - (5 : ℂ) • exercise_7B_22_sol +
        (6 : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) ≠ 0 := by
  sorry

/-- 7B.23 If {lit}`T` is self-adjoint and {lit}`‖Tv − λv‖ < ε` for some unit
{lit}`v`, then {lit}`T` has an eigenvalue within {lit}`ε` of {lit}`λ`. -/
theorem exercise_7B_23 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (μ : 𝕜)
    (ε : ℝ) (hε : 0 < ε) (v : V) (hv : ‖v‖ = 1) (hlt : ‖T v - μ • v‖ < ε) :
    ∃ μ' : 𝕜, HasEigenvalue T μ' ∧ ‖μ - μ'‖ < ε := by
  sorry

/-- 7B.24 (a) For {lit}`𝔽 = ℝ`, {lit}`T` is diagonalizable iff some basis gives a
matrix equal to its transpose. -/
theorem exercise_7B_24a {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (T : U →ₗ[ℝ] U) :
    Section_5D.IsDiagonalizable T ↔
      ∃ b : Module.Basis (Fin (finrank ℝ U)) ℝ U,
        (LinearMap.toMatrix b b T).transpose = LinearMap.toMatrix b b T := by
  sorry

/-- 7B.24 (b) For {lit}`𝔽 = ℂ`, {lit}`T` is diagonalizable iff some basis gives a
matrix commuting with its conjugate transpose. -/
theorem exercise_7B_24b {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] (T : U →ₗ[ℂ] U) :
    Section_5D.IsDiagonalizable T ↔
      ∃ b : Module.Basis (Fin (finrank ℂ U)) ℂ U,
        LinearMap.toMatrix b b T * (LinearMap.toMatrix b b T).conjTranspose =
          (LinearMap.toMatrix b b T).conjTranspose * LinearMap.toMatrix b b T := by
  sorry

/-- 7B.25 For {lit}`T` with orthonormal eigenbasis {lit}`e` and eigenvalues
{lit}`λ`, the pseudoinverse satisfies {lit}`T† eₖ = (1/λₖ) eₖ` if {lit}`λₖ ≠ 0`,
else {lit}`0`. -/
theorem exercise_7B_25 {n : ℕ} (T : V →ₗ[𝕜] V) (e : OrthonormalBasis (Fin n) 𝕜 V)
    (lam : Fin n → 𝕜) (he : ∀ k, T (e k) = lam k • e k) (k : Fin n) :
    LADR.Section_6C.pinv T (e k) = (if lam k = 0 then 0 else (lam k)⁻¹ • e k) := by
  sorry

end LADR.Section_7B
