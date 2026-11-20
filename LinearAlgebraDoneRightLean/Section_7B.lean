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
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
  -- <= by Schur over C we have an orthonormal basis s.t. the matrix is
  --    upper diagonal the matrix of T† is conjugate transpose, which is lower triangular
  --    take the first basis vector (1, 0, ..., 0) in that basis
  --    it is an eigenvector of T, thus it is eigenvector of T†
  --    the non-zero entries in the first row of the upper triangular matrix
  --    have to be zero. Continue by induction on the dimension k.
  --    so both T and T† are diagonal in that basis, hence there is
  --    an orthonormal basis of eigenvectors for T, hence normal.
  constructor
  · intro hN v μ hv
    exact ⟨conj μ, Module.End.mem_eigenspace_iff.mpr
      ((LADR.Section_7A.eigenvector_adjoint hN v μ).mp hv.apply_eq_smul), hv.2⟩
  · intro hev
    obtain ⟨n, e, he, hUT⟩ := LADR.Section_6B.exists_orthonormal_upperTriangular_complex T
    have hflag : ∀ k, T (e k) ∈ Submodule.span ℂ (e '' {i | i ≤ k}) :=
      ((LADR.Section_5C.tfae_upperTriangular he T).out 1 3).mp hUT
    -- entries below the diagonal vanish (upper triangular)
    have hUTz : ∀ i j : Fin n, j < i → ⟪e i, T (e j)⟫_ℂ = 0 := fun i j hji =>
      inner_eq_zero_of_upperTriangular T e hflag hji
    -- a column that is zero off the diagonal makes `e k` an eigenvector
    have hTk : ∀ k, (∀ i, i ≠ k → ⟪e i, T (e k)⟫_ℂ = 0) →
        T (e k) = ⟪e k, T (e k)⟫_ℂ • e k := fun k hcol => by
      conv_lhs => rw [← e.sum_repr' (T (e k))]
      exact Finset.sum_eq_single k (fun i _ hik => by rw [hcol i hik, zero_smul]) (by simp)
    -- induction on `k`: row `k` is zero off the diagonal
    have hrow : ∀ m : ℕ, ∀ k : Fin n, k.val = m → ∀ j, j ≠ k → ⟪e k, T (e j)⟫_ℂ = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m IH =>
        intro k hk j hjk
        -- column `k` is zero off the diagonal: above it by induction, below it by `hUTz`
        have hcol : ∀ i, i ≠ k → ⟪e i, T (e k)⟫_ℂ = 0 := fun i hik => by
          rcases lt_or_gt_of_ne hik with h | h
          · exact IH i.val (by rw [← hk]; exact Fin.lt_def.mp h) i rfl k (ne_of_lt h).symm
          · exact hUTz i k h
        -- so `e k` is an eigenvector of `T`, hence of `T†`, which kills row `k`
        obtain ⟨ν, hν⟩ := hev (e k) _ (hasEigenvector_of_orthonormalBasis e (hTk k hcol))
        rw [← LinearMap.adjoint_inner_left, hν.apply_eq_smul, inner_smul_left,
          e.orthonormal.inner_eq_zero hjk.symm, mul_zero]
    -- every `e k` is an eigenvector, so 7.31 (c) ⟹ (a) gives normality
    have hbasis : HasOrthonormalEigenbasis T := ⟨n, e, fun k => ⟨_,
      hasEigenvector_of_orthonormalBasis e (hTk k fun i hik => hrow i.val i rfl k hik.symm)⟩⟩
    exact ((tfae_complex_spectral T).out 1 3).mpr hbasis

/-- 7B.9 For {lit}`𝔽 = ℂ`, {lit}`T` is normal iff {lit}`T* = p(T)` for some
polynomial {lit}`p ∈ 𝒫(ℂ)`. -/
theorem exercise_7B_9 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔ ∃ p : Polynomial ℂ, T† = Polynomial.aeval T p := by
  -- => by spectral theorem, there is orthonormal eigenbasis ei for T
  --    T*ei = conj(λi) ei. Define p(z) as interpolation polynomial
  --    with p(λi) = conj(λi) for each eigenvalue λi. This is doable because it is
  --    a finite set of points, so there exists an interpolation polynomial.
  --    then p(T)ei = p(λi) ei = conj(λi) ei = T* ei
  --    but if P(T) and T* agree on the eigenbasis, they are equal as linear maps.
  --    concretely, with μ1, ..., μm the *distinct* eigenvalues (so μa - μb ≠ 0 for a ≠ b),
  --    p(z) = ∑ a, conj(μa) * ∏ (b ≠ a), (z - μb) / (μa - μb)
  -- <= assume p(T) = T* and that v is eigenvector of T
  -- then T* v = p(T) v = p(λ) v, thus v is also an eigenvector of T*
  -- by previous exercise, T is normal.
  constructor
  · intro hN
    obtain ⟨n, e, he⟩ := complex_spectral T hN
    -- the (distinct) eigenvalues as a finite set of interpolation nodes
    let s : Finset ℂ := Finset.univ.image fun k => ⟪e k, T (e k)⟫_ℂ
    refine ⟨Lagrange.interpolate s id (fun z => conj z), e.toBasis.ext fun k => ?_⟩
    set μ := ⟪e k, T (e k)⟫_ℂ
    have hk : T (e k) = μ • e k := he k
    have hnode : (Lagrange.interpolate s id (fun z => conj z)).eval μ = conj μ :=
      Lagrange.eval_interpolate_at_node (fun z => conj z) Function.injective_id.injOn
        (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    rw [OrthonormalBasis.coe_toBasis, (LADR.Section_7A.eigenvector_adjoint hN (e k) μ).mp hk,
      Module.End.aeval_apply_of_hasEigenvector (hasEigenvector_of_orthonormalBasis e hk), hnode]
  · rintro ⟨p, hp⟩
    refine (exercise_7B_8 T).mpr fun v μ hv => ⟨p.eval μ, ?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff, hp, Module.End.aeval_apply_of_hasEigenvector hv]

/-- 7B.10 Every normal operator on a complex inner product space has a square
root. -/
theorem exercise_7B_10 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    ∃ S : V →ₗ[ℂ] V, S ^ 2 = T := by
  -- pick an orthonormal basis of eigenvectors for T that diagonalizes it (by spectral theorem)
  -- then take a sqrt of each diagonal value to construct S
  -- Since matrices of S^2 = matrix of T, the result holds.
  obtain ⟨n, e, he⟩ := complex_spectral T hN
  -- a square root of each eigenvalue (exists by the fundamental theorem of algebra, 4.12)
  let r : Fin n → ℂ := fun k => ⟪e k, T (e k)⟫_ℂ ^ ((2 : ℕ) : ℂ)⁻¹
  have hr : ∀ k, r k * r k = ⟪e k, T (e k)⟫_ℂ := fun k => by
    rw [← pow_two]; exact Complex.cpow_nat_inv_pow _ two_ne_zero
  -- `S eₖ = √λₖ eₖ`, defined on the basis
  let S : V →ₗ[ℂ] V := e.toBasis.constr ℂ fun k => r k • e k
  have hS : ∀ k, S (e k) = r k • e k := fun k => by
    have := e.toBasis.constr_basis ℂ (fun k => r k • e k) k
    rwa [OrthonormalBasis.coe_toBasis] at this
  -- `S² eₖ = √λₖ √λₖ eₖ = λₖ eₖ = T eₖ`
  refine ⟨S, e.toBasis.ext fun k => ?_⟩
  rw [OrthonormalBasis.coe_toBasis, pow_two, Module.End.mul_apply, hS, map_smul, hS, smul_smul,
    hr, ← he k]

/-- 7B.11 Every self-adjoint operator on {lit}`V` has a cube root. -/
theorem exercise_7B_11 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) :
    ∃ S : V →ₗ[𝕜] V, S ^ 3 = T := by
  -- same as 10, but take cube roots of the eigenvalues instead of square roots
  -- for V = ℝ, we can use spectral theorem for self-adjoint operators
  -- for V = ℂ, we use the spectral theorem for normal operators (which includes self-adjoint operators)
  -- every real number has a real cube root
  have hcube : ∀ x : ℝ, ∃ c : ℝ, c ^ 3 = x := by
    intro x
    rcases le_total 0 x with hx | hx
    · exact ⟨x ^ ((3 : ℕ) : ℝ)⁻¹, Real.rpow_inv_natCast_pow hx (by norm_num)⟩
    · refine ⟨-((-x) ^ ((3 : ℕ) : ℝ)⁻¹), ?_⟩
      rw [neg_pow, Real.rpow_inv_natCast_pow (neg_nonneg.mpr hx) (by norm_num)]
      ring
  choose c hc using hcube
  -- the self-adjoint spectral theorem gives real eigenvalues for both 𝔽 = ℝ and 𝔽 = ℂ
  obtain ⟨n, e, μ, he⟩ := exists_orthonormalBasis_eigenvectors T hT
  -- `S eₖ = ∛λₖ eₖ`, defined on the basis
  let S : V →ₗ[𝕜] V := e.toBasis.constr 𝕜 fun k => ((c (μ k) : ℝ) : 𝕜) • e k
  have hS : ∀ k, S (e k) = ((c (μ k) : ℝ) : 𝕜) • e k := fun k => by
    have := e.toBasis.constr_basis 𝕜 (fun k => ((c (μ k) : ℝ) : 𝕜) • e k) k
    rwa [OrthonormalBasis.coe_toBasis] at this
  -- `S³ eₖ = (∛λₖ)³ eₖ = λₖ eₖ = T eₖ`
  refine ⟨S, e.toBasis.ext fun k => ?_⟩
  simp only [OrthonormalBasis.coe_toBasis, pow_succ, pow_zero, one_mul, Module.End.mul_apply,
    hS, map_smul, smul_smul]
  rw [he k]
  congr 1
  have h3 : ((c (μ k) : ℝ) : 𝕜) ^ 3 = ((μ k : ℝ) : 𝕜) := by exact_mod_cast hc (μ k)
  linear_combination h3

/-- 7B.12 (Fuglede) For normal {lit}`T` on a complex inner product space, any
{lit}`S` commuting with {lit}`T` also commutes with {lit}`T*`. -/
theorem exercise_7B_12 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T S : V →ₗ[ℂ] V) (hN : IsStarNormal T)
    (h : S ∘ₗ T = T ∘ₗ S) :
    S ∘ₗ T† = T† ∘ₗ S := by
  -- use ex9, that since normal, T† = p(T), and that is ST=TS, Sp(T) = p(T)S
  obtain ⟨p, hp⟩ := (exercise_7B_9 T).mp hN
  rw [hp]
  have hc : Commute S T := h
  -- `S` commutes with `T`, hence with every `a Tⁿ`, hence with every polynomial in `T`
  have hcp : ∀ q : Polynomial ℂ, Commute S (Polynomial.aeval T q) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q₁ q₂ h₁ h₂ => rw [map_add]; exact h₁.add_right h₂
    | monomial n a =>
      rw [Polynomial.aeval_monomial]
      exact (Algebra.commute_algebraMap_right a S).mul_right (hc.pow_right n)
  exact (hcp p).eq

/-- 7B.13 (Via Schur for two commuting operators) Every normal operator on a
complex inner product space has an orthonormal basis of eigenvectors. -/
theorem exercise_7B_13 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hN : IsStarNormal T) :
    ∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V), ∀ k, ∃ μ : ℂ, HasEigenvector T μ (e k) := by
  -- apply the exercise from chapter 5 (orthonormal version: 6B.20) to {T, T*}
  -- since normal means they commute.
  -- then we have a single orthonormal basis is which they are both upper triangular matrix
  -- but matrix T* = conj transpose of matrix T, so T is also lower triangular,
  -- which can only happen if T is diagonal.
  have hcomm : ∀ A ∈ ({T, T†} : Set (V →ₗ[ℂ] V)), ∀ B ∈ ({T, T†} : Set (V →ₗ[ℂ] V)),
      Commute A B := by
    have h1 : Commute T† T := by
      have := hN.star_comm_self; rwa [LinearMap.star_eq_adjoint] at this
    rintro A (rfl | rfl) B (rfl | rfl)
    · exact Commute.refl _
    · exact h1.symm
    · exact h1
    · exact Commute.refl _
  obtain ⟨n, e, he, hUT⟩ := LADR.Section_6B.exercise_6B_20 _ hcomm
  have hflag : ∀ X ∈ ({T, T†} : Set (V →ₗ[ℂ] V)), ∀ k,
      X (e k) ∈ Submodule.span ℂ (e '' {i | i ≤ k}) := fun X hX =>
    ((LADR.Section_5C.tfae_upperTriangular he X).out 1 3).mp (hUT X hX)
  -- `T` upper triangular: entries below the diagonal vanish
  have hlow : ∀ i j : Fin n, j < i → ⟪e i, T (e j)⟫_ℂ = 0 := fun i j h =>
    inner_eq_zero_of_upperTriangular T e (hflag T (by simp)) h
  -- `T*` upper triangular, i.e. `T` lower triangular: entries above the diagonal vanish
  have hup : ∀ i j : Fin n, j < i → ⟪e j, T (e i)⟫_ℂ = 0 := fun i j h => by
    have := inner_eq_zero_of_upperTriangular T† e (hflag T† (by simp)) h
    rw [LinearMap.adjoint_inner_right] at this
    rw [← inner_conj_symm, this, map_zero]
  -- so the matrix of `T` is diagonal: each `eₖ` is an eigenvector
  refine ⟨n, e, fun k => ⟨_, hasEigenvector_of_orthonormalBasis e (μ := ⟪e k, T (e k)⟫_ℂ) ?_⟩⟩
  conv_lhs => rw [← e.sum_repr' (T (e k))]
  refine Finset.sum_eq_single k (fun i _ hik => ?_) (by simp)
  rcases lt_or_gt_of_ne hik with h | h
  · rw [hup k i h, zero_smul]
  · rw [hlow i k h, zero_smul]

/-- 7B.14 For {lit}`𝔽 = ℝ`, {lit}`T` is self-adjoint iff eigenvectors for distinct
eigenvalues are orthogonal and the eigenspaces span {lit}`V`. -/
theorem exercise_7B_14 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) :
    LinearMap.IsSymmetric T ↔
      ((∀ (μ ν : ℝ) (u v : V), μ ≠ ν → HasEigenvector T μ u → HasEigenvector T ν v →
          ⟪u, v⟫_ℝ = 0) ∧
        (⨆ μ : ℝ, Module.End.eigenspace T μ) = ⊤) := by
  -- => by spectral theorem, there exists an orthonormal basis of eigenvectors
  --    hence there are enough eigenvectors to form an orthonormal basis,
  --    thus satisfying the second condition of the theorem.
  --    first condition is proven as 7.22
  -- <= from each eigenspace we can pick orthonormal eigenvectors and combine them into an orthonormal basis
  --    by assumption we span all of V. By construction they are orthogonal within the eigenspace
  --    and by assumption they are orthogonal across different eigenspaces.
  --    Thus by spectral theorem condition 3) V has a basis of orthonormal eigenvectors
  --    hence is self-adjoint.
  constructor
  · intro hT
    refine ⟨fun μ ν u v hμν hu hv => LADR.Section_7A.orthogonal_eigenvectors
      (LADR.Section_7A.symmetric_isStarNormal hT) hμν hu.apply_eq_smul hv.apply_eq_smul, ?_⟩
    -- every vector is a combination of the orthonormal eigenbasis
    obtain ⟨n, e, he⟩ := spectral_orthonormal_eigenbasis T hT
    refine eq_top_iff.mpr fun x _ => ?_
    rw [← e.sum_repr' x]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    obtain ⟨μ, hμ⟩ := he i
    exact Submodule.mem_iSup_of_mem μ (Module.End.mem_eigenspace_iff.mpr hμ.apply_eq_smul)
  · rintro ⟨horth, hspan⟩
    -- index the eigenspaces by the (finitely many) eigenvalues
    let A : Module.End.Eigenvalues T → Submodule ℝ V := fun μ => Module.End.eigenspace T μ
    have hsup : iSup A = ⊤ := by
      refine eq_top_iff.mpr (hspan ▸ iSup_le fun μ => ?_)
      by_cases hμ : HasEigenvalue T μ
      · exact le_iSup_of_le (⟨μ, hμ⟩ : Module.End.Eigenvalues T) le_rfl
      · rw [Module.End.hasEigenvalue_iff, not_not] at hμ
        rw [hμ]; exact bot_le
    -- eigenspaces for distinct eigenvalues are orthogonal (the hypothesis)
    have hV : OrthogonalFamily ℝ (fun μ => A μ) fun μ => (A μ).subtypeₗᵢ := by
      intro μ ν hμν u w
      by_cases hu : (u : V) = 0
      · simp [hu]
      by_cases hw : (w : V) = 0
      · simp [hw]
      exact horth μ ν u w (fun h => hμν (Subtype.ext h)) ⟨u.2, hu⟩ ⟨w.2, hw⟩
    have hint : DirectSum.IsInternal A :=
      hV.isInternal_iff.mpr (by rw [hsup, Submodule.top_orthogonal_eq_bot])
    -- glue orthonormal bases of the eigenspaces into one orthonormal basis of `V`
    let e := hint.collectedOrthonormalBasis hV fun μ => stdOrthonormalBasis ℝ (A μ)
    let e' := e.reindex (Fintype.equivFin _)
    have hbasis : HasOrthonormalEigenbasis T := ⟨_, e', fun i => by
      refine ⟨Module.End.Eigenvalues.val T ((Fintype.equivFin _).symm i).1, ?_,
        e'.orthonormal.ne_zero i⟩
      rw [OrthonormalBasis.reindex_apply]
      exact hint.collectedOrthonormalBasis_mem hV _ _⟩
    exact ((tfae_real_spectral T).out 1 3).mpr hbasis

/-- 7B.15 For {lit}`𝔽 = ℂ`, {lit}`T` is normal iff eigenvectors for distinct
eigenvalues are orthogonal and the eigenspaces span {lit}`V`. -/
theorem exercise_7B_15 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) :
    IsStarNormal T ↔
      ((∀ (μ ν : ℂ) (u v : V), μ ≠ ν → HasEigenvector T μ u → HasEigenvector T ν v →
          ⟪u, v⟫_ℂ = 0) ∧
        (⨆ μ : ℂ, Module.End.eigenspace T μ) = ⊤) := by
  -- equivalent proof to 14, just using the complex spectral theorem.
  constructor
  · intro hN
    refine ⟨fun μ ν u v hμν hu hv => LADR.Section_7A.orthogonal_eigenvectors
      hN hμν hu.apply_eq_smul hv.apply_eq_smul, ?_⟩
    -- every vector is a combination of the orthonormal eigenbasis
    obtain ⟨n, e, he⟩ := ((tfae_complex_spectral T).out 1 3).mp hN
    refine eq_top_iff.mpr fun x _ => ?_
    rw [← e.sum_repr' x]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    obtain ⟨μ, hμ⟩ := he i
    exact Submodule.mem_iSup_of_mem μ (Module.End.mem_eigenspace_iff.mpr hμ.apply_eq_smul)
  · rintro ⟨horth, hspan⟩
    -- index the eigenspaces by the (finitely many) eigenvalues
    let A : Module.End.Eigenvalues T → Submodule ℂ V := fun μ => Module.End.eigenspace T μ
    have hsup : iSup A = ⊤ := by
      refine eq_top_iff.mpr (hspan ▸ iSup_le fun μ => ?_)
      by_cases hμ : HasEigenvalue T μ
      · exact le_iSup_of_le (⟨μ, hμ⟩ : Module.End.Eigenvalues T) le_rfl
      · rw [Module.End.hasEigenvalue_iff, not_not] at hμ
        rw [hμ]; exact bot_le
    -- eigenspaces for distinct eigenvalues are orthogonal (the hypothesis)
    have hV : OrthogonalFamily ℂ (fun μ => A μ) fun μ => (A μ).subtypeₗᵢ := by
      intro μ ν hμν u w
      by_cases hu : (u : V) = 0
      · simp [hu]
      by_cases hw : (w : V) = 0
      · simp [hw]
      exact horth μ ν u w (fun h => hμν (Subtype.ext h)) ⟨u.2, hu⟩ ⟨w.2, hw⟩
    have hint : DirectSum.IsInternal A :=
      hV.isInternal_iff.mpr (by rw [hsup, Submodule.top_orthogonal_eq_bot])
    -- glue orthonormal bases of the eigenspaces into one orthonormal basis of `V`
    let e := hint.collectedOrthonormalBasis hV fun μ => stdOrthonormalBasis ℂ (A μ)
    let e' := e.reindex (Fintype.equivFin _)
    have hbasis : HasOrthonormalEigenbasis T := ⟨_, e', fun i => by
      refine ⟨Module.End.Eigenvalues.val T ((Fintype.equivFin _).symm i).1, ?_,
        e'.orthonormal.ne_zero i⟩
      rw [OrthonormalBasis.reindex_apply]
      exact hint.collectedOrthonormalBasis_mem hV _ _⟩
    exact ((tfae_complex_spectral T).out 1 3).mpr hbasis

/-- 7B.16 For {lit}`𝔽 = ℂ` and {lit}`ℰ ⊆ ℒ(V)`, there is an orthonormal basis
diagonalizing every element of {lit}`ℰ` iff all pairs in {lit}`ℰ` are commuting
normal operators. -/
theorem exercise_7B_16 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ℰ : Set (V →ₗ[ℂ] V)) :
    (∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℂ V),
        ∀ T ∈ ℰ, (LinearMap.toMatrixOrthonormal e T).IsDiag) ↔
      (∀ S ∈ ℰ, ∀ T ∈ ℰ, IsStarNormal S ∧ IsStarNormal T ∧ S ∘ₗ T = T ∘ₗ S) := by
  -- => by spectral theorem, if orthonormal basis exists that diagonalizes S, it is normal
  --    and diagonal matrices commute, so the operators commute as well.
  -- <= by previous theorem, since they all pairwise commute, there is an
  --    orthonormal basis that make them upper-triangular simultaneously.
  --    but since they are normal, upper-triangular implies diagonal.
  constructor
  · rintro ⟨n, e, hd⟩ S hS T hT
    -- diagonal w.r.t. an orthonormal basis ⟹ normal (7.31 (b) ⟹ (a))
    have hnorm : ∀ X ∈ ℰ, IsStarNormal X := fun X hX => by
      have hX' : HasDiagonalMatrix X := ⟨n, e, hd X hX⟩
      exact ((tfae_complex_spectral X).out 2 1).mp hX'
    refine ⟨hnorm S hS, hnorm T hT, ?_⟩
    -- diagonal matrices commute, and `M` is injective
    apply (LinearMap.toMatrixOrthonormal e).injective
    change LinearMap.toMatrixOrthonormal e (S * T) = LinearMap.toMatrixOrthonormal e (T * S)
    rw [map_mul, map_mul, ← (Matrix.isDiag_iff_diagonal_diag _).mp (hd S hS),
      ← (Matrix.isDiag_iff_diagonal_diag _).mp (hd T hT), Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · intro h
    -- commuting family ⟹ simultaneously upper-triangular w.r.t. one orthonormal basis (6B.20)
    have hcomm : ∀ S ∈ ℰ, ∀ T ∈ ℰ, Commute S T := fun S hS T hT => (h S hS T hT).2.2
    obtain ⟨n, e, he, hUT⟩ := LADR.Section_6B.exercise_6B_20 ℰ hcomm
    -- normal + upper-triangular w.r.t. an orthonormal basis ⟹ diagonal
    exact ⟨n, e, fun T hT => normal_ut_diagonal T (h T hT T hT).1 e
      (((LADR.Section_5C.tfae_upperTriangular he T).out 1 3).mp (hUT T hT))⟩

/-- 7B.17 For {lit}`𝔽 = ℝ` and {lit}`ℰ ⊆ ℒ(V)`, there is an orthonormal basis
diagonalizing every element of {lit}`ℰ` iff all pairs in {lit}`ℰ` are commuting
self-adjoint operators. -/
theorem exercise_7B_17 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (ℰ : Set (V →ₗ[ℝ] V)) :
    (∃ (n : ℕ) (e : OrthonormalBasis (Fin n) ℝ V),
        ∀ T ∈ ℰ, (LinearMap.toMatrixOrthonormal e T).IsDiag) ↔
      (∀ S ∈ ℰ, ∀ T ∈ ℰ,
        LinearMap.IsSymmetric S ∧ LinearMap.IsSymmetric T ∧ S ∘ₗ T = T ∘ₗ S) := by
  -- => in the basis that diagonalizes every element of ℰ,
  --  the matrices are diagonal, so they commute and are self-adjoint (equal to their transpose)
  -- <= exercise 5E2, states that since the pair commute, and are diagonlizable
  --   (through spectral theorem since symmetric)
  --    there is a basis that makes them diagonalizable simultaneously.
  --    Then we can apply Gram-Schmidt to obtain an orthonormal basis,
  --    now the matrix of each operator in this orthonormal basis is upper-triangular.
  --    but since they are symmetric it has to be diagonal.
  constructor
  · rintro ⟨n, e, hd⟩ S hS T hT
    -- diagonal w.r.t. an orthonormal basis ⟹ self-adjoint (7.29 (b) ⟹ (a))
    have hsym : ∀ X ∈ ℰ, LinearMap.IsSymmetric X := fun X hX => by
      have hX' : HasDiagonalMatrix X := ⟨n, e, hd X hX⟩
      exact ((tfae_real_spectral X).out 2 1).mp hX'
    refine ⟨hsym S hS, hsym T hT, ?_⟩
    -- diagonal matrices commute, and `M` is injective
    apply (LinearMap.toMatrixOrthonormal e).injective
    change LinearMap.toMatrixOrthonormal e (S * T) = LinearMap.toMatrixOrthonormal e (T * S)
    rw [map_mul, map_mul, ← (Matrix.isDiag_iff_diagonal_diag _).mp (hd S hS),
      ← (Matrix.isDiag_iff_diagonal_diag _).mp (hd T hT), Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · intro h
    -- each `T ∈ ℰ` is self-adjoint, hence diagonalizable (7.29)
    have hdiag : ∀ T ∈ ℰ, Section_5D.IsDiagonalizable T := fun T hT => by
      obtain ⟨n, e, he⟩ := spectral_orthonormal_eigenbasis T (h T hT T hT).1
      have hb : Section_2B.IsBasis ℝ (⇑e) := ⟨e.orthonormal.linearIndependent, by
        show Submodule.span ℝ (Set.range ⇑e) = ⊤
        simpa using e.toBasis.span_eq⟩
      exact ⟨n, ⇑e, hb, Section_5D.isDiag_matrixOf_of_eigenvectors hb T fun j => by
        obtain ⟨μ, hμ⟩ := he j
        exact ⟨μ, hμ.apply_eq_smul⟩⟩
    -- 5E.2: commuting diagonalizable operators share a diagonalizing basis
    have hcomm : ∀ S ∈ ℰ, ∀ T ∈ ℰ, Commute S T := fun S hS T hT => (h S hS T hT).2.2
    obtain ⟨m, v, hv, hall⟩ := (Section_5E.exercise_5E_2 ℰ hdiag).mpr hcomm
    -- Gram–Schmidt keeps every (diagonal, hence) upper-triangular matrix upper-triangular
    obtain ⟨e, he, hUT⟩ := Section_6B.exists_orthonormal_upperTriangular_of_basis hv
    -- self-adjoint (so normal) + upper-triangular w.r.t. an orthonormal basis ⟹ diagonal
    exact ⟨m, e, fun T hT => normal_ut_diagonal T
      (Section_7A.symmetric_isStarNormal (h T hT T hT).1) e
      (((Section_5C.tfae_upperTriangular he T).out 1 3).mp
        (hUT T fun j k hkj => hall T hT (ne_of_lt hkj).symm))⟩

/-- The witness operator for 7B.18. -/
noncomputable def exercise_7B_18_sol_T :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  -- let's try 90 deg rotation as it is non-diagonalizable
  -- as it has no real eigenvalues.
  -- T = (0 -1; 1 0) - clearly not self-adjoint
  -- T^2 + bT + cI = (-1 0; 0 -1) + b * (0 -1; 1 0) + c * (1 0; 0 1) =
  -- (c-1 -b; b c-1)
  -- we want the matrix to be non-invertible, so row1 and row2 should be linearly dependent
  -- this gives the condition b^2 = -(c-1)^2, which can
  -- only work with b = 0, and c = 1,
  -- but that does satisfy b^2 < 4c.
  -- so T^2 + I is non-invertible (acutally it is just 0)
  Matrix.toEuclideanLin !![0, -1; 1, 0]

/-- The witness coefficient {lit}`b` for 7B.18. It is part of the answer in its own
right — nothing determines it from {lit}`exercise_7B_18_sol_T`. -/
noncomputable def exercise_7B_18_sol_b : ℝ := 0

/-- The witness coefficient {lit}`c` for 7B.18. -/
noncomputable def exercise_7B_18_sol_c : ℝ := 1

/-- 7B.18 The self-adjoint hypothesis in 7.26 cannot be dropped: there is a real
inner product space operator {lit}`T` and {lit}`b, c` with {lit}`b² < 4c` making
{lit}`T² + bT + cI` non-invertible. -/
theorem exercise_7B_18 :
    exercise_7B_18_sol_b ^ 2 < 4 * exercise_7B_18_sol_c ∧
      ¬ Function.Bijective (exercise_7B_18_sol_T ∘ₗ exercise_7B_18_sol_T +
        exercise_7B_18_sol_b • exercise_7B_18_sol_T +
        exercise_7B_18_sol_c •
          (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))) := by
  refine ⟨by norm_num [exercise_7B_18_sol_b, exercise_7B_18_sol_c], fun hbij => ?_⟩
  -- `T² + 0·T + 1·I = 0` for the rotation by 90°
  have h0 : exercise_7B_18_sol_T ∘ₗ exercise_7B_18_sol_T +
      exercise_7B_18_sol_b • exercise_7B_18_sol_T + exercise_7B_18_sol_c •
        (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = 0 := by
    refine LinearMap.ext fun x => ?_
    ext i
    fin_cases i <;> simp [exercise_7B_18_sol_T, exercise_7B_18_sol_b, exercise_7B_18_sol_c,
      Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  -- the zero map on `ℝ²` is not injective
  have hne : (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    simp at this
  exact hne (hbij.1 (by rw [h0, LinearMap.zero_apply, LinearMap.zero_apply]))

/-- 7B.19 (a) If {lit}`T` is self-adjoint and {lit}`U` is invariant under
{lit}`T`, then {lit}`U⟂` is invariant under {lit}`T`. -/
theorem exercise_7B_19a (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    ∀ w ∈ Uᗮ, T w ∈ Uᗮ := by
  -- by ex4 in 7A, Uᗮ is invariant under T*, so for self-adjoint T
  -- Uᗮ is invariant under T itself.
  have h := (Section_7A.exercise_7A_4 T U).mp hU
  rw [(Section_7A.isSelfAdjoint_iff T).mp hT] at h
  exact h

omit [FiniteDimensional 𝕜 V] in
/-- 7B.19 (b) {lit}`T|U ∈ ℒ(U)` is self-adjoint. -/
theorem exercise_7B_19b (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    LinearMap.IsSymmetric (T.restrict hU) := by
  -- self-adjoint means ⟪T v, w⟫ = ⟪v, T w⟫ for all v, w in V.
  -- When we restrict V to U, the same condition holds for all v, w in U,
  -- since we use the same inner product.
  exact fun v w => hT v w

/-- 7B.19 (c) {lit}`T|U⟂ ∈ ℒ(U⟂)` is self-adjoint. The invariance of {lit}`U⟂`
needed to form the restriction is part (a). -/
theorem exercise_7B_19c (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    LinearMap.IsSymmetric (T.restrict (exercise_7B_19a T hT U hU)) := by
  -- same argument as in part (b) for the orthogonal complement.
  -- restiction to any invariant subspace preserves the self-adjoint property.
  exact exercise_7B_19b T hT Uᗮ (exercise_7B_19a T hT U hU)

/-- 7B.20 (a) If {lit}`T` is normal and {lit}`U` is invariant under {lit}`T`, then
{lit}`U⟂` is invariant under {lit}`T`. -/
theorem exercise_7B_20a (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    ∀ w ∈ Uᗮ, T w ∈ Uᗮ := by
  -- Take an orthonormal basis of U and extend it orthonormally to V
  -- the U part is ui and rest if fi
  -- in matrix form T has a block structure with the U part
  -- [A C; 0 B] - with 0 by invariance of U
  -- if we show C = 0 we are done.
  -- but by 7.20, we know that for normal matrices
  -- the ‖.‖^2 norm of row i equals column i (the conj in ℂ doesn't affect the norm)
  -- summing over all the U rows and columns, we get ‖A‖^2 = ‖A‖^2 + ‖C‖^2, so ‖C‖ = 0
  -- Hence C = 0 and Uᗮ is invariant under T.
  -- (In Lean we avoid the basis f of Uᗮ: the squared norm of row j of C is
  --  ‖P_{Uᗮ} (T* uⱼ)‖², by Parseval in Uᗮ.)
  have hnorm : ∀ v, ‖T v‖ = ‖T† v‖ := (Section_7A.normal_iff_norm T).mp hN
  let u := stdOrthonormalBasis 𝕜 U
  -- the entries of the block A
  set a : _ → _ → 𝕜 := fun i j => ⟪(u i : V), T (u j)⟫_𝕜 with ha
  -- column j: `T uⱼ ∈ U`, so its squared norm is `Σᵢ |aᵢⱼ|²` (the 0 block)
  have hcol : ∀ j, ‖T (u j)‖ ^ 2 = ∑ i, ‖a i j‖ ^ 2 := fun j => by
    have := u.sum_sq_norm_inner_right (⟨T (u j), hU _ (u j).2⟩ : U)
    simp only [Submodule.coe_inner] at this
    exact this.symm
  -- row j: `‖T* uⱼ‖² = Σᵢ |aⱼᵢ|² + ‖row j of C‖²`
  have hrow : ∀ j, ‖T† (u j)‖ ^ 2 = ∑ i, ‖a j i‖ ^ 2 +
      ‖Uᗮ.orthogonalProjectionOnto (T† (u j))‖ ^ 2 := fun j => by
    rw [Submodule.norm_sq_eq_add_norm_sq_projection _ U, ← u.sum_sq_norm_inner_right]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, LinearMap.adjoint_inner_right,
      ← inner_conj_symm, RCLike.norm_conj]
  -- 7.20 for each uⱼ, summed over the U part: ‖A‖² = ‖A‖² + ‖C‖²
  have hC : ∑ j, ‖Uᗮ.orthogonalProjectionOnto (T† (u j))‖ ^ 2 = 0 := by
    have h1 : ∑ j, ‖T (u j)‖ ^ 2 = ∑ j, ‖T† (u j)‖ ^ 2 :=
      Finset.sum_congr rfl fun j _ => by rw [hnorm]
    simp only [hcol, hrow, Finset.sum_add_distrib] at h1
    rw [Finset.sum_comm] at h1
    linarith
  -- so C = 0: every row of C vanishes, i.e. `T* uⱼ ∈ U`
  have hCj : ∀ j, T† (u j) ∈ U := fun j => by
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hC j
      (Finset.mem_univ _)
    have h0 : Uᗮ.orthogonalProjectionOnto (T† (u j)) = 0 :=
      norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal] at h0
    exact h0
  -- C = 0 means `⟪uᵢ, T w⟫ = ⟪T* uᵢ, w⟫ = 0` for `w ∈ Uᗮ`, i.e. `T w ∈ Uᗮ`
  intro w hw
  rw [Submodule.mem_orthogonal]
  intro x hx
  have hx' : x = ∑ i, ⟪(u i : V), x⟫_𝕜 • (u i : V) := by
    have := congrArg Subtype.val (u.sum_repr' (⟨x, hx⟩ : U))
    simpa using this.symm
  rw [hx', sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_smul_left, ← LinearMap.adjoint_inner_left,
    Submodule.inner_right_of_mem_orthogonal (hCj i) hw, mul_zero]

/-- 7B.20 (b) {lit}`U` is invariant under {lit}`T*`. -/
theorem exercise_7B_20b (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    ∀ u ∈ U, T† u ∈ U := by
  -- by 7Aex4, U is invariant under T implies Uᗮ is invariant under T*
  -- so apply with Uᗮ from a) to get invariance under T* for Uᗮᗮ = U.
  have h := (Section_7A.exercise_7A_4 T Uᗮ).mp (exercise_7B_20a T hN U hU)
  rw [Submodule.orthogonal_orthogonal] at h
  exact h

/-- 7B.20 (c) {lit}`(T|U)* = (T*)|U`. The invariance of {lit}`U` under {lit}`T*`
needed to form the right-hand restriction is part (b). -/
theorem exercise_7B_20c (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    (T.restrict hU)† =
      T†.restrict (exercise_7B_20b T hN U hU) := by
  -- (T|U)* is the unique operator that ⟨(T|U)* u, v⟩ = ⟨u, T|U v⟩ for all u, v ∈ U
  -- but T|U is just the restriction of T to U
  -- so ⟪u, T v⟫ = ⟪T* u, v⟫ for all u, v ∈ U, and by b) T* u is well defined.
  -- so we can do (T*)|U without ambiguity, and it satisfies the defining property of (T|U)*.
  exact ((LinearMap.eq_adjoint_iff (T†.restrict (exercise_7B_20b T hN U hU))
    (T.restrict hU)).mpr fun x y => LinearMap.adjoint_inner_left T (y : V) (x : V)).symm

/-- 7B.20 (d) Both {lit}`T|U ∈ ℒ(U)` and {lit}`T|U⟂ ∈ ℒ(U⟂)` are normal. -/
theorem exercise_7B_20d (T : V →ₗ[𝕜] V) (hN : IsStarNormal T)
    (U : Submodule 𝕜 V) (hU : ∀ u ∈ U, T u ∈ U) :
    IsStarNormal (T.restrict hU) ∧
      IsStarNormal (T.restrict (exercise_7B_20a T hN U hU)) := by
  -- by T|U = T and c), we can move the restriction out and use normality of T.
  -- to prove T|U is normal, use a) to prove the second part for a new U = Uᗮ.
  have hTT : T† * T = T * T† := by
    have := hN.star_comm_self; rwa [LinearMap.star_eq_adjoint] at this
  -- for any T-invariant W: (T|W)* = (T*)|W by (c), and T*T = TT* restricts to W
  have key : ∀ (W : Submodule 𝕜 V) (hW : ∀ u ∈ W, T u ∈ W), IsStarNormal (T.restrict hW) := by
    intro W hW
    refine ⟨?_⟩
    rw [LinearMap.star_eq_adjoint, exercise_7B_20c T hN W hW]
    show T†.restrict (exercise_7B_20b T hN W hW) * T.restrict hW =
      T.restrict hW * T†.restrict (exercise_7B_20b T hN W hW)
    ext v
    exact congrArg (fun S : V →ₗ[𝕜] V => S v) hTT
  exact ⟨key U hU, key Uᗮ (exercise_7B_20a T hN U hU)⟩

/-- 7B.21 If {lit}`T` is self-adjoint with {lit}`2, 3` its only eigenvalues, then
{lit}`T² − 5T + 6I = 0`. -/
theorem exercise_7B_21 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T)
    (h : ∀ μ : 𝕜, HasEigenvalue T μ ↔ μ = 2 ∨ μ = 3) :
    T ∘ₗ T - (5 : 𝕜) • T + (6 : 𝕜) • (LinearMap.id : V →ₗ[𝕜] V) = 0 := by
  -- direct application of 7.27 in 7B and exercise 28 in 7A
  -- the minimal polynomial is of form Π (x - l_i) for the distinct eigenvalues l_i
  -- thus the minimal polynomial is (x - 2)(x - 3), giving T² - 5T + 6I = 0
  classical
  -- 7.27: the minimal polynomial is ∏ₖ (z - λₖ)
  obtain ⟨m, lams, hmin⟩ := minpoly_isSymmetric_eq_prod T hT
  -- 7A.28 (T is normal): no factor (z - λ)², so the λₖ are distinct
  have hinj : Function.Injective fun k => ((lams k : ℝ) : 𝕜) := by
    intro i j hij
    by_contra hne
    apply Section_7A.exercise_7A_28 (Section_7A.symmetric_isStarNormal hT) ((lams i : ℝ) : 𝕜)
    have hij' : ((lams i : ℝ) : 𝕜) = ((lams j : ℝ) : 𝕜) := hij
    have hpair : (Polynomial.X - Polynomial.C ((lams i : ℝ) : 𝕜)) *
        (Polynomial.X - Polynomial.C ((lams j : ℝ) : 𝕜)) ∣
          ∏ k, (Polynomial.X - Polynomial.C ((lams k : ℝ) : 𝕜)) := by
      have := Finset.prod_dvd_prod_of_subset {i, j} Finset.univ
        (fun k => Polynomial.X - Polynomial.C ((lams k : ℝ) : 𝕜)) (Finset.subset_univ _)
      rwa [Finset.prod_pair hne] at this
    rwa [← hij', ← pow_two, ← hmin] at hpair
  -- regroup as a product over the finite set of (distinct) λₖ
  set s : Finset 𝕜 := Finset.univ.image fun k => ((lams k : ℝ) : 𝕜)
  have hs : minpoly 𝕜 T = ∏ a ∈ s, (Polynomial.X - Polynomial.C a) := by
    rw [hmin, Finset.prod_image fun i _ j _ h => hinj h]
  -- the zeros of the minimal polynomial are the eigenvalues (5.27), so `s ⊆ {2, 3}`
  have hsub : s ⊆ {2, 3} := fun a ha => by
    have hroot : (minpoly 𝕜 T).IsRoot a := by
      rw [hs, Polynomial.IsRoot, Polynomial.eval_prod]
      exact Finset.prod_eq_zero ha (by simp)
    have := (h a).mp ((Section_5B.isEigenvalue_iff_isRoot T a).mpr hroot)
    simpa using this
  -- so the minimal polynomial divides `(z - 2)(z - 3)`, which therefore annihilates `T`
  have hdvd : minpoly 𝕜 T ∣
      (Polynomial.X - Polynomial.C (2 : 𝕜)) * (Polynomial.X - Polynomial.C 3) := by
    have := Finset.prod_dvd_prod_of_subset s {2, 3}
      (fun a : 𝕜 => Polynomial.X - Polynomial.C a) hsub
    rwa [← hs, Finset.prod_pair (by norm_num : (2 : 𝕜) ≠ 3)] at this
  obtain ⟨q, hq⟩ := hdvd
  have h0 : Polynomial.aeval T
      ((Polynomial.X - Polynomial.C (2 : 𝕜)) * (Polynomial.X - Polynomial.C 3)) = 0 := by
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  -- expand `(T - 2I)(T - 3I) = T² - 5T + 6I`
  rw [← h0]
  simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, ← Module.End.mul_eq_comp, ← Module.End.one_eq_id, sub_mul,
    mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  module

/-- The witness for 7B.22. -/
noncomputable def exercise_7B_22_sol :
    EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) :=
  -- it has to be non-self-adjoint matrix.
  -- so (2 1 1; 0 3 1; 0 0 3) would have 2 and 3 as the only eigenvalues and not be self-adjoint.
  -- T² − 5T + 6I = (0 0 1; 0 0 1; 0 0 0)
  Matrix.toEuclideanLin !![2, 1, 1; 0, 3, 1; 0, 0, 3]

/-- 7B.22 There is an operator on {lit}`ℂ³` with {lit}`2, 3` its only eigenvalues
but {lit}`T² − 5T + 6I ≠ 0`. -/
theorem exercise_7B_22 :
    (∀ μ : ℂ, HasEigenvalue exercise_7B_22_sol μ ↔ μ = 2 ∨ μ = 3) ∧
      exercise_7B_22_sol ∘ₗ exercise_7B_22_sol - (5 : ℂ) • exercise_7B_22_sol +
        (6 : ℂ) • (LinearMap.id : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3)) ≠ 0 := by
  have hev : ∀ (μ : ℂ) (x : EuclideanSpace ℂ (Fin 3)), x ≠ 0 → exercise_7B_22_sol x = μ • x →
      HasEigenvalue exercise_7B_22_sol μ := fun μ x hx h =>
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr h, hx⟩
  have hne : ∀ f : Fin 3 → ℂ, f ≠ 0 →
      (WithLp.equiv 2 _).symm f ≠ (0 : EuclideanSpace ℂ (Fin 3)) :=
    fun f hf h => hf (by simpa using congrArg (WithLp.equiv 2 _) h)
  refine ⟨fun μ => ⟨fun hμ => ?_, ?_⟩, fun h => ?_⟩
  · -- an eigenvector `v` of the upper-triangular matrix: solve `Tv = μv` from the bottom row up;
    -- if `μ ∉ {2, 3}` this forces `v = 0`
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    have hTv := hv.apply_eq_smul
    have e0 := congrArg (fun w : EuclideanSpace ℂ (Fin 3) => w 0) hTv
    have e1 := congrArg (fun w : EuclideanSpace ℂ (Fin 3) => w 1) hTv
    have e2 := congrArg (fun w : EuclideanSpace ℂ (Fin 3) => w 2) hTv
    simp [exercise_7B_22_sol, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] at e0 e1 e2
    by_contra hμ23
    have hμ2 : μ ≠ 2 := fun h => hμ23 (Or.inl h)
    have hμ3 : μ ≠ 3 := fun h => hμ23 (Or.inr h)
    have h2 : v 2 = 0 := e2.resolve_left fun h => hμ3 h.symm
    have h1 : v 1 = 0 := by
      have : (3 - μ) * v 1 = 0 := by linear_combination e1 - h2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linear_combination -h : μ = 3) hμ3
      · exact h
    have h0 : v 0 = 0 := by
      have : (2 - μ) * v 0 = 0 := by linear_combination e0 - h1 - h2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linear_combination -h : μ = 2) hμ2
      · exact h
    exact hv.2 (by ext i; fin_cases i <;> simp [h0, h1, h2])
  · -- eigenvectors `(1, 0, 0)` for 2 and `(1, 1, 0)` for 3
    rintro (rfl | rfl)
    · refine hev 2 ((WithLp.equiv 2 _).symm ![1, 0, 0]) (hne _ (by simp)) ?_
      ext i; fin_cases i <;> simp [exercise_7B_22_sol, Matrix.toEuclideanLin]
    · refine hev 3 ((WithLp.equiv 2 _).symm ![1, 1, 0]) (hne _ (by simp)) ?_
      ext i; fin_cases i <;> simp [exercise_7B_22_sol, Matrix.toEuclideanLin]; norm_num
  · -- the (1, 3) entry of `T² − 5T + 6I` is 1: apply to `e₃` and read coordinate 1
    have := congrArg (fun S : EuclideanSpace ℂ (Fin 3) →ₗ[ℂ] EuclideanSpace ℂ (Fin 3) =>
      S ((WithLp.equiv 2 _).symm ![0, 0, 1]) 0) h
    simp [exercise_7B_22_sol, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_three] at this
    norm_num at this

/-- 7B.23 If {lit}`T` is self-adjoint and {lit}`‖Tv − λv‖ < ε` for some unit
{lit}`v`, then {lit}`T` has an eigenvalue within {lit}`ε` of {lit}`λ`. -/
theorem exercise_7B_23 (T : V →ₗ[𝕜] V) (hT : LinearMap.IsSymmetric T) (μ : 𝕜)
    (ε : ℝ) (hε : 0 < ε) (v : V) (hv : ‖v‖ = 1) (hlt : ‖T v - μ • v‖ < ε) :
    ∃ μ' : 𝕜, HasEigenvalue T μ' ∧ ‖μ - μ'‖ < ε := by
  -- apply the spectral theorem (for ℝ directly, for ℂ self-adjoint implies normal)
  -- then there is an orthonornal basis in which T is diagonal, and each entry is an eigenvalue
  -- so T = (λ₁, λ₂, ..., λₙ) in that orthonormal basis
  -- and Tv = (λ₁v₁, λ₂v₂, ..., λₙvₙ) in that orthonormal basis
  -- and |Tv - λv| = |(λ₁ - λ)v₁, (λ₂ - λ)v₂, ..., (λₙ - λ)vₙ| = √∑ i, |(λᵢ - λ)vᵢ|² (since orthonormal basis)
  -- ε > √∑ i, |(λᵢ - λ)|² |vᵢ|²
  -- by contradiction assume that |λᵢ - λ| ≥ ε for all i
  -- so ε > √∑ i, |(λᵢ - λ)|² |vᵢ|² ≥ √∑ i, ε² |vᵢ|² = √(ε² ∑ i, |vᵢ|²) = ε ‖v‖ = ε, contradiction
  obtain ⟨n, e, lam, he⟩ := exists_orthonormalBasis_eigenvectors T hT
  by_contra hcon
  -- every λᵢ is an eigenvalue, so (by contradiction) |λᵢ - λ| ≥ ε for all i
  have hall : ∀ i, ε ≤ ‖μ - ((lam i : ℝ) : 𝕜)‖ := fun i => le_of_not_gt fun h =>
    hcon ⟨_, Module.End.hasEigenvalue_of_hasEigenvector
      (hasEigenvector_of_orthonormalBasis e (he i)), h⟩
  -- the i-th coordinate of Tv - λv is (λᵢ - λ) vᵢ
  have hcoef : ∀ i, ⟪e i, T v - μ • v⟫_𝕜 = (((lam i : ℝ) : 𝕜) - μ) * ⟪e i, v⟫_𝕜 := fun i => by
    rw [inner_sub_right, inner_smul_right, ← hT (e i) v, he i, inner_smul_left,
      RCLike.conj_ofReal, sub_mul]
  -- ‖Tv - λv‖² = ∑ |λᵢ - λ|² |vᵢ|²  and  ∑ |vᵢ|² = ‖v‖² = 1  (6.30)
  have hsum : ‖T v - μ • v‖ ^ 2 = ∑ i, ‖((lam i : ℝ) : 𝕜) - μ‖ ^ 2 * ‖⟪e i, v⟫_𝕜‖ ^ 2 := by
    rw [← e.sum_sq_norm_inner_right]
    exact Finset.sum_congr rfl fun i _ => by rw [hcoef, norm_mul, mul_pow]
  have hv2 : ∑ i, ‖⟪e i, v⟫_𝕜‖ ^ 2 = 1 := by rw [e.sum_sq_norm_inner_right, hv, one_pow]
  -- ∑ |λᵢ - λ|² |vᵢ|² ≥ ε² ∑ |vᵢ|² = ε²
  have hge : ε ^ 2 ≤ ‖T v - μ • v‖ ^ 2 := by
    rw [hsum, ← mul_one (ε ^ 2), ← hv2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [norm_sub_rev]
    exact pow_le_pow_left₀ hε.le (hall i) 2
  have hlt2 : ‖T v - μ • v‖ ^ 2 < ε ^ 2 := pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  linarith

/-- 7B.24 (a) For {lit}`𝔽 = ℝ`, {lit}`T` is diagonalizable iff some basis gives a
matrix equal to its transpose. -/
theorem exercise_7B_24a {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (T : U →ₗ[ℝ] U) :
    Section_5D.IsDiagonalizable T ↔
      ∃ b : Module.Basis (Fin (finrank ℝ U)) ℝ U,
        (LinearMap.toMatrix b b T).transpose = LinearMap.toMatrix b b T := by
  -- => If T is diagonalizable in some basis, then in the same basis the matrix transpose
  --    equals itself, because diag transpose is itself.
  -- <= take the basis ei, and defined an inner product in which the basis
  --    would be orthonormal, thus we can apply the spectral theorem to conclude T is diagonalizable.
  --    if ⟪v, w⟫ = ⟪∑ ai ei , ∑ bi ei⟫ = ∑ ai conj(bi), then the basis is orthonormal.
  --    the transformation is self-adjoint in this inner product, because the inner product
  --    did not change the matrix representation in that basis, and the matrix equals it's transpose.
  --    to prove the inner product is indeed valid, we need to check it is
  --    1) positive definite and 2) sesquilinear and 3) conj symmetric
  --    1 - positive definite: ⟪v, v⟫ = ∑ |ai|² ≥ 0 and = 0 iff v = 0
  --    2 - sesquilinear: ⟪v, w⟫ = ∑ ai conj(bi) is linear in the first argument and conjugate linear in the second argument.
  --    3 - conj symmetric ⟪v, w⟫ = conj(⟪w, v⟫) by definition of the inner product as ∑ ai conj(bi)
  --    (In Lean `U` already carries an inner product, so instead of putting a second one on `U`
  --    we transport `T` along the coordinate map `ψ : U ≃ ℝⁿ` of the basis; the standard inner
  --    product on ℝⁿ is exactly "the one that makes the basis orthonormal".)
  constructor
  · rintro ⟨n', v, hv, hD⟩
    have hcard : n' = finrank ℝ U := Section_2C.isBasis_card_eq_finrank v hv
    let b' := hv.toModuleBasis.reindex (finCongr hcard)
    -- each basis vector is an eigenvector
    have hT' : ∀ k, ∃ c : ℝ, T (b' k) = c • b' k := fun k => by
      refine ⟨Section_3C.matrixOf hv hv T ((finCongr hcard).symm k) ((finCongr hcard).symm k), ?_⟩
      simp only [b', Module.Basis.reindex_apply, Section_2B.IsBasis.toModuleBasis_apply]
      exact Section_5D.apply_eq_smul_of_isDiag hv T hD _
    choose c hc using hT'
    -- the diagonal matrix equals its transpose
    refine ⟨b', ?_⟩
    ext i j
    simp only [Matrix.transpose_apply, LinearMap.toMatrix_apply, hc, map_smul,
      Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
  · rintro ⟨b, hb⟩
    -- the operator on ℝⁿ with matrix M(T, b), self-adjoint since the matrix is symmetric
    let S : EuclideanSpace ℝ (Fin (finrank ℝ U)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ U)) :=
      Matrix.toEuclideanLin (LinearMap.toMatrix b b T)
    have hS : S.IsSymmetric :=
      Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hb)
    -- coordinates w.r.t. `b`; they intertwine `T` and `S`
    let ψ : U ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ U)) :=
      b.equivFun.trans (WithLp.linearEquiv 2 ℝ (Fin (finrank ℝ U) → ℝ)).symm
    have key : ∀ u, S (ψ u) = ψ (T u) := fun u => by
      ext i
      have := congrFun (LinearMap.toMatrix_mulVec_repr b b T u) i
      simpa [S, ψ, Matrix.toEuclideanLin] using this
    -- real spectral theorem for `S`, then pull the eigenbasis back to `U`
    obtain ⟨m, e, μ, he⟩ := exists_orthonormalBasis_eigenvectors S hS
    have hTw : ∀ k, T (ψ.symm (e k)) = μ k • ψ.symm (e k) := fun k =>
      ψ.injective (by rw [← key, ψ.apply_symm_apply, he k, map_smul, ψ.apply_symm_apply]; rfl)
    let bw := e.toBasis.map ψ.symm
    have hbw_apply : ∀ k, bw k = ψ.symm (e k) := fun k => by
      simp [bw, Module.Basis.map_apply]
    have hbw : Section_2B.IsBasis ℝ (⇑bw) := ⟨bw.linearIndependent, bw.span_eq⟩
    exact ⟨m, ⇑bw, hbw, Section_5D.isDiag_matrixOf_of_eigenvectors hbw T fun j =>
      ⟨μ j, by rw [hbw_apply]; exact hTw j⟩⟩

/-- 7B.24 (b) For {lit}`𝔽 = ℂ`, {lit}`T` is diagonalizable iff some basis gives a
matrix commuting with its conjugate transpose. -/
theorem exercise_7B_24b {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] (T : U →ₗ[ℂ] U) :
    Section_5D.IsDiagonalizable T ↔
      ∃ b : Module.Basis (Fin (finrank ℂ U)) ℂ U,
        LinearMap.toMatrix b b T * (LinearMap.toMatrix b b T).conjTranspose =
          (LinearMap.toMatrix b b T).conjTranspose * LinearMap.toMatrix b b T := by
  -- same as a) just using ℂ spectral theorem instead of ℝ and same observation that adding
  -- an inner product doesn't change the normal equaltion in matrix form.
  constructor
  · rintro ⟨n', v, hv, hD⟩
    have hcard : n' = finrank ℂ U := Section_2C.isBasis_card_eq_finrank v hv
    let b' := hv.toModuleBasis.reindex (finCongr hcard)
    have hT' : ∀ k, ∃ c : ℂ, T (b' k) = c • b' k := fun k => by
      refine ⟨Section_3C.matrixOf hv hv T ((finCongr hcard).symm k) ((finCongr hcard).symm k), ?_⟩
      simp only [b', Module.Basis.reindex_apply, Section_2B.IsBasis.toModuleBasis_apply]
      exact Section_5D.apply_eq_smul_of_isDiag hv T hD _
    choose c hc using hT'
    -- the matrix is diagonal, and diagonal matrices commute with their conjugate transpose
    have hM : LinearMap.toMatrix b' b' T = Matrix.diagonal c := by
      ext i j
      simp only [LinearMap.toMatrix_apply, hc, map_smul, Module.Basis.repr_self,
        Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    refine ⟨b', ?_⟩
    rw [hM, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · rintro ⟨b, hb⟩
    -- the operator on ℂⁿ with matrix M(T, b); normal since M commutes with M* (7.9)
    let S : EuclideanSpace ℂ (Fin (finrank ℂ U)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ U)) :=
      Matrix.toEuclideanLin (LinearMap.toMatrix b b T)
    have hmul : ∀ P Q : Matrix (Fin (finrank ℂ U)) (Fin (finrank ℂ U)) ℂ,
        Matrix.toEuclideanLin (P * Q) = Matrix.toEuclideanLin P * Matrix.toEuclideanLin Q :=
      fun P Q => by ext x i; simp [Matrix.toEuclideanLin, Matrix.mulVec_mulVec]
    have hN : IsStarNormal S := by
      refine ⟨?_⟩
      rw [LinearMap.star_eq_adjoint, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      show _ * _ = _ * _
      rw [← hmul, ← hmul, hb]
    -- coordinates w.r.t. `b`; they intertwine `T` and `S`
    let ψ : U ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (finrank ℂ U)) :=
      b.equivFun.trans (WithLp.linearEquiv 2 ℂ (Fin (finrank ℂ U) → ℂ)).symm
    have key : ∀ u, S (ψ u) = ψ (T u) := fun u => by
      ext i
      have := congrFun (LinearMap.toMatrix_mulVec_repr b b T u) i
      simpa [S, ψ, Matrix.toEuclideanLin] using this
    -- complex spectral theorem for `S`, then pull the eigenbasis back to `U`
    obtain ⟨m, e, he⟩ := complex_spectral S hN
    have hTw : ∀ k, T (ψ.symm (e k)) = ⟪e k, S (e k)⟫_ℂ • ψ.symm (e k) := fun k =>
      ψ.injective (by rw [← key, ψ.apply_symm_apply, map_smul, ψ.apply_symm_apply]; exact he k)
    let bw := e.toBasis.map ψ.symm
    have hbw_apply : ∀ k, bw k = ψ.symm (e k) := fun k => by
      simp [bw, Module.Basis.map_apply]
    have hbw : Section_2B.IsBasis ℂ (⇑bw) := ⟨bw.linearIndependent, bw.span_eq⟩
    exact ⟨m, ⇑bw, hbw, Section_5D.isDiag_matrixOf_of_eigenvectors hbw T fun j =>
      ⟨_, by rw [hbw_apply]; exact hTw j⟩⟩

/-- 7B.25 For {lit}`T` with orthonormal eigenbasis {lit}`e` and eigenvalues
{lit}`λ`, the pseudoinverse satisfies {lit}`T† eₖ = (1/λₖ) eₖ` if {lit}`λₖ ≠ 0`,
else {lit}`0`. -/
theorem exercise_7B_25 {n : ℕ} (T : V →ₗ[𝕜] V) (e : OrthonormalBasis (Fin n) 𝕜 V)
    (lam : Fin n → 𝕜) (he : ∀ k, T (e k) = lam k • e k) (k : Fin n) :
    LADR.Section_6C.pinv T (e k) = (if lam k = 0 then 0 else (lam k)⁻¹ • e k) := by
  -- the defintion of pseudoinverse is first project onto range T
  -- and then apply the inverse of the bijection from (null T)^⊥ to range T.
  -- in the orthogonal basis e, null T is spanned by e_k with lam k = 0
  -- and (null T)^⊥ is spanned by e_k with lam k ≠ 0
  -- so the projection sends e_k with lam k ≠ 0 to itself and e_k with lam k = 0 to 0
  -- thus (Pinv T) (e k) = 0 if lam k = 0
  -- for ek with lam k ≠ 0
  -- first the projection is identity
  -- then the rest of PInv is the the inverse of T (e k)
  -- but since T (e k) = lam k • e k, the inverse is (1/lam k) • e k
  -- (Lean: by 6.70, T† w is *the* v ∈ (null T)⟂ with T v = P_(range T) w.)
  -- the j-th coordinate of T x is λⱼ times the j-th coordinate of x
  have hcoord : ∀ (j : Fin n) (x : V), ⟪e j, T x⟫_𝕜 = lam j * ⟪e j, x⟫_𝕜 := fun j x => by
    conv_lhs => rw [← e.sum_repr' x]
    rw [map_sum, inner_sum, Finset.sum_eq_single j]
    · rw [map_smul, he j, inner_smul_right, inner_smul_right, e.inner_eq_ite, ite_eq_left rfl,
        mul_one, mul_comm]
    · intro i _ hij
      rw [map_smul, he i, inner_smul_right, inner_smul_right,
        e.orthonormal.inner_eq_zero (Ne.symm hij), mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  split_ifs with h0
  · -- λₖ = 0: eₖ ⟂ range T (⟪T x, eₖ⟫ = conj (λₖ ⟪eₖ, x⟫) = 0), so P_(range T) eₖ = 0
    apply Section_6C.pinv_eq_of T (Submodule.zero_mem _)
    rw [map_zero, eq_comm, Submodule.starProjection_apply_eq_zero_iff]
    rintro _ ⟨x, rfl⟩
    rw [← inner_conj_symm, hcoord, h0, zero_mul, map_zero]
  · -- λₖ ≠ 0: λₖ⁻¹ eₖ ∈ (null T)⟂, T (λₖ⁻¹ eₖ) = eₖ ∈ range T, so P_(range T) eₖ = eₖ
    have hTv : T ((lam k)⁻¹ • e k) = e k := by
      rw [map_smul, he k, smul_smul, inv_mul_cancel₀ h0, one_smul]
    apply Section_6C.pinv_eq_of T
    · rw [Submodule.mem_orthogonal]
      intro u hu
      -- u ∈ null T has zero eₖ-coordinate, since 0 = ⟪eₖ, T u⟫ = λₖ ⟪eₖ, u⟫
      have hu0 : ⟪e k, u⟫_𝕜 = 0 := by
        have := hcoord k u
        rw [LinearMap.mem_ker.mp hu, inner_zero_right] at this
        exact (mul_eq_zero.mp this.symm).resolve_left h0
      rw [inner_smul_right, ← inner_conj_symm, hu0, map_zero, mul_zero]
    · rw [hTv, eq_comm, Submodule.starProjection_eq_self_iff]
      exact ⟨_, hTv⟩

end LADR.Section_7B
