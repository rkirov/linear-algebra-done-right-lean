module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linter.Style
public import LinearAlgebraDoneRightLean.Section_2B
public import LinearAlgebraDoneRightLean.Section_2C
public import LinearAlgebraDoneRightLean.Section_3D
public import CompanionHelper

/-!
# Axler, *Linear Algebra Done Right* (4e) — Section 9D: Tensor Products
-/

@[expose] public section

namespace LADR.Section_9D

open LADR.Section_2B (IsBasis)
open Module (Finite finrank Dual)
open scoped TensorProduct

variable {F : Type*} [Field F]
  {V : Type*} [AddCommGroup V] [Module F V]
  {W : Type*} [AddCommGroup W] [Module F W]
  {U : Type*} [AddCommGroup U] [Module F U]

/-! # Tensor Product of Two Vector Spaces -/

/-! 9.68 Definition: bilinear functional on {lit}`V × W`, the vector space {lit}`ℬ(V, W)`.

A bilinear functional is a function {lit}`β : V × W → F` that is linear in each
slot separately. In mathlib we curry the two arguments: a bilinear functional is
an element of {lit}`V →ₗ[F] W →ₗ[F] F`, i.e. a linear map sending each {lit}`v` to
the linear functional {lit}`w ↦ β(v, w)`. Addition and scalar multiplication are
the pointwise operations, making {lit}`ℬ(V, W)` a vector space. -/

example : Type _ := V →ₗ[F] W →ₗ[F] F

example : Module F (V →ₗ[F] W →ₗ[F] F) := inferInstance

/-! 9.69 Example: bilinear functionals. -/

/-- First bullet: for {lit}`φ ∈ V'` and {lit}`τ ∈ W'`, the map
{lit}`β(v, w) = φ(v)τ(w)` is a bilinear functional on {lit}`V × W`. -/
def bilin_9_69_a (φ : Dual F V) (τ : Dual F W) : V →ₗ[F] W →ₗ[F] F :=
  LinearMap.mk₂ F (fun v w => φ v * τ w)
    (fun v₁ v₂ w => by simp [map_add, add_mul])
    (fun c v w => by simp [map_smul, mul_assoc])
    (fun v w₁ w₂ => by simp [map_add, mul_add])
    (fun c v w => by simp [map_smul, mul_left_comm])

/-- Third bullet: {lit}`β(v, φ) = φ(v)` is a bilinear functional on
{lit}`V × V'`. This is exactly mathlib's evaluation map {name}`Module.Dual.eval`
(here viewed as a bilinear functional {lit}`V →ₗ[F] (Dual F V) →ₗ[F] F`). -/
example : V →ₗ[F] Dual F V →ₗ[F] F := Module.Dual.eval F V

example (v : V) (φ : Dual F V) : Module.Dual.eval F V v φ = φ v := rfl

/-- Fifth bullet: {lit}`β(A, B) = tr(AB)` is a bilinear functional on
{lit}`Fᵐ'ⁿ × Fⁿ'ᵐ`. -/
def bilin_9_69_e (m n : ℕ) :
    Matrix (Fin m) (Fin n) F →ₗ[F] Matrix (Fin n) (Fin m) F →ₗ[F] F :=
  LinearMap.mk₂ F (fun A B => (A * B).trace)
    (fun A₁ A₂ B => by simp [Matrix.add_mul, Matrix.trace_add])
    (fun c A B => by simp [Matrix.smul_mul, Matrix.trace_smul])
    (fun A B₁ B₂ => by simp [Matrix.mul_add, Matrix.trace_add])
    (fun c A B => by simp [Matrix.mul_smul, Matrix.trace_smul])

/-! 9.70 Dimension of the vector space of bilinear functionals:
{lit}`dim ℬ(V, W) = (dim V)(dim W)`.

Following Axler, the proof identifies {lit}`ℬ(V, W)` with the space of
{lit}`m`-by-{lit}`n` matrices, giving dimension {lit}`(dim V)(dim W)`. In mathlib
this reduces to two applications of {name}`Module.finrank_linearMap` (proved in
Section 3D as {name}`LADR.Section_3D.finrank_linearMap`): the dimension of a
space of linear maps is the product of the dimensions. -/

theorem finrank_bilinear [Finite F V] [Finite F W] :
    finrank F (V →ₗ[F] W →ₗ[F] F) = finrank F V * finrank F W := by
  rw [LADR.Section_3D.finrank_linearMap, LADR.Section_3D.finrank_linearMap,
      Module.finrank_self, mul_one]

/-! 9.71 Definition: tensor product, {lit}`V ⊗ W`, {lit}`v ⊗ w`.

Axler defines {lit}`V ⊗ W` to be {lit}`ℬ(V', W')`, the bilinear functionals on the
dual spaces, with {lit}`(v ⊗ w)(φ, τ) = φ(v)τ(w)`. mathlib instead constructs the
tensor product {name}`TensorProduct` (notation {lit}`V ⊗[F] W`) as a quotient of the
free module on {lit}`V × W`, with elementary tensors {lit}`v ⊗ₜ[F] w`
({name}`TensorProduct.tmul`). The two constructions are canonically isomorphic in
finite dimensions (both have dimension {lit}`(dim V)(dim W)` and satisfy the same
universal property, 9.79). We use mathlib's {name}`TensorProduct` throughout. -/

example : Type _ := V ⊗[F] W

example (v : V) (w : W) : V ⊗[F] W := v ⊗ₜ[F] w

/-- Every element of {lit}`V ⊗ W` is a finite sum of elementary tensors, the
induction principle {name}`TensorProduct.inductionOn` (no zero case is needed:
{lit}`0 = 0 ⊗ 0`). -/
example (x : V ⊗[F] W) (motive : V ⊗[F] W → Prop)
    (htmul : ∀ v w, motive (v ⊗ₜ[F] w))
    (hadd : ∀ x y, motive x → motive y → motive (x + y)) : motive x :=
  TensorProduct.inductionOn x htmul hadd

/-! 9.72 Dimension of the tensor product of two vector spaces:
{lit}`dim(V ⊗ W) = (dim V)(dim W)`.

mathlib provides this directly as {name}`Module.finrank_tensorProduct`. -/

theorem finrank_tensorProduct [Finite F V] [Finite F W] :
    finrank F (V ⊗[F] W) = finrank F V * finrank F W :=
  Module.finrank_tensorProduct

/-! 9.73 Bilinearity of tensor product.

For {lit}`v, v₁, v₂ ∈ V`, {lit}`w, w₁, w₂ ∈ W`, {lit}`λ ∈ F`, the elementary tensor
is additive in each slot and pulls scalars through either slot. -/

/-- {lit}`(v₁ + v₂) ⊗ w = v₁ ⊗ w + v₂ ⊗ w`. -/
theorem add_tmul (v₁ v₂ : V) (w : W) :
    (v₁ + v₂) ⊗ₜ[F] w = v₁ ⊗ₜ[F] w + v₂ ⊗ₜ[F] w :=
  TensorProduct.add_tmul v₁ v₂ w

/-- {lit}`v ⊗ (w₁ + w₂) = v ⊗ w₁ + v ⊗ w₂`. -/
theorem tmul_add (v : V) (w₁ w₂ : W) :
    v ⊗ₜ[F] (w₁ + w₂) = v ⊗ₜ[F] w₁ + v ⊗ₜ[F] w₂ :=
  TensorProduct.tmul_add v w₁ w₂

/-- {lit}`λ(v ⊗ w) = (λv) ⊗ w = v ⊗ (λw)`. -/
theorem smul_tmul (l : F) (v : V) (w : W) :
    l • (v ⊗ₜ[F] w) = (l • v) ⊗ₜ[F] w ∧ (l • v) ⊗ₜ[F] w = v ⊗ₜ[F] (l • w) :=
  ⟨TensorProduct.smul_tmul' l v w, TensorProduct.smul_tmul l v w⟩

/-! 9.74 Basis of {lit}`V ⊗ W`.

The doubly indexed list {lit}`{eⱼ ⊗ fₖ}` (indexed by the product {lit}`Fin m × Fin n`,
mathlib's natural index for the tensor-product basis) is linearly independent when
{lit}`e` and {lit}`f` are, and is a basis when {lit}`e` and {lit}`f` are bases. -/

/-- (a) If {lit}`e₁, …, eₘ` and {lit}`f₁, …, fₙ` are both linearly independent, then
{lit}`{eⱼ ⊗ fₖ}` is linearly independent. Axler's proof builds dual functionals
{lit}`φⱼ, τₖ` and evaluates a vanishing combination at {lit}`(φ_M, τ_N)`; mathlib
packages the same fact as {name}`LinearIndependent.tmul_of_flat_left` (a vector
space over {lit}`F` is free, hence flat). -/
theorem linearIndependent_tmul {ι κ : Type*} {e : ι → V} {f : κ → W}
    (he : LinearIndependent F e) (hf : LinearIndependent F f) :
    LinearIndependent F (fun i : ι × κ => e i.1 ⊗ₜ[F] f i.2) :=
  he.tmul_of_flat_left hf

/-- (b) If {lit}`e₁, …, eₘ` is a basis of {lit}`V` and {lit}`f₁, …, fₙ` is a basis of
{lit}`W`, then {lit}`{eⱼ ⊗ fₖ}` is a basis of {lit}`V ⊗ W`, via
{name}`Module.Basis.tensorProduct`. -/
noncomputable def basis_tensorProduct {m n : ℕ} {e : Fin m → V} {f : Fin n → W}
    (he : IsBasis F e) (hf : IsBasis F f) :
    Module.Basis (Fin m × Fin n) F (V ⊗[F] W) :=
  he.toModuleBasis.tensorProduct hf.toModuleBasis

theorem basis_tensorProduct_apply {m n : ℕ} {e : Fin m → V} {f : Fin n → W}
    (he : IsBasis F e) (hf : IsBasis F f) (j : Fin m) (k : Fin n) :
    basis_tensorProduct he hf (j, k) = e j ⊗ₜ[F] f k := by
  rw [basis_tensorProduct, Module.Basis.tensorProduct_apply,
      IsBasis.toModuleBasis_apply, IsBasis.toModuleBasis_apply]

/-! 9.76 Example: tensor product of an element of {lit}`Fᵐ` with an element of
{lit}`Fⁿ`. With respect to the basis {lit}`{eⱼ ⊗ fₖ}` of {lit}`Fᵐ ⊗ Fⁿ` coming from
the standard bases (9.74(b)), the coefficient of {lit}`v ⊗ w` at {lit}`(j, k)` is
{lit}`vⱼwₖ` — the entries of the rank-one matrix {lit}`v wᵗ`. -/

theorem tmul_repr_stdBasis {m n : ℕ} (v : Fin m → F) (w : Fin n → F)
    (j : Fin m) (k : Fin n) :
    ((Pi.basisFun F (Fin m)).tensorProduct (Pi.basisFun F (Fin n))).repr
        (v ⊗ₜ[F] w) (j, k) = v j * w k := by
  rw [Module.Basis.tensorProduct_repr_tmul_apply]
  simp [Pi.basisFun_repr, mul_comm]

/-! 9.77 Definition: bilinear map.

A bilinear map from {lit}`V × W` to a vector space {lit}`U` is linear in each slot;
in mathlib this is {lit}`V →ₗ[F] W →ₗ[F] U`. (A bilinear functional, 9.68, is the
special case {lit}`U = F`.) -/

example : Type _ := V →ₗ[F] W →ₗ[F] U

/-! 9.78 Example: bilinear maps. -/

/-- Second bullet: {lit}`Γ(v, w) = v ⊗ w` is a bilinear map from {lit}`V × W` to
{lit}`V ⊗ W`. This is mathlib's {name}`TensorProduct.mk`. -/
example : V →ₗ[F] W →ₗ[F] V ⊗[F] W := TensorProduct.mk F V W

example (v : V) (w : W) : TensorProduct.mk F V W v w = v ⊗ₜ[F] w := rfl

/-- Third bullet: {lit}`Γ(S, T) = ST` is a bilinear map on {lit}`ℒ(V) × ℒ(V)`,
namely composition {lit}`LinearMap.mulₗ` / {name}`LinearMap.mul`. -/
example : (V →ₗ[F] V) →ₗ[F] (V →ₗ[F] V) →ₗ[F] (V →ₗ[F] V) := LinearMap.mul F (V →ₗ[F] V)

example (S T : V →ₗ[F] V) : LinearMap.mul F (V →ₗ[F] V) S T = S ∘ₗ T := rfl

/-- Fourth bullet: {lit}`Γ(v, T) = Tv` is a bilinear map from
{lit}`V × ℒ(V, W)` to {lit}`W`. -/
def bilin_9_78_d : V →ₗ[F] (V →ₗ[F] W) →ₗ[F] W :=
  LinearMap.mk₂ F (fun v T => T v)
    (fun v₁ v₂ T => by simp)
    (fun c v T => by simp)
    (fun v T₁ T₂ => by simp)
    (fun c v T => by simp)

/-! 9.79 Converting bilinear maps to linear maps (the universal property of the
tensor product). -/

/-- (a) Every bilinear map {lit}`Γ : V × W → U` factors as {lit}`Γ = Γ̂ ∘ ⊗` through
a *unique* linear map {lit}`Γ̂ : V ⊗ W → U` with {lit}`Γ̂(v ⊗ w) = Γ(v, w)`. mathlib's
witness is {name}`TensorProduct.lift`; the factoring is {name}`TensorProduct.lift.tmul`
and the uniqueness is {name}`TensorProduct.lift.unique`. -/
theorem lift_tmul (Γ : V →ₗ[F] W →ₗ[F] U) (v : V) (w : W) :
    TensorProduct.lift Γ (v ⊗ₜ[F] w) = Γ v w :=
  TensorProduct.lift.tmul v w

theorem lift_unique (Γ : V →ₗ[F] W →ₗ[F] U) (g : V ⊗[F] W →ₗ[F] U)
    (hg : ∀ v w, g (v ⊗ₜ[F] w) = Γ v w) : g = TensorProduct.lift Γ :=
  TensorProduct.lift.unique hg

/-- (b) Conversely, every linear map {lit}`T : V ⊗ W → U` restricts to a *unique*
bilinear map {lit}`T# : V × W → U` with {lit}`T#(v, w) = T(v ⊗ w)`, namely
{lit}`T# = T ∘ (v, w ↦ v ⊗ w)` ({name}`LinearMap.compr₂` of {name}`TensorProduct.mk`). -/
def uncurryTensor (T : V ⊗[F] W →ₗ[F] U) : V →ₗ[F] W →ₗ[F] U :=
  LinearMap.compr₂ (TensorProduct.mk F V W) T

theorem uncurryTensor_apply (T : V ⊗[F] W →ₗ[F] U) (v : V) (w : W) :
    uncurryTensor T v w = T (v ⊗ₜ[F] w) := rfl

theorem uncurryTensor_unique (T : V ⊗[F] W →ₗ[F] U) (S : V →ₗ[F] W →ₗ[F] U)
    (hS : ∀ v w, S v w = T (v ⊗ₜ[F] w)) : S = uncurryTensor T := by
  ext v w
  rw [uncurryTensor_apply, hS]

/-! # Tensor Product of Inner Product Spaces -/

/-! 9.80 / 9.82 Inner product on the tensor product of two inner product spaces.

The tensor product {lit}`V ⊗ W` of two inner product spaces carries a unique inner
product determined by {lit}`⟨v ⊗ w, u ⊗ x⟩ = ⟨v, u⟩⟨w, x⟩`. In the pinned mathlib
this is {name}`TensorProduct.instInnerProductSpace`, and the defining identity is
{name}`TensorProduct.inner_tmul`. -/

open scoped InnerProductSpace in
theorem inner_tmul_tensor {𝕜 : Type*} [RCLike 𝕜] {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (v u : E) (w x : G) :
    ⟪v ⊗ₜ[𝕜] w, u ⊗ₜ[𝕜] x⟫_𝕜 = ⟪v, u⟫_𝕜 * ⟪w, x⟫_𝕜 :=
  TensorProduct.inner_tmul 𝕜 v u w x

/-! 9.83 Orthonormal basis of {lit}`V ⊗ W`: the tensor products {lit}`{eⱼ ⊗ fₖ}` of
orthonormal families form an orthonormal family, since
{lit}`⟨eⱼ ⊗ fₖ, e_M ⊗ f_N⟩ = ⟨eⱼ, e_M⟩⟨fₖ, f_N⟩` is {lit}`1` when
{lit}`(j, k) = (M, N)` and {lit}`0` otherwise. -/

theorem orthonormal_tmul {𝕜 : Type*} [RCLike 𝕜] {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι κ : Type*} {e : ι → E} {f : κ → G}
    (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f) :
    Orthonormal 𝕜 (fun p : ι × κ => e p.1 ⊗ₜ[𝕜] f p.2) :=
  he.tmul hf

/-! # Tensor Product of Multiple Vector Spaces -/

/-! 9.84 Notation: {lit}`V₁, …, Vₘ`. Throughout this subsection {lit}`m > 1` and the
spaces are given as a family {lit}`Vi : Fin m → Type*` of finite-dimensional vector
spaces. -/

/-! 9.85 Definition: {lit}`m`-linear functional, the vector space
{lit}`ℬ(V₁, …, Vₘ)`.

An {lit}`m`-linear functional on {lit}`V₁ × ⋯ × Vₘ` is linear in each slot; this is a
mathlib {name}`MultilinearMap` into {lit}`F`. -/

example {m : ℕ} (Vi : Fin m → Type*) [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] : Type _ := MultilinearMap F Vi F

/-! 9.86 Example: {lit}`m`-linear functional. For {lit}`φₖ ∈ Vₖ'`, the product
{lit}`β(v₁, …, vₘ) = φ₁(v₁) ⋯ φₘ(vₘ)` is an {lit}`m`-linear functional, built by
composing the coordinate functionals into the product form
{name}`MultilinearMap.mkPiAlgebra`. -/

def mlinear_9_86 {m : ℕ} {Vi : Fin m → Type*} [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] (φ : ∀ i, Dual F (Vi i)) : MultilinearMap F Vi F :=
  (MultilinearMap.mkPiAlgebra F (Fin m) F).compLinearMap φ

theorem mlinear_9_86_apply {m : ℕ} {Vi : Fin m → Type*} [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] (φ : ∀ i, Dual F (Vi i)) (v : ∀ i, Vi i) :
    mlinear_9_86 φ v = ∏ i, φ i (v i) := by
  rw [mlinear_9_86, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-! 9.87 Dimension of the vector space of {lit}`m`-linear functionals:
{lit}`dim ℬ(V₁, …, Vₘ) = (dim V₁) ⋯ (dim Vₘ)`.

The two-space case is 9.70. Via the universal property {name}`PiTensorProduct.lift`
(a linear equivalence) the space of {lit}`m`-linear functionals is the dual of the
iterated tensor product {lit}`V₁ ⊗ ⋯ ⊗ Vₘ`, so its dimension equals that of the
tensor product; the latter is a product of {lit}`dim Vᵢ` by the tensor-product
basis {name}`Basis.piTensorProduct` (9.90 below). As in 9.70 the dual step is just
{name}`LADR.Section_3D.finrank_linearMap` into the {lit}`1`-dimensional {lit}`F`. -/
theorem finrank_multilinearForms {m : ℕ} {Vi : Fin m → Type*}
    [∀ i, AddCommGroup (Vi i)] [∀ i, Module F (Vi i)] [∀ i, Finite F (Vi i)] :
    finrank F (MultilinearMap F Vi F) = ∏ i, finrank F (Vi i) := by
  classical
  have hb := Basis.piTensorProduct (fun i => Module.finBasis F (Vi i))
  have : Module.Finite F (⨂[F] i, Vi i) := Module.Finite.of_basis hb
  rw [LinearEquiv.finrank_eq PiTensorProduct.lift, LADR.Section_3D.finrank_linearMap,
    Module.finrank_self, mul_one, Module.finrank_eq_card_basis hb, Fintype.card_pi]
  simp [Fintype.card_fin]

/-! 9.88 Definition: tensor product {lit}`V₁ ⊗ ⋯ ⊗ Vₘ`, {lit}`v₁ ⊗ ⋯ ⊗ vₘ`.

mathlib's iterated tensor product is {name}`PiTensorProduct`, written
{lit}`⨂[F] i, Vi i`, with elementary tensors {name}`PiTensorProduct.tprod`. -/

example {m : ℕ} (Vi : Fin m → Type*) [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] : Type _ := ⨂[F] i, Vi i

example {m : ℕ} {Vi : Fin m → Type*} [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] (v : ∀ i, Vi i) : ⨂[F] i, Vi i :=
  PiTensorProduct.tprod F v

/-! 9.89 Dimension of the tensor product:
{lit}`dim(V₁ ⊗ ⋯ ⊗ Vₘ) = (dim V₁) ⋯ (dim Vₘ)`.

The {lit}`m = 2` case is 9.72. In general the tensor-product basis 9.90 has index
{lit}`∏ᵢ κᵢ` (functions choosing one basis vector per factor), so its cardinality —
and hence the dimension — is the product {lit}`∏ᵢ dim Vᵢ`. -/
theorem finrank_piTensorProduct {m : ℕ} {Vi : Fin m → Type*}
    [∀ i, AddCommGroup (Vi i)] [∀ i, Module F (Vi i)] [∀ i, Finite F (Vi i)] :
    finrank F (⨂[F] i, Vi i) = ∏ i, finrank F (Vi i) := by
  classical
  rw [Module.finrank_eq_card_basis
      (Basis.piTensorProduct (fun i => Module.finBasis F (Vi i))), Fintype.card_pi]
  simp [Fintype.card_fin]

/-! 9.90 Basis of {lit}`V₁ ⊗ ⋯ ⊗ Vₘ`.

The {lit}`m = 2` case is 9.74(b) ({name}`Module.Basis.tensorProduct`). For a finite
family, if {lit}`bᵢ` is a basis of {lit}`Vᵢ` (indexed by {lit}`κᵢ`) then the
elementary tensors {lit}`⨂ᵢ bᵢ(pᵢ)`, one per choice function {lit}`p ∈ ∏ᵢ κᵢ`, form
a basis of {lit}`V₁ ⊗ ⋯ ⊗ Vₘ`, via {name}`Basis.piTensorProduct`. -/
noncomputable def basis_piTensorProduct {m : ℕ} {Vi : Fin m → Type*}
    [∀ i, AddCommGroup (Vi i)] [∀ i, Module F (Vi i)] {κ : Fin m → Type*}
    (b : ∀ i, Module.Basis (κ i) F (Vi i)) :
    Module.Basis (∀ i, κ i) F (⨂[F] i, Vi i) :=
  Basis.piTensorProduct b

theorem basis_piTensorProduct_apply {m : ℕ} {Vi : Fin m → Type*}
    [∀ i, AddCommGroup (Vi i)] [∀ i, Module F (Vi i)] {κ : Fin m → Type*}
    (b : ∀ i, Module.Basis (κ i) F (Vi i)) (p : ∀ i, κ i) :
    basis_piTensorProduct b p = ⨂ₜ[F] i, b i (p i) :=
  Basis.piTensorProduct_apply b p

/-! 9.91 Definition: {lit}`m`-linear map.

An {lit}`m`-linear map from {lit}`V₁ × ⋯ × Vₘ` to a vector space {lit}`U` is a
{name}`MultilinearMap` into {lit}`U`. -/

example {m : ℕ} (Vi : Fin m → Type*) [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] : Type _ := MultilinearMap F Vi U

/-! 9.92 Converting {lit}`m`-linear maps to linear maps (the universal property of
the iterated tensor product). -/

/-- (a) Every {lit}`m`-linear map {lit}`Γ : V₁ × ⋯ × Vₘ → U` factors uniquely through
{lit}`Γ̂ : V₁ ⊗ ⋯ ⊗ Vₘ → U` with {lit}`Γ̂(v₁ ⊗ ⋯ ⊗ vₘ) = Γ(v₁, …, vₘ)`, via
{name}`PiTensorProduct.lift`. -/
theorem piLift_tprod {m : ℕ} {Vi : Fin m → Type*} [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] (Γ : MultilinearMap F Vi U) (v : ∀ i, Vi i) :
    PiTensorProduct.lift Γ (PiTensorProduct.tprod F v) = Γ v :=
  PiTensorProduct.lift.tprod v

theorem piLift_unique {m : ℕ} {Vi : Fin m → Type*} [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] (Γ : MultilinearMap F Vi U)
    (g : (⨂[F] i, Vi i) →ₗ[F] U)
    (hg : ∀ v, g (PiTensorProduct.tprod F v) = Γ v) : g = PiTensorProduct.lift Γ :=
  PiTensorProduct.lift.unique hg

/-- (b) Conversely, every linear map {lit}`T : V₁ ⊗ ⋯ ⊗ Vₘ → U` restricts to a
unique {lit}`m`-linear map {lit}`T#(v₁, …, vₘ) = T(v₁ ⊗ ⋯ ⊗ vₘ)`, namely
{lit}`T ∘ tprod` ({name}`LinearMap.compMultilinearMap`). -/
def uncurryPiTensor {m : ℕ} {Vi : Fin m → Type*} [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] (T : (⨂[F] i, Vi i) →ₗ[F] U) : MultilinearMap F Vi U :=
  T.compMultilinearMap (PiTensorProduct.tprod F)

theorem uncurryPiTensor_apply {m : ℕ} {Vi : Fin m → Type*} [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] (T : (⨂[F] i, Vi i) →ₗ[F] U) (v : ∀ i, Vi i) :
    uncurryPiTensor T v = T (PiTensorProduct.tprod F v) := rfl

theorem uncurryPiTensor_unique {m : ℕ} {Vi : Fin m → Type*} [∀ i, AddCommGroup (Vi i)]
    [∀ i, Module F (Vi i)] (T : (⨂[F] i, Vi i) →ₗ[F] U) (S : MultilinearMap F Vi U)
    (hS : ∀ v, S v = T (PiTensorProduct.tprod F v)) : S = uncurryPiTensor T := by
  ext v
  rw [uncurryPiTensor_apply, hS]

/-! # Exercises 9D -/

/-- 9D.1 {lit}`v ⊗ w = 0` if and only if {lit}`v = 0` or {lit}`w = 0`. -/
theorem exercise_9D_1 (v : V) (w : W) :
    v ⊗ₜ[F] w = 0 ↔ v = 0 ∨ w = 0 := by
  sorry

/-- 9D.2 Six distinct vectors in {lit}`ℝ³` with
{lit}`v₁ ⊗ w₁ + v₂ ⊗ w₂ + v₃ ⊗ w₃ = 0` but no {lit}`vᵢ ⊗ wᵢ` a scalar multiple of
another. -/
theorem exercise_9D_2 :
    ∃ v w : Fin 3 → (Fin 3 → ℝ),
      (Function.Injective ![v 0, v 1, v 2, w 0, w 1, w 2]) ∧
      (v 0) ⊗ₜ[ℝ] (w 0) + (v 1) ⊗ₜ[ℝ] (w 1) + (v 2) ⊗ₜ[ℝ] (w 2) = 0 ∧
      (∀ i j : Fin 3, i ≠ j →
        ¬ ∃ c : ℝ, (v i) ⊗ₜ[ℝ] (w i) = c • ((v j) ⊗ₜ[ℝ] (w j))) := by
  sorry

/-- 9D.3 If {lit}`v₁, …, vₘ` is linearly independent and
{lit}`v₁ ⊗ w₁ + ⋯ + vₘ ⊗ wₘ = 0`, then {lit}`w₁ = ⋯ = wₘ = 0`. -/
theorem exercise_9D_3 {m : ℕ} (v : Fin m → V) (w : Fin m → W)
    (hv : LinearIndependent F v) (h : ∑ i, v i ⊗ₜ[F] w i = 0) :
    ∀ i, w i = 0 := by
  sorry

/-- 9D.4 If {lit}`dim V > 1` and {lit}`dim W > 1`, then the set of elementary
tensors {lit}`{v ⊗ w}` is not a subspace of {lit}`V ⊗ W`. We phrase "not a subspace"
as: it is not closed under addition. -/
theorem exercise_9D_4 [Finite F V] [Finite F W]
    (hV : 1 < finrank F V) (hW : 1 < finrank F W) :
    ¬ ∀ x y : V ⊗[F] W,
        (∃ v w, x = v ⊗ₜ[F] w) → (∃ v w, y = v ⊗ₜ[F] w) →
          ∃ v w, x + y = v ⊗ₜ[F] w := by
  sorry

/-- 9D.5 For {lit}`v ∈ Fᵐ`, {lit}`w ∈ Fⁿ`, identifying {lit}`v ⊗ w` with the matrix
{lit}`(vⱼwₖ)`, the set {lit}`{v ⊗ w}` is exactly the matrices of rank at most one.
We use the matrix with entries {lit}`Aⱼ,ₖ = vⱼwₖ` (an outer product) as the
identification. -/
theorem exercise_9D_5 {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    (∃ v : Fin m → F, ∃ w : Fin n → F, ∀ j k, A j k = v j * w k) ↔
      A.rank ≤ 1 := by
  sorry

/-- 9D.6 Analogously to 9D.5, the {lit}`m×n` matrices of rank at most two are
exactly the sums of two outer products {lit}`v₁w₁ᵀ + v₂w₂ᵀ`. -/
theorem exercise_9D_6 {m n : ℕ} (A : Matrix (Fin m) (Fin n) F) :
    (∃ v : Fin 2 → (Fin m → F), ∃ w : Fin 2 → (Fin n → F),
        ∀ j k, A j k = ∑ i, v i j * w i k) ↔
      A.rank ≤ 2 := by
  sorry

/-- 9D.7 If {lit}`dim V > 2` and {lit}`dim W > 2`, then the sums of two elementary
tensors do not exhaust {lit}`V ⊗ W`. -/
theorem exercise_9D_7 [Finite F V] [Finite F W]
    (hV : 2 < finrank F V) (hW : 2 < finrank F W) :
    ∃ x : V ⊗[F] W, ¬ ∃ v₁ v₂ : V, ∃ w₁ w₂ : W,
      x = v₁ ⊗ₜ[F] w₁ + v₂ ⊗ₜ[F] w₂ := by
  sorry

/-- 9D.8 If {lit}`v₁ ⊗ w₁ + ⋯ + vₘ ⊗ wₘ = 0` and {lit}`Γ : V × W → U` is bilinear,
then {lit}`Γ(v₁, w₁) + ⋯ + Γ(vₘ, wₘ) = 0`. (This is the universal property 9.79:
apply {lit}`Γ̂ = lift Γ`, a linear map, to the vanishing sum.) -/
theorem exercise_9D_8 {m : ℕ} (v : Fin m → V) (w : Fin m → W)
    (h : ∑ i, v i ⊗ₜ[F] w i = 0) (Γ : V →ₗ[F] W →ₗ[F] U) :
    ∑ i, Γ (v i) (w i) = 0 := by
  sorry

/-- 9D.9 For {lit}`S ∈ ℒ(V)` and {lit}`T ∈ ℒ(W)` there is a unique operator on
{lit}`V ⊗ W` taking {lit}`v ⊗ w` to {lit}`Sv ⊗ Tw`; mathlib's witness is
{name}`TensorProduct.map`. The exercise is existence and uniqueness. -/
theorem exercise_9D_9 (S : V →ₗ[F] V) (T : W →ₗ[F] W) :
    ∃! P : V ⊗[F] W →ₗ[F] V ⊗[F] W,
      ∀ v w, P (v ⊗ₜ[F] w) = (S v) ⊗ₜ[F] (T w) := by
  sorry

/-- 9D.10 {lit}`S ⊗ T` is invertible iff both {lit}`S` and {lit}`T` are, and then
{lit}`(S ⊗ T)⁻¹ = S⁻¹ ⊗ T⁻¹`. We phrase it with {name}`TensorProduct.map` and
bijectivity. -/
theorem exercise_9D_10 [Finite F V] [Finite F W] (S : V →ₗ[F] V) (T : W →ₗ[F] W) :
    Function.Bijective (TensorProduct.map S T) ↔
      (Function.Bijective S ∧ Function.Bijective T) := by
  sorry

open scoped InnerProductSpace in
/-- 9D.11 For inner product spaces {lit}`V, W` and {lit}`S ∈ ℒ(V)`, {lit}`T ∈ ℒ(W)`,
the adjoint of {lit}`S ⊗ T` on {lit}`V ⊗ W` is {lit}`S* ⊗ T*`. (mathlib's tensor
inner product is {name}`TensorProduct.instInnerProductSpace`.) -/
theorem exercise_9D_11 {𝕜 : Type*} [RCLike 𝕜] {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
    (S : E →ₗ[𝕜] E) (T : G →ₗ[𝕜] G) :
    LinearMap.adjoint (TensorProduct.map S T) =
      TensorProduct.map (LinearMap.adjoint S) (LinearMap.adjoint T) := by
  sorry

open scoped InnerProductSpace in
/-- 9D.12 The inner product on {lit}`V ⊗ W` (LADR 9.80) satisfies
{lit}`⟨v ⊗ w, u ⊗ u'⟩ = ⟨v, u⟩⟨w, u'⟩`, and hence {lit}`‖v ⊗ w‖ = ‖v‖‖w‖`. -/
theorem exercise_9D_12 {𝕜 : Type*} [RCLike 𝕜] {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (v u : E) (w u' : G) :
    (⟪v ⊗ₜ[𝕜] w, u ⊗ₜ[𝕜] u'⟫_𝕜 = ⟪v, u⟫_𝕜 * ⟪w, u'⟫_𝕜) ∧
      ‖v ⊗ₜ[𝕜] w‖ = ‖v‖ * ‖w‖ := by
  sorry

/-- 9D.13 With that inner product, the tensor products {lit}`eᵢ ⊗ fⱼ` of orthonormal
families are orthonormal (so an orthonormal basis of {lit}`V ⊗ W`). -/
theorem exercise_9D_13 {𝕜 : Type*} [RCLike 𝕜] {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {ι κ : Type*} {e : ι → E} {f : κ → G} (he : Orthonormal 𝕜 e) (hf : Orthonormal 𝕜 f) :
    Orthonormal 𝕜 (fun p : ι × κ => e p.1 ⊗ₜ[𝕜] f p.2) := by
  sorry

end LADR.Section_9D
