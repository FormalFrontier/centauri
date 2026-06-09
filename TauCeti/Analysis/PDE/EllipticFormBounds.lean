/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.PDE.UniformEllipticity

/-!
# Operator-norm bounds for uniformly elliptic coefficient forms

This file packages the boundedness half of the matrix coefficient API from
`TauCeti.Analysis.PDE.UniformEllipticity`.  The existing predicate
`UniformlyEllipticOn Ω a λ Λ` stores the pointwise estimate

`‖ηᵀ a(x) ξ‖ ≤ Λ ‖η‖ ‖ξ‖`.

For the PDE roadmap's Lane D weak formulation, the same estimate is needed in the bundled
continuous-bilinear-map norm and in radius-restricted forms before the pointwise integrand is
assembled into an energy bilinear form.  The proofs here reuse Mathlib's generic
`ContinuousLinearMap.opNorm_le_bound₂`; no new analytic boundedness principle is introduced.

## Main declarations

* `TauCeti.PDE.matrixBilinearForm_opNorm_le_of_upper_bound`: a pointwise bilinear estimate
  bounds the operator norm of the bundled matrix form.
* `TauCeti.PDE.matrixBilinearForm_apply_norm_le_opNorm`: the specialized operator-norm
  estimate for matrix forms.
* `TauCeti.PDE.UniformlyEllipticOn.opNorm_matrixBilinearForm_le`: a uniformly elliptic
  coefficient field has pointwise operator norm at most its upper ellipticity constant.
* `TauCeti.PDE.UniformlyEllipticOn.norm_point_matrixBilinearForm_le_mul_of_norm_le`:
  bounded vectors give a bounded integrand.

These estimates are deliberately pointwise in `x`; measurability and integration belong to
the later Sobolev-space and energy-form development.
-/

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- A pointwise bilinear upper bound controls the operator norm of the bundled matrix
bilinear form.

This is the matrix-coefficient specialization of Mathlib's
`ContinuousLinearMap.opNorm_le_bound₂`. -/
lemma matrixBilinearForm_opNorm_le_of_upper_bound (A : Matrix n n ℝ) {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ C * ‖η‖ * ‖ξ‖) :
    ‖matrixBilinearForm A‖ ≤ C := by
  refine (matrixBilinearForm A).opNorm_le_bound₂ hC_nonneg ?_
  intro η ξ
  exact norm_matrixBilinearForm_le_of_upper_bound A hA η ξ

/-- The operator norm of a matrix bilinear form gives the usual two-vector bound. -/
lemma matrixBilinearForm_apply_norm_le_opNorm (A : Matrix n n ℝ)
    (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm A η ξ‖ ≤ ‖matrixBilinearForm A‖ * ‖η‖ * ‖ξ‖ :=
  (matrixBilinearForm A).le_opNorm₂ η ξ

/-- If the operator norm of a matrix bilinear form is bounded by `C`, then its value on
vectors of norm at most `R` and `S` is bounded by `C * R * S`. -/
lemma matrixBilinearForm_apply_norm_le_of_opNorm_le {A : Matrix n n ℝ} {C R S : ℝ}
    (hA : ‖matrixBilinearForm A‖ ≤ C) {η ξ : EuclideanSpace ℝ n}
    (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm A η ξ‖ ≤ C * R * S := by
  exact (matrixBilinearForm A).le_of_opNorm₂_le_of_le hA hη hξ

/-- A pointwise bilinear upper bound gives a radius-restricted estimate for the bundled
matrix bilinear form. -/
lemma matrixBilinearForm_apply_norm_le_of_upper_bound {A : Matrix n n ℝ} {C R S : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ C * ‖η‖ * ‖ξ‖)
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm A η ξ‖ ≤ C * R * S :=
  matrixBilinearForm_apply_norm_le_of_opNorm_le
    (matrixBilinearForm_opNorm_le_of_upper_bound A hC_nonneg hA) hη hξ

/-- The identity coefficient matrix has matrix-bilinear-form operator norm at most `1`.

This remains a `≤` statement because the index type may be empty. -/
lemma matrixBilinearForm_one_opNorm_le :
    ‖matrixBilinearForm (1 : Matrix n n ℝ)‖ ≤ 1 := by
  refine matrixBilinearForm_opNorm_le_of_upper_bound (1 : Matrix n n ℝ) zero_le_one ?_
  intro η ξ
  rw [one_mulVec]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    abs_real_inner_le_norm η ξ

/-- A scalar identity coefficient matrix has matrix-bilinear-form operator norm at most
`|c|`. -/
lemma matrixBilinearForm_smul_one_opNorm_le (c : ℝ) :
    ‖matrixBilinearForm (c • (1 : Matrix n n ℝ))‖ ≤ |c| :=
  matrixBilinearForm_opNorm_le_of_upper_bound (c • (1 : Matrix n n ℝ)) (abs_nonneg c)
    (abs_dotProduct_smul_one_mulVec_le_of_abs_le le_rfl)

/-- If a scalar coefficient is bounded in absolute value by `C`, then the operator norm of
the corresponding scalar identity matrix form is at most `C`. -/
lemma matrixBilinearForm_smul_one_opNorm_le_of_abs_le {c C : ℝ} (hc : |c| ≤ C) :
    ‖matrixBilinearForm (c • (1 : Matrix n n ℝ))‖ ≤ C := by
  exact (matrixBilinearForm_smul_one_opNorm_le (n := n) c).trans hc

/-- A scalar identity matrix form evaluated on vectors of norm at most `R` and `S` is
bounded by `|c| * R * S`. -/
lemma matrixBilinearForm_smul_one_apply_norm_le (c : ℝ) {R S : ℝ}
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm (c • (1 : Matrix n n ℝ)) η ξ‖ ≤ |c| * R * S :=
  matrixBilinearForm_apply_norm_le_of_opNorm_le
    (matrixBilinearForm_smul_one_opNorm_le (n := n) c) hη hξ

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}

/-- The upper ellipticity constant is nonnegative. -/
lemma upper_nonneg (h : UniformlyEllipticOn Ω a lam Lam) : 0 ≤ Lam :=
  h.pos.le.trans h.le

/-- At every point of the domain, uniform ellipticity bounds the operator norm of the
attached matrix bilinear form by the upper ellipticity constant. -/
@[grind =>]
lemma opNorm_matrixBilinearForm_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X}
    (hx : x ∈ Ω) :
    ‖matrixBilinearForm (a x)‖ ≤ Lam :=
  matrixBilinearForm_opNorm_le_of_upper_bound (a x) h.upper_nonneg (h.upper_bound hx)

/-- Uniform ellipticity gives a radius-restricted pointwise bound for the coefficient
integrand. -/
lemma norm_point_matrixBilinearForm_le_mul_of_norm_le
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {R S : ℝ}
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * R * S :=
  matrixBilinearForm_apply_norm_le_of_opNorm_le (h.opNorm_matrixBilinearForm_le hx) hη hξ

/-- Uniform ellipticity bounds the bilinear-form value on vectors in the closed ball of
radius `R`. -/
lemma norm_point_matrixBilinearForm_le_mul_of_norm_le_same_radius
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {R : ℝ}
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ R) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * R * R :=
  h.norm_point_matrixBilinearForm_le_mul_of_norm_le hx hη hξ

/-- Uniform ellipticity bounds the coefficient integrand on unit vectors by the upper
ellipticity constant. -/
lemma norm_point_matrixBilinearForm_le_of_norm_le_one
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ 1) (hξ : ‖ξ‖ ≤ 1) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam := by
  simpa using h.norm_point_matrixBilinearForm_le_mul_of_norm_le hx hη hξ

/-- If the coefficient field is uniformly elliptic on a larger domain, the pointwise
operator-norm bound remains available after restricting the domain. -/
lemma opNorm_matrixBilinearForm_le_of_mem_of_subset {Ω' : Set X}
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : Ω' ⊆ Ω) {x : X} (hx : x ∈ Ω') :
    ‖matrixBilinearForm (a x)‖ ≤ Lam :=
  h.opNorm_matrixBilinearForm_le (hΩ hx)

/-- Weakening constants preserves the pointwise operator-norm estimate with the new upper
constant. -/
lemma opNorm_matrixBilinearForm_le_of_mono_constants (h : UniformlyEllipticOn Ω a lam Lam)
    {lam' Lam' : ℝ} (hlam' : 0 < lam') (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam')
    {x : X} (hx : x ∈ Ω) :
    ‖matrixBilinearForm (a x)‖ ≤ Lam' :=
  (h.mono_constants hlam' hlam'_le hLam_le).opNorm_matrixBilinearForm_le hx

end UniformlyEllipticOn

end PDE

end TauCeti
