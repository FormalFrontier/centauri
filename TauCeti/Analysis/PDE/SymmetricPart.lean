/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.PDE.UniformEllipticity
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Symmetric parts of PDE coefficient matrices

For a real divergence-form coefficient matrix `A`, the quadratic expression
`ξᵀ A ξ` only depends on the symmetric part `(A + Aᵀ) / 2`. This file records that
bookkeeping in the explicit-constant API from `TauCeti.Analysis.PDE.UniformEllipticity`.

The main result is `UniformlyEllipticOn.symmetricPart`: a uniformly elliptic, possibly
nonsymmetric coefficient field has a symmetric part that is uniformly elliptic with the
same constants. This is a small prerequisite for the PDE roadmap's energy-form and
Lax--Milgram lane, where coercivity comes from the symmetric quadratic part while
boundedness still controls the full bilinear form.

## Main declarations

* `TauCeti.PDE.symmetricPart`: the symmetric part `(A + Aᵀ) / 2` of a real matrix.
* `TauCeti.PDE.skewPart`: the skew-symmetric part `(A - Aᵀ) / 2`.
* `TauCeti.PDE.toQuadraticForm'_symmetricPart`: symmetrization preserves `ξᵀ A ξ`.
* `TauCeti.PDE.UniformlyEllipticOn.symmetricPart`: uniform ellipticity descends to the
  symmetric part with unchanged constants.
-/

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- The symmetric part `(A + Aᵀ) / 2` of a real matrix. -/
noncomputable def symmetricPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (2 : ℝ)⁻¹ • (A + Aᵀ)

/-- The skew-symmetric part `(A - Aᵀ) / 2` of a real matrix. -/
noncomputable def skewPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (2 : ℝ)⁻¹ • (A - Aᵀ)

omit [Fintype n] [DecidableEq n] in
/-- The symmetric part is symmetric. -/
lemma symmetricPart_isSymm (A : Matrix n n ℝ) : (symmetricPart A).IsSymm := by
  rw [symmetricPart]
  exact (Matrix.isSymm_add_transpose_self A).smul (2 : ℝ)⁻¹

omit [Fintype n] [DecidableEq n] in
/-- The transpose of the skew part is its negative. -/
lemma skewPart_transpose (A : Matrix n n ℝ) : (skewPart A)ᵀ = -skewPart A := by
  ext i j
  simp [skewPart, sub_eq_add_neg]

omit [Fintype n] [DecidableEq n] in
/-- A matrix is the sum of its symmetric and skew-symmetric parts. -/
@[simp]
lemma symmetricPart_add_skewPart (A : Matrix n n ℝ) : symmetricPart A + skewPart A = A := by
  ext i j
  simp [symmetricPart, skewPart]
  ring

/-- Transposing a real matrix does not change its quadratic form. -/
@[simp]
lemma toQuadraticForm'_transpose (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    Aᵀ.toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct]
  exact Matrix.dotProduct_transpose_mulVec A ξ ξ

/-- The skew-symmetric part has zero quadratic form. -/
@[simp]
lemma toQuadraticForm'_skewPart (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (skewPart A).toQuadraticForm' ξ = 0 := by
  have htranspose := toQuadraticForm'_transpose (skewPart A) ξ
  rw [skewPart_transpose] at htranspose
  have hneg :
      (-skewPart A).toQuadraticForm' ξ = - (skewPart A).toQuadraticForm' ξ := by
    simpa using toQuadraticForm'_smul (-1 : ℝ) (skewPart A) ξ
  linarith

/-- The symmetric part has the same quadratic form as the original matrix. -/
@[simp]
lemma toQuadraticForm'_symmetricPart (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (symmetricPart A).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [symmetricPart, toQuadraticForm'_smul, toQuadraticForm'_eq_dotProduct,
    toQuadraticForm'_eq_dotProduct]
  simp only [add_mulVec, dotProduct_add]
  have htranspose : ξ ⬝ᵥ (Aᵀ *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ ξ) :=
    Matrix.dotProduct_transpose_mulVec A ξ ξ
  rw [htranspose]
  ring

/-- On the diagonal, the bilinear form attached to the symmetric part agrees with the
bilinear form attached to the original matrix. -/
@[simp]
lemma matrixBilinearForm_symmetricPart_self (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (symmetricPart A) ξ ξ = matrixBilinearForm A ξ ξ := by
  rw [matrixBilinearForm_self, matrixBilinearForm_self, toQuadraticForm'_symmetricPart]

/-- The bilinear form attached to the symmetric part is the average of the two transposed
placements of the original bilinear form. -/
lemma matrixBilinearForm_symmetricPart_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (symmetricPart A) η ξ =
      (2 : ℝ)⁻¹ * (matrixBilinearForm A η ξ + matrixBilinearForm A ξ η) := by
  rw [symmetricPart, matrixBilinearForm_smul_apply, matrixBilinearForm_apply,
    matrixBilinearForm_apply, matrixBilinearForm_apply]
  rw [add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec]

omit [DecidableEq n] in
/-- If a matrix bilinear form is bounded by `Λ`, then the symmetric part is bounded by the
same `Λ`. -/
lemma abs_dotProduct_symmetricPart_mulVec_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (symmetricPart A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  rw [symmetricPart, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add]
  have htranspose : η ⬝ᵥ (Aᵀ *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ η) :=
    Matrix.dotProduct_transpose_mulVec A η ξ
  rw [htranspose]
  have hηξ := hA η ξ
  have hξη := hA ξ η
  have hnorm_eq : Lam * ‖ξ‖ * ‖η‖ = Lam * ‖η‖ * ‖ξ‖ := by ring
  rw [hnorm_eq] at hξη
  calc
    |(2 : ℝ)⁻¹ * (η ⬝ᵥ (A *ᵥ ξ) + ξ ⬝ᵥ (A *ᵥ η))|
        = (2 : ℝ)⁻¹ * |η ⬝ᵥ (A *ᵥ ξ) + ξ ⬝ᵥ (A *ᵥ η)| := by
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr zero_le_two)]
    _ ≤ (2 : ℝ)⁻¹ * (|η ⬝ᵥ (A *ᵥ ξ)| + |ξ ⬝ᵥ (A *ᵥ η)|) := by
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (inv_nonneg.mpr zero_le_two)
    _ ≤ (2 : ℝ)⁻¹ * (Lam * ‖η‖ * ‖ξ‖ + Lam * ‖η‖ * ‖ξ‖) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (inv_nonneg.mpr zero_le_two)
          · exact hηξ
          · exact hξη
    _ = Lam * ‖η‖ * ‖ξ‖ := by ring

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}

/-- Taking the pointwise symmetric part preserves uniform ellipticity with the same
constants. -/
lemma symmetricPart (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => symmetricPart (a x)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simpa using h.lower_bound hx ξ
  · exact abs_dotProduct_symmetricPart_mulVec_le_of_upper_bound (a x) (h.upper_bound hx) η ξ

/-- At each point of the domain, the symmetric part of a uniformly elliptic coefficient is
a symmetric matrix. -/
lemma symmetricPart_isSymm (_h : UniformlyEllipticOn Ω a lam Lam) {x : X} (_hx : x ∈ Ω) :
    (PDE.symmetricPart (a x)).IsSymm :=
  PDE.symmetricPart_isSymm (a x)

end UniformlyEllipticOn

end PDE

end TauCeti
