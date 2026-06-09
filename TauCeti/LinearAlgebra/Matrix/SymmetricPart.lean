/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Symmetric parts of real square matrices

This file records the elementary real matrix API for the symmetric part `(A + Aᵀ) / 2`.

## Main declarations

* `TauCeti.Matrix.symmetricPart`: the symmetric part `(A + Aᵀ) / 2` of a real square matrix.
* `TauCeti.Matrix.symmetricPart_isSymm`: the symmetric part of any real square matrix is
  symmetric.
* `TauCeti.Matrix.symmetricPart_of_isSymm`: a symmetric real square matrix equals its
  symmetric part.
* `TauCeti.Matrix.toQuadraticForm'_symmetricPart`: taking symmetric parts preserves the
  real quadratic form.
-/

namespace TauCeti

namespace Matrix

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's matrix quadratic form is the dot-product expression `ξᵀ A ξ`. -/
lemma toQuadraticForm'_eq_dotProduct (A : _root_.Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    A.toQuadraticForm' ξ = ξ ⬝ᵥ A.mulVec ξ := by
  rw [_root_.Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, _root_.Matrix.toLinearMap₂'_apply']

/-- Transposition does not change the quadratic form associated to a real matrix. -/
@[simp]
lemma toQuadraticForm'_transpose (A : _root_.Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    A.transpose.toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct,
    _root_.Matrix.dotProduct_transpose_mulVec]

/-- Matrix quadratic forms are linear in scalar multiplication of the coefficient matrix. -/
@[simp]
lemma toQuadraticForm'_smul (c : ℝ) (A : _root_.Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (c • A).toQuadraticForm' ξ = c * A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct,
    _root_.Matrix.smul_mulVec, _root_.dotProduct_smul]
  simp [smul_eq_mul]

/-- The symmetric part `(A + Aᵀ) / 2` of a real square matrix. -/
noncomputable def symmetricPart (A : _root_.Matrix n n ℝ) : _root_.Matrix n n ℝ :=
  (2⁻¹ : ℝ) • (A + A.transpose)

omit [Fintype n] [DecidableEq n] in
/-- The symmetric part of a matrix is symmetric. -/
lemma symmetricPart_isSymm (A : _root_.Matrix n n ℝ) : (symmetricPart A).IsSymm :=
  (_root_.Matrix.isSymm_add_transpose_self A).smul _

omit [Fintype n] [DecidableEq n] in
/-- A symmetric matrix is equal to its symmetric part. -/
lemma symmetricPart_of_isSymm {A : _root_.Matrix n n ℝ} (hA : A.IsSymm) :
    symmetricPart A = A := by
  ext i j
  simp [symmetricPart, hA.eq]
  ring

/-- The symmetric part has the same quadratic form as the original matrix. -/
@[simp]
lemma toQuadraticForm'_symmetricPart (A : _root_.Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (symmetricPart A).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct]
  simp only [symmetricPart, _root_.Matrix.smul_mulVec, _root_.Matrix.add_mulVec,
    _root_.dotProduct_smul, _root_.dotProduct_add, smul_eq_mul,
    _root_.Matrix.dotProduct_transpose_mulVec]
  ring

end Matrix

end TauCeti
