/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.Symmetric
import TauCeti.LinearAlgebra.Matrix.QuadraticForm

/-!
# Symmetric parts of square matrices

This file records elementary matrix API for the symmetric part `(A + Aᵀ) / 2` over a
commutative ring where `2` is invertible.

## Main declarations

* `TauCeti.Matrix.symmetricPart`: the symmetric part `(A + Aᵀ) / 2` of a square matrix.
* `TauCeti.Matrix.symmetricPart_def`: the defining formula for the symmetric part.
* `TauCeti.Matrix.isSymm_symmetricPart`: the symmetric part of any square matrix is symmetric.
* `TauCeti.Matrix.symmetricPart_of_isSymm`: a symmetric square matrix equals its symmetric part.
* `TauCeti.Matrix.toBilin'_symmetricPart`: the bilinear form of the symmetric part is the
  bilinear form associated to the original matrix's quadratic form.
* `TauCeti.Matrix.symmetricPart_eq_toMatrix'_toQuadraticForm'`: the symmetric part is
  Mathlib's associated matrix of the quadratic form attached to `A`.
* `TauCeti.Matrix.toQuadraticForm'_symmetricPart`: taking symmetric parts preserves the
  real quadratic form.
-/

namespace TauCeti

namespace Matrix

open scoped Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [Invertible (2 : R)]

/-- The symmetric part `(A + Aᵀ) / 2` of a square matrix. -/
noncomputable def symmetricPart (A : _root_.Matrix n n R) : _root_.Matrix n n R :=
  ⅟(2 : R) • (A + A.transpose)

omit [Fintype n] [DecidableEq n] in
/-- Characteristic formula for the symmetric part of a matrix. -/
@[simp]
lemma symmetricPart_def (A : _root_.Matrix n n R) :
    symmetricPart A = ⅟(2 : R) • (A + A.transpose) :=
  rfl

omit [Fintype n] [DecidableEq n] in
/-- The symmetric part of a matrix is symmetric. -/
@[simp]
lemma isSymm_symmetricPart (A : _root_.Matrix n n R) : (symmetricPart A).IsSymm :=
  (_root_.Matrix.isSymm_add_transpose_self A).smul _

omit [Fintype n] [DecidableEq n] in
/-- A symmetric matrix is equal to its symmetric part. -/
@[simp]
lemma symmetricPart_of_isSymm {A : _root_.Matrix n n R} (hA : A.IsSymm) :
    symmetricPart A = A := by
  ext i j
  change ⅟(2 : R) * (A i j + A j i) = A i j
  rw [hA.apply]
  rw [← two_mul, ← mul_assoc, invOf_mul_self, one_mul]

/-- The bilinear form of the symmetric part is the associated bilinear form of the quadratic
form attached to the original matrix. -/
lemma toBilin'_symmetricPart (A : _root_.Matrix n n R) :
    _root_.Matrix.toBilin' (symmetricPart A) = A.toQuadraticForm'.associated := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  rw [symmetricPart_def, _root_.Matrix.toQuadraticForm',
    _root_.QuadraticMap.associated_toQuadraticMap]
  rw [_root_.Matrix.toBilin'_apply', _root_.Matrix.smul_mulVec, _root_.Matrix.add_mulVec,
    _root_.dotProduct_smul, _root_.dotProduct_add,
    _root_.Matrix.dotProduct_transpose_mulVec, _root_.Matrix.toLinearMap₂'_apply',
    _root_.Matrix.toLinearMap₂'_apply']
  rfl

/-- The symmetric part is Mathlib's associated matrix of the quadratic form attached to `A`. -/
lemma symmetricPart_eq_toMatrix'_toQuadraticForm' (A : _root_.Matrix n n R) :
    symmetricPart A = A.toQuadraticForm'.toMatrix' := by
  apply (_root_.Matrix.toBilin' : _root_.Matrix n n R ≃ₗ[R] _).injective
  rw [toBilin'_symmetricPart]
  exact (_root_.Matrix.toLinearMap₂'_toMatrix' A.toQuadraticForm'.associated).symm

/-- The symmetric part has the same quadratic form as the original matrix. -/
@[simp]
lemma toQuadraticForm'_symmetricPart (A : _root_.Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (symmetricPart A).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct]
  simp only [symmetricPart_def, invOf_eq_inv, _root_.Matrix.smul_mulVec, _root_.Matrix.add_mulVec,
    _root_.dotProduct_smul, _root_.dotProduct_add, smul_eq_mul,
    _root_.Matrix.dotProduct_transpose_mulVec]
  ring

end Matrix

end TauCeti
