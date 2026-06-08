/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Uniform ellipticity for divergence-form PDE coefficients

This file records the explicit-constant matrix inequality used for uniformly elliptic
divergence-form operators. For a coefficient field
`a : X → Matrix n n ℝ` on a domain `Ω : Set X`, the predicate
`UniformlyEllipticOn Ω a λ Λ` means

`λ ‖ξ‖² ≤ ξᵀ a(x) ξ ≤ Λ ‖ξ‖²`

for every `x ∈ Ω` and every vector `ξ`, together with the quantitative side conditions
`0 < λ` and `λ ≤ Λ`.

This is the coefficient hypothesis named in the PDE roadmap before the energy bilinear form
and Lax--Milgram arguments: constants are parameters, not hidden existential data.

## Main declarations

* `TauCeti.PDE.ellipticQuadraticForm`: the scalar `ξᵀ A ξ`.
* `TauCeti.PDE.UniformlyEllipticOn`: uniform lower and upper ellipticity bounds on a set.
* `TauCeti.PDE.uniformlyEllipticOn_const_one`: the identity matrix is uniformly elliptic.
* `TauCeti.PDE.UniformlyEllipticOn.mono_constants`: weakening constants preserves the
  predicate.
* `TauCeti.PDE.UniformlyEllipticOn.mono_set`: restriction to a smaller domain preserves the
  predicate.

The vectors are `EuclideanSpace ℝ n`, matching the roadmap's bounded open subsets of
`ℝⁿ`; this type is reducibly a finite `L²` product, so Mathlib's matrix-vector API applies
directly.
-/

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n]

/-- The quadratic form `ξᵀ A ξ` associated to a real matrix `A`. This is the pointwise
coefficient expression appearing in the ellipticity bounds for divergence-form operators. -/
noncomputable def ellipticQuadraticForm (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) : ℝ :=
  ξ ⬝ᵥ (A *ᵥ ξ)

/-- The identity matrix has quadratic form `‖ξ‖²`. -/
@[simp]
lemma ellipticQuadraticForm_one [DecidableEq n] (ξ : EuclideanSpace ℝ n) :
    ellipticQuadraticForm (1 : Matrix n n ℝ) ξ = ‖ξ‖ ^ 2 := by
  rw [ellipticQuadraticForm, one_mulVec]
  simpa [dotProduct, sq] using (EuclideanSpace.real_norm_sq_eq ξ).symm

/-- Uniform ellipticity with explicit constants on a domain.

The predicate says that for every `x ∈ Ω`, the matrix `a x` has quadratic form bounded below
by `λ‖ξ‖²` and above by `Λ‖ξ‖²`, uniformly in `x` and `ξ`. The side conditions `0 < λ` and
`λ ≤ Λ` are part of the predicate so later energy estimates can recover them directly. -/
def UniformlyEllipticOn (Ω : Set X) (a : X → Matrix n n ℝ) (lam Lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧
    ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ellipticQuadraticForm (a x) ξ ∧
        ellipticQuadraticForm (a x) ξ ≤ Lam * ‖ξ‖ ^ 2

namespace UniformlyEllipticOn

variable {Ω Ω' : Set X} {a : X → Matrix n n ℝ} {lam Lam lam' Lam' : ℝ}

/-- The lower ellipticity constant is positive. -/
lemma pos (h : UniformlyEllipticOn Ω a lam Lam) : 0 < lam :=
  h.1

/-- The lower ellipticity constant is no larger than the upper constant. -/
lemma le (h : UniformlyEllipticOn Ω a lam Lam) : lam ≤ Lam :=
  h.2.1

/-- The lower quadratic-form bound supplied by uniform ellipticity. -/
lemma lower_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    lam * ‖ξ‖ ^ 2 ≤ ellipticQuadraticForm (a x) ξ :=
  (h.2.2 hx ξ).1

/-- The upper quadratic-form bound supplied by uniform ellipticity. -/
lemma upper_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    ellipticQuadraticForm (a x) ξ ≤ Lam * ‖ξ‖ ^ 2 :=
  (h.2.2 hx ξ).2

/-- Uniform ellipticity implies pointwise nonnegativity of the coefficient quadratic form. -/
lemma quadraticForm_nonneg (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    0 ≤ ellipticQuadraticForm (a x) ξ := by
  exact (mul_nonneg h.pos.le (sq_nonneg ‖ξ‖)).trans (h.lower_bound hx ξ)

/-- Uniform ellipticity gives a positive quadratic form on every nonzero vector. -/
lemma quadraticForm_pos (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {ξ : EuclideanSpace ℝ n} (hξ : ξ ≠ 0) :
    0 < ellipticQuadraticForm (a x) ξ := by
  exact (mul_pos h.pos (sq_pos_of_ne_zero (by simpa using hξ))).trans_le
    (h.lower_bound hx ξ)

/-- Restricting the domain preserves uniform ellipticity with the same constants. -/
lemma mono_set (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : Ω' ⊆ Ω) :
    UniformlyEllipticOn Ω' a lam Lam :=
  ⟨h.pos, h.le, fun {_} hx ξ => h.2.2 (hΩ hx) ξ⟩

/-- Weakening the lower constant and increasing the upper constant preserves uniform
ellipticity. -/
lemma mono_constants (h : UniformlyEllipticOn Ω a lam Lam) (hlam' : 0 < lam')
    (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam') :
    UniformlyEllipticOn Ω a lam' Lam' := by
  refine ⟨hlam', hlam'_le.trans (h.le.trans hLam_le), fun {x} hx ξ => ?_⟩
  have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
  exact ⟨(mul_le_mul_of_nonneg_right hlam'_le hnorm).trans (h.lower_bound hx ξ),
    (h.upper_bound hx ξ).trans (mul_le_mul_of_nonneg_right hLam_le hnorm)⟩

/-- A constructor when the side conditions and pointwise quadratic-form bounds are already
available separately. -/
lemma of_bounds (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hbounds : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ ellipticQuadraticForm (a x) ξ ∧
        ellipticQuadraticForm (a x) ξ ≤ Lam * ‖ξ‖ ^ 2) :
    UniformlyEllipticOn Ω a lam Lam :=
  ⟨hlam, hlamLam, hbounds⟩

end UniformlyEllipticOn

/-- The constant identity coefficient field is uniformly elliptic with any constants
`λ ≤ 1 ≤ Λ` and `0 < λ`. This is the coefficient field of the Laplacian model problem. -/
lemma uniformlyEllipticOn_const_one [DecidableEq n] (Ω : Set X) {lam Lam : ℝ} (hlam : 0 < lam)
    (hlam_one : lam ≤ 1) (hone_Lam : 1 ≤ Lam) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds hlam (hlam_one.trans hone_Lam) fun {x} hx ξ => ?_
  have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
  simp only [ellipticQuadraticForm_one]
  exact ⟨by simpa using mul_le_mul_of_nonneg_right hlam_one hnorm,
    by simpa using mul_le_mul_of_nonneg_right hone_Lam hnorm⟩

/-- In particular, the identity coefficient field is uniformly elliptic with constants
`λ = Λ = 1`. -/
lemma uniformlyEllipticOn_const_one_one [DecidableEq n] (Ω : Set X) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) 1 1 :=
  uniformlyEllipticOn_const_one Ω zero_lt_one le_rfl le_rfl

end PDE

end TauCeti
