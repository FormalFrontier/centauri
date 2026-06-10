/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Analysis.PDE.UniformEllipticity

/-!
# Pointwise energy forms for divergence-form PDEs

This file relates the pointwise bilinear expression

`ηᵀ A ξ = η ⬝ᵥ A *ᵥ ξ`

to Mathlib's continuous sesquilinear form
`ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A)`.
It is the local algebraic ingredient for the PDE roadmap's divergence-form energy
`∫ x, ∂u(x)ᵀ a(x) ∂v(x)`: uniform ellipticity gives the lower bound needed for coercivity,
and the bilinear upper bound gives continuity.

The file deliberately stays pointwise. Domain Sobolev spaces and integrals are later Lane A/D
material; once they exist, these lemmas are the coefficient-matrix facts used under the integral.

## Main declarations

* `TauCeti.PDE.toSesqForm_toEuclideanCLM_eq_matrixBilinearForm`: Mathlib's matrix
  sesquilinear form is the existing Tau Ceti matrix bilinear form, so callers can reuse
  `matrixBilinearForm_self`, `matrixBilinearForm_opNorm_le_of_upper_bound`,
  `UniformlyEllipticOn.isCoercive_matrixBilinearForm`, and
  `UniformlyEllipticOn.opNorm_matrixBilinearForm_le` after this rewrite.
-/

namespace TauCeti

namespace PDE

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's matrix sesquilinear form is the same bundled bilinear form as
`matrixBilinearForm`. -/
lemma toSesqForm_toEuclideanCLM_eq_matrixBilinearForm (A : Matrix n n ℝ) :
    ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A) =
      matrixBilinearForm A := by
  ext η ξ
  calc
    (ContinuousLinearMap.toSesqForm (Matrix.toEuclideanCLM (𝕜 := ℝ) A) η) ξ =
        η ⬝ᵥ (A *ᵥ ξ) := Matrix.inner_toEuclideanCLM A η ξ
    _ = matrixBilinearForm A η ξ := (matrixBilinearForm_apply A η ξ).symm

end

end PDE

end TauCeti
