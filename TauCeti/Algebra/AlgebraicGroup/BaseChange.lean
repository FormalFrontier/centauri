/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Base change of Hopf-algebra points

This file records that the usual algebraic base-change adjunction is compatible with the
convolution group structure on the functor of points of a Hopf algebra. For a Hopf `k`-algebra
`A`, a `k`-algebra `K`, and a commutative `K`-algebra `R`, `K`-points of the base-changed Hopf
algebra `K ⊗[k] A` are the same as `k`-algebra maps `A →ₐ[k] R`, and this identification is a
group isomorphism for convolution.

This is the algebraic-group-facing form of the ReductiveGroups roadmap item "Base change.
`K ⊗[k] A` as a Hopf algebra over `K`"; it builds on Mathlib's tensor-product Hopf algebra
instance and `AlgHom.liftEquiv`.

## Main definitions

* `TauCeti.AlgHom.baseChangePointsMulEquiv`: the convolution group isomorphism between
  `A →ₐ[k] R` and `K ⊗[k] A →ₐ[K] R`.

## References

The tensor-product Hopf algebra structure and algebra base-change adjunction used here are
from Mathlib, respectively `Mathlib.RingTheory.HopfAlgebra.TensorProduct` and
`AlgHom.liftEquiv`.
-/

open Coalgebra HopfAlgebra TensorProduct WithConv

namespace TauCeti

namespace AlgHom

variable {k K A R : Type*} [CommSemiring k] [CommSemiring K] [CommSemiring A]
  [CommSemiring R] [Algebra k K] [_root_.HopfAlgebra k A] [Algebra K R] [Algebra k R]
  [IsScalarTower k K R]

/-- Base change of points along `k → K`: a `k`-point of `A` with values in a `K`-algebra `R`
is equivalently a `K`-point of the base-changed Hopf algebra `K ⊗[k] A`. -/
noncomputable abbrev baseChangePointsEquiv :
    (A →ₐ[k] R) ≃ (K ⊗[k] A →ₐ[K] R) :=
  AlgHom.liftEquiv k K A R

/-- The base-change equivalence sends a point `f : A →ₐ[k] R` to the `K`-algebra map
`s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsEquiv_apply_tmul (f : A →ₐ[k] R) (s : K) (a : A) :
    baseChangePointsEquiv (K := K) f (s ⊗ₜ[k] a) = s • f a :=
  rfl

/-- Restricting a base-changed point back along `A → K ⊗[k] A` evaluates it on `1 ⊗ a`. -/
@[simp]
lemma baseChangePointsEquiv_symm_apply (f : K ⊗[k] A →ₐ[K] R) (a : A) :
    (baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)).symm f a =
      f (1 ⊗ₜ[k] a) :=
  rfl

private lemma baseChangePointsEquiv_map_one :
    baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)
      (WithConv.ofConv (1 : WithConv (A →ₐ[k] R))) =
    WithConv.ofConv (1 : WithConv (K ⊗[k] A →ₐ[K] R)) := by
  ext a
  simp [AlgHom.convOne_apply, IsScalarTower.algebraMap_apply k K R, Algebra.smul_def]

private lemma baseChangePointsEquiv_map_mul
    (f g : WithConv (A →ₐ[k] R)) :
    baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)
      (WithConv.ofConv (f * g)) =
    WithConv.ofConv
      ((WithConv.toConv (baseChangePointsEquiv (K := K) f.ofConv) *
        WithConv.toConv (baseChangePointsEquiv (K := K) g.ofConv)) :
          WithConv (K ⊗[k] A →ₐ[K] R)) := by
  ext a
  suffices
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => .all _ _))
        (Coalgebra.comul (R := k) a) =
      (Algebra.TensorProduct.lift (baseChangePointsEquiv (K := K) f.ofConv)
        (baseChangePointsEquiv (K := K) g.ofConv) (fun _ _ => .all _ _))
        ((AlgebraTensorModule.tensorTensorTensorComm k K k K K K A A)
          (1 ⊗ₜ[K] 1 ⊗ₜ[k] Coalgebra.comul (R := k) a)) by
    simpa only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul,
      AlgHom.convMul_apply, TensorProduct.comul_tmul, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def] using this
  induction Coalgebra.comul (R := k) a with
  | zero => simp only [tmul_zero, map_zero]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | tmul a₁ a₂ =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgebraTensorModule.tensorTensorTensorComm_tmul,
        AlgHom.liftEquiv_tmul, Algebra.smul_def, map_one, one_mul]

/-- Base change of Hopf-algebra points is a group isomorphism for the convolution product.

The forward direction sends `f : A →ₐ[k] R` to `s ⊗ a ↦ s • f a`; the inverse restricts a
`K`-algebra map `K ⊗[k] A →ₐ[K] R` along `a ↦ 1 ⊗ a`. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (A →ₐ[k] R) ≃* WithConv (K ⊗[k] A →ₐ[K] R) where
  toFun f := WithConv.toConv (baseChangePointsEquiv (K := K) f.ofConv)
  invFun f := WithConv.toConv
    ((baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)).symm f.ofConv)
  left_inv f := by
    apply WithConv.ext
    ext a
    change ((baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)).symm
        (baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R) f.ofConv)) a =
      f.ofConv a
    have h :=
      (baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)).left_inv f.ofConv
    exact congrFun (congrArg DFunLike.coe h) a
  right_inv f := by
    apply WithConv.ext
    ext a
    change (baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)
        ((baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)).symm f.ofConv))
        (1 ⊗ₜ[k] a) =
      f.ofConv (1 ⊗ₜ[k] a)
    have h :=
      (baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)).right_inv f.ofConv
    exact congrFun (congrArg DFunLike.coe h) (1 ⊗ₜ[k] a)
  map_mul' f g := by
    apply WithConv.ext
    ext a
    simp [baseChangePointsEquiv_map_mul]

/-- The base-change convolution-group isomorphism sends `f` to `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_ofConv (f : WithConv (A →ₐ[k] R)) :
    (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f).ofConv =
      baseChangePointsEquiv (K := K) f.ofConv :=
  rfl

/-- The inverse base-change convolution-group isomorphism is restriction along
`A → K ⊗[k] A`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_ofConv (f : WithConv (K ⊗[k] A →ₐ[K] R)) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f).ofConv =
      (baseChangePointsEquiv (k := k) (K := K) (A := A) (R := R)).symm f.ofConv :=
  rfl

/-- The base-change convolution-group isomorphism sends `f` to `s ⊗ a ↦ s • f a`. -/
@[simp]
lemma baseChangePointsMulEquiv_apply_tmul (f : WithConv (A →ₐ[k] R)) (s : K) (a : A) :
    baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R) f (s ⊗ₜ[k] a) =
      s • f.ofConv a :=
  rfl

/-- The inverse of the base-change convolution-group isomorphism restricts along
`a ↦ 1 ⊗ a`. -/
@[simp]
lemma baseChangePointsMulEquiv_symm_apply (f : WithConv (K ⊗[k] A →ₐ[K] R)) (a : A) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)).symm f).ofConv a =
      f.ofConv (1 ⊗ₜ[k] a) :=
  rfl

end AlgHom

end TauCeti
