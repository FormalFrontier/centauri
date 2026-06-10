/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Coalgebra.Comodule.Finite
import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Tensor products of group-like and trivial comodules

This file records the first tensor-product cases for right comodules over a bialgebra. If
two modules carry the group-like coactions attached to `g` and `h`, their tensor product
carries the group-like coaction attached to `g * h`. In particular, tensor products of
trivial comodules are trivial.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target
"Comodules over a coalgebra/Hopf algebra", where the finite-dimensional comodule category is
to become a rigid monoidal category. The fully general tensor product of comodules requires
the usual bialgebraic coaction formula; this file supplies the tensor-unit and group-like
special cases used as checks for that later construction.

## Main definitions

* `TauCeti.Comodule.groupLikeTensor`: the tensor product of two group-like comodules.
* `TauCeti.Comodule.trivialTensor`: the tensor product of two trivial comodules.
* `TauCeti.Comodule.Hom.tensorOfGroupLike`: tensor a pair of linear maps between matching
  group-like comodules.
* `TauCeti.Comodule.Hom.tensorOfTrivial`: tensor a pair of linear maps between trivial
  comodules.
* `TauCeti.FGComoduleCat.trivial` and `TauCeti.FGComoduleCat.tensorTrivial`: finitely
  generated bundled versions of the trivial tensor-unit examples.

## References

The group-like calculation uses Mathlib's `GroupLike` monoid structure from
`Mathlib.RingTheory.Bialgebra.GroupLike`, due to Yaël Dillies and Michał Mrugała.
-/

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x y z

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [Semiring C] [Bialgebra R C]
variable {M : Type w} {N : Type x} {P : Type y} {Q : Type z}
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]
variable [AddCommMonoid Q] [Module R Q]

/-- The tensor product of the group-like comodules attached to `g` and `h`.

The coaction on `M ⊗[R] N` is the group-like coaction attached to the product `g * h`.
This is the expected tensor-product formula in the special case where both coactions are
pure tensors. It is not registered globally, since the same tensor product module may carry
other coactions. -/
@[implicit_reducible]
def groupLikeTensor (g h : GroupLike R C) : Comodule R C (M ⊗[R] N) :=
  groupLike (R := R) (C := C) (M := M ⊗[R] N) (g * h)

section GroupLikeTensor

variable (g h : GroupLike R C)

/-- The coaction on the tensor product of group-like comodules is `t ↦ t ⊗ (g * h)`. -/
@[simp]
theorem groupLikeTensor_coact :
    letI : Comodule R C (M ⊗[R] N) :=
      groupLikeTensor (R := R) (C := C) (M := M) (N := N) g h
    coact (R := R) (C := C) (M := M ⊗[R] N) =
      (TensorProduct.mk R (M ⊗[R] N) C).flip ((g * h : GroupLike R C) : C) :=
  rfl

/-- On a pure tensor, the tensor product of group-like coactions is attached to `g * h`. -/
@[simp]
theorem groupLikeTensor_coact_tmul (m : M) (n : N) :
    letI : Comodule R C (M ⊗[R] N) :=
      groupLikeTensor (R := R) (C := C) (M := M) (N := N) g h
    coact (R := R) (C := C) (M := M ⊗[R] N) (m ⊗ₜ[R] n) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] ((g * h : GroupLike R C) : C) :=
  rfl

/-- A pair of linear maps tensors to a comodule morphism between tensor products of
matching group-like comodules. -/
def Hom.tensorOfGroupLike (f : M →ₗ[R] P) (k : N →ₗ[R] Q) :
    letI : Comodule R C (M ⊗[R] N) :=
      groupLikeTensor (R := R) (C := C) (M := M) (N := N) g h
    letI : Comodule R C (P ⊗[R] Q) :=
      groupLikeTensor (R := R) (C := C) (M := P) (N := Q) g h
    Hom R C (M ⊗[R] N) (P ⊗[R] Q) := by
  letI : Comodule R C (M ⊗[R] N) :=
    groupLikeTensor (R := R) (C := C) (M := M) (N := N) g h
  letI : Comodule R C (P ⊗[R] Q) :=
    groupLikeTensor (R := R) (C := C) (M := P) (N := Q) g h
  exact Hom.ofGroupLike (R := R) (C := C) (M := M ⊗[R] N) (N := P ⊗[R] Q)
    (g * h) (TensorProduct.map f k)

namespace Hom

/-- The underlying linear map of `Hom.tensorOfGroupLike` is the tensor product of the two
linear maps. -/
@[simp]
theorem tensorOfGroupLike_toLinearMap (f : M →ₗ[R] P) (k : N →ₗ[R] Q) :
    letI : Comodule R C (M ⊗[R] N) :=
      groupLikeTensor (R := R) (C := C) (M := M) (N := N) g h
    letI : Comodule R C (P ⊗[R] Q) :=
      groupLikeTensor (R := R) (C := C) (M := P) (N := Q) g h
    (tensorOfGroupLike (R := R) (C := C) (M := M) (N := N) (P := P) (Q := Q) g h
      f k).toLinearMap = TensorProduct.map f k :=
  rfl

/-- Tensoring two linear maps between group-like comodules acts on pure tensors as expected. -/
@[simp]
theorem tensorOfGroupLike_tmul (f : M →ₗ[R] P) (k : N →ₗ[R] Q) (m : M) (n : N) :
    letI : Comodule R C (M ⊗[R] N) :=
      groupLikeTensor (R := R) (C := C) (M := M) (N := N) g h
    letI : Comodule R C (P ⊗[R] Q) :=
      groupLikeTensor (R := R) (C := C) (M := P) (N := Q) g h
    tensorOfGroupLike (R := R) (C := C) (M := M) (N := N) (P := P) (Q := Q) g h
      f k (m ⊗ₜ[R] n) = f m ⊗ₜ[R] k n :=
  rfl

/-- Tensoring identity maps between group-like comodules gives the identity morphism. -/
@[simp]
theorem tensorOfGroupLike_id :
    letI : Comodule R C (M ⊗[R] N) :=
      groupLikeTensor (R := R) (C := C) (M := M) (N := N) g h
    tensorOfGroupLike (R := R) (C := C) (M := M) (N := N) (P := M) (Q := N) g h
      LinearMap.id LinearMap.id =
        Comodule.Hom.id R C (M ⊗[R] N) := by
  letI : Comodule R C (M ⊗[R] N) :=
    groupLikeTensor (R := R) (C := C) (M := M) (N := N) g h
  apply Hom.ext
  intro t
  change TensorProduct.map (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N) t = t
  rw [TensorProduct.map_id]
  rfl

end Hom

end GroupLikeTensor

/-- The tensor product of two trivial comodules.

This is the group-like tensor construction specialized to the unit group-like element. It is
kept as a named definition because later monoidal-category API should recognize the trivial
comodule as the tensor unit. -/
@[implicit_reducible]
def trivialTensor : Comodule R C (M ⊗[R] N) :=
  groupLikeTensor (R := R) (C := C) (M := M) (N := N)
    (1 : GroupLike R C) (1 : GroupLike R C)

section TrivialTensor

attribute [local instance] trivialTensor

/-- The tensor product of trivial comodules has coaction `t ↦ t ⊗ 1`. -/
@[simp]
theorem trivialTensor_coact :
    coact (R := R) (C := C) (M := M ⊗[R] N) =
      (TensorProduct.mk R (M ⊗[R] N) C).flip (1 : C) :=
  by
    change
      (letI : Comodule R C (M ⊗[R] N) :=
        groupLikeTensor (R := R) (C := C) (M := M) (N := N)
          (1 : GroupLike R C) (1 : GroupLike R C)
       coact (R := R) (C := C) (M := M ⊗[R] N)) =
        (TensorProduct.mk R (M ⊗[R] N) C).flip (1 : C)
    convert
      groupLikeTensor_coact (R := R) (C := C) (M := M) (N := N)
        (1 : GroupLike R C) (1 : GroupLike R C) using 1
    simp

/-- On pure tensors, the tensor product of trivial coactions is trivial. -/
@[simp]
theorem trivialTensor_coact_tmul (m : M) (n : N) :
    coact (R := R) (C := C) (M := M ⊗[R] N) (m ⊗ₜ[R] n) =
      (m ⊗ₜ[R] n) ⊗ₜ[R] (1 : C) :=
  by
    change
      (letI : Comodule R C (M ⊗[R] N) :=
        groupLikeTensor (R := R) (C := C) (M := M) (N := N)
          (1 : GroupLike R C) (1 : GroupLike R C)
       coact (R := R) (C := C) (M := M ⊗[R] N) (m ⊗ₜ[R] n)) =
        (m ⊗ₜ[R] n) ⊗ₜ[R] (1 : C)
    convert
      groupLikeTensor_coact_tmul (R := R) (C := C) (M := M) (N := N)
        (1 : GroupLike R C) (1 : GroupLike R C) m n using 1
    simp

/-- A pair of linear maps tensors to a comodule morphism between tensor products of trivial
comodules. -/
def Hom.tensorOfTrivial (f : M →ₗ[R] P) (k : N →ₗ[R] Q) : Hom R C (M ⊗[R] N) (P ⊗[R] Q) :=
  Hom.tensorOfGroupLike (R := R) (C := C) (M := M) (N := N) (P := P) (Q := Q)
    (1 : GroupLike R C) (1 : GroupLike R C) f k

namespace Hom

/-- The underlying linear map of `Hom.tensorOfTrivial` is the tensor product of the two
linear maps. -/
@[simp]
theorem tensorOfTrivial_toLinearMap (f : M →ₗ[R] P) (k : N →ₗ[R] Q) :
    (tensorOfTrivial (R := R) (C := C) f k).toLinearMap = TensorProduct.map f k :=
  rfl

/-- Tensoring two linear maps between trivial comodules acts on pure tensors as expected. -/
@[simp]
theorem tensorOfTrivial_tmul (f : M →ₗ[R] P) (k : N →ₗ[R] Q) (m : M) (n : N) :
    tensorOfTrivial (R := R) (C := C) f k (m ⊗ₜ[R] n) = f m ⊗ₜ[R] k n :=
  rfl

end Hom

end TrivialTensor

end Comodule

namespace FGComoduleCat

variable (R : Type u) (C : Type v) [CommSemiring R] [Semiring C] [Bialgebra R C]

/-- The finitely generated bundled trivial right comodule over a bialgebra.

Its underlying module is the rank-one module `R`, with coaction `r ↦ r ⊗ 1`. -/
abbrev trivial : FGComoduleCat.{u, v, u} R C :=
  letI : Comodule R C R := Comodule.trivial (R := R) (C := C) (M := R)
  of (R := R) (C := C) R

variable {R C}
variable {M : Type w} {N : Type x}
variable [AddCommMonoid M] [Module R M] [Module.Finite R M]
variable [AddCommMonoid N] [Module R N] [Module.Finite R N]

/-- The finitely generated bundled tensor product of two trivial comodules. -/
abbrev tensorTrivial : FGComoduleCat.{u, v, max w x} R C :=
  letI : Comodule R C (M ⊗[R] N) :=
    Comodule.trivialTensor (R := R) (C := C) (M := M) (N := N)
  of (R := R) (C := C) (M ⊗[R] N)

end FGComoduleCat

end TauCeti
