/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The functor of points of a Hopf algebra

For a Hopf algebra `H` over a commutative ring `R`, and a commutative `R`-algebra `A`, the
`A`-points of `H` are the `R`-algebra homomorphisms `H →ₐ[R] A`, equipped with the convolution
group structure. This file packages that construction as a functor

`CommAlgCat R ⥤ GrpCat`.

The group structure and its functoriality in the value algebra are proved in
`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints`; here we add only the categorical wrapper
needed to use those groups as the functor-of-points view in the reductive-groups roadmap.

## Main definitions

* `HopfAlgebra.pointsFunctor`: for a Hopf algebra `H`, the functor sending a
  commutative `R`-algebra `A` to the convolution group on `H →ₐ[R] A`.

## References

This advances the Tau Ceti reductive-groups roadmap, Layer 0, "R-points as a group":
the points of a commutative Hopf algebra are functorial in commutative value algebras and form
a group by convolution.
-/

open CategoryTheory WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable (R : Type u) [CommRing R] (H : Type v) [Semiring H] [_root_.HopfAlgebra R H]

/-- The functor of points of a Hopf algebra `H`.

It sends a commutative `R`-algebra `A` to the convolution group on algebra homomorphisms
`H →ₐ[R] A`, and sends an algebra map `A ⟶ B` to post-composition with that map. -/
noncomputable def pointsFunctor : CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (WithConv (H →ₐ[R] A))
  map {A B} φ := GrpCat.ofHom (AlgHom.mapValue (H := H) φ.hom)
  map_id A := by
    apply GrpCat.hom_ext
    simp
  map_comp {A B C} φ ψ := by
    apply GrpCat.hom_ext
    simp [AlgHom.mapValue_comp]

namespace PointsFunctor

variable {R H}

/-- The value of `pointsFunctor R H` at a commutative `R`-algebra `A` is the convolution
group on `R`-algebra homomorphisms `H →ₐ[R] A`. -/
@[simp]
lemma obj_carrier (A : CommAlgCat.{w} R) :
    ((pointsFunctor R H).obj A : Type (max v w)) = WithConv (H →ₐ[R] A) :=
  rfl

/-- On an algebra map `φ : A ⟶ B`, the functor of points acts by post-composition. -/
@[simp]
lemma map_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : WithConv (H →ₐ[R] A)) (h : H) :
    (((pointsFunctor R H).map φ f : WithConv (H →ₐ[R] B)).ofConv h) =
      φ.hom (f.ofConv h) := by
  rfl

end PointsFunctor

end HopfAlgebra

end TauCeti
