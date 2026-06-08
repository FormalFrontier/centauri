/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# The functor of points of a Hopf algebra

This file packages the convolution group from
`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints` as the functor of points of a Hopf algebra.
For a Hopf algebra `H` over a commutative ring `R`, its `A`-points are the `R`-algebra maps
`H →ₐ[R] A`, with multiplication given by convolution. Post-composition in the value algebra
then gives a functor

```
CommAlgCat R ⥤ GrpCat
```

This is the categorical form of the "R-points as a group" item in Layer 0 of the Tau Ceti
reductive-groups roadmap. The convolution monoid and inverse are provided by the preceding
Tau Ceti file, which in turn builds on Mathlib's convolution API.
-/

open CategoryTheory WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w x y

variable (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] [_root_.Bialgebra R H]

/-- The `A`-points represented by a bialgebra `H` over `R`.

This is the type of `R`-algebra homomorphisms `H →ₐ[R] A`, equipped with the convolution
monoid structure. When `H` is a Hopf algebra this monoid is the convolution group used by
`pointsFunctor`. The source algebra `H` is allowed to be noncommutative here; for the usual
affine group-scheme interpretation one later adds commutativity of `H` so that `Spec H` exists
as an affine scheme over `R`. -/
abbrev AlgPoints (R : Type u) (H : Type v) [CommSemiring R] [Semiring H]
    [_root_.Bialgebra R H] (A : Type w) [CommSemiring A] [Algebra R A] : Type (max v w) :=
  WithConv (H →ₐ[R] A)

namespace AlgPoints

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [_root_.Bialgebra R H]
variable {A : Type w} {B : Type x} {C : Type y} [CommSemiring A] [Algebra R A]
  [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C]

/-- The underlying algebra homomorphism of a point of a Hopf algebra. -/
abbrev hom (f : AlgPoints R H A) : H →ₐ[R] A :=
  f.ofConv

/-- Post-composition in the value algebra gives the functorial map on points. -/
noncomputable abbrev map (φ : A →ₐ[R] B) : AlgPoints R H A →* AlgPoints R H B :=
  AlgHom.mapValue (H := H) φ

/-- The map on points induced by `φ : A →ₐ[R] B` is post-composition by `φ`. -/
@[simp]
lemma map_apply (φ : A →ₐ[R] B) (f : AlgPoints R H A) :
    map (H := H) φ f = toConv (φ.comp f.hom) :=
  rfl

/-- On underlying functions, `map φ` sends `f` to `φ ∘ f`. -/
@[simp]
lemma map_apply_apply (φ : A →ₐ[R] B) (f : AlgPoints R H A) (h : H) :
    map (H := H) φ f h = φ (f.hom h) :=
  rfl

/-- Mapping points along the identity algebra homomorphism is the identity. -/
@[simp]
lemma map_id : map (H := H) (AlgHom.id R A) = MonoidHom.id (AlgPoints R H A) :=
  AlgHom.mapValue_id (H := H)

/-- Mapping points is compatible with composition in the value algebra. -/
lemma map_comp (ψ : B →ₐ[R] C) (φ : A →ₐ[R] B) :
    map (H := H) (ψ.comp φ) = (map ψ).comp (map φ) :=
  AlgHom.mapValue_comp (H := H) ψ φ

end AlgPoints

/-- The functor of points of a Hopf algebra, valued in groups via convolution.

It sends a commutative `R`-algebra `A` to the convolution group of algebra maps
`H →ₐ[R] A`, and sends `φ : A ⟶ B` to post-composition with `φ`. -/
noncomputable def pointsFunctor (R : Type u) (H : Type v) [CommRing R] [Semiring H]
    [_root_.HopfAlgebra R H] : CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (AlgPoints R H A)
  map {A B} φ := GrpCat.ofHom (AlgPoints.map (H := H) φ.hom)
  map_id A := by
    rw [CommAlgCat.hom_id, AlgPoints.map_id, GrpCat.ofHom_id]
  map_comp φ ψ := by
    rw [CommAlgCat.hom_comp, AlgPoints.map_comp, GrpCat.ofHom_comp]

namespace pointsFunctor

variable {R : Type u} {H : Type v} [CommRing R] [Semiring H] [_root_.HopfAlgebra R H]
variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Evaluating the points functor at `A` gives the convolution group of `A`-points. -/
@[simp]
lemma obj_of :
    (pointsFunctor R H).obj (CommAlgCat.of R A) = GrpCat.of (AlgPoints R H A) :=
  rfl

/-- The morphism induced by an algebra map on the points functor is `AlgPoints.map`. -/
@[simp]
lemma map_ofHom_hom (φ : A →ₐ[R] B) :
    ((pointsFunctor R H).map (CommAlgCat.ofHom φ)).hom = AlgPoints.map (H := H) φ :=
  rfl

/-- Pointwise, the points functor acts by post-composition. -/
@[simp]
lemma map_ofHom_apply (φ : A →ₐ[R] B) (f : AlgPoints R H A) :
    (pointsFunctor R H).map (CommAlgCat.ofHom φ) f = toConv (φ.comp f.hom) :=
  rfl

/-- Pointwise on `H`, the points functor acts by applying the value-algebra morphism. -/
@[simp]
lemma map_ofHom_apply_apply (φ : A →ₐ[R] B) (f : AlgPoints R H A) (h : H) :
    ((pointsFunctor R H).map (CommAlgCat.ofHom φ) f : AlgPoints R H B).hom h =
      φ (f.hom h) :=
  rfl

end pointsFunctor

end HopfAlgebra

end TauCeti
