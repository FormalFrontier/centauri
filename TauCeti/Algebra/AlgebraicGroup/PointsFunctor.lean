/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The functor of points of a Hopf algebra

This file packages the convolution group of algebra homomorphisms out of a Hopf algebra as a
functor from commutative algebras to groups. For a Hopf algebra `H` over `R`, an object
`A : CommAlgCat R` is sent to the convolution group on `H →ₐ[R] A`; a morphism
`φ : A ⟶ B` acts by post-composition with `φ`.

This is the categorical form of the ReductiveGroups roadmap Layer 0 target "R-points as a
group": for the affine group scheme represented by a commutative Hopf algebra `H`, its
functor of points has values `A ↦ (H →ₐ[R] A)` and group law given by convolution.

## Main definitions

* `HopfAlgebra.points`: the bundled group of `A`-points.
* `HopfAlgebra.mapPoints`: the group homomorphism induced by post-composition in the value
  algebra.
* `HopfAlgebra.pointsFunctor`: the functor `CommAlgCat R ⥤ GrpCat`.

## References

This packages the "R-points as a group via convolution" milestone of the Tau Ceti
ReductiveGroups roadmap, Layer 0. It builds on Mathlib's convolution monoid for algebra
homomorphisms and the convolution-group inverse already developed in
`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints`.
-/

open CategoryTheory _root_.HopfAlgebra TensorProduct WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} [CommRing R] {H : Type v} [Ring H] [_root_.HopfAlgebra R H]

/-- The group of `A`-points of the affine group object represented by a Hopf algebra `H`.

The underlying type is `WithConv (H →ₐ[R] A)`: algebra homomorphisms from `H` to `A`, with
the convolution group structure supplied by the antipode of `H`. -/
noncomputable abbrev points (A : CommAlgCat.{w} R) : GrpCat.{max v w} :=
  GrpCat.of (WithConv (H →ₐ[R] A))

/-- The group homomorphism on points induced by a morphism of value algebras.

It sends an `A`-point `f : H →ₐ[R] A` to the `B`-point `φ ∘ f`. -/
noncomputable def mapPoints {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    points (H := H) A ⟶ points (H := H) B :=
  GrpCat.ofHom (AlgHom.mapValue (H := H) φ.hom)

/-- On points, `mapPoints` is post-composition with the algebra homomorphism `φ`. -/
@[simp]
lemma mapPoints_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : points (H := H) A) :
    mapPoints (H := H) φ f = toConv (φ.hom.comp f.ofConv) :=
  rfl

/-- The identity element of the group of `A`-points is the counit of the Hopf algebra,
followed by the structure map `R → A`. -/
@[simp]
lemma points_one_apply {A : CommAlgCat.{w} R} (h : H) :
    ((1 : points (H := H) A).ofConv) h = algebraMap R A (Coalgebra.counit h) :=
  AlgHom.convOne_apply h

/-- Multiplication in the group of `A`-points is convolution along the comultiplication of
the Hopf algebra. -/
lemma points_mul_apply {A : CommAlgCat.{w} R} (f g : points (H := H) A) (h : H) :
    ((f * g).ofConv) h =
      Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ ↦ .all ..) (Coalgebra.comul h) :=
  AlgHom.convMul_apply f g h

/-- The map on points sends the identity point to the identity point. -/
@[simp]
lemma mapPoints_one {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    mapPoints (H := H) φ (1 : points (H := H) A) = 1 := by
  exact (mapPoints (H := H) φ).hom.map_one

/-- The map on points preserves multiplication of points. -/
lemma mapPoints_mul {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (f g : points (H := H) A) :
    mapPoints (H := H) φ (f * g) = mapPoints (H := H) φ f * mapPoints (H := H) φ g := by
  exact (mapPoints (H := H) φ).hom.map_mul f g

/-- The map on points preserves inverses of points. -/
lemma mapPoints_inv {A B : CommAlgCat.{w} R} (φ : A ⟶ B) (f : points (H := H) A) :
    mapPoints (H := H) φ f⁻¹ = (mapPoints (H := H) φ f)⁻¹ := by
  exact (mapPoints (H := H) φ).hom.map_inv f

/-- `mapPoints` preserves identity morphisms of value algebras. -/
@[simp]
lemma mapPoints_id (A : CommAlgCat.{w} R) :
    mapPoints (H := H) (𝟙 A) = 𝟙 (points (H := H) A) := by
  change GrpCat.ofHom (AlgHom.mapValue (H := H) (AlgHom.id R A)) =
    GrpCat.ofHom (MonoidHom.id (WithConv (H →ₐ[R] A)))
  rw [AlgHom.mapValue_id]

/-- `mapPoints` preserves composition of morphisms of value algebras. -/
lemma mapPoints_comp {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapPoints (H := H) (φ ≫ ψ) = mapPoints (H := H) φ ≫ mapPoints (H := H) ψ := by
  change GrpCat.ofHom (AlgHom.mapValue (H := H) (ψ.hom.comp φ.hom)) =
    GrpCat.ofHom ((AlgHom.mapValue (H := H) ψ.hom).comp (AlgHom.mapValue (H := H) φ.hom))
  rw [AlgHom.mapValue_comp]

/-- The functor of points of the affine group object represented by a Hopf algebra.

It maps a commutative `R`-algebra `A` to the convolution group on algebra homomorphisms
`H →ₐ[R] A`, and maps `φ : A ⟶ B` to post-composition with `φ`. -/
noncomputable def pointsFunctor : CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := points (H := H) A
  map φ := mapPoints (H := H) φ
  map_id A := mapPoints_id (H := H) A
  map_comp φ ψ := mapPoints_comp (H := H) φ ψ

/-- The object part of `pointsFunctor` is the convolution group of algebra homomorphisms. -/
@[simp]
lemma pointsFunctor_obj (A : CommAlgCat.{w} R) :
    (pointsFunctor (H := H)).obj A = GrpCat.of (WithConv (H →ₐ[R] A)) :=
  rfl

/-- The morphism part of `pointsFunctor` is post-composition in the value algebra. -/
@[simp]
lemma pointsFunctor_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (pointsFunctor (H := H)).map φ = mapPoints (H := H) φ :=
  rfl

/-- On points, `pointsFunctor.map φ` sends `f` to `φ ∘ f`. -/
@[simp]
lemma pointsFunctor_map_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : (pointsFunctor (H := H)).obj A) :
    (pointsFunctor (H := H)).map φ f = toConv (φ.hom.comp f.ofConv) :=
  rfl

/-- The pointwise value of the image of an `A`-point under `pointsFunctor.map φ`. -/
@[simp]
lemma pointsFunctor_map_apply_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : (pointsFunctor (H := H)).obj A) (h : H) :
    (((pointsFunctor (H := H)).map φ f : WithConv (H →ₐ[R] B)).ofConv) h =
      φ.hom (f.ofConv h) :=
  rfl

/-- The functorial map on points sends the identity point to the identity point. -/
@[simp]
lemma pointsFunctor_map_one {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (pointsFunctor (H := H)).map φ (1 : (pointsFunctor (H := H)).obj A) = 1 :=
  mapPoints_one (H := H) φ

/-- The functorial map on points preserves multiplication of points. -/
lemma pointsFunctor_map_mul {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f g : (pointsFunctor (H := H)).obj A) :
    (pointsFunctor (H := H)).map φ (f * g) =
      (pointsFunctor (H := H)).map φ f * (pointsFunctor (H := H)).map φ g :=
  mapPoints_mul (H := H) φ f g

/-- The functorial map on points preserves inverses of points. -/
lemma pointsFunctor_map_inv {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : (pointsFunctor (H := H)).obj A) :
    (pointsFunctor (H := H)).map φ f⁻¹ = ((pointsFunctor (H := H)).map φ f)⁻¹ :=
  mapPoints_inv (H := H) φ f

/-- The inverse in the group of `A`-points is given by post-composition with the antipode. -/
@[simp]
lemma points_inv_apply {A : CommAlgCat.{w} R} (f : points (H := H) A) (h : H) :
    f⁻¹ h = f.ofConv (antipode R h) :=
  AlgHom.convInv_apply f h

end HopfAlgebra

end TauCeti
