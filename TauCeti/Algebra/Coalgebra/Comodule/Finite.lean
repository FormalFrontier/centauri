/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Preadditive

/-!
# Finite comodules

This file packages finite right comodules over a coalgebra as a full subcategory of
`ComoduleCat`. An object of `FiniteComoduleCat R C` is a right `C`-comodule whose underlying
`R`-module is finitely generated; over a field this is the finite-dimensional comodule
category requested by the reductive-groups roadmap.

This is a small Layer 1 prerequisite for the finite-dimensional representation category of an
affine group scheme: later tensor products, duals, matrix coefficients, and Tannakian
reconstruction should be built on this full subcategory rather than on all comodules.

## Main definitions

* `TauCeti.ComoduleCat.isFinite`: the finite-generation object property on `ComoduleCat`.
* `TauCeti.FiniteComoduleCat`: finite right comodules as a full subcategory.
* `TauCeti.FiniteComoduleCat.of`: build a finite bundled comodule from unbundled data.
* `TauCeti.FiniteComoduleCat.ofHom`: lift an unbundled comodule morphism between finite
  comodules.

## References

This supplies the finite-dimensional-category part of
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target "Comodules over a coalgebra/Hopf
algebra". The construction follows Mathlib's `FGModuleCat` pattern: finite objects are a full
subcategory defined by the object property `Module.Finite`.
-/

open CategoryTheory

namespace TauCeti

universe u v w

variable (R : Type u) [CommRing R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace ComoduleCat

/-- Finite-generation as an object property on the category of right comodules. -/
def isFinite : ObjectProperty (ComoduleCat.{u, v, w} R C) :=
  fun M => Module.Finite R M

/-- The finite-comodule property is exactly finite generation of the underlying module. -/
theorem isFinite_iff (M : ComoduleCat.{u, v, w} R C) :
    isFinite (R := R) (C := C) M ↔ Module.Finite R M :=
  Iff.rfl

end ComoduleCat

/-- The category of finite right comodules over a fixed coalgebra.

For a field base, this is the category of finite-dimensional right comodules. -/
abbrev FiniteComoduleCat :=
  (ComoduleCat.isFinite.{u, v, w} R C).FullSubcategory

namespace FiniteComoduleCat

variable {R C}

/-- The underlying type of a finite comodule. -/
@[reducible]
def carrier (M : FiniteComoduleCat.{u, v, w} R C) : Type w :=
  M.obj

instance : CoeSort (FiniteComoduleCat.{u, v, w} R C) (Type w) :=
  ⟨carrier⟩

attribute [coe] carrier

instance (M : FiniteComoduleCat.{u, v, w} R C) : AddCommMonoid M :=
  inferInstanceAs (AddCommMonoid M.obj)

instance (M : FiniteComoduleCat.{u, v, w} R C) : Module R M :=
  inferInstanceAs (Module R M.obj)

instance (M : FiniteComoduleCat.{u, v, w} R C) : Comodule R C M :=
  inferInstanceAs (Comodule R C M.obj)

instance (M : FiniteComoduleCat.{u, v, w} R C) : AddCommGroup M :=
  Module.addCommMonoidToAddCommGroup R

/-- The underlying module of a finite comodule is finitely generated. -/
instance (M : FiniteComoduleCat.{u, v, w} R C) : Module.Finite R M :=
  M.property

/-- Lift an unbundled finite right comodule to `FiniteComoduleCat`. -/
abbrev of (M : Type w) [AddCommGroup M] [Module R M] [Comodule R C M]
    [Module.Finite R M] : FiniteComoduleCat.{u, v, w} R C :=
  ⟨ComoduleCat.of R C M, inferInstanceAs (Module.Finite R M)⟩

/-- The object of `ComoduleCat` underlying `FiniteComoduleCat.of` is `ComoduleCat.of`. -/
@[simp]
theorem of_obj (M : Type w) [AddCommGroup M] [Module R M] [Comodule R C M]
    [Module.Finite R M] :
    (of (R := R) (C := C) M).obj = ComoduleCat.of R C M :=
  rfl

/-- The coaction on `FiniteComoduleCat.of` is the original unbundled coaction. -/
@[simp]
theorem of_coact {M : Type w} [AddCommGroup M] [Module R M] [Comodule R C M]
    [Module.Finite R M] :
    Comodule.coact (R := R) (C := C) (M := of (R := R) (C := C) M) =
      Comodule.coact (R := R) (C := C) (M := M) :=
  rfl

/-- Typecheck an unbundled comodule morphism between finite comodules as a categorical
morphism in `FiniteComoduleCat`. -/
abbrev ofHom {M N : Type w} [AddCommGroup M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) :
    of (R := R) (C := C) M ⟶ of (R := R) (C := C) N :=
  ObjectProperty.homMk (ComoduleCat.ofHom (R := R) (C := C) f)

/-- Turning an unbundled comodule morphism into a finite-comodule morphism and projecting to
the ambient comodule category recovers the original bundled morphism. -/
@[simp]
theorem ofHom_hom {M N : Type w} [AddCommGroup M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) :
    (ofHom (R := R) (C := C) f).hom = ComoduleCat.ofHom (R := R) (C := C) f :=
  rfl

/-- The finite-comodule morphism induced by an unbundled morphism applies as that morphism. -/
@[simp]
theorem ofHom_apply {M N : Type w} [AddCommGroup M] [Module R M] [Comodule R C M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [Comodule R C N]
    [Module.Finite R N] (f : Comodule.Hom R C M N) (m : M) :
    ofHom (R := R) (C := C) f m = f m :=
  rfl

/-- The inclusion of finite comodules into all comodules sends objects to their ambient
bundled comodules. -/
@[simp]
theorem ι_obj (M : FiniteComoduleCat.{u, v, w} R C) :
    (ComoduleCat.isFinite.{u, v, w} R C).ι.obj M = M.obj :=
  rfl

/-- The inclusion of finite comodules into all comodules sends morphisms to their ambient
comodule morphisms. -/
@[simp]
theorem ι_map {M N : FiniteComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    (ComoduleCat.isFinite.{u, v, w} R C).ι.map f = f.hom :=
  rfl

/-- The standard forgetful functor from finite comodules to all comodules is the full
subcategory inclusion. -/
@[simp]
theorem forget₂_obj (M : FiniteComoduleCat.{u, v, w} R C) :
    (forget₂ (FiniteComoduleCat.{u, v, w} R C) (ComoduleCat.{u, v, w} R C)).obj M =
      M.obj :=
  rfl

/-- The standard forgetful functor from finite comodules to all comodules sends morphisms to
their ambient comodule morphisms. -/
@[simp]
theorem forget₂_map {M N : FiniteComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    (forget₂ (FiniteComoduleCat.{u, v, w} R C) (ComoduleCat.{u, v, w} R C)).map f =
      f.hom :=
  rfl

end FiniteComoduleCat

end TauCeti
