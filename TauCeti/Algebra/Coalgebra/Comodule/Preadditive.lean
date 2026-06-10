/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import TauCeti.Algebra.Coalgebra.ComoduleCat

/-!
# Preadditive structure on comodule categories

This file records the additive-group structure on morphisms of right comodules over a
coalgebra over a commutative ring, and uses it to make the bundled comodule category
preadditive.

The semiring-level files already show that comodule morphisms are closed under zero,
addition, scalar multiplication, and finite sums. Over a ring, every semimodule is an
additive group by `Module.addCommMonoidToAddCommGroup`; the same pointwise operations also
give negatives and subtraction of comodule morphisms. This is the categorical additive
infrastructure needed before the reductive-groups roadmap's finite-dimensional comodule
representation category can be developed.

## Main declarations

* `TauCeti.Comodule.Hom.instNeg`, `instSub`, `instAddCommGroup`: pointwise additive-group
  structure on comodule morphisms over a commutative ring.
* `TauCeti.ComoduleCat.preadditive`: `ComoduleCat R C` is preadditive over a commutative
  ring `R`.

## References

This supplies a prerequisite for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target "Comodules over a coalgebra/Hopf
algebra": the finite-dimensional comodule representation category should be an additive
category before tensor products, duals, and Tannakian structure are built on top.
-/

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommRing R]
variable [AddCommGroup C] [Module R C] [Coalgebra R C]
variable [AddCommGroup M] [Module R M] [Comodule R C M]
variable [AddCommGroup N] [Module R N] [Comodule R C N]

namespace Hom

/-- Negation of right-comodule morphisms, defined pointwise. -/
instance instNeg : Neg (Hom R C M N) where
  neg f :=
    { toLinearMap := -f.toLinearMap
      map_coact := by
        ext m
        rw [← neg_one_smul R f.toLinearMap, TensorProduct.map_smul_left]
        simp [map_coact_apply] }

/-- Subtraction of right-comodule morphisms, defined pointwise. -/
instance instSub : Sub (Hom R C M N) where
  sub f g :=
    { toLinearMap := f.toLinearMap - g.toLinearMap
      map_coact := by
        ext m
        rw [sub_eq_add_neg, TensorProduct.map_add_left]
        rw [← neg_one_smul R g.toLinearMap, TensorProduct.map_smul_left]
        simp [map_coact_apply] }

/-- Integer scalar multiplication of right-comodule morphisms, defined pointwise. -/
instance instZSMul : SMul ℤ (Hom R C M N) where
  smul z f :=
    { toLinearMap := z • f.toLinearMap
      map_coact := by
        ext m
        dsimp
        have hzmap : z • f.toLinearMap = (z : R) • f.toLinearMap := by
          ext n
          rw [Int.cast_smul_eq_zsmul]
        rw [hzmap, TensorProduct.map_smul_left]
        rw [LinearMap.smul_apply, map_coact_apply, ← Int.cast_smul_eq_zsmul R z (f m),
          map_smul] }

/-- Negation of comodule morphisms is negation of the underlying linear maps. -/
@[simp]
theorem neg_toLinearMap (f : Hom R C M N) : (-f).toLinearMap = -f.toLinearMap :=
  rfl

/-- Subtraction of comodule morphisms is subtraction of the underlying linear maps. -/
@[simp]
theorem sub_toLinearMap (f g : Hom R C M N) :
    (f - g).toLinearMap = f.toLinearMap - g.toLinearMap :=
  rfl

/-- Integer scalar multiplication of comodule morphisms is integer scalar multiplication of
the underlying linear maps. -/
@[simp]
theorem zsmul_toLinearMap (z : ℤ) (f : Hom R C M N) :
    (z • f).toLinearMap = z • f.toLinearMap :=
  rfl

/-- Negation of comodule morphisms is pointwise negation. -/
@[simp]
theorem neg_apply (f : Hom R C M N) (m : M) : (-f) m = -f m :=
  rfl

/-- Subtraction of comodule morphisms is pointwise subtraction. -/
@[simp]
theorem sub_apply (f g : Hom R C M N) (m : M) : (f - g) m = f m - g m :=
  rfl

/-- Integer scalar multiplication of comodule morphisms is pointwise. -/
@[simp]
theorem zsmul_apply (z : ℤ) (f : Hom R C M N) (m : M) :
    (z • f) m = z • f m :=
  rfl

/-- Comodule morphisms over a commutative ring form an additive commutative group under
pointwise operations. -/
instance instAddCommGroupRing : AddCommGroup (Hom R C M N) :=
  Function.Injective.addCommGroup (fun f : Hom R C M N => f.toLinearMap)
    (fun f g h => by
      ext m
      exact LinearMap.congr_fun h m)
    zero_toLinearMap add_toLinearMap neg_toLinearMap sub_toLinearMap
    (fun f n => nsmul_toLinearMap n f) (fun f z => zsmul_toLinearMap z f)

section Comp

variable {P : Type*} [AddCommGroup P] [Module R P] [Comodule R C P]

/-- Composition of comodule morphisms is compatible with negation in the left argument. -/
@[simp]
theorem neg_comp (g : Hom R C N P) (f : Hom R C M N) :
    comp (-g) f = -comp g f := by
  ext m
  simp [comp]

/-- Composition of comodule morphisms is compatible with negation in the right argument. -/
@[simp]
theorem comp_neg (g : Hom R C N P) (f : Hom R C M N) :
    comp g (-f) = -comp g f := by
  ext m
  exact map_neg g.toLinearMap (f m)

/-- Composition of comodule morphisms is subtractive in the left argument. -/
@[simp]
theorem sub_comp (g h : Hom R C N P) (f : Hom R C M N) :
    comp (g - h) f = comp g f - comp h f := by
  ext m
  simp [comp, sub_eq_add_neg]

/-- Composition of comodule morphisms is subtractive in the right argument. -/
@[simp]
theorem comp_sub (g : Hom R C N P) (f h : Hom R C M N) :
    comp g (f - h) = comp g f - comp g h := by
  ext m
  exact map_sub g.toLinearMap (f m) (h m)

end Comp

end Hom

end Comodule

namespace ComoduleCat

universe u v w

variable (R : Type u) [CommRing R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The category of right comodules over a coalgebra over a commutative ring is
preadditive. -/
instance preadditive : Preadditive (ComoduleCat.{u, v, w} R C) where
  homGroup M N := by
    letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    exact inferInstanceAs (AddCommGroup (Comodule.Hom R C M N))
  add_comp M N P f g h := by
    letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
    exact Comodule.Hom.comp_add (R := R) (C := C) h f g
  comp_add M N P f g h := by
    letI : AddCommGroup C := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup R
    letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
    exact Comodule.Hom.add_comp (R := R) (C := C) g h f

end ComoduleCat

end TauCeti
