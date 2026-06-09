/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Coalgebra.Comodule

/-!
# Additive structure on comodule morphisms

This file records the pointwise additive-monoid structure on morphisms of right comodules.
The underlying linear maps already have zero, addition, natural-number scalar
multiplication, and finite sums; the only point to check is that these operations still
commute with the coactions.

This is basic infrastructure for the reductive-groups roadmap Layer 1 target
"Comodules over a coalgebra/Hopf algebra": the representation category of an affine group
scheme should have additive hom-sets before finite-dimensional, tensor, and dual structures
are built on top.
-/

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

namespace Hom

/-- The zero morphism of right comodules. -/
instance instZero : Zero (Hom R C M N) where
  zero :=
    { toLinearMap := 0
      map_coact := by
        ext m
        simp }

/-- Addition of right-comodule morphisms, defined pointwise. -/
instance instAdd : Add (Hom R C M N) where
  add f g :=
    { toLinearMap := f.toLinearMap + g.toLinearMap
      map_coact := by
        ext m
        simp [TensorProduct.map_add_left, map_coact_apply] }

@[simp]
theorem zero_toLinearMap : (0 : Hom R C M N).toLinearMap = 0 :=
  rfl

@[simp]
theorem add_toLinearMap (f g : Hom R C M N) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap :=
  rfl

/-- The zero comodule morphism evaluates to zero. -/
@[simp]
theorem zero_apply (m : M) : (0 : Hom R C M N) m = 0 :=
  rfl

/-- Addition of comodule morphisms is pointwise addition. -/
@[simp]
theorem add_apply (f g : Hom R C M N) (m : M) : (f + g) m = f m + g m :=
  rfl

/-- Natural-number scalar multiplication of comodule morphisms, defined by repeated
pointwise addition. -/
instance instNSMul : SMul ℕ (Hom R C M N) where
  smul n f := n.rec 0 fun _ g => f + g

instance instAddCommMonoid : AddCommMonoid (Hom R C M N) where
  zero := 0
  add := (· + ·)
  nsmul := (· • ·)
  zero_add f := by
    ext m
    simp
  add_zero f := by
    ext m
    simp
  add_assoc f g h := by
    ext m
    simp [add_assoc]
  add_comm f g := by
    ext m
    simp [add_comm]
  nsmul_zero f := by
    ext m
    change (0 : Hom R C M N) m = 0
    rfl
  nsmul_succ n f := by
    ext m
    change (f + n • f) m = (n • f + f) m
    rw [add_apply, add_apply, add_comm]

/-- Natural-number scalar multiplication of comodule morphisms is pointwise. -/
@[simp]
theorem nsmul_apply (n : ℕ) (f : Hom R C M N) (m : M) :
    (n • f) m = n • f m := by
  induction n with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      rfl
  | succ n ih =>
      rw [succ_nsmul, add_apply, ih, succ_nsmul]

/-- Finite sums of comodule morphisms are evaluated pointwise. -/
@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → Hom R C M N) (m : M) :
    (∑ i ∈ s, f i) m = ∑ i ∈ s, f i m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

section Comp

variable {P : Type*} [AddCommMonoid P] [Module R P] [Comodule R C P]

/-- Composition of comodule morphisms is additive in the left argument. -/
@[simp]
theorem comp_add (g h : Hom R C N P) (f : Hom R C M N) :
    comp (g + h) f = comp g f + comp h f := by
  ext m
  rfl

/-- Composition of comodule morphisms is additive in the right argument. -/
@[simp]
theorem add_comp (g : Hom R C N P) (f h : Hom R C M N) :
    comp g (f + h) = comp g f + comp g h := by
  ext m
  exact map_add g.toLinearMap (f m) (h m)

/-- Composing the zero morphism on the left gives the zero morphism. -/
@[simp]
theorem zero_comp (f : Hom R C M N) : comp (0 : Hom R C N P) f = 0 := by
  ext m
  rfl

/-- Composing the zero morphism on the right gives the zero morphism. -/
@[simp]
theorem comp_zero (g : Hom R C N P) : comp g (0 : Hom R C M N) = 0 := by
  ext m
  exact map_zero g.toLinearMap

end Comp

end Hom

end Comodule

end TauCeti
