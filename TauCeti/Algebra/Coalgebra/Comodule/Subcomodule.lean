/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Coalgebra.Comodule

/-!
# Subcomodules

This file defines subcomodules of a right comodule over a coalgebra: submodules whose
coaction factors through the tensor product of the submodule with the coalgebra.

The reductive-groups roadmap asks for finite-dimensional subcomodules and the fundamental
theorem of comodules. This file supplies the first small piece of that infrastructure:
the stability predicate, the bundled subtype of stable submodules, and the top and bottom
subcomodules.

## Main definitions

* `TauCeti.IsSubcomodule`: the predicate that a submodule is stable under the coaction.
* `TauCeti.Subcomodule`: a submodule satisfying `IsSubcomodule`.

## References

This is standard coalgebra language, added for
`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 1 target "Finite-dimensional
subcoalgebras (the fundamental theorem of comodules)" and its statement that every comodule
is the union of its finite-dimensional subcomodules.
-/

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The image of `P ⊗ C` in `M ⊗ C` induced by the inclusion of a submodule `P ≤ M`. -/
def submoduleCoactionRange (P : Submodule R M) : Submodule R (M ⊗[R] C) :=
  LinearMap.range (TensorProduct.map P.subtype (LinearMap.id (R := R) (M := C)))

/-- A submodule of a right comodule is a subcomodule if the coaction of every element factors
through `P ⊗ C → M ⊗ C`. -/
def IsSubcomodule (P : Submodule R M) : Prop :=
  ∀ ⦃m : M⦄, m ∈ P →
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      submoduleCoactionRange (R := R) (C := C) P

/-- A subcomodule of a right comodule, bundled as a coaction-stable submodule. -/
abbrev Subcomodule (R : Type u) (C : Type v) (M : Type w) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M]
    [Comodule R C M] :=
  { P : Submodule R M // IsSubcomodule (R := R) (C := C) (M := M) P }

namespace Subcomodule

/-- Bundle a coaction-stable submodule as a subcomodule. -/
def mk (P : Submodule R M) (hP : IsSubcomodule (R := R) (C := C) (M := M) P) :
    Subcomodule R C M :=
  ⟨P, hP⟩

/-- The underlying submodule of a subcomodule. -/
def toSubmodule (P : Subcomodule R C M) : Submodule R M :=
  P.1

@[simp]
theorem mk_toSubmodule (P : Submodule R M)
    (hP : IsSubcomodule (R := R) (C := C) (M := M) P) :
    toSubmodule (mk (R := R) (C := C) (M := M) P hP) = P :=
  rfl

/-- The stability proof carried by a subcomodule. -/
theorem isSubcomodule (P : Subcomodule R C M) :
    IsSubcomodule (R := R) (C := C) (M := M) P.toSubmodule :=
  P.property

@[simp]
theorem mem_toSubmodule (P : Subcomodule R C M) (m : M) :
    m ∈ P.toSubmodule ↔ m ∈ P.1 :=
  Iff.rfl

/-- The coaction of an element of a subcomodule factors through `P ⊗ C`. -/
theorem map_coact (P : Subcomodule R C M) ⦃m : M⦄ (hm : m ∈ P.toSubmodule) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      submoduleCoactionRange (R := R) (C := C) P.toSubmodule :=
  P.property hm

/-- Membership in the underlying submodule is closed under zero. -/
theorem zero_mem (P : Subcomodule R C M) : (0 : M) ∈ P.toSubmodule :=
  P.toSubmodule.zero_mem

/-- Membership in the underlying submodule is closed under addition. -/
theorem add_mem (P : Subcomodule R C M) ⦃m n : M⦄ (hm : m ∈ P.toSubmodule)
    (hn : n ∈ P.toSubmodule) : m + n ∈ P.toSubmodule :=
  P.toSubmodule.add_mem hm hn

/-- Membership in the underlying submodule is closed under scalar multiplication. -/
theorem smul_mem (P : Subcomodule R C M) (r : R) ⦃m : M⦄
    (hm : m ∈ P.toSubmodule) : r • m ∈ P.toSubmodule :=
  P.toSubmodule.smul_mem r hm

end Subcomodule

end TauCeti
