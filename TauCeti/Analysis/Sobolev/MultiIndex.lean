/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finsupp.Weight

/-!
# Multiindices for Sobolev spaces

This file packages finitely supported functions `ι →₀ ℕ` as multiindices and records the
small amount of order bookkeeping needed to define weak derivatives of bounded total order.
For the PDE roadmap Lane A, the Sobolev norm on a finite-dimensional domain is indexed by
all multiindices of order at most `k`; the main structural fact here is that this indexing
type is finite when `ι` is finite.
-/

namespace TauCeti

/-- A multiindex on `ι`.

This wraps the `Finsupp` representation so the Sobolev API can stay focused on
finite-support derivative orders instead of exposing arbitrary `Finsupp` operations. -/
structure MultiIndex (ι : Type*) : Type _ where
  /-- The underlying finitely supported function. -/
  toFinsupp : ι →₀ ℕ
deriving DecidableEq

namespace MultiIndex

noncomputable section

variable {ι : Type*}

instance : CoeFun (MultiIndex ι) fun _ => ι → ℕ :=
  ⟨fun α => α.toFinsupp⟩

@[ext]
lemma ext {α β : MultiIndex ι} (h : ∀ i, α i = β i) : α = β := by
  cases α
  cases β
  congr
  exact Finsupp.ext h

instance : Zero (MultiIndex ι) :=
  ⟨⟨0⟩⟩

noncomputable instance : Add (MultiIndex ι) :=
  ⟨fun α β => ⟨α.toFinsupp + β.toFinsupp⟩⟩

instance : LE (MultiIndex ι) :=
  ⟨fun α β => α.toFinsupp ≤ β.toFinsupp⟩

@[simp]
lemma toFinsupp_zero : (0 : MultiIndex ι).toFinsupp = 0 :=
  rfl

@[simp]
lemma toFinsupp_add (α β : MultiIndex ι) :
    (α + β).toFinsupp = α.toFinsupp + β.toFinsupp :=
  rfl

@[simp]
lemma zero_apply (i : ι) : (0 : MultiIndex ι) i = 0 :=
  rfl

@[simp]
lemma add_apply (α β : MultiIndex ι) (i : ι) : (α + β) i = α i + β i :=
  rfl

/-- The total order, or degree, of a multiindex. -/
def order (α : MultiIndex ι) : ℕ :=
  Finsupp.degree α.toFinsupp

/-- The multiindex with one derivative in coordinate `i` and none elsewhere. -/
noncomputable def unit (i : ι) : MultiIndex ι :=
  ⟨Finsupp.single i 1⟩

@[simp]
lemma toFinsupp_unit (i : ι) : (unit i).toFinsupp = Finsupp.single i 1 :=
  rfl

@[simp]
lemma order_unit (i : ι) : order (unit i : MultiIndex ι) = 1 := by
  simp [order, unit]

@[simp]
lemma order_zero : order (0 : MultiIndex ι) = 0 := by
  simp [order]

@[simp]
lemma order_add (α β : MultiIndex ι) : order (α + β) = order α + order β := by
  simp [order]

@[simp]
lemma unit_apply_self (i : ι) : unit i i = 1 := by
  classical
  simp [unit]

@[simp]
lemma unit_apply_ne {i j : ι} (hij : j ≠ i) : unit i j = 0 := by
  classical
  simp [unit, hij]

lemma unit_le_iff (i : ι) (α : MultiIndex ι) : unit i ≤ α ↔ 1 ≤ α i := by
  classical
  constructor
  · intro h
    simpa [unit] using h i
  · intro hi j
    by_cases hji : j = i
    · subst j
      simpa [unit] using hi
    · simp [unit, hji]

/-- Multiindices whose total order is at most `k`, as a subtype. -/
abbrev DegreeLE (ι : Type*) (k : ℕ) : Type _ :=
  { α : MultiIndex ι // order α ≤ k }

section DegreeLE

variable {k : ℕ}

/-- There are only finitely many multiindices of order at most `k` on a finite index type. -/
lemma finite_setOf_order_le [Finite ι] (k : ℕ) : {α : MultiIndex ι | order α ≤ k}.Finite := by
  classical
  change Set.Finite (toFinsupp ⁻¹' {f : ι →₀ ℕ | Finsupp.degree f ≤ k})
  exact (Finsupp.finite_of_degree_le (σ := ι) k).preimage fun _ _ _ _ h =>
    ext fun i => congrFun (congrArg DFunLike.coe h) i

instance degreeLEFintype [Finite ι] : Fintype (DegreeLE ι k) := by
  classical
  exact Set.Finite.fintype (finite_setOf_order_le (ι := ι) k)

@[simp]
lemma mem_degreeLE_iff (α : MultiIndex ι) : α ∈ {α : MultiIndex ι | order α ≤ k} ↔
    order α ≤ k :=
  Iff.rfl

end DegreeLE

end

end MultiIndex

end TauCeti
