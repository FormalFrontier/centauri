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

/-- A multiindex on `ι`, represented as a finitely supported function `ι →₀ ℕ`. -/
abbrev MultiIndex (ι : Type*) : Type _ :=
  ι →₀ ℕ

namespace MultiIndex

variable {ι : Type*}

/-- The total order, or degree, of a multiindex. -/
noncomputable abbrev order (α : MultiIndex ι) : ℕ :=
  Finsupp.degree α

/-- The multiindex with one derivative in coordinate `i` and none elsewhere. -/
noncomputable def unit (i : ι) : MultiIndex ι :=
  Finsupp.single i 1

@[simp]
lemma order_zero : order (0 : MultiIndex ι) = 0 := by
  simp [order]

@[simp]
lemma order_single (i : ι) (n : ℕ) : order (Finsupp.single i n : MultiIndex ι) = n := by
  simp [order]

@[simp]
lemma order_unit (i : ι) : order (unit i : MultiIndex ι) = 1 := by
  simp [unit]

@[simp]
lemma order_add (α β : MultiIndex ι) :
    order (α + β) = order α + order β := by
  simp [order]

lemma order_le_order_add_left (α β : MultiIndex ι) : order α ≤ order (α + β) := by
  rw [order_add]
  exact Nat.le_add_right _ _

lemma order_le_order_add_right (α β : MultiIndex ι) : order β ≤ order (α + β) := by
  rw [order_add]
  exact Nat.le_add_left _ _

lemma order_mono {α β : MultiIndex ι} (h : α ≤ β) :
    order α ≤ order β := by
  exact Finsupp.degree_mono h

lemma order_eq_sum [Fintype ι] (α : MultiIndex ι) : order α = ∑ i, α i := by
  exact Finsupp.degree_eq_sum α

lemma apply_le_order (α : MultiIndex ι) (i : ι) : α i ≤ order α := by
  exact Finsupp.le_degree i α

lemma eq_zero_of_order_eq_zero {α : MultiIndex ι} (h : order α = 0) : α = 0 := by
  exact (Finsupp.degree_eq_zero_iff α).mp h

@[simp]
lemma order_eq_zero_iff {α : MultiIndex ι} : order α = 0 ↔ α = 0 :=
  Finsupp.degree_eq_zero_iff α

@[simp]
lemma zero_lt_order_iff {α : MultiIndex ι} : 0 < order α ↔ α ≠ 0 := by
  constructor
  · intro h hα
    simp [hα] at h
  · intro h
    exact Nat.pos_of_ne_zero fun horder => h (order_eq_zero_iff.mp horder)

lemma order_pos_of_ne_zero {α : MultiIndex ι} (hα : α ≠ 0) : 0 < order α :=
  zero_lt_order_iff.mpr hα

lemma order_eq_one_iff {α : MultiIndex ι} : order α = 1 ↔ ∃ i, α = unit i := by
  constructor
  · intro h
    have hmem : α ∈ {d : ι →₀ ℕ | Finsupp.degree d = 1} := h
    rw [← Finsupp.range_single_one] at hmem
    rcases hmem with ⟨i, hi⟩
    exact ⟨i, by simpa [unit] using hi.symm⟩
  · rintro ⟨i, rfl⟩
    simp [unit, order]

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

noncomputable instance degreeLEFintype [Finite ι] : Fintype (DegreeLE ι k) := by
  classical
  exact Set.Finite.fintype (by
    change ({f : ι →₀ ℕ | Finsupp.degree f ≤ k} : Set (ι →₀ ℕ)).Finite
    exact Finsupp.finite_of_degree_le (σ := ι) k)

/-- There are only finitely many multiindices of order at most `k` on a finite index type. -/
lemma finite_setOf_order_le [Finite ι] (k : ℕ) : {α : MultiIndex ι | order α ≤ k}.Finite := by
  simpa [MultiIndex, order] using Finsupp.finite_of_degree_le (σ := ι) k

@[simp]
lemma mem_degreeLE_iff (α : MultiIndex ι) : α ∈ {α : MultiIndex ι | order α ≤ k} ↔
    order α ≤ k :=
  Iff.rfl

end DegreeLE

end MultiIndex

end TauCeti
