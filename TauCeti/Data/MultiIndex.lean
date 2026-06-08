/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.Weight

/-!
# Multiindices

Multiindices are finitely supported natural-valued functions with a total order. They are
used by the PDE roadmap Lane A to index the finite derivative families appearing in
weak-derivative Sobolev norms.

Mathlib already provides the underlying finitely supported functions `ι →₀ ℕ`, coordinate
units via `Finsupp.single`, total degree via `Finsupp.degree`, and bounded-degree finiteness
via `Finsupp.finite_of_degree_le`. This file packages that representation behind a small
Tau Ceti API for derivative bookkeeping.
-/

namespace TauCeti

/-- A multiindex on `ι`, backed by Mathlib's finitely supported functions. -/
structure MultiIndex (ι : Type*) : Type _ where
  /-- The finitely supported function represented by a multiindex. -/
  toFinsupp : ι →₀ ℕ

namespace MultiIndex

instance : CoeFun (MultiIndex ι) fun _ => ι → ℕ where
  coe α := α.toFinsupp

@[ext]
lemma ext {α β : MultiIndex ι} (h : ∀ i, α i = β i) : α = β := by
  cases α
  cases β
  congr
  exact Finsupp.ext h

noncomputable instance : Zero (MultiIndex ι) where
  zero := ⟨0⟩

@[simp]
lemma toFinsupp_zero : (0 : MultiIndex ι).toFinsupp = 0 :=
  rfl

@[simp]
lemma zero_apply (i : ι) : (0 : MultiIndex ι) i = 0 :=
  rfl

/-- The total order of a multiindex. -/
noncomputable def order (α : MultiIndex ι) : ℕ :=
  Finsupp.degree α.toFinsupp

@[simp]
lemma order_def (α : MultiIndex ι) : α.order = Finsupp.degree α.toFinsupp :=
  rfl

@[simp]
lemma order_zero : (0 : MultiIndex ι).order = 0 :=
  rfl

/-- The first-order multiindex in the coordinate `i`. -/
noncomputable def unit (i : ι) : MultiIndex ι :=
  ⟨Finsupp.single i 1⟩

@[simp]
lemma toFinsupp_unit (i : ι) : (unit i).toFinsupp = Finsupp.single i 1 :=
  rfl

@[simp]
lemma unit_apply_self (i : ι) : unit i i = 1 :=
  Finsupp.single_eq_same

@[simp]
lemma unit_apply_of_ne {i j : ι} (h : j ≠ i) : unit i j = 0 :=
  Finsupp.single_eq_of_ne h

@[simp]
lemma order_unit (i : ι) : (unit i).order = 1 :=
  Finsupp.degree_single i 1

/-- Multiindices whose total order is at most `k`, as a set. -/
def degreeLE (ι : Type*) (k : ℕ) : Set (MultiIndex ι) :=
  {α | α.order ≤ k}

/-- Multiindices whose total order is at most `k`, as a subtype. -/
abbrev DegreeLE (ι : Type*) (k : ℕ) : Type _ :=
  degreeLE ι k

@[simp]
lemma mem_degreeLE_iff {α : MultiIndex ι} {k : ℕ} : α ∈ degreeLE ι k ↔ α.order ≤ k :=
  Iff.rfl

variable {k : ℕ}

lemma coordinate_le_order (α : MultiIndex ι) (i : ι) : α i ≤ α.order :=
  Finsupp.le_degree i α.toFinsupp

lemma coordinate_le_of_mem_degreeLE (α : DegreeLE ι k) (i : ι) : α.1 i ≤ k :=
  le_trans (coordinate_le_order α.1 i) α.2

lemma eq_zero_of_order_eq_zero {α : MultiIndex ι} (hα : α.order = 0) : α = 0 := by
  ext i
  have h : α.toFinsupp = 0 := (Finsupp.degree_eq_zero_iff α.toFinsupp).mp hα
  rw [h]
  rfl

lemma eq_unit_of_order_eq_one {α : MultiIndex ι} (hα : α.order = 1) :
    ∃ i, α = unit i := by
  have hmem : α.toFinsupp ∈ Set.range (fun i : ι => Finsupp.single i 1) := by
    rw [Finsupp.range_single_one]
    exact hα
  rcases hmem with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  cases α with
  | mk f =>
      cases hi
      rfl

lemma order_le_one_iff {α : MultiIndex ι} :
    α.order ≤ 1 ↔ α = 0 ∨ ∃ i, α = unit i := by
  constructor
  · intro hα
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hα with hzero | hone
    · exact Or.inl (eq_zero_of_order_eq_zero hzero)
    · exact Or.inr (eq_unit_of_order_eq_one hone)
  · rintro (rfl | ⟨i, rfl⟩)
    · simp
    · simp

noncomputable instance degreeLEFintype [Finite ι] : Fintype (DegreeLE ι k) := by
  classical
  letI : Fintype { α : ι →₀ ℕ // Finsupp.degree α ≤ k } :=
    Set.Finite.fintype (Finsupp.finite_of_degree_le (σ := ι) k)
  exact Fintype.ofEquiv { α : ι →₀ ℕ // Finsupp.degree α ≤ k }
    { toFun := fun α => ⟨⟨α.1⟩, α.2⟩
      invFun := fun α => ⟨α.1.toFinsupp, α.2⟩
      left_inv := by
        intro α
        rfl
      right_inv := by
        intro α
        cases α with
        | mk α hα =>
            cases α
            rfl }

end MultiIndex

end TauCeti
