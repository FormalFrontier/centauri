/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.GroupTheory.GroupAction.Quotient
import TauCeti.Topology.Algebra.HomeomorphAction

/-!
# Deck transformations of a map

For a map `p : E → B`, its deck transformations are the homeomorphisms of `E` over `B`,
viewed as a subgroup of the homeomorphism group `E ≃ₜ E`. This is the first algebraic
piece needed by the universal-covers roadmap Stage 0.4: for a covering projection `p`, the
subgroup `Deck p` will be the deck transformation group.

The action of `Deck p` on the total space is inherited, by subgroup transfer, from the
tautological action of the ambient homeomorphism group `E ≃ₜ E` on `E`
(`TauCeti.Homeomorph.applyMulAction`). Each deck transformation preserves `p`, hence
preserves every fibre of `p`.

The final section records the quotient bookkeeping for this action: the projection `p`
descends to the orbit quotient by `Deck p`, and this descended map is an equivalence exactly
when the fibres of `p` are the orbits of the deck action. This is the set-level part of the
quotient comparison needed in the universal-covers roadmap after identifying
`Deck (UniversalCover.proj x₀)` with the fundamental group action.

## References

This file follows the deck-transformation target in the Tau Ceti universal-covers roadmap,
Stage 0.4, and the shape of the construction in Kim Morrison's mathlib4#40135.
-/

namespace TauCeti

variable {E B : Type*} [TopologicalSpace E] (p : E → B)

/-- The deck transformations of a map `p : E → B`, as the subgroup of homeomorphisms of `E`
which commute with `p`. For a covering projection, this is the usual deck transformation
group. -/
def Deck : Subgroup (E ≃ₜ E) where
  carrier := {φ | ∀ e, p (φ e) = p e}
  one_mem' e := rfl
  mul_mem' hφ hψ e := by
    rw [Homeomorph.mul_apply, hφ, hψ]
  inv_mem' := by
    intro φ hφ e
    have h := hφ (φ⁻¹ e)
    simpa only [Homeomorph.inv_apply, Homeomorph.apply_symm_apply] using h.symm

namespace Deck

variable {p}

/-- A homeomorphism lies in `Deck p` exactly when it preserves `p` pointwise. -/
@[simp]
lemma mem_iff (φ : E ≃ₜ E) : φ ∈ Deck p ↔ ∀ e, p (φ e) = p e :=
  Iff.rfl

/-- A deck transformation preserves the projection map pointwise. -/
lemma map_proj (φ : Deck p) (e : E) : p (φ.1 e) = p e :=
  φ.2 e

/-- A deck transformation preserves each fibre of the projection. -/
lemma mapsTo_fiber (φ : Deck p) (b : B) : Set.MapsTo φ.1 (p ⁻¹' {b}) (p ⁻¹' {b}) := by
  intro e he
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, map_proj] using he

/-- The inverse of a deck transformation also preserves each fibre of the projection. -/
lemma mapsTo_fiber_symm (φ : Deck p) (b : B) :
    Set.MapsTo φ.1.symm (p ⁻¹' {b}) (p ⁻¹' {b}) := by
  intro e he
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at he ⊢
  rw [← map_proj φ (φ.1.symm e), Homeomorph.apply_symm_apply]
  exact he

/-- A deck transformation restricts to a homeomorphism of every fibre of the projection,
the restriction of its underlying homeomorphism along `Homeomorph.subtype`. -/
def fiberHomeomorph (φ : Deck p) (b : B) : p ⁻¹' {b} ≃ₜ p ⁻¹' {b} :=
  φ.1.subtype fun e => by simp [Set.mem_preimage, eq_comm, map_proj]

/-- On points, the fibre homeomorphism induced by a deck transformation is just evaluation
of that transformation. -/
@[simp]
lemma fiberHomeomorph_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    (fiberHomeomorph φ b e : E) = φ.1 e.1 :=
  rfl

/-- On points, the inverse fibre homeomorphism induced by a deck transformation is
evaluation of the inverse homeomorphism. -/
@[simp]
lemma fiberHomeomorph_symm_apply (φ : Deck p) (b : B) (e : p ⁻¹' {b}) :
    ((fiberHomeomorph φ b).symm e : E) = φ.1.symm e.1 :=
  rfl

/-- On points, the action of a deck transformation is evaluation of its underlying
homeomorphism. The action itself is inherited, by subgroup transfer, from the tautological
action of `E ≃ₜ E` on `E`. -/
@[simp]
lemma smul_eq_apply (φ : Deck p) (e : E) : φ • e = φ.1 e :=
  rfl

/-- The action of a deck transformation preserves the projection map pointwise. -/
lemma proj_smul (φ : Deck p) (e : E) : p (φ • e) = p e := by
  rw [smul_eq_apply]
  exact map_proj φ e

/-- Acting by a deck transformation keeps a point in the same fibre. -/
lemma smul_mem_fiber (φ : Deck p) (e : E) : φ • e ∈ p ⁻¹' {p e} := by
  exact proj_smul φ e

/-- The deck orbit of a point is contained in its fibre. -/
lemma orbit_subset_fiber (e : E) : MulAction.orbit (Deck p) e ⊆ p ⁻¹' {p e} := by
  intro e' he'
  rcases MulAction.mem_orbit_iff.mp he' with ⟨φ, rfl⟩
  exact smul_mem_fiber φ e

/-- If two points lie in the same deck orbit, then they have the same image under `p`. -/
lemma eq_proj_of_mem_orbit {e₁ e₂ : E} (h : e₁ ∈ MulAction.orbit (Deck p) e₂) :
    p e₁ = p e₂ :=
  orbit_subset_fiber (p := p) e₂ h

/-- Equality under `p` is equivalent to lying in the same deck orbit, provided every fibre is
a single deck orbit. This packages the freeness/transitivity condition used by quotient-cover
arguments. -/
lemma proj_eq_iff_mem_orbit
    (h : ∀ {e₁ e₂ : E}, p e₁ = p e₂ → e₁ ∈ MulAction.orbit (Deck p) e₂) {e₁ e₂ : E} :
    p e₁ = p e₂ ↔ e₁ ∈ MulAction.orbit (Deck p) e₂ :=
  ⟨h, eq_proj_of_mem_orbit (p := p)⟩

/-- If the projection has fibre-orbit equality, the quotient relation for the deck action is
the same as equality of projections. -/
lemma orbitRel_iff_proj_eq
    (h : ∀ {e₁ e₂ : E}, p e₁ = p e₂ → e₁ ∈ MulAction.orbit (Deck p) e₂) {e₁ e₂ : E} :
    MulAction.orbitRel (Deck p) E e₁ e₂ ↔ p e₁ = p e₂ := by
  rw [MulAction.orbitRel_apply]
  exact (proj_eq_iff_mem_orbit (p := p) h).symm

/-- The projection `p` descends to the quotient of `E` by the deck action. -/
def orbitProj : MulAction.orbitRel.Quotient (Deck p) E → B :=
  Quotient.lift p fun e₁ e₂ h => by
    exact eq_proj_of_mem_orbit (p := p) (MulAction.orbitRel_apply.mp h)

/-- The descended projection sends the orbit of `e` to `p e`. -/
@[simp]
lemma orbitProj_mk (e : E) :
    orbitProj (p := p) (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) = p e := by
  rfl

/-- The descended projection is surjective when the original projection is surjective. -/
lemma orbitProj_surjective (hp : Function.Surjective p) :
    Function.Surjective (orbitProj (p := p)) :=
  Quotient.lift_surjective p _ hp

/-- The descended projection is injective when each fibre of `p` is a deck orbit. -/
lemma orbitProj_injective
    (h : ∀ {e₁ e₂ : E}, p e₁ = p e₂ → e₁ ∈ MulAction.orbit (Deck p) e₂) :
    Function.Injective (orbitProj (p := p)) := by
  intro q r hqr
  induction q using Quotient.inductionOn
  induction r using Quotient.inductionOn
  apply Quotient.sound
  rw [orbitProj_mk, orbitProj_mk] at hqr
  exact (orbitRel_iff_proj_eq (p := p) h).mpr hqr

/-- If `p` is surjective and its fibres are exactly the deck orbits, then the orbit quotient
by `Deck p` is equivalent to the base. This is the set-level quotient comparison used before
upgrading to a homeomorphism in covering-space applications. -/
noncomputable def orbitProjEquiv (hp : Function.Surjective p)
    (h : ∀ {e₁ e₂ : E}, p e₁ = p e₂ → e₁ ∈ MulAction.orbit (Deck p) e₂) :
    MulAction.orbitRel.Quotient (Deck p) E ≃ B :=
  Equiv.ofBijective (orbitProj (p := p))
    ⟨orbitProj_injective (p := p) h, orbitProj_surjective (p := p) hp⟩

/-- The equivalence induced by the descended deck-orbit projection sends the orbit of `e` to
`p e`. -/
@[simp]
lemma orbitProjEquiv_apply (hp : Function.Surjective p)
    (h : ∀ {e₁ e₂ : E}, p e₁ = p e₂ → e₁ ∈ MulAction.orbit (Deck p) e₂) (e : E) :
    orbitProjEquiv (p := p) hp h
      (Quotient.mk'' e : MulAction.orbitRel.Quotient (Deck p) E) = p e := by
  simp [orbitProjEquiv]

/-- A point of the base is the image of any representative of its preimage under the inverse
of the deck-orbit quotient equivalence. -/
lemma proj_orbitProjEquiv_symm (hp : Function.Surjective p)
    (h : ∀ {e₁ e₂ : E}, p e₁ = p e₂ → e₁ ∈ MulAction.orbit (Deck p) e₂) (b : B) :
    p ((orbitProjEquiv (p := p) hp h).symm b).out = b := by
  let q := (orbitProjEquiv (p := p) hp h).symm b
  have hb : orbitProj (p := p) q = b := (orbitProjEquiv (p := p) hp h).apply_symm_apply b
  calc
    p q.out = orbitProj (p := p)
        (Quotient.mk'' q.out : MulAction.orbitRel.Quotient (Deck p) E) := by
      exact (orbitProj_mk (p := p) q.out).symm
    _ = orbitProj (p := p) q := by
      rw [Quotient.out_eq' q]
    _ = b := hb

-- `FaithfulSMul (Deck p) E` and `ContinuousConstSMul (Deck p) E` are inherited from the generic
-- subgroup instances in `TauCeti.Topology.Algebra.HomeomorphAction`; `Deck p` is a `Subgroup`.

end Deck

end TauCeti
