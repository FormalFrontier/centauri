/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homeomorph.Lemmas
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
lemma smul_mem_fiber (φ : Deck p) (e : E) : φ • e ∈ p ⁻¹' {p e} :=
  proj_smul φ e

/-- The deck orbit of a point is contained in its fibre. -/
lemma orbit_subset_fiber (e : E) : MulAction.orbit (Deck p) e ⊆ p ⁻¹' {p e} := by
  intro e' he'
  rcases MulAction.mem_orbit_iff.mp he' with ⟨φ, rfl⟩
  exact smul_mem_fiber φ e

/-- If two points lie in the same deck orbit, then they have the same image under `p`. -/
lemma eq_proj_of_mem_orbit {e₁ e₂ : E} (h : e₁ ∈ MulAction.orbit (Deck p) e₂) :
    p e₁ = p e₂ :=
  orbit_subset_fiber (p := p) e₂ h

/-- If two points are related by the deck orbit relation, then they have the same image under
`p`. This is the quotient-facing form of `Deck.eq_proj_of_mem_orbit`. -/
lemma eq_proj_of_orbitRel {e₁ e₂ : E} (h : MulAction.orbitRel (Deck p) E e₁ e₂) :
    p e₁ = p e₂ :=
  eq_proj_of_mem_orbit (p := p) (MulAction.orbitRel_apply.mp h)

/-- The map induced by `p` on the quotient of `E` by the deck-orbit relation. -/
def orbitRelQuotientProj : Quotient (MulAction.orbitRel (Deck p) E) → B :=
  Quotient.lift p fun _ _ h => eq_proj_of_orbitRel (p := p) h

/-- The descended projection sends the orbit class of a point to its image under `p`. -/
@[simp]
lemma orbitRelQuotientProj_mk (e : E) :
    orbitRelQuotientProj (p := p) (Quotient.mk'' e) = p e :=
  rfl

/-- If `p` is surjective, then so is the projection descended to deck-orbit classes. -/
lemma orbitRelQuotientProj_surjective (hp : Function.Surjective p) :
    Function.Surjective (orbitRelQuotientProj (p := p)) := by
  rintro b
  rcases hp b with ⟨e, rfl⟩
  exact ⟨Quotient.mk'' e, rfl⟩

/-- If every fibre is contained in a deck orbit, then the projection descended to deck-orbit
classes is injective. Together with `Deck.orbit_subset_fiber`, this says precisely that
fibres are the deck orbits. -/
lemma orbitRelQuotientProj_injective_of_fiber_subset_orbit
    (h : ∀ {e₁ e₂ : E}, p e₁ = p e₂ → MulAction.orbitRel (Deck p) E e₁ e₂) :
    Function.Injective (orbitRelQuotientProj (p := p)) := by
  intro q₁ q₂ hq
  induction q₁ using Quotient.inductionOn' with
  | h e₁ =>
    induction q₂ using Quotient.inductionOn' with
    | h e₂ =>
      exact Quotient.sound' (h hq)

/-- When `p` is surjective and every fibre is a deck orbit, the projection descended to
deck-orbit classes is an equivalence. -/
noncomputable def orbitRelQuotientProjEquivOfFiberOrbit
    (hp : Function.Surjective p)
    (h : ∀ {e₁ e₂ : E}, p e₁ = p e₂ → MulAction.orbitRel (Deck p) E e₁ e₂) :
    Quotient (MulAction.orbitRel (Deck p) E) ≃ B :=
  Equiv.ofBijective (orbitRelQuotientProj (p := p))
    ⟨orbitRelQuotientProj_injective_of_fiber_subset_orbit (p := p) h,
      orbitRelQuotientProj_surjective (p := p) hp⟩

-- `FaithfulSMul (Deck p) E` and `ContinuousConstSMul (Deck p) E` are inherited from the generic
-- subgroup instances in `TauCeti.Topology.Algebra.HomeomorphAction`; `Deck p` is a `Subgroup`.

end Deck

end TauCeti
