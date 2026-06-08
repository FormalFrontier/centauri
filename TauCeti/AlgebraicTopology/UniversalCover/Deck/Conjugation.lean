/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.AlgebraicTopology.UniversalCover.Deck

/-!
# Conjugating deck transformations

An isomorphism of maps over the same base transports deck transformations by conjugation.
This file packages that transport as a multiplicative equivalence of deck groups. It is
basic bookkeeping for the universal-covers roadmap: once covers are organized up to
isomorphism over the base, their deck groups must be identified by conjugating along the
chosen total-space homeomorphism.

## Main definitions

* `TauCeti.Deck.conjHomeomorph`: if `h : E ≃ₜ F` satisfies `q (h e) = p e`, then
  conjugation by `h` gives `Deck p ≃* Deck q`.
* `TauCeti.Deck.conjHomeomorphRefl`: the identity over-base homeomorphism induces the
  identity deck-group equivalence.
* `TauCeti.Deck.conjHomeomorphTrans`: conjugating along a composite over-base
  homeomorphism is the composite of the conjugation equivalences.

## References

This file supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 0.4
(`Deck p` as the deck transformation group), and the later cover-isomorphism bookkeeping in
Stage 2.
-/

namespace TauCeti

namespace Deck

variable {E F G B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → B} {q : F → B} {r : G → B}

/-- If `h : E ≃ₜ F` lies over the base, then its inverse also lies over the base in the
opposite direction. -/
lemma map_symm_eq_of_map_eq (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (f : F) :
    p (h.symm f) = q f := by
  rw [← hpq (h.symm f), h.apply_symm_apply]

/-- The homeomorphism obtained by conjugating an end-homeomorphism by `h`. This is the
underlying total-space homeomorphism used by `Deck.conjHomeomorph`. -/
def conjUnderlying (h : E ≃ₜ F) (φ : E ≃ₜ E) : F ≃ₜ F :=
  (h.symm.trans φ).trans h

/-- Conjugating by the identity homeomorphism leaves an end-homeomorphism unchanged. -/
@[simp]
lemma conjUnderlying_refl (φ : E ≃ₜ E) :
    conjUnderlying (Homeomorph.refl E) φ = φ := by
  ext e
  simp [conjUnderlying]

/-- Conjugation by a homeomorphism is evaluation by `h`, then `φ`, then `h.symm`, in the
expected order for a map `F → F`. -/
@[simp]
lemma conjUnderlying_apply (h : E ≃ₜ F) (φ : E ≃ₜ E) (f : F) :
    conjUnderlying h φ f = h (φ (h.symm f)) := by
  rfl

/-- The inverse of a conjugated homeomorphism is the conjugate of the inverse. -/
@[simp]
lemma conjUnderlying_symm (h : E ≃ₜ F) (φ : E ≃ₜ E) :
    (conjUnderlying h φ).symm = conjUnderlying h φ.symm := by
  ext f
  simp [conjUnderlying]

/-- Conjugation sends the identity homeomorphism to the identity homeomorphism. -/
@[simp]
lemma conjUnderlying_one (h : E ≃ₜ F) :
    conjUnderlying h 1 = 1 := by
  ext f
  simp [conjUnderlying]

/-- Conjugation sends composition of homeomorphisms to composition of the conjugates. -/
@[simp]
lemma conjUnderlying_mul (h : E ≃ₜ F) (φ ψ : E ≃ₜ E) :
    conjUnderlying h (φ * ψ) = conjUnderlying h φ * conjUnderlying h ψ := by
  ext f
  simp [conjUnderlying, Homeomorph.mul_apply]

/-- Conjugating twice is the same as conjugating by the composite homeomorphism. -/
@[simp]
lemma conjUnderlying_trans (h : E ≃ₜ F) (k : F ≃ₜ G) (φ : E ≃ₜ E) :
    conjUnderlying k (conjUnderlying h φ) = conjUnderlying (h.trans k) φ := by
  ext g
  simp [conjUnderlying]

/-- Conjugation by an over-base homeomorphism sends deck transformations to deck
transformations. -/
lemma conjUnderlying_mem_deck (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) (φ : Deck p) :
    conjUnderlying h φ.1 ∈ Deck q := by
  intro f
  calc
    q (conjUnderlying h φ.1 f) = q (h (φ.1 (h.symm f))) := rfl
    _ = p (φ.1 (h.symm f)) := hpq _
    _ = p (h.symm f) := map_proj φ _
    _ = q f := map_symm_eq_of_map_eq h hpq f

/-- An isomorphism of maps over the same base identifies their deck transformation groups
by conjugation on the total spaces. -/
def conjHomeomorph (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e) : Deck p ≃* Deck q where
  toFun φ := ⟨conjUnderlying h φ.1, conjUnderlying_mem_deck h hpq φ⟩
  invFun ψ := ⟨conjUnderlying h.symm ψ.1,
    conjUnderlying_mem_deck h.symm (map_symm_eq_of_map_eq h hpq) ψ⟩
  left_inv φ := by
    ext e
    simp [conjUnderlying]
  right_inv ψ := by
    ext f
    simp [conjUnderlying]
  map_mul' φ ψ := by
    ext f
    simp [conjUnderlying, Homeomorph.mul_apply]

/-- The deck transformation produced by `conjHomeomorph` evaluates by conjugation. -/
@[simp]
lemma conjHomeomorph_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (φ : Deck p) (f : F) :
    ((conjHomeomorph h hpq φ).1 f) = h (φ.1 (h.symm f)) := by
  rfl

/-- The inverse equivalence of `conjHomeomorph` is conjugation by the inverse
homeomorphism. -/
@[simp]
lemma conjHomeomorph_symm_apply_coe (h : E ≃ₜ F) (hpq : ∀ e, q (h e) = p e)
    (ψ : Deck q) (e : E) :
    (((conjHomeomorph h hpq).symm ψ).1 e) = h.symm (ψ.1 (h e)) := by
  rfl

/-- Conjugating deck transformations along the identity over-base homeomorphism gives the
identity deck-group equivalence. -/
@[simp]
lemma conjHomeomorphRefl :
    conjHomeomorph (Homeomorph.refl E) (p := p) (q := p) (fun _ => rfl) =
      MulEquiv.refl (Deck p) := by
  ext φ e
  simp

/-- Conjugating along a composite over-base homeomorphism is the composite of the two
conjugation equivalences. -/
lemma conjHomeomorphTrans (h : E ≃ₜ F) (k : F ≃ₜ G)
    (hpq : ∀ e, q (h e) = p e) (hqr : ∀ f, r (k f) = q f) :
    conjHomeomorph (h.trans k) (fun e => by rw [Homeomorph.trans_apply, hqr, hpq]) =
      (conjHomeomorph h hpq).trans (conjHomeomorph k hqr) := by
  ext φ g
  simp

end Deck

end TauCeti
