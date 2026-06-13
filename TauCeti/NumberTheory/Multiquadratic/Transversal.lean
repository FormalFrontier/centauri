/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Conjugate-transversal ideal families in a Dedekind domain

Let `σ` be a ring involution of a Dedekind domain `R` and `S` a finite set of nonzero prime
ideals that is closed under `σ`, on which `σ` acts as a fixed-point-free involution. Pairing
each prime with its conjugate `σ p ≠ p`, one can choose, for each of the `S.card / 2` conjugate
orbits, either the prime or its conjugate; multiplying the choices gives a family of `2 ^ (S.card
/ 2)` ideals `A`, each satisfying `A * σ A = ∏ p ∈ S, p`.

This is the combinatorial core behind counting the ideals `𝔄` with `𝔄 · σ 𝔄` a fixed product of
split primes — the engine of the prime-splitting layer of the multiquadratic roadmap.

## Main results

* `TauCeti.Multiquadratic.exists_transversal_family`: the family of `≥ 2 ^ (S.card / 2)` ideals.

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where it counted
the conjugate-product ideals over primes `p ≡ 1 (mod 4)` in a concrete CM field.
-/

attribute [local instance] Classical.propDecidable

namespace TauCeti.Multiquadratic

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A nonzero prime ideal of a Dedekind domain does not divide a finite product of nonzero
prime ideals unless it equals one of the factors. -/
private theorem isPrime_not_dvd_prod {p : Ideal R} (hp : p.IsPrime) (hp0 : p ≠ ⊥)
    {T : Finset (Ideal R)} (hT : ∀ q ∈ T, q.IsPrime) (hT0 : ∀ q ∈ T, q ≠ ⊥)
    (hpT : p ∉ T) : ¬ p ∣ ∏ q ∈ T, q := by
  haveI := hp
  have hpprime : Prime p := (Ideal.prime_iff_isPrime hp0).mpr hp
  rw [Prime.dvd_finsetProd_iff hpprime]
  rintro ⟨q, hqT, hpq⟩
  have hqprime : q.IsPrime := hT q hqT
  have hqmax : q.IsMaximal := hqprime.isMaximal (hT0 q hqT)
  have hpmax : p.IsMaximal := hp.isMaximal hp0
  have heq : q = p := hqmax.eq_of_le hpmax.ne_top (Ideal.le_of_dvd hpq)
  exact hpT (heq ▸ hqT)

/-- **Conjugate-transversal ideal family.** For a fixed-point-free involution `σ` of a finite set
`S` of nonzero prime ideals of a Dedekind domain, there are at least `2 ^ (S.card / 2)` ideals
`A` with `A * σ A = ∏ p ∈ S, p` — one for each way of choosing a representative from each
conjugate pair. -/
theorem exists_transversal_family (σ : R ≃+* R) (S : Finset (Ideal R))
    (hprime : ∀ p ∈ S, p.IsPrime) (hne : ∀ p ∈ S, p ≠ ⊥)
    (hinv : ∀ p ∈ S, Ideal.map σ p ∈ S)
    (hinvol : ∀ p ∈ S, Ideal.map σ (Ideal.map σ p) = p)
    (hfree : ∀ p ∈ S, Ideal.map σ p ≠ p) :
    ∃ G : Finset (Ideal R), 2 ^ (S.card / 2) ≤ G.card ∧
      ∀ A ∈ G, A * Ideal.map σ A = ∏ p ∈ S, p := by
  induction S using Finset.strongInduction with
  | _ S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hS
  · refine ⟨{1}, by simp, fun A hA => ?_⟩
    rw [Finset.mem_singleton.mp hA, Finset.prod_empty, one_mul, Ideal.one_eq_top, Ideal.map_top]
  obtain ⟨p, hpS⟩ := hS
  set q := Ideal.map σ p with hqdef
  have hqS : q ∈ S := hinv p hpS
  have hpq : q ≠ p := hfree p hpS
  have hp0 : p ≠ ⊥ := hne p hpS
  have hpprime : p.IsPrime := hprime p hpS
  have hpair : ({p, q} : Finset (Ideal R)) ⊆ S := by
    intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hpS
    · rw [Finset.mem_singleton.mp hx]; exact hqS
  set S' := S \ {p, q} with hS'def
  have hS'sub : S' ⊂ S := by
    refine Finset.sdiff_ssubset hpair ?_
    exact ⟨p, Finset.mem_insert_self _ _⟩
  -- The subset `S'` still satisfies all the hypotheses.
  have hmem' : ∀ {x}, x ∈ S' → x ∈ S := fun hx => (Finset.mem_sdiff.mp hx).1
  obtain ⟨G', hcard', hprod'⟩ := ih S' hS'sub
    (fun x hx => hprime x (hmem' hx)) (fun x hx => hne x (hmem' hx))
    (fun x hx => by
      have hxS := hmem' hx
      have hxnotpair : x ∉ ({p, q} : Finset (Ideal R)) := (Finset.mem_sdiff.mp hx).2
      refine Finset.mem_sdiff.mpr ⟨hinv x hxS, ?_⟩
      rw [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h)
      · -- `map σ x = p` forces `x = map σ p = q`, but `x ∉ {p, q}`.
        refine hxnotpair ?_
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr <| calc x = Ideal.map σ (Ideal.map σ x) := (hinvol x hxS).symm
          _ = Ideal.map σ p := by rw [h]
          _ = q := hqdef.symm
      · -- `map σ x = q = map σ p` forces `x = p`, but `x ∉ {p, q}`.
        refine hxnotpair ?_
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl <| calc x = Ideal.map σ (Ideal.map σ x) := (hinvol x hxS).symm
          _ = Ideal.map σ q := by rw [h]
          _ = Ideal.map σ (Ideal.map σ p) := by rw [hqdef]
          _ = p := hinvol p hpS)
    (fun x hx => hinvol x (hmem' hx)) (fun x hx => hfree x (hmem' hx))
  -- The product over `S` factors through the conjugate pair we removed.
  have hprodS : ∏ x ∈ S, x = (∏ x ∈ S', x) * p * q := by
    rw [hS'def, ← Finset.prod_sdiff hpair, Finset.prod_pair hpq.symm, mul_assoc]
  have hcardS : S'.card = S.card - 2 := by
    have h := Finset.card_sdiff_add_card_eq_card hpair
    rw [Finset.card_pair hpq.symm] at h
    rw [hS'def]; omega
  have hpS' : p ∉ S' := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self _ _)
  refine ⟨(G'.image (· * p)) ∪ (G'.image (· * q)), ?_, ?_⟩
  · -- The two images are disjoint and each has the size of `G'`.
    have hinjp : Function.Injective (· * p : Ideal R → Ideal R) :=
      fun a b h => mul_right_cancel₀ hp0 h
    have hinjq : Function.Injective (· * q : Ideal R → Ideal R) :=
      fun a b h => mul_right_cancel₀ (by rw [hqdef]; exact (hne q hqS)) h
    have hdisj : Disjoint (G'.image (· * p)) (G'.image (· * q)) := by
      rw [Finset.disjoint_left]
      rintro A hAp hAq
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hAp
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hAq
      -- `a * p = b * q` forces `p ∣ b`, hence `p ∣ ∏ S'`, a contradiction.
      have hpdvd : p ∣ b := by
        have hpdvd' : p ∣ b * q := hab.symm ▸ dvd_mul_left p a
        rcases ((Ideal.prime_iff_isPrime hp0).mpr hpprime).dvd_or_dvd hpdvd' with h | h
        · exact h
        · have hqmax : q.IsMaximal := (hprime q hqS).isMaximal (hne q hqS)
          have hpmax : p.IsMaximal := hpprime.isMaximal hp0
          exact absurd (hqmax.eq_of_le hpmax.ne_top (Ideal.le_of_dvd h)) hpq
      exact isPrime_not_dvd_prod hpprime hp0 (fun x hx => hprime x (hmem' hx))
        (fun x hx => hne x (hmem' hx)) hpS'
        (hprod' b hb ▸ dvd_mul_of_dvd_left hpdvd (Ideal.map σ b))
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinjp,
      Finset.card_image_of_injective _ hinjq]
    have h2 : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨p, hpS, q, hqS, hpq.symm⟩
    calc 2 ^ (S.card / 2) = 2 * 2 ^ (S.card / 2 - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_div_iff (by norm_num) |>.mpr h2)]
      _ ≤ 2 * 2 ^ (S'.card / 2) := by
            gcongr
            · norm_num
            · rw [hcardS]; omega
      _ ≤ G'.card + G'.card := by omega
  · rintro A hA
    rw [Finset.mem_union] at hA
    rcases hA with hA | hA
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
      rw [Ideal.map_mul, ← hqdef, hprodS, ← hprod' a ha]; ring
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
      have hmapq : Ideal.map σ q = p := hinvol p hpS
      rw [Ideal.map_mul, hmapq, hprodS, ← hprod' a ha]; ring

end TauCeti.Multiquadratic
