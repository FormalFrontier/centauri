/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import TauCeti.NumberTheory.Multiquadratic.Degree

/-!
# A multiquadratic field is Galois, with group `(ℤ/2)ⁿ`

Over a field `K` of characteristic zero, a multiquadratic field `M = K(rootᵢ : i)` (with
`rootᵢ ^ 2 = dᵢ ∈ K`) is the splitting field of the polynomial `∏ᵢ (X² - dᵢ)`, hence Galois.
Each automorphism sends every generator to `± rootᵢ`, so it is determined by a *sign pattern*
`ι → ℤ/2`; this assignment is an injective group homomorphism. When the radicands are
square-class independent the degree is `2ⁿ` (`TauCeti.NumberTheory.Multiquadratic.Degree`), so
counting forces the homomorphism to be an isomorphism: `Gal(M/K) ≃ (ℤ/2)ⁿ`.

## Main results

* `TauCeti.Multiquadratic.isGalois`: `M / K` is Galois.
* `TauCeti.Multiquadratic.signHom`: the injective sign-pattern homomorphism `Gal(M/K) →* (ℤ/2)ⁿ`.
* `TauCeti.Multiquadratic.galoisGroupEquiv`: the explicit isomorphism
  `Gal(M/K) ≃* Multiplicative (ι → ℤ/2)`.

## Provenance

Generalised from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture, where the
sign-change automorphisms of one concrete multiquadratic field were analysed; here the
construction is carried out for an arbitrary such tower.
-/

open Polynomial IntermediateField

attribute [local instance] Classical.propDecidable

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*} [Finite ι]
  {d : ι → K} {root : ι → L}

/-- The defining polynomial of the multiquadratic field: `∏ᵢ (X² - dᵢ)`. -/
noncomputable def mqPoly (d : ι → K) : K[X] :=
  letI := Fintype.ofFinite ι
  ∏ i, (X ^ 2 - C (d i))

omit [Finite ι] in
/-- Each quadratic factor splits in `M`, with roots `± rootᵢ`. -/
theorem splits_X_sq_sub_C (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    ((X ^ 2 - C (d i)).map (algebraMap K (adjoin K (Set.range root)))).Splits := by
  have hmem : root i ∈ adjoin K (Set.range root) := subset_adjoin _ _ ⟨i, rfl⟩
  have hy2 : (⟨root i, hmem⟩ : adjoin K (Set.range root)) ^ 2
      = algebraMap K (adjoin K (Set.range root)) (d i) := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, IntermediateField.coe_algebraMap_apply]
    exact hroot i
  have hfac : (X ^ 2 - C (d i)).map (algebraMap K (adjoin K (Set.range root)))
      = (X - C ⟨root i, hmem⟩) * (X - C (-⟨root i, hmem⟩)) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, ← hy2, map_pow, map_neg]; ring
  rw [hfac]
  exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.X_sub_C _)

/-- The `i`-th generator, as an element of the multiquadratic field `M`. -/
noncomputable def gen (root : ι → L) (i : ι) : adjoin K (Set.range root) :=
  ⟨root i, subset_adjoin _ _ ⟨i, rfl⟩⟩

omit [Finite ι] in
@[simp] theorem coe_gen (i : ι) : (gen (K := K) root i : L) = root i := rfl

omit [Finite ι] in
/-- The generators generate `M` as its own top field. -/
theorem adjoin_gen_eq_top :
    IntermediateField.adjoin K (Set.range (gen (K := K) root)) = ⊤ := by
  refine IntermediateField.map_injective (adjoin K (Set.range root)).val ?_
  have hmaptop : (⊤ : IntermediateField K (adjoin K (Set.range root))).map
      (adjoin K (Set.range root)).val = adjoin K (Set.range root) := by
    ext x
    simp only [IntermediateField.mem_map, IntermediateField.mem_top, true_and]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [IntermediateField.adjoin_map, hmaptop]
  congr 1
  rw [← Set.range_comp]
  rfl

omit [Finite ι] in
/-- The generator squares to its radicand (in `M`). -/
theorem gen_sq (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    gen (K := K) root i ^ 2 = algebraMap K (adjoin K (Set.range root)) (d i) := by
  apply Subtype.ext
  rw [IntermediateField.coe_pow, coe_gen, IntermediateField.coe_algebraMap_apply]
  exact hroot i

/-- `∏ᵢ (X² - dᵢ)` is nonzero. -/
theorem mqPoly_ne_zero : mqPoly d ≠ 0 := by
  rw [mqPoly, Finset.prod_ne_zero_iff]
  exact fun i _ => Polynomial.X_pow_sub_C_ne_zero (by norm_num) (d i)

/-- The defining polynomial splits over `M`. -/
theorem splits_mqPoly (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    ((mqPoly d).map (algebraMap K (adjoin K (Set.range root)))).Splits := by
  rw [mqPoly, Polynomial.map_prod]
  exact Polynomial.Splits.prod fun i _ => splits_X_sq_sub_C hroot i

omit [Finite ι] in
/-- Each generator is algebraic over `K` (it satisfies `X² - dᵢ`). -/
theorem isAlgebraic_gen (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) (i : ι) :
    IsAlgebraic K (gen (K := K) root i) :=
  ⟨X ^ 2 - C (d i), X_pow_sub_C_ne_zero (by norm_num) _, by
    rw [map_sub, map_pow, aeval_X, aeval_C, gen_sq hroot i, sub_self]⟩

/-- `M = K(rootᵢ : i)` is the splitting field of `∏ᵢ (X² - dᵢ)` over `K`. -/
theorem isSplittingField (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    (mqPoly d).IsSplittingField K (adjoin K (Set.range root)) where
  splits' := splits_mqPoly hroot
  adjoin_rootSet' := by
    letI := Fintype.ofFinite ι
    have hsub : Set.range (gen (K := K) root) ⊆
        (mqPoly d).rootSet (adjoin K (Set.range root)) := by
      rintro _ ⟨i, rfl⟩
      rw [Polynomial.mem_rootSet]
      refine ⟨mqPoly_ne_zero, ?_⟩
      rw [mqPoly, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [map_sub, map_pow, aeval_X, aeval_C, gen_sq hroot i, sub_self])
    have halg : ∀ x ∈ Set.range (gen (K := K) root), IsAlgebraic K x := by
      rintro _ ⟨i, rfl⟩; exact isAlgebraic_gen hroot i
    refine le_antisymm le_top ?_
    rw [← Algebra.adjoin_eq_top_of_intermediateField halg (adjoin_gen_eq_top (root := root))]
    exact Algebra.adjoin_mono hsub

/-- A multiquadratic field over a field of characteristic zero is Galois. -/
theorem isGalois [CharZero K] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    IsGalois K (adjoin K (Set.range root)) := by
  haveI := isSplittingField hroot
  haveI : Normal K (adjoin K (Set.range root)) := Normal.of_isSplittingField (mqPoly d)
  constructor

omit [Finite ι] in
/-- Every automorphism sends a generator to `± itself`. -/
theorem aut_gen_eq_or (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    σ (gen root i) = gen root i ∨ σ (gen root i) = -gen root i := by
  have h1 : (σ (gen root i)) ^ 2 = (gen root i) ^ 2 := by
    rw [← map_pow, gen_sq hroot, AlgEquiv.commutes, ← gen_sq hroot]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h1

variable (root) in
/-- The sign pattern of an automorphism: `0` where it fixes a generator, `1` where it negates. -/
noncomputable def signPattern
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) : ZMod 2 :=
  if σ (gen root i) = gen root i then 0 else 1

omit [Finite ι] in
/-- An automorphism acts on each generator by the corresponding sign. -/
theorem aut_gen_eq_signPattern (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι) :
    σ (gen root i) = (-1) ^ (signPattern root σ i).val * gen root i := by
  rw [signPattern]
  split_ifs with h
  · simp [h]
  · rcases aut_gen_eq_or hroot σ i with h' | h'
    · exact absurd h' h
    · simp [h', show ((1 : ZMod 2).val) = 1 from rfl]

omit [Finite ι] in
/-- Two automorphisms with the same sign pattern are equal. -/
theorem signPattern_injective (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i)) :
    Function.Injective (signPattern (K := K) root) := by
  intro σ τ h
  refine AlgEquiv.coe_algHom_injective
    (IntermediateField.algHom_ext_of_eq_adjoin (F := K)
      (S := adjoin K (Set.range root)) (s := Set.range root) rfl ?_)
  rintro x ⟨i, rfl⟩
  have hgen : σ (gen root i) = τ (gen root i) := by
    rw [aut_gen_eq_signPattern hroot, aut_gen_eq_signPattern hroot, h]
  exact hgen

omit [Finite ι] in
/-- A generator is not equal to its own negation (the radicand is a nonzero non-square). -/
theorem gen_ne_neg [CharZero K] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) (i : ι) :
    gen (K := K) root i ≠ -gen root i := by
  intro h
  have hcoe : root i = -root i := by simpa using congrArg Subtype.val h
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr (by norm_num)
  have hr0 : root i = 0 := by
    have h2 : (2 : L) * root i = 0 := by rw [two_mul]; nth_rewrite 1 [hcoe]; rw [neg_add_cancel]
    exact (mul_eq_zero.mp h2).resolve_left h2L
  have hd0 : d i = 0 := by
    have hh : algebraMap K L (d i) = 0 := by rw [← hroot i, hr0]; ring
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mp hh
  refine hindep {i} ⟨i, Finset.mem_singleton_self i⟩ ?_
  rw [Finset.prod_singleton, hd0]
  exact ⟨0, by ring⟩

omit [Finite ι] in
/-- The sign is `0` exactly where the automorphism fixes the generator. -/
theorem signPattern_eq_zero
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι)
    (h : σ (gen root i) = gen root i) : signPattern root σ i = 0 := by
  simp [signPattern, h]

omit [Finite ι] in
/-- The sign is `1` where the automorphism negates the generator (a nonzero non-square root). -/
theorem signPattern_eq_one [CharZero K] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (σ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) (i : ι)
    (h : σ (gen root i) = -gen root i) : signPattern root σ i = 1 := by
  have hne : gen (K := K) root i ≠ -gen root i := gen_ne_neg hroot hindep i
  have hni : σ (gen root i) ≠ gen root i := fun hh => hne (h ▸ hh.symm)
  simp [signPattern, hni]

omit [Finite ι] in
@[simp] theorem signPattern_one : signPattern (K := K) root (1 : adjoin K (Set.range root) ≃ₐ[K]
    adjoin K (Set.range root)) = 0 := by
  funext i; exact signPattern_eq_zero _ _ rfl

omit [Finite ι] in
/-- The sign pattern is additive: it is a group homomorphism to `ι → ℤ/2`. -/
theorem signPattern_mul [CharZero K] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (σ τ : adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) :
    signPattern root (σ * τ) = signPattern root σ + signPattern root τ := by
  funext i
  rw [Pi.add_apply]
  rcases aut_gen_eq_or hroot τ i with hτ | hτ <;> rcases aut_gen_eq_or hroot σ i with hσ | hσ
  · rw [signPattern_eq_zero _ _ (by rw [AlgEquiv.mul_apply, hτ, hσ]),
      signPattern_eq_zero _ _ hσ, signPattern_eq_zero _ _ hτ]; decide
  · rw [signPattern_eq_one hroot hindep _ _ (by rw [AlgEquiv.mul_apply, hτ, hσ]),
      signPattern_eq_one hroot hindep _ _ hσ, signPattern_eq_zero _ _ hτ]; decide
  · rw [signPattern_eq_one hroot hindep _ _ (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ]),
      signPattern_eq_zero _ _ hσ, signPattern_eq_one hroot hindep _ _ hτ]; decide
  · rw [signPattern_eq_zero _ _ (by rw [AlgEquiv.mul_apply, hτ, map_neg, hσ, neg_neg]),
      signPattern_eq_one hroot hindep _ _ hσ, signPattern_eq_one hroot hindep _ _ hτ]; decide

variable (root) in
/-- The Galois group of `M / K` maps to the sign patterns `(ℤ/2)ⁱ`. -/
noncomputable def signHom [CharZero K] (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) →* Multiplicative (ι → ZMod 2) where
  toFun σ := Multiplicative.ofAdd (signPattern root σ)
  map_one' := by simp
  map_mul' σ τ := by simp [signPattern_mul hroot hindep, ofAdd_add]

/-- **The Galois group of a multiquadratic field is `(ℤ/2)ⁿ`.** -/
noncomputable def galoisGroupEquiv [CharZero K]
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    (adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root)) ≃*
      Multiplicative (ι → ZMod 2) := by
  haveI := isSplittingField hroot
  haveI : FiniteDimensional K (adjoin K (Set.range root)) :=
    IsSplittingField.finiteDimensional _ (mqPoly d)
  haveI := isGalois hroot
  letI := Fintype.ofFinite ι
  refine MulEquiv.ofBijective (signHom root hroot hindep) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨signPattern_injective hroot, ?_⟩
  rw [← Nat.card_eq_fintype_card (α := adjoin K (Set.range root) ≃ₐ[K] _),
    IsGalois.card_aut_eq_finrank K (adjoin K (Set.range root)),
    finrank_adjoin_range hroot hindep]
  simp [ZMod.card]

end TauCeti.Multiquadratic
