/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Homotopy.Lifting

/-!
# The monodromy action on a fibre

Mathlib's covering-space API associates to a covering map `p : E → X` a monodromy functor
from the fundamental groupoid of `X` to types. This file packages the restriction of that
functor to a based loop as a permutation of the fibre over the basepoint, then records the
corresponding action of `π₁(X, x)` on that fibre.

This is a small prerequisite for the universal-covers roadmap: Stage 1 asks to pin the
composition convention in the comparison between deck transformations and the fundamental
group, and Stage 2 proposes the classification of connected covers through transitive
`π₁`-sets and Mathlib's `monodromyFunctor`.
-/

namespace TauCeti

open FundamentalGroup

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
variable (cov : IsCoveringMap p) (x : X)

/-- The monodromy of a based loop, as a permutation of the fibre over the basepoint. -/
noncomputable def monodromyPerm (γ : FundamentalGroup X x) : Equiv.Perm (p ⁻¹' {x}) :=
  Equiv.ofBijective (cov.monodromy γ.toPath) (cov.monodromy_bijective γ.toPath)

/-- The monodromy permutation is Mathlib's monodromy map on points of the fibre. -/
@[simp]
lemma monodromyPerm_apply (γ : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    monodromyPerm cov x γ e = cov.monodromy γ.toPath e :=
  rfl

/-- The identity loop acts by the identity permutation of the fibre. -/
@[simp]
lemma monodromyPerm_one : monodromyPerm cov x 1 = 1 := by
  ext e
  rw [monodromyPerm_apply]
  exact congr_arg Subtype.val (congr_fun cov.monodromy_refl e)

/-- Monodromy is compatible with the multiplication convention on Mathlib's fundamental group.

The fundamental group is the endomorphism group of the basepoint in the fundamental groupoid;
its multiplication is the endomorphism multiplication from category theory. With that
convention, monodromy is a monoid homomorphism to permutations of the fibre. -/
@[simp]
lemma monodromyPerm_mul (γ δ : FundamentalGroup X x) :
    monodromyPerm cov x (γ * δ) = monodromyPerm cov x γ * monodromyPerm cov x δ := by
  ext e
  rw [monodromyPerm_apply]
  exact congr_arg Subtype.val (cov.monodromy_trans_apply δ.toPath γ.toPath e)

/-- The inverse loop acts by the inverse monodromy permutation. -/
@[simp]
lemma monodromyPerm_inv (γ : FundamentalGroup X x) :
    monodromyPerm cov x γ⁻¹ = (monodromyPerm cov x γ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← monodromyPerm_mul, inv_mul_cancel, monodromyPerm_one]

/-- The monodromy representation of the fundamental group on the fibre over the basepoint. -/
noncomputable def monodromyPermHom : FundamentalGroup X x →* Equiv.Perm (p ⁻¹' {x}) where
  toFun := monodromyPerm cov x
  map_one' := monodromyPerm_one cov x
  map_mul' := monodromyPerm_mul cov x

/-- The monodromy homomorphism evaluates to the monodromy permutation. -/
@[simp]
lemma monodromyPermHom_apply (γ : FundamentalGroup X x) :
    monodromyPermHom cov x γ = monodromyPerm cov x γ :=
  rfl

/-- A covering map's fundamental group action on a fibre by monodromy.

Use this locally with `letI := cov.monodromyMulAction x` when treating the fibre as a
`π₁(X, x)`-set. It is a named definition rather than a global instance because the covering-map
proof `cov` is not inferable from the action type. -/
@[reducible]
noncomputable def monodromyMulAction : MulAction (FundamentalGroup X x) (p ⁻¹' {x}) :=
  MulAction.compHom _ (monodromyPermHom cov x)

/-- On points, the monodromy action is Mathlib's monodromy map. -/
lemma monodromy_smul_eq (γ : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    letI := monodromyMulAction cov x
    γ • e = cov.monodromy γ.toPath e :=
  rfl

/-- The monodromy action agrees with the monodromy permutation. -/
lemma monodromy_smul_eq_monodromyPerm (γ : FundamentalGroup X x) (e : p ⁻¹' {x}) :
    letI := monodromyMulAction cov x
    γ • e = monodromyPerm cov x γ e :=
  rfl

/-- If a loop in the total space projects to a loop in the base, its monodromy fixes the
starting point in the fibre. -/
@[simp]
lemma monodromyPerm_map_toPath (e : E) (γ : FundamentalGroup E e) :
    monodromyPerm cov (p e) (map ⟨p, cov.continuous⟩ e γ) ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  rw [monodromyPerm_apply]
  exact cov.monodromy_map γ.toPath

/-- The monodromy action fixes the starting point of a lifted loop. -/
lemma map_toPath_smul (e : E) (γ : FundamentalGroup E e) :
    letI := monodromyMulAction cov (p e)
    map ⟨p, cov.continuous⟩ e γ • (⟨e, by simp⟩ : p ⁻¹' {p e}) = ⟨e, by simp⟩ :=
  monodromyPerm_map_toPath cov e γ

/-- A projected loop from the total space fixes its starting point under monodromy. -/
lemma smul_eq_self_of_mem_map_range (e : E) {γ : FundamentalGroup X (p e)}
    (hγ : γ ∈ (map ⟨p, cov.continuous⟩ e).range) :
    letI := monodromyMulAction cov (p e)
    γ • (⟨e, by simp⟩ : p ⁻¹' {p e}) = ⟨e, by simp⟩ := by
  rcases hγ with ⟨δ, rfl⟩
  exact map_toPath_smul cov e δ

/-- The image of the fundamental group of the total space is contained in the stabilizer of the
chosen point in the fibre under the monodromy action. -/
lemma map_range_le_stabilizer (e : E) :
    letI := monodromyMulAction cov (p e)
    (map ⟨p, cov.continuous⟩ e).range ≤
      MulAction.stabilizer (FundamentalGroup X (p e)) (⟨e, by simp⟩ : p ⁻¹' {p e}) := by
  intro γ hγ
  letI := monodromyMulAction cov (p e)
  exact MulAction.mem_stabilizer_iff.mpr (smul_eq_self_of_mem_map_range cov e hγ)

end IsCoveringMap

end TauCeti
