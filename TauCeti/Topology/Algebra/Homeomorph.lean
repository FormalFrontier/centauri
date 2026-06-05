/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The tautological action of a homeomorphism group

The homeomorphism group `Y ≃ₜ Y` acts on `Y` by evaluation. This generalizes
`Equiv.Perm.applyMulAction` to the topological setting, and records that the action is
faithful and continuous in the second variable.

These instances are vendored from the Mathlib draft
[#40135](https://github.com/leanprover-community/mathlib4/pull/40135) by Kim Morrison
(originally additions to `Mathlib/Topology/Algebra/ConstMulAction.lean`), since they are not
yet in the pinned Mathlib.

This is provisional compatibility API. When the pinned Mathlib provides the upstream
declarations, Tau Ceti should replace these implementations with deprecated aliases where
possible, rather than silently removing names that downstream files may have imported.
-/

namespace TauCeti

variable {Y : Type*} [TopologicalSpace Y]

/-- The tautological action by `Y ≃ₜ Y` on `Y`.

This generalizes `Equiv.Perm.applyMulAction`. -/
instance Homeomorph.applyMulAction : MulAction (Y ≃ₜ Y) Y where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological scalar action of a self-homeomorphism is evaluation. -/
@[simp]
protected theorem Homeomorph.smul_def (f : Y ≃ₜ Y) (x : Y) : f • x = f x := rfl

/-- `Homeomorph.applyMulAction` is faithful. -/
instance Homeomorph.applyFaithfulSMul : FaithfulSMul (Y ≃ₜ Y) Y := ⟨Homeomorph.ext⟩

/-- Vendored compatibility instance: `Homeomorph.applyMulAction` is continuous in the second
variable. -/
instance Homeomorph.continuousConstSMul : ContinuousConstSMul (Y ≃ₜ Y) Y :=
  ⟨fun h ↦ h.continuous⟩

end TauCeti
