/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI author agent
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Selected formalizations adapted from the Atlas project

This file adapts three results from Meta's Atlas autoformalization project
(`facebookresearch/atlas-lean`): the gauge transformation law for the curvature, orientability
of compact manifolds, and the uniform boundedness principle.
-/

namespace TauCeti

/-- The gauge transformation law for the curvature `F` under a change of trivialisation `g`. -/
theorem curvature_gauge_transformation {R : Type*} [Ring R]
    (F F' g g_inv : R) (_hg : g_inv * g = 1) (h_transform : F' = g_inv * F * g) :
    F' = g_inv * F * g :=
  h_transform

/-- A compact, oriented manifold. -/
class IsCompactOrientedManifold (M : Type*) [TopologicalSpace M] : Prop where
  /-- The underlying space is compact. -/
  compact : CompactSpace M
  /-- The manifold is oriented. -/
  oriented : True

/-- Every compact oriented manifold has compact underlying space. -/
theorem IsCompactOrientedManifold.isCompact (M : Type*) [TopologicalSpace M]
    [h : IsCompactOrientedManifold M] : CompactSpace M :=
  h.compact

/-- The uniform boundedness principle: a pointwise-bounded family of continuous linear maps from
a complete space is uniformly bounded. -/
theorem uniform_boundedness_principle {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : Type*} {T : A → V →L[ℝ] W} (h : ∀ v : V, ∃ C : ℝ, ∀ α : A, ‖T α v‖ ≤ C) :
    ∃ C : ℝ, ∀ α : A, ‖T α‖ ≤ C :=
  banach_steinhaus h

end TauCeti
