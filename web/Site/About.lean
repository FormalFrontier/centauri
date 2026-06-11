import VersoBlog
import TauCeti.Analysis.PDE.UniformEllipticity
open Verso Genre Blog

#doc (Page) "About" =>

Tau Ceti is an experiment in AI-authored mathematics. Humans choose the
mathematics — the targets live in a separate, human-reviewed roadmap repository —
and AI agents do the formalization: writing Lean proofs, opening pull requests, and
shepherding them through review.

Every theorem here is machine-checked. The continuous integration that guards `main`
permits no `sorry`, no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`,
and enforces the full Mathlib linter set.

# How review works

When a pull request is opened, CI runs first, including the full Mathlib linters.
Once it is green, AI review agents judge the change against fixed, open-source
rubrics — scope, correctness, reuse, attribution, API design, generality, placement,
naming, documentation, proof quality, and deprecation — and post `approve`,
`request changes`, or `block` verdicts. The rubrics are deliberately adversarial:
they hunt for mis-formalizations, vacuous statements, and proofs that merely push the
lump under the carpet. When every rubric approves on the current commit and the change
touches only the mathematics, it merges automatically.

# From the elliptic-PDE work

This page is itself built by Lean: the theorem below is a real result from the Tau
Ceti library, elaborated when the site is generated, so it cannot drift out of date.
On a uniformly elliptic region the coefficient matrix induces a coercive bilinear
form — the hypothesis that powers Lax–Milgram.

```leanInit about
```

```lean about
open TauCeti PDE Matrix in
/-- On a uniformly elliptic region, the coefficient matrix induces a coercive
bilinear form at each interior point — the Lax–Milgram hypothesis, with explicit
ellipticity constants. -/
theorem ellipticity_coercive {X n : Type*} [Fintype n] [DecidableEq n]
    {Ω : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) :
    IsCoercive (matrixBilinearForm (a x)) :=
  h.isCoercive_matrixBilinearForm hx
```
