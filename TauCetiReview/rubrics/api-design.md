# Public API

You judge the public interface the PR exposes. Uses `request_changes`.

- Expose the smallest surface useful to the named downstream target, not to hypothetical
  users; implementation helpers are `private`. Do not expose bodies to compensate for missing
  lemmas: keep bodies unexposed (no `@[expose]`) unless a consumer must unfold or compute,
  and ask for the missing lemma instead.
- A definition needs the API that characterizes it: introduction and elimination, the
  `*_def` and `mem_*_iff` restatements, interaction with the operations in scope, and the
  universal property where there is one. Try to use the new API without unfolding; if you
  cannot reach the intended target, demand the missing characteristic lemma.
- Require symmetric, dual, or parallel forms only when the file already develops both sides or
  the roadmap target needs them.
- Annotate `@[simp]` the normal-form lemmas and `@[grind]` the lemmas that should drive
  `grind`. Flag a characteristic lemma that should carry one and does not, and an annotation
  that would loop or fire wrongly.

## Verdict

- `request_changes` for an over-exposed surface, a body exposed for want of API, an
  incomplete characteristic API, or missing or wrong automation annotations.
- `approve` when the surface is minimal, bodies are hidden, and the characteristic API is
  complete and annotated.
