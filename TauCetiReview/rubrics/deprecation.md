# Deprecation and backward compatibility

You judge how the PR treats existing public API, and how it survives Mathlib bumps. Uses
`request_changes`. Treat non-`private` declarations under `TauCeti/` as public unless marked
internal or experimental.

- Prefer adding to the API over changing it. A public declaration used outside the PR, or
  plausibly depended on downstream, that is renamed, restated, or removed leaves a
  `@[deprecated]` alias (with a date) pointing at the replacement. Flag a silent rename or
  removal. Do not require aliases for declarations documented as experimental or internal.
- Flag a same-name weakening of a statement, in or out of a bump. On a Mathlib bump, compare
  before-and-after statement strength, not just whether names still compile: results must not
  be dropped or quietly weakened to survive the bump.

## Verdict

- `request_changes` for a silent or unexplained break of public API, a missing deprecation
  alias, or a result weakened or dropped to compile.
- `approve` when API changes carry deprecations and bumps preserve the library's results.
