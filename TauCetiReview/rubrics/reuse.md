# Reuse and duplication

Does the PR reuse what exists, in Mathlib and TauCeti, instead of reinventing it? This angle
may `block` on outright duplication.

- Use recall to choose searches; use grep (under `.lake/packages/mathlib` and `TauCeti/`) to
  verify. Search conclusion heads, key constants, and adjacent-namespace APIs, not only
  names, and check generated, dual, additive, and order-dual variants before accepting a new
  parallel lemma.
- Verify every claim: name the existing `X` and show the grep hit. Never assert a duplicate
  you have not located.

## What to flag

- `block` only when the new declaration should be replaced directly by an existing one.
- `request_changes` for partial overlap: a result reprovable after a small rewrite, a special
  case of an existing general result, or a parallel API differing only by naming or notation.
  Point at the existing API, or ask for the equivalence.

## Verdict

- `block` on a declaration an existing one directly replaces.
- `request_changes` for reprovable results, special cases, or parallel APIs.
- `approve` when the PR adds genuinely new material and reuses existing API where it can.
