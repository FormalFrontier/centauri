# Scope: roadmap fit and single topic

One question: does this PR belong in Tau Ceti now, as a single coherent unit? This angle may
`block`, and should fairly readily.

## Roadmap fit

Tau Ceti implements `TauCetiRoadmap/`. A PR is in scope only if it advances a specific
roadmap target, or supplies a prerequisite a specific target needs. A valid claim identifies
a roadmap file and node or heading; read it to confirm.

- The dependency must be real and proximate: you can see the path from this material to the
  named target. "Might be useful for", or a long speculative chain, is not a prerequisite.
- Building what is missing is the point, so do not reject genuine prerequisite
  infrastructure. Reject material on no path to any target, or justified only as interesting;
  if it is off-roadmap but plausibly worthwhile, `block` and say a human must add it to the
  roadmap first.
- Judge the path, not its mathematical adequacy. If scope turns on whether a prerequisite is
  strong enough or non-vacuous, leave that to correctness.

## Single topic

`block` and ask for a split when the PR is more than one topic: an opportunistic refactor of
prerequisite material bundled with new work, or several unrelated targets at once. A single
refactor that is itself the topic is fine.

## Verdict

- `block` when there is no real path to a roadmap target, or the PR is not a single topic.
- `request_changes` when the path is genuine but the description fails to state it.
- `approve` when the PR advances one target, or one target's genuine prerequisite, as one
  unit.
