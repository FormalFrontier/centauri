# Placement and imports

Where does the new material live, and what does it import? Uses `request_changes`. File
length is linter-enforced; do not re-report it. `shake` is not yet enforced, so report only
imports whose wrongness is evident from the diff or the dependency topic.

## Placement

- Each declaration belongs in its canonical home: the file whose topic, level, and
  dependencies fit it, near the definition or result it elaborates. If it belongs in an
  earlier `TauCeti/` file, or depends on no later theory and is broadly useful, ask to move it
  there.
- Reject generic placement for declarations whose hypotheses or names are roadmap-specific:
  do not let roadmap-specific lemmas masquerade as reusable by living in a generic file.

## Imports

- Import directly what a file uses. Flag an import whose wrongness is evident: unused, or a
  broad `import Mathlib` where specific modules would do.

## Verdict

- `request_changes` for a declaration in the wrong home, material that belongs in an earlier
  file, roadmap-specific material hidden in a generic file, or an evidently wrong import.
- `approve` when each declaration is in its natural place with direct imports.
