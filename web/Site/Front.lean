import VersoBlog
open Verso Genre Blog

#doc (Page) "Tau Ceti" =>

Deck-transformation rigidity, from the universal-covers development: two deck
transformations of a connected covering space that agree at a single point are equal.

```
theorem eq_of_apply_eq [PreconnectedSpace E] (hp : IsCoveringMap p)
    (φ ψ : Deck p) {e : E} (h : φ.1 e = ψ.1 e) : φ = ψ
```

The full statement and proof live [in the library](https://github.com/FormalFrontier/TauCeti/blob/main/TauCeti/AlgebraicTopology/UniversalCover/Deck/Connected.lean), where Tau Ceti's CI checks them on every change.
