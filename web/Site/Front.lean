import VersoBlog
import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected
open Verso Genre Blog

#doc (Page) "Tau Ceti" =>

```leanInit maths
```

```lean maths
open TauCeti in
/-- Two deck transformations of a connected covering space that agree at a single
point of the total space are equal — the rigidity that pins down the deck group. -/
theorem deck_rigidity {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} [PreconnectedSpace E] (hp : IsCoveringMap p)
    (φ ψ : Deck p) {e : E} (h : φ.1 e = ψ.1 e) : φ = ψ :=
  Deck.eq_of_apply_eq hp φ ψ h
```
