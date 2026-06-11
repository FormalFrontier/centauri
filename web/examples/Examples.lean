import TauCeti.AlgebraicTopology.UniversalCover.Deck.Connected
import TauCeti.Analysis.PDE.UniformEllipticity
import SubVerso.Examples
open SubVerso.Examples
open TauCeti TauCeti.PDE Matrix

%example deck_rigidity
/-- Two deck transformations of a connected covering space that agree at a single
point of the total space are equal — the rigidity that pins down the deck group. -/
theorem deck_rigidity {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} [PreconnectedSpace E] (hp : IsCoveringMap p)
    (φ ψ : Deck p) {e : E} (h : φ.1 e = ψ.1 e) : φ = ψ :=
  Deck.eq_of_apply_eq hp φ ψ h
%end

%example ellipticity_coercive
/-- On a uniformly elliptic region, the coefficient matrix induces a coercive
bilinear form at each interior point — the Lax–Milgram hypothesis, with explicit
ellipticity constants. -/
theorem ellipticity_coercive {X n : Type*} [Fintype n] [DecidableEq n]
    {Ω : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) :
    IsCoercive (matrixBilinearForm (a x)) :=
  h.isCoercive_matrixBilinearForm hx
%end
