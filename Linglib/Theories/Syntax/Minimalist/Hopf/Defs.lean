import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Core.Combinatorics.RootedTree.Decorated

/-!
# Bialgebra of Decorated Forests: Linguistic Specialization
@cite{marcolli-chomsky-berwick-2025}

The `[LINGLIB]` half of the original `Hopf/Defs.lean`: specialization
of the generic Connes-Kreimer substrate (in `Core/`, namespace
`ConnesKreimer`) to the Minimalism instantiation with `α := LIToken`,
plus the bridge to plain `SyntacticObject` via the `toSyntacticObject?`
forgetful map.

## Where the substrate lives

The `[UPSTREAM]` portions are in:

- `Linglib/Core/Combinatorics/RootedTree/Decorated.lean` —
  `ConnesKreimer.DecoratedTree α`, `ConnesKreimer.Forest α`, `Mul`
  instance, `recOnMul`, `leafCount*`
- `Linglib/Core/Combinatorics/RootedTree/AdmissibleCut.lean` —
  `ConnesKreimer.CutShape T` and friends
- `Linglib/Core/Algebra/ConnesKreimer/Defs.lean` —
  `ConnesKreimer.Hc R α := AddMonoidAlgebra R (Forest α)` + Algebra/
  Semiring forwarding instances
- `Linglib/Core/Algebra/ConnesKreimer/Coproduct.lean` —
  `ConnesKreimer.{forestToHc, comulAlgHom, comulDelAlgHom, counit}`

This file (and `Hopf/Merge.lean`, `Hopf/MergeAction.lean`) bring those
into scope via `open ConnesKreimer`.

## Linguistic specialization

`SyntacticObjectH := DecoratedTree LIToken` is the Minimalism-side
alias (M-C-B §1.1.2 + Def 1.2.4 with leaf type `LIToken`). The
forgetful maps `SyntacticObject.toH` (lossless embed of plain SO into
the Hopf side) and `treeToSyntacticObject?` (option-valued projection
back, returning `none` if any trace leaf survives) bridge the two
encodings.

The `treeToSyntacticObject?_ofSO` round-trip theorem confirms
trace-free SOs survive embedding-then-projection.
-/

namespace Minimalist.Hopf

open ConnesKreimer

/-! ## Linguistic specialization to `α := LIToken` -/

/-- Linglib-specific alias: syntactic objects in the Hopf-algebra
    layer. M-C-B §1.1.2 + Def 1.2.4 with leaf type `LIToken`. -/
abbrev SyntacticObjectH := DecoratedTree LIToken

end Minimalist.Hopf

/-- Embed a plain `SyntacticObject` into the Hopf-side `SyntacticObjectH`
    by recursing via `leaf`/`node` (no traces produced). Lives in the
    `SyntacticObject` namespace so that `(so : SyntacticObject).toH`
    works as dot notation. -/
def Minimalist.SyntacticObject.toH :
    Minimalist.SyntacticObject → Minimalist.Hopf.SyntacticObjectH
  | .leaf tok => .leaf tok
  | .node l r => .node l.toH r.toH

namespace Minimalist.Hopf

open ConnesKreimer

/-- Forgetful map from `SyntacticObjectH = DecoratedTree LIToken` back
    to plain `SyntacticObject`: returns `none` if any trace leaf
    survives, otherwise `some` the reconstructed trace-free tree.
    Used by `MergeAction.lean` to bridge the Hopf side to `Step.apply`
    (which operates on `SyntacticObject`).

    Plain function rather than dot-notation extension on
    `ConnesKreimer.DecoratedTree` (which would mix LIToken-specific
    Minimalism content into the generic Core namespace). Callers use
    `Minimalist.Hopf.treeToSyntacticObject? t` qualified. -/
def treeToSyntacticObject? :
    DecoratedTree LIToken → Option Minimalist.SyntacticObject
  | .leaf tok => some (.leaf tok)
  | .trace _  => none
  | .node l r => do
      let l' ← treeToSyntacticObject? l
      let r' ← treeToSyntacticObject? r
      pure (.node l' r')

/-- Round-trip: embedding a trace-free SO and forgetting the trace
    structure recovers the original. -/
@[simp] theorem treeToSyntacticObject?_ofSO
    (so : Minimalist.SyntacticObject) :
    treeToSyntacticObject? so.toH = some so := by
  induction so with
  | leaf _ => rfl
  | node l r ihl ihr =>
    show treeToSyntacticObject? (.node l.toH r.toH) = _
    rw [treeToSyntacticObject?, ihl]
    rw [ihr]
    rfl

end Minimalist.Hopf
