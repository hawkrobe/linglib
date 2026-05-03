import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Core.Combinatorics.RootedTree.Decorated

/-!
# Bialgebra of Decorated Forests: Linguistic Specialization
@cite{marcolli-chomsky-berwick-2025}

The `[LINGLIB]` half of the original `Hopf/Defs.lean`: specialization
of the generic Connes-Kreimer substrate (now in `Core/`) to the
Minimalism instantiation with `α := LIToken`, plus the bridge to plain
`SyntacticObject` via the `toSyntacticObject?` forgetful map.

## Where the substrate lives now

The `[UPSTREAM]` portions are hoisted to:

- `Linglib/Core/Combinatorics/RootedTree/Decorated.lean` —
  `DecoratedTree α`, `Forest α`, `Mul` instance, `recOnMul`, `leafCount*`
- `Linglib/Core/Algebra/ConnesKreimer/Defs.lean` —
  `Hc R α := AddMonoidAlgebra R (Forest α)` + Algebra/Semiring
  forwarding instances

This file re-exports them by `import` so existing `Minimalist.Hopf.X`
qualified references continue to resolve. The namespace remains
`Minimalist.Hopf` in the Core/ files for now — namespace rename is a
separate follow-up. See `scratch/mcb_stage1_plan.md` Stage 0.5.

## Linguistic specialization

`SyntacticObjectH := DecoratedTree LIToken` is the Minimalism-side
alias (M-C-B §1.1.2 + Def 1.2.4 with leaf type `LIToken`). The
forgetful maps `SyntacticObject.toH` (lossless embed of plain SO into
the Hopf side) and `DecoratedTree.toSyntacticObject?` (option-valued
projection back, returning `none` if any trace leaf survives) bridge
the two encodings.

The `toSyntacticObject?_ofSO` round-trip theorem confirms
trace-free SOs survive embedding-then-projection.
-/

namespace Minimalist.Hopf

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

/-- Forgetful map from `SyntacticObjectH = DecoratedTree LIToken` back
    to plain `SyntacticObject`: returns `none` if any trace leaf
    survives, otherwise `some` the reconstructed trace-free tree.
    Used by `MergeAction.lean` to bridge the Hopf side to `Step.apply`
    (which operates on `SyntacticObject`).

    Lives on `DecoratedTree` rather than `SyntacticObjectH` so that
    dot notation `(l : SyntacticObjectH).toSyntacticObject?` resolves
    correctly (Lean's dot notation looks at the head type, which is
    `DecoratedTree` after unfolding the `SyntacticObjectH` abbrev). -/
def DecoratedTree.toSyntacticObject? :
    DecoratedTree LIToken → Option Minimalist.SyntacticObject
  | .leaf tok => some (.leaf tok)
  | .trace _  => none
  | .node l r => do
      let l' ← DecoratedTree.toSyntacticObject? l
      let r' ← DecoratedTree.toSyntacticObject? r
      pure (.node l' r')

/-- Round-trip: embedding a trace-free SO and forgetting the trace
    structure recovers the original. -/
@[simp] theorem DecoratedTree.toSyntacticObject?_ofSO
    (so : Minimalist.SyntacticObject) :
    DecoratedTree.toSyntacticObject? so.toH = some so := by
  induction so with
  | leaf _ => rfl
  | node l r ihl ihr =>
    show DecoratedTree.toSyntacticObject? (.node l.toH r.toH) = _
    rw [DecoratedTree.toSyntacticObject?, ihl]
    rw [ihr]
    rfl

end Minimalist.Hopf
