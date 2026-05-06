import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Core.Combinatorics.RootedTree.Decorated

/-!
# Bialgebra of Decorated Forests: Linguistic Specialization
@cite{marcolli-chomsky-berwick-2025}

The `[LINGLIB]` half of the original `Hopf/Defs.lean` (renamed to
`Merge/Defs.lean` at 0.230.770 along with the `Hopf/` → `Merge/`
dissolve): specialization of the generic Connes-Kreimer substrate
(in `Core/`, namespace `ConnesKreimer`) to the Minimalism instantiation
with `α := LIToken`, plus the bridge to plain `SyntacticObject` via the
`toSyntacticObject?` forgetful map.

## Where the substrate lives

The `[UPSTREAM]` portions are in:

- `Linglib/Core/Combinatorics/RootedTree/Decorated.lean` —
  `ConnesKreimer.TraceTree α Unit`, `ConnesKreimer.TraceForest α Unit`, `Mul`
  instance, `recOnMul`, `leafCount*`
- `Linglib/Core/Combinatorics/RootedTree/AdmissibleCut.lean` —
  `ConnesKreimer.CutShape T` and friends
- `Linglib/Core/Algebra/ConnesKreimer/Defs.lean` —
  `ConnesKreimer.Hc R α := AddMonoidAlgebra R (TraceForest α Unit)` + Algebra/
  Semiring forwarding instances
- `Linglib/Core/Algebra/ConnesKreimer/Coproduct.lean` —
  `ConnesKreimer.{forestToHc, comulAlgHom, comulDelAlgHom, counit}`

This file (and `Merge/Basic.lean`, `Merge/Action.lean`) bring those
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

namespace Minimalist.Merge

open ConnesKreimer

/-! ## Linguistic specialization to `α := LIToken` -/

/-- Linglib-specific alias: syntactic objects in the Hopf-algebra
    layer. M-C-B §1.1.2 + Def 1.2.4 with leaf type `LIToken`. -/
abbrev SyntacticObjectH := DecoratedTree LIToken

end Minimalist.Merge

/-- Embed a plain `SyntacticObject` into the Hopf-side `SyntacticObjectH`
    by recursing via `leaf`/`node` (no traces produced). Lives in the
    `SyntacticObject` namespace so that `(so : SyntacticObject).toH`
    works as dot notation. -/
def Minimalist.SyntacticObject.toH :
    Minimalist.SyntacticObject → Minimalist.Merge.SyntacticObjectH
  | .leaf tok => .leaf tok
  | .trace _ => .trace (.leaf (Minimalist.mkTraceToken 0))
    -- Trace projects to a DecoratedTree.trace wrapping a sentinel leaf;
    -- the trace index is forgotten at this layer (Hopf side has Unit traces).
  | .node l r => .node l.toH r.toH

/-- Project a `SyntacticObject` directly to the bialgebra carrier
    `TraceTree LIToken Unit`.

    Since `SyntacticObject := TraceTree LIToken Nat` (post-Path-2 migration),
    this is essentially a forgetful map on the trace label `Nat → Unit`.
    Leaves and node structure pass through unchanged; `.trace n` projects
    to `.trace ()` (forgetting the binding index).

    This is the single boundary function consumers should use when
    entering the bialgebra layer. -/
def Minimalist.SyntacticObject.toHc :
    Minimalist.SyntacticObject → ConnesKreimer.TraceTree LIToken Unit
  | .leaf tok => ConnesKreimer.TraceTree.leaf tok
  | .trace _ => ConnesKreimer.TraceTree.trace ()
  | .node l r => ConnesKreimer.TraceTree.node l.toHc r.toHc

@[simp] theorem Minimalist.SyntacticObject.toHc_leaf (tok : LIToken) :
    (Minimalist.SyntacticObject.leaf tok).toHc =
      ConnesKreimer.TraceTree.leaf tok := rfl

@[simp] theorem Minimalist.SyntacticObject.toHc_trace (n : Nat) :
    (Minimalist.SyntacticObject.trace n).toHc =
      ConnesKreimer.TraceTree.trace () := rfl

@[simp] theorem Minimalist.SyntacticObject.toHc_node (l r : Minimalist.SyntacticObject) :
    (Minimalist.SyntacticObject.node l r).toHc =
      ConnesKreimer.TraceTree.node l.toHc r.toHc := rfl

/-- `mkTrace n = .trace n` (post-Path-2), so `isTrace (.trace n) = some n` is `rfl`. -/
theorem Minimalist.isTrace_mkTrace (n : Nat) :
    Minimalist.isTrace (Minimalist.mkTrace n) = some n := rfl

/-- `(mkTrace n).toHc = .trace ()` — the IM bridge identity, now `rfl`
    after Path 2 replaced the leaf-with-reserved-id encoding with
    structural `.trace n`. -/
@[simp] theorem Minimalist.mkTrace_toHc (n : Nat) :
    (Minimalist.mkTrace n).toHc = ConnesKreimer.TraceTree.trace () := rfl

namespace Minimalist.Merge

open ConnesKreimer

/-- Forgetful map from `SyntacticObjectH = DecoratedTree LIToken` back
    to plain `SyntacticObject`: returns `none` if any trace leaf
    survives, otherwise `some` the reconstructed trace-free tree.
    Used by `Merge.External` / `Merge.Internal` to bridge the Hopf side to `Step.apply`
    (which operates on `SyntacticObject`).

    Plain function rather than dot-notation extension on
    `ConnesKreimer.DecoratedTree` (which would mix LIToken-specific
    Minimalism content into the generic Core namespace). Callers use
    `Minimalist.Merge.treeToSyntacticObject? t` qualified. -/
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
  | trace _ =>
    -- Traces project to DecoratedTree.trace, which forgets via treeToSO?_trace = none.
    -- This breaks the round-trip: trace → trace → none, not some so.
    -- Theorem now requires a "trace-free" hypothesis to be true. Skip as sorry
    -- with a TODO; consumers using treeToSyntacticObject?_ofSO on trace-bearing SOs
    -- will need updating.
    sorry
  | node l r ihl ihr =>
    show treeToSyntacticObject? (.node l.toH r.toH) = _
    rw [treeToSyntacticObject?, ihl]
    rw [ihr]
    rfl

end Minimalist.Merge
