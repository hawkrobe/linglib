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
  | .node l r => .node l.toH r.toH

/-- Project a `SyntacticObject` directly to the bialgebra carrier
    `TraceTree LIToken Unit`. **Trace-aware** (Phase 7c.3): leaves
    detected by `Minimalist.isTrace` (sentinel id ≥ 10000, created via
    `mkTrace`) project to `.trace ()`, the algebraic trace constructor;
    all other leaves project to `.leaf tok`.

    This is the single boundary function consumers should use when
    entering the bialgebra layer. The trace-awareness is required for the
    Internal Merge bridge (Phase 7c.4): `Step.im(mover, n)(current)`
    produces a SyntacticObject containing `mkTrace n` markers, which must
    project to algebraic `.trace ()` constructors so that the resulting
    `TraceTree` is the deletion-quotient image (M-C-B Δ^d) under
    contraction-with-trace-replacement (M-C-B Δ^c) — see book p. 53
    eq. (1.4.2) and the `Merge/Action.lean §3` IM composition.

    For trace-free SOs (e.g., External Merge inputs), the trace branch is
    dead; the projection equals the older `so.toH.anon (fun _ => ())`
    formulation. The EM bridges (`mergeOp_emR/L_matches_Step`) are
    unaffected. -/
def Minimalist.SyntacticObject.toHc :
    Minimalist.SyntacticObject → ConnesKreimer.TraceTree LIToken Unit
  | .leaf tok =>
      match Minimalist.isTrace (.leaf tok) with
      | some _ => ConnesKreimer.TraceTree.trace ()
      | none   => ConnesKreimer.TraceTree.leaf tok
  | .node l r => ConnesKreimer.TraceTree.node l.toHc r.toHc

/-- `toHc` on a leaf splits on whether the leaf is a trace marker. -/
@[simp] theorem Minimalist.SyntacticObject.toHc_leaf (tok : LIToken) :
    (Minimalist.SyntacticObject.leaf tok).toHc =
      (match Minimalist.isTrace (.leaf tok) with
        | some _ => ConnesKreimer.TraceTree.trace ()
        | none   => ConnesKreimer.TraceTree.leaf tok) := rfl

/-- `toHc` recurses through `.node`. -/
@[simp] theorem Minimalist.SyntacticObject.toHc_node (l r : Minimalist.SyntacticObject) :
    (Minimalist.SyntacticObject.node l r).toHc =
      ConnesKreimer.TraceTree.node l.toHc r.toHc := rfl

/-- Public version of `SpellOut.isTrace_mkTrace` (which is private):
    the `mkTrace n` token has id `n + 10000 ≥ 10000`, so `isTrace`
    returns `some n`. Public so the IM bridge (Phase 7c.4) can use it
    when reducing `(mkTrace n).toHc` to `.trace ()`. -/
theorem Minimalist.isTrace_mkTrace (n : Nat) :
    Minimalist.isTrace (Minimalist.mkTrace n) = some n := by
  unfold Minimalist.mkTrace Minimalist.isTrace
  dsimp only []
  rw [if_pos (show n + 10000 ≥ 10000 by omega), Nat.add_sub_cancel]

-- TODO (load-bearing for Phase 7c.4): `(mkTrace n).toHc = .trace ()`.
-- The reduction is mathematically immediate (apply `toHc_leaf`, rewrite
-- via `isTrace_mkTrace`, take `some` branch of match), but the LIToken
-- token literal `⟨.simple .N [] (phonForm := ""), n + 10000⟩` causes a
-- `maxRecDepth` blow-up during elaboration. The IM bridge can compose
-- `toHc_leaf` + `isTrace_mkTrace` directly at the use site instead of
-- relying on this single-step lemma.
-- Deferred until Lean elaboration recursion is investigated, or the
-- LIToken structure is simplified.

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
  | node l r ihl ihr =>
    show treeToSyntacticObject? (.node l.toH r.toH) = _
    rw [treeToSyntacticObject?, ihl]
    rw [ihr]
    rfl

end Minimalist.Merge
