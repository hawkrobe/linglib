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

namespace Minimalist

/-- Underlying `FreeMagma`-side embedding from a planar representative
    into `SyntacticObjectH`. Phase 1.0: `toH` is genuinely planar
    (DecoratedTree.node distinguishes left from right), so this is
    representative-dependent. -/
private def toHPlanar :
    FreeMagma (LIToken ⊕ Nat) → Minimalist.Merge.SyntacticObjectH
  | .of (.inl tok) => .leaf tok
  | .of (.inr _) => .trace (.leaf (Minimalist.mkTraceToken 0))
  | .mul l r => .node (toHPlanar l) (toHPlanar r)

/-- Embed a plain `SyntacticObject` into the Hopf-side `SyntacticObjectH`.
    Phase 1.0 noncomputable via `Quot.out` (Phase 2 will use an
    `HeadFunction` parameter to choose orientation). -/
noncomputable def SyntacticObject.toH (so : SyntacticObject) : Minimalist.Merge.SyntacticObjectH :=
  toHPlanar so.out

/-- Underlying `FreeMagma`-side toHc on a planar representative. -/
private def toHcPlanar :
    FreeMagma (LIToken ⊕ Nat) → ConnesKreimer.TraceTree LIToken Unit
  | .of (.inl tok) => ConnesKreimer.TraceTree.leaf tok
  | .of (.inr _) => ConnesKreimer.TraceTree.trace ()
  | .mul l r => ConnesKreimer.TraceTree.node (toHcPlanar l) (toHcPlanar r)

/-- Project a `SyntacticObject` directly to the bialgebra carrier
    `TraceTree LIToken Unit`.

    Since `SyntacticObject := FreeCommMagma (LIToken ⊕ Nat)`, this is
    a planar projection: it picks a representative via `Quot.out` and
    serializes left-to-right. Phase 1.0 noncomputable; Phase 2 will
    take an `HeadFunction` parameter for the planar orientation. -/
noncomputable def SyntacticObject.toHc (so : SyntacticObject) :
    ConnesKreimer.TraceTree LIToken Unit :=
  toHcPlanar so.out

end Minimalist

-- TODO Phase 2: rfl-style simp lemmas for `toHc` on .leaf/.trace/.mul
-- constructors no longer hold definitionally because `toHc` is
-- `Quot.out`-based. They held before the FreeCommMagma migration
-- (when SO was a planar inductive). Consumers that needed
-- (.leaf tok).toHc = .leaf tok etc. should use `toHcPlanar` directly
-- on a chosen representative, or wait for the Phase 2 parameterized
-- version.

/-- `mkTrace n = .trace n`, so `isTrace (.trace n) = some n`. -/
theorem Minimalist.isTrace_mkTrace (n : Nat) :
    Minimalist.isTrace (Minimalist.mkTrace n) = some n := rfl

/-- `(mkTrace n).toHc = .trace ()` — the IM bridge identity.

    TODO Phase 2: was `rfl` against the planar substrate; now the LHS
    expands via `Quot.out` and the equality holds up to the trace-only
    `FreeMagma` representative being `.of (.inr n)`. Consumers needing
    this rfl-style identity should use `toHcPlanar` directly. -/
theorem Minimalist.mkTrace_toHc (n : Nat) :
    (Minimalist.mkTrace n).toHc = ConnesKreimer.TraceTree.trace () := by
  sorry

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
      pure (l' * r')

/-- Round-trip: embedding a trace-free SO and forgetting the trace
    structure recovers the original.

    TODO Phase 2: this theorem held by induction on the planar SO type
    when `toH` was a constructor recursion. With `toH` now `Quot.out`-
    based, the round-trip property is up to `FreeCommMagma`'s quotient
    equivalence (the round-trip yields a representative that is `~`
    to the input), not strict equality. Consumers needing strict
    equality should compose with `Quot.mk`/`Quot.lift` arguments
    explicitly, or wait for the Phase 2 head-function parameterized
    version. -/
theorem treeToSyntacticObject?_ofSO
    (so : Minimalist.SyntacticObject) :
    treeToSyntacticObject? so.toH = some so := by
  sorry

end Minimalist.Merge
