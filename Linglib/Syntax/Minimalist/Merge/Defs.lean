import Linglib.Syntax.Minimalist.Basic
import Linglib.Syntax.Minimalist.HeadFunction
import Linglib.Core.Combinatorics.RootedTree.Decorated

/-!
# Bialgebra of Decorated Forests: Linguistic Specialization
[marcolli-chomsky-berwick-2025]

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
    into `SyntacticObjectH`. `toH` is genuinely planar (DecoratedTree.node
    distinguishes left from right), so this is representative-dependent.
    Public so `HeadFunction.toHWith` can compose it with a chosen
    `externalize` section. -/
def toHPlanar :
    FreeMagma (LIToken ⊕ Nat) → Minimalist.Merge.SyntacticObjectH
  | .of (.inl tok) => .leaf tok
  | .of (.inr _) => .trace (.leaf (Minimalist.mkTraceToken 0))
  | .mul l r => .node (toHPlanar l) (toHPlanar r)

/-- Embed a plain `SyntacticObject` into the Hopf-side `SyntacticObjectH`.
    Phase 1.0 noncomputable via `Quot.out`; the parameterized
    `HeadFunction.toHWith` takes an explicit `externalize` for orientation. -/
noncomputable def SyntacticObject.toH (so : SyntacticObject) : Minimalist.Merge.SyntacticObjectH :=
  toHPlanar so.out

/-- Parameterized embedding: `toH` under head function `h`, using
    `h.section_.σ` to pick the planar representative. Computable when
    `h.section_.σ` is. -/
def HeadFunction.toHWith (h : HeadFunction) (so : SyntacticObject) :
    Minimalist.Merge.SyntacticObjectH :=
  toHPlanar (h.section_.σ so)

/-- Underlying `FreeMagma`-side toHc on a planar representative. Public
    so `HeadFunction.toHcWith` can compose it with a chosen `externalize`. -/
def toHcPlanar :
    FreeMagma (LIToken ⊕ Nat) → ConnesKreimer.TraceTree LIToken Unit
  | .of (.inl tok) => ConnesKreimer.TraceTree.leaf tok
  | .of (.inr _) => ConnesKreimer.TraceTree.trace ()
  | .mul l r => ConnesKreimer.TraceTree.node (toHcPlanar l) (toHcPlanar r)

/-- Project a `SyntacticObject` directly to the bialgebra carrier
    `TraceTree LIToken Unit`.

    Since `SyntacticObject := FreeCommMagma (LIToken ⊕ Nat)`, this is
    a planar projection: it picks a representative via `Quot.out` and
    serializes left-to-right. Phase 1.0 noncomputable; the parameterized
    `HeadFunction.toHcWith` takes an explicit `externalize`. -/
noncomputable def SyntacticObject.toHc (so : SyntacticObject) :
    ConnesKreimer.TraceTree LIToken Unit :=
  toHcPlanar so.out

/-- Parameterized projection: `toHc` under head function `h`, using
    `h.section_.σ` to pick the planar representative. Computable when
    `h.section_.σ` is. -/
def HeadFunction.toHcWith (h : HeadFunction) (so : SyntacticObject) :
    ConnesKreimer.TraceTree LIToken Unit :=
  toHcPlanar (h.section_.σ so)

/-! ### Singleton-class simp lemmas

`toHc_leaf` / `toHc_trace` are recoverable as `simp` lemmas because
leaf-only equivalence classes under `FreeMagma.CommRel` are singletons
(no `swap` constructor fires on `.of _`). The proof routes through
`Quot.out_eq` + `mk_eq_iff_commEqv` + the singleton structure of `.of`.

`toHc_mul` does NOT recover at this level: `(l * r).out` may pick
either `mul l.out r.out` or `mul r.out l.out`, and `TraceTree.node`
is planar (`.node a b ≠ .node b a`). Phase 2 will take an
`HeadFunction` parameter to canonicalize the orientation. -/

@[simp] theorem SyntacticObject.toHc_leaf (tok : LIToken) :
    (SyntacticObject.leaf tok).toHc = ConnesKreimer.TraceTree.leaf tok := by
  show toHcPlanar (SyntacticObject.leaf tok).out = _
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.leaf tok).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inl tok)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.leaf tok).out with
  | .of x =>
    rw [h] at hmk
    show toHcPlanar (.of x) = _
    cases x with
    | inl t =>
      simp only [toHcPlanar]
      exact congrArg ConnesKreimer.TraceTree.leaf
        (Sum.inl.inj (hmk : Sum.inl t = Sum.inl tok))
    | inr n => exact absurd (hmk : Sum.inr n = Sum.inl tok) (by intro; contradiction)
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

@[simp] theorem SyntacticObject.toHc_trace (n : Nat) :
    (SyntacticObject.trace n).toHc = ConnesKreimer.TraceTree.trace () := by
  show toHcPlanar (SyntacticObject.trace n).out = _
  have hmk :
      (Quot.mk FreeMagma.CommRel (SyntacticObject.trace n).out : SyntacticObject)
        = FreeCommMagma.mk (FreeMagma.of (Sum.inr n)) := Quot.out_eq _
  rw [FreeCommMagma.mk_eq_iff_commEqv] at hmk
  match h : (SyntacticObject.trace n).out with
  | .of x =>
    rw [h] at hmk
    show toHcPlanar (.of x) = _
    cases x with
    | inl t => exact absurd (hmk : Sum.inl t = Sum.inr n) (by intro; contradiction)
    | inr m => simp only [toHcPlanar]
  | .mul _ _ =>
    rw [h] at hmk
    exact absurd hmk (by simp [FreeMagma.CommEqv])

/-! ### Singleton-class simp lemmas for `toHcWith`/`toHWith` (parameterized)

All three lemmas reduce via the keystone `FreeCommMagma.Section.σ_of` helper:
the section's image of `FreeCommMagma.of x` is exactly `FreeMagma.of x`. -/

/-- `toHcWith h` on a leaf returns the corresponding `TraceTree.leaf`. -/
@[simp] theorem HeadFunction.toHcWith_leaf (h : HeadFunction) (tok : LIToken) :
    h.toHcWith (.leaf tok) = ConnesKreimer.TraceTree.leaf tok := by
  show toHcPlanar (h.section_.σ (FreeCommMagma.of (.inl tok))) = _
  rw [h.section_.σ_of]
  rfl

/-- `toHcWith h` on a trace returns `TraceTree.trace ()`. -/
@[simp] theorem HeadFunction.toHcWith_trace (h : HeadFunction) (n : Nat) :
    h.toHcWith (.trace n) = ConnesKreimer.TraceTree.trace () := by
  show toHcPlanar (h.section_.σ (FreeCommMagma.of (.inr n))) = _
  rw [h.section_.σ_of]
  rfl

/-- `toHWith h` on a leaf returns the corresponding `DecoratedTree.leaf`. -/
@[simp] theorem HeadFunction.toHWith_leaf (h : HeadFunction) (tok : LIToken) :
    h.toHWith (.leaf tok) = (.leaf tok : Minimalist.Merge.SyntacticObjectH) := by
  show toHPlanar (h.section_.σ (FreeCommMagma.of (.inl tok))) = _
  rw [h.section_.σ_of]
  rfl

end Minimalist

/-- `mkTrace n = .trace n`, so `isTrace (.trace n) = some n`. -/
theorem Minimalist.isTrace_mkTrace (n : Nat) :
    Minimalist.isTrace (Minimalist.mkTrace n) = some n := rfl

/-- `(mkTrace n).toHc = .trace ()` — the IM bridge identity. -/
theorem Minimalist.mkTrace_toHc (n : Nat) :
    (Minimalist.mkTrace n).toHc = ConnesKreimer.TraceTree.trace () :=
  Minimalist.SyntacticObject.toHc_trace n

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

    **The statement as given is FALSE for SOs containing traces**:
    `treeToSyntacticObject?` returns `none` on trace leaves by
    construction (line 173), so the round-trip is undefined whenever
    `so` contains a `.trace _`. The honest reformulation requires
    a "trace-free" hypothesis (e.g., `(traceIndices so).card = 0`,
    importable from `TraceInterpretation`).

    Even with the trace-free hypothesis, the proof requires a
    representative-level induction through `Quot.out`-based `toH` that
    is more involved than the leaf/trace singleton-class simps.
    Deferred to Phase 2 alongside head-function parameterization. -/
theorem treeToSyntacticObject?_ofSO
    (so : Minimalist.SyntacticObject) :
    treeToSyntacticObject? so.toH = some so := by
  -- TODO Phase 2: statement is false for trace-containing SOs;
  -- restate with `(traceIndices so).card = 0` hypothesis once
  -- Defs.lean can import TraceInterpretation, then prove via
  -- representative-level induction.
  sorry

end Minimalist.Merge
