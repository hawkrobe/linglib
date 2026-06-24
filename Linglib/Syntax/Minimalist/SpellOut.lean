/-
# Spell-Out: Narrow Syntax → LF Tree

Spell-Out sends the output of narrow syntax (a `SyntacticObject` built by
Merge) to the interfaces for interpretation:

- **LF** (Logical Form): `toLFTree` maps an SO to a `Tree Unit String` for
  compositional semantic interpretation via `Semantics.Composition.Tree.interp`
- **PF** (Phonological Form): `linearize` (in `Core/Basic.lean`) maps an SO
  to the left-to-right sequence of leaf tokens

```
                    ┌→ LF: toLFTree → interp → ⟦meaning⟧
Merge → SO → Spell-Out
                    └→ PF: linearize → [word₁, word₂, ...]
```

## What a syntactician needs to know

- `SyntacticObject` = narrow syntax output. Binary trees built by Merge.
  Leaves are `LIToken`s (lexical items with features). No linear order yet.
- `Tree Unit String` = LF tree. What `interp` reads. Terminals are strings
  (phonological forms), traces are indexed variables, binders are λ-nodes.
- `toLFTree` converts the first into the second. Traces (id ≥ 10000) become
  trace nodes; everything else becomes a terminal labeled by its phonForm.
- Predicate Abstraction (λ-binding at landing sites) is a separate step
  handled by `Syntax/Minimalist/TraceInterpretation.lean`.

## Feature convergence

Before Spell-Out sends an SO to the interfaces, strong features must be
checked (see `Core.Checking.convergesAtSpellOut`). After Spell-Out,
covert operations on the LF branch check remaining –Interpretable features.
At LF, all –Interpretable features must be checked for the derivation to
converge (`Core.Checking.convergesAtLF`). See `Core.Economy.Admissibility`
for the full admissibility conditions.

[chomsky-1995] [heim-kratzer-1998]
-/

import Linglib.Syntax.Minimalist.Basic
import Linglib.Syntax.Minimalist.HeadFunction
import Linglib.Syntax.Minimalist.Selection
import Linglib.Syntax.Tree.Cat

namespace Minimalist

open Syntax

/-! ## LF branch of Spell-Out -/

/-- Underlying LF transfer on a planar `FreeMagma` representative. -/
private def toLFTreePlanar : FreeMagma (LIToken ⊕ Nat) → Tree Unit String
  | .of (.inl tok) => .leaf tok.phonForm
  | .of (.inr n) => .tr n
  | .mul a b => .bin (toLFTreePlanar a) (toLFTreePlanar b)

/-- Convert a narrow-syntax `SyntacticObject` to an LF tree for
    compositional interpretation.

    - Leaf tokens → `Tree.leaf phonForm` (terminal nodes keyed by
      phonological form, which `interp` uses for lexical lookup)
    - Traces (id ≥ 10000) → `Tree.tr n` (indexed trace nodes, which
      `interp` evaluates as `g(n)` under assignment `g`)
    - Binary nodes → `Tree.bin left right` (preserving structure)

    `Tree` is planar (`.bin a b ≠ .bin b a` in general); this transfer
    therefore depends on a planar representative. We use the **selection-induced**
    head-initial embedding (`selLinearize .initial`,
    [marcolli-chomsky-berwick-2025] Lemma 1.13.5) — computable, selection-faithful,
    superseding the arbitrary `Quot.out` representative. -/
def SyntacticObject.toLFTree (so : SyntacticObject) : Tree Unit String :=
  toLFTreePlanar (selLinearize .initial so)

/-- The PF branch of Spell-Out: the leaf tokens of `so` in the left-to-right
    order of the **selection-induced** head-initial embedding (`selLinearize
    .initial`, [marcolli-chomsky-berwick-2025] Lemma 1.13.5) — computable,
    selection-faithful. For derivation-based PF that recovers movement order,
    use `Derivation.surfaceTokens` instead. -/
def SyntacticObject.toPF (so : SyntacticObject) : List LIToken :=
  linearizePlanar (selLinearize .initial so)

/-! ## Structural preservation — re-proof TODO

`toLFTree`/`toPF` now linearize through the **computable** selection-induced
embedding `selLinearize .initial` (no `Quot.out`). The previous structural
preservation theorems (`toLFTree_leaf`/`_trace`/`_node`/`_merge` and the
YModelDemo end-to-end test) were deleted in the nonplanar migration — they
had relied on `rfl` against the old planar `TraceTree` constructor pattern.
They can now be re-proven against the canonical `selLinearize` representative;
that re-proof remains open. The LF-side constructors (`.leaf`/`.tr`/`.bin`)
are unchanged. -/

end Minimalist
