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
  handled by `Theories/Syntax/Minimalist/TraceInterpretation.lean`.

## Feature convergence

Before Spell-Out sends an SO to the interfaces, strong features must be
checked (see `Core.Checking.convergesAtSpellOut`). After Spell-Out,
covert operations on the LF branch check remaining –Interpretable features.
At LF, all –Interpretable features must be checked for the derivation to
converge (`Core.Checking.convergesAtLF`). See `Core.Economy.Admissibility`
for the full admissibility conditions.

@cite{chomsky-1995} @cite{heim-kratzer-1998}
-/

import Linglib.Theories.Syntax.Minimalist.Basic
import Linglib.Core.Tree

namespace Minimalist

open Core.Tree

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
    therefore depends on a planar representative of the underlying
    `FreeCommMagma`. Phase 1.0 placeholder via `Quot.out`; Phase 2 will
    replace with LCA-derived linearization parameterized by head
    directionality. -/
noncomputable def SyntacticObject.toLFTree (so : SyntacticObject) : Tree Unit String :=
  toLFTreePlanar so.out

/-- The PF branch of Spell-Out is `linearize` (defined in `Core/Basic.lean`):
    `linearize : SyntacticObject → List LIToken`.

    This alias makes the Y-model explicit. Noncomputable because
    `linearize` itself is (Phase 1.0 placeholder via `Quot.out`). -/
noncomputable abbrev SyntacticObject.toPF := @linearize

/-! ## Structural preservation — Phase 2 TODO

The previous structural preservation theorems (`toLFTree_leaf`,
`toLFTree_trace`, `toLFTree_node`, `toLFTree_merge` and the YModelDemo
end-to-end test) were written when `SyntacticObject` was a planar
inductive (`TraceTree`) — they relied on `rfl` against the planar
constructor pattern. After the nonplanar migration (Phase 1.0), `Tree`
remains planar (`.bin a b ≠ .bin b a`) while `SyntacticObject` is
nonplanar; `toLFTree` therefore goes through `Quot.out` (a noncomputable
representative choice). The preservation theorems are not provable by
`rfl` against an arbitrary representative.

**Phase 2 plan.** Replace `Quot.out`-based `toLFTree` with an
LCA-derived linearization parameterized by head directionality, then
restate preservation as "for the canonical planar representative
(per the LCA), the structural correspondence holds". The YModelDemo
end-to-end test will then be re-proved against that canonical form.

Keeping `toLFTree` itself as a noncomputable placeholder until that
work lands. The constructor on the LF side (`.leaf`/`.tr`/`.bin`) is
unchanged; the change is purely on the *order* preserved. -/

end Minimalist
