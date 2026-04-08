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
  handled by `Interfaces/SyntaxSemantics/Minimalism/Interface.lean`.

@cite{chomsky-1995} @cite{heim-kratzer-1998}
-/

import Linglib.Theories.Syntax.Minimalism.Core.Basic
import Linglib.Core.Tree

namespace Minimalism

open Core.Tree

/-! ## LF branch of Spell-Out -/

/-- Convert a narrow-syntax `SyntacticObject` to an LF tree for
    compositional interpretation.

    - Leaf tokens → `Tree.leaf phonForm` (terminal nodes keyed by
      phonological form, which `interp` uses for lexical lookup)
    - Traces (id ≥ 10000) → `Tree.tr n` (indexed trace nodes, which
      `interp` evaluates as `g(n)` under assignment `g`)
    - Binary nodes → `Tree.bin left right` (preserving structure) -/
def SyntacticObject.toLFTree : SyntacticObject → Tree Unit String
  | .leaf tok =>
    match isTrace (.leaf tok) with
    | some n => .tr n
    | none   => .leaf tok.phonForm
  | .node a b => .bin a.toLFTree b.toLFTree

/-- The PF branch of Spell-Out is `linearize` (defined in `Core/Basic.lean`):
    `linearize : SyntacticObject → List LIToken`.

    This alias makes the Y-model explicit. -/
abbrev SyntacticObject.toPF := @linearize

/-! ## Structural preservation

`toLFTree` preserves tree geometry: the shape of the LF tree matches
the shape of the narrow-syntax SO (modulo trace nodes, which change
from `leaf` to `trace`). -/

/-- `isTrace` on a non-trace leaf returns `none`. -/
private theorem isTrace_leaf_none (tok : LIToken) (h : tok.id < 10000) :
    isTrace (SyntacticObject.leaf tok) = none := by
  unfold isTrace; dsimp only []
  rw [if_neg (show ¬ tok.id ≥ 10000 by omega)]

/-- `isTrace` on a trace returns `some n`. -/
private theorem isTrace_mkTrace (n : Nat) :
    isTrace (mkTrace n) = some n := by
  unfold mkTrace isTrace; dsimp only []
  rw [if_pos (show n + 10000 ≥ 10000 by omega)]
  simp only [Nat.add_sub_cancel]

/-- `toLFTree` on a non-trace leaf produces a terminal node. -/
theorem toLFTree_leaf (tok : LIToken) (h : tok.id < 10000) :
    (SyntacticObject.leaf tok).toLFTree = Tree.leaf tok.phonForm := by
  show (match isTrace (SyntacticObject.leaf tok) with
    | some n => Tree.tr n | none => Tree.leaf tok.phonForm) = _
  rw [isTrace_leaf_none tok h]

/-- `toLFTree` on a trace produces a trace node. -/
theorem toLFTree_trace (n : Nat) :
    (mkTrace n).toLFTree = Tree.tr n := by
  unfold SyntacticObject.toLFTree mkTrace; dsimp only []
  rw [show isTrace (SyntacticObject.leaf
    ⟨LexicalItem.simple .N [], n + 10000⟩) = some n from isTrace_mkTrace n]

/-- `toLFTree` on a binary node produces a binary node. -/
theorem toLFTree_node (a b : SyntacticObject) :
    (SyntacticObject.node a b).toLFTree = .bin a.toLFTree b.toLFTree := by
  rfl

/-- `toLFTree` on Merge = binary node of the LF-transferred children. -/
theorem toLFTree_merge (x y : SyntacticObject) :
    (merge x y).toLFTree = .bin x.toLFTree y.toLFTree := by
  rfl

/-! ## End-to-end derivation: the Y-model pipeline

Demonstrate the full narrow-syntax → Spell-Out → LF/PF path for a
minimal VP "sat the cat", proving the Y-model actually composes:

```
                    ┌→ LF: .bin (.leaf "sat") (.bin (.leaf "the") (.leaf "cat"))
sat the cat → SO →
                    └→ PF: ["sat", "the", "cat"]
```
-/

section YModelDemo

private def sat : SyntacticObject := mkLeafPhon .V [.D] "sat" 1
private def the : SyntacticObject := mkLeafPhon .D [.N] "the" 2
private def cat : SyntacticObject := mkLeafPhon .N [] "cat" 3

/-- Step 1 — Narrow syntax: build DP via Merge(the, cat) -/
private def thecat : SyntacticObject := merge the cat

/-- Step 2 — Narrow syntax: build VP via Merge(sat, DP) -/
private def satthecat : SyntacticObject := merge sat thecat

/-- Step 3a — Spell-Out → LF: `toLFTree` produces a binary tree of
    phonological labels ready for compositional interpretation. -/
theorem satthecat_toLFTree :
    satthecat.toLFTree = .bin (.leaf "sat") (.bin (.leaf "the") (.leaf "cat")) := by
  rfl

/-- Step 3b — Spell-Out → PF: `linearize` yields left-to-right word order. -/
theorem satthecat_toPF :
    (linearize satthecat).map LIToken.phonForm = ["sat", "the", "cat"] := by
  rfl

/-- PF and LF are independent projections of the same SO (the Y-model).
    Both branches start from `satthecat` but produce different types. -/
theorem y_model_branches :
    satthecat.toLFTree = .bin (.leaf "sat") (.bin (.leaf "the") (.leaf "cat")) ∧
    (linearize satthecat).map LIToken.phonForm = ["sat", "the", "cat"] :=
  ⟨satthecat_toLFTree, satthecat_toPF⟩

end YModelDemo

end Minimalism
