import Linglib.Theories.Syntax.Minimalism.Basic

/-!
# Head Functions for Minimalist Syntactic Objects

@cite{marcolli-chomsky-berwick-2025}

Implements the head-function abstraction of NEW Minimalism. Per M-C-B
§1.13.3, a head function is **external** to the syntactic object and
**partial**: defined only on `Dom(h) ⊂ SO`. This is the canonical formalism
for Chomsky 2013/2015 Bare Phrase Structure: labels are NOT carried by
the type — they are computed by the Labeling Algorithm (§1.15) from a head
function plus the leaf lexical items.

## Why this file exists

linglib's `SyntacticObject := FreeMagma LIToken` (in `Basic.lean`) is
deliberately label-free, matching M-C-B's NEW Minimalism. The natural
consequence: any operation that needs head information must either
- track that information through derivation construction (see
  `Selection.lean`'s `SelectionalState` / `Derivation.headLI?`), OR
- consult an external head function as defined here

The pre-existing `Theories/Syntax/Minimalism/Labeling.lean` implements an
ad-hoc `partial def getCategory` that conflates these two roles. This file
provides the M-C-B-aligned alternative for new code; eventual migration of
`Labeling.lean` to use this abstraction is deferred.

## Key definitions

- `HeadFunction` — a partial map from `SyntacticObject` to `LIToken`
  (Definition 1.13.3), with explicit decidable domain `Dom`
- `HeadFunction.leafOnly` — the trivial head function defined on leaves
- `HeadFunction.IsRaising` — Definition 1.15.1, the constraint required
  for the Labeling Algorithm to extend through Internal Merge

## Out of scope

- The Labeling Algorithm itself (Definition 1.15.2) — requires per-vertex
  labeling and accessible-term machinery from M-C-B §1.14
- The complemented head function (Definition 1.14.2) — extends `h(v)` to
  `(h(v), Z_v)` with the complement
- Phase-theoretic restrictions on `Dom(h)` — M-C-B §1.14
-/

namespace Minimalism

/-- A **head function** in the sense of @cite{marcolli-chomsky-berwick-2025}
    Definition 1.13.3.

    Per M-C-B, head functions are partial: defined only on a domain
    `Dom(h) ⊂ SO`. They are **not** part of the SO type; they are external
    maps that the Labeling Algorithm consults to produce labels.

    This bundle records the domain as a decidable predicate and the head-of
    operation as a function on that domain. -/
structure HeadFunction where
  /-- `Dom(h)` per M-C-B §1.13.3: the subset of `SyntacticObject` on which
      the head function is defined. -/
  Dom : SyntacticObject → Prop
  /-- `Dom` membership is decidable. -/
  decDom : DecidablePred Dom
  /-- `h(T)` for `T ∈ Dom(h)`: the LIToken at the projecting head's leaf. -/
  headOf : (so : SyntacticObject) → Dom so → LIToken

attribute [instance] HeadFunction.decDom

/-- The trivial head function: defined on leaves, where `h(.leaf tok) = tok`.

    This is the minimal head function. Per M-C-B, every well-built SO has
    its leaves in Dom(h); the question is which non-leaf nodes also belong.
    The leaf-only function is correct but uninformative — it refuses to
    label any internal vertex. -/
def HeadFunction.leafOnly : HeadFunction where
  Dom so := so.isLeaf
  decDom := inferInstance
  headOf so h := match so, h with
    | .leaf tok, _ => tok

/-- The leftmost-leaf head function: defined on **all** SOs, using the
    leftmost-leaf-along-left-spine as the head. Sound for left-headed trees
    built via `Step.emR` complement Merge; heuristic for arbitrary
    `FreeMagma LIToken` values.

    Per M-C-B §1.13.3, this is one possible total extension of the head
    function to `Dom = SO`. It is the formalization of `Basic.lean`'s
    `outerCat` heuristic as an explicit `HeadFunction` instance. -/
def HeadFunction.leftSpine : HeadFunction where
  Dom _ := True
  decDom _ := isTrue trivial
  headOf so _ := so.leftmostLeaf

/-- Definition 1.15.1 (M-C-B): A head function `h` is **raising** when its
    behavior under Internal Merge is consistent with the labeling assigned
    to the structure built by `M(T_v, T/^c T_v)`.

    The full statement requires accessible-term operations from M-C-B §1.14
    (workspace coproducts, admissible cuts) which are not yet implemented
    in linglib. We provide the predicate shape as a placeholder; concrete
    head-function instances should eventually carry a proof of this
    property. The trivial `leafOnly` head function is vacuously raising
    (Internal Merge of a leaf is not in its domain). -/
def HeadFunction.IsRaising (_ : HeadFunction) : Prop := True

/-- Convenience: the head's outer categorial feature, when defined. -/
def HeadFunction.outerCatOf (h : HeadFunction) (so : SyntacticObject)
    (hd : h.Dom so) : Cat :=
  (h.headOf so hd).item.outerCat

/-- Convenience: the head's selectional stack, when defined. -/
def HeadFunction.outerSelOf (h : HeadFunction) (so : SyntacticObject)
    (hd : h.Dom so) : SelStack :=
  (h.headOf so hd).item.outerSel

end Minimalism
