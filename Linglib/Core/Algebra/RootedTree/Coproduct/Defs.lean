import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Combinatorics.RootedTree.PlanarCut
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

set_option autoImplicit false

/-!
# Generalized cut-summand enumeration on `RootedTree.Planar α`
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-introduction-hopf-algebras-trees}

The **admissible-cut enumeration** parameterized by an extraction policy
`extract : Planar α → Option (List (Planar α))`. A cut at a child
position calls `extract` on the cut subtree:

- `extract t = none` — cuts at this subtree are forbidden (the
  "extract whole" branch is omitted).
- `extract t = some []` — extract whole, leaving NOTHING in the
  parent's child slot (the deletion / Δ^p convention).
- `extract t = some [r]` — extract whole, leaving a single replacement
  leaf `r` in the parent's child slot (the trace / Δ^c convention).
- `extract t = some [r₁, r₂, ...]` — extract whole, leaving multiple
  replacement leaves (general; not used by current consumers).

Both Δ^p (deletion-style, `Coproduct.lean`) and Δ^c (trace-preserving,
`CoproductDecorated.lean`) are specializations of this enumeration. The
combinatorial cut bookkeeping is shared; only the per-cut remainder
semantics varies.

## Status

`[UPSTREAM]` candidate. Sorry-free. Substrate for the GL-duality
coassoc proof of Δ^c (Foissy 2018, hal-01924416, §4.2 + Cor 4.10):
once a single cut enumeration is in place, the per-cut remainder
function (deletion vs trace vs other) is just a parameter to the same
combinatorial bookkeeping.

## MCB anchor

@cite{marcolli-chomsky-berwick-2025} Definition 1.2.8 (book p. 33),
formula (1.2.8) defines Δ^ω(T) := T ⊗ 1 + 1 ⊗ T + Σ F_v ⊗ T/^ω F_v
for ω ∈ {c, d, ρ}. The three remainder semantics differ in T/^ω F_v
but the cut enumeration F_v is the same. This file factors the cut
enumeration out of the remainder choice.
-/

namespace RootedTree

namespace ConnesKreimer

variable {α : Type*}

/-! ### `cutSummandsG` — enumeration parameterized by `extract`

Mirrors `cutSummandsP`/`cutListSummandsP`/`augActionP` (in `Coproduct.lean`)
but with the per-child decision factored through `extract`. The
remainder type is `List (Planar α)` (zero, one, or many replacement
leaves per cut), uniform across deletion and trace variants.

For Δ^p: `extract t := some []` (always extract, leave nothing).
For Δ^c: `extract` returns `some [traceLeaf (τ t)]` for `Sum.inl`-rooted
inputs and `none` for `Sum.inr`-rooted inputs. -/

mutual
/-- Multiset of (cut forest, remainder) pairs for a planar tree, under
    the extraction policy `extract`. -/
def cutSummandsG (extract : Planar α → Option (List (Planar α))) :
    Planar α → Multiset (Forest (Planar α) × Planar α)
  | .node a cs => (cutListSummandsG extract cs).map (fun p => (p.1, .node a p.2))
/-- Auxiliary: cut summands for a list of children. The remainder is a
    list of replacement entries — each surviving child contributes one
    entry (its remainder); each extracted child contributes
    `extract t`-many entries. -/
def cutListSummandsG (extract : Planar α → Option (List (Planar α))) :
    List (Planar α) → Multiset (Forest (Planar α) × List (Planar α))
  | [] => {((0 : Forest (Planar α)), ([] : List (Planar α)))}
  | t :: ts =>
      ((augActionG extract t ×ˢ cutListSummandsG extract ts) : Multiset _).map
        (fun p => (p.1.1 + p.2.1, p.1.2 ++ p.2.2))
/-- Auxiliary: per-child action under `extract`. The `extract` branch
    contributes `({t}, replacement)` if `extract t = some replacement`
    (omitted if `extract t = none`). The recursive branch contributes
    `(cut, [remainder])` for each cut summand of t. -/
def augActionG (extract : Planar α → Option (List (Planar α))) :
    Planar α → Multiset (Forest (Planar α) × List (Planar α))
  | t =>
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Forest (Planar α)), r)})
      + (cutSummandsG extract t).map (fun p => (p.1, [p.2]))
end

/-- Recursive formula on a node: cutSummandsG unfolds via cutListSummandsG. -/
@[simp] theorem cutSummandsG_node
    (extract : Planar α → Option (List (Planar α)))
    (a : α) (cs : List (Planar α)) :
    cutSummandsG extract (Planar.node a cs) =
      (cutListSummandsG extract cs).map (fun p => (p.1, .node a p.2)) := by
  unfold cutSummandsG; rfl

/-- Recursive formula for cutListSummandsG on empty list. -/
@[simp] theorem cutListSummandsG_nil
    (extract : Planar α → Option (List (Planar α))) :
    cutListSummandsG extract ([] : List (Planar α)) =
      {((0 : Forest (Planar α)), ([] : List (Planar α)))} := by
  unfold cutListSummandsG; rfl

/-- Recursive formula for cutListSummandsG on a cons list. -/
@[simp] theorem cutListSummandsG_cons
    (extract : Planar α → Option (List (Planar α)))
    (t : Planar α) (ts : List (Planar α)) :
    cutListSummandsG extract (t :: ts) =
      ((augActionG extract t ×ˢ cutListSummandsG extract ts) : Multiset _).map
        (fun p => (p.1.1 + p.2.1, p.1.2 ++ p.2.2)) := by
  conv_lhs => unfold cutListSummandsG

/-- Recursive formula for augActionG. -/
@[simp] theorem augActionG_eq
    (extract : Planar α → Option (List (Planar α))) (t : Planar α) :
    augActionG extract t =
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Forest (Planar α)), r)})
      + (cutSummandsG extract t).map (fun p => (p.1, [p.2])) := by
  conv_lhs => unfold augActionG

/-- Specialized form of `augActionG_eq` when `extract t = none`: only
    the inherited cut summands survive. -/
theorem augActionG_eq_none
    (extract : Planar α → Option (List (Planar α))) (t : Planar α)
    (h : extract t = none) :
    augActionG extract t =
      (cutSummandsG extract t).map (fun p => (p.1, [p.2])) := by
  rw [augActionG_eq, h]
  simp

/-- Specialized form of `augActionG_eq` when `extract t = some r`: the
    extract-whole branch contributes `({t}, r)`. -/
theorem augActionG_eq_some
    (extract : Planar α → Option (List (Planar α))) (t : Planar α)
    (r : List (Planar α)) (h : extract t = some r) :
    augActionG extract t =
      (({t} : Forest (Planar α)), r) ::ₘ
        (cutSummandsG extract t).map (fun p => (p.1, [p.2])) := by
  rw [augActionG_eq, h]
  rw [Multiset.singleton_add]

/-! ### Sanity: cuts of a leaf are just the empty cut -/

section Tests

example (extract : Planar Unit → Option (List (Planar Unit))) :
    cutSummandsG extract (Planar.leaf () : Planar Unit)
      = {((0 : Forest (Planar Unit)), (Planar.leaf () : Planar Unit))} := by
  show cutSummandsG extract (Planar.node () []) = _
  rw [cutSummandsG_node, cutListSummandsG_nil]
  rfl

end Tests

end ConnesKreimer

end RootedTree
