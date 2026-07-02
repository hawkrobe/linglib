import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Data.RoseTree.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

set_option autoImplicit false

/-!
# Generalized cut-summand enumeration on `RoseTree α`
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The **admissible-cut enumeration** parameterized by an extraction policy
`extract : RoseTree α → Option (List (RoseTree α))`. A cut at a child
position calls `extract` on the cut subtree:

- `extract t = none` — cuts at this subtree are forbidden (the
  "extract whole" branch is omitted).
- `extract t = some []` — extract whole, leaving NOTHING in the
  parent's child slot (the deletion / Δ^ρ convention).
- `extract t = some [r]` — extract whole, leaving a single replacement
  leaf `r` in the parent's child slot (the trace / Δ^c convention).
- `extract t = some [r₁, r₂, ...]` — extract whole, leaving multiple
  replacement leaves (general; not used by current consumers).

Both Δ^ρ (deletion-style, `Pruning.lean`) and Δ^c (trace-preserving,
`Trace.lean`) are specializations of this enumeration. The
combinatorial cut bookkeeping is shared; only the per-cut remainder
semantics varies.

## Status

`[UPSTREAM]` candidate. Sorry-free. Substrate for the GL-duality
coassoc proof of Δ^c (Foissy 2018, hal-01924416, §4.2 + Cor 4.10):
once a single cut enumeration is in place, the per-cut remainder
function (deletion vs trace vs other) is just a parameter to the same
combinatorial bookkeeping.

## MCB anchor

[marcolli-chomsky-berwick-2025] Definition 1.2.8 (book p. 33),
formula (1.2.8) defines Δ^ω(T) := T ⊗ 1 + 1 ⊗ T + Σ F_v ⊗ T/^ω F_v
for ω ∈ {c, d, ρ}. The three remainder semantics differ in T/^ω F_v
but the cut enumeration F_v is the same. This file factors the cut
enumeration out of the remainder choice.
-/

namespace RootedTree

namespace ConnesKreimer

variable {α : Type*}

/-! ### `cutSummandsG` — enumeration parameterized by `extract`

Mirrors `cutSummandsP`/`cutListSummandsP`/`augActionP` (in `Pruning.lean`)
but with the per-child decision factored through `extract`. The
remainder type is `List (RoseTree α)` (zero, one, or many replacement
leaves per cut), uniform across deletion and trace variants.

For Δ^ρ: `extract t := some []` (always extract, leave nothing).
For Δ^c: `extract` returns `some [traceLeaf (τ t)]` for `Sum.inl`-rooted
inputs and `none` for `Sum.inr`-rooted inputs. -/

mutual
/-- Multiset of (cut forest, remainder) pairs for a tree, under
    the extraction policy `extract`. -/
def cutSummandsG (extract : RoseTree α → Option (List (RoseTree α))) :
    RoseTree α → Multiset (Forest (RoseTree α) × RoseTree α)
  | .node a cs => (cutListSummandsG extract cs).map (fun p => (p.1, .node a p.2))
/-- Auxiliary: cut summands for a list of children. The remainder is a
    list of replacement entries — each surviving child contributes one
    entry (its remainder); each extracted child contributes
    `extract t`-many entries. -/
def cutListSummandsG (extract : RoseTree α → Option (List (RoseTree α))) :
    List (RoseTree α) → Multiset (Forest (RoseTree α) × List (RoseTree α))
  | [] => {((0 : Forest (RoseTree α)), ([] : List (RoseTree α)))}
  | t :: ts =>
      ((augActionG extract t ×ˢ cutListSummandsG extract ts) : Multiset _).map
        (fun p => (p.1.1 + p.2.1, p.1.2 ++ p.2.2))
/-- Auxiliary: per-child action under `extract`. The `extract` branch
    contributes `({t}, replacement)` if `extract t = some replacement`
    (omitted if `extract t = none`). The recursive branch contributes
    `(cut, [remainder])` for each cut summand of t. -/
def augActionG (extract : RoseTree α → Option (List (RoseTree α))) :
    RoseTree α → Multiset (Forest (RoseTree α) × List (RoseTree α))
  | t =>
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Forest (RoseTree α)), r)})
      + (cutSummandsG extract t).map (fun p => (p.1, [p.2]))
end

/-- Recursive formula on a node: cutSummandsG unfolds via cutListSummandsG. -/
@[simp] theorem cutSummandsG_node
    (extract : RoseTree α → Option (List (RoseTree α)))
    (a : α) (cs : List (RoseTree α)) :
    cutSummandsG extract (RoseTree.node a cs) =
      (cutListSummandsG extract cs).map (fun p => (p.1, .node a p.2)) := by
  unfold cutSummandsG; rfl

/-- Recursive formula for cutListSummandsG on empty list. -/
@[simp] theorem cutListSummandsG_nil
    (extract : RoseTree α → Option (List (RoseTree α))) :
    cutListSummandsG extract ([] : List (RoseTree α)) =
      {((0 : Forest (RoseTree α)), ([] : List (RoseTree α)))} := by
  unfold cutListSummandsG; rfl

/-- Recursive formula for cutListSummandsG on a cons list. -/
@[simp] theorem cutListSummandsG_cons
    (extract : RoseTree α → Option (List (RoseTree α)))
    (t : RoseTree α) (ts : List (RoseTree α)) :
    cutListSummandsG extract (t :: ts) =
      ((augActionG extract t ×ˢ cutListSummandsG extract ts) : Multiset _).map
        (fun p => (p.1.1 + p.2.1, p.1.2 ++ p.2.2)) := by
  conv_lhs => unfold cutListSummandsG

/-- Recursive formula for augActionG. -/
@[simp] theorem augActionG_eq
    (extract : RoseTree α → Option (List (RoseTree α))) (t : RoseTree α) :
    augActionG extract t =
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Forest (RoseTree α)), r)})
      + (cutSummandsG extract t).map (fun p => (p.1, [p.2])) := by
  conv_lhs => unfold augActionG

/-- Specialized form of `augActionG_eq` when `extract t = none`: only
    the inherited cut summands survive. -/
theorem augActionG_eq_none
    (extract : RoseTree α → Option (List (RoseTree α))) (t : RoseTree α)
    (h : extract t = none) :
    augActionG extract t =
      (cutSummandsG extract t).map (fun p => (p.1, [p.2])) := by
  rw [augActionG_eq, h]
  simp

/-- Specialized form of `augActionG_eq` when `extract t = some r`: the
    extract-whole branch contributes `({t}, r)`. -/
theorem augActionG_eq_some
    (extract : RoseTree α → Option (List (RoseTree α))) (t : RoseTree α)
    (r : List (RoseTree α)) (h : extract t = some r) :
    augActionG extract t =
      (({t} : Forest (RoseTree α)), r) ::ₘ
        (cutSummandsG extract t).map (fun p => (p.1, [p.2])) := by
  rw [augActionG_eq, h]
  rw [Multiset.singleton_add]

/-! ### Node-count conservation under generic cuts

For extraction policies whose replacement entries carry a single node
total (Δ^c's single trace leaf, `extractC`), every cut summand conserves
vertices up to one replacement vertex per crown component: crown node
count plus remainder node count equals the original node count plus the
crown's component count. At the edge level this is exact conservation —
the grading of MCB Lemma 1.2.10 (`TraceNonplanar.lean`).

A child list's total node count is `(l.map RoseTree.numNodes).sum`, so
`List.map_append`/`List.sum_append` discharge the append step directly
and `RoseTree.numNodes_node` unfolds the node count — no bespoke child-list
recursion or append lemma is needed. -/

mutual

/-- Cut summands conserve node count (tree level): crown node count plus
    trunk node count equals the tree node count plus one replacement
    vertex per crown component. Requires single-node replacement entries. -/
theorem cutSummandsG_numNodes
    (extract : RoseTree α → Option (List (RoseTree α)))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numNodes).sum = 1) :
    ∀ (t : RoseTree α), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map RoseTree.numNodes p.1).sum + RoseTree.numNodes p.2 =
        RoseTree.numNodes t + Multiset.card p.1
  | .node a cs => by
    intro p hp
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsG_numNodes extract hext cs q hq
    simp only [RoseTree.numNodes_node]
    omega

/-- Mutual aux: node-count conservation for children-list cut summands. -/
theorem cutListSummandsG_numNodes
    (extract : RoseTree α → Option (List (RoseTree α)))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numNodes).sum = 1) :
    ∀ (cs : List (RoseTree α)), ∀ q ∈ cutListSummandsG extract cs,
      (Multiset.map RoseTree.numNodes q.1).sum + (q.2.map RoseTree.numNodes).sum =
        (cs.map RoseTree.numNodes).sum + Multiset.card q.1
  | [] => by
    intro q hq
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    simp
  | t :: ts => by
    intro q hq
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionG_numNodes extract hext t pr.1 ha
    have h2 := cutListSummandsG_numNodes extract hext ts pr.2 hq'
    rw [Multiset.map_add, Multiset.sum_add, List.map_append, List.sum_append,
        Multiset.card_add, List.map_cons, List.sum_cons]
    omega

/-- Mutual aux: node-count conservation for per-child actions. -/
theorem augActionG_numNodes
    (extract : RoseTree α → Option (List (RoseTree α)))
    (hext : ∀ t r, extract t = some r → (r.map RoseTree.numNodes).sum = 1) :
    ∀ (t : RoseTree α), ∀ a ∈ augActionG extract t,
      (Multiset.map RoseTree.numNodes a.1).sum + (a.2.map RoseTree.numNodes).sum =
        RoseTree.numNodes t + Multiset.card a.1
  | t => by
    intro a ha
    rw [augActionG_eq] at ha
    rcases Multiset.mem_add.mp ha with h | h
    · cases hex : extract t with
      | none =>
        rw [hex] at h
        exact absurd h (Multiset.notMem_zero a)
      | some r =>
        rw [hex] at h
        obtain rfl := Multiset.mem_singleton.mp h
        have hr := hext t r hex
        rw [Multiset.map_singleton, Multiset.sum_singleton, hr,
            Multiset.card_singleton]
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      have h := cutSummandsG_numNodes extract hext t p hp
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

end

/-! ### Sanity: cuts of a leaf are just the empty cut -/

section Tests

example (extract : RoseTree Unit → Option (List (RoseTree Unit))) :
    cutSummandsG extract (RoseTree.leaf () : RoseTree Unit)
      = {((0 : Forest (RoseTree Unit)), (RoseTree.leaf () : RoseTree Unit))} := by
  show cutSummandsG extract (RoseTree.node () []) = _
  rw [cutSummandsG_node, cutListSummandsG_nil]
  rfl

end Tests

end ConnesKreimer

end RootedTree
