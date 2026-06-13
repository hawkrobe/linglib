import Linglib.Core.Algebra.RootedTree.ConnesKreimer
import Linglib.Core.Combinatorics.RootedTree.PlanarCut
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

set_option autoImplicit false

/-!
# Generalized cut-summand enumeration on `RootedTree.Planar α`
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The **admissible-cut enumeration** parameterized by an extraction policy
`extract : Planar α → Option (List (Planar α))`. A cut at a child
position calls `extract` on the cut subtree:

- `extract t = none` — cuts at this subtree are forbidden (the
  "extract whole" branch is omitted).
- `extract t = some []` — extract whole, leaving NOTHING in the
  parent's child slot (the deletion / Δ^ρ convention).
- `extract t = some [r]` — extract whole, leaving a single replacement
  leaf `r` in the parent's child slot (the trace / Δ^c convention).
- `extract t = some [r₁, r₂, ...]` — extract whole, leaving multiple
  replacement leaves (general; not used by current consumers).

Both Δ^ρ (deletion-style, `Coproduct.lean`) and Δ^c (trace-preserving,
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

Mirrors `cutSummandsP`/`cutListSummandsP`/`augActionP` (in `Coproduct.lean`)
but with the per-child decision factored through `extract`. The
remainder type is `List (Planar α)` (zero, one, or many replacement
leaves per cut), uniform across deletion and trace variants.

For Δ^ρ: `extract t := some []` (always extract, leave nothing).
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

/-! ### Weight conservation under generic cuts

For extraction policies whose replacement entries carry unit total
weight (Δ^c's single trace leaf, `extractC`), every cut summand
conserves vertices up to one replacement vertex per crown component:
crown weight plus remainder weight equals the original weight plus the
crown's component count. At the edge level this is exact conservation —
the grading of MCB Lemma 1.2.10 (`TraceNonplanar.lean`). -/

private theorem weightList_append (l₁ l₂ : List (Planar α)) :
    Planar.weightList (l₁ ++ l₂) =
      Planar.weightList l₁ + Planar.weightList l₂ := by
  induction l₁ with
  | nil => show Planar.weightList l₂ = 0 + Planar.weightList l₂; omega
  | cons t ts ih =>
    show Planar.weight t + Planar.weightList (ts ++ l₂) =
      Planar.weight t + Planar.weightList ts + Planar.weightList l₂
    rw [ih]
    omega

mutual

/-- Cut summands conserve weight (tree level): crown weight plus trunk
    weight equals the tree weight plus one replacement vertex per crown
    component. Requires unit-weight replacement entries. -/
theorem cutSummandsG_weight
    (extract : Planar α → Option (List (Planar α)))
    (hext : ∀ t r, extract t = some r → Planar.weightList r = 1) :
    ∀ (t : Planar α), ∀ p ∈ cutSummandsG extract t,
      (Multiset.map Planar.weight p.1).sum + Planar.weight p.2 =
        Planar.weight t + Multiset.card p.1
  | .node a cs => by
    intro p hp
    rw [cutSummandsG_node] at hp
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
    have h := cutListSummandsG_weight extract hext cs q hq
    show (Multiset.map Planar.weight q.1).sum +
        (1 + Planar.weightList q.2) =
      (1 + Planar.weightList cs) + Multiset.card q.1
    omega

/-- Mutual aux: weight conservation for children-list cut summands. -/
theorem cutListSummandsG_weight
    (extract : Planar α → Option (List (Planar α)))
    (hext : ∀ t r, extract t = some r → Planar.weightList r = 1) :
    ∀ (cs : List (Planar α)), ∀ q ∈ cutListSummandsG extract cs,
      (Multiset.map Planar.weight q.1).sum + Planar.weightList q.2 =
        Planar.weightList cs + Multiset.card q.1
  | [] => by
    intro q hq
    rw [cutListSummandsG_nil] at hq
    obtain rfl := Multiset.mem_singleton.mp hq
    show (Multiset.map Planar.weight 0).sum + Planar.weightList [] =
      Planar.weightList [] + Multiset.card 0
    rfl
  | t :: ts => by
    intro q hq
    rw [cutListSummandsG_cons] at hq
    obtain ⟨pr, hpr, rfl⟩ := Multiset.mem_map.mp hq
    obtain ⟨ha, hq'⟩ := Multiset.mem_product.mp hpr
    have h1 := augActionG_weight extract hext t pr.1 ha
    have h2 := cutListSummandsG_weight extract hext ts pr.2 hq'
    show (Multiset.map Planar.weight (pr.1.1 + pr.2.1)).sum +
        Planar.weightList (pr.1.2 ++ pr.2.2) =
      (Planar.weight t + Planar.weightList ts) +
        Multiset.card (pr.1.1 + pr.2.1)
    rw [Multiset.map_add, Multiset.sum_add, weightList_append,
        Multiset.card_add]
    omega

/-- Mutual aux: weight conservation for per-child actions. -/
theorem augActionG_weight
    (extract : Planar α → Option (List (Planar α)))
    (hext : ∀ t r, extract t = some r → Planar.weightList r = 1) :
    ∀ (t : Planar α), ∀ a ∈ augActionG extract t,
      (Multiset.map Planar.weight a.1).sum + Planar.weightList a.2 =
        Planar.weight t + Multiset.card a.1
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
        show (Multiset.map Planar.weight {t}).sum + Planar.weightList r =
          Planar.weight t + Multiset.card {t}
        rw [Multiset.map_singleton, Multiset.sum_singleton, hr,
            Multiset.card_singleton]
    · obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp h
      have h := cutSummandsG_weight extract hext t p hp
      show (Multiset.map Planar.weight p.1).sum +
          (Planar.weight p.2 + Planar.weightList []) =
        Planar.weight t + Multiset.card p.1
      show (Multiset.map Planar.weight p.1).sum +
          (Planar.weight p.2 + 0) = Planar.weight t + Multiset.card p.1
      omega

end

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
