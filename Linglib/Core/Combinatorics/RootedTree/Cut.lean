import Linglib.Core.Data.RoseTree.Nonplanar
import Linglib.Core.Data.RoseTree.DecEq
import Mathlib.Data.Multiset.Bind
import Linglib.Core.Data.RoseTree.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

open RoseTree RoseTree.Nonplanar

/-!
# Admissible-cut enumeration on rose trees
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The combinatorics of admissible cuts, independent of the Hopf-algebra
structures built on it in `Core/Algebra/RootedTree/Coproduct/`: the
policy-parameterized enumeration (`cutSummandsG`), its Δ^ρ instance
(`cutSummandsP`) and Δ^c instance (`extractC`, `cutSummandsCP`), the
projections to `RoseTree.Nonplanar` with their `Perm`-invariance
(`cutSummandsN`, `cutSummandsCN`), and the single-cut count
(`countSingleCutsRho`).

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

`[UPSTREAM]` candidate. Once a single cut enumeration is in place, the
per-cut remainder function (deletion vs trace vs other) is just a
parameter to the same combinatorial bookkeeping.

## MCB anchor

[marcolli-chomsky-berwick-2025] Definition 1.2.8 (book p. 33),
formula (1.2.8) defines Δ^ω(T) := T ⊗ 1 + 1 ⊗ T + Σ F_v ⊗ T/^ω F_v
for ω ∈ {c, d, ρ}. The three remainder semantics differ in T/^ω F_v
but the cut enumeration F_v is the same. This file factors the cut
enumeration out of the remainder choice.
-/

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
    RoseTree α → Multiset (Multiset (RoseTree α) × RoseTree α)
  | .node a cs => (cutListSummandsG extract cs).map (fun p => (p.1, .node a p.2))
/-- Auxiliary: cut summands for a list of children. The remainder is a
    list of replacement entries — each surviving child contributes one
    entry (its remainder); each extracted child contributes
    `extract t`-many entries. -/
def cutListSummandsG (extract : RoseTree α → Option (List (RoseTree α))) :
    List (RoseTree α) → Multiset (Multiset (RoseTree α) × List (RoseTree α))
  | [] => {((0 : Multiset (RoseTree α)), ([] : List (RoseTree α)))}
  | t :: ts =>
      ((augActionG extract t ×ˢ cutListSummandsG extract ts) : Multiset _).map
        (fun p => (p.1.1 + p.2.1, p.1.2 ++ p.2.2))
/-- Auxiliary: per-child action under `extract`. The `extract` branch
    contributes `({t}, replacement)` if `extract t = some replacement`
    (omitted if `extract t = none`). The recursive branch contributes
    `(cut, [remainder])` for each cut summand of t. -/
def augActionG (extract : RoseTree α → Option (List (RoseTree α))) :
    RoseTree α → Multiset (Multiset (RoseTree α) × List (RoseTree α))
  | t =>
      (match extract t with
       | none => (0 : Multiset _)
       | some r => {(({t} : Multiset (RoseTree α)), r)})
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
      {((0 : Multiset (RoseTree α)), ([] : List (RoseTree α)))} := by
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
       | some r => {(({t} : Multiset (RoseTree α)), r)})
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
      (({t} : Multiset (RoseTree α)), r) ::ₘ
        (cutSummandsG extract t).map (fun p => (p.1, [p.2])) := by
  rw [augActionG_eq, h]
  rw [Multiset.singleton_add]

/-! ### Node-count conservation under generic cuts

For extraction policies whose replacement entries carry a single node
total (Δ^c's single trace leaf, `extractC`), every cut summand conserves
vertices up to one replacement vertex per crown component: crown node
count plus remainder node count equals the original node count plus the
crown's component count. At the edge level this is exact conservation —
the grading of MCB Lemma 1.2.10 (`Trace.lean`).

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
      = {((0 : Multiset (RoseTree Unit)), (RoseTree.leaf () : RoseTree Unit))} := by
  show cutSummandsG extract (RoseTree.node () []) = _
  rw [cutSummandsG_node, cutListSummandsG_nil]
  rfl

end Tests

/-! ### cutSummandsP — multiset of (cut forest, deletion remainder) pairs

Recursive enumeration of cut summands. For a leaf, the only cut is the
empty cut. For a node, sum over all per-child decisions: each child can
either be extracted whole (contributes to cut forest, drops from
remainder) OR recurse with a smaller cut (contributes whatever its cut
extracts, leaves its deletion-remainder in the remainder list).

This bespoke block is the deletion (Δ^ρ) sibling of the
extraction-policy-parameterized `cutSummandsG`. It is deliberately NOT
re-expressed as `cutSummandsG (fun _ => some [])`: the Δ^ρ consumers are
written against the `Option` remainder encoding used here — deletion is
`Option.none`, a surviving child is `Option.some r` — whereas
`cutSummandsG` carries `List` remainders (deletion `[]`, survival `[r]`).
Folding onto `cutSummandsG` would change the public return type of
`augActionP` and the shapes of `augActionP_eq`/`cutListSummandsP_cons`,
so the two enumerations coexist. (Δ^c *does* derive from `cutSummandsG`,
being written against the `List` encoding.) -/

mutual
/-- Multiset of (cut forest, deletion remainder) pairs for a tree.
    Each summand corresponds to one admissible cut on T under the
    deletion semantics. -/
def cutSummandsP : RoseTree α →
    Multiset (Multiset (RoseTree α) × RoseTree α)
  | .node a cs => (cutListSummandsP cs).map (fun p => (p.1, .node a p.2))
/-- Auxiliary: cut summands for a list of children. The remainder is a
    list (children of the parent that survived the cut). -/
def cutListSummandsP : List (RoseTree α) →
    Multiset (Multiset (RoseTree α) × List (RoseTree α))
  | [] => {((0 : Multiset (RoseTree α)), ([] : List (RoseTree α)))}
  | t :: ts =>
      ((augActionP t ×ˢ cutListSummandsP ts) : Multiset _).map
        (fun p => match p.1.2 with
          | Option.none => (p.1.1 + p.2.1, p.2.2)
          | Option.some r => (p.1.1 + p.2.1, r :: p.2.2))
/-- Auxiliary: per-child action — either extract whole (`none` remainder)
    or recurse with a cut (`some remainder`). -/
def augActionP : RoseTree α →
    Multiset (Multiset (RoseTree α) × Option (RoseTree α))
  | t => (({t} : Multiset (RoseTree α)), Option.none) ::ₘ
         (cutSummandsP t).map (fun p => (p.1, Option.some p.2))
end

/-- Recursive formula on a node: cutSummandsP unfolds via cutListSummandsP. -/
@[simp] theorem cutSummandsP_node (a : α) (cs : List (RoseTree α)) :
    cutSummandsP (RoseTree.node a cs) =
      (cutListSummandsP cs).map (fun p => (p.1, .node a p.2)) := by
  unfold cutSummandsP; rfl

/-- Recursive formula for cutListSummandsP on empty list. -/
@[simp] theorem cutListSummandsP_nil :
    cutListSummandsP ([] : List (RoseTree α)) =
      {((0 : Multiset (RoseTree α)), ([] : List (RoseTree α)))} := by
  unfold cutListSummandsP; rfl

/-- Recursive formula for cutListSummandsP on a cons list. -/
@[simp] theorem cutListSummandsP_cons (t : RoseTree α) (ts : List (RoseTree α)) :
    cutListSummandsP (t :: ts) =
      ((augActionP t ×ˢ cutListSummandsP ts) : Multiset _).map
        (fun p => match p.1.2 with
          | Option.none => (p.1.1 + p.2.1, p.2.2)
          | Option.some r => (p.1.1 + p.2.1, r :: p.2.2)) := by
  conv_lhs => unfold cutListSummandsP

/-- Recursive formula for augActionP. -/
@[simp] theorem augActionP_eq (t : RoseTree α) :
    augActionP t = (({t} : Multiset (RoseTree α)), Option.none) ::ₘ
                   (cutSummandsP t).map (fun p => (p.1, Option.some p.2)) := by
  conv_lhs => unfold augActionP

/-- Named version of the combine_P function (extracted to avoid Lean's
    "inline match generates fresh matchers" issue when this is reused
    across proofs via rewrite). -/
def combineP_fn :
    (Multiset (RoseTree α) × Option (RoseTree α)) ×
        (Multiset (RoseTree α) × List (RoseTree α)) →
      Multiset (RoseTree α) × List (RoseTree α) :=
  fun p => match p.1.2 with
    | none => (p.1.1 + p.2.1, p.2.2)
    | some r => (p.1.1 + p.2.1, r :: p.2.2)

theorem cutListSummandsP_cons' (t : RoseTree α) (ts : List (RoseTree α)) :
    cutListSummandsP (t :: ts) =
      (augActionP t ×ˢ cutListSummandsP ts).map combineP_fn := by
  rw [cutListSummandsP_cons]; rfl
/-! ## Projection of cut summands and descent to `Nonplanar`

To descend Δ^ρ from `RoseTree` to `Nonplanar`, we need a Nonplanar-side
cut-summand multiset that is `Perm`-invariant. The strategy:
project each tree-level cut summand through `mk` componentwise, then prove
the resulting multiset depends on `T : RoseTree α` only through `mk T`.

The proof factors through three layers:
- **Pointwise projection** (`projSummand`, `projForest`, `projAugAction`):
  the per-element `Nonplanar.mk` lifts.
- **Combine factoring** (`cutListSummandsP_cons_proj`): the cons case of
  `cutListSummandsP` distributes over the projection, giving a clean
  cartesian-product recursion at the `Nonplanar` level.
- **Headline recursion** (`cutSummandsP_proj_perm` with its `PermList`
  companion `cutListSummandsP_proj_permList`, and the derived
  `cutListSummandsP_proj_componentwise`): structural recursion over the
  mutual `Perm`/`PermList` for the substantive content; a pure
  `List.Forall₂` lift for the rest. -/

/-! ### Pointwise projection -/

/-- Project a tree-level cut summand to a nonplanar one. -/
def projSummand : Multiset (RoseTree α) × RoseTree α →
    Multiset (Nonplanar α) × Nonplanar α :=
  fun p => (p.1.map Nonplanar.mk, Nonplanar.mk p.2)

/-- Project a `cutListSummandsP` summand to nonplanar level, discarding
    the list-order of the remainder children. The discarded order doesn't
    affect the eventual `mk (.node a remainder)`, since `mk` is invariant
    under children-list permutation (`RoseTree.Perm.node_of_perm`). -/
def projForest : Multiset (RoseTree α) × List (RoseTree α) →
    Multiset (Nonplanar α) × Multiset (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, Multiset.ofList (p.2.map Nonplanar.mk))

/-- Project an `augActionP` summand to nonplanar level (per-child decision). -/
def projAugAction : Multiset (RoseTree α) × Option (RoseTree α) →
    Multiset (Nonplanar α) × Option (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, p.2.map Nonplanar.mk)

/-- Bridge: applying `cutSummandsP_node`'s wrapper `(p.1, .node a p.2)`
    then `projSummand` factors through `projForest` followed by the
    `Nonplanar.node a` smart constructor. -/
theorem projSummand_node_factors (a : α) (p : Multiset (RoseTree α) × List (RoseTree α)) :
    projSummand (p.1, .node a p.2) =
      ((projForest p).1, Nonplanar.node a (projForest p).2) := by
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       (p.1.map Nonplanar.mk, Nonplanar.node a (Multiset.ofList (p.2.map Nonplanar.mk)))
  congr 1
  exact (Nonplanar.node_mk_tree_list a p.2).symm

/-! ### Combine factoring through projection

The cons case of `cutListSummandsP` combines a per-child decision
(`augActionP`) with the cut-summands of the remaining children. This
combination distributes over the `Nonplanar` projection: the "projected
combiner" `innerCombinerProj` operates on
`(Forest × Option) × (Forest × Multiset)` and matches `projForest` of
the inline tree-level combiner. The headline result is
`cutListSummandsP_cons_proj`, which expresses the cons case of the
projected `cutListSummandsP` as a clean cartesian product at the
Nonplanar level. -/

/-- The Nonplanar-level combiner: given a per-child decision and the
    accumulated cuts of the remaining children, produce the merged
    (cut forest, remainder multiset) pair. Mirrors the inline lambda in
    `cutListSummandsP`'s cons case but operates on `Multiset` remainders. -/
def innerCombinerProj :
    (Multiset (Nonplanar α) × Option (Nonplanar α)) ×
    (Multiset (Nonplanar α) × Multiset (Nonplanar α)) →
    Multiset (Nonplanar α) × Multiset (Nonplanar α)
  | ((F, Option.none), (G, ms)) => (F + G, ms)
  | ((F, Option.some r), (G, ms)) => (F + G, r ::ₘ ms)

/-- Pointwise: `projForest` of an applied tree-level combiner equals
    `innerCombinerProj` applied to the projected pair-of-pairs. -/
private theorem projForest_innerCombiner_apply
    (p : (Multiset (RoseTree α) × Option (RoseTree α)) ×
         (Multiset (RoseTree α) × List (RoseTree α))) :
    projForest (match p.1.2 with
                | Option.none => (p.1.1 + p.2.1, p.2.2)
                | Option.some r => (p.1.1 + p.2.1, r :: p.2.2)) =
      innerCombinerProj (projAugAction p.1, projForest p.2) := by
  obtain ⟨⟨F, dec⟩, ⟨G, list⟩⟩ := p
  cases dec with
  | none =>
    show ((F + G).map Nonplanar.mk, Multiset.ofList (list.map Nonplanar.mk)) =
         (F.map Nonplanar.mk + G.map Nonplanar.mk, Multiset.ofList (list.map Nonplanar.mk))
    rw [Multiset.map_add]
  | some r =>
    show ((F + G).map Nonplanar.mk, Multiset.ofList ((r :: list).map Nonplanar.mk)) =
         (F.map Nonplanar.mk + G.map Nonplanar.mk,
          Nonplanar.mk r ::ₘ Multiset.ofList (list.map Nonplanar.mk))
    rw [Multiset.map_add]
    rfl

/-- Pointwise: `projAugAction` of `augActionP old` is determined by the
    Nonplanar projection of the cut summands plus the equality of the
    `Nonplanar.mk`-projection of the trees themselves (needed for the
    extract-whole element of `augActionP`). -/
private theorem augActionP_proj_eq_of_step_data
    {old new : RoseTree α}
    (h_mk : Nonplanar.mk old = Nonplanar.mk new)
    (h_proj : (cutSummandsP old).map projSummand =
              (cutSummandsP new).map projSummand) :
    (augActionP old).map projAugAction =
      (augActionP new).map projAugAction := by
  rw [augActionP_eq, augActionP_eq, Multiset.map_cons, Multiset.map_cons]
  congr 1
  · -- First element (extract-whole): projAugAction ({old}, none) = ({mk old}, none)
    show (({old} : Multiset (RoseTree α)).map Nonplanar.mk,
          (Option.none : Option (RoseTree α)).map Nonplanar.mk) =
         (({new} : Multiset (RoseTree α)).map Nonplanar.mk,
          (Option.none : Option (RoseTree α)).map Nonplanar.mk)
    rw [Multiset.map_singleton, Multiset.map_singleton, h_mk]
  · -- Tail: projAugAction-of-projection = (s.1, some s.2) ∘ projSummand
    rw [Multiset.map_map, Multiset.map_map]
    -- Both sides now: (cutSummandsP _).map (projAugAction ∘ (fun p => (p.1, some p.2)))
    -- Rewrite this composed function as (fun s => (s.1, some s.2)) ∘ projSummand
    have eq_fn : (projAugAction (α := α)) ∘
        (fun (p : Multiset (RoseTree α) × RoseTree α) => (p.1, Option.some p.2)) =
        (fun (s : Multiset (Nonplanar α) × Nonplanar α) => (s.1, Option.some s.2)) ∘
        (projSummand (α := α)) := by
      funext p
      rfl
    rw [eq_fn]
    -- Now: (cutSummandsP old).map (g ∘ projSummand) = (cutSummandsP new).map (g ∘ projSummand)
    -- = ((cutSummandsP old).map projSummand).map g = ((cutSummandsP new).map projSummand).map g
    rw [← Multiset.map_map, ← Multiset.map_map, h_proj]

/-! ### Cartesian-product distributivity

The pair-componentwise `Prod.map` distributes over `Multiset.product`
(`×ˢ`). Mathlib has the bind-side analogues but not this exact form for
multiset products; the proof is one inductive line via `cons_product`. -/

private theorem map_prodMap_product {α β γ δ : Type*}
    (f : α → γ) (g : β → δ)
    (s : Multiset α) (t : Multiset β) :
    (s ×ˢ t).map (Prod.map f g) = s.map f ×ˢ t.map g := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.cons_product, Multiset.map_add, Multiset.map_map,
               Multiset.map_cons, ih]
    rfl

/-! ### Headline factoring: cons case of projected `cutListSummandsP` -/

/-- The projected `cutListSummandsP` on a cons list factors as a clean
    cartesian product at the Nonplanar level. This is the key lemma
    enabling all subsequent invariance proofs. -/
theorem cutListSummandsP_cons_proj (t : RoseTree α) (ts : List (RoseTree α)) :
    (cutListSummandsP (t :: ts)).map projForest =
      ((augActionP t).map projAugAction ×ˢ
       (cutListSummandsP ts).map projForest).map innerCombinerProj := by
  rw [cutListSummandsP_cons, Multiset.map_map, ← map_prodMap_product,
      Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  exact projForest_innerCombiner_apply p

/-! ### List-side projection invariants

These three theorems establish that the projected `cutListSummandsP` is
invariant under (1) substituting an "augAction-projection-equal" child,
(2) substituting a "projForest-equal" tail, and (3) any list permutation. -/

/-- Substituting `old` with `new` in `cutListSummandsP` is invariant
    under `projForest` if `(augActionP old).map projAugAction =
    (augActionP new).map projAugAction`. -/
private theorem cutListSummandsP_proj_at_via_augAction
    {pre post : List (RoseTree α)} {old new : RoseTree α}
    (h : (augActionP old).map projAugAction =
         (augActionP new).map projAugAction) :
    (cutListSummandsP (pre ++ old :: post)).map projForest =
    (cutListSummandsP (pre ++ new :: post)).map projForest := by
  induction pre with
  | nil =>
    show (cutListSummandsP (old :: post)).map projForest =
         (cutListSummandsP (new :: post)).map projForest
    rw [cutListSummandsP_cons_proj, cutListSummandsP_cons_proj, h]
  | cons p pre' ih =>
    show (cutListSummandsP (p :: (pre' ++ old :: post))).map projForest =
         (cutListSummandsP (p :: (pre' ++ new :: post))).map projForest
    rw [cutListSummandsP_cons_proj, cutListSummandsP_cons_proj, ih]

/-- Tail lift: `cutListSummandsP` is invariant under `projForest`-equal
    tails when consed with a fixed head. -/
private theorem cutListSummandsP_proj_tail_lift (d : RoseTree α)
    {cs ds : List (RoseTree α)}
    (h : (cutListSummandsP cs).map projForest =
         (cutListSummandsP ds).map projForest) :
    (cutListSummandsP (d :: cs)).map projForest =
      (cutListSummandsP (d :: ds)).map projForest := by
  rw [cutListSummandsP_cons_proj, cutListSummandsP_cons_proj, h]

/-- Triple-combiner symmetry: combining three pieces (two decisions plus
    the accumulated rest) at the projected level is symmetric in the
    first two decision arguments. -/
theorem innerCombinerProj_swap_args
    (a b : Multiset (Nonplanar α) × Option (Nonplanar α))
    (c : Multiset (Nonplanar α) × Multiset (Nonplanar α)) :
    innerCombinerProj (a, innerCombinerProj (b, c)) =
    innerCombinerProj (b, innerCombinerProj (a, c)) := by
  obtain ⟨Fa, da⟩ := a
  obtain ⟨Fb, db⟩ := b
  obtain ⟨Fc, mc⟩ := c
  cases da with
  | none =>
    cases db with
    | none =>
      show (Fa + (Fb + Fc), mc) = (Fb + (Fa + Fc), mc)
      rw [← add_assoc, ← add_assoc, add_comm Fa Fb]
    | some rb =>
      show (Fa + (Fb + Fc), rb ::ₘ mc) = (Fb + (Fa + Fc), rb ::ₘ mc)
      rw [← add_assoc, ← add_assoc, add_comm Fa Fb]
  | some ra =>
    cases db with
    | none =>
      show (Fa + (Fb + Fc), ra ::ₘ mc) = (Fb + (Fa + Fc), ra ::ₘ mc)
      rw [← add_assoc, ← add_assoc, add_comm Fa Fb]
    | some rb =>
      show (Fa + (Fb + Fc), ra ::ₘ rb ::ₘ mc) =
           (Fb + (Fa + Fc), rb ::ₘ ra ::ₘ mc)
      have hF : Fa + (Fb + Fc) = Fb + (Fa + Fc) := by
        rw [← add_assoc, ← add_assoc, add_comm Fa Fb]
      have hM : (ra ::ₘ rb ::ₘ mc : Multiset (Nonplanar α)) = rb ::ₘ ra ::ₘ mc :=
        Multiset.cons_swap ra rb mc
      rw [hF, hM]

/-- Doubly-applied `innerCombinerProj` over a triple cartesian product
    is symmetric in the first two factors. The substantive content of
    `cutListSummandsP_proj_perm`'s `swap` case. -/
theorem swap_double_combinerProj
    (A B : Multiset (Multiset (Nonplanar α) × Option (Nonplanar α)))
    (C : Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α))) :
    (A ×ˢ (B ×ˢ C).map innerCombinerProj).map innerCombinerProj =
    (B ×ˢ (A ×ˢ C).map innerCombinerProj).map innerCombinerProj := by
  -- Convert both sides to triple-bind form, swap outer two binds via
  -- `bind_bind`, then close pointwise via `innerCombinerProj_swap_args`.
  have lhs :
      (A ×ˢ (B ×ˢ C).map innerCombinerProj).map innerCombinerProj =
        A.bind (fun a => B.bind (fun b => C.map (fun c =>
          innerCombinerProj (a, innerCombinerProj (b, c))))) := by
    show ((A.bind fun a => ((B ×ˢ C).map innerCombinerProj).map (Prod.mk a))
          ).map innerCombinerProj = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr; intro a _
    show ((((B.bind fun b => C.map (Prod.mk b)) : Multiset _).map innerCombinerProj).map
            (Prod.mk a)).map innerCombinerProj = _
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    apply Multiset.bind_congr; intro b _
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    rfl
  have rhs :
      (B ×ˢ (A ×ˢ C).map innerCombinerProj).map innerCombinerProj =
        B.bind (fun b => A.bind (fun a => C.map (fun c =>
          innerCombinerProj (b, innerCombinerProj (a, c))))) := by
    show ((B.bind fun b => ((A ×ˢ C).map innerCombinerProj).map (Prod.mk b))
          ).map innerCombinerProj = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr; intro b _
    show ((((A.bind fun a => C.map (Prod.mk a)) : Multiset _).map innerCombinerProj).map
            (Prod.mk b)).map innerCombinerProj = _
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    apply Multiset.bind_congr; intro a _
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    rfl
  rw [lhs, rhs, Multiset.bind_bind]
  apply Multiset.bind_congr; intro b _
  apply Multiset.bind_congr; intro a _
  apply Multiset.map_congr rfl; intro c _
  exact innerCombinerProj_swap_args a b c

/-- The projected `cutListSummandsP` is `List.Perm`-invariant: two
    permutation-related child lists yield the same projected
    cut-summand multiset. -/
theorem cutListSummandsP_proj_perm
    {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    (cutListSummandsP cs).map projForest =
      (cutListSummandsP ds).map projForest := by
  induction h with
  | nil => rfl
  | cons c _ ih => exact cutListSummandsP_proj_tail_lift c ih
  | swap c d cs =>
    rw [cutListSummandsP_cons_proj, cutListSummandsP_cons_proj,
        cutListSummandsP_cons_proj, cutListSummandsP_cons_proj]
    exact (swap_double_combinerProj _ _ _).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Headline: `Perm` + `PermList` recursion

Structural recursion over the mutual `Perm`/`PermList`. The `node` case lifts
the companion's list-level equality through the `Nonplanar.node a` wrapper; the
`PermList.cons` case changes the head child then the tail; the `PermList.swap`
case reorders identical siblings (`cutListSummandsP_proj_perm`). -/

mutual
/-- Projection invariance of `cutSummandsP` under `Perm`. -/
theorem cutSummandsP_proj_perm :
    ∀ {t s : RoseTree α}, RoseTree.Perm t s →
      (cutSummandsP t).map projSummand = (cutSummandsP s).map projSummand
  | _, _, @RoseTree.Perm.node _ a cs ds h => by
    rw [cutSummandsP_node, cutSummandsP_node, Multiset.map_map, Multiset.map_map]
    have hL : (cutListSummandsP cs).map projForest =
              (cutListSummandsP ds).map projForest :=
      cutListSummandsP_proj_permList h
    have eq_fn :
        (projSummand (α := α)) ∘
          (fun (p : Multiset (RoseTree α) × List (RoseTree α)) => (p.1, .node a p.2)) =
        (fun (pf : Multiset (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForest (α := α)) := by
      funext p
      exact projSummand_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]
  | _, _, .trans h₁ h₂ => (cutSummandsP_proj_perm h₁).trans (cutSummandsP_proj_perm h₂)

/-- Companion: projection invariance of `cutListSummandsP` under `PermList`. -/
private theorem cutListSummandsP_proj_permList :
    ∀ {cs ds : List (RoseTree α)}, RoseTree.PermList cs ds →
      (cutListSummandsP cs).map projForest = (cutListSummandsP ds).map projForest
  | _, _, .nil => rfl
  | _, _, @RoseTree.PermList.cons _ c d cs' ds' hcd hs => by
    have h_aug : (augActionP c).map projAugAction =
                 (augActionP d).map projAugAction :=
      augActionP_proj_eq_of_step_data (Nonplanar.mk_eq_mk_iff.mpr hcd)
        (cutSummandsP_proj_perm hcd)
    have step1 : (cutListSummandsP (c :: cs')).map projForest =
                 (cutListSummandsP (d :: cs')).map projForest :=
      cutListSummandsP_proj_at_via_augAction (pre := []) (post := cs') h_aug
    have step2 : (cutListSummandsP (d :: cs')).map projForest =
                 (cutListSummandsP (d :: ds')).map projForest :=
      cutListSummandsP_proj_tail_lift d (cutListSummandsP_proj_permList hs)
    exact step1.trans step2
  | _, _, .swap c d cs => cutListSummandsP_proj_perm (List.Perm.swap c d cs)
  | _, _, .trans h₁ h₂ =>
    (cutListSummandsP_proj_permList h₁).trans (cutListSummandsP_proj_permList h₂)
end

/-- Componentwise `Perm` invariance for child lists, from the `PermList`
    companion via `PermList.of_forall₂`. -/
theorem cutListSummandsP_proj_componentwise
    {cs ds : List (RoseTree α)}
    (h : List.Forall₂ RoseTree.Perm cs ds) :
    (cutListSummandsP cs).map projForest =
      (cutListSummandsP ds).map projForest :=
  cutListSummandsP_proj_permList (RoseTree.PermList.of_forall₂ h)

/-! ### Δ^ρ on Nonplanar via descent

The `cutSummandsP_proj_perm` invariance lifts `cutSummandsP`
through `Nonplanar.lift`, giving a well-defined `cutSummandsN`. The
tree-level coproduct `comulTreeN` then extends multiplicatively to a
forest-level monoid hom and finally to the algebra hom `comulAlgHomN`. -/

/-- The **Nonplanar cut-summand multiset**, defined via `Nonplanar.lift`
    using the `cutSummandsP_proj_perm` invariance. -/
noncomputable def cutSummandsN :
    Nonplanar α → Multiset (Multiset (Nonplanar α) × Nonplanar α) :=
  Nonplanar.lift (fun T => (cutSummandsP T).map projSummand)
    (fun _ _ h => cutSummandsP_proj_perm h)

@[simp] theorem cutSummandsN_mk (T : RoseTree α) :
    cutSummandsN (Nonplanar.mk T) = (cutSummandsP T).map projSummand := rfl

/-- The cut summands of a leaf: only the empty cut `(0, leaf a)`. -/
theorem cutSummandsN_leaf (a : α) :
    cutSummandsN (Nonplanar.leaf a : Nonplanar α) =
      ({((0 : Multiset (Nonplanar α)), Nonplanar.leaf a)} : Multiset _) := by
  show (cutSummandsP (RoseTree.leaf a)).map (projSummand (α := α)) = _
  rw [show RoseTree.leaf a = RoseTree.node a [] from rfl, cutSummandsP_node,
      cutListSummandsP_nil, Multiset.map_singleton, Multiset.map_singleton]
  rfl

/-- Number of Δ^ρ cut summands of `T` whose cut forest is `{T₁}` and whose
    remainder tree is `T₂` — the Δ^ρ analog of the count `c^T_{T₁,T₂}` of
    [marcolli-chomsky-berwick-2025]. -/
noncomputable def countSingleCutsRho [DecidableEq α] (T T₁ T₂ : Nonplanar α) : ℕ :=
  (cutSummandsN T).countP fun p => p.1 = ({T₁} : Multiset (Nonplanar α)) ∧ p.2 = T₂

variable {β : Type*}

/-! ### `augActionN` and `cutForestSummandsN` substrate

`cutForestSummandsN F` is the Nonplanar-level multiset of
`(cut_forest, remainder_forest)` pairs ranging over per-tree decisions
on the forest `F`. Each per-tree decision (`augActionN T`) is either
"extract `T` whole" (pair `({T}, none)`) or "recurse with a cut summand
of `T`" (pair `(s.1, some s.2)` for `s ∈ cutSummandsN T`).

Defined recursively at the Nonplanar level via `Multiset.foldr`, with
the `LeftCommutative` obligation discharged by `swap_double_combinerProj`
(the per-tree-decision swap symmetry, established for the tree-level
projection in §3 above and reused here verbatim). -/

/-- Per-tree decision multiset at the Nonplanar level: extract this tree
    whole (`({T}, none)`), or recurse into a cut summand. -/
noncomputable def augActionN (T : Nonplanar α) :
    Multiset (Multiset (Nonplanar α) × Option (Nonplanar α)) :=
  (({T} : Multiset (Nonplanar α)), Option.none) ::ₘ
    (cutSummandsN T).map (fun s => (s.1, Option.some s.2))

/-- Bridge to the tree-level `augActionP`: at a tree-level lift, `augActionN`
    agrees with `(augActionP T).map projAugAction`. -/
theorem augActionN_mk (T : RoseTree α) :
    augActionN (Nonplanar.mk T) = (augActionP T).map projAugAction := by
  unfold augActionN
  simp only [cutSummandsN_mk, augActionP_eq, Multiset.map_cons, Multiset.map_map]
  rfl

/-- Multiset.foldr combiner for `cutForestSummandsN`: combine a per-tree
    decision with the accumulated cuts of the remaining trees via the
    cartesian product and `innerCombinerProj`. -/
private noncomputable def cutForestCombinerN (T : Nonplanar α)
    (acc : Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α))) :
    Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α)) :=
  (augActionN T ×ˢ acc).map innerCombinerProj

/-- The combiner is left-commutative — discharged by `swap_double_combinerProj`,
    the per-tree-decision swap symmetry of `innerCombinerProj`. -/
private instance : LeftCommutative (cutForestCombinerN (α := α)) where
  left_comm _ _ _ := swap_double_combinerProj _ _ _

/-- The **forest cut summand multiset**: every per-tree decision tuple on
    `F : Multiset (Nonplanar α)` produces a pair `(cut_forest, remainder_forest)`,
    and `cutForestSummandsN F` enumerates them all (as a multiset). The
    public Nonplanar-level analog of `(cutListSummandsP ps).map projForest`,
    independent of the tree-level list representation. -/
noncomputable def cutForestSummandsN (F : Multiset (Nonplanar α)) :
    Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α)) :=
  Multiset.foldr cutForestCombinerN
    ({((0 : Multiset (Nonplanar α)), (0 : Multiset (Nonplanar α)))} : Multiset _) F

@[simp] theorem cutForestSummandsN_zero :
    cutForestSummandsN (0 : Multiset (Nonplanar α)) =
      ({((0 : Multiset (Nonplanar α)), (0 : Multiset (Nonplanar α)))} : Multiset _) := rfl

@[simp] theorem cutForestSummandsN_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    cutForestSummandsN (T ::ₘ F) =
      (augActionN T ×ˢ cutForestSummandsN F).map innerCombinerProj := by
  show Multiset.foldr cutForestCombinerN _ (T ::ₘ F) = _
  rw [Multiset.foldr_cons]
  rfl

/-! ### Bridges to the tree-level list representation

The tree-level substrate `cutListSummandsP` (defined on `List (RoseTree α)`)
evaluates `cutForestSummandsN` on a tree-level list rep and characterizes
cuts of a Nonplanar node (`cutSummandsN_node`). -/

/-- `cutForestSummandsN` evaluated on a tree-level list rep agrees with the
    tree-level `cutListSummandsP` projected through `projForest`. By
    induction on `ps` using `cutListSummandsP_cons_proj` and
    `augActionN_mk`. -/
theorem cutForestSummandsN_via_planar_list (ps : List (RoseTree α)) :
    cutForestSummandsN (Multiset.ofList (ps.map Nonplanar.mk)) =
      (cutListSummandsP ps).map projForest := by
  induction ps with
  | nil =>
    show cutForestSummandsN (0 : Multiset (Nonplanar α)) = _
    rw [cutForestSummandsN_zero, cutListSummandsP_nil, Multiset.map_singleton]
    rfl
  | cons p ps' ih =>
    show cutForestSummandsN (Nonplanar.mk p ::ₘ Multiset.ofList (ps'.map Nonplanar.mk)) = _
    rw [cutForestSummandsN_cons, ih, augActionN_mk]
    exact (cutListSummandsP_cons_proj p ps').symm

/-- Cuts of a node decompose via the tree-level `cutListSummandsP` projected
    through `projForest` — the tree-level-list-rep form of `cutSummandsN_node`.
    The map `(p ↦ (p.1, Nonplanar.node a p.2))` re-grafts the remainder
    children onto a fresh root with label `a`. -/
theorem cutSummandsN_node_planar_list (a : α) (ps : List (RoseTree α)) :
    cutSummandsN (Nonplanar.node a (Multiset.ofList (ps.map Nonplanar.mk))) =
      ((cutListSummandsP ps).map projForest).map
        (fun pf => (pf.1, Nonplanar.node a pf.2)) := by
  rw [Nonplanar.node_mk_tree_list]
  show (cutSummandsP (RoseTree.node a ps)).map (projSummand (α := α)) = _
  rw [cutSummandsP_node, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       ((projForest p).1, Nonplanar.node a (projForest p).2)
  rw [← Nonplanar.node_mk_tree_list]
  rfl

/-- Cuts of `Nonplanar.node a F` decompose along the per-tree decisions
    of `F`: each pair `(cf, rem) ∈ cutForestSummandsN F` gives a cut
    summand `(cf, Nonplanar.node a rem)`. The Nonplanar-level form. -/
@[simp] theorem cutSummandsN_node (a : α) (F : Multiset (Nonplanar α)) :
    cutSummandsN (Nonplanar.node a F) =
      (cutForestSummandsN F).map (fun pf => (pf.1, Nonplanar.node a pf.2)) := by
  induction F using Nonplanar.forest_inductionOn with
  | h ps => rw [cutSummandsN_node_planar_list, ← cutForestSummandsN_via_planar_list]

/-! ### `traceLeaf` — placeholder for a cut subtree -/

/-- The trace-marker placeholder leaf carrying the encoded label `b : β`. -/
def traceLeaf (b : β) : RoseTree (α ⊕ β) := .node (Sum.inr b) []

/-! ### Δ^c extraction policy -/

/-- The Δ^c extraction policy: for `Sum.inl`-rooted (non-trace)
    subtrees, extract whole leaving a single `traceLeaf (τ t)` in the
    parent's child slot. For `Sum.inr`-rooted (trace) subtrees, decline
    to extract.

    Declining at trace subtrees is required for coassociativity —
    without it, iterated Δ^c produces "trace of trace" right-channel
    terms that break the double-cut bijection — and matches
    [marcolli-chomsky-berwick-2025] Definition 1.2.2's restriction of
    cuts to accessible terms, which excludes trace placeholders. -/
def extractC (τ : RoseTree (α ⊕ β) → β) :
    RoseTree (α ⊕ β) → Option (List (RoseTree (α ⊕ β)))
  | t@(.node (Sum.inl _) _) => some [traceLeaf (τ t)]
  | .node (Sum.inr _) _ => none

@[simp] theorem extractC_inl (τ : RoseTree (α ⊕ β) → β)
    (a : α) (cs : List (RoseTree (α ⊕ β))) :
    extractC τ (RoseTree.node (Sum.inl a) cs) =
      some [traceLeaf (τ (RoseTree.node (Sum.inl a) cs))] := rfl

@[simp] theorem extractC_inr (τ : RoseTree (α ⊕ β) → β)
    (b : β) (cs : List (RoseTree (α ⊕ β))) :
    extractC τ (RoseTree.node (Sum.inr b) cs) = none := rfl

/-! ### `cutSummandsCP` — Δ^c cut enumeration via the generic `cutSummandsG`

Defined as `cutSummandsG (extractC τ)`. The generic-side simp lemmas
(`cutSummandsG_node`, `cutListSummandsG_*`, `augActionG_*`) compose with
`extractC_inl`/`extractC_inr` to give the Δ^c-specific reductions. -/

/-- The Δ^c cut summands: cuts at non-trace subtrees with trace
    placeholders, skipping cuts at trace leaves. -/
def cutSummandsCP (τ : RoseTree (α ⊕ β) → β) :
    RoseTree (α ⊕ β) → Multiset (Multiset (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β)) :=
  cutSummandsG (extractC τ)

theorem cutSummandsCP_def (τ : RoseTree (α ⊕ β) → β) (T : RoseTree (α ⊕ β)) :
    cutSummandsCP τ T = cutSummandsG (extractC τ) T := rfl

@[simp] theorem cutSummandsCP_node (τ : RoseTree (α ⊕ β) → β)
    (a : α ⊕ β) (cs : List (RoseTree (α ⊕ β))) :
    cutSummandsCP τ (RoseTree.node a cs) =
      (cutListSummandsG (extractC τ) cs).map (fun p => (p.1, .node a p.2)) := by
  rw [cutSummandsCP_def, cutSummandsG_node]
/-! ### Sanity: the trace policy on leaves -/

section Tests

/-- A leaf has exactly one cut summand: the empty cut `(0, leaf)`. -/
example (τ : RoseTree (Unit ⊕ Unit) → Unit) :
    cutSummandsCP τ (RoseTree.leaf (Sum.inl ()) : RoseTree (Unit ⊕ Unit))
      = {((0 : Multiset (RoseTree (Unit ⊕ Unit))),
          (RoseTree.leaf (Sum.inl ()) : RoseTree (Unit ⊕ Unit)))} := by
  rw [RoseTree.leaf, cutSummandsCP_node, cutListSummandsG_nil]
  rfl

/-- The trace-extract branch sits in the augmented per-child action for
    a `Sum.inl`-rooted subtree. Witness that Δ^c (placeholder leaf)
    differs from Δ^ρ (admissible-cut pruning). -/
example (τ : RoseTree (Unit ⊕ Unit) → Unit) :
    (({RoseTree.leaf (Sum.inl ())} : Multiset (RoseTree (Unit ⊕ Unit))),
      [traceLeaf (τ (RoseTree.leaf (Sum.inl ())))]) ∈
        augActionG (extractC τ)
          (RoseTree.leaf (Sum.inl ()) : RoseTree (Unit ⊕ Unit)) := by
  rw [RoseTree.leaf, augActionG_eq_some _ _ _ (extractC_inl τ () [])]
  exact Multiset.mem_cons_self _ _

/-- Trace-marker leaves are NOT extracted: `extractC τ` returns `none`,
    so the per-child action only inherits cuts from `cutSummandsG`. -/
example (b : Unit) (τ : RoseTree (Unit ⊕ Unit) → Unit) :
    augActionG (extractC τ) (traceLeaf b : RoseTree (Unit ⊕ Unit))
      = (cutSummandsG (extractC τ) (RoseTree.node (Sum.inr b) [])).map
          (fun p => (p.1, [p.2])) :=
  augActionG_eq_none _ _ (extractC_inr τ b [])

/-- The `traceLeaf` placeholder is a `Sum.inr`-labeled leaf. -/
example (b : β) : (traceLeaf b : RoseTree (α ⊕ β)).arity = 0 := rfl

example (b : β) :
    (traceLeaf b : RoseTree (α ⊕ β)).value = Sum.inr b := rfl

end Tests

/-! ## Descent of cut-summand enumeration

Mirrors `Coproduct/Pruning.lean`'s descent of `cutSummandsP`,
but for the generic `cutSummandsG` (which uses a `List`-shaped per-cut
remainder rather than `Option`). The descent applies whenever the
`extract` policy is invariant under `RoseTree.Perm` modulo
`Nonplanar.mk`. For Δ^c (`extractC (τ ∘ Nonplanar.mk)`) this follows
from `Perm.value_eq`. -/

/-! ### Pointwise projection for the G-form -/

/-- Project a `cutListSummandsG` summand to nonplanar level, discarding
    the list-order of the remainder by sending to `Multiset`. -/
private def projForestG : Multiset (RoseTree α) × List (RoseTree α) →
    Multiset (Nonplanar α) × Multiset (Nonplanar α) :=
  fun p => (p.1.map Nonplanar.mk, Multiset.ofList (p.2.map Nonplanar.mk))

/-! ### Bridge: `projSummand` factors through `projForestG` + `node` -/

/-- Applying the `cutSummandsG_node` wrapper `(p.1, .node a p.2)` then
    `projSummand` factors through `projForestG` followed by the
    `Nonplanar.node a` smart constructor. -/
private theorem projSummandG_node_factors (a : α)
    (p : Multiset (RoseTree α) × List (RoseTree α)) :
    projSummand (α := α) (p.1, .node a p.2) =
      ((projForestG p).1, Nonplanar.node a (projForestG p).2) := by
  show (p.1.map Nonplanar.mk, Nonplanar.mk (.node a p.2)) =
       (p.1.map Nonplanar.mk,
        Nonplanar.node a (Multiset.ofList (p.2.map Nonplanar.mk)))
  congr 1
  exact (Nonplanar.node_mk_tree_list a p.2).symm

/-! ### Combiner factoring

The cons case of `cutListSummandsG` adds the cut forest and concatenates
the remainder lists. At the Nonplanar level (via `projForestG`), the
remainder concatenation becomes multiset addition. -/

/-- The Nonplanar-level combiner: clean addition on both components. -/
def combinerProjG :
    (Multiset (Nonplanar α) × Multiset (Nonplanar α)) ×
    (Multiset (Nonplanar α) × Multiset (Nonplanar α)) →
    Multiset (Nonplanar α) × Multiset (Nonplanar α)
  | ((F1, m1), (F2, m2)) => (F1 + F2, m1 + m2)

/-- Pointwise: `projForestG` of an applied tree-level combiner equals
    `combinerProjG` applied to the projected pair-of-pairs. -/
private theorem projForestG_combine_apply
    (p : (Multiset (RoseTree α) × List (RoseTree α)) ×
         (Multiset (RoseTree α) × List (RoseTree α))) :
    projForestG (p.1.1 + p.2.1, p.1.2 ++ p.2.2) =
      combinerProjG (projForestG p.1, projForestG p.2) := by
  obtain ⟨⟨F1, l1⟩, ⟨F2, l2⟩⟩ := p
  show ((F1 + F2).map Nonplanar.mk,
        Multiset.ofList ((l1 ++ l2).map Nonplanar.mk)) =
       (F1.map Nonplanar.mk + F2.map Nonplanar.mk,
        Multiset.ofList (l1.map Nonplanar.mk) +
        Multiset.ofList (l2.map Nonplanar.mk))
  rw [Multiset.map_add]
  congr 1
  show Multiset.ofList ((l1 ++ l2).map Nonplanar.mk) = _
  rw [List.map_append]
  rfl

/-! ### Cartesian-product distributivity (G-form copy) -/

theorem map_prodMap_product_G {α' β' γ δ : Type*}
    (f : α' → γ) (g : β' → δ)
    (s : Multiset α') (t : Multiset β') :
    (s ×ˢ t).map (Prod.map f g) = s.map f ×ˢ t.map g := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.cons_product, Multiset.map_add, Multiset.map_map,
               Multiset.map_cons, ih]
    rfl

/-! ### Headline factoring: cons case of projected `cutListSummandsG` -/

/-- The projected `cutListSummandsG` on a cons list factors as a clean
    cartesian product at the Nonplanar level via `combinerProjG`. -/
private theorem cutListSummandsG_cons_proj
    (extract : RoseTree α → Option (List (RoseTree α)))
    (t : RoseTree α) (ts : List (RoseTree α)) :
    (cutListSummandsG extract (t :: ts)).map projForestG =
      ((augActionG extract t).map projForestG ×ˢ
       (cutListSummandsG extract ts).map projForestG).map combinerProjG := by
  rw [cutListSummandsG_cons, Multiset.map_map, ← map_prodMap_product_G,
      Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  exact projForestG_combine_apply p

/-! ### Extract-policy invariance

The hypothesis on the `extract` policy: its return value, projected
component-wise through `Nonplanar.mk`, is the same on `Perm`-equal
inputs. For Δ^c (`extractC (τ ∘ Nonplanar.mk)`) this holds because the
root label and the τ value are both `Perm`-invariant. -/

/-- An extract policy is **`Nonplanar.mk`-invariant** if its return
    value, projected componentwise through `Nonplanar.mk`, depends on
    its input only through `Nonplanar.mk`. -/
def ExtractInvariant (extract : RoseTree α → Option (List (RoseTree α))) : Prop :=
  ∀ t s : RoseTree α, Nonplanar.mk t = Nonplanar.mk s →
    (extract t).map (List.map (Nonplanar.mk (α := α))) =
      (extract s).map (List.map (Nonplanar.mk (α := α)))

/-- `augActionG`-projection invariance under the descent hypothesis. -/
private theorem augActionG_proj_eq_of_step_data
    {extract : RoseTree α → Option (List (RoseTree α))}
    (hExt : ExtractInvariant extract)
    {old new : RoseTree α}
    (h_mk : Nonplanar.mk old = Nonplanar.mk new)
    (h_proj : (cutSummandsG extract old).map projSummand =
              (cutSummandsG extract new).map projSummand) :
    (augActionG extract old).map projForestG =
      (augActionG extract new).map projForestG := by
  rw [augActionG_eq, augActionG_eq, Multiset.map_add, Multiset.map_add]
  congr 1
  · -- Extract-whole sentinel branch: invariance from hExt + h_mk.
    have hExtEq := hExt old new h_mk
    -- Branch on extract old / extract new; rewrite into goal directly.
    rcases hOld : extract old with _ | rOld
    · -- extract old = none
      rw [hOld] at hExtEq
      simp only [Option.map_none] at hExtEq
      rcases hNew : extract new with _ | rNew
      · -- both none: both sentinel branches reduce to 0
        show Multiset.map projForestG
              (match (none : Option (List (RoseTree α))) with
               | none => 0
               | some r => {((({old} : Multiset (RoseTree α))), r)}) =
             Multiset.map projForestG
              (match (none : Option (List (RoseTree α))) with
               | none => 0
               | some r => {((({new} : Multiset (RoseTree α))), r)})
        simp
      · -- new is some, but old is none — contradiction with hExtEq.
        rw [hNew] at hExtEq
        simp at hExtEq
    · -- extract old = some rOld
      rw [hOld] at hExtEq
      simp only [Option.map_some] at hExtEq
      rcases hNew : extract new with _ | rNew
      · -- old is some, new is none — contradiction.
        rw [hNew] at hExtEq
        simp at hExtEq
      · -- both some: pure equality on the singleton sentinel.
        rw [hNew] at hExtEq
        simp only [Option.map_some, Option.some.injEq] at hExtEq
        -- hExtEq : rOld.map mk = rNew.map mk
        show Multiset.map projForestG
              (match (some rOld : Option (List (RoseTree α))) with
               | none => 0
               | some r => {((({old} : Multiset (RoseTree α))), r)}) =
             Multiset.map projForestG
              (match (some rNew : Option (List (RoseTree α))) with
               | none => 0
               | some r => {((({new} : Multiset (RoseTree α))), r)})
        show Multiset.map projForestG
                ({(({old} : Multiset (RoseTree α)), rOld)} : Multiset _) =
             Multiset.map projForestG
                ({(({new} : Multiset (RoseTree α)), rNew)} : Multiset _)
        rw [Multiset.map_singleton, Multiset.map_singleton]
        show ({(({old} : Multiset (RoseTree α)).map Nonplanar.mk,
                Multiset.ofList (rOld.map Nonplanar.mk))} :
              Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α))) =
             {(({new} : Multiset (RoseTree α)).map Nonplanar.mk,
                Multiset.ofList (rNew.map Nonplanar.mk))}
        rw [Multiset.map_singleton, Multiset.map_singleton, h_mk, hExtEq]
  · -- Inherited branch: projForestG of (p.1, [p.2]) = ((projSummand p).1, ↑[(projSummand p).2])
    rw [Multiset.map_map, Multiset.map_map]
    have eq_fn :
        (projForestG (α := α)) ∘
          (fun (p : Multiset (RoseTree α) × RoseTree α) => (p.1, [p.2])) =
        (fun (s : Multiset (Nonplanar α) × Nonplanar α) =>
          (s.1, (Multiset.ofList [s.2] : Multiset (Nonplanar α)))) ∘
        (projSummand (α := α)) := by
      funext p
      rfl
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, h_proj]

/-! ### List-side projection invariants

Three theorems parallel to `cutListSummandsP_proj_at_via_augAction`,
`cutListSummandsP_proj_tail_lift`, and `cutListSummandsP_proj_perm`. -/

/-- Substituting `old` with `new` in `cutListSummandsG` is invariant
    under `projForestG` if the `augActionG`-projections agree. -/
private theorem cutListSummandsG_proj_at_via_augAction
    (extract : RoseTree α → Option (List (RoseTree α)))
    {pre post : List (RoseTree α)} {old new : RoseTree α}
    (h : (augActionG extract old).map projForestG =
         (augActionG extract new).map projForestG) :
    (cutListSummandsG extract (pre ++ old :: post)).map projForestG =
    (cutListSummandsG extract (pre ++ new :: post)).map projForestG := by
  induction pre with
  | nil =>
    show (cutListSummandsG extract (old :: post)).map projForestG =
         (cutListSummandsG extract (new :: post)).map projForestG
    rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj, h]
  | cons p pre' ih =>
    show (cutListSummandsG extract (p :: (pre' ++ old :: post))).map projForestG =
         (cutListSummandsG extract (p :: (pre' ++ new :: post))).map projForestG
    rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj, ih]

/-- Tail lift: `cutListSummandsG` is invariant under `projForestG`-equal
    tails when consed with a fixed head. -/
private theorem cutListSummandsG_proj_tail_lift
    (extract : RoseTree α → Option (List (RoseTree α)))
    (d : RoseTree α) {cs ds : List (RoseTree α)}
    (h : (cutListSummandsG extract cs).map projForestG =
         (cutListSummandsG extract ds).map projForestG) :
    (cutListSummandsG extract (d :: cs)).map projForestG =
      (cutListSummandsG extract (d :: ds)).map projForestG := by
  rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj, h]

/-! ### Swap symmetry for `combinerProjG` -/

/-- Triple-combiner symmetry: combining three projected pieces at the
    Nonplanar level is symmetric in the first two factors. -/
theorem combinerProjG_swap_args
    (a b : Multiset (Nonplanar α) × Multiset (Nonplanar α))
    (c : Multiset (Nonplanar α) × Multiset (Nonplanar α)) :
    combinerProjG (a, combinerProjG (b, c)) =
    combinerProjG (b, combinerProjG (a, c)) := by
  obtain ⟨Fa, ma⟩ := a
  obtain ⟨Fb, mb⟩ := b
  obtain ⟨Fc, mc⟩ := c
  show (Fa + (Fb + Fc), ma + (mb + mc)) = (Fb + (Fa + Fc), mb + (ma + mc))
  rw [← add_assoc, ← add_assoc, add_comm Fa Fb,
      ← add_assoc, ← add_assoc, add_comm ma mb]

/-- Doubly-applied `combinerProjG` over a triple cartesian product is
    symmetric in the first two factors. The substantive content of
    `cutListSummandsG_proj_perm`'s `swap` case. -/
theorem swap_double_combinerProjG
    (A B : Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α)))
    (C : Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α))) :
    (A ×ˢ (B ×ˢ C).map combinerProjG).map combinerProjG =
    (B ×ˢ (A ×ˢ C).map combinerProjG).map combinerProjG := by
  have lhs :
      (A ×ˢ (B ×ˢ C).map combinerProjG).map combinerProjG =
        A.bind (fun a => B.bind (fun b => C.map (fun c =>
          combinerProjG (a, combinerProjG (b, c))))) := by
    show ((A.bind fun a => ((B ×ˢ C).map combinerProjG).map (Prod.mk a))
          ).map combinerProjG = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr; intro a _
    show ((((B.bind fun b => C.map (Prod.mk b)) : Multiset _).map combinerProjG).map
            (Prod.mk a)).map combinerProjG = _
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    apply Multiset.bind_congr; intro b _
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    rfl
  have rhs :
      (B ×ˢ (A ×ˢ C).map combinerProjG).map combinerProjG =
        B.bind (fun b => A.bind (fun a => C.map (fun c =>
          combinerProjG (b, combinerProjG (a, c))))) := by
    show ((B.bind fun b => ((A ×ˢ C).map combinerProjG).map (Prod.mk b))
          ).map combinerProjG = _
    rw [Multiset.map_bind]
    apply Multiset.bind_congr; intro b _
    show ((((A.bind fun a => C.map (Prod.mk a)) : Multiset _).map combinerProjG).map
            (Prod.mk b)).map combinerProjG = _
    rw [Multiset.map_bind, Multiset.map_bind, Multiset.map_bind]
    apply Multiset.bind_congr; intro a _
    rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    rfl
  rw [lhs, rhs, Multiset.bind_bind]
  apply Multiset.bind_congr; intro b _
  apply Multiset.bind_congr; intro a _
  apply Multiset.map_congr rfl; intro c _
  exact combinerProjG_swap_args a b c

/-- The projected `cutListSummandsG` is `List.Perm`-invariant. -/
private theorem cutListSummandsG_proj_perm
    (extract : RoseTree α → Option (List (RoseTree α)))
    {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    (cutListSummandsG extract cs).map projForestG =
      (cutListSummandsG extract ds).map projForestG := by
  induction h with
  | nil => rfl
  | cons c _ ih => exact cutListSummandsG_proj_tail_lift extract c ih
  | swap c d cs =>
    rw [cutListSummandsG_cons_proj, cutListSummandsG_cons_proj,
        cutListSummandsG_cons_proj, cutListSummandsG_cons_proj]
    exact (swap_double_combinerProjG _ _ _).symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Headline: `Perm` + `PermList` recursion

Structural recursion over the mutual `Perm`/`PermList`. The `node` case lifts
the companion's list-level equality through the `Nonplanar.node a` wrapper; the
`PermList.cons` case changes the head child (via `cutSummandsG_proj_perm` and
`augActionG_proj_eq_of_step_data`) then the tail; the `PermList.swap` case is
the identical-siblings reorder (`cutListSummandsG_proj_perm`). -/

mutual
/-- Projection invariance of `cutSummandsG` under `Perm`. -/
theorem cutSummandsG_proj_perm
    {extract : RoseTree α → Option (List (RoseTree α))}
    (hExt : ExtractInvariant extract) :
    ∀ {t s : RoseTree α}, RoseTree.Perm t s →
      (cutSummandsG extract t).map projSummand =
        (cutSummandsG extract s).map projSummand
  | _, _, @RoseTree.Perm.node _ a cs ds h => by
    rw [cutSummandsG_node, cutSummandsG_node, Multiset.map_map, Multiset.map_map]
    have hL : (cutListSummandsG extract cs).map projForestG =
              (cutListSummandsG extract ds).map projForestG :=
      cutListSummandsG_proj_permList hExt h
    have eq_fn :
        (projSummand (α := α)) ∘
          (fun (p : Multiset (RoseTree α) × List (RoseTree α)) => (p.1, .node a p.2)) =
        (fun (pf : Multiset (Nonplanar α) × Multiset (Nonplanar α)) =>
          (pf.1, Nonplanar.node a pf.2)) ∘ (projForestG (α := α)) := by
      funext p
      exact projSummandG_node_factors a p
    rw [eq_fn, ← Multiset.map_map, ← Multiset.map_map, hL]
  | _, _, .trans h₁ h₂ =>
    (cutSummandsG_proj_perm hExt h₁).trans (cutSummandsG_proj_perm hExt h₂)

/-- Companion: projection invariance of `cutListSummandsG` under `PermList`. -/
private theorem cutListSummandsG_proj_permList
    {extract : RoseTree α → Option (List (RoseTree α))}
    (hExt : ExtractInvariant extract) :
    ∀ {cs ds : List (RoseTree α)}, RoseTree.PermList cs ds →
      (cutListSummandsG extract cs).map projForestG =
        (cutListSummandsG extract ds).map projForestG
  | _, _, .nil => rfl
  | _, _, @RoseTree.PermList.cons _ c d cs' ds' hcd hs => by
    have h_mk : Nonplanar.mk c = Nonplanar.mk d := Nonplanar.mk_eq_mk_iff.mpr hcd
    have h_aug : (augActionG extract c).map projForestG =
                 (augActionG extract d).map projForestG :=
      augActionG_proj_eq_of_step_data hExt h_mk (cutSummandsG_proj_perm hExt hcd)
    have step1 : (cutListSummandsG extract (c :: cs')).map projForestG =
                 (cutListSummandsG extract (d :: cs')).map projForestG :=
      cutListSummandsG_proj_at_via_augAction extract (pre := []) (post := cs') h_aug
    have step2 : (cutListSummandsG extract (d :: cs')).map projForestG =
                 (cutListSummandsG extract (d :: ds')).map projForestG :=
      cutListSummandsG_proj_tail_lift extract d (cutListSummandsG_proj_permList hExt hs)
    exact step1.trans step2
  | _, _, .swap c d cs =>
    cutListSummandsG_proj_perm extract (List.Perm.swap c d cs)
  | _, _, .trans h₁ h₂ =>
    (cutListSummandsG_proj_permList hExt h₁).trans (cutListSummandsG_proj_permList hExt h₂)
end

/-! ### Generic cut convolution: `treeCutsG` and `forestCutsG`

All cut summands of a tree as (crown forest, trunk forest) pairs — the
full cut `({T}, 0)` plus each `cuts`-summand with a singleton trunk —
and their `combinerProjG`-convolution over the trees of a forest. The
generic coproduct expands as a single sum over these
(`comulTreeNG_eq_sum`/`comulForestNG_eq_sum`, `Coproduct/WithCuts.lean`). -/

/-- All cut summands of a tree as (crown, trunk-forest) pairs: the full
    cut `({T}, 0)` plus each summand of `cuts T` with a singleton trunk. -/
noncomputable def treeCutsG
    (cuts : Nonplanar α → Multiset (Multiset (Nonplanar α) × Nonplanar α))
    (T : Nonplanar α) :
    Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α)) :=
  ({T}, 0) ::ₘ (cuts T).map (fun p => (p.1, {p.2}))

/-- Convolution-of-cuts is left-commutative (it is the symmetric
    `combinerProjG`); needed for `Multiset.foldr`. -/
instance instLeftCommConvCut : LeftCommutative
    (fun (s acc : Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α))) =>
      (s ×ˢ acc).map combinerProjG) :=
  ⟨fun a b c => swap_double_combinerProjG a b c⟩

/-- Forest-level cut enumeration: `combinerProjG`-convolution of
    `treeCutsG` over the component trees. -/
noncomputable def forestCutsG
    (cuts : Nonplanar α → Multiset (Multiset (Nonplanar α) × Nonplanar α))
    (F : Multiset (Nonplanar α)) :
    Multiset (Multiset (Nonplanar α) × Multiset (Nonplanar α)) :=
  (F.map (treeCutsG cuts)).foldr
    (fun s acc => (s ×ˢ acc).map combinerProjG) {(0, 0)}

theorem forestCutsG_zero
    (cuts : Nonplanar α → Multiset (Multiset (Nonplanar α) × Nonplanar α)) :
    forestCutsG cuts (0 : Multiset (Nonplanar α)) = {(0, 0)} := by
  unfold forestCutsG; simp

theorem forestCutsG_cons
    (cuts : Nonplanar α → Multiset (Multiset (Nonplanar α) × Nonplanar α))
    (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    forestCutsG cuts (T ::ₘ F) =
      (treeCutsG cuts T ×ˢ forestCutsG cuts F).map combinerProjG := by
  unfold forestCutsG
  rw [Multiset.map_cons, Multiset.foldr_cons]

/-- Mapping the head factor through the cartesian product commutes with a
    final map. -/
private theorem map_map_product_left {α' β' γ δ : Type*}
    (f : α' → γ) (g : γ × β' → δ) (s : Multiset α') (t : Multiset β') :
    ((s.map f) ×ˢ t).map g = (s ×ˢ t).map (fun p => g (f p.1, p.2)) := by
  conv_lhs => rw [show s.map f ×ˢ t = (s ×ˢ t).map (Prod.map f id) from by
    rw [map_prodMap_product_G, Multiset.map_id]]
  rw [Multiset.map_map]
  rfl

/-- The Option-encoded per-tree decisions `augActionN` map onto the
    forest-encoded `treeCutsG cutSummandsN` (`none` ↦ empty trunk,
    `some` ↦ singleton trunk). -/
private theorem treeCutsG_cutSummandsN (T : Nonplanar α) :
    treeCutsG cutSummandsN T =
      (augActionN T).map
        (fun d => (d.1, d.2.elim 0 (fun r => ({r} : Multiset (Nonplanar α))))) := by
  unfold treeCutsG augActionN
  simp only [Multiset.map_cons, Multiset.map_map]
  rfl

/-- The Δ^ρ forest cut enumeration is the generic convolution at
    `cuts := cutSummandsN`: `augActionN` (Option-encoded) and
    `treeCutsG cutSummandsN` (forest-encoded) enumerate the same
    per-tree decisions, and `innerCombinerProj` matches `combinerProjG`
    across the encoding. -/
theorem cutForestSummandsN_eq_forestCutsG (F : Multiset (Nonplanar α)) :
    cutForestSummandsN F = forestCutsG cutSummandsN F := by
  induction F using Multiset.induction with
  | empty => rw [cutForestSummandsN_zero, forestCutsG_zero]
  | cons T F ih =>
    rw [cutForestSummandsN_cons, forestCutsG_cons, ← ih, treeCutsG_cutSummandsN,
        map_map_product_left]
    refine Multiset.map_congr rfl (fun p _ => ?_)
    obtain ⟨⟨G, _ | r⟩, q1, q2⟩ := p
    · show (G + q1, q2) = (G + q1, 0 + q2)
      rw [zero_add]
    · show (G + q1, r ::ₘ q2) = (G + q1, {r} + q2)
      rw [Multiset.singleton_add]

/-! ### Trace specialization

The Δ^c policy `extractC (τ ∘ Nonplanar.mk)` is `ExtractInvariant`:
- For `Sum.inl _`-rooted inputs, `extractC` returns `some [traceLeaf (τ (mk t))]`.
- For `Sum.inr _`-rooted inputs, `extractC` returns `none`.

Both cases are determined by the root label and the τ value, both of
which are `Perm`-invariant. -/

/-- The Δ^c extract policy is `ExtractInvariant`. -/
theorem extractC_mkComp_invariant (τ : Nonplanar (α ⊕ β) → β) :
    ExtractInvariant (extractC (τ ∘ Nonplanar.mk)) := by
  intro t s hmk
  -- Root labels match (perm-invariant), so the extractC branches match.
  have hlabel : t.value = s.value := by
    have heq : RoseTree.Perm t s := Nonplanar.mk_eq_mk_iff.mp hmk
    exact RoseTree.Perm.value_eq heq
  -- Destructure both trees as nodes; rewrite root labels via hlabel.
  obtain ⟨at_, cs_t⟩ := t
  obtain ⟨as, cs_s⟩ := s
  simp only [RoseTree.value] at hlabel
  subst hlabel
  -- Now both have root label at_. Case-split on at_.
  cases at_ with
  | inl a =>
    show (extractC (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inl a) cs_t)).map _ =
         (extractC (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inl a) cs_s)).map _
    simp only [extractC_inl, Option.map_some]
    -- Goal: some [mk (traceLeaf (τ (mk t)))] = some [mk (traceLeaf (τ (mk s)))]
    -- Reduces to: τ (mk t) = τ (mk s), which is congrArg τ hmk.
    have : (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inl a) cs_t) =
           (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inl a) cs_s) := by
      show τ (Nonplanar.mk _) = τ (Nonplanar.mk _)
      exact congrArg τ hmk
    rw [this]
  | inr b =>
    show (extractC (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inr b) cs_t)).map _ =
         (extractC (τ ∘ Nonplanar.mk) (RoseTree.node (Sum.inr b) cs_s)).map _
    simp only [extractC_inr, Option.map_none]

/-- Δ^c cut-summand-projection invariance under `Perm`. -/
theorem cutSummandsCP_proj_perm (τ : Nonplanar (α ⊕ β) → β)
    {t s : RoseTree (α ⊕ β)} (h : RoseTree.Perm t s) :
    (cutSummandsCP (τ ∘ Nonplanar.mk) t).map projSummand =
      (cutSummandsCP (τ ∘ Nonplanar.mk) s).map projSummand :=
  cutSummandsG_proj_perm (extractC_mkComp_invariant τ) h

/-! ### Descent of `cutSummandsCP` through `Nonplanar.mk` -/

/-- The Nonplanar Δ^c cut summands, descended from `cutSummandsCP` via
    `Nonplanar.lift` using the descent invariance
    `cutSummandsCP_proj_perm`. -/
noncomputable def cutSummandsCN (τ : Nonplanar (α ⊕ β) → β) :
    Nonplanar (α ⊕ β) → Multiset (Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) :=
  Nonplanar.lift
    (fun T => (ConnesKreimer.cutSummandsCP (τ ∘ Nonplanar.mk) T).map
      ConnesKreimer.projSummand)
    (fun _ _ h => ConnesKreimer.cutSummandsCP_proj_perm τ h)

@[simp] theorem cutSummandsCN_mk (τ : Nonplanar (α ⊕ β) → β) (T : RoseTree (α ⊕ β)) :
    cutSummandsCN τ (Nonplanar.mk T) =
      (ConnesKreimer.cutSummandsCP (τ ∘ Nonplanar.mk) T).map
        ConnesKreimer.projSummand := rfl

/-- `Σ (wᵢ − 1) + card = Σ wᵢ` for tree-level forests (each `wᵢ ≥ 1`). -/
private theorem sum_map_numNodes_sub_one_add_card {γ : Type*}
    (F : Multiset (RoseTree γ)) :
    ((F.map (fun t => RoseTree.numNodes t - 1)).sum + Multiset.card F =
      (F.map RoseTree.numNodes).sum) := by
  induction F using Multiset.induction_on with
  | empty => rfl
  | cons a F ih =>
    have h1 : 1 ≤ RoseTree.numNodes a := RoseTree.numNodes_pos a
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.sum_cons, Multiset.card_cons]
    omega

/-- Edge conservation for Δ^c cut summands: the trace marker replaces
    the cut subtree by a unit-weight leaf, so crown edges plus trunk
    weight recover the tree weight exactly. Descends
    `cutSummandsG_numNodes` through `Nonplanar.mk`. -/
theorem cutSummandsCN_numNodes (τ : Nonplanar (α ⊕ β) → β)
    (T : Nonplanar (α ⊕ β)) :
    ∀ p ∈ cutSummandsCN τ T,
      Forest.edgeCount p.1 + p.2.numNodes = T.numNodes := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨T.out, (Quotient.out_eq T).symm⟩
  intro p hp
  rw [cutSummandsCN_mk] at hp
  obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hp
  rw [cutSummandsCP_def] at hq
  have hext : ∀ (t : RoseTree (α ⊕ β)) r,
      extractC (τ ∘ Nonplanar.mk) t = some r →
      (r.map RoseTree.numNodes).sum = 1 := by
    intro t r h
    cases t with
    | node x cs =>
      cases x with
      | inl a =>
        rw [extractC_inl] at h
        obtain rfl := (Option.some.injEq _ _ ▸ h :
          [traceLeaf ((τ ∘ Nonplanar.mk)
            (RoseTree.node (Sum.inl a) cs))] = r)
        simp [traceLeaf]
      | inr b =>
        rw [extractC_inr] at h
        exact absurd h (by simp)
  have h := cutSummandsG_numNodes _ hext T₀ q hq
  have hsub := sum_map_numNodes_sub_one_add_card q.1
  show Forest.edgeCount (q.1.map Nonplanar.mk) +
      (Nonplanar.mk q.2).numNodes = (Nonplanar.mk T₀).numNodes
  rw [Nonplanar.numNodes_mk, Nonplanar.numNodes_mk]
  rw [show Forest.edgeCount (q.1.map Nonplanar.mk) =
      ((q.1.map (fun t => RoseTree.numNodes t - 1)).sum) from by
    show ((q.1.map Nonplanar.mk).map
        (fun T => Nonplanar.numNodes T - 1)).sum = _
    rw [Multiset.map_map]
    rfl]
  omega

/-! ### Empty-cut uniqueness — combinatorial substrate for the per-tree counit law

For any extract policy and tree `T`, the unique cut summand of
`cutSummandsG extract T` with empty cut forest (`p.1.card = 0`) is the
empty cut `(0, T)`. By mutual structural induction with the list and
per-child cases. This is the substrate for the Δ^c per-tree counit law:
under `(counit ⊗ id)`, only this summand survives, contributing
`1 ⊗ ofTree T`. -/

/-- Helper: filter of `(s ×ˢ t)` by a conjunction predicate distributes
    into a product of filters. Used to factor the cardinality-zero
    condition on `(p.1.1 + p.2.1)` into independent conditions on each
    factor of the cartesian product. -/
private lemma filter_product_split {α₁ β₁ : Type*}
    (s : Multiset α₁) (t : Multiset β₁)
    (p : α₁ → Prop) [DecidablePred p] (q : β₁ → Prop) [DecidablePred q] :
    (s ×ˢ t).filter (fun pr => p pr.1 ∧ q pr.2) = (s.filter p) ×ˢ (t.filter q) := by
  show ((s.bind fun a => t.map (Prod.mk a)).filter (fun pr => p pr.1 ∧ q pr.2)) =
       (s.filter p).bind (fun a => (t.filter q).map (Prod.mk a))
  rw [Multiset.filter_bind, Multiset.bind_filter]
  apply Multiset.bind_congr
  intro a _
  rw [Multiset.filter_map]
  by_cases h : p a
  · rw [if_pos h]
    apply congrArg
    apply Multiset.filter_congr
    intro b _
    show (p a ∧ q b) ↔ q b
    simp [h]
  · rw [if_neg h]
    apply Multiset.eq_zero_of_forall_notMem
    intro pr hpr
    rw [Multiset.mem_map] at hpr
    obtain ⟨b, hb_mem, _hb_eq⟩ := hpr
    rw [Multiset.mem_filter] at hb_mem
    -- hb_mem.2 : ((fun pr => p pr.1 ∧ q pr.2) ∘ Prod.mk a) b = (p a ∧ q b) after β
    have hpa : p a := hb_mem.2.1
    exact h hpa

mutual

/-- The unique cut summand of `cutSummandsG extract T` with empty cut
    forest is the empty cut `(0, T)`. -/
theorem cutSummandsG_filter_empty
    (extract : RoseTree α → Option (List (RoseTree α))) :
    ∀ (T : RoseTree α),
      (cutSummandsG extract T).filter (fun p => p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), T)} : Multiset _)
  | .node a cs => by
    rw [cutSummandsG_node, Multiset.filter_map]
    -- After filter_map the inner predicate is `(·.1.card = 0) ∘ (fun p => (p.1, .node a p.2))`,
    -- which is definitionally `fun p => p.1.card = 0`. Use Multiset.filter_congr to
    -- rewrite the predicate to the form the IH expects.
    have hcongr :
        Multiset.filter
            ((fun p : Multiset (RoseTree α) × RoseTree α => p.1.card = 0) ∘
              fun p : Multiset (RoseTree α) × List (RoseTree α) => (p.1, RoseTree.node a p.2))
            (cutListSummandsG extract cs) =
        Multiset.filter (fun p => p.1.card = 0) (cutListSummandsG extract cs) := by
      apply Multiset.filter_congr
      intro p _
      rfl
    rw [hcongr, cutListSummandsG_filter_empty extract cs, Multiset.map_singleton]

/-- The unique list-cut summand of `cutListSummandsG extract cs` with
    empty cut forest is `(0, cs)`. -/
theorem cutListSummandsG_filter_empty
    (extract : RoseTree α → Option (List (RoseTree α))) :
    ∀ (cs : List (RoseTree α)),
      (cutListSummandsG extract cs).filter (fun p => p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), cs)} : Multiset _)
  | [] => by
    rw [cutListSummandsG_nil, Multiset.filter_singleton]
    rw [if_pos (show (0 : Multiset (RoseTree α)).card = 0 from Multiset.card_zero)]
  | t :: ts => by
    rw [cutListSummandsG_cons, Multiset.filter_map]
    -- Convert composed predicate to a conjunction form using card_add.
    have hcongr :
        Multiset.filter
            ((fun p : Multiset (RoseTree α) × List (RoseTree α) => p.1.card = 0) ∘
              fun p : (Multiset (RoseTree α) × List (RoseTree α)) ×
                       (Multiset (RoseTree α) × List (RoseTree α)) =>
                (p.1.1 + p.2.1, p.1.2 ++ p.2.2))
            (augActionG extract t ×ˢ cutListSummandsG extract ts) =
        Multiset.filter
            (fun p : (Multiset (RoseTree α) × List (RoseTree α)) ×
                     (Multiset (RoseTree α) × List (RoseTree α)) =>
              (fun q : Multiset (RoseTree α) × List (RoseTree α) => q.1.card = 0) p.1 ∧
              (fun q : Multiset (RoseTree α) × List (RoseTree α) => q.1.card = 0) p.2)
            (augActionG extract t ×ˢ cutListSummandsG extract ts) := by
      apply Multiset.filter_congr
      intro p _
      show (p.1.1 + p.2.1).card = 0 ↔ p.1.1.card = 0 ∧ p.2.1.card = 0
      rw [Multiset.card_add, Nat.add_eq_zero_iff]
    rw [hcongr,
        filter_product_split (augActionG extract t) (cutListSummandsG extract ts)
          (fun q : Multiset (RoseTree α) × List (RoseTree α) => q.1.card = 0)
          (fun q : Multiset (RoseTree α) × List (RoseTree α) => q.1.card = 0),
        augActionG_filter_empty extract t,
        cutListSummandsG_filter_empty extract ts,
        Multiset.product_singleton, Multiset.map_singleton]
    show ({((0 : Multiset (RoseTree α)) + (0 : Multiset (RoseTree α)),
            ([t] : List (RoseTree α)) ++ ts)} : Multiset _) = _
    rw [zero_add]
    rfl

/-- The unique per-child decision of `augActionG extract t` with empty
    cut forest is `(0, [t])` (the "recurse with empty cut" branch). -/
theorem augActionG_filter_empty
    (extract : RoseTree α → Option (List (RoseTree α))) :
    ∀ (t : RoseTree α),
      (augActionG extract t).filter (fun p => p.1.card = 0) =
        ({((0 : Multiset (RoseTree α)), [t])} : Multiset _)
  | t => by
    -- Case-split on extract t up-front using the specialized augActionG_eq_*
    -- lemmas (which avoid the inline match expression).
    cases h_ext : extract t with
    | none =>
      rw [augActionG_eq_none extract t h_ext, Multiset.filter_map]
      have hcongr :
          Multiset.filter
              ((fun p : Multiset (RoseTree α) × List (RoseTree α) => p.1.card = 0) ∘
                fun p : Multiset (RoseTree α) × RoseTree α => (p.1, [p.2]))
              (cutSummandsG extract t) =
          Multiset.filter (fun p => p.1.card = 0) (cutSummandsG extract t) := by
        apply Multiset.filter_congr
        intro p _
        rfl
      rw [hcongr, cutSummandsG_filter_empty extract t, Multiset.map_singleton]
    | some r =>
      rw [augActionG_eq_some extract t r h_ext, Multiset.filter_cons]
      -- filter cons: if pred (({t}, r)) then {({t},r)} else 0, plus filter of the tail
      rw [if_neg (by
        show ¬ ({t} : Multiset (RoseTree α)).card = 0
        rw [Multiset.card_singleton]
        decide)]
      rw [Multiset.zero_add, Multiset.filter_map]
      have hcongr :
          Multiset.filter
              ((fun p : Multiset (RoseTree α) × List (RoseTree α) => p.1.card = 0) ∘
                fun p : Multiset (RoseTree α) × RoseTree α => (p.1, [p.2]))
              (cutSummandsG extract t) =
          Multiset.filter (fun p => p.1.card = 0) (cutSummandsG extract t) := by
        apply Multiset.filter_congr
        intro p _
        rfl
      rw [hcongr, cutSummandsG_filter_empty extract t, Multiset.map_singleton]

end

/-- Nonplanar-level descent: the unique cut summand of `cutSummandsCN τ T`
    with empty cut forest is `(0, T)`. -/
theorem cutSummandsCN_filter_empty
    (τ : Nonplanar (α ⊕ β) → β) (T : Nonplanar (α ⊕ β)) :
    (cutSummandsCN τ T).filter (fun p => p.1.card = 0) =
      ({((0 : Multiset (Nonplanar (α ⊕ β))), T)} : Multiset _) := by
  obtain ⟨T₀, rfl⟩ : ∃ T₀ : RoseTree (α ⊕ β), T = Nonplanar.mk T₀ :=
    ⟨Quotient.out T, (Quotient.out_eq T).symm⟩
  rw [cutSummandsCN_mk, Multiset.filter_map]
  -- `(projSummand p).1.card = (p.1.map Nonplanar.mk).card = p.1.card`; use filter_congr.
  have hcongr :
      Multiset.filter
          ((fun p : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β) => p.1.card = 0) ∘
            projSummand (α := α ⊕ β))
          (cutSummandsCP (τ ∘ Nonplanar.mk) T₀) =
      Multiset.filter (fun p : Multiset (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β) => p.1.card = 0)
          (cutSummandsCP (τ ∘ Nonplanar.mk) T₀) := by
    apply Multiset.filter_congr
    intro p _
    show (p.1.map Nonplanar.mk).card = 0 ↔ p.1.card = 0
    rw [Multiset.card_map]
  rw [hcongr]
  show Multiset.map projSummand
        (Multiset.filter (fun p : Multiset (RoseTree (α ⊕ β)) × RoseTree (α ⊕ β) => p.1.card = 0)
          (cutSummandsG (extractC (τ ∘ Nonplanar.mk)) T₀)) = _
  rw [cutSummandsG_filter_empty (extractC (τ ∘ Nonplanar.mk)) T₀,
      Multiset.map_singleton]
  show ((((0 : Multiset (RoseTree (α ⊕ β))).map Nonplanar.mk : Multiset (Nonplanar (α ⊕ β))),
         Nonplanar.mk T₀) : Multiset (Nonplanar (α ⊕ β)) × Nonplanar (α ⊕ β)) ::ₘ 0 = _
  rw [Multiset.map_zero]
  rfl

end ConnesKreimer
