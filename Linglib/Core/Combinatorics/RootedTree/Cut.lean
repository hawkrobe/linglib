import Linglib.Core.Data.RoseTree.Nonplanar
import Linglib.Core.Data.RoseTree.DecEq
import Mathlib.Data.Multiset.Bind
import Linglib.Core.Data.RoseTree.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

open RoseTree RoseTree.Nonplanar

set_option autoImplicit false

/-!
# Admissible-cut enumeration on rose trees
[marcolli-chomsky-berwick-2025] [foissy-introduction-hopf-algebras-trees]

The combinatorics of admissible cuts, independent of the Hopf-algebra
structures built on it in `Core/Algebra/RootedTree/Coproduct/`: the
policy-parameterized enumeration (`cutSummandsG`), its Δ^ρ instance
(`cutSummandsP`), the projection to `RoseTree.Nonplanar` with its
`Perm`-invariance (`cutSummandsN`), and the single-cut count
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
extracts, leaves its deletion-remainder in the remainder list). -/

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

/-- Number of Δ^ρ cut summands of `T` whose cut forest is `{T₁}` and whose
    remainder tree is `T₂` — the Δ^ρ analog of the count `c^T_{T₁,T₂}` of
    [marcolli-chomsky-berwick-2025]. -/
noncomputable def countSingleCutsRho [DecidableEq α] (T T₁ T₂ : Nonplanar α) : ℕ :=
  (cutSummandsN T).countP fun p => p.1 = ({T₁} : Multiset (Nonplanar α)) ∧ p.2 = T₂

end ConnesKreimer
