import Linglib.Phonology.Prosody.Word
import Mathlib.Data.List.MinMax

/-!
# The metrical grid
[liberman-prince-1977] [prince-1983] [hayes-1995] [ito-mester-2009]

The **metrical grid** is the prominence dual of the prosodic word: a column of marks over each
syllable, taller columns standing for greater relative prominence (primary > secondary >
unstressed). It is read off a `Prosody.Tree` by the *Relative Prominence Projection Rule*
([liberman-prince-1977], canonized in [prince-1983]): one mark per syllable, plus one more for
each layer of headedness above it.

`gridColumns` makes this constructive — a σ-leaf's height is `1` plus its run of *contiguous
head-edges*. The structure underneath is `gridColumnsLive`, the **head-projection** (designated
terminal element) refinement: `gridColumns` is its head-mark-forgetful image
(`gridColumns_eq_live`). This is the *determinate* bracketed grid of Halle & Vergnaud 1987 /
[hayes-1995] — our `Tree` *is* the bracketed grid, and `toGrid` the forgetful map onto the pure
grid. What it forgets is twofold and *theorem*-shaped: it loses constituency
(`toGrid_not_injective`) and, under recursion, [liberman-prince-1977]'s order-invariant
culminativity (`grid_not_culminative_under_recursion`).

## Main definitions

* `gridColumns` / `gridPeak` / `toGrid` — the bracketed grid: column heights, the peak (the
  designated terminal element's prominence), and the stacked rows.
* `gridColumnsLive` — the head-projection refinement, each column tagged `live` on its DTE chain.
* `IsContinuous` / `IsCulminative` — the grid well-formedness invariants.

## Main results

* `gridColumns_eq_live` — the **projection law**: `gridColumns` is the forgetful image of
  `gridColumnsLive`.
* `toGrid_isContinuous` — the **Continuous Column Constraint** holds by construction.
* `gridColumns_toProsTree` / `foot_headRow` / `gridPeak_toProsTree` — **head-preservation**:
  the grid recovers a foot's head.
* `toGrid_not_injective` / `grid_not_culminative_under_recursion` — what the projection
  **forgets**: constituency, and culminativity under embedding.
-/

namespace Prosody

open Features.Prosody

/-! ### The grid -/

/-- A **metrical grid**: rows of head-marks, bottom row first. Row `r`, position `i` is
    `true` iff syllable `i` reaches grid level `r`. -/
abbrev Grid := List (List Bool)

/-- The **grid-column heights** of a tree's σ-frontier, left to right
    ([liberman-prince-1977]): each σ-leaf's height is `1` plus the contiguous run of
    head-edges above it. A top-down fold (cf. `parseInto`) threading `count`, the number of
    contiguous head-edges from the current node upward: a head child extends the run
    (`count + 1`), a non-head child resets it to `0`, and each σ-leaf emits `count + 1`. -/
def gridColumns (t : Tree) : List ℕ := go 0 t where
  go (count : ℕ) : Tree → List ℕ
    | .node a cs =>
        if decide (a.level = .σ) && cs.isEmpty then [count + 1]
        else goList count cs
  goList (count : ℕ) : List Tree → List ℕ
    | []      => []
    | c :: cs => go (if c.label.isHead then count + 1 else 0) c ++ goList count cs

private theorem gridColumns.goList_eq (count : ℕ) (cs : List Tree) :
    gridColumns.goList count cs =
      cs.flatMap (fun c => gridColumns.go (if c.label.isHead then count + 1 else 0) c) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [gridColumns.goList, List.flatMap_cons, ih]

/-- The **grid peak** ([liberman-prince-1977]): the height of the tallest column — the
    prominence of the designated terminal element, the primary-stress syllable. A tree with no
    σ-frontier has peak `0`. (`toGrid` stacks exactly `gridPeak t` rows.) -/
def gridPeak (t : Tree) : ℕ := (gridColumns t).foldr max 0

/-- The **metrical grid** of a tree ([liberman-prince-1977]): the `gridColumns` heights stacked
    into rows, row `r` marking the syllables whose column exceeds `r` (so a height-`h` column
    is marked on exactly rows `0 … h-1`), `gridPeak t` rows in all. Determinate level indexing
    à la Halle & Vergnaud 1987 / [hayes-1995]. -/
def toGrid (t : Tree) : Grid :=
  (List.range (gridPeak t)).map
    (fun r => (gridColumns t).map (fun h => decide (r < h)))

/-! ### Head-projection: the live grid

A syllable's grid height is the size of its **head-projection chain** — itself, plus every node
above it that it is the *designated terminal element* of ([liberman-prince-1977]: a node's DTE
is the leaf reached by descending through head-marked children only). `gridColumnsLive` is that
chain made visible: each column carries a `live` bit — whether the leaf is still the DTE of the
node currently folded — extended by one mark on a head edge, ended by any non-head edge.
`gridColumns` is its head-mark-forgetful image (`gridColumns_eq_live`, the **projection law**):
the live grid is the catamorphism, the bare grid its `Prod.fst` shadow. Since the head-ancestors
of a fixed leaf form a *chain* in the head-dominance order, a column of height `h` is a chain of
`h` nodes — its cardinality is that chain's `Set.chainHeight`, equivalently `Order.height + 1`. -/

/-- Carry a column through one parent edge, tracking whether its leaf is still on a live
    head-projection (DTE) chain: a head edge over a live column adds a grid mark, and any
    non-head edge breaks the chain (no further marks accrue). -/
private def bumpLive (isHead : Bool) : ℕ × Bool → ℕ × Bool :=
  fun p => (p.1 + (if isHead && p.2 then 1 else 0), isHead && p.2)

/-- `gridColumns` with each σ-leaf's column tagged by `live` — whether that leaf is the
    designated terminal element of every node up to the current root (its head-projection chain
    is still unbroken). The structural `go`/`goList` fold mirrors `gridColumns`, threading the
    bit through `bumpLive` in place of a counter, so it stays decide-reducible. -/
def gridColumnsLive (t : Tree) : List (ℕ × Bool) := go t where
  go : Tree → List (ℕ × Bool)
    | .node a cs => if decide (a.level = .σ) && cs.isEmpty then [(1, true)] else goList cs
  goList : List Tree → List (ℕ × Bool)
    | []      => []
    | c :: cs => (go c).map (bumpLive c.label.isHead) ++ goList cs

private theorem gridColumnsLive.goList_eq (cs : List Tree) :
    gridColumnsLive.goList cs
      = cs.flatMap (fun c => (gridColumnsLive.go c).map (bumpLive c.label.isHead)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [gridColumnsLive.goList, List.flatMap_cons, ih]

/-- **The projection law** ([liberman-prince-1977]): the metrical grid is the head-mark
    forgetful image of the live-annotated grid — a leaf's column is `1` plus the length of its
    head-projection chain (the run of nodes it is the DTE of). One structural induction threads
    the head-run count, which survives only on still-live columns (`bumpLive`); the count is the
    determinate Halle & Vergnaud / [hayes-1995] level. -/
theorem gridColumns_eq_live (t : Tree) :
    gridColumns t = (gridColumnsLive t).map Prod.fst := by
  suffices h : ∀ count, gridColumns.go count t
      = (gridColumnsLive.go t).map (fun p => p.1 + if p.2 then count else 0) by
    have hz := h 0
    simp only [ite_self, Nat.add_zero] at hz
    simpa [gridColumns, gridColumnsLive] using hz
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro count
    simp only [gridColumns.go, gridColumnsLive.go]
    by_cases hc : (decide (a.level = .σ) && cs.isEmpty) = true
    · rw [if_pos hc, if_pos hc]; simp; omega
    · rw [if_neg hc, if_neg hc, gridColumns.goList_eq, gridColumnsLive.goList_eq,
        List.map_flatMap]
      refine List.flatMap_congr fun c hc' => ?_
      rw [IH c hc', List.map_map]
      refine List.map_congr_left fun p _ => ?_
      obtain ⟨ph, pb⟩ := p
      simp only [Function.comp_apply, bumpLive]
      cases c.label.isHead <;> cases pb <;> simp
      all_goals omega

/-! ### The Continuous Column Constraint -/

/-- One row is a **submask** of another (the row below it): every position marked in `upper`
    is marked in `lower`. -/
private def rowSubmask (upper lower : List Bool) : Bool :=
  (upper.zip lower).all (fun p => !p.1 || p.2)

/-- The `Bool` Continuous-Column checker: each row is a submask of the row below it. -/
private def isContinuousGrid : Grid → Bool
  | []              => true
  | [_]             => true
  | lower :: upper :: rest => rowSubmask upper lower && isContinuousGrid (upper :: rest)

/-- The **Continuous Column Constraint** ([prince-1983]; [hayes-1995]): a grid has no gap in any column — if
    a syllable is marked at level `r` it is marked at every lower level. Equivalently (the
    `Bool` checker), each row is a submask of the row below it. A well-formed metrical grid
    satisfies CCC; here it is a *theorem* of `toGrid` (`toGrid_isContinuous`), not a filter. -/
def IsContinuous (g : Grid) : Prop := isContinuousGrid g

instance (g : Grid) : Decidable (IsContinuous g) :=
  inferInstanceAs (Decidable (isContinuousGrid g = true))

private theorem rowSubmask_gt (cols : List ℕ) (r : ℕ) :
    rowSubmask (cols.map (fun h => decide (r + 1 < h))) (cols.map (fun h => decide (r < h)))
      = true := by
  rw [rowSubmask, List.zip_map', List.all_map, List.all_eq_true]
  intro h _
  simp only [Function.comp_apply]
  by_cases hr : r + 1 < h
  · simp [hr, Nat.lt_of_succ_lt hr]
  · simp [hr]

private theorem isContinuousGrid_range' (F : ℕ → List Bool)
    (h : ∀ r, rowSubmask (F (r + 1)) (F r) = true) (k n : ℕ) :
    isContinuousGrid ((List.range' k n).map F) = true := by
  induction n generalizing k with
  | zero => rfl
  | succ m ih =>
    cases m with
    | zero => rfl
    | succ m' =>
      have hcons : (List.range' k (m' + 2)).map F
          = F k :: F (k + 1) :: (List.range' (k + 2) m').map F := by
        simp only [List.range'_succ, List.map_cons]
      have htail : (List.range' (k + 1) (m' + 1)).map F
          = F (k + 1) :: (List.range' (k + 2) m').map F := by
        simp only [List.range'_succ, List.map_cons]
      rw [hcons, isContinuousGrid, h k, Bool.true_and, ← htail]
      exact ih (k + 1)

/-- **The Continuous Column Constraint holds by construction.** Every grid `toGrid` produces
    has gapless columns: a height-`h` column is marked on a contiguous bottom run `0 … h-1`,
    because row `r` is `· > r`. CCC is thus a *theorem* of the projection ([prince-1983]; [hayes-1995]),
    not a stipulated well-formedness filter. -/
theorem toGrid_isContinuous (t : Tree) : IsContinuous (toGrid t) := by
  show isContinuousGrid (toGrid t) = true
  rw [toGrid, List.range_eq_range']
  exact isContinuousGrid_range' _ (fun r => rowSubmask_gt _ r) 0 _

/-! ### Head-preservation

The grid recovers a foot's head: re-representing a `Foot` as a prosodic tree and reading off
its grid gives back exactly its headedness, the foot-level (depth-1) core of the projection. -/

/-- On a σ-leaf the fold emits a single column of height `count + 1`. -/
private theorem gridColumns.go_leaf (count : ℕ) (a : Constituent) (h : a.level = .σ) :
    gridColumns.go count (.node a []) = [count + 1] := by
  simp [gridColumns.go, h]

/-- The σ-leaf case keyed on `Constituent.syl`, for rewriting under a `flatMap` binder. -/
private theorem gridColumns.go_syl (count : ℕ) (wt : Syllable.Weight) (hd : Bool) :
    gridColumns.go count (.node (Constituent.syl wt hd) []) = [count + 1] :=
  gridColumns.go_leaf count _ rfl

/-- **Head-preservation through the grid** (the depth-1 / foot case, generalizing
    `Foot.headFlags_toProsTree`). A foot's prosodic tree projects to columns of height `2` at
    the head σ and `1` elsewhere: the grid records exactly the foot's headedness. -/
theorem gridColumns_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    gridColumns (f.toProsTree w) = (Foot.toGrid f).map (fun b => if b then 2 else 1) := by
  have hroot : gridColumns (f.toProsTree w)
      = gridColumns.goList 0 ((List.finRange f.syllables.length).map
          (fun i => (.node (Constituent.syl (w (f.syllables.get i)) (decide (i = f.head)))
            [] : Tree))) := rfl
  rw [hroot, gridColumns.goList_eq, List.flatMap_map]
  simp only [gridColumns.go_syl, RootedTree.Planar.label_node, Constituent.syl]
  rw [← List.map_eq_flatMap, Foot.toGrid, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  by_cases hi : i = f.head <;> simp [hi]

/-- The grid's **head row** recovers the foot's head profile: a foot's σ reaches grid level
    `2` exactly at its head, so the `> 1` row of `toGrid` equals `Foot.toGrid f`. Combined
    with `Foot.headFlags_toProsTree` (`Foot.toGrid f` = the prosodic tree's σ-leaf head
    flags), the grid's head row equals those head flags — head-preservation, now through the
    grid projection rather than the tree re-representation. -/
theorem foot_headRow {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    (gridColumns (f.toProsTree w)).map (fun h => decide (1 < h)) = Foot.toGrid f := by
  rw [gridColumns_toProsTree, List.map_map]
  refine List.map_id'' (fun b => ?_) _
  cases b <;> rfl

/-- **Head-preservation through the grid peak** ([liberman-prince-1977]): the height-axis
    member of the head-preservation family, the foot-case analogue of `gridColumns_toProsTree`.
    A single foot's prosodic tree peaks at `2` — its head σ is the unique tallest column, one
    head-edge above the σ floor of `1` (column height = head-chain length, read at the peak). -/
theorem gridPeak_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    gridPeak (f.toProsTree w) = 2 := by
  rw [gridPeak, gridColumns_toProsTree]
  refine Nat.le_antisymm (List.max_le_of_forall_le _ 2 ?_) (List.le_max_of_le' 0 ?_ le_rfl)
  · rintro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  · exact List.mem_map.mpr ⟨true,
      List.mem_map.mpr ⟨f.head, List.mem_finRange _, decide_eq_true_eq.mpr rfl⟩, rfl⟩

/-! ### What the grid forgets

The projection is **one-way**. Distinct trees share a grid (`toGrid_not_injective`): the bare
grid records prominence, not bracketing — [hayes-1995]'s bracketed tree keeps the constituency
`toGrid` drops. And the determinate grid drops [liberman-prince-1977]'s order-invariant
**culminativity**: the RPPR keeps relative prominence ordered under embedding (one DTE per
domain), but under prosodic recursion (ω over ω) a weak embedded word re-projects its own DTE to
the matrix head's height (`grid_not_culminative_under_recursion`), leaving no unique peak.
Relating the bracketed grid to the pure strata surfaces both incompatibilities. -/

/-- **The grid loses constituency** ([liberman-prince-1977]). `toGrid` is not injective:
    distinct prosodic trees can project to the same grid. Witnesses — a single unstressed σ
    parsed into a foot vs. left bare under ω — share the column profile `[1]`, so the grid
    cannot recover whether a syllable is footed. Relating the grid to the bracketed tree
    surfaces the incompatibility: the grid encodes prominence, not bracketing. -/
theorem toGrid_not_injective :
    ∃ t₁ t₂ : Tree, t₁ ≠ t₂ ∧ toGrid t₁ = toGrid t₂ :=
  ⟨.node .om [.node .ft [.node (.syl 1) []]], .node .om [.node (.syl 1) []],
    by decide, by decide⟩

/-- **Culminativity** ([liberman-prince-1977]; [hayes-1995]): a grid designates a unique
    primary stress — exactly one column attains the maximal height. The defining property of a
    well-formed prominence domain (one designated terminal element per word). -/
def IsCulminative (cols : List ℕ) : Prop :=
  (cols.filter (· = cols.foldr max 0)).length = 1

instance (cols : List ℕ) : Decidable (IsCulminative cols) := by
  unfold IsCulminative; infer_instance

/-- A recursive prosodic word, ω over ω ([ito-mester-2009]): a head foot and a weak embedded
    word, each projecting a head σ. -/
private def recursiveWord : Tree :=
  .node .om
    [ .node (.ft true) [.node (.syl 1 true) []],
      .node .om [.node (.ft true) [.node (.syl 1 true) []]] ]

/-- A flat word: a head foot beside a weak foot. -/
private def flatWord : Tree :=
  .node .om
    [ .node (.ft true)  [.node (.syl 1 true) []],
      .node (.ft false) [.node (.syl 1 true) []] ]

/-- **Recursion breaks culminativity** ([liberman-prince-1977]). The RPPR keeps relative
    prominence ordered under embedding, designating one DTE per domain; the determinate
    bracketed grid does not. A well-formed ω-over-ω word's weak embedded word re-projects its
    own DTE to the matrix head's height (`gridColumns recursiveWord = [3, 3]`), leaving two
    equal peaks — no unique primary stress. The prominence sibling of `toGrid_not_injective`:
    relating the bracketed grid to [liberman-prince-1977]'s strata surfaces the incompatibility. -/
theorem grid_not_culminative_under_recursion :
    ∃ t : Tree, IsWord t ∧ ¬ IsCulminative (gridColumns t) :=
  ⟨recursiveWord, by decide, by decide⟩

/-- A flat word keeps a single strongest column (`gridColumns flatWord = [3, 2]`): the head
    foot's σ is the unique DTE, so culminativity holds without recursion. -/
theorem grid_culminative_flat : IsCulminative (gridColumns flatWord) := by decide

/-! ### Worked example

A three-syllable ω with a head foot (primary), a non-head foot (secondary), and a stray σ
(unstressed) projects to the column profile `[3, 2, 1]` and the staircase grid — the
canonical Liberman & Prince display. -/

private def exWord : Tree :=
  .node .om
    [ .node (.ft true)  [.node (.syl 1 true) []],
      .node (.ft false) [.node (.syl 1 true) []],
      .node (.syl 1 false) [] ]

example : gridColumns exWord = [3, 2, 1] := by decide
example : gridPeak exWord = 3 := by decide
example : toGrid exWord =
    [[true, true, true], [true, true, false], [true, false, false]] := by decide
example : IsContinuous (toGrid exWord) := by decide

end Prosody
