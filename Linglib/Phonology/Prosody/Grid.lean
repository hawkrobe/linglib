import Linglib.Phonology.Prosody.Word
import Mathlib.Data.List.MinMax

/-!
# The metrical grid
[liberman-prince-1977] [prince-1983] [hayes-1995] [ito-mester-2009]

The **metrical grid** is the prominence dual of the prosodic word: a column of marks over each
syllable, taller standing for greater relative prominence (primary > secondary > unstressed),
read off a `Prosody.Tree` by the *Relative Prominence Projection Rule* ([liberman-prince-1977],
canonized in [prince-1983]) — one mark per syllable, one more per layer of headedness above it.

The fold underneath is `gridColumnsLive`, the **head-projection** (designated terminal element)
computation: each column is tagged `live` while its leaf is still the DTE of every node up to the
root. `gridColumns` is its `Prod.fst` forgetful image, *by definition* (`gridColumns_eq_live`).
This is the *determinate* bracketed grid of Halle & Vergnaud 1987 / [hayes-1995] — our `Tree`
*is* the bracketed grid, `toGrid` the forgetful map onto the pure grid. What it forgets is
*theorem*-shaped: constituency (`toGrid_not_injective`) and, under recursion,
[liberman-prince-1977]'s order-invariant culminativity (`grid_not_culminative_under_recursion`).

## Main definitions
* `gridColumnsLive` — the head-projection fold, each column tagged `live` on its DTE chain.
* `gridColumns` / `gridPeak` / `toGrid` — its forgetful image: heights, the peak (the DTE's
  prominence), the stacked rows.
* `IsContinuous` / `IsCulminative` — the grid well-formedness invariants.

## Main results
* `gridColumns_eq_live` — the **projection law**: `gridColumns` is the forgetful image of
  `gridColumnsLive` (definitional).
* `toGrid_isContinuous` — the **Continuous Column Constraint**, by construction.
* `gridColumns_toProsTree` / `foot_headRow` / `gridPeak_toProsTree` — **head-preservation**.
* `toGrid_not_injective` / `grid_not_culminative_under_recursion` — what the projection
  **forgets**.
-/

namespace Prosody

open Features.Prosody

/-! ### The grid

The grid is computed by the head-projection fold `gridColumnsLive`: each column carries a `live`
bit — whether its leaf is still the designated terminal element ([liberman-prince-1977]) of every
node up to the current root. `gridColumns` reads off the heights, its forgetful `Prod.fst` image
(`gridColumns_eq_live`, definitional); a column of height `h` is a head-projection chain of `h`
nodes. `gridPeak`/`toGrid` are the peak and the stacked rows. -/

/-- A metrical grid: rows of head-marks, bottom first (row `r`, position `i` is `true` iff
    syllable `i` reaches level `r`). -/
abbrev Grid := List (List Bool)

/-- Carry a column through one edge, tracking whether its leaf stays on a live DTE chain (a head
    edge over a live column adds a mark, any non-head edge ends the chain). -/
private def bumpLive (isHead : Bool) : ℕ × Bool → ℕ × Bool :=
  fun p => (p.1 + (if isHead && p.2 then 1 else 0), isHead && p.2)

/-- The grid with each σ-leaf column tagged `live` — whether its leaf is the designated terminal
    element of every node up to the current root (its head-projection chain is unbroken). -/
def gridColumnsLive (t : Tree) : List (ℕ × Bool) := go t where
  go : Tree → List (ℕ × Bool)
    | .node a cs => if decide (a.level = .σ) && cs.isEmpty then [(1, true)] else goList cs
  goList : List Tree → List (ℕ × Bool)
    | []      => []
    | c :: cs => (go c).map (bumpLive c.label.isHead) ++ goList cs

/-- The `goList` fold as a `flatMap` over children. -/
private theorem gridColumnsLive.goList_eq (cs : List Tree) :
    gridColumnsLive.goList cs
      = cs.flatMap (fun c => (gridColumnsLive.go c).map (bumpLive c.label.isHead)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [gridColumnsLive.goList, List.flatMap_cons, ih]

/-- **Grid-column heights** of the σ-frontier ([liberman-prince-1977]): the forgetful image of
    the live grid. A leaf's height is `1` plus its contiguous run of head-edges. -/
def gridColumns (t : Tree) : List ℕ := (gridColumnsLive t).map Prod.fst

/-- **The projection law** ([liberman-prince-1977]): the grid is the head-mark forgetful image
    of the live grid — definitional; a column of height `h` is a head-projection chain of
    `h` nodes. -/
theorem gridColumns_eq_live (t : Tree) : gridColumns t = (gridColumnsLive t).map Prod.fst := rfl

/-- The tallest column — the designated terminal element's prominence ([liberman-prince-1977]);
    `0` on an empty σ-frontier. -/
def gridPeak (t : Tree) : ℕ := (gridColumns t).foldr max 0

/-- The grid as stacked rows ([liberman-prince-1977]): row `r` marks columns exceeding `r`,
    `gridPeak t` rows in all (determinate Halle & Vergnaud / [hayes-1995] indexing). -/
def toGrid (t : Tree) : Grid :=
  (List.range (gridPeak t)).map
    (fun r => (gridColumns t).map (fun h => decide (r < h)))

/-! ### The Continuous Column Constraint -/

/-- One row is a submask of the row below (every mark above is marked below). -/
private def rowSubmask (upper lower : List Bool) : Bool :=
  (upper.zip lower).all (fun p => !p.1 || p.2)

/-- The **Continuous Column Constraint** ([prince-1983]; [hayes-1995]): no column has a gap — a
    mark at level `r` forces one at every lower level. Equivalently the rows form a chain, each a
    submask of the one below. A *theorem* of `toGrid` (`toGrid_isContinuous`), not a filter. -/
def IsContinuous (g : Grid) : Prop := g.IsChain (fun lower upper => rowSubmask upper lower = true)

instance (g : Grid) : Decidable (IsContinuous g) := by unfold IsContinuous; infer_instance

/-- **The CCC holds by construction** ([prince-1983]; [hayes-1995]): every `toGrid` grid is
    gapless — its rows are the decreasing chain `· > r`, each a submask of the one below
    (a `> r+1` mark needs a `> r` mark, i.e. `r+1 < h → r < h`). -/
theorem toGrid_isContinuous (t : Tree) : IsContinuous (toGrid t) := by
  rw [IsContinuous, toGrid, List.isChain_map, List.isChain_iff_getElem]
  intro i _
  simp only [List.getElem_range]
  rw [rowSubmask, List.zip_map', List.all_map, List.all_eq_true]
  intro h _
  by_cases hr : i + 1 < h <;> simp [hr]
  omega

/-! ### Head-preservation

Re-representing a `Foot` as a tree and reading its grid recovers its head — the depth-1 core. -/

/-- On a σ-leaf the live fold emits `[(1, true)]` (the fold's leaf step). -/
private theorem gridColumnsLive.go_syl (wt : Syllable.Weight) (hd : Bool) :
    gridColumnsLive.go (.node (Constituent.syl wt hd) []) = [(1, true)] := rfl

/-- The live grid of a non-σ node is the bumped concatenation of its children's grids — the
    fold's node step (`goList_eq` is its list step, `go_syl` its leaf step). -/
private theorem gridColumnsLive.node_of_ne_σ {a : Constituent} {cs : List Tree}
    (ha : a.level ≠ .σ) :
    gridColumnsLive (.node a cs)
      = cs.flatMap (fun c => (gridColumnsLive.go c).map (bumpLive c.label.isHead)) := by
  rw [← gridColumnsLive.goList_eq]
  simp [gridColumnsLive, gridColumnsLive.go, ha]

/-- **Head-preservation through the grid** (the foot case, generalizing
    `Foot.headFlags_toProsTree`): a foot's tree projects to columns `2` at the head σ, `1`
    elsewhere — the grid records its headedness. -/
theorem gridColumns_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    gridColumns (f.toProsTree w) = (Foot.toGrid f).map (fun b => if b then 2 else 1) := by
  rw [gridColumns, Foot.toProsTree,
      gridColumnsLive.node_of_ne_σ (a := Constituent.ft false) (by decide), List.flatMap_map]
  simp only [gridColumnsLive.go_syl, RootedTree.Planar.label_node, Constituent.syl,
    List.map_cons, List.map_nil, bumpLive]
  rw [← List.map_eq_flatMap, Foot.toGrid, List.map_map, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i = f.head <;> simp [hi]

/-- The grid's `> 1` head row equals `Foot.toGrid f`: with `Foot.headFlags_toProsTree`, the grid
    recovers the foot's head — head-preservation through the grid, not the tree. -/
theorem foot_headRow {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    (gridColumns (f.toProsTree w)).map (fun h => decide (1 < h)) = Foot.toGrid f := by
  rw [gridColumns_toProsTree, List.map_map]
  refine List.map_id'' (fun b => ?_) _
  cases b <;> rfl

/-- A foot's tree peaks at `2` ([liberman-prince-1977]): its head σ is the unique tallest column,
    one head-edge above the floor — the height member of the head-preservation family. -/
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

The projection is one-way: it drops constituency (`toGrid_not_injective`) and, under recursion,
[liberman-prince-1977]'s order-invariant culminativity (`grid_not_culminative_under_recursion`). -/

/-- **The grid loses constituency** ([liberman-prince-1977]): `toGrid` is not injective — a
    footed vs. a bare σ both give `[1]`, so the grid can't recover bracketing. -/
theorem toGrid_not_injective :
    ∃ t₁ t₂ : Tree, t₁ ≠ t₂ ∧ toGrid t₁ = toGrid t₂ :=
  ⟨.node .om [.node .ft [.node (.syl 1) []]], .node .om [.node (.syl 1) []],
    by decide, by decide⟩

/-- **Culminativity** ([liberman-prince-1977]; [hayes-1995]): exactly one column is tallest — a
    unique primary stress (one DTE per domain). -/
def IsCulminative (cols : List ℕ) : Prop :=
  (cols.filter (· = cols.foldr max 0)).length = 1

instance (cols : List ℕ) : Decidable (IsCulminative cols) := by
  unfold IsCulminative; infer_instance

/-- **Recursion breaks culminativity** ([liberman-prince-1977]): an ω-over-ω word's embedded
    weak DTE ties the matrix head (columns `[3, 3]`), leaving no unique peak — the prominence
    sibling of `toGrid_not_injective`. -/
theorem grid_not_culminative_under_recursion :
    ∃ t : Tree, IsWord t ∧ ¬ IsCulminative (gridColumns t) :=
  ⟨.node .om
      [ .node (.ft true) [.node (.syl 1 true) []],
        .node .om [.node (.ft true) [.node (.syl 1 true) []]] ],
    by decide, by decide⟩

/-- A flat word (head foot beside weak foot) keeps a unique peak (`[3, 2]`): culminativity
    without recursion. -/
theorem grid_culminative_flat :
    IsCulminative (gridColumns
      (.node .om [ .node (.ft true)  [.node (.syl 1 true) []],
                   .node (.ft false) [.node (.syl 1 true) []] ])) := by decide

/-! ### Worked example

A three-syllable ω — head foot (primary), weak foot (secondary), stray σ (unstressed) — projects
to `[3, 2, 1]` and the canonical staircase. -/

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
