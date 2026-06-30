import Linglib.Phonology.Prosody.Word
import Mathlib.Data.List.MinMax

/-!
# The metrical grid
[liberman-prince-1977] [prince-1983] [hayes-1995] [ito-mester-2009]

The **metrical grid** is the prominence dual of the prosodic word: a column of marks over each
syllable, taller standing for greater relative prominence (primary > secondary > unstressed),
read off a `Prosody.Tree` by the *Relative Prominence Projection Rule* ([liberman-prince-1977],
canonized in [prince-1983]) — one mark per syllable, one more per layer of headedness above it.

The fold underneath is `gridColumnsLive`, the **head-projection** computation: each `Column` is
tagged `live` while its leaf is still the **head terminal** (Liberman & Prince's *designated
terminal element*) of every node up to the root. `gridColumns` is its height projection, *by
definition* (`gridColumns_eq_live`); `headHeights`/`headTerminals` read the live columns' heights
and leaves. This is the *determinate* bracketed grid of Halle & Vergnaud 1987 / [hayes-1995] — our
`Tree` *is* the bracketed grid, `toGrid` the forgetful map onto the pure grid. What it forgets is
*theorem*-shaped: constituency (`toGrid_not_injective`) and, under recursion,
[liberman-prince-1977]'s order-invariant culminativity (`grid_not_culminative_under_recursion`).

## Main definitions
* `gridColumnsLive` — the head-projection fold; each `Column` carries its leaf, height, and `live`
  bit (whether its leaf is a head terminal).
* `gridColumns` / `gridPeak` / `toGrid` — its height image: heights, the peak (the head terminal's
  prominence), the stacked rows.
* `headTerminals` / `headHeights` / `IsHeaded` — the head terminals (DTEs) as nodes / as heights,
  and the unique-head-terminal predicate.
* `IsContinuous` / `IsCulminative` — the grid well-formedness invariants.

## Main results
* `gridColumns_eq_live` — the **projection law**: `gridColumns` is the height image of
  `gridColumnsLive` (definitional).
* `toGrid_isContinuous` — the **Continuous Column Constraint**, by construction.
* `gridColumns_toProsTree` / `foot_headRow` / `gridPeak_toProsTree` — **head-preservation**.
* `headHeights_eq_peak` — the **peak is the head terminal** on a non-recursive headed word.
* `toGrid_not_injective` / `grid_not_culminative_under_recursion` — what the projection
  **forgets**.
-/

namespace Prosody

/-! ### The grid -/

/-- A metrical grid: rows of head-marks, bottom first (row `r`, position `i` is `true` iff
    syllable `i` reaches level `r`). -/
abbrev Grid := List (List Bool)

/-- One metrical-grid column: a σ-leaf, its head-projection height, and `live` — whether that leaf
    is the head of every node up to the root (its head-projection chain is unbroken). -/
structure Column where
  /-- The σ-leaf carrying the column. -/
  leaf : Tree
  /-- The column height: `1` plus the contiguous run of head-edges above the leaf. -/
  height : ℕ
  /-- Whether the head-projection chain reaches the root — the leaf is a **head terminal**. -/
  live : Bool

/-- Carry a column through one edge: the leaf passes through, a head edge over a live column adds a
    mark and stays live, any non-head edge ends the chain. -/
private def bumpLive (isHead : Bool) : Column → Column :=
  fun c => { c with height := c.height + (if isHead && c.live then 1 else 0), live := isHead && c.live }

/-- The live grid: each σ-leaf column carries its leaf, height, and `live` bit — whether the leaf
    is the head terminal (Liberman & Prince's *designated terminal element*) of every node up to
    the root. The single fold the grid, its heights, its peak, and the head terminals
    (`gridColumns`/`headHeights`/`headTerminals`) all project from. -/
def gridColumnsLive (t : Tree) : List Column := go t where
  go : Tree → List Column
    | .node a cs => if a.isSyl && cs.isEmpty then [⟨.node a cs, 1, true⟩] else goList cs
  goList : List Tree → List Column
    | []      => []
    | c :: cs => (go c).map (bumpLive c.label.isHead) ++ goList cs

/-- The `goList` fold as a `flatMap` over children. -/
private theorem gridColumnsLive.goList_eq (cs : List Tree) :
    gridColumnsLive.goList cs
      = cs.flatMap (fun c => (gridColumnsLive.go c).map (bumpLive c.label.isHead)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [gridColumnsLive.goList, List.flatMap_cons, ih]

/-- **Grid-column heights** of the σ-frontier ([liberman-prince-1977]): the height projection of
    the live grid. A leaf's height is `1` plus its contiguous run of head-edges. -/
def gridColumns (t : Tree) : List ℕ := (gridColumnsLive t).map (·.height)

/-- **The projection law** ([liberman-prince-1977]): the grid is the height projection of the live
    grid — definitional; a column of height `h` is a head-projection chain of `h` nodes. -/
theorem gridColumns_eq_live (t : Tree) : gridColumns t = (gridColumnsLive t).map (·.height) := rfl

/-- The tallest column — the head terminal's prominence ([liberman-prince-1977]); `0` on an empty
    σ-frontier. -/
def gridPeak (t : Tree) : ℕ := (gridColumns t).foldr max 0

/-- The **head-terminal prominences** ([liberman-prince-1977]): the heights of the *live* columns
    — the σ-positions whose head-projection chain reaches the root. The height projection of
    `gridColumnsLive`'s live sublist (cf. `gridColumns`, its full image; `headTerminals`, the same
    sublist's node projection). A headed word has exactly one; under recursion it can sit *below*
    the tallest column (`head_below_peak_under_recursion`). -/
def headHeights (t : Tree) : List ℕ := ((gridColumnsLive t).filter (·.live)).map (·.height)

/-- A tree is **headed** when it has a unique head terminal — one unbroken head-projection chain to
    the root (Liberman & Prince's Culminativity, head version; strictly stronger than
    `IsCulminative`, which sees only heights). -/
def IsHeaded (t : Tree) : Prop := (headHeights t).length = 1

instance (t : Tree) : Decidable (IsHeaded t) := by unfold IsHeaded; infer_instance

/-- The **head terminals** ([liberman-prince-1977]): the σ-leaves whose head-projection chain
    reaches the root — Liberman & Prince's *designated terminal elements* as nodes. The node
    projection of `gridColumnsLive`'s live sublist — the very sublist `headHeights` reads for
    heights, so the two are bijective by construction. -/
def headTerminals (t : Tree) : List Tree := ((gridColumnsLive t).filter (·.live)).map (·.leaf)

/-- The head terminal as one element, when the word is headed (`IsHeaded`); `none` otherwise. -/
def headTerminal (t : Tree) : Option Tree := (headTerminals t).head?

/-- **Headedness read on the node image** ([liberman-prince-1977]): a tree is headed iff it has a
    single head terminal. `headTerminals` and `headHeights` are the node and height projections of
    one live sublist, so this is `IsHeaded` re-read, not a second notion. -/
theorem isHeaded_iff_headTerminals (t : Tree) : IsHeaded t ↔ (headTerminals t).length = 1 := by
  simp only [IsHeaded, headHeights, headTerminals, List.length_map]

/-- **Head terminal, declaratively** ([liberman-prince-1977]): `leaf` is a head terminal of `t`
    when it is a σ-leaf reached from the root by an **all-head descent** — Liberman & Prince's
    *designated terminal element* as a relation rather than a computed list. The decidable grid
    fold realizes it (`mem_headTerminals_iff`). -/
inductive IsHeadTerminal : Tree → Tree → Prop
  | leaf (wt hd) :
      IsHeadTerminal (.node (Constituent.syl wt hd) []) (.node (Constituent.syl wt hd) [])
  | head {a : Constituent} {cs : List Tree} {c leaf : Tree} :
      c ∈ cs → c.label.isHead = true → IsHeadTerminal c leaf → IsHeadTerminal (.node a cs) leaf

/-- A bumped column keeps its leaf — `bumpLive` only retags height and liveness. -/
private theorem bumpLive_leaf (b : Bool) (c : Column) : (bumpLive b c).leaf = c.leaf := rfl

/-- A bumped column is live iff the edge is a head edge over a still-live column. -/
private theorem bumpLive_live (b : Bool) (c : Column) :
    (bumpLive b c).live = (b && c.live) := rfl

/-- The live grid of a node that is **not** a σ-leaf — either a non-σ node, or a σ-labelled node
    that still has children — is the bumped concatenation of its children's grids. The general
    node step (`gridColumnsLive.node_of_ne_σ` is the `a.level ≠ .σ` special case). -/
private theorem gridColumnsLive.node_else {a : Constituent} {cs : List Tree}
    (h : ¬ (a.isSyl = true ∧ cs = [])) :
    gridColumnsLive (.node a cs)
      = cs.flatMap (fun c => (gridColumnsLive.go c).map (bumpLive c.label.isHead)) := by
  have hcond : (a.isSyl && cs.isEmpty) = false := by
    rcases Bool.eq_false_or_eq_true (a.isSyl && cs.isEmpty) with h' | h'
    · rw [Bool.and_eq_true, List.isEmpty_iff] at h'
      exact absurd h' h
    · exact h'
  have hgo : gridColumnsLive (.node a cs) = gridColumnsLive.goList cs := by
    simp [gridColumnsLive, gridColumnsLive.go, hcond]
  rw [hgo, gridColumnsLive.goList_eq]

/-- A leaf lies in a non-σ-leaf node's head terminals iff some **head** child carries it as a head
    terminal: the live-column bookkeeping of `gridColumnsLive` pushed one edge down. The recursive
    content of `mem_headTerminals_iff`. -/
private theorem mem_headTerminals_node_else {a : Constituent} {cs : List Tree} {leaf : Tree}
    (hcond : ¬ (a.isSyl = true ∧ cs = [])) :
    leaf ∈ headTerminals (.node a cs)
      ↔ ∃ c ∈ cs, c.label.isHead = true ∧ leaf ∈ headTerminals c := by
  rw [headTerminals, gridColumnsLive.node_else hcond]
  constructor
  · intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨col, hcolf, hleaf⟩ := hmem
    rw [List.mem_filter, List.mem_flatMap] at hcolf
    obtain ⟨⟨c, hc, hcolm⟩, hlive⟩ := hcolf
    rw [List.mem_map] at hcolm
    obtain ⟨col0, hcol0, rfl⟩ := hcolm
    rw [bumpLive_live, Bool.and_eq_true] at hlive
    rw [bumpLive_leaf] at hleaf
    refine ⟨c, hc, hlive.1, ?_⟩
    rw [headTerminals, List.mem_map]
    exact ⟨col0, List.mem_filter.mpr ⟨hcol0, hlive.2⟩, hleaf⟩
  · rintro ⟨c, hc, hhead, hmem⟩
    rw [headTerminals, List.mem_map] at hmem
    obtain ⟨col0, hcol0f, hleaf⟩ := hmem
    rw [List.mem_filter] at hcol0f
    rw [List.mem_map]
    refine ⟨bumpLive c.label.isHead col0, ?_, ?_⟩
    · rw [List.mem_filter, List.mem_flatMap]
      refine ⟨⟨c, hc, ?_⟩, ?_⟩
      · rw [List.mem_map]; exact ⟨col0, hcol0f.1, rfl⟩
      · rw [bumpLive_live, Bool.and_eq_true]; exact ⟨hhead, hcol0f.2⟩
    · rw [bumpLive_leaf]; exact hleaf

/-- **The grid fold realizes the head terminal** ([liberman-prince-1977]): a leaf is in
    `headTerminals t` iff `IsHeadTerminal t leaf`. The decidable head-projection fold computes the
    declarative all-head descent — the spec↔implementation bridge. -/
theorem mem_headTerminals_iff {t leaf : Tree} :
    leaf ∈ headTerminals t ↔ IsHeadTerminal t leaf := by
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    by_cases hcond : a.isSyl = true ∧ cs = []
    · obtain ⟨hσ, rfl⟩ := hcond
      cases a with
      | syl w hd =>
        have hht : headTerminals (.node (Constituent.syl w hd) []) = [.node (Constituent.syl w hd) []] := by
          simp [headTerminals, gridColumnsLive, gridColumnsLive.go, Constituent.isSyl]
        rw [hht, List.mem_singleton]
        constructor
        · rintro rfl
          exact .leaf w hd
        · intro h
          cases h with
          | leaf wt hd => rfl
          | head hc _ _ => exact absurd hc List.not_mem_nil
      | ft hd => simp [Constituent.isSyl] at hσ
      | om => simp [Constituent.isSyl] at hσ
      | ph => simp [Constituent.isSyl] at hσ
    · rw [mem_headTerminals_node_else hcond]
      constructor
      · rintro ⟨c, hc, hhead, hmem⟩
        exact .head hc hhead ((IH c (by simpa using hc)).mp hmem)
      · intro h
        cases h with
        | leaf wt hd => exact absurd ⟨rfl, rfl⟩ hcond
        | head hc hhead hsub =>
          exact ⟨_, hc, hhead, (IH _ (by simpa using hc)).mpr hsub⟩

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

/-- On a σ-leaf the live fold emits the leaf at height `1`, live (the fold's leaf step). -/
private theorem gridColumnsLive.go_syl (wt : Syllable.Weight) (hd : Bool) :
    gridColumnsLive.go (.node (Constituent.syl wt hd) [])
      = [⟨.node (Constituent.syl wt hd) [], 1, true⟩] := rfl

/-- The live grid of a non-σ node is the bumped concatenation of its children's grids — the
    fold's node step (`goList_eq` is its list step, `go_syl` its leaf step). -/
private theorem gridColumnsLive.node_of_ne_σ {a : Constituent} {cs : List Tree}
    (ha : a.isSyl = false) :
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
  simp only [gridColumnsLive.go_syl, RootedTree.Planar.label_node, Constituent.isHead,
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
    unique primary stress (one head terminal per domain). -/
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

/-! ### The word peak and the head terminal

The ω analogue of `gridPeak_toProsTree`: on a non-recursive headed word the grid peak *is* the
head terminal (Liberman & Prince's designated terminal element) — primary stress reads off the
grid. Recursion is the sole obstruction, and (unlike the foot) culminativity alone is not enough. -/

/-- `isWordTree.goList` as a `List.all` over children — the list step of the Layeredness
    checker (cf. `gridColumnsLive.goList_eq`). -/
private theorem isWordTree.goList_all (cs : List Tree) :
    isWordTree.goList cs
      = cs.all (fun c => isFootTree c || isWordTree.go c
          || (c.label.isSyl && c.children.isEmpty)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [isWordTree.goList, List.all_cons, ih]

/-- On a non-recursive word (`IsWord` + `noRec = 0`) the root is an ω each daughter of which
    is either a well-formed foot or a stray σ-leaf — the ω-over-ω arm of `isWordTree` is killed
    by `noRec = 0`. This is the depth-≤-2 structure `headHeights_eq_peak` rests on. -/
private theorem isWord_children {a : Constituent} {cs : List Tree}
    (hw : IsWord (.node a cs)) (hr : noRec (.node a cs) = 0) :
    a.isOm = true ∧ ∀ c ∈ cs, isFootTree c = true ∨ (c.label.isSyl = true ∧ c.children = []) := by
  simp only [IsWord, isWordTree, isWordTree.go, Bool.and_eq_true,
    isWordTree.goList_all, List.all_eq_true] at hw
  obtain ⟨ha, hall⟩ := hw
  obtain rfl : a = .om := by cases a <;> simp_all [Constituent.isOm]
  have hr' : (cs.filter (fun c => Constituent.sameLevel c.label .om)).length = 0 := by
    have e : noRec (.node (.om : Constituent) cs)
        = (cs.filter (fun c => Constituent.sameLevel c.label .om)).length + noRec.goList cs := rfl
    rw [hr] at e; omega
  have hnoω : ∀ c ∈ cs, Constituent.sameLevel c.label .om = false := by
    intro c hc
    by_contra h
    rw [Bool.not_eq_false] at h
    have hmem : c ∈ cs.filter (fun c => Constituent.sameLevel c.label .om) := by
      rw [List.mem_filter]; exact ⟨hc, h⟩
    rw [List.length_eq_zero_iff] at hr'
    rw [hr'] at hmem; exact List.not_mem_nil hmem
  refine ⟨ha, fun c hc => ?_⟩
  have hdisj := hall c hc
  have hsl := hnoω c hc
  obtain ⟨cl, ccs⟩ := c
  simp only [RootedTree.Planar.label_node] at hsl
  have hcω : cl.isOm = false := by
    cases cl <;> simp_all [Constituent.sameLevel, Constituent.isOm]
  rw [show isWordTree.go (.node cl ccs)
        = (cl.isOm && isWordTree.goList ccs) from rfl, hcω] at hdisj
  simp only [Bool.false_and, Bool.or_false, Bool.or_eq_true, Bool.and_eq_true,
    RootedTree.Planar.children_node, List.isEmpty_iff,
    RootedTree.Planar.label_node] at hdisj ⊢
  rcases hdisj with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The live fold emits any σ-labelled childless node at height `1`, live — the general form
    of `gridColumnsLive.go_syl`. -/
private theorem gridColumnsLive.go_leaf {sb : Constituent} (h : sb.isSyl = true) :
    gridColumnsLive.go (.node sb []) = [⟨.node sb [], 1, true⟩] := by
  simp [gridColumnsLive.go, h]

/-- **Bounded columns** under Layeredness + No-Recursion: on a word with `noRec = 0` every grid
    column has height `≤ 3`, every *live* column height `≥ 2`, and any height-`3` column is live
    (the head-foot's head σ). The depth-≤-2 structure, pinned per column — the engine of
    `headHeights_eq_peak`. -/
private theorem gridColumnsLive_bounded {t : Tree} (hw : IsWord t) (hr : noRec t = 0) :
    ∀ col ∈ gridColumnsLive t,
      col.height ≤ 3 ∧ (col.live = true → 2 ≤ col.height) ∧ (col.height = 3 → col.live = true) := by
  obtain ⟨a, cs⟩ := t
  obtain ⟨ha, hchild⟩ := isWord_children hw hr
  intro col hcol
  rw [gridColumnsLive.node_of_ne_σ (a := a) (Constituent.isSyl_eq_false_of_isOm ha),
    List.mem_flatMap] at hcol
  obtain ⟨c, hc, hcol⟩ := hcol
  rw [List.mem_map] at hcol
  obtain ⟨col0, hcol0, rfl⟩ := hcol
  rcases hchild c hc with hfoot | ⟨hlev, hchildren⟩
  · obtain ⟨cl, ccs⟩ := c
    simp only [isFootTree, Bool.and_eq_true] at hfoot
    obtain ⟨⟨hclf, _⟩, hleaves⟩ := hfoot
    have hgoc : gridColumnsLive.go (.node cl ccs)
        = ccs.flatMap (fun s => (gridColumnsLive.go s).map (bumpLive s.label.isHead)) :=
      gridColumnsLive.node_of_ne_σ (a := cl) (Constituent.isSyl_eq_false_of_isFt hclf)
    rw [hgoc, List.mem_flatMap] at hcol0
    obtain ⟨s, hs, hcol0⟩ := hcol0
    have hsleaf := List.all_eq_true.mp hleaves s hs
    obtain ⟨sb, sds⟩ := s
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hsleaf
    obtain ⟨hsσ, hsds⟩ := hsleaf
    subst hsds
    rw [gridColumnsLive.go_leaf hsσ, List.map_cons, List.map_nil, List.mem_singleton] at hcol0
    subst hcol0
    cases hclh : cl.isHead <;> cases hsbh : sb.isHead <;>
      simp [bumpLive, RootedTree.Planar.label_node, hclh, hsbh]
  · obtain ⟨cb, cbs⟩ := c
    simp only [RootedTree.Planar.label_node] at hlev
    simp only [RootedTree.Planar.children_node] at hchildren
    subst hchildren
    rw [gridColumnsLive.go_leaf hlev, List.mem_singleton] at hcol0
    subst hcol0
    cases hcbh : cb.isHead <;>
      simp [bumpLive, RootedTree.Planar.label_node, hcbh]

/-- **The peak is the head terminal** ([liberman-prince-1977]; the ω analogue of
    `gridPeak_toProsTree`): in a non-recursive headed *word* the head terminal's prominence *is*
    the grid peak, so primary stress reads off the grid. Both **Layeredness** (`IsWord`) and
    **No-Recursion** are essential — without Layeredness a deep dead column can outrank the head
    terminal (`head_below_peak_unlayered`), and recursion divorces the two
    (`head_below_peak_under_recursion`); culminativity alone suffices for neither. -/
theorem headHeights_eq_peak {t : Tree} (hw : IsWord t) (hh : IsHeaded t) (hr : noRec t = 0) :
    headHeights t = [gridPeak t] := by
  have facts := gridColumnsLive_bounded hw hr
  rw [IsHeaded, headHeights, List.length_map] at hh
  obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hh
  have hc0mf : c0 ∈ (gridColumnsLive t).filter (·.live) := by rw [hc0]; simp
  rw [List.mem_filter] at hc0mf
  obtain ⟨hc0mem, hc0live⟩ := hc0mf
  have hpeak : c0.height = gridPeak t := by
    rw [gridPeak, gridColumns]
    refine le_antisymm
      (List.le_max_of_le' 0 (List.mem_map.mpr ⟨c0, hc0mem, rfl⟩) (le_refl c0.height))
      (List.max_le_of_forall_le _ c0.height fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨col, hcm, rfl⟩ := hx
    obtain ⟨_, hc0ge2, _⟩ := facts c0 hc0mem
    obtain ⟨hle3, _, h3⟩ := facts col hcm
    rcases (show col.height ≤ 2 ∨ col.height = 3 by omega) with h2 | h3eq
    · exact le_trans h2 (hc0ge2 hc0live)
    · have hmem : col ∈ (gridColumnsLive t).filter (·.live) :=
        List.mem_filter.mpr ⟨hcm, h3 h3eq⟩
      rw [hc0, List.mem_singleton] at hmem
      exact le_of_eq (congrArg Column.height hmem)
  rw [headHeights, hc0]; simp [hpeak]

/-- **Recursion divorces the peak from the head terminal** ([ito-mester-2009]): even a
    *culminative*, headed ω-over-ω word can peak on a recessive embedded column, not its head
    terminal. Here the head stray-σ is live at `2`, while the embedded word's head-σ chains to `3`
    before dying at the outer-ω edge — columns `[2, 3]`, peak `3`, but `headHeights = [2]`. The
    sharper sibling of `grid_not_culminative_under_recursion`: it is why `headHeights_eq_peak` must
    assume No-Recursion rather than `IsCulminative`. -/
theorem head_below_peak_under_recursion :
    ∃ t : Tree, IsWord t ∧ IsHeaded t ∧ IsCulminative (gridColumns t)
      ∧ headHeights t ≠ [gridPeak t] :=
  ⟨.node .om [ .node (.syl 1 true) [],
               .node .om [.node (.ft true) [.node (.syl 1 true) []]] ],
    by decide, by decide, by decide, by decide⟩

/-- **Layeredness is essential too**: an anti-Layered tree (`ω` dominating a `φ`!) hides a
    height-`3` *dead* column under a non-head edge beside a height-`2` live head terminal —
    `IsHeaded` and `noRec = 0` both hold, yet `headHeights = [2] ≠ [3] = [gridPeak]`. The
    Layeredness sibling of `head_below_peak_under_recursion`, and why `headHeights_eq_peak` needs
    `IsWord`. -/
theorem head_below_peak_unlayered :
    ∃ t : Tree, IsHeaded t ∧ noRec t = 0 ∧ ¬ IsWord t ∧ headHeights t ≠ [gridPeak t] :=
  ⟨.node .om [ .node Constituent.ph [.node (.ft true) [.node (.syl 1 true) []]],
               .node (.syl 1 true) [] ],
    by decide, by decide, by decide, by decide⟩

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
