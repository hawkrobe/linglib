import Linglib.Phonology.Prosody.Word
import Mathlib.Data.List.MinMax

/-!
# The metrical grid
[liberman-prince-1977] [prince-1983] [hayes-1995] [ito-mester-2009]

The **metrical grid** is the prominence dual of the prosodic word: a column of marks over each
syllable, taller standing for greater relative prominence (primary > secondary > unstressed),
read off a `Prosody.Tree` by the *Relative Prominence Projection Rule* ([liberman-prince-1977],
canonized in [prince-1983]) — one mark per syllable, one more per layer of headedness above it.

The fold underneath is `Grid.columnsLive`, the **head-projection** computation: each `Grid.Column` is
tagged `live` while its leaf is still the **head terminal** (Liberman & Prince's *designated
terminal element*) of every node up to the root. `Grid.columns` is its height projection;
`Grid.headHeights`/`Grid.headTerminals` read the live columns' heights and leaves. This is the *determinate*
bracketed grid of Halle & Vergnaud 1987 / [hayes-1995] — our
`Tree` *is* the bracketed grid, `Grid.ofTree` the forgetful map onto the pure grid. What it forgets is
*theorem*-shaped: constituency (`Grid.ofTree_not_injective`) and, under recursion,
[liberman-prince-1977]'s order-invariant culminativity (`Grid.not_culminative_under_recursion`).

## Main definitions
* `Grid.columnsLive` — the head-projection fold; each `Grid.Column` carries its leaf, height, and `live`
  bit (whether its leaf is a head terminal).
* `Grid.columns` / `Grid.peak` / `Grid.ofTree` — its height image: heights, the peak (the head terminal's
  prominence), the stacked rows.
* `Grid.headTerminals` / `Grid.headHeights` / `Grid.IsHeaded` — the head terminals (DTEs) as nodes /
  as heights, and the unique-head-terminal predicate.
* `Grid.IsContinuous` / `Grid.IsCulminative` — the grid well-formedness invariants.

## Main results
* `Grid.ofTree_isContinuous` — the Continuous Column Constraint, by construction.
* `Grid.columns_toProsTree` / `Grid.foot_headRow` / `Grid.peak_toProsTree` — head-preservation.
* `Grid.headHeights_eq_peak` — the peak is the head terminal on a non-recursive headed word.
* `Grid.ofTree_not_injective` / `Grid.not_culminative_under_recursion` — what the projection forgets.
-/

namespace Prosody

/-! ### The grid -/

/-- A metrical grid: rows of head-marks, bottom row first. -/
abbrev Grid := List (List Bool)

namespace Grid

/-- A metrical-grid column: a σ-leaf with its head-projection height and liveness. -/
structure Column where
  /-- The σ-leaf carrying the column. -/
  leaf : Tree
  /-- The column's head-projection height. -/
  height : ℕ
  /-- Whether the leaf is a head terminal. -/
  live : Bool

/-- Carry a column up one edge, bumping its height and liveness. -/
private def bumpLive (isHead : Bool) : Column → Column :=
  fun c => { c with height := c.height + (if isHead && c.live then 1 else 0), live := isHead && c.live }

variable (t : Tree)

/-- The live grid: one `Column` per σ-leaf, tracking head-terminal liveness. -/
def columnsLive : List Column := go t where
  go : Tree → List Column
    | .node a cs => if a.isSyl && cs.isEmpty then [⟨.node a cs, 1, true⟩] else goList cs
  goList : List Tree → List Column
    | []      => []
    | c :: cs => (go c).map (bumpLive c.label.isHead) ++ goList cs

/-- **The fold's recursion** ([liberman-prince-1977]): a σ-leaf is its own column; every other
    node's columns are its children's, each carried up (`bumpLive`) along the edge to it. -/
@[simp] theorem columnsLive_node (a : Constituent) (cs : List Tree) :
    columnsLive (.node a cs)
      = if a.isSyl ∧ cs = [] then [⟨.node a cs, 1, true⟩]
        else cs.flatMap (fun c => (columnsLive c).map (bumpLive c.label.isHead)) := by
  have hg : ∀ ds : List Tree, columnsLive.goList ds
      = ds.flatMap (fun c => (columnsLive c).map (bumpLive c.label.isHead)) := fun ds => by
    induction ds with
    | nil => rfl
    | cons c ds ih => simp only [columnsLive.goList, List.flatMap_cons, ih, columnsLive]
  by_cases h : a.isSyl = true ∧ cs = []
  · obtain ⟨hσ, rfl⟩ := h
    simp [columnsLive, columnsLive.go, hσ]
  · rw [if_neg h]
    have hb : (a.isSyl && cs.isEmpty) = false := by
      rcases Bool.eq_false_or_eq_true (a.isSyl && cs.isEmpty) with h' | h'
      · rw [Bool.and_eq_true, List.isEmpty_iff] at h'; exact absurd h' h
      · exact h'
    rw [show columnsLive (.node a cs) = columnsLive.goList cs from by
          simp [columnsLive, columnsLive.go, hb], hg]

/-- The grid-column heights of a tree. -/
def columns : List ℕ := (columnsLive t).map (·.height)

/-- The tallest grid column. -/
def peak : ℕ := (columns t).foldr max 0

/-- The head terminals' prominences. -/
def headHeights : List ℕ := ((columnsLive t).filter (·.live)).map (·.height)

/-- A tree is headed when it has a unique head terminal. -/
def IsHeaded : Prop := (headHeights t).length = 1

instance : Decidable (IsHeaded t) := by unfold IsHeaded; infer_instance

/-- `leaf` is a head terminal of `t`, reached from the root by an all-head descent. -/
inductive IsHeadTerminal : Tree → Tree → Prop
  | leaf (wt hd) : IsHeadTerminal (.node (.syl wt hd) []) (.node (.syl wt hd) [])
  | head {a cs c leaf} : c ∈ cs → c.label.isHead →
      IsHeadTerminal c leaf → IsHeadTerminal (.node a cs) leaf

/-- The **head terminals** (DTEs) — Liberman & Prince's *designated terminal elements*: the
    σ-leaves reached from the root by an all-head descent. The head-child recursion mirroring
    `IsHeadTerminal`, structural (so `decide` computes it) via `Planar.fold`. -/
def headTerminals (t : Tree) : List Tree :=
  t.fold fun a ps =>
    if a.isSyl ∧ ps = [] then [.node a []]
    else (ps.filter (·.1.label.isHead)).flatMap (·.2)

/-- Head terminals recurse through the head children: a σ-leaf is its own; otherwise a non-head
    edge drops a child's terminals while a head edge keeps them. -/
@[simp] theorem headTerminals_node (a : Constituent) (cs : List Tree) :
    headTerminals (.node a cs)
      = if a.isSyl ∧ cs = [] then [.node a []]
        else (cs.filter (·.label.isHead)).flatMap headTerminals := by
  conv_lhs => rw [headTerminals, RootedTree.Planar.fold_node]
  simp only [List.map_eq_nil_iff]
  split
  · rfl
  · rw [List.filter_map, List.flatMap_map]; rfl

/-- The head terminal as a single element, if the tree is headed. -/
def headTerminal (t : Tree) : Option Tree := (headTerminals t).head?

/-- The fold `headTerminals` computes the relation `IsHeadTerminal`. -/
theorem mem_headTerminals_iff {t leaf : Tree} :
    leaf ∈ headTerminals t ↔ IsHeadTerminal t leaf := by
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    rw [headTerminals_node]
    split
    · rename_i hσ; obtain ⟨hσ, rfl⟩ := hσ
      obtain ⟨w, hd, rfl⟩ : ∃ w hd, a = .syl w hd := by cases a <;> simp_all [Constituent.isSyl]
      simp only [List.mem_singleton]
      constructor
      · rintro rfl; exact .leaf w hd
      · intro h; cases h with
        | leaf _ _ => rfl
        | head hc _ _ => exact absurd hc List.not_mem_nil
    · rename_i hcond
      simp only [List.mem_flatMap, List.mem_filter]
      constructor
      · rintro ⟨c, ⟨hc, hhead⟩, hmem⟩
        exact .head hc hhead ((IH c (by simpa using hc)).mp hmem)
      · intro h; cases h with
        | leaf _ _ => exact absurd ⟨rfl, rfl⟩ hcond
        | head hc hhead hsub => exact ⟨_, ⟨hc, hhead⟩, (IH _ (by simpa using hc)).mpr hsub⟩

/-- `(l.filter p).flatMap f` drops the elements failing `p`. -/
private theorem List.filter_flatMap_eq {β γ : Type*} (p : β → Bool) (f : β → List γ)
    (l : List β) : (l.filter p).flatMap f = l.flatMap (fun x => if p x then f x else []) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : p x <;> simp [List.filter_cons, h, ih]

/-- The structural head terminals are exactly the leaves of the *live* grid columns: the all-head
    descent and `columnsLive`'s `live` bit pick out the same σ-leaves. -/
private theorem headTerminals_eq_live :
    headTerminals t = ((columnsLive t).filter (·.live)).map (·.leaf) := by
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    rw [headTerminals_node, columnsLive_node]
    by_cases h : a.isSyl = true ∧ cs = []
    · obtain ⟨hσ, rfl⟩ := h; simp [hσ]
    · rw [if_neg h, if_neg h, List.filter_flatMap_eq, List.filter_flatMap, List.map_flatMap]
      refine List.flatMap_congr fun c hc => ?_
      rw [List.filter_map, List.map_map]
      cases hh : c.label.isHead <;>
        simp [bumpLive, Function.comp_def, IH c (by simpa using hc)]

/-- A tree is headed iff it has a single head terminal. -/
theorem isHeaded_iff_headTerminals : IsHeaded t ↔ (headTerminals t).length = 1 := by
  rw [IsHeaded, headHeights, List.length_map, headTerminals_eq_live, List.length_map]

/-- The metrical grid of a tree, as stacked rows. -/
def ofTree : Grid :=
  (List.range (peak t)).map
    (fun r => (columns t).map (fun h => decide (r < h)))

/-! ### The Continuous Column Constraint -/

/-- Whether one row is a submask of the row below. -/
private def rowSubmask (upper lower : List Bool) : Bool :=
  (upper.zip lower).all (fun p => !p.1 || p.2)

/-- The Continuous Column Constraint ([prince-1983]; [hayes-1995]): no column has a gap. -/
def IsContinuous (g : Grid) : Prop := g.IsChain (fun lower upper => rowSubmask upper lower = true)

instance (g : Grid) : Decidable (IsContinuous g) := by unfold IsContinuous; infer_instance

/-- `ofTree` always satisfies the Continuous Column Constraint ([prince-1983]; [hayes-1995]). -/
theorem ofTree_isContinuous (t : Tree) : IsContinuous (ofTree t) := by
  rw [IsContinuous, ofTree, List.isChain_map, List.isChain_iff_getElem]
  intro i _
  simp only [List.getElem_range]
  rw [rowSubmask, List.zip_map', List.all_map, List.all_eq_true]
  intro h _
  by_cases hr : i + 1 < h <;> simp [hr]
  omega

/-! ### Head-preservation

Re-representing a `Foot` as a tree and reading its grid recovers its head — the depth-1 core. -/

/-- The live fold on a σ-leaf: one live column at height `1`. -/
private theorem columnsLive.go_syl (wt : Syllable.Weight) (hd : Bool) :
    columnsLive.go (.node (Constituent.syl wt hd) [])
      = [⟨.node (Constituent.syl wt hd) [], 1, true⟩] := rfl

/-- The `goList` fold as a `flatMap` over children. -/
private theorem columnsLive.goList_eq (cs : List Tree) :
    columnsLive.goList cs
      = cs.flatMap (fun c => (columnsLive.go c).map (bumpLive c.label.isHead)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [columnsLive.goList, List.flatMap_cons, ih]

/-- The live grid of a non-σ node is the bumped concatenation of its children's. -/
private theorem columnsLive.node_of_ne_σ {a : Constituent} {cs : List Tree}
    (ha : a.isSyl = false) :
    columnsLive (.node a cs)
      = cs.flatMap (fun c => (columnsLive.go c).map (bumpLive c.label.isHead)) := by
  rw [← columnsLive.goList_eq]
  simp [columnsLive, columnsLive.go, ha]

/-- A foot's grid is `2` at the head σ, `1` elsewhere. -/
theorem columns_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    columns (f.toProsTree w) = (Foot.toGrid f).map (fun b => if b then 2 else 1) := by
  rw [columns, Foot.toProsTree,
      columnsLive.node_of_ne_σ (a := Constituent.ft false) (by decide), List.flatMap_map]
  simp only [columnsLive.go_syl, RootedTree.Planar.label_node, Constituent.isHead,
    List.map_cons, List.map_nil, bumpLive]
  rw [← List.map_eq_flatMap, Foot.toGrid, List.map_map, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i = f.head <;> simp [hi]

/-- The grid's head row recovers `Foot.toGrid`. -/
theorem foot_headRow {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    (columns (f.toProsTree w)).map (fun h => decide (1 < h)) = Foot.toGrid f := by
  rw [columns_toProsTree, List.map_map]
  refine List.map_id'' (fun b => ?_) _
  cases b <;> rfl

/-- A foot's grid peaks at `2`. -/
theorem peak_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    peak (f.toProsTree w) = 2 := by
  rw [peak, columns_toProsTree]
  refine Nat.le_antisymm (List.max_le_of_forall_le _ 2 ?_) (List.le_max_of_le' 0 ?_ le_rfl)
  · rintro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  · exact List.mem_map.mpr ⟨true,
      List.mem_map.mpr ⟨f.head, List.mem_finRange _, decide_eq_true_eq.mpr rfl⟩, rfl⟩

/-! ### What the grid forgets

The projection is one-way: it drops constituency (`ofTree_not_injective`) and, under recursion,
[liberman-prince-1977]'s order-invariant culminativity (`not_culminative_under_recursion`). -/

/-- `ofTree` is not injective: the grid forgets constituency. -/
theorem ofTree_not_injective :
    ∃ t₁ t₂ : Tree, t₁ ≠ t₂ ∧ ofTree t₁ = ofTree t₂ :=
  ⟨.node .om [.node .ft [.node (.syl 1) []]], .node .om [.node (.syl 1) []],
    by decide, by decide⟩

/-- Culminativity ([liberman-prince-1977]): exactly one column is tallest. -/
def IsCulminative (cols : List ℕ) : Prop :=
  (cols.filter (· = cols.foldr max 0)).length = 1

instance (cols : List ℕ) : Decidable (IsCulminative cols) := by
  unfold IsCulminative; infer_instance

/-- Recursion can break culminativity. -/
theorem not_culminative_under_recursion :
    ∃ t : Tree, IsWord t ∧ ¬ IsCulminative (columns t) :=
  ⟨.node .om
      [ .node (.ft true) [.node (.syl 1 true) []],
        .node .om [.node (.ft true) [.node (.syl 1 true) []]] ],
    by decide, by decide⟩

/-- A flat word stays culminative. -/
theorem culminative_flat :
    IsCulminative (columns
      (.node .om [ .node (.ft true)  [.node (.syl 1 true) []],
                   .node (.ft false) [.node (.syl 1 true) []] ])) := by decide

/-! ### The word peak and the head terminal

The ω analogue of `peak_toProsTree`: on a non-recursive headed word the grid peak *is* the
head terminal (Liberman & Prince's designated terminal element) — primary stress reads off the
grid. Recursion is the sole obstruction, and (unlike the foot) culminativity alone is not enough. -/

/-- `isWordTree.goList` as a `List.all` over children. -/
private theorem isWordTree.goList_all (cs : List Tree) :
    isWordTree.goList cs
      = cs.all (fun c => isFootTree c || isWordTree.go c
          || (c.label.isSyl && c.children.isEmpty)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [isWordTree.goList, List.all_cons, ih]

/-- A non-recursive word is an ω over well-formed feet and stray σ-leaves. -/
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

/-- The live fold on any σ-leaf: one live column at height `1`. -/
private theorem columnsLive.go_leaf {sb : Constituent} (h : sb.isSyl = true) :
    columnsLive.go (.node sb []) = [⟨.node sb [], 1, true⟩] := by
  simp [columnsLive.go, h]

/-- Column-height bounds for a non-recursive word: `≤ 3`, live `≥ 2`, and height `3` ⇒ live. -/
private theorem columnsLive_bounded {t : Tree} (hw : IsWord t) (hr : noRec t = 0) :
    ∀ col ∈ columnsLive t,
      col.height ≤ 3 ∧ (col.live = true → 2 ≤ col.height) ∧ (col.height = 3 → col.live = true) := by
  obtain ⟨a, cs⟩ := t
  obtain ⟨ha, hchild⟩ := isWord_children hw hr
  intro col hcol
  rw [columnsLive.node_of_ne_σ (a := a) (Constituent.isSyl_eq_false_of_isOm ha),
    List.mem_flatMap] at hcol
  obtain ⟨c, hc, hcol⟩ := hcol
  rw [List.mem_map] at hcol
  obtain ⟨col0, hcol0, rfl⟩ := hcol
  rcases hchild c hc with hfoot | ⟨hlev, hchildren⟩
  · obtain ⟨cl, ccs⟩ := c
    simp only [isFootTree, Bool.and_eq_true] at hfoot
    obtain ⟨⟨hclf, _⟩, hleaves⟩ := hfoot
    have hgoc : columnsLive.go (.node cl ccs)
        = ccs.flatMap (fun s => (columnsLive.go s).map (bumpLive s.label.isHead)) :=
      columnsLive.node_of_ne_σ (a := cl) (Constituent.isSyl_eq_false_of_isFt hclf)
    rw [hgoc, List.mem_flatMap] at hcol0
    obtain ⟨s, hs, hcol0⟩ := hcol0
    have hsleaf := List.all_eq_true.mp hleaves s hs
    obtain ⟨sb, sds⟩ := s
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hsleaf
    obtain ⟨hsσ, hsds⟩ := hsleaf
    subst hsds
    rw [columnsLive.go_leaf hsσ, List.map_cons, List.map_nil, List.mem_singleton] at hcol0
    subst hcol0
    cases hclh : cl.isHead <;> cases hsbh : sb.isHead <;>
      simp [bumpLive, RootedTree.Planar.label_node, hclh, hsbh]
  · obtain ⟨cb, cbs⟩ := c
    simp only [RootedTree.Planar.label_node] at hlev
    simp only [RootedTree.Planar.children_node] at hchildren
    subst hchildren
    rw [columnsLive.go_leaf hlev, List.mem_singleton] at hcol0
    subst hcol0
    cases hcbh : cb.isHead <;>
      simp [bumpLive, RootedTree.Planar.label_node, hcbh]

/-- On a non-recursive headed word, the head terminal is the grid peak ([liberman-prince-1977]). -/
theorem headHeights_eq_peak {t : Tree} (hw : IsWord t) (hh : IsHeaded t) (hr : noRec t = 0) :
    headHeights t = [peak t] := by
  have facts := columnsLive_bounded hw hr
  rw [IsHeaded, headHeights, List.length_map] at hh
  obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hh
  have hc0mf : c0 ∈ (columnsLive t).filter (·.live) := by rw [hc0]; simp
  rw [List.mem_filter] at hc0mf
  obtain ⟨hc0mem, hc0live⟩ := hc0mf
  have hpeak : c0.height = peak t := by
    rw [peak, columns]
    refine le_antisymm
      (List.le_max_of_le' 0 (List.mem_map.mpr ⟨c0, hc0mem, rfl⟩) (le_refl c0.height))
      (List.max_le_of_forall_le _ c0.height fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨col, hcm, rfl⟩ := hx
    obtain ⟨_, hc0ge2, _⟩ := facts c0 hc0mem
    obtain ⟨hle3, _, h3⟩ := facts col hcm
    rcases (show col.height ≤ 2 ∨ col.height = 3 by omega) with h2 | h3eq
    · exact le_trans h2 (hc0ge2 hc0live)
    · have hmem : col ∈ (columnsLive t).filter (·.live) :=
        List.mem_filter.mpr ⟨hcm, h3 h3eq⟩
      rw [hc0, List.mem_singleton] at hmem
      exact le_of_eq (congrArg Column.height hmem)
  rw [headHeights, hc0]; simp [hpeak]

/-- Under recursion the peak can desert the head terminal, even when culminative
    ([ito-mester-2009]). -/
theorem head_below_peak_under_recursion :
    ∃ t : Tree, IsWord t ∧ IsHeaded t ∧ IsCulminative (columns t)
      ∧ headHeights t ≠ [peak t] :=
  ⟨.node .om [ .node (.syl 1 true) [],
               .node .om [.node (.ft true) [.node (.syl 1 true) []]] ],
    by decide, by decide, by decide, by decide⟩

/-- Without Layeredness the peak can desert the head terminal too. -/
theorem head_below_peak_unlayered :
    ∃ t : Tree, IsHeaded t ∧ noRec t = 0 ∧ ¬ IsWord t ∧ headHeights t ≠ [peak t] :=
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

example : columns exWord = [3, 2, 1] := by decide
example : peak exWord = 3 := by decide
example : ofTree exWord =
    [[true, true, true], [true, true, false], [true, false, false]] := by decide
example : IsContinuous (ofTree exWord) := by decide

end Grid

end Prosody
