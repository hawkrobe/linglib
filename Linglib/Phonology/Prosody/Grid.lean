import Linglib.Phonology.Prosody.Word
import Mathlib.Data.List.MinMax

/-!
# The metrical grid
[liberman-prince-1977] [prince-1983] [hayes-1995] [ito-mester-2009]

The **metrical grid** is the prominence dual of the prosodic word: a column of marks over each
syllable, taller standing for greater relative prominence (primary > secondary > unstressed),
read off a `Prosody.Tree` by the *Relative Prominence Projection Rule* ([liberman-prince-1977],
canonized in [prince-1983]) — one mark per syllable, one more per layer of headedness above it.

The fold underneath is `Grid.cells`, the **head-projection**: one pass tagging each σ-leaf with its
height and a `live` bit — `live` holding while the leaf is still the **head terminal** (Liberman &
Prince's *designated terminal element*) of every node up to the root. The four grid readers are its
projections: `Grid.terminals` (the leaves), `Grid.columns` (their heights), and the live sublists
`Grid.headTerminals` / `Grid.headHeights`. This determines the *determinate* bracketed grid of Halle
& Vergnaud 1987 / [hayes-1995]; `Grid.ofTree` is the forgetful map onto the pure grid. What it
forgets is *theorem*-shaped: constituency (`Grid.ofTree_not_injective`) and, under recursion,
[liberman-prince-1977]'s order-invariant culminativity (`Grid.not_culminative_under_recursion`).

## Main definitions
* `Grid.cells` — the single head-projection fold; each σ-leaf as `(leaf, height, live)`.
* `Grid.terminals` / `Grid.columns` / `Grid.peak` / `Grid.ofTree` — its projections: the σ-leaves,
  their heights, the peak (the head terminal's prominence), and the stacked rows.
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

/-- The single head-projection fold ([liberman-prince-1977]): each σ-leaf as a cell
    `(leaf, height, live)`. The `height` is `1` plus the contiguous run of head edges ending at the
    leaf; `live` holds while every edge from the root has been a head edge — i.e. the leaf is still
    a head terminal. The grid readers below are all projections of this one fold. -/
def cells (t : Tree) : ℕ × Bool → List (Tree × ℕ × Bool) :=
  t.fold (β := ℕ × Bool → _) fun a ps st =>
    if a.isSyl ∧ ps = [] then [(.node a [], st.1 + 1, st.2)]
    else ps.flatMap fun p => p.2 (if p.1.label.isHead then (st.1 + 1, st.2) else (0, false))

/-- The recursion of `cells`: a σ-leaf is one cell carrying the running state; otherwise visit each
    child with the run extended (`+1`) and liveness kept across a head edge, both reset across any
    other edge. -/
@[simp] theorem cells_node (a : Constituent) (cs : List Tree) (st : ℕ × Bool) :
    cells (.node a cs) st
      = if a.isSyl ∧ cs = [] then [(.node a [], st.1 + 1, st.2)]
        else cs.flatMap fun c =>
          cells c (if c.label.isHead then (st.1 + 1, st.2) else (0, false)) := by
  conv_lhs => rw [cells, RootedTree.Planar.fold_node]
  simp only [List.map_eq_nil_iff]
  split
  · rfl
  · rw [List.flatMap_map]; rfl

variable (t : Tree)

/-- The σ-leaves of a tree, left to right: the terminal tier the grid sits over. -/
def terminals : List Tree := (cells t (0, true)).map (·.1)

/-- The grid-column heights ([liberman-prince-1977]): each σ-leaf's height is `1` plus the
    contiguous run of head-edges ending at it. -/
def columns : List ℕ := (cells t (0, true)).map (·.2.1)

/-- The tallest grid column. -/
def peak : ℕ := (columns t).foldr max 0

/-- The **head terminals** (DTEs) — Liberman & Prince's *designated terminal elements*: the σ-leaves
    still `live` after the descent, i.e. reached from the root by all head edges. -/
def headTerminals : List Tree := ((cells t (0, true)).filter (·.2.2)).map (·.1)

/-- The head terminals' prominences ([liberman-prince-1977]): the live cells' heights — each its
    depth `+ 1`, the whole root-path being head edges. -/
def headHeights : List ℕ := ((cells t (0, true)).filter (·.2.2)).map (·.2.1)

/-- Head-terminal heights are a sublist of the columns — a head terminal is one of the σ-leaves.
    The universal half of `headHeights_eq_peak`, free because both read the one `cells` fold. -/
theorem headHeights_sublist_columns : (headHeights t).Sublist (columns t) :=
  List.filter_sublist.map _

/-- The head terminal as a single element, if the tree is headed. -/
def headTerminal : Option Tree := (headTerminals t).head?

/-- A tree is headed when it has a unique head terminal. -/
def IsHeaded : Prop := (headHeights t).length = 1

instance : Decidable (IsHeaded t) := by unfold IsHeaded; infer_instance

/-- `leaf` is a head terminal of `t`, reached from the root by an all-head descent. -/
inductive IsHeadTerminal : Tree → Tree → Prop
  | leaf (wt hd) : IsHeadTerminal (.node (.syl wt hd) []) (.node (.syl wt hd) [])
  | head {a cs c leaf} : c ∈ cs → c.label.isHead →
      IsHeadTerminal c leaf → IsHeadTerminal (.node a cs) leaf

/-- The `live` leaves of `cells t (r, l)` are exactly the head terminals — once the descent so far
    is itself all-head (`l = true`). -/
theorem mem_liveLeaves {t : Tree} (leaf : Tree) :
    ∀ {r : ℕ} {l : Bool},
      leaf ∈ ((cells t (r, l)).filter (·.2.2)).map (·.1) ↔ l = true ∧ IsHeadTerminal t leaf := by
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro r l
    rw [cells_node]
    split
    · rename_i hσ; obtain ⟨hσ, rfl⟩ := hσ
      obtain ⟨w, hd, rfl⟩ : ∃ w hd, a = .syl w hd := by cases a <;> simp_all [Constituent.isSyl]
      cases l <;> simp only [List.filter_cons, List.filter_nil, List.map_cons, List.map_nil,
        List.mem_singleton, List.not_mem_nil, if_true, if_false, Bool.false_eq_true, false_and,
        true_and]
      constructor
      · rintro rfl; exact .leaf w hd
      · rintro h; cases h with
        | leaf => rfl
        | head hc => cases hc
    · rename_i hσ
      simp only [List.filter_flatMap, List.map_flatMap, List.mem_flatMap]
      constructor
      · rintro ⟨c, hc, hmem⟩
        rw [IH c (by simpa using hc)] at hmem
        obtain ⟨hlive, hht⟩ := hmem
        refine ⟨?_, .head hc ?_ hht⟩ <;>
          · by_cases hh : c.label.isHead = true <;> simp_all
      · rintro ⟨rfl, h⟩
        cases h with
        | leaf => simp [Constituent.isSyl] at hσ
        | head hc hhd hsub =>
          exact ⟨_, hc, by rw [IH _ (by simpa using hc), if_pos hhd]; exact ⟨rfl, hsub⟩⟩

/-- `headTerminals` computes the relation `IsHeadTerminal`. -/
theorem mem_headTerminals_iff {t leaf : Tree} :
    leaf ∈ headTerminals t ↔ IsHeadTerminal t leaf := by
  rw [headTerminals, mem_liveLeaves]; simp

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

/-- A foot's grid is `2` at the head σ, `1` elsewhere. -/
theorem columns_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    columns (f.toProsTree w) = (Foot.toGrid f).map (fun b => if b then 2 else 1) := by
  rw [columns, Foot.toProsTree, cells_node, if_neg (by simp [Constituent.isSyl]),
      List.map_flatMap, List.flatMap_map, Foot.toGrid, List.map_map, List.map_eq_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  rw [cells_node, if_pos ⟨by simp [Constituent.isSyl], rfl⟩]
  simp only [RootedTree.Planar.label_node, Constituent.isHead, List.map_cons, List.map_nil]
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

/-- A live cell only deepens its seed: a still-`live` cell of `cells t (r, l)` had an all-head
    descent so far (`l = true`) and height at least `r + 1`. -/
theorem live_seed_le {t : Tree} : ∀ {r : ℕ} {l : Bool} {x : Tree × ℕ × Bool},
    x ∈ cells t (r, l) → x.2.2 = true → l = true ∧ r + 1 ≤ x.2.1 := by
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    intro r l x hx hlive
    rw [cells_node] at hx
    split at hx
    · simp only [List.mem_singleton] at hx; subst hx; exact ⟨hlive, le_rfl⟩
    · rw [List.mem_flatMap] at hx
      obtain ⟨c, hc, hx⟩ := hx
      by_cases hh : c.label.isHead = true
      · rw [if_pos hh] at hx; obtain ⟨hl, hle⟩ := IH c (by simpa using hc) hx hlive
        exact ⟨hl, by omega⟩
      · rw [if_neg hh] at hx; obtain ⟨hl, _⟩ := IH c (by simpa using hc) hx hlive
        exact absurd hl (by simp)

/-- In a word the head terminal sits below ω, so its height is at least `2`. -/
theorem two_le_headHeight_of_word {t : Tree} (hw : IsWord t) (hr : noRec t = 0)
    {h : ℕ} (hh : h ∈ headHeights t) : 2 ≤ h := by
  obtain ⟨a, cs⟩ := t
  obtain ⟨ha, _⟩ := isWord_children hw hr
  rw [headHeights, cells_node, if_neg (by simp [Constituent.isSyl_eq_false_of_isOm ha])] at hh
  simp only [List.filter_flatMap, List.map_flatMap, List.mem_flatMap, List.mem_map,
    List.mem_filter] at hh
  obtain ⟨ch, _, x, ⟨hx, hlive⟩, rfl⟩ := hh
  by_cases hchh : ch.label.isHead = true
  · rw [if_pos hchh] at hx; obtain ⟨_, hle⟩ := live_seed_le hx hlive; omega
  · rw [if_neg hchh] at hx; obtain ⟨hl, _⟩ := live_seed_le hx hlive; exact absurd hl (by simp)

/-- The genuine non-recursion content: in a word of depth `≤ 2` every column is `≤ 2`, unless it is
    reached by an all-head descent — in which case it is a head-terminal height, read straight off
    the cell's `live` bit. -/
theorem col_le_two_or_headHeight {t : Tree} (hw : IsWord t) (hr : noRec t = 0) :
    ∀ {c : ℕ}, c ∈ columns t → c ≤ 2 ∨ c ∈ headHeights t := by
  obtain ⟨a, cs⟩ := t
  obtain ⟨ha, hchild⟩ := isWord_children hw hr
  have hσ : a.isSyl = false := Constituent.isSyl_eq_false_of_isOm ha
  intro c hc
  rw [columns, List.mem_map] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  rw [cells_node, if_neg (by simp [hσ]), List.mem_flatMap] at hx
  obtain ⟨ch, hch, hxch⟩ := hx
  by_cases hlive : x.2.2 = true
  · -- live cell: its height is a head-terminal height
    right
    rw [headHeights, List.mem_map]
    refine ⟨x, List.mem_filter.mpr ⟨?_, hlive⟩, rfl⟩
    rw [cells_node, if_neg (by simp [hσ]), List.mem_flatMap]; exact ⟨ch, hch, hxch⟩
  · -- non-live cell: depth `≤ 2`, so height `≤ 2`
    left
    rcases hchild ch hch with hfoot | ⟨hstrayσ, hstraycs⟩
    · obtain ⟨chl, chcs⟩ := ch
      simp only [isFootTree, Bool.and_eq_true, List.all_eq_true] at hfoot
      obtain ⟨⟨hchft, _⟩, hleaves⟩ := hfoot
      have hchσ : chl.isSyl = false := Constituent.isSyl_eq_false_of_isFt hchft
      rw [RootedTree.Planar.label_node, cells_node, if_neg (by simp [hchσ]),
          List.mem_flatMap] at hxch
      obtain ⟨s, hs, hxs⟩ := hxch
      obtain ⟨sb, sds⟩ := s
      have hsm := hleaves (.node sb sds) hs
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hsm
      obtain ⟨hsbσ, rfl⟩ := hsm
      rw [RootedTree.Planar.label_node, cells_node, if_pos ⟨hsbσ, rfl⟩,
          List.mem_singleton] at hxs
      subst hxs
      by_cases hsh : sb.isHead = true
      · by_cases hchh : chl.isHead = true
        · simp only [if_pos hsh, if_pos hchh] at hlive; exact absurd trivial hlive
        · simp only [if_pos hsh, if_neg hchh]; omega
      · simp only [if_neg hsh]; omega
    · obtain ⟨chl, chcs⟩ := ch
      simp only [RootedTree.Planar.children_node] at hstraycs; subst hstraycs
      rw [RootedTree.Planar.label_node, cells_node, if_pos ⟨by simpa using hstrayσ, rfl⟩,
          List.mem_singleton] at hxch
      subst hxch
      by_cases hchh : chl.isHead = true
      · simp only [if_pos hchh]; omega
      · simp only [if_neg hchh]; omega

/-- Every head-terminal height is at most the peak — free from `headHeights_sublist_columns`. -/
theorem headHeight_le_peak {t : Tree} {h : ℕ} (hh : h ∈ headHeights t) : h ≤ peak t := by
  rw [peak]; exact List.le_max_of_le' 0 ((headHeights_sublist_columns t).subset hh) le_rfl

/-- On a non-recursive headed word, the head terminal is the grid peak ([liberman-prince-1977]):
    primary stress reads off the grid. The head terminal is one of the columns
    (`headHeights_sublist_columns`); and no column outgrows it (`col_le_two_or_headHeight`). -/
theorem headHeights_eq_peak {t : Tree} (hw : IsWord t) (hh : IsHeaded t) (hr : noRec t = 0) :
    headHeights t = [peak t] := by
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp hh
  have hvmem : v ∈ headHeights t := by rw [hv]; exact List.mem_singleton_self v
  have hge : peak t ≤ v := by
    rw [peak]
    refine List.max_le_of_forall_le _ v fun c hc => ?_
    rcases col_le_two_or_headHeight hw hr hc with h2 | hmem
    · have := two_le_headHeight_of_word hw hr hvmem; omega
    · rw [hv, List.mem_singleton] at hmem; omega
  rw [hv, le_antisymm (headHeight_le_peak hvmem) hge]

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
