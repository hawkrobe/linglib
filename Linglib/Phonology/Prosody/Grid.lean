import Linglib.Phonology.Prosody.Word
import Mathlib.Data.List.MinMax

/-!
# The metrical grid
[liberman-prince-1977] [prince-1983] [hayes-1995] [halle-vergnaud-1987] [ito-mester-2009]

The **metrical grid** is the prominence dual of the prosodic word: a column of marks over each
syllable, taller standing for greater relative prominence (primary > secondary > unstressed). This
file is organised as a small tower of objects, each adding structure to the plain grid and each
connected to the plainer one below by a forgetful map:

```
Marks        rendered rows of marks; the Continuous Column Constraint lives here
  ↑ rows                                    (Prince 1983's autonomous grid)
Grid         column heights — the pure rhythmic grid
  ↑ toGrid                                   (add the designated terminal element)
MarkedGrid   a grid whose columns carry the head-spine (Liberman & Prince's DTE)
  ↑ project                                  (the RPPR)
Tree         the bracketed grid — brackets at all layers ([hayes-1995] §3.5)
```

The projection `Grid.project` is the *Relative Prominence Projection Rule* ([liberman-prince-1977]):
a homomorphism from the tree into the DTE-marked grid, built from a small algebra
(`cell`/`juxtapose`/`promote`/`clear`). The grid readers (`columns`, `terminals`, `headTerminals`,
`headHeights`) are the forgetful maps out of it. What the forgetful map onto the pure grid drops is
*theorem*-shaped: constituency (`Grid.ofTree_not_injective`; the grid underdetermines bracketing,
[hayes-1995] §3.8) and, under recursion, order-invariant culminativity
(`Grid.not_culminative_under_recursion`).

## Main definitions
* `Grid` / `Grid.peak` / `Grid.IsCulminative` — the pure grid (column heights) and its invariants.
* `Marks` / `Marks.IsContinuous` / `Grid.rows` — the rendered grid and the Continuous Column
  Constraint, which holds for any rendered grid by construction.
* `MarkedGrid` / `Grid.project` — the DTE-marked grid and the RPPR projection from a tree.
* `Grid.columns` / `Grid.headTerminals` / `Grid.headHeights` / `Grid.IsHeaded` — the grid readers.

## Main results
* `Grid.ofTree_isContinuous` — the Continuous Column Constraint, by construction (free).
* `Grid.columns_toProsTree` / `Grid.peak_toProsTree` — head-preservation for a foot.
* `Grid.headHeights_eq_peak` — on a non-recursive headed word the head terminal's height is the
  grid peak: metrical primary stress is the tallest column.
* `Grid.ofTree_not_injective` / `Grid.not_culminative_under_recursion` — what the projection forgets.
-/

namespace Prosody

/-! ## The pure grid -/

/-- A metrical grid ([hayes-1995] §3.2): the beat count (column height) over each position, left to
    right. Absolute heights carry no significance; only relative prominence does. -/
abbrev Grid := List ℕ

namespace Grid

/-- The prominence peak: the tallest column. -/
def peak (g : Grid) : ℕ := g.foldr max 0

@[simp] theorem peak_nil : peak [] = 0 := rfl

/-- Every column is at most the peak. -/
theorem le_peak {g : Grid} {h : ℕ} (hh : h ∈ g) : h ≤ peak g :=
  List.le_max_of_le' 0 hh le_rfl

/-- The peak is bounded by any common bound on the columns. -/
theorem peak_le {g : Grid} {n : ℕ} (h : ∀ x ∈ g, x ≤ n) : peak g ≤ n :=
  List.max_le_of_forall_le _ n h

/-- Culminativity ([liberman-prince-1977]; [hayes-1995]): exactly one column is tallest. Note this
    is strictly stronger than having a unique head terminal (`IsHeaded`) — two columns can tie. -/
def IsCulminative (g : Grid) : Prop := g.countP (· == peak g) = 1

instance (g : Grid) : Decidable (IsCulminative g) := by unfold IsCulminative; infer_instance

end Grid

/-! ## The rendered grid and the Continuous Column Constraint -/

/-- A rendered metrical grid: rows of head-marks, bottom row first. -/
abbrev Marks := List (List Bool)

namespace Marks

/-- Whether one row is a submask of the row below. -/
private def rowSubmask (upper lower : List Bool) : Bool :=
  (upper.zip lower).all (fun p => !p.1 || p.2)

/-- The Continuous Column Constraint ([prince-1983]; [hayes-1995] §3.4.2 (9)): no column has a gap.
    A *violable* predicate on an arbitrary rendered grid. -/
def IsContinuous (m : Marks) : Prop :=
  m.IsChain (fun lower upper => rowSubmask upper lower = true)

instance (m : Marks) : Decidable (IsContinuous m) := by unfold IsContinuous; infer_instance

end Marks

namespace Grid

/-- Render a grid as stacked rows of marks: row `r` carries a mark over every column taller than
    `r`. -/
def rows (g : Grid) : Marks := (List.range (peak g)).map (fun r => g.map (r < ·))

/-- **The Continuous Column Constraint is free.** Every rendered grid satisfies it, because a column
    is a solid stack of marks by construction — continuity is the shape of a histogram, not a
    theorem about trees ([hayes-1995] §3.4.2). -/
theorem rows_isContinuous (g : Grid) : Marks.IsContinuous (rows g) := by
  rw [Marks.IsContinuous, rows, List.isChain_map, List.isChain_iff_getElem]
  intro i _
  simp only [List.getElem_range]
  rw [Marks.rowSubmask, List.zip_map', List.all_map, List.all_eq_true]
  intro h _
  by_cases hr : i + 1 < h <;> simp [hr]
  omega

end Grid

/-! ## The DTE-marked grid and the RPPR projection -/

/-- One column of a marked grid: the σ-leaf it sits over, its mark count (`height`), and whether it
    lies on the current head-spine (the designated terminal element so far, [liberman-prince-1977]). -/
structure Column (α : Type*) where
  /-- The σ-leaf under this column. -/
  terminal : α
  /-- The column height = number of grid marks. -/
  height : ℕ
  /-- Whether this column is (so far) the designated terminal element. -/
  onSpine : Bool

/-- A grid whose columns carry the head-spine (the DTE, [liberman-prince-1977]). This is the pure
    grid *plus a DTE marking* — it deliberately does not record the full bracketing (that is `Tree`;
    `Grid.ofTree_not_injective` is the honest statement that heights lose it). -/
abbrev MarkedGrid (α : Type*) := List (Column α)

namespace MarkedGrid
variable {α : Type*}

/-- Forget the marking: the underlying pure grid of column heights. -/
def toGrid (b : MarkedGrid α) : Grid := b.map (·.height)

/-- The terminals under the columns, left to right. -/
def terminals (b : MarkedGrid α) : List α := b.map (·.terminal)

/-- The head-spine columns' heights — the designated terminal elements' prominences. -/
def headHeights (b : MarkedGrid α) : Grid := (b.filter (·.onSpine)).map (·.height)

/-- The head-spine terminals — the designated terminal elements. -/
def headTerminals (b : MarkedGrid α) : List α := (b.filter (·.onSpine)).map (·.terminal)

/-- A single terminal: one column of height `1`, on its own head-spine. -/
def cell (x : α) : MarkedGrid α := [⟨x, 1, true⟩]

/-- Juxtapose sibling constituents. -/
def juxtapose (bs : List (MarkedGrid α)) : MarkedGrid α := bs.flatten

/-- The **head-projection step** of the RPPR ([liberman-prince-1977]): a head edge raises the head
    by one grid mark — bump every head-spine column. -/
def promote (b : MarkedGrid α) : MarkedGrid α :=
  b.map (fun c => { c with height := c.height + if c.onSpine then 1 else 0 })

/-- A weak edge: heights freeze, the head-spine marking is dropped. -/
def clear (b : MarkedGrid α) : MarkedGrid α :=
  b.map (fun c => { c with onSpine := false })

/-- One edge of the descent: a head edge projects, any other clears the spine. -/
def edge (isHead : Bool) (b : MarkedGrid α) : MarkedGrid α :=
  if isHead then b.promote else b.clear

@[simp] theorem edge_true (b : MarkedGrid α) : edge true b = b.promote := rfl
@[simp] theorem edge_false (b : MarkedGrid α) : edge false b = b.clear := rfl

/-! ### The algebra of the marked grid -/

@[simp] theorem toGrid_cell (x : α) : (cell x).toGrid = [1] := rfl
@[simp] theorem headHeights_cell (x : α) : (cell x).headHeights = [1] := rfl
@[simp] theorem terminals_cell (x : α) : (cell x).terminals = [x] := rfl
@[simp] theorem headTerminals_cell (x : α) : (cell x).headTerminals = [x] := rfl

@[simp] theorem toGrid_clear (b : MarkedGrid α) : (clear b).toGrid = b.toGrid := by
  simp [clear, toGrid, List.map_map, Function.comp]

@[simp] theorem headHeights_clear (b : MarkedGrid α) : (clear b).headHeights = [] := by
  simp [clear, headHeights, List.filter_map, Function.comp]

@[simp] theorem headTerminals_clear (b : MarkedGrid α) : (clear b).headTerminals = [] := by
  simp [clear, headTerminals, List.filter_map, Function.comp]

@[simp] theorem headHeights_promote (b : MarkedGrid α) :
    (promote b).headHeights = b.headHeights.map (· + 1) := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    obtain ⟨x, h, d⟩ := c
    simp only [promote, headHeights, List.map_cons, List.filter_cons, List.map_map] at ih ⊢
    cases d <;> simp_all

@[simp] theorem headTerminals_promote (b : MarkedGrid α) :
    (promote b).headTerminals = b.headTerminals := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    obtain ⟨x, h, d⟩ := c
    simp only [promote, headTerminals, List.map_cons, List.filter_cons] at ih ⊢
    cases d <;> simp_all

@[simp] theorem toGrid_juxtapose (bs : List (MarkedGrid α)) :
    (juxtapose bs).toGrid = bs.flatMap (·.toGrid) := by
  simp only [juxtapose, toGrid, List.map_flatten, List.flatMap_def]

@[simp] theorem headHeights_juxtapose (bs : List (MarkedGrid α)) :
    (juxtapose bs).headHeights = bs.flatMap (·.headHeights) := by
  simp only [juxtapose, headHeights, List.filter_flatten, List.map_flatten, List.flatMap_def,
    List.map_map]; rfl

@[simp] theorem headTerminals_juxtapose (bs : List (MarkedGrid α)) :
    (juxtapose bs).headTerminals = bs.flatMap (·.headTerminals) := by
  simp only [juxtapose, headTerminals, List.filter_flatten, List.map_flatten, List.flatMap_def,
    List.map_map]; rfl

@[simp] theorem headHeights_edge (h : Bool) (b : MarkedGrid α) :
    (edge h b).headHeights = if h then b.headHeights.map (· + 1) else [] := by
  cases h <;> simp [edge]

@[simp] theorem headTerminals_edge (h : Bool) (b : MarkedGrid α) :
    (edge h b).headTerminals = if h then b.headTerminals else [] := by
  cases h <;> simp [edge]

end MarkedGrid

namespace Grid
open MarkedGrid

/-- The **Relative Prominence Projection Rule** ([liberman-prince-1977]) as a homomorphism
    `Tree → MarkedGrid`: a σ-leaf is one `cell`; any other node juxtaposes its children, projecting
    across head edges and clearing the spine across the rest. -/
def project : Tree → MarkedGrid Tree :=
  RootedTree.Planar.fold fun a ps =>
    if a.isSyl ∧ ps = [] then cell (.node a [])
    else juxtapose (ps.map fun p => edge p.1.label.isHead p.2)

@[simp] theorem project_node (a : Constituent) (cs : List Tree) :
    project (.node a cs)
      = if a.isSyl ∧ cs = [] then cell (.node a [])
        else juxtapose (cs.map fun c => edge c.label.isHead (project c)) := by
  conv_lhs => rw [project, RootedTree.Planar.fold_node]
  simp only [List.map_eq_nil_iff]
  split
  · rfl
  · rw [List.map_map]; rfl

/-! ## Reading the grid off a tree (the forgetful maps) -/

variable (t : Tree)

/-- The σ-leaves of a tree, left to right: the terminal tier the grid sits over. -/
def terminals : List Tree := (project t).terminals

/-- The grid-column heights ([liberman-prince-1977]): each σ-leaf's height is `1` plus the
    contiguous run of head edges ending at it. -/
def columns : Grid := (project t).toGrid

/-- The **head terminals** (DTEs) — Liberman & Prince's *designated terminal elements*: the σ-leaves
    reached from the root by all head edges. -/
def headTerminals : List Tree := (project t).headTerminals

/-- The head terminals' prominences: the live cells' heights. -/
def headHeights : Grid := (project t).headHeights

/-- A tree is headed when it has a unique head terminal. -/
def IsHeaded : Prop := (headHeights t).length = 1

instance : Decidable (IsHeaded t) := by unfold IsHeaded; infer_instance

/-- The head terminal as a single element, if the tree is headed. -/
def headTerminal : Option Tree := (headTerminals t).head?

/-- The metrical grid of a tree, as stacked rows. -/
def ofTree : Marks := (columns t).rows

/-- `ofTree` always satisfies the Continuous Column Constraint ([prince-1983]; [hayes-1995]) — free
    from `Grid.rows_isContinuous`, since a projected grid is a histogram. -/
theorem ofTree_isContinuous : Marks.IsContinuous (ofTree t) := rows_isContinuous _

/-! ### The reader recursions

Each reader is a homomorphism out of the marked-grid algebra, so on a node it is the juxtaposition
of the children's readings, projected across head edges. These fuse `project_node` with the algebra
once, so the downstream proofs never re-walk the fold. -/

theorem columns_node (a : Constituent) (cs : List Tree) :
    columns (.node a cs)
      = if a.isSyl ∧ cs = [] then [1]
        else cs.flatMap fun c => (MarkedGrid.edge c.label.isHead (project c)).toGrid := by
  rw [columns, project_node]; split
  · rfl
  · rw [MarkedGrid.toGrid_juxtapose, List.flatMap_map]

theorem headHeights_node (a : Constituent) (cs : List Tree) :
    headHeights (.node a cs)
      = if a.isSyl ∧ cs = [] then [1]
        else cs.flatMap fun c => if c.label.isHead then (headHeights c).map (· + 1) else [] := by
  rw [headHeights, project_node]; split
  · rfl
  · rw [MarkedGrid.headHeights_juxtapose, List.flatMap_map]
    simp only [MarkedGrid.headHeights_edge]; rfl

theorem headTerminals_node (a : Constituent) (cs : List Tree) :
    headTerminals (.node a cs)
      = if a.isSyl ∧ cs = [] then [.node a []]
        else cs.flatMap fun c => if c.label.isHead then headTerminals c else [] := by
  rw [headTerminals, project_node]; split
  · rfl
  · rw [MarkedGrid.headTerminals_juxtapose, List.flatMap_map]
    simp only [MarkedGrid.headTerminals_edge]; rfl

/-! ### The head terminals compute the head-terminal relation -/

/-- `leaf` is a head terminal of `t`, reached from the root by an all-head descent. -/
inductive IsHeadTerminal : Tree → Tree → Prop
  | leaf (wt hd) : IsHeadTerminal (.node (.syl wt hd) []) (.node (.syl wt hd) [])
  | head {a cs c leaf} : c ∈ cs → c.label.isHead →
      IsHeadTerminal c leaf → IsHeadTerminal (.node a cs) leaf

/-- `headTerminals` computes the relation `IsHeadTerminal` — a clean, seed-free induction over the
    RPPR projection. -/
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
      · rintro h; cases h with
        | leaf => rfl
        | head hc => cases hc
    · rename_i hσ
      rw [List.mem_flatMap]
      constructor
      · rintro ⟨c, hc, hmem⟩
        by_cases hh : c.label.isHead = true
        · rw [if_pos hh] at hmem; exact .head hc hh ((IH c (by simpa using hc)).mp hmem)
        · rw [if_neg hh] at hmem; exact absurd hmem (List.not_mem_nil)
      · rintro h
        cases h with
        | leaf => simp [Constituent.isSyl] at hσ
        | head hc hhd hsub =>
          exact ⟨_, hc, by rw [if_pos hhd]; exact (IH _ (by simpa using hc)).mpr hsub⟩

/-! ## Head-preservation: the foot commuting square

Reading a `Foot`'s grid recovers its head — the depth-1 core of the transport story. -/

/-- A foot's grid is `2` at the head σ, `1` elsewhere. -/
theorem columns_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    columns (f.toProsTree w) = (Foot.toGrid f).map (fun b => if b then 2 else 1) := by
  rw [Foot.toProsTree, columns_node, if_neg (by simp [Constituent.isSyl]),
      List.flatMap_map, Foot.toGrid, List.map_map, List.map_eq_flatMap]
  refine List.flatMap_congr fun i _ => ?_
  by_cases hi : i = f.head <;>
    simp [project_node, Constituent.isSyl, Constituent.isHead, MarkedGrid.edge,
      MarkedGrid.promote, MarkedGrid.clear, MarkedGrid.toGrid, MarkedGrid.cell, hi]

/-- The grid's head row recovers `Foot.toGrid`. -/
theorem foot_headRow {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    (columns (f.toProsTree w)).map (fun h => decide (1 < h)) = Foot.toGrid f := by
  rw [columns_toProsTree, List.map_map]
  refine List.map_id'' (fun b => ?_) _
  cases b <;> rfl

/-- A foot's grid peaks at `2`. -/
theorem peak_toProsTree {S : Type*} (w : S → Syllable.Weight) (f : Foot S) :
    peak (columns (f.toProsTree w)) = 2 := by
  rw [columns_toProsTree]
  refine Nat.le_antisymm (peak_le fun x hx => ?_) (le_peak ?_)
  · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  · exact List.mem_map.mpr ⟨true,
      List.mem_map.mpr ⟨f.head, List.mem_finRange _, decide_eq_true_eq.mpr rfl⟩, rfl⟩

/-! ## What the grid forgets

The forgetful map onto the pure grid is one-way: it drops constituency (`ofTree_not_injective`;
[hayes-1995] §3.8 argues *for* bracketing precisely because the grid underdetermines it) and, under
recursion, order-invariant culminativity (`not_culminative_under_recursion`). -/

/-- `ofTree` is not injective: the grid forgets constituency ([hayes-1995] §3.8). -/
theorem ofTree_not_injective :
    ∃ t₁ t₂ : Tree, t₁ ≠ t₂ ∧ ofTree t₁ = ofTree t₂ :=
  ⟨.node .om [.node .ft [.node (.syl 1) []]], .node .om [.node (.syl 1) []],
    by decide, by decide⟩

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

/-! ## The word peak is the head terminal

On a non-recursive headed word the grid peak *is* the head terminal ([liberman-prince-1977]'s DTE):
metrical primary stress is the tallest column. Recursion is the sole obstruction, and — this being
[hayes-1995] §3.4.2(C)'s "the higher grid mark may only be assigned to a syllable that already bears
stress" — the peak sits atop a foot head. -/

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

/-- The depth of a child is at most the max child depth. -/
private theorem depth_le_depthMaxList {c : Tree} {cs : List Tree} (h : c ∈ cs) :
    c.depth ≤ RootedTree.Planar.depthMaxList cs := by
  induction cs with
  | nil => cases h
  | cons a as ih =>
    rw [show RootedTree.Planar.depthMaxList (a :: as)
          = max a.depth (RootedTree.Planar.depthMaxList as) from rfl]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

private theorem depthMaxList_le {cs : List Tree} {n : ℕ} (h : ∀ c ∈ cs, c.depth ≤ n) :
    RootedTree.Planar.depthMaxList cs ≤ n := by
  induction cs with
  | nil => exact Nat.zero_le n
  | cons a as ih =>
    rw [show RootedTree.Planar.depthMaxList (a :: as)
          = max a.depth (RootedTree.Planar.depthMaxList as) from rfl]
    exact max_le (h a (List.mem_cons_self ..)) (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- Non-recursive word children (feet and stray σ) have depth at most `2` — the ω→f→σ hierarchy. -/
private theorem depth_word_child_le {ch : Tree}
    (h : isFootTree ch = true ∨ (ch.label.isSyl = true ∧ ch.children = [])) : ch.depth ≤ 2 := by
  rcases h with hfoot | ⟨_, hcs⟩
  · obtain ⟨chl, chcs⟩ := ch
    simp only [isFootTree, Bool.and_eq_true, List.all_eq_true] at hfoot
    obtain ⟨_, hleaves⟩ := hfoot
    rw [show (RootedTree.Planar.node chl chcs).depth
          = 1 + RootedTree.Planar.depthMaxList chcs from rfl]
    have : RootedTree.Planar.depthMaxList chcs ≤ 1 := depthMaxList_le fun c hc => by
      obtain ⟨cl, ccs⟩ := c
      have hc' := hleaves _ hc
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hc'
      obtain ⟨_, rfl⟩ := hc'
      exact le_of_eq rfl
    omega
  · obtain ⟨chl, chcs⟩ := ch
    simp only [RootedTree.Planar.children_node] at hcs; subst hcs
    exact Nat.le_succ_of_le (le_of_eq rfl)

/-- Every grid column height is at most the tree depth: the RPPR count grows by one per head edge. -/
theorem toGrid_le_depth {t : Tree} : ∀ c ∈ columns t, c ≤ t.depth := by
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    rw [columns_node]
    split
    · intro c hc
      simp only [List.mem_singleton] at hc; subst hc
      rw [show RootedTree.Planar.depth (.node a cs) = 1 + RootedTree.Planar.depthMaxList cs from rfl]
      omega
    · intro c hc
      rw [List.mem_flatMap] at hc
      obtain ⟨ch, hch, hc⟩ := hc
      have hle : c ≤ ch.depth + 1 := by
        cases hh : ch.label.isHead with
        | false =>
          simp only [hh, MarkedGrid.edge_false, MarkedGrid.toGrid_clear] at hc
          exact le_trans (IH ch (by simpa using hch) c hc) (by omega)
        | true =>
          simp only [hh, MarkedGrid.edge_true, MarkedGrid.promote, MarkedGrid.toGrid, List.map_map,
            List.mem_map] at hc
          obtain ⟨x, hx, rfl⟩ := hc
          have := IH ch (by simpa using hch) x.height (List.mem_map.mpr ⟨x, hx, rfl⟩)
          by_cases hs : x.onSpine <;> simp [hs] <;> omega
      rw [show RootedTree.Planar.depth (.node a cs) = 1 + RootedTree.Planar.depthMaxList cs from rfl]
      have := depth_le_depthMaxList hch; omega

/-- Grid heights are positive. -/
theorem one_le_toGrid {t : Tree} : ∀ c ∈ columns t, 1 ≤ c := by
  induction t using Core.Order.Branching.inductionOn with
  | ih t IH =>
    obtain ⟨a, cs⟩ := t
    rw [columns_node]
    split
    · intro c hc; simp only [List.mem_singleton] at hc; omega
    · intro c hc
      rw [List.mem_flatMap] at hc
      obtain ⟨ch, hch, hc⟩ := hc
      cases hh : ch.label.isHead with
      | false =>
        simp only [hh, MarkedGrid.edge_false, MarkedGrid.toGrid_clear] at hc
        exact IH ch (by simpa using hch) c hc
      | true =>
        simp only [hh, MarkedGrid.edge_true, MarkedGrid.promote, MarkedGrid.toGrid, List.map_map,
          List.mem_map] at hc
        obtain ⟨x, hx, rfl⟩ := hc
        have := IH ch (by simpa using hch) x.height (List.mem_map.mpr ⟨x, hx, rfl⟩)
        by_cases hs : x.onSpine <;> simp [hs] <;> omega

/-- Head-terminal heights are a sublist of the columns. -/
theorem headHeights_sublist_columns (t : Tree) : (headHeights t).Sublist (columns t) :=
  List.filter_sublist.map _

/-- Every head-terminal height is at most the peak. -/
theorem headHeight_le_peak {t : Tree} {h : ℕ} (hh : h ∈ headHeights t) : h ≤ peak (columns t) :=
  le_peak ((headHeights_sublist_columns t).subset hh)

/-- An edge column is either a child column or a head height of the edge — the algebraic split that
    replaces the foot-internal case analysis. -/
theorem mem_toGrid_edge {h : Bool} {b : MarkedGrid Tree} {c : ℕ}
    (hc : c ∈ (edge h b).toGrid) : c ∈ b.toGrid ∨ c ∈ (edge h b).headHeights := by
  cases h with
  | false => exact .inl (by simpa using hc)
  | true =>
    simp only [MarkedGrid.edge_true, MarkedGrid.promote, MarkedGrid.toGrid, List.map_map,
      List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    by_cases hs : x.onSpine = true
    · refine .inr ?_
      simp only [MarkedGrid.edge_true, MarkedGrid.headHeights_promote, List.mem_map]
      exact ⟨x.height, List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, hs⟩, rfl⟩, by simp [hs]⟩
    · simp only [Bool.not_eq_true] at hs
      exact .inl (List.mem_map.mpr ⟨x, hx, by simp [hs]⟩)

/-- In a word every column is `≤ 2` unless it is a head-terminal height — the genuine non-recursion
    content, now one algebraic split (`mem_toGrid_edge`) plus the depth bound. -/
theorem col_le_two_or_head {t : Tree} (hw : IsWord t) (hr : noRec t = 0) :
    ∀ c ∈ columns t, c ≤ 2 ∨ c ∈ headHeights t := by
  obtain ⟨a, cs⟩ := t
  obtain ⟨ha, hchild⟩ := isWord_children hw hr
  have hσ : a.isSyl = false := Constituent.isSyl_eq_false_of_isOm ha
  intro c hc
  rw [columns_node, if_neg (by simp [hσ]), List.mem_flatMap] at hc
  obtain ⟨ch, hch, hc⟩ := hc
  rcases mem_toGrid_edge hc with hcol | hhead
  · exact .inl (le_trans (toGrid_le_depth c hcol) (depth_word_child_le (hchild ch hch)))
  · refine .inr ?_
    rw [headHeights_node, if_neg (by simp [hσ]), List.mem_flatMap]
    exact ⟨ch, hch, by rwa [MarkedGrid.headHeights_edge] at hhead⟩

/-- In a word the head terminal sits below ω, so its height is at least `2`. -/
theorem two_le_head {t : Tree} (hw : IsWord t) (hr : noRec t = 0)
    {h : ℕ} (hh : h ∈ headHeights t) : 2 ≤ h := by
  obtain ⟨a, cs⟩ := t
  obtain ⟨ha, _⟩ := isWord_children hw hr
  have hσ : a.isSyl = false := Constituent.isSyl_eq_false_of_isOm ha
  rw [headHeights_node, if_neg (by simp [hσ]), List.mem_flatMap] at hh
  obtain ⟨ch, hch, hh⟩ := hh
  split at hh
  · obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hh
    have : 1 ≤ h' := one_le_toGrid h' ((headHeights_sublist_columns ch).subset hh')
    omega
  · exact absurd hh (List.not_mem_nil)

/-- On a non-recursive headed word, the head terminal is the grid peak ([liberman-prince-1977]):
    metrical primary stress is the tallest column. -/
theorem headHeights_eq_peak {t : Tree} (hw : IsWord t) (hh : IsHeaded t) (hr : noRec t = 0) :
    headHeights t = [peak (columns t)] := by
  obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp hh
  have hvmem : v ∈ headHeights t := by rw [hv]; exact List.mem_singleton_self v
  have hge : peak (columns t) ≤ v := by
    refine peak_le fun c hc => ?_
    rcases col_le_two_or_head hw hr c hc with h2 | hmem
    · have := two_le_head hw hr hvmem; omega
    · rw [hv, List.mem_singleton] at hmem; omega
  rw [hv, le_antisymm (headHeight_le_peak hvmem) hge]

/-- Under recursion the peak can desert the head terminal, even when culminative
    ([ito-mester-2009] for recursive ω; the peak≠DTE consequence is a property of this model). -/
theorem head_below_peak_under_recursion :
    ∃ t : Tree, IsWord t ∧ IsHeaded t ∧ IsCulminative (columns t)
      ∧ headHeights t ≠ [peak (columns t)] :=
  ⟨.node .om [ .node (.syl 1 true) [],
               .node .om [.node (.ft true) [.node (.syl 1 true) []]] ],
    by decide, by decide, by decide, by decide⟩

/-- Without Layeredness the peak can desert the head terminal too. -/
theorem head_below_peak_unlayered :
    ∃ t : Tree, IsHeaded t ∧ noRec t = 0 ∧ ¬ IsWord t ∧ headHeights t ≠ [peak (columns t)] :=
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
example : peak (columns exWord) = 3 := by decide
example : ofTree exWord =
    [[true, true, true], [true, true, false], [true, false, false]] := by decide
example : Marks.IsContinuous (ofTree exWord) := by decide

end Grid

end Prosody
