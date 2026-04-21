import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.Partition.Lattice
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Subperm

/-!
# Partition Cells
@cite{groenendijk-stokhof-1984} @cite{merin-1999}

Concrete cell enumeration for partitions (`QUD`) over finite domains:

* `toCells` / `numCells` — `List`-based cells via greedy representative fold.
* `toFinpartition` — bridge to mathlib's `Finpartition` (exhaustivity and
  disjointness for free).
* `toCellsFinset` and helpers — `Finset`-based cells used by the decision-
  theoretic bridge in `Core/Agent/PartitionDT.lean`.

The two views are complementary: `toCells` gives a chosen ordering of
representatives (useful for induction), while `toCellsFinset` is unordered
and plays nicely with `Finset.sum_biUnion` decompositions.
-/

namespace QUD

variable {M : Type*}

/-! ### Finite Partition Cells -/

/-- Compute partition cells as Finsets over a finite domain.

Each cell is the set of elements equivalent to a representative, restricted
to the input list. Representatives are chosen greedily from the input list. -/
def toCells [DecidableEq M] (q : QUD M) (elements : List M) : List (Finset M) :=
  let representatives := elements.foldl (λ acc w =>
    if acc.any λ r => q.sameAnswer r w then acc else w :: acc
  ) []
  representatives.map λ rep => elements.toFinset.filter (q.sameAnswer rep ·)

/-- Number of cells in the partition over a finite domain. -/
def numCells [DecidableEq M] (q : QUD M) (elements : List M) : Nat :=
  (q.toCells elements).length

/-! #### Representative fold helpers -/

private abbrev stepFn (q : QUD M) : List M → M → List M :=
  fun acc w => if acc.any (fun r => q.sameAnswer r w) then acc else w :: acc

private theorem mem_repFold_of_mem_acc (q : QUD M) (elements : List M)
    (acc : List M) (r : M) (hr : r ∈ acc) :
    r ∈ elements.foldl (stepFn q) acc := by
  induction elements generalizing acc with
  | nil => exact hr
  | cons w ws ih =>
    simp only [List.foldl_cons]; apply ih; simp only [stepFn]
    split <;> [exact hr; exact .tail w hr]

private theorem mem_repFold_sub (q : QUD M) (elements : List M)
    (acc : List M) (r : M)
    (hr : r ∈ elements.foldl (stepFn q) acc) : r ∈ acc ∨ r ∈ elements := by
  induction elements generalizing acc with
  | nil => exact Or.inl hr
  | cons w ws ih =>
    simp only [List.foldl_cons] at hr
    cases ih _ hr with
    | inl h =>
      simp only [stepFn] at h; split at h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (.head ws)
        · exact Or.inl h
    | inr h => exact Or.inr (h.tail w)

private theorem repFold_covers (q : QUD M) (elements : List M)
    (acc : List M) (w : M) (hw : w ∈ elements) :
    ∃ r ∈ elements.foldl (stepFn q) acc, q.sameAnswer r w = true := by
  induction elements generalizing acc with
  | nil => exact absurd hw List.not_mem_nil
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hw with rfl | hmem
    · simp only [stepFn]; split
      case isTrue h =>
        obtain ⟨r, hr_mem, hr_eq⟩ := List.any_eq_true.mp h
        exact ⟨r, mem_repFold_of_mem_acc q xs _ r hr_mem, hr_eq⟩
      case isFalse _ =>
        exact ⟨w, mem_repFold_of_mem_acc q xs _ w (.head acc), q.refl w⟩
    · exact ih _ hmem

private theorem not_covered_mem (q : QUD M) {acc : List M} {r w : M}
    (hncov : ¬ (acc.any (fun s => q.sameAnswer s w) = true))
    (hr : r ∈ acc) : ¬ q.sameAnswer r w = true :=
  fun h => hncov (List.any_eq_true.mpr ⟨r, hr, h⟩)

private theorem stepFn_pairwiseInequiv (q : QUD M) (acc : List M) (w : M)
    (hpw : ∀ r1 ∈ acc, ∀ r2 ∈ acc, q.sameAnswer r1 r2 = true → r1 = r2) :
    ∀ r1 ∈ stepFn q acc w, ∀ r2 ∈ stepFn q acc w,
      q.sameAnswer r1 r2 = true → r1 = r2 := by
  simp only [stepFn]; split
  · exact hpw
  · rename_i hncov
    intro r1 hr1 r2 hr2 heq
    rcases List.mem_cons.mp hr1 with h1 | h1 <;> rcases List.mem_cons.mp hr2 with h2 | h2
    · exact h1.trans h2.symm
    · have heq' : q.sameAnswer r2 w = true := by rw [q.symm, ← h1]; exact heq
      exact absurd heq' (not_covered_mem q hncov h2)
    · have heq' : q.sameAnswer r1 w = true := by rw [← h2]; exact heq
      exact absurd heq' (not_covered_mem q hncov h1)
    · exact hpw r1 h1 r2 h2 heq

private theorem repFold_pairwiseInequiv (q : QUD M) (elements : List M)
    (acc : List M)
    (hpw : ∀ r1 ∈ acc, ∀ r2 ∈ acc, q.sameAnswer r1 r2 = true → r1 = r2) :
    ∀ r1 ∈ elements.foldl (stepFn q) acc,
      ∀ r2 ∈ elements.foldl (stepFn q) acc,
        q.sameAnswer r1 r2 = true → r1 = r2 := by
  induction elements generalizing acc with
  | nil => exact hpw
  | cons w ws ih =>
    simp only [List.foldl_cons]; exact ih _ (stepFn_pairwiseInequiv q acc w hpw)

private theorem repFold_nodup (q : QUD M) (elements : List M)
    (acc : List M) (hacc : acc.Nodup)
    (hpw : ∀ r1 ∈ acc, ∀ r2 ∈ acc, q.sameAnswer r1 r2 = true → r1 = r2) :
    (elements.foldl (stepFn q) acc).Nodup := by
  induction elements generalizing acc with
  | nil => exact hacc
  | cons w ws ih =>
    simp only [List.foldl_cons]; apply ih
    · simp only [stepFn]; split
      · exact hacc
      · rename_i hncov
        exact List.Nodup.cons
          (fun hw => hncov (List.any_eq_true.mpr ⟨w, hw, q.refl w⟩)) hacc
    · exact stepFn_pairwiseInequiv q acc w hpw

private theorem nodup_length_le_of_injOn {α β : Type*}
    (l1 : List α) (l2 : List β) (f : α → β) (hl1 : l1.Nodup)
    (hf_inj : ∀ x ∈ l1, ∀ y ∈ l1, f x = f y → x = y)
    (hf_mem : ∀ x ∈ l1, f x ∈ l2) :
    l1.length ≤ l2.length := by
  have hmap_nd := List.Nodup.map_on hf_inj hl1
  have hmap_sub : ∀ y ∈ l1.map f, y ∈ l2 := by
    intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hf_mem x hx
  calc l1.length = (l1.map f).length := (List.length_map f).symm
    _ ≤ l2.length := (hmap_nd.subperm hmap_sub).length_le

/-- Finer partitions have at least as many cells.

The covering map from q'-representatives to q-representatives is injective
(by pairwise inequivalence and refinement), giving `|q-reps| ≥ |q'-reps|`. -/
theorem refines_numCells_ge [DecidableEq M] (q q' : QUD M) (elements : List M) :
    q ⊑ q' → q.numCells elements >= q'.numCells elements := by
  intro hqq
  unfold numCells toCells
  simp only [List.length_map]
  set reps_q := elements.foldl (stepFn q) []
  set reps_q' := elements.foldl (stepFn q') []
  have hempty : ∀ (r1 : M), r1 ∈ ([] : List M) →
      ∀ r2 ∈ ([] : List M), (q.sameAnswer r1 r2 = true → r1 = r2) :=
    fun _ h1 => absurd h1 List.not_mem_nil
  have hempty' : ∀ (r1 : M), r1 ∈ ([] : List M) →
      ∀ r2 ∈ ([] : List M), (q'.sameAnswer r1 r2 = true → r1 = r2) :=
    fun _ h1 => absurd h1 List.not_mem_nil
  have hsub : ∀ r' ∈ reps_q', r' ∈ elements := by
    intro r' hr'
    rcases mem_repFold_sub q' elements [] r' hr' with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  have hcov : ∀ r' ∈ reps_q', ∃ r ∈ reps_q, q.sameAnswer r r' = true :=
    fun r' hr' => repFold_covers q elements [] r' (hsub r' hr')
  have hpw_q' : ∀ r1 ∈ reps_q', ∀ r2 ∈ reps_q',
      q'.sameAnswer r1 r2 = true → r1 = r2 :=
    repFold_pairwiseInequiv q' elements [] hempty'
  have hnd_q : reps_q.Nodup := repFold_nodup q elements [] List.nodup_nil hempty
  have hnd_q' : reps_q'.Nodup := repFold_nodup q' elements [] List.nodup_nil hempty'
  classical
  choose f hf_mem hf_cover using fun r' (hr' : r' ∈ reps_q') => hcov r' hr'
  let g : M → M := fun r' => if h : r' ∈ reps_q' then f r' h else r'
  exact nodup_length_le_of_injOn reps_q' reps_q g hnd_q'
    (fun r1 hr1 r2 hr2 hg => by
      simp only [g, dif_pos hr1, dif_pos hr2] at hg
      have hc1 := hf_cover r1 hr1; rw [hg] at hc1
      exact hpw_q' r1 hr1 r2 hr2 (hqq r1 r2
        (q.trans r1 (f r2 hr2) r2 (by rw [q.symm]; exact hc1) (hf_cover r2 hr2))))
    (fun x hx => by simp only [g, dif_pos hx]; exact hf_mem x hx)

/-- Cells of a QUD respect the equivalence relation: for any cell in `q.toCells worlds`,
if `q.sameAnswer w v = true` and both `w, v ∈ worlds`, then `w ∈ cell ↔ v ∈ cell`. -/
theorem toCells_sameAnswer_eq [DecidableEq M] (q : QUD M) (worlds : List M)
    (cell : Finset M) (hcell : cell ∈ q.toCells worlds) (w v : M)
    (hwmem : w ∈ worlds) (hvmem : v ∈ worlds)
    (hsame : q.sameAnswer w v = true) :
    (w ∈ cell ↔ v ∈ cell) := by
  simp only [toCells, List.mem_map] at hcell
  obtain ⟨rep, _, rfl⟩ := hcell
  simp only [Finset.mem_filter, List.mem_toFinset]
  refine ⟨fun ⟨_, hrw⟩ => ⟨hvmem, q.trans rep w v hrw hsame⟩,
          fun ⟨_, hrv⟩ => ⟨hwmem, q.trans rep v w hrv (by rw [q.symm]; exact hsame)⟩⟩

/-- Each fine cell is contained in some coarse cell (w.r.t. `toCells`).

If `q` refines `q'` (`q ⊑ q'`, finer partition), then for every fine cell
`c` of `q`, there exists a coarse cell of `q'` containing it. -/
theorem toCells_fine_sub_coarse [DecidableEq M] (q q' : QUD M)
    (worlds : List M) (hRefines : q ⊑ q')
    (c : Finset M) (hc : c ∈ q.toCells worlds) :
    ∃ c' ∈ q'.toCells worlds, c ⊆ c' := by
  simp only [toCells, List.mem_map] at hc ⊢
  obtain ⟨rep, hrep_mem, rfl⟩ := hc
  have hrep_worlds : rep ∈ worlds := by
    rcases mem_repFold_sub q worlds [] rep hrep_mem with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  obtain ⟨rep', hrep'_mem, hrep'_eq⟩ := repFold_covers q' worlds [] rep hrep_worlds
  refine ⟨worlds.toFinset.filter (q'.sameAnswer rep' ·),
          ⟨rep', hrep'_mem, rfl⟩, fun w hw => ?_⟩
  simp only [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, q'.trans rep' rep w hrep'_eq (hRefines rep w hw.2)⟩

/-- Each coarse cell contains some fine cell (w.r.t. `toCells`).

If `q'` refines `q` (`q' ⊑ q`, finer partition), then for every coarse cell
`c` of `q`, there exists a fine cell of `q'` contained in it. -/
theorem toCells_coarse_contains_fine [DecidableEq M] (q q' : QUD M)
    (worlds : List M) (hRefines : q' ⊑ q)
    (c : Finset M) (hc : c ∈ q.toCells worlds) :
    ∃ c' ∈ q'.toCells worlds, c' ⊆ c := by
  simp only [toCells, List.mem_map] at hc ⊢
  obtain ⟨rep, hrep_mem, rfl⟩ := hc
  have hrep_worlds : rep ∈ worlds := by
    rcases mem_repFold_sub q worlds [] rep hrep_mem with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  obtain ⟨rep', hrep'_mem, hrep'_eq⟩ := repFold_covers q' worlds [] rep hrep_worlds
  refine ⟨worlds.toFinset.filter (q'.sameAnswer rep' ·),
          ⟨rep', hrep'_mem, rfl⟩, fun w hw => ?_⟩
  simp only [Finset.mem_filter] at hw ⊢
  -- hw.2 : q'.sameAnswer rep' w = true
  -- Need: q.sameAnswer rep w = true
  have h1 : q'.sameAnswer rep rep' = true := by rw [q'.symm]; exact hrep'_eq
  have h2 : q'.sameAnswer rep w = true := q'.trans rep rep' w h1 hw.2
  exact ⟨hw.1, hRefines rep w h2⟩

/-- Each cell of `toCells` is nonempty: there exists an element in `elements`
that belongs to the cell (namely, the cell's representative). -/
theorem toCells_cell_nonempty [DecidableEq M] (q : QUD M) (elements : List M)
    (c : Finset M) (hc : c ∈ q.toCells elements) :
    ∃ w ∈ elements, w ∈ c := by
  simp only [toCells, List.mem_map] at hc
  obtain ⟨rep, hrep, rfl⟩ := hc
  have hrep_elem : rep ∈ elements := by
    rcases mem_repFold_sub q elements [] rep hrep with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  exact ⟨rep, hrep_elem, by
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨hrep_elem, q.refl rep⟩⟩

/-- `toCells` of a nonempty list is nonempty. Every element gets covered
by a representative, so at least one representative (and cell) exists. -/
theorem toCells_nonempty [DecidableEq M] (q : QUD M) (w : M) (ws : List M) :
    q.toCells (w :: ws) ≠ [] := by
  intro h
  -- Step 1: w is in the representative fold (first element always added)
  have hw : w ∈ (w :: ws).foldl (stepFn q) [] := by
    show w ∈ ws.foldl (stepFn q) (if ([] : List M).any (fun r => q.sameAnswer r w) then [] else w :: [])
    simp only [List.any_nil, Bool.false_eq_true, ite_false]
    exact mem_repFold_of_mem_acc q ws [w] w List.mem_cons_self
  -- Step 2: toCells = [] means the map input is [], contradicting hw
  have : (w :: ws).foldl (stepFn q) [] = [] := by
    unfold toCells at h
    match hfold : (w :: ws).foldl (stepFn q) [] with
    | [] => rfl
    | _ :: _ => rw [hfold] at h; simp at h
  rw [this] at hw
  exact List.not_mem_nil hw

/-- Every element in the input list belongs to some cell of `toCells`. -/
theorem toCells_covers [DecidableEq M] (q : QUD M) (elements : List M)
    (w : M) (hw : w ∈ elements) :
    ∃ c ∈ q.toCells elements, w ∈ c := by
  obtain ⟨r, hr, hsame⟩ := repFold_covers q elements [] w hw
  refine ⟨elements.toFinset.filter (q.sameAnswer r ·),
          List.mem_map.mpr ⟨r, hr, rfl⟩, ?_⟩
  simp only [Finset.mem_filter, List.mem_toFinset]
  exact ⟨hw, hsame⟩

/-- Every cell in `toCells` has a representative from the input list,
    and cell membership is `w ∈ elements ∧ q.sameAnswer rep w`. -/
theorem toCells_exists_rep [DecidableEq M] (q : QUD M) (elements : List M)
    (c : Finset M) (hc : c ∈ q.toCells elements) :
    ∃ rep ∈ elements, ∀ w, w ∈ c ↔ w ∈ elements ∧ q.sameAnswer rep w = true := by
  simp only [toCells, List.mem_map] at hc
  obtain ⟨rep, hrep, rfl⟩ := hc
  refine ⟨rep, ?_, fun w => by simp [Finset.mem_filter, List.mem_toFinset]⟩
  rcases mem_repFold_sub q elements [] rep hrep with h | h
  · exact absurd h List.not_mem_nil
  · exact h

/-! ### Finpartition from QUD -/

/-- The `Finpartition` induced by a QUD over a `Fintype`.

Uses Mathlib's `Finpartition.ofSetoid` — exhaustivity, disjointness, and
non-emptiness of cells come for free from the `Finpartition` structure. -/
def toFinpartition [Fintype M] [DecidableEq M] (q : QUD M) :
    Finpartition (Finset.univ : Finset M) :=
  Finpartition.ofSetoid q.toSetoid

/-! ### Finset-based Partition Cells -/

/-- Partition cells of worlds under QUD q, as a Finset of Finsets.
Each cell is the set of elements in worlds that are q-equivalent to some w. -/
def toCellsFinset [DecidableEq M] (q : QUD M) (worlds : Finset M) : Finset (Finset M) :=
  worlds.image (fun w => worlds.filter (fun v => q.sameAnswer w v))

/-- Every world belongs to some cell in `toCellsFinset`. -/
lemma toCellsFinset_covers [DecidableEq M] (q : QUD M) (worlds : Finset M) :
    (q.toCellsFinset worlds).biUnion id = worlds := by
  ext w; simp only [Finset.mem_biUnion, id, toCellsFinset, Finset.mem_image]
  constructor
  · rintro ⟨cell, ⟨v, hv, rfl⟩, hw⟩; exact (Finset.mem_filter.mp hw).1
  · intro hw
    exact ⟨worlds.filter (fun v => q.sameAnswer w v),
           ⟨w, hw, rfl⟩, Finset.mem_filter.mpr ⟨hw, q.refl w⟩⟩

/-- Cells from `toCellsFinset` are pairwise disjoint. -/
lemma toCellsFinset_pairwiseDisjoint [DecidableEq M]
    (q : QUD M) (worlds : Finset M) :
    (q.toCellsFinset worlds : Set (Finset M)).PairwiseDisjoint id := by
  intro c₁ hc₁ c₂ hc₂ hne
  simp only [Function.onFun, id]
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  exfalso; apply hne
  simp only [Finset.mem_coe, toCellsFinset, Finset.mem_image] at hc₁ hc₂
  obtain ⟨w₁, _, rfl⟩ := hc₁; obtain ⟨w₂, _, rfl⟩ := hc₂
  simp only [Finset.mem_filter] at hv₁ hv₂
  have h12 : q.sameAnswer w₁ w₂ = true :=
    q.trans w₁ v w₂ hv₁.2 (by rw [q.symm]; exact hv₂.2)
  ext u; simp only [Finset.mem_filter]
  exact ⟨fun ⟨hu, h1u⟩ => ⟨hu, q.trans w₂ w₁ u (by rw [q.symm]; exact h12) h1u⟩,
         fun ⟨hu, h2u⟩ => ⟨hu, q.trans w₁ w₂ u h12 h2u⟩⟩

/-- Under refinement, each fine cell is a subset of some coarse cell. -/
lemma fine_cell_sub_coarse_finset [DecidableEq M]
    (q q' : QUD M) (worlds : Finset M) (hrefines : q ⊑ q')
    (c : Finset M) (hc : c ∈ q.toCellsFinset worlds) :
    ∃ c' ∈ q'.toCellsFinset worlds, c ⊆ c' := by
  simp only [toCellsFinset, Finset.mem_image] at hc
  obtain ⟨w, hw, rfl⟩ := hc
  refine ⟨worlds.filter (fun v => q'.sameAnswer w v),
         Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_⟩
  intro v hv; simp only [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, hrefines w v hv.2⟩

/-- A coarse cell equals the union of fine cells within it. -/
lemma coarse_eq_biUnion_fine [DecidableEq M]
    (q q' : QUD M) (worlds : Finset M) (hrefines : q ⊑ q')
    (c' : Finset M) (hc' : c' ∈ q'.toCellsFinset worlds) :
    c' = ((q.toCellsFinset worlds).filter (· ⊆ c')).biUnion id := by
  simp only [toCellsFinset, Finset.mem_image] at hc'
  obtain ⟨w', hw', rfl⟩ := hc'
  ext v
  constructor
  · intro hv
    simp only [Finset.mem_filter] at hv
    rw [Finset.mem_biUnion]
    refine ⟨worlds.filter (fun u => q.sameAnswer v u), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_image.mpr ⟨v, hv.1, rfl⟩
      · intro u hu
        simp only [Finset.mem_filter] at hu ⊢
        exact ⟨hu.1, q'.trans w' v u hv.2 (hrefines v u hu.2)⟩
    · simp only [id]; exact Finset.mem_filter.mpr ⟨hv.1, q.refl v⟩
  · intro hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨cell, hcell, hv_in⟩ := hv
    simp only [id] at hv_in
    exact (Finset.mem_filter.mp hcell).2 hv_in

/-- Fine cells within a coarse cell are pairwise disjoint (inherited from the
fine partition being pairwise disjoint). -/
lemma fine_cells_in_coarse_pairwiseDisjoint [DecidableEq M]
    (q : QUD M) (worlds : Finset M) (c' : Finset M) :
    (((q.toCellsFinset worlds).filter (· ⊆ c')) : Set (Finset M)).PairwiseDisjoint id := by
  intro a ha b hb hab
  exact toCellsFinset_pairwiseDisjoint q worlds
    (Finset.mem_of_mem_filter a ha) (Finset.mem_of_mem_filter b hb) hab


end QUD
