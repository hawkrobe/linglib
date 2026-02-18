/-
Word Grammar (Dependency Grammar): nodes are words, edges are typed dependencies.
Auxiliaries are heads; lexical rules derive new entries; argument structures specify direction.

Dependency relations use UD.DepRel from Core/UD.lean (Universal Dependencies v2).

References: Hudson (1984, 1990, 2007), Gibson (2025) Syntax, MIT Press.
-/

import Linglib.Core.Basic
import Mathlib.Data.List.Basic

namespace DepGrammar

section DependenciesAndTrees

/-- A dependency: directed edge from head to dependent.
    Uses UD.DepRel for the relation label. -/
structure Dependency where
  headIdx : Nat
  depIdx : Nat
  depType : UD.DepRel
  deriving Repr, DecidableEq

/-- A dependency tree for a sentence. -/
structure DepTree where
  words : List Word
  deps : List Dependency
  rootIdx : Nat
  deriving Repr

/-- An enhanced dependency graph: like DepTree but allows multiple heads per word.
    Relaxes the unique-heads constraint (de Marneffe & Nivre 2019, §4.2). -/
structure DepGraph where
  words : List Word
  deps : List Dependency
  rootIdx : Nat
  deriving Repr

/-- Every DepTree is trivially a DepGraph. -/
def DepTree.toGraph (t : DepTree) : DepGraph :=
  { words := t.words, deps := t.deps, rootIdx := t.rootIdx }

end DependenciesAndTrees

-- ============================================================================
-- Projection: the foundational primitive for non-projectivity theory
-- ============================================================================

section Projection

/-- **Projection** π(i): the yield of node i — all nodes it transitively
    dominates, including itself — sorted in ascending order.

    The projection is the central primitive of Kuhlmann & Nivre (2006) and
    Kuhlmann (2013). Projectivity, gap degree, block-degree, edge degree,
    and well-nestedness are all defined in terms of projections.

    A dependency graph is **projective** iff every projection is an interval
    (Kuhlmann & Nivre 2006, Definition 3). -/
def projection (deps : List Dependency) (root : Nat) : List Nat :=
  let fuel := deps.length * (deps.length + 1) + 2
  let rec go (queue : List Nat) (visited : List Nat) (fuel : Nat) : List Nat :=
    match fuel, queue with
    | 0, _ => visited
    | _, [] => visited
    | fuel' + 1, node :: rest =>
      if visited.contains node then go rest visited fuel'
      else
        let children := deps.filter (·.headIdx == node) |>.map (·.depIdx)
        go (rest ++ children) (node :: visited) fuel'
  (go [root] [] fuel).mergeSort (· ≤ ·)

/-- Whether a sorted list of positions forms an interval [min..max] with no
    internal gaps. A projection is an interval iff its node has gap degree 0. -/
def isInterval (sorted : List Nat) : Bool :=
  match sorted with
  | [] | [_] => true
  | _ => sorted.getLast! - sorted.head! + 1 == sorted.length

/-- The **gaps** in a sorted projection: pairs (jₖ, jₖ₊₁) adjacent in the
    projection where jₖ₊₁ − jₖ > 1.
    (Kuhlmann & Nivre 2006, Definition 6; Kuhlmann 2013, §7.1) -/
def gaps (sorted : List Nat) : List (Nat × Nat) :=
  sorted.zip (sorted.drop 1) |>.filter λ (a, b) => b - a > 1

/-- The **blocks** of a sorted projection: maximal contiguous segments.
    (Kuhlmann 2013, §4.1)

    Example: projection [1, 2, 5, 6, 7] → blocks [[1, 2], [5, 6, 7]]

    The number of blocks equals gap degree + 1 and corresponds to the
    fan-out of the LCFRS rule extracted for that node (Kuhlmann 2013, §7.3). -/
def blocks : List Nat → List (List Nat)
  | [] => []
  | [a] => [[a]]
  | a :: b :: rest =>
    if b = a + 1 then
      match blocks (b :: rest) with
      | [] => [[a]]
      | first :: remaining => (a :: first) :: remaining
    else [a] :: blocks (b :: rest)

/-- **Gap degree** of a node: number of gaps in its projection.
    (Kuhlmann & Nivre 2006, Definition 6) -/
def gapDegreeAt (deps : List Dependency) (root : Nat) : Nat :=
  (gaps (projection deps root)).length

/-- **Gap degree** of a tree: max gap degree over all nodes.
    (Kuhlmann & Nivre 2006, Definition 7)
    Gap degree 0 ⟺ projective. -/
def DepTree.gapDegree (t : DepTree) : Nat :=
  List.range t.words.length |>.map (gapDegreeAt t.deps) |>.foldl max 0

/-- **Block-degree** of a node: number of blocks in its projection.
    (Kuhlmann 2013, §7.1)
    Block-degree = gap degree + 1 = fan-out of extracted LCFRS rule. -/
def blockDegreeAt (deps : List Dependency) (root : Nat) : Nat :=
  (blocks (projection deps root)).length

/-- **Block-degree** of a tree: max block-degree over all nodes.
    (Kuhlmann 2013, §7.1)
    Block-degree 1 ⟺ projective.
    Bounded block-degree + well-nestedness ⟺ polynomial parsing
    (Kuhlmann 2013, Lemma 10). -/
def DepTree.blockDegree (t : DepTree) : Nat :=
  List.range t.words.length |>.map (blockDegreeAt t.deps) |>.foldl max 0

-- ============================================================================
-- Projection Properties (proved from BFS structure)
-- ============================================================================

/-- BFS `go` produces a list with no duplicates when starting from Nodup visited. -/
private theorem go_nodup (deps : List Dependency)
    (queue visited : List Nat) (fuel : Nat)
    (hv : visited.Nodup) :
    (projection.go deps queue visited fuel).Nodup := by
  induction fuel generalizing queue visited with
  | zero => exact hv
  | succ fuel' ih =>
    match queue with
    | [] => exact hv
    | node :: rest =>
      simp only [projection.go]
      split
      · exact ih rest visited hv
      · rename_i hnotcontains
        apply ih
        have hnotin : node ∉ visited := by
          intro hmem
          apply hnotcontains
          simp only [List.contains_eq_any_beq, List.any_eq_true]
          exact ⟨node, hmem, beq_self_eq_true node⟩
        exact List.nodup_cons.mpr ⟨hnotin, hv⟩

/-- Sorted (≤) + no duplicates → strictly sorted (<). -/
private theorem pairwise_lt_of_sorted_nodup (l : List Nat)
    (hs : l.Pairwise (· ≤ ·)) (hn : l.Nodup) : l.Pairwise (· < ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
    rw [List.pairwise_cons] at hs ⊢
    obtain ⟨hnotin, hn_rest⟩ := List.nodup_cons.mp hn
    exact ⟨fun b hb => Nat.lt_of_le_of_ne (hs.1 b hb) (fun heq => hnotin (heq ▸ hb)),
           ih hs.2 hn_rest⟩

/-- The output of `projection` is strictly increasing (sorted, no duplicates).
    Proof: BFS visits each node at most once (visited check), then
    `mergeSort` produces a sorted list. Since visited prevents duplicates,
    the sorted list is strictly increasing. -/
theorem projection_chain' (deps : List Dependency) (root : Nat) :
    (projection deps root).IsChain (· < ·) := by
  unfold projection
  set goResult := projection.go deps [root] [] (deps.length * (deps.length + 1) + 2)
  have hnodup_go : goResult.Nodup := go_nodup deps [root] [] _ List.nodup_nil
  have hnodup : (goResult.mergeSort (· ≤ ·)).Nodup :=
    (List.mergeSort_perm goResult (· ≤ ·)).nodup_iff.mpr hnodup_go
  have hsorted : (goResult.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
    have h := @List.pairwise_mergeSort Nat (fun a b => decide (a ≤ b))
      (fun a b c hab hbc => decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
      (fun a b => by rcases Nat.le_total a b with h | h <;> simp [decide_eq_true h])
      goResult
    exact h.imp (fun hab => of_decide_eq_true hab)
  exact List.isChain_iff_pairwise.mpr (pairwise_lt_of_sorted_nodup _ hsorted hnodup)

/-- Elements in `visited` are preserved by `go`. -/
private theorem go_visited_subset (deps : List Dependency)
    (queue visited : List Nat) (fuel : Nat)
    (x : Nat) (hx : x ∈ visited) :
    x ∈ projection.go deps queue visited fuel := by
  induction fuel generalizing queue visited with
  | zero => exact hx
  | succ fuel' ih =>
    match queue with
    | [] => exact hx
    | node :: rest =>
      simp only [projection.go]
      split
      · exact ih rest visited hx
      · exact ih _ _ (List.mem_cons.mpr (Or.inr hx))

/-- root is always in the BFS output. -/
private theorem root_mem_go (deps : List Dependency) (root : Nat) :
    root ∈ projection.go deps [root] [] (deps.length * (deps.length + 1) + 2) := by
  have : deps.length * (deps.length + 1) + 2 = (deps.length * (deps.length + 1) + 1) + 1 := by omega
  rw [this]; simp only [projection.go, List.contains_nil]
  exact go_visited_subset deps _ _ _ root (List.mem_cons.mpr (Or.inl rfl))

/-- root is always in its own projection. -/
theorem root_mem_projection (deps : List Dependency) (root : Nat) :
    root ∈ projection deps root := by
  unfold projection
  exact (List.mergeSort_perm _ (· ≤ ·)).mem_iff.mpr (root_mem_go deps root)

/-- The output of `projection` is non-empty (root is always included). -/
theorem projection_nonempty (deps : List Dependency) (root : Nat) :
    projection deps root ≠ [] := by
  intro h; have := root_mem_projection deps root; rw [h] at this; simp at this

/-- BFS with empty queue returns visited unchanged. -/
private theorem go_empty_queue (deps : List Dependency)
    (visited : List Nat) (fuel : Nat) :
    projection.go deps [] visited fuel = visited := by
  cases fuel <;> rfl

/-- Projection of a node with no outgoing edges is just [root].

    Key step: BFS from root finds no children, so only root is visited.
    Used by `leaf_no_subtree_members` in HarmonicOrder.lean. -/
theorem projection_of_no_children (deps : List Dependency) (idx : Nat)
    (h : deps.filter (fun d => d.headIdx == idx) = []) :
    projection deps idx = [idx] := by
  unfold projection
  have : deps.length * (deps.length + 1) + 2 =
      (deps.length * (deps.length + 1) + 1) + 1 := by omega
  rw [this]
  simp only [projection.go, List.contains_nil]
  -- children = deps.filter (·.headIdx == idx) |>.map (·.depIdx)
  -- By h, filter = [], so children = [], so go ([] ++ []) [idx] fuel'
  simp only [h, List.map_nil, List.append_nil]
  rw [go_empty_queue]
  exact List.mergeSort_singleton idx

-- ============================================================================
-- BFS Queue Membership Lemmas (for child_mem_projection)
-- ============================================================================

/-- BFS queue invariant: if x appears after |pfx| elements in the queue,
    x ends up in the result, provided fuel ≥ |pfx| + 1.

    Each BFS step removes the queue head (by processing or skipping),
    so x advances toward the front. When x reaches the front (pfx = []),
    it is either already visited (stays in result) or gets added to visited. -/
private theorem go_mem_of_queue (deps : List Dependency)
    (pfx : List Nat) (x : Nat) (sfx visited : List Nat) (fuel : Nat)
    (hfuel : fuel ≥ pfx.length + 1) :
    x ∈ projection.go deps (pfx ++ x :: sfx) visited fuel := by
  induction pfx generalizing sfx visited fuel with
  | nil =>
    simp only [List.nil_append]
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp only [projection.go]
    split
    · rename_i hc
      have : x ∈ visited := by
        simp only [List.contains_eq_any_beq, List.any_eq_true] at hc
        obtain ⟨y, hy, hbeq⟩ := hc
        rwa [show y = x from (beq_iff_eq.mp hbeq).symm] at hy
      exact go_visited_subset deps sfx visited fuel' x this
    · exact go_visited_subset deps (sfx ++ _) (x :: visited) fuel' x
        (List.mem_cons.mpr (Or.inl rfl))
  | cons y ys ih =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp only [List.cons_append, projection.go]
    split
    · exact ih sfx visited fuel' (by simp only [List.length_cons] at hfuel; omega)
    · have : (ys ++ x :: sfx) ++ (deps.filter (·.headIdx == y) |>.map (·.depIdx))
          = ys ++ x :: (sfx ++ (deps.filter (·.headIdx == y) |>.map (·.depIdx))) := by
        simp only [List.append_assoc, List.cons_append]
      rw [this]
      exact ih (sfx ++ _) (y :: visited) fuel'
        (by simp only [List.length_cons] at hfuel; omega)

/-- The output of `projection` is a list with no duplicates.
    Follows from BFS visiting each node at most once (`go_nodup`), composed
    with the fact that `mergeSort` preserves the multiset (hence Nodup). -/
theorem projection_nodup (deps : List Dependency) (root : Nat) :
    (projection deps root).Nodup := by
  unfold projection
  set goResult := projection.go deps [root] [] (deps.length * (deps.length + 1) + 2)
  have hnodup_go : goResult.Nodup := go_nodup deps [root] [] _ List.nodup_nil
  exact (List.mergeSort_perm goResult (· ≤ ·)).nodup_iff.mpr hnodup_go

/-- If (v, w) is a dependency edge, then w ∈ projection deps v.
    Proof: BFS from v processes v first (adding children to queue),
    w is a child of v (by the edge), so w enters the queue and is processed. -/
theorem child_mem_projection (deps : List Dependency) (v w : Nat)
    (hedge : ∃ d ∈ deps, d.headIdx = v ∧ d.depIdx = w) :
    w ∈ projection deps v := by
  unfold projection
  set goResult := projection.go deps [v] [] (deps.length * (deps.length + 1) + 2)
  -- Suffices to show w ∈ goResult (membership preserved by mergeSort)
  suffices h : w ∈ goResult from
    (List.mergeSort_perm goResult (· ≤ ·)).mem_iff.mpr h
  -- Unfold one BFS step: go processes v, adding children to queue
  show w ∈ projection.go deps [v] [] (deps.length * (deps.length + 1) + 2)
  have hfuel_rw : deps.length * (deps.length + 1) + 2 =
      (deps.length * (deps.length + 1) + 1) + 1 := by omega
  rw [hfuel_rw]
  simp only [projection.go, List.contains_nil]
  -- State: go children [v] fuel' where children = filter/map, w ∈ children
  set children := deps.filter (·.headIdx == v) |>.map (·.depIdx) with children_def
  simp only [List.nil_append]
  -- Prove w ∈ children
  have hw_children : w ∈ children := by
    obtain ⟨d, hd_mem, hd_head, hd_dep⟩ := hedge
    exact List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hd_mem, by simp [hd_head]⟩, hd_dep⟩
  -- Case split: w = v (trivially in visited) or w ≠ v (use go_mem_of_queue)
  by_cases hvw : w = v
  · exact go_visited_subset deps children [v]
      (deps.length * (deps.length + 1) + 1) w (by simp [hvw])
  · obtain ⟨s, t, hst⟩ := List.append_of_mem hw_children
    rw [hst]
    apply go_mem_of_queue deps s w t [v]
      (deps.length * (deps.length + 1) + 1)
    -- Need: fuel ≥ s.length + 1
    have hplen : s.length < children.length := by
      have : children.length = s.length + 1 + t.length := by
        rw [hst, List.length_append, List.length_cons]; omega
      omega
    have hclen : children.length ≤ deps.length := by
      simp only [children_def, List.length_map]
      exact List.length_filter_le _ _
    -- deps.length ≤ deps.length * (deps.length + 1) + 1
    have hmul : deps.length ≤ deps.length * (deps.length + 1) + 1 := by
      calc deps.length = deps.length * 1 := (Nat.mul_one _).symm
        _ ≤ deps.length * (deps.length + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ deps.length * (deps.length + 1) + 1 := Nat.le_succ _
    omega

-- ============================================================================
-- List Helper Lemmas (for hierarchy theorem proofs)
-- ============================================================================

/-- For IsChain (· < ·), getLast! ≥ head + tail length. -/
private theorem chain_getLast_ge (a : Nat) (rest : List Nat)
    (h : (a :: rest).IsChain (· < ·)) :
    (a :: rest).getLast! ≥ a + rest.length := by
  induction rest generalizing a with
  | nil => simp [List.getLast!]
  | cons b rest' ih =>
    have hab : a < b := by
      have := h; simp [List.IsChain] at this; exact this.1
    have hchain : (b :: rest').IsChain (· < ·) := by
      have := h; simp [List.IsChain] at this; exact this.2
    have hih := ih b hchain
    have hlast : (a :: b :: rest').getLast! = (b :: rest').getLast! := by
      simp [List.getLast!]
    rw [hlast]
    simp only [List.length_cons]
    omega

/-- getLast! of a nonempty list is a member of that list. -/
private theorem getLast!_mem_cons (a : Nat) (rest : List Nat) :
    (a :: rest).getLast! ∈ (a :: rest) := by
  induction rest generalizing a with
  | nil => simp [List.getLast!]
  | cons b rest' ih =>
    have : (a :: b :: rest').getLast! = (b :: rest').getLast! := by simp [List.getLast!]
    rw [this]; exact .tail _ (ih b)

/-- A strictly increasing list of Nats with all elements in (lo, hi)
    has length ≤ hi - lo - 1. Proof: the head ≥ lo + 1, the last ≤ hi - 1,
    and `chain_getLast_ge` gives last ≥ head + (length - 1), so
    lo + 1 + (length - 1) ≤ hi - 1, giving length ≤ hi - lo - 1. -/
theorem chain_length_le_range (l : List Nat) (lo hi : Nat)
    (hchain : l.IsChain (· < ·))
    (hbounds : ∀ x ∈ l, lo < x ∧ x < hi) :
    l.length ≤ hi - lo - 1 := by
  induction hchain with
  | nil => simp
  | singleton a =>
    have ⟨halo, hahi⟩ := hbounds a (.head _)
    simp only [List.length_cons, List.length_nil]; omega
  | @cons_cons a b rest hab hchain _ =>
    have ⟨halo, _⟩ := hbounds a (.head _)
    have hlast_bound : (a :: b :: rest).getLast! < hi := by
      exact (hbounds _ (getLast!_mem_cons a (b :: rest))).2
    have hge := chain_getLast_ge a (b :: rest) (.cons_cons hab hchain)
    simp only [List.length_cons] at hge ⊢
    omega

/-- isInterval for a list with ≥ 2 elements reduces to an arithmetic check. -/
private theorem isInterval_eq_beq (a b : Nat) (rest : List Nat) :
    isInterval (a :: b :: rest) =
      ((a :: b :: rest).getLast! - a + 1 == (a :: b :: rest).length) := by
  rfl

/-- Convert isInterval to a Prop equality for ≥ 2-element lists. -/
private theorem isInterval_iff_eq (a b : Nat) (rest : List Nat) :
    isInterval (a :: b :: rest) = true ↔
      (a :: b :: rest).getLast! - a + 1 = (a :: b :: rest).length := by
  rw [isInterval_eq_beq]; simp [beq_iff_eq]

/-- Helper: gaps of a cons-cons list. -/
private theorem gaps_cons_cons (a b : Nat) (rest : List Nat) :
    gaps (a :: b :: rest) =
      if b - a > 1 then (a, b) :: gaps (b :: rest) else gaps (b :: rest) := by
  simp only [gaps, List.zip, List.drop, List.filter]
  split <;> simp_all

/-- For IsChain (· < ·) lists, isInterval = true ↔ gaps = []. -/
theorem isInterval_iff_gaps_nil (ls : List Nat) (h : ls.IsChain (· < ·)) :
    isInterval ls = true ↔ gaps ls = [] := by
  induction h with
  | nil => simp [isInterval, gaps]
  | singleton a => simp [isInterval, gaps]
  | @cons_cons a b rest hab hchain ih =>
    rw [gaps_cons_cons]
    have hlast_eq : (a :: b :: rest).getLast! = (b :: rest).getLast! := by
      simp [List.getLast!]
    have hge := chain_getLast_ge b rest hchain
    have hlen : (a :: b :: rest).length = rest.length + 2 := by simp [List.length_cons]
    constructor
    · -- Forward: isInterval → gaps = []
      intro hint
      have hp := (isInterval_iff_eq a b rest).mp hint
      rw [hlast_eq, hlen] at hp
      -- hp : (b :: rest).getLast! - a + 1 = rest.length + 2
      have hba : ¬(b - a > 1) := by intro hgap; omega
      simp only [hba, ↓reduceIte]
      have hba1 : b = a + 1 := by omega
      apply ih.mp
      match rest, hchain with
      | [], _ => simp [isInterval]
      | c :: rest', hchain' =>
        rw [isInterval_iff_eq]
        simp only [List.length_cons] at hp ⊢; omega
    · -- Backward: gaps = [] → isInterval
      intro hg
      have hba : ¬(b - a > 1) := by intro hgap; simp [hgap] at hg
      have hba1 : b = a + 1 := by omega
      simp only [hba, ↓reduceIte] at hg
      have ih_tl := ih.mpr hg
      rw [isInterval_iff_eq]; rw [hlast_eq, hlen]
      match rest, hchain, ih_tl with
      | [], _, _ => simp [List.getLast!]; omega
      | c :: rest', hchain', ih_tl' =>
        have ih_prop := (isInterval_iff_eq b c rest').mp ih_tl'
        simp only [List.length_cons] at ih_prop ⊢; omega

/-- `blocks` of a non-empty list is non-empty. -/
private theorem blocks_ne_nil (a : Nat) (rest : List Nat) :
    blocks (a :: rest) ≠ [] := by
  cases rest with
  | nil => simp [blocks]
  | cons b rest' =>
    simp only [blocks]
    split
    · split <;> exact List.cons_ne_nil _ _
    · exact List.cons_ne_nil _ _

/-- blocks length for a :: b :: rest when b = a + 1. -/
private theorem blocks_length_cons_succ (a b : Nat) (rest : List Nat)
    (hab : b = a + 1) :
    (blocks (a :: b :: rest)).length = (blocks (b :: rest)).length := by
  have h := blocks_ne_nil b rest
  show (if b = a + 1 then
      match blocks (b :: rest) with
      | [] => [[a]]
      | first :: remaining => (a :: first) :: remaining
    else [a] :: blocks (b :: rest)).length = _
  rw [if_pos hab]
  match hm : blocks (b :: rest) with
  | [] => exact absurd hm h
  | _ :: _ => rfl

/-- blocks length for a :: b :: rest when b ≠ a + 1. -/
private theorem blocks_length_cons_gap (a b : Nat) (rest : List Nat)
    (hab : ¬(b = a + 1)) :
    (blocks (a :: b :: rest)).length = (blocks (b :: rest)).length + 1 := by
  show (if b = a + 1 then
      match blocks (b :: rest) with
      | [] => [[a]]
      | first :: remaining => (a :: first) :: remaining
    else [a] :: blocks (b :: rest)).length = _
  rw [if_neg hab, List.length_cons]

/-- For non-empty strictly increasing lists, #blocks = #gaps + 1. -/
theorem blocks_length_eq_gaps_length_succ (ls : List Nat)
    (hne : ls ≠ []) (hc : ls.IsChain (· < ·)) :
    (blocks ls).length = (gaps ls).length + 1 := by
  induction hc with
  | nil => contradiction
  | singleton a => simp [blocks, gaps, List.zip, List.drop]
  | @cons_cons a b rest hab hchain ih =>
    rw [gaps_cons_cons]
    have hb_ne : (b :: rest) ≠ [] := List.cons_ne_nil b rest
    by_cases hgap : b - a > 1
    · have hba : ¬(b = a + 1) := by omega
      simp only [hgap, ↓reduceIte, List.length_cons]
      rw [blocks_length_cons_gap a b rest hba, ih hb_ne]
    · have hba : b = a + 1 := by omega
      simp only [hgap, ↓reduceIte]
      rw [blocks_length_cons_succ a b rest hba, ih hb_ne]

/-- For a strictly increasing interval list, every integer in [head!, getLast!]
    is a member. Proof by induction: isInterval + chain forces consecutive
    elements (b = a + 1), so each integer in the range appears. -/
theorem interval_mem_of_range : (l : List Nat) → l ≠ [] →
    l.IsChain (· < ·) → isInterval l = true →
    (x : Nat) → l.head! ≤ x → x ≤ l.getLast! → x ∈ l
  | [], hne, _, _, _, _, _ => absurd rfl hne
  | [a], _, _, _, x, hge, hle => by
    simp [List.head!, List.getLast!] at hge hle
    exact List.mem_cons.mpr (Or.inl (by omega))
  | a :: b :: rest, _, hchain, hint, x, hge, hle => by
    have hlast_eq : (a :: b :: rest).getLast! = (b :: rest).getLast! := by simp [List.getLast!]
    have hlen : (a :: b :: rest).length = rest.length + 2 := by simp [List.length_cons]
    have hab : a < b := by
      have := hchain; simp [List.IsChain] at this; exact this.1
    have hchain_tl : (b :: rest).IsChain (· < ·) := by
      have := hchain; simp [List.IsChain] at this; exact this.2
    have hp := (isInterval_iff_eq a b rest).mp hint
    rw [hlast_eq, hlen] at hp
    have hge_b := chain_getLast_ge b rest hchain_tl
    have hba : b = a + 1 := by omega
    have hint_tl : isInterval (b :: rest) = true := by
      match rest, hchain_tl with
      | [], _ => simp [isInterval]
      | c :: rest', hchain' =>
        rw [isInterval_iff_eq]
        simp only [List.length_cons] at hp ⊢; omega
    simp [List.head!] at hge
    by_cases hxa : x = a
    · subst hxa; exact List.mem_cons.mpr (Or.inl rfl)
    · have hxb : (b :: rest).head! ≤ x := by simp [List.head!]; omega
      have hle' : x ≤ (b :: rest).getLast! := by rwa [← hlast_eq]
      exact List.mem_cons.mpr (Or.inr (interval_mem_of_range (b :: rest) (List.cons_ne_nil _ _) hchain_tl hint_tl x hxb hle'))

/-- In a strictly increasing list, head! ≤ every element. -/
private theorem head_le_of_chain (l : List Nat) (hpw : l.Pairwise (· < ·))
    (y : Nat) (hy : y ∈ l) : l.head! ≤ y := by
  match l, hpw with
  | x :: rest, hpw' =>
    simp [List.head!]
    rcases List.mem_cons.mp hy with rfl | hmem
    · exact Nat.le_refl _
    · exact Nat.le_of_lt ((List.pairwise_cons.mp hpw').1 y hmem)

/-- In a strictly increasing list, every element ≤ getLast!. -/
private theorem le_getLast_of_chain : (l : List Nat) → l.Pairwise (· < ·) →
    (y : Nat) → y ∈ l → y ≤ l.getLast!
  | [a], _, y, hy => by
    simp [List.getLast!]; exact List.mem_cons.mp hy |>.elim (by omega) (by simp)
  | a :: b :: rest, hpw, y, hy => by
    have hlast : (a :: b :: rest).getLast! = (b :: rest).getLast! := by simp [List.getLast!]
    rw [hlast]
    rcases List.mem_cons.mp hy with rfl | hmem
    · have := (List.pairwise_cons.mp hpw).1 _ (getLast!_mem_cons b rest)
      omega
    · exact le_getLast_of_chain (b :: rest) (List.pairwise_cons.mp hpw).2 y hmem

/-- If a strictly increasing interval list contains `a` and `c` with
    `a < b < c`, then it contains `b`. -/
theorem interval_mem_between (l : List Nat)
    (hchain : l.IsChain (· < ·)) (hint : isInterval l = true)
    (a b c : Nat) (ha : a ∈ l) (hc : c ∈ l) (hab : a < b) (hbc : b < c) :
    b ∈ l := by
  have hpw := List.isChain_iff_pairwise.mp hchain
  have hne : l ≠ [] := by intro h; rw [h] at ha; simp at ha
  apply interval_mem_of_range l hne hchain hint
  · exact Nat.le_trans (head_le_of_chain l hpw a ha) (Nat.le_of_lt hab)
  · exact Nat.le_trans (Nat.le_of_lt hbc) (le_getLast_of_chain l hpw c hc)

-- ============================================================================
-- Prop-level Dominance (for mathematical proofs about projections)
-- ============================================================================

/-- Prop-level dominance: `Dominates deps v x` iff v transitively dominates x
    via dependency edges (head → dep). Defined as the reflexive-transitive
    closure of the parent relation. -/
inductive Dominates (deps : List Dependency) : Nat → Nat → Prop where
  | refl : (v : Nat) → Dominates deps v v
  | step : (v w x : Nat) → (∃ d ∈ deps, d.headIdx = v ∧ d.depIdx = w) →
           Dominates deps w x → Dominates deps v x

/-- Dominance is transitive. -/
theorem Dominates.trans {deps : List Dependency} {u v w : Nat}
    (huv : Dominates deps u v) (hvw : Dominates deps v w) :
    Dominates deps u w := by
  induction huv with
  | refl => exact hvw
  | step v' w' _ hedge _ ih => exact .step v' w' w hedge (ih hvw)

/-- If there is a direct edge (v, w), then v dominates w. -/
theorem Dominates.edge {deps : List Dependency} {v w : Nat}
    (h : ∃ d ∈ deps, d.headIdx = v ∧ d.depIdx = w) :
    Dominates deps v w :=
  .step v w w h (.refl w)

/-- BFS soundness: every node in the BFS output is either in the initial
    visited set or dominated by some node in the initial queue. -/
private theorem go_dominates_of_mem (deps : List Dependency)
    (queue visited : List Nat) (fuel : Nat) :
    ∀ x ∈ projection.go deps queue visited fuel,
      x ∈ visited ∨ ∃ q ∈ queue, Dominates deps q x := by
  induction fuel generalizing queue visited with
  | zero => intro x hx; exact Or.inl hx
  | succ fuel' ih =>
    match queue with
    | [] => intro x hx; exact Or.inl hx
    | node :: rest =>
      intro x hx
      simp only [projection.go] at hx
      split at hx
      · -- node ∈ visited: skip
        rename_i hcontains
        rcases ih rest visited x hx with h | ⟨q, hq, hdom⟩
        · exact Or.inl h
        · exact Or.inr ⟨q, List.mem_cons.mpr (Or.inr hq), hdom⟩
      · -- node ∉ visited: process
        rename_i hnotcontains
        rcases ih (rest ++ (deps.filter (·.headIdx == node) |>.map (·.depIdx)))
          (node :: visited) x hx with h | ⟨q, hq, hdom⟩
        · -- x ∈ node :: visited
          rcases List.mem_cons.mp h with rfl | hv
          · exact Or.inr ⟨x, List.mem_cons.mpr (Or.inl rfl), Dominates.refl x⟩
          · exact Or.inl hv
        · -- q ∈ rest ++ children
          rcases List.mem_append.mp hq with hr | hc
          · exact Or.inr ⟨q, List.mem_cons.mpr (Or.inr hr), hdom⟩
          · -- q ∈ children: edge (node, q)
            have hq_child : ∃ d ∈ deps, d.headIdx = node ∧ d.depIdx = q := by
              obtain ⟨d, hd_filter, hd_dep⟩ := List.mem_map.mp hc
              obtain ⟨hd_mem, hd_head⟩ := List.mem_filter.mp hd_filter
              exact ⟨d, hd_mem, beq_iff_eq.mp hd_head, hd_dep⟩
            exact Or.inr ⟨node, List.mem_cons.mpr (Or.inl rfl),
              Dominates.step node q x hq_child hdom⟩

/-- Backward bridge: BFS membership implies dominance. -/
theorem dominates_of_mem_projection {deps : List Dependency} {v x : Nat}
    (h : x ∈ projection deps v) : Dominates deps v x := by
  have hx_go : x ∈ projection.go deps [v] [] (deps.length * (deps.length + 1) + 2) := by
    simp only [projection, List.mem_mergeSort] at h
    exact h
  rcases go_dominates_of_mem deps [v] [] _ x hx_go with habs | ⟨q, hq, hdom⟩
  · exact nomatch habs
  · exact List.mem_singleton.mp hq ▸ hdom

/-- Fuel monotonicity: more fuel never loses BFS results. -/
private theorem go_mono_fuel (deps : List Dependency)
    (queue visited : List Nat) (f k : Nat) (x : Nat)
    (hx : x ∈ projection.go deps queue visited f) :
    x ∈ projection.go deps queue visited (f + k) := by
  induction f generalizing queue visited with
  | zero =>
    simpa [Nat.zero_add] using go_visited_subset deps queue visited k x hx
  | succ f' ih =>
    match queue with
    | [] =>
      rw [go_empty_queue] at hx; rw [go_empty_queue]; exact hx
    | node :: rest =>
      simp only [projection.go] at hx
      rw [Nat.add_right_comm]; simp only [projection.go]
      split at hx <;> split
      · exact ih rest visited hx
      · rename_i h1 h2; exact absurd h1 h2
      · rename_i h1 h2; exact absurd h2 h1
      · exact ih (rest ++ _) (node :: visited) hx

/-- If predicate `p` implies `q` on all list elements, then `filter p` is no longer than `filter q`. -/
private theorem filter_length_le_of_imp {α : Type*} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a as ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))
    simp only [List.filter]
    cases hp : p a <;> cases hq : q a
    · exact ih'
    · exact Nat.le_succ_of_le ih'
    · exact absurd (h a (List.mem_cons.mpr (Or.inl rfl)) hp)
        (by rw [hq]; exact Bool.noConfusion)
    · simp only [List.length_cons]; exact Nat.succ_le_succ ih'

/-- The old filter (not in visited) splits into: the new filter (not in node::visited)
    plus deps with headIdx == node. Key identity for the bfsPot invariant. -/
private theorem filter_split_at_node (deps : List Dependency)
    (visited : List Nat) (node : Nat)
    (hcont : visited.contains node = false) :
    (deps.filter (fun d => !(visited.contains d.headIdx))).length =
      (deps.filter (fun d => !((node :: visited).contains d.headIdx))).length +
      (deps.filter (fun d => d.headIdx == node)).length := by
  induction deps with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.filter]
    cases hv : visited.contains d.headIdx <;> cases hdn : (d.headIdx == node)
    · -- headIdx ∉ visited, headIdx ≠ node: in old filter and new filter, not in node filter
      have : (node :: visited).contains d.headIdx = false := by
        simp only [List.contains_cons, hv, hdn, Bool.false_or]
      simp only [hv, hdn, this, Bool.not_false, Bool.not_true, List.length_cons]; omega
    · -- headIdx ∉ visited, headIdx = node: in old filter and node filter, not in new filter
      have : (node :: visited).contains d.headIdx = true := by
        simp only [List.contains_cons, hdn, Bool.true_or]
      simp only [hv, hdn, this, Bool.not_false, Bool.not_true, List.length_cons]; omega
    · -- headIdx ∈ visited, headIdx ≠ node: not in any filter
      have : (node :: visited).contains d.headIdx = true := by
        simp only [List.contains_cons, hv, Bool.or_true]
      simp only [hv, hdn, this, Bool.not_false, Bool.not_true]; exact ih
    · -- headIdx ∈ visited, headIdx = node: impossible (node ∉ visited but d.headIdx = node ∈ visited)
      have := beq_iff_eq.mp hdn
      rw [this] at hv; exact absurd hv (by rw [hcont]; exact Bool.noConfusion)

/-- BFS potential: deps whose headIdx hasn't been visited + queue length.
    Decreases by exactly 1 each BFS step. -/
private abbrev bfsPot (deps : List Dependency) (queue visited : List Nat) : Nat :=
  (deps.filter (fun d => !(visited.contains d.headIdx))).length + queue.length

/-- BFS closure under children: if `w` ends up in the BFS output (wasn't in
    initial visited) and `c` is a child of `w`, then `c` is also in the output,
    provided fuel ≥ bfsPot + 1.

    The fuel bound is an invariant of BFS: each step decreases bfsPot by 1
    and consumes 1 fuel, so `fuel ≥ bfsPot + 1` is preserved across steps. -/
private theorem go_children_complete (deps : List Dependency)
    (queue visited : List Nat) (fuel : Nat) (w c : Nat)
    (hw : w ∈ projection.go deps queue visited fuel)
    (hw_not_vis : w ∉ visited)
    (hc : c ∈ (deps.filter (fun d => d.headIdx == w)).map (fun d => d.depIdx))
    (hfuel : fuel ≥ bfsPot deps queue visited + 1) :
    c ∈ projection.go deps queue visited fuel := by
  induction fuel generalizing queue visited with
  | zero => exact absurd (by simpa [projection.go] using hw) hw_not_vis
  | succ fuel' ih =>
    match queue with
    | [] => exact absurd (by simpa [projection.go] using hw) hw_not_vis
    | node :: rest =>
      simp only [projection.go] at hw ⊢
      by_cases hcont : (visited.contains node) = true
      · -- Skip: node ∈ visited. Queue shrinks by 1, filter unchanged → bfsPot decreases.
        simp only [hcont, ↓reduceIte] at hw ⊢
        apply ih rest visited hw hw_not_vis
        -- bfsPot (node :: rest) = bfsPot rest + 1 (same filter, queue shrinks by 1)
        have hstep : bfsPot deps (node :: rest) visited = bfsPot deps rest visited + 1 := by
          simp [bfsPot, List.length_cons, Nat.add_assoc]
        omega
      · -- Process: node ∉ visited
        have hcont_f : visited.contains node = false := by
          cases h : visited.contains node
          · rfl
          · exact absurd h hcont
        simp only [hcont, ↓reduceIte] at hw ⊢
        by_cases hwn : w = node
        · -- w IS the node being processed: c enters the queue
          subst hwn
          set children_node := (deps.filter (fun d => d.headIdx == w)).map (fun d => d.depIdx)
          obtain ⟨pfx, sfx, hpfx⟩ := List.append_of_mem
            (List.mem_append.mpr (Or.inr hc) : c ∈ rest ++ children_node)
          rw [hpfx]
          apply go_mem_of_queue deps pfx c sfx (w :: visited) fuel'
          have hpfx_bound : pfx.length < rest.length + children_node.length := by
            have := congrArg List.length hpfx
            simp [List.length_append, List.length_cons] at this; omega
          have hclen : children_node.length ≤
              (deps.filter (fun d => !(visited.contains d.headIdx))).length := by
            simp only [children_node, List.length_map]
            apply filter_length_le_of_imp
            intro d _ hd
            have heq : d.headIdx = w := beq_iff_eq.mp hd
            simp only [heq, hcont_f, Bool.not_false]
          -- Expand bfsPot to connect filter length, rest length, and fuel
          have hbfs : bfsPot deps (w :: rest) visited =
              (deps.filter (fun d => !(visited.contains d.headIdx))).length +
              rest.length + 1 := rfl
          omega
        · -- w ≠ node: IH on recursive call
          have hw_not_vis' : w ∉ (node :: visited) := by
            simp only [List.mem_cons, not_or]; exact ⟨hwn, hw_not_vis⟩
          apply ih (rest ++ _) (node :: visited) hw hw_not_vis'
          -- bfsPot decreases by exactly 1: the filter loses deps with headIdx == node,
          -- but queue gains exactly those deps' depIdx values, minus the removed front.
          have hsplit := filter_split_at_node deps visited node hcont_f
          have hstep : bfsPot deps (node :: rest) visited =
              bfsPot deps (rest ++ (deps.filter (fun d => d.headIdx == node)).map
                (fun d => d.depIdx)) (node :: visited) + 1 := by
            simp only [bfsPot, List.length_append, List.length_cons, List.length_map]
            omega
          omega

/-- Projection is closed under children: if `w ∈ projection deps r` and
    `(w, c)` is a dependency edge, then `c ∈ projection deps r`. -/
theorem projection_closed_under_children (deps : List Dependency) (r w c : Nat)
    (hw : w ∈ projection deps r)
    (hedge : ∃ d ∈ deps, d.headIdx = w ∧ d.depIdx = c) :
    c ∈ projection deps r := by
  unfold projection at hw ⊢
  rw [List.mem_mergeSort] at hw ⊢
  have hc_child : c ∈ (deps.filter (fun d => d.headIdx == w)).map (fun d => d.depIdx) := by
    obtain ⟨d, hd_mem, hd_head, hd_dep⟩ := hedge
    exact List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hd_mem, by simp [hd_head]⟩, hd_dep⟩
  apply go_children_complete deps [r] [] _ w c hw (fun h => nomatch h) hc_child
  -- bfsPot deps [r] [] = deps.length + 1 (filter is trivially all of deps since visited = [])
  have hfilt : (deps.filter (fun d => !(([] : List Nat).contains d.headIdx))).length
      = deps.length := by
    congr 1; apply List.filter_eq_self.mpr; intro d _; simp [List.contains_nil]
  simp only [bfsPot, List.length_cons, List.length_nil, hfilt]
  have : deps.length ≤ deps.length * (deps.length + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- If `w ∈ projection deps r` and `Dominates deps w x`, then `x ∈ projection deps r`. -/
private theorem mem_projection_of_dominated_member (deps : List Dependency)
    {r w x : Nat} (hw : w ∈ projection deps r) (h : Dominates deps w x) :
    x ∈ projection deps r := by
  induction h with
  | refl => exact hw
  | step _ w' _ hedge _ ih =>
    exact ih (projection_closed_under_children deps r _ w' hw hedge)

/-- Forward bridge: dominance implies BFS membership. -/
theorem mem_projection_of_dominates {deps : List Dependency} {v x : Nat}
    (h : Dominates deps v x) : x ∈ projection deps v :=
  mem_projection_of_dominated_member deps (root_mem_projection deps v) h

/-- **Bridge theorem**: BFS projection membership ↔ Prop-level dominance. -/
theorem dominates_iff_mem_projection (deps : List Dependency) (v x : Nat) :
    Dominates deps v x ↔ x ∈ projection deps v :=
  ⟨mem_projection_of_dominates, dominates_of_mem_projection⟩

end Projection

-- ============================================================================
-- Nat List Maximum Utilities (for foldl max 0 reasoning in hierarchy proofs)
-- ============================================================================

section FoldlMax

/-- `foldl max init ls ≥ init`. -/
theorem foldl_max_ge_init (ls : List Nat) (init : Nat) :
    ls.foldl max init ≥ init := by
  induction ls generalizing init with
  | nil => simp [List.foldl]
  | cons a as ih =>
    simp only [List.foldl]
    have := ih (max init a)
    omega

/-- `foldl max init ls ≥ x` for any `x ∈ ls`. -/
theorem foldl_max_ge_mem (ls : List Nat) (init : Nat) (x : Nat)
    (hx : x ∈ ls) : ls.foldl max init ≥ x := by
  induction ls generalizing init with
  | nil => contradiction
  | cons a as ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp hx with rfl | h
    · have := foldl_max_ge_init as (max init x)
      omega
    · exact ih (max init a) h

/-- `List.foldl max 0 ls = 0` iff every element of `ls` is 0. -/
theorem foldl_max_zero_iff (ls : List Nat) :
    ls.foldl max 0 = 0 ↔ ∀ x ∈ ls, x = 0 := by
  constructor
  · intro hfold x hx
    have hge := foldl_max_ge_mem ls 0 x hx
    omega
  · intro hall
    induction ls with
    | nil => rfl
    | cons a as ih =>
      simp only [List.foldl]
      have ha : a = 0 := hall a (List.mem_cons.mpr (Or.inl rfl))
      subst ha
      have : max 0 0 = 0 := by omega
      rw [this]
      exact ih (λ x hx => hall x (List.mem_cons.mpr (Or.inr hx)))

/-- If some element of `ls` is positive, then `List.foldl max 0 ls > 0`. -/
theorem foldl_max_pos_of_mem_pos (ls : List Nat) (x : Nat)
    (hx : x ∈ ls) (hpos : x > 0) :
    ls.foldl max 0 > 0 := by
  have hge := foldl_max_ge_mem ls 0 x hx
  omega

/-- `foldl max init ls ≤ bound` when `init ≤ bound` and all elements `≤ bound`. -/
theorem foldl_max_le_bound (ls : List Nat) (init bound : Nat)
    (hinit : init ≤ bound) (hall : ∀ x ∈ ls, x ≤ bound) :
    ls.foldl max init ≤ bound := by
  induction ls generalizing init with
  | nil => simpa [List.foldl]
  | cons a as ih =>
    simp only [List.foldl]
    apply ih (max init a)
    · have := hall a (.head _)
      omega
    · exact λ x hx => hall x (.tail _ hx)

/-- `foldl max 0 ls = k` when all elements are `k` and the list is non-empty. -/
theorem foldl_max_const (ls : List Nat) (k : Nat)
    (hne : ls ≠ []) (hall : ∀ x ∈ ls, x = k) :
    ls.foldl max 0 = k := by
  apply Nat.le_antisymm
  · exact foldl_max_le_bound ls 0 k (Nat.zero_le _)
      (λ x hx => Nat.le_of_eq (hall x hx))
  · match ls, hne with
    | a :: rest, _ =>
      have ha : a = k := hall a (.head _)
      have := foldl_max_ge_mem (a :: rest) 0 a (.head _)
      omega

end FoldlMax

section ArgumentStructure

/-- Direction of a dependent relative to head. -/
inductive Dir where
  | left   -- dependent precedes head
  | right  -- dependent follows head
  deriving Repr, DecidableEq, Inhabited

/-- A single argument slot in an argument structure. -/
structure ArgSlot where
  depType : UD.DepRel
  dir : Dir
  required : Bool := true
  cat : Option UD.UPOS := none
  deriving Repr, DecidableEq

/-- Argument structure: what dependents a word requires/allows. -/
structure ArgStr where
  slots : List ArgSlot
  deriving Repr

end ArgumentStructure

section WellFormedness

/-- Check if every word except root has exactly one head. -/
def hasUniqueHeads (t : DepTree) : Bool :=
  let n := t.words.length
  let inCounts := List.range n |>.map λ i =>
    t.deps.filter (·.depIdx == i) |>.length
  (List.range inCounts.length).zip inCounts |>.all λ (i, count) =>
    if i == t.rootIdx then count == 0 else count == 1

/-- Check for cycles: no word is its own ancestor. -/
def isAcyclic (t : DepTree) : Bool :=
  let n := t.words.length
  List.range n |>.all λ start =>
    let rec follow (current : Nat) (visited : List Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => true
      | fuel' + 1 =>
        if visited.contains current then false
        else
          match t.deps.find? (·.depIdx == current) with
          | some dep => follow dep.headIdx (current :: visited) fuel'
          | none => true
    follow start [] (n + 1)

/-- Check projectivity: every node's projection is an interval.
    (Kuhlmann & Nivre 2006, Definition 3)

    Equivalent to: no two dependency arcs cross.
    Equivalent to: gap degree = 0.
    Equivalent to: block-degree = 1. -/
def isProjective (t : DepTree) : Bool :=
  List.range t.words.length |>.all λ i =>
    isInterval (projection t.deps i)

/-- Bundled well-formedness: unique heads + valid index bounds.
    Collects the three hypotheses that most dominance/planarity theorems need. -/
structure DepTree.WF (t : DepTree) : Prop where
  uniqueHeads : hasUniqueHeads t = true
  depIdx_lt : ∀ d ∈ t.deps, d.depIdx < t.words.length
  headIdx_lt : ∀ d ∈ t.deps, d.headIdx < t.words.length

end WellFormedness

-- ============================================================================
-- Dominance Properties Under Unique Heads
-- ============================================================================

section DominanceUnderUniqueHeads

/-- In a tree with unique heads, the unique head of a non-root node. -/
private def uniqueHead (t : DepTree) (x : Nat) : Option Nat :=
  (t.deps.filter (·.depIdx == x)).head?.map (·.headIdx)

/-- With unique heads and acyclicity, the depth (distance to root) of any
    node is well-defined and finite. Following the unique head pointer from
    any node terminates at the root. -/
private def depth (t : DepTree) (x : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
    if x == t.rootIdx then 0
    else match t.deps.find? (·.depIdx == x) with
    | some d => depth t d.headIdx fuel' + 1
    | none => 0

/-- Adding one unit of fuel increases depth by at most 1. -/
private theorem depth_fuel_step (t : DepTree) (x : Nat) (k : Nat) :
    depth t x (k + 1) ≤ depth t x k + 1 := by
  induction k generalizing x with
  | zero =>
    simp only [depth]
    split <;> (try split) <;> omega
  | succ k' ih =>
    -- Unfold depth exactly one level on both sides via `change`
    show depth t x (k' + 1 + 1) ≤ depth t x (k' + 1) + 1
    change (if (x == t.rootIdx) = true then 0
            else match t.deps.find? (·.depIdx == x) with
            | some d => depth t d.headIdx (k' + 1) + 1
            | none => 0)
           ≤
           (if (x == t.rootIdx) = true then 0
            else match t.deps.find? (·.depIdx == x) with
            | some d => depth t d.headIdx k' + 1
            | none => 0) + 1
    by_cases hroot : (x == t.rootIdx) = true
    · simp [hroot]
    · rw [if_neg hroot, if_neg hroot]
      cases hfind : t.deps.find? (·.depIdx == x) with
      | none => simp
      | some d => exact Nat.add_le_add_right (ih d.headIdx) 1

/-- Extract from `hasUniqueHeads` for a specific node index: root has 0 incoming
    edges, non-root nodes have exactly 1. -/
private theorem hasUniqueHeads_count (t : DepTree)
    (hwf : hasUniqueHeads t = true) (c : Nat) (hc : c < t.words.length) :
    (if c = t.rootIdx then
      (t.deps.filter (·.depIdx == c)).length == 0
    else
      (t.deps.filter (·.depIdx == c)).length == 1) = true := by
  unfold hasUniqueHeads at hwf
  have hmem : (c, (t.deps.filter (·.depIdx == c)).length) ∈
    (List.range (List.map (λ i => (List.filter (·.depIdx == i) t.deps).length)
      (List.range t.words.length)).length).zip
      (List.map (λ i => (List.filter (·.depIdx == i) t.deps).length)
        (List.range t.words.length)) := by
    rw [List.mem_iff_getElem]
    simp only [List.length_zip, List.length_range, List.length_map]
    exact ⟨c, by omega, by simp [List.getElem_zip, List.getElem_range, List.getElem_map]⟩
  have h := (List.all_eq_true.mp hwf) _ hmem
  simp only [beq_iff_eq] at h
  exact h

/-- One dominance step: if edge (u, p) and `hasUniqueHeads`, then
    `depth u ≤ depth p` (with any fuel ≥ 1).

    Under `hasUniqueHeads`, `p ≠ rootIdx` and `find? (·.depIdx == p)` returns
    an edge with head = u. So `depth p (k+1) = depth u k + 1 ≥ depth u (k+1)`
    by `depth_fuel_step`. -/
private theorem depth_le_of_edge (t : DepTree)
    (hwf : hasUniqueHeads t = true) {u p : Nat}
    (hp_lt : p < t.words.length)
    (hedge : ∃ d ∈ t.deps, d.headIdx = u ∧ d.depIdx = p)
    (k : Nat) : depth t u (k + 1) ≤ depth t p (k + 1) := by
  obtain ⟨d, hd_mem, hd_head, hd_dep⟩ := hedge
  have hspec := hasUniqueHeads_count t hwf p hp_lt
  -- p ≠ rootIdx: root has 0 incoming edges, but d is incoming to p
  have hp_ne_root : p ≠ t.rootIdx := by
    intro hp_eq
    rw [if_pos hp_eq, beq_iff_eq] at hspec
    have : d ∈ t.deps.filter (·.depIdx == p) :=
      List.mem_filter.mpr ⟨hd_mem, beq_iff_eq.mpr hd_dep⟩
    have := List.length_pos_of_mem this
    omega
  rw [if_neg hp_ne_root, beq_iff_eq] at hspec
  -- filter has exactly 1 element; d is it
  obtain ⟨e, he_eq⟩ := List.length_eq_one_iff.mp hspec
  have hd_filter : d ∈ t.deps.filter (·.depIdx == p) :=
    List.mem_filter.mpr ⟨hd_mem, beq_iff_eq.mpr hd_dep⟩
  rw [he_eq] at hd_filter
  have hd_eq_e := List.eq_of_mem_singleton hd_filter
  -- find? returns some edge (since d has matching depIdx)
  have hfind_some : (t.deps.find? (·.depIdx == p)).isSome = true :=
    List.find?_isSome.mpr ⟨d, hd_mem, beq_iff_eq.mpr hd_dep⟩
  obtain ⟨f, hf_find⟩ := Option.isSome_iff_exists.mp hfind_some
  -- f has depIdx = p and f ∈ t.deps
  have hf_dep : f.depIdx = p := by
    have := List.find?_some hf_find; exact beq_iff_eq.mp this
  have hf_mem : f ∈ t.deps := List.mem_of_find?_eq_some hf_find
  -- f is in the filter, which is [e], so f = e = d
  have hf_filter : f ∈ t.deps.filter (·.depIdx == p) :=
    List.mem_filter.mpr ⟨hf_mem, beq_iff_eq.mpr hf_dep⟩
  rw [he_eq] at hf_filter
  have hf_eq_e := List.eq_of_mem_singleton hf_filter
  -- f.headIdx = u
  have hf_head : f.headIdx = u := by
    rw [hf_eq_e, ← hd_eq_e]; exact hd_head
  -- Unfold depth t p (k+1): since p ≠ rootIdx and find? = some f
  have hp_ne : ¬((p == t.rootIdx) = true) := by
    intro h; exact hp_ne_root (beq_iff_eq.mp h)
  have h_depth_p : depth t p (k + 1) = depth t u k + 1 := by
    change (if (p == t.rootIdx) = true then 0
            else match t.deps.find? (·.depIdx == p) with
            | some d => depth t d.headIdx k + 1
            | none => 0) = depth t u k + 1
    simp only [if_neg hp_ne, hf_find, hf_head]
  rw [h_depth_p]
  exact depth_fuel_step t u k

/-- If `Dominates v w`, then `depth v ≤ depth w` (non-strict).

    Each dominance step uses `depth_le_of_edge` + `depth_fuel_step`.
    Non-strict inequality suffices when combined with strict inequality
    for the proper-ancestor case (see `dominates_antisymm`). -/
private theorem dominates_depth_le (t : DepTree)
    (hwf : hasUniqueHeads t = true)
    (h_wf : ∀ d ∈ t.deps, d.depIdx < t.words.length)
    {v w : Nat} (h : Dominates t.deps v w) :
    depth t v t.words.length ≤ depth t w t.words.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | step v w' x hedge dom_w'_x ih =>
    obtain ⟨d, hd_mem, hd_head, hd_dep⟩ := hedge
    have hw'_lt : w' < t.words.length := hd_dep ▸ h_wf d hd_mem
    have hk : t.words.length - 1 + 1 = t.words.length := by omega
    have h1 : depth t v (t.words.length - 1 + 1) ≤
              depth t w' (t.words.length - 1 + 1) :=
      depth_le_of_edge t hwf hw'_lt ⟨d, hd_mem, hd_head, hd_dep⟩ _
    rw [hk] at h1
    exact Nat.le_trans h1 ih

-- ============================================================================
-- Parent-pointer tracing infrastructure for dominates_antisymm
-- ============================================================================

/-- The unique parent of node x (follows `find?` on depIdx). Returns x if no parent. -/
def parentOf_uh (t : DepTree) (x : Nat) : Nat :=
  match t.deps.find? (fun d => d.depIdx == x) with
  | some d => d.headIdx
  | none => x

/-- Iterate parentOf k times. -/
def iterParent_uh (t : DepTree) (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => parentOf_uh t (iterParent_uh t x k)

private theorem iterParent_add_uh (t : DepTree) (x : Nat) (a b : Nat) :
    iterParent_uh t x (a + b) = iterParent_uh t (iterParent_uh t x a) b := by
  induction b generalizing x a with
  | zero => simp [iterParent_uh]
  | succ b ih => simp only [iterParent_uh]; congr 1; exact ih x a

/-- `follow` returns false when current node is already visited. -/
private theorem follow_visited_uh (t : DepTree) (current : Nat)
    (visited : List Nat) (fuel : Nat)
    (h : visited.contains current = true) :
    isAcyclic.follow t current visited (fuel + 1) = false := by
  unfold isAcyclic.follow
  split
  · rfl
  · rename_i h2; exact absurd h h2

/-- `follow` steps through the unique parent edge. -/
private theorem follow_step_uh (t : DepTree) (current : Nat)
    (visited : List Nat) (fuel : Nat)
    (h1 : visited.contains current = false) (dep : Dependency)
    (h2 : t.deps.find? (fun d => d.depIdx == current) = some dep) :
    isAcyclic.follow t current visited (fuel + 1) =
    isAcyclic.follow t dep.headIdx (current :: visited) fuel := by
  conv_lhs => unfold isAcyclic.follow
  split
  · rename_i h3; exact absurd h3 (by rw [h1]; decide)
  · split
    · rename_i _ heq
      have := Option.some.inj (heq.symm.trans h2)
      subst this; rfl
    · rename_i _ heq; rw [h2] at heq; cases heq

/-- `follow` returns true when no parent edge exists. -/
private theorem follow_no_parent_uh (t : DepTree) (current : Nat)
    (visited : List Nat) (fuel : Nat)
    (h1 : visited.contains current = false)
    (h2 : t.deps.find? (fun d => d.depIdx == current) = none) :
    isAcyclic.follow t current visited (fuel + 1) = true := by
  unfold isAcyclic.follow
  split
  · rename_i h3; exact absurd h3 (by rw [h1]; decide)
  · split
    · rename_i _ heq; rw [h2] at heq; cases heq
    · rfl

/-- If `follow` returns false with fuel f, it also returns false with fuel f+1.
    (Cycles detected at depth f persist at depth f+1.) -/
private theorem follow_false_mono (t : DepTree) (x : Nat) (visited : List Nat)
    (f : Nat) (h : isAcyclic.follow t x visited f = false) :
    isAcyclic.follow t x visited (f + 1) = false := by
  induction f generalizing x visited with
  | zero => unfold isAcyclic.follow at h; exact absurd h (by decide)
  | succ f ih =>
    match hcv : visited.contains x with
    | true => exact follow_visited_uh t x visited (f + 1) hcv
    | false =>
      match hfind : t.deps.find? (fun d => d.depIdx == x) with
      | none =>
        have := follow_no_parent_uh t x visited f hcv hfind
        rw [this] at h; exact absurd h (by decide)
      | some dep =>
        rw [follow_step_uh t x visited f hcv dep hfind] at h
        rw [follow_step_uh t x visited (f + 1) hcv dep hfind]
        exact ih dep.headIdx (x :: visited) h

/-- Generalized monotonicity: false at fuel f implies false at any fuel f' ≥ f. -/
private theorem follow_false_mono_gen (t : DepTree) (x : Nat) (visited : List Nat)
    (f f' : Nat) (hff : f' ≥ f)
    (h : isAcyclic.follow t x visited f = false) :
    isAcyclic.follow t x visited f' = false := by
  obtain ⟨d, rfl⟩ : ∃ d, f' = f + d := ⟨f' - f, by omega⟩
  induction d with
  | zero => exact h
  | succ d ih => exact follow_false_mono t x visited _ (ih (by omega))

/-- If the iterParent chain revisits a node in `visited` after m steps,
    `follow` returns false. -/
private theorem follow_false_of_chain_revisit (t : DepTree)
    (current : Nat) (visited : List Nat)
    (m fuel : Nat) (hfuel : fuel ≥ m + 1)
    (hparents : ∀ i, i < m →
      ∃ dep, t.deps.find? (fun d => d.depIdx == iterParent_uh t current i) = some dep ∧
             dep.headIdx = iterParent_uh t current (i + 1))
    (hrevisit : visited.contains (iterParent_uh t current m) = true) :
    isAcyclic.follow t current visited fuel = false := by
  induction m generalizing current visited fuel with
  | zero =>
    have : iterParent_uh t current 0 = current := rfl
    rw [this] at hrevisit
    match fuel, hfuel with
    | fuel + 1, _ => exact follow_visited_uh t current visited fuel hrevisit
  | succ m' ih =>
    match fuel, hfuel with
    | fuel + 1, hfuel =>
      match hcv : visited.contains current with
      | true => exact follow_visited_uh t current visited fuel hcv
      | false =>
        obtain ⟨dep, hdep_find, hdep_head⟩ := hparents 0 (by omega)
        have : iterParent_uh t current 0 = current := rfl
        rw [this] at hdep_find
        rw [follow_step_uh t current visited fuel hcv dep hdep_find, hdep_head]
        apply ih
        · omega
        · intro i hi
          have hshift : ∀ j, iterParent_uh t (iterParent_uh t current 1) j =
                        iterParent_uh t current (j + 1) := by
            intro j; rw [← iterParent_add_uh]; congr 1; omega
          obtain ⟨dep', h1, h2⟩ := hparents (i + 1) (by omega)
          exact ⟨dep', hshift i ▸ h1, by rw [hshift (i + 1)]; convert h2 using 2⟩
        · have hshift : iterParent_uh t (iterParent_uh t current 1) m' =
                        iterParent_uh t current (m' + 1) := by
            rw [← iterParent_add_uh]; congr 1; omega
          rw [hshift]
          exact List.elem_eq_true_of_mem
            (List.mem_cons_of_mem current (List.mem_of_elem_eq_true hrevisit))

/-- If the iterParent chain cycles back to start after m+1 steps,
    `follow` from start with empty visited returns false. -/
private theorem follow_false_of_cycle (t : DepTree)
    (start : Nat) (m fuel : Nat) (hfuel : fuel ≥ m + 2)
    (hparents : ∀ i, i ≤ m →
      ∃ dep, t.deps.find? (fun d => d.depIdx == iterParent_uh t start i) = some dep ∧
             dep.headIdx = iterParent_uh t start (i + 1))
    (hcycle : iterParent_uh t start (m + 1) = start) :
    isAcyclic.follow t start [] fuel = false := by
  match fuel, hfuel with
  | fuel + 1, hfuel =>
    obtain ⟨dep, hdep_find, hdep_head⟩ := hparents 0 (by omega)
    have : iterParent_uh t start 0 = start := rfl
    rw [this] at hdep_find
    rw [follow_step_uh t start [] fuel (by rfl) dep hdep_find, hdep_head]
    apply follow_false_of_chain_revisit t (iterParent_uh t start 1) [start] m fuel
    · omega
    · intro i hi
      have hshift : ∀ j, iterParent_uh t (iterParent_uh t start 1) j =
                    iterParent_uh t start (j + 1) := by
        intro j; rw [← iterParent_add_uh]; congr 1; omega
      obtain ⟨dep', h1, h2⟩ := hparents (i + 1) (by omega)
      exact ⟨dep', hshift i ▸ h1, by rw [hshift (i + 1)]; convert h2 using 2⟩
    · have hshift : iterParent_uh t (iterParent_uh t start 1) m =
                    iterParent_uh t start (m + 1) := by
        rw [← iterParent_add_uh]; congr 1; omega
      rw [hshift, hcycle]
      exact List.elem_eq_true_of_mem List.mem_cons_self

/-- Extract from `isAcyclic`: `follow v [] (n+1) = true` for v < n. -/
private theorem isAcyclic_follow_uh (t : DepTree) (hacyc : isAcyclic t = true)
    (v : Nat) (hv : v < t.words.length) :
    isAcyclic.follow t v [] (t.words.length + 1) = true := by
  unfold isAcyclic at hacyc
  exact List.all_eq_true.mp hacyc v (List.mem_range.mpr hv)

/-- `parentOf_uh` equals the headIdx from `find?`. -/
private theorem parentOf_eq_find_uh (t : DepTree) (x : Nat) {dep : Dependency}
    (hfind : t.deps.find? (fun d => d.depIdx == x) = some dep) :
    parentOf_uh t x = dep.headIdx := by
  simp [parentOf_uh, hfind]

/-- Under unique heads, if edge(v, c) exists, then `parentOf c = v`. -/
theorem parentOf_of_edge_uh (t : DepTree)
    (hwf : t.WF)
    {v c : Nat} (hedge : ∃ d ∈ t.deps, d.headIdx = v ∧ d.depIdx = c) :
    parentOf_uh t c = v := by
  obtain ⟨d, hd_mem, hd_head, hd_dep⟩ := hedge
  have hfind_some : (t.deps.find? (fun d => d.depIdx == c)).isSome = true :=
    List.find?_isSome.mpr ⟨d, hd_mem, beq_iff_eq.mpr hd_dep⟩
  obtain ⟨f, hf_find⟩ := Option.isSome_iff_exists.mp hfind_some
  rw [parentOf_eq_find_uh t c hf_find]
  have hf_mem := List.mem_of_find?_eq_some hf_find
  have hf_dep : f.depIdx = c := by
    have h := @List.find?_some _ (fun d => d.depIdx == c) f t.deps hf_find
    exact (beq_iff_eq (α := Nat)).mp h
  have hc_lt := hd_dep ▸ hwf.depIdx_lt d hd_mem
  have hspec := hasUniqueHeads_count t hwf.uniqueHeads c hc_lt
  have hc_ne_root : c ≠ t.rootIdx := by
    intro heq; rw [if_pos heq, beq_iff_eq] at hspec
    have : d ∈ t.deps.filter (·.depIdx == c) :=
      List.mem_filter.mpr ⟨hd_mem, (beq_iff_eq (α := Nat)).mpr hd_dep⟩
    exact absurd hspec (by have := List.length_pos_of_mem this; omega)
  rw [if_neg hc_ne_root, beq_iff_eq] at hspec
  obtain ⟨e, he_eq⟩ := List.length_eq_one_iff.mp hspec
  have hd_beq : (d.depIdx == c) = true := (beq_iff_eq (α := Nat)).mpr hd_dep
  have hf_beq : (f.depIdx == c) = true := (beq_iff_eq (α := Nat)).mpr hf_dep
  have hd_in : d ∈ t.deps.filter (·.depIdx == c) :=
    List.mem_filter.mpr ⟨hd_mem, hd_beq⟩
  have hf_in : f ∈ t.deps.filter (·.depIdx == c) :=
    List.mem_filter.mpr ⟨hf_mem, hf_beq⟩
  rw [he_eq] at hd_in hf_in
  have := List.eq_of_mem_singleton hd_in
  have := List.eq_of_mem_singleton hf_in
  rw [‹f = e›, ← ‹d = e›, hd_head]

/-- Under unique heads, `Dominates v w` with v ≠ w implies the iterParent chain
    from w reaches v, with valid parent edges at each step. -/
theorem dominates_iterParent_uh (t : DepTree)
    (hwf : t.WF)
    {v w : Nat} (hdom : Dominates t.deps v w) (hne : v ≠ w) :
    ∃ k : Nat, k > 0 ∧ iterParent_uh t w k = v ∧
      (∀ i, i < k → ∃ dep, t.deps.find? (fun d => d.depIdx == iterParent_uh t w i) = some dep ∧
                            dep.headIdx = iterParent_uh t w (i + 1)) := by
  induction hdom with
  | refl => exact absurd rfl hne
  | step u c x hedge hcx ih =>
    by_cases hc_eq : c = x
    · -- One step: edge(u, c). parentOf c = u.
      subst hc_eq
      have hpo := parentOf_of_edge_uh t hwf hedge
      refine ⟨1, by omega, ?_, ?_⟩
      · show parentOf_uh t c = u; exact hpo
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        have hfind_some : (t.deps.find? (fun d => d.depIdx == c)).isSome = true := by
          obtain ⟨d, hd_mem, _, hd_dep⟩ := hedge
          exact List.find?_isSome.mpr ⟨d, hd_mem, beq_iff_eq.mpr hd_dep⟩
        obtain ⟨f, hf_find⟩ := Option.isSome_iff_exists.mp hfind_some
        exact ⟨f, hf_find, (parentOf_eq_find_uh t c hf_find).symm⟩
    · -- Multiple steps: by IH, ∃ k, iterParent x k = c
      obtain ⟨k, hk, hiter, hchain⟩ := ih hc_eq
      have hpo := parentOf_of_edge_uh t hwf hedge
      refine ⟨k + 1, by omega, ?_, ?_⟩
      · show parentOf_uh t (iterParent_uh t x k) = u
        rw [hiter, hpo]
      · intro i hi
        by_cases hi_lt : i < k
        · exact hchain i hi_lt
        · have hik : i = k := by omega
          subst hik
          rw [hiter]
          have hfind_some : (t.deps.find? (fun d => d.depIdx == c)).isSome = true := by
            obtain ⟨d, hd_mem, _, hd_dep⟩ := hedge
            exact List.find?_isSome.mpr ⟨d, hd_mem, beq_iff_eq.mpr hd_dep⟩
          obtain ⟨f, hf_find⟩ := Option.isSome_iff_exists.mp hfind_some
          exact ⟨f, hf_find, by
            show f.headIdx = parentOf_uh t (iterParent_uh t x i)
            rw [hiter]; exact (parentOf_eq_find_uh t c hf_find).symm⟩

/-- If `Dominates v w` with v ≠ w, then w is a depIdx in some edge, hence < n. -/
private theorem dominates_depIdx_lt (t : DepTree)
    (h_dep_wf : ∀ d ∈ t.deps, d.depIdx < t.words.length)
    {v w : Nat} (hdom : Dominates t.deps v w) (hne : v ≠ w) :
    w < t.words.length := by
  induction hdom with
  | refl => exact absurd rfl hne
  | step u c x hedge _ ih =>
    by_cases hcx : c = x
    · subst hcx
      obtain ⟨d, hd_mem, _, hd_dep⟩ := hedge
      exact hd_dep ▸ h_dep_wf d hd_mem
    · exact ih hcx

/-- Each node in the iterParent chain (with valid parent edges) is a depIdx < n. -/
private theorem iterParent_chain_lt (t : DepTree)
    (h_dep_wf : ∀ d ∈ t.deps, d.depIdx < t.words.length)
    (start : Nat) (k : Nat) (i : Nat) (hi : i < k)
    (hchain : ∀ j, j < k →
      ∃ dep, t.deps.find? (fun d => d.depIdx == iterParent_uh t start j) = some dep ∧
             dep.headIdx = iterParent_uh t start (j + 1)) :
    iterParent_uh t start i < t.words.length := by
  obtain ⟨dep, hdep_find, _⟩ := hchain i hi
  have hdep_mem := List.mem_of_find?_eq_some hdep_find
  have hdep_pred := List.find?_some hdep_find
  have hdep_eq : dep.depIdx = iterParent_uh t start i := by
    exact beq_iff_eq.mp hdep_pred
  exact hdep_eq ▸ h_dep_wf dep hdep_mem

/-- A nodup list of natural numbers all less than n has length ≤ n
    (pigeonhole principle, proved by induction on n). -/
private theorem nodup_bound (l : List Nat) (n : Nat)
    (hnd : l.Nodup) (hb : ∀ x ∈ l, x < n) : l.length ≤ n := by
  induction n generalizing l with
  | zero =>
    have : l = [] := by
      cases l with
      | nil => rfl
      | cons x xs =>
        have : x ∈ x :: xs := List.mem_cons_self
        exact absurd (hb x this) (Nat.not_lt_zero x)
    simp [this]
  | succ n ih =>
    by_cases hn : n ∈ l
    · have h1 := List.length_erase_of_mem hn
      have h2 : (l.erase n).Nodup := hnd.erase n
      have h3 : ∀ x ∈ l.erase n, x < n := by
        intro x hx
        have hx_mem : x ∈ l := List.mem_of_mem_erase hx
        have hx_lt : x < n + 1 := hb x hx_mem
        have hx_ne : x ≠ n := by
          intro heq; subst heq; exact (List.Nodup.not_mem_erase hnd) hx
        omega
      have := ih (l.erase n) h2 h3
      omega
    · have hb' : ∀ x ∈ l, x < n := by
        intro x hx
        have := hb x hx
        have hne : x ≠ n := fun heq => by subst heq; exact hn hx
        omega
      have := ih l hnd hb'
      omega

/-- `List.ofFn f` is nodup when f is injective. -/
private theorem ofFn_nodup_of_injective {α : Type*} [DecidableEq α] {n : Nat}
    {f : Fin n → α} (hinj : Function.Injective f) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.nodup_cons]
    constructor
    · rw [List.mem_ofFn]
      rintro ⟨j, hj⟩
      exact (Fin.succ_ne_zero j) (hinj hj)
    · apply ih
      intro a b hab
      have : f a.succ = f b.succ := hab
      exact Fin.succ_inj.mp (hinj this)

/-- The iterParent chain length from a dominance derivation is bounded by n.

    If k > n, the first n+1 chain values are n+1 distinct values in `[0, n)`.
    Distinctness: any duplicate at positions `i < j ≤ n` creates a sub-cycle
    of length `j - i ≤ n`, detectable by `follow_false_of_cycle` with fuel
    `n + 1 ≥ j - i + 1`. But `isAcyclic = true`, contradiction.
    Then `nodup_bound` gives `n + 1 ≤ n`, contradiction. -/
theorem iterParent_chain_bound (t : DepTree)
    (hacyc : isAcyclic t = true)
    (h_dep_wf : ∀ d ∈ t.deps, d.depIdx < t.words.length)
    (start : Nat) (k : Nat)
    (hchain : ∀ i, i < k →
      ∃ dep, t.deps.find? (fun d => d.depIdx == iterParent_uh t start i) = some dep ∧
             dep.headIdx = iterParent_uh t start (i + 1))
    (hstart_lt : start < t.words.length) :
    k ≤ t.words.length := by
  by_contra hk
  -- k > n = t.words.length. Consider first n+1 chain values.
  set n := t.words.length with hn_def
  -- f maps [0, n+1) to chain values
  let f : Fin (n + 1) → Nat := fun i => iterParent_uh t start i.val
  -- All values < n
  have hvals : ∀ i : Fin (n + 1), f i < n := by
    intro ⟨i, hi⟩
    simp only [f]
    rcases i with _ | i
    · exact hstart_lt
    · exact iterParent_chain_lt t h_dep_wf start k (i + 1) (by omega) hchain
  -- f is injective (any duplicate creates a detectable sub-cycle)
  have hinj : Function.Injective f := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    simp only [f, Fin.mk.injEq] at heq ⊢
    by_contra hij
    -- heq : iterParent_uh t start i = iterParent_uh t start j, i ≠ j
    rcases Nat.lt_or_gt_of_ne hij with h_lt | h_lt
    · -- i < j ≤ n: sub-cycle of length j - i ≤ n
      have v_lt : iterParent_uh t start i < n := hvals ⟨i, hi⟩
      have hcyc : iterParent_uh t (iterParent_uh t start i) (j - i) =
                  iterParent_uh t start i := by
        rw [← iterParent_add_uh]; convert heq.symm using 2; omega
      have hsub : ∀ p, p ≤ j - i - 1 →
          ∃ dep, t.deps.find? (fun d => d.depIdx ==
            iterParent_uh t (iterParent_uh t start i) p) = some dep ∧
            dep.headIdx = iterParent_uh t (iterParent_uh t start i) (p + 1) := by
        intro p hp
        have hshift : ∀ q, iterParent_uh t (iterParent_uh t start i) q =
                      iterParent_uh t start (i + q) := by
          intro q; rw [← iterParent_add_uh]
        rw [hshift p, hshift (p + 1)]
        exact hchain (i + p) (by omega)
      have hcyc' : iterParent_uh t (iterParent_uh t start i) (j - i - 1 + 1) =
                   iterParent_uh t start i := by
        convert hcyc using 2; omega
      -- fuel n+1 ≥ (j-i-1)+2 because j-i ≤ n
      have hfalse := follow_false_of_cycle t (iterParent_uh t start i)
        (j - i - 1) (n + 1) (by omega) hsub hcyc'
      have htrue := isAcyclic_follow_uh t hacyc _ v_lt
      rw [hfalse] at htrue; exact absurd htrue (by decide)
    · -- j < i: symmetric
      have v_lt : iterParent_uh t start j < n := hvals ⟨j, hj⟩
      have hcyc : iterParent_uh t (iterParent_uh t start j) (i - j) =
                  iterParent_uh t start j := by
        rw [← iterParent_add_uh]; convert heq using 2; omega
      have hsub : ∀ p, p ≤ i - j - 1 →
          ∃ dep, t.deps.find? (fun d => d.depIdx ==
            iterParent_uh t (iterParent_uh t start j) p) = some dep ∧
            dep.headIdx = iterParent_uh t (iterParent_uh t start j) (p + 1) := by
        intro p hp
        have hshift : ∀ q, iterParent_uh t (iterParent_uh t start j) q =
                      iterParent_uh t start (j + q) := by
          intro q; rw [← iterParent_add_uh]
        rw [hshift p, hshift (p + 1)]
        exact hchain (j + p) (by omega)
      have hcyc' : iterParent_uh t (iterParent_uh t start j) (i - j - 1 + 1) =
                   iterParent_uh t start j := by
        convert hcyc using 2; omega
      have hfalse := follow_false_of_cycle t (iterParent_uh t start j)
        (i - j - 1) (n + 1) (by omega) hsub hcyc'
      have htrue := isAcyclic_follow_uh t hacyc _ v_lt
      rw [hfalse] at htrue; exact absurd htrue (by decide)
  -- nodup list of n+1 values all < n: impossible by pigeonhole
  have hnodup := ofFn_nodup_of_injective hinj
  have hbound : ∀ x ∈ List.ofFn f, x < n := by
    intro x hx; rw [List.mem_ofFn] at hx; obtain ⟨i, rfl⟩ := hx; exact hvals i
  have := nodup_bound (List.ofFn f) n hnodup hbound
  rw [List.length_ofFn] at this
  omega

/-- In a well-formed tree (unique heads + acyclic), dominance is antisymmetric:
    if v dominates w and w dominates v, then v = w.

    **Proof**: By contradiction, assume v ≠ w. Extract iterParent chains
    from both `Dominates` derivations, combine into a cycle, and show
    `isAcyclic.follow` detects it (returning `false`), contradicting
    `isAcyclic = true`. -/
theorem dominates_antisymm (t : DepTree)
    (hwf : t.WF) (hacyc : isAcyclic t = true)
    (v w : Nat) (hvw : Dominates t.deps v w) (hwv : Dominates t.deps w v) :
    v = w := by
  by_contra hne
  -- Extract iterParent chains from both directions
  obtain ⟨k₁, hk₁, hiter₁, hchain₁⟩ := dominates_iterParent_uh t hwf hwv (Ne.symm hne)
  obtain ⟨k₂, hk₂, hiter₂, hchain₂⟩ := dominates_iterParent_uh t hwf hvw hne
  -- Combined cycle: iterParent(v, k₁+k₂) = v
  have hcycle : iterParent_uh t v (k₁ + k₂) = v := by
    rw [iterParent_add_uh, hiter₁, hiter₂]
  -- Full chain: valid parent edges at every step
  have hfull_chain : ∀ i, i < k₁ + k₂ →
      ∃ dep, t.deps.find? (fun d => d.depIdx == iterParent_uh t v i) = some dep ∧
             dep.headIdx = iterParent_uh t v (i + 1) := by
    intro i hi
    by_cases hi_lt : i < k₁
    · exact hchain₁ i hi_lt
    · have hshift : iterParent_uh t v i = iterParent_uh t w (i - k₁) := by
        conv_lhs => rw [show i = k₁ + (i - k₁) from by omega, iterParent_add_uh, hiter₁]
      have hshift' : iterParent_uh t v (i + 1) = iterParent_uh t w (i - k₁ + 1) := by
        conv_lhs => rw [show i + 1 = k₁ + (i - k₁ + 1) from by omega, iterParent_add_uh, hiter₁]
      obtain ⟨dep, h1, h2⟩ := hchain₂ (i - k₁) (by omega)
      exact ⟨dep, hshift ▸ h1, by rw [hshift']; exact h2⟩
  -- Detect the cycle via follow
  have hv_lt : v < t.words.length := dominates_depIdx_lt t hwf.depIdx_lt hwv (Ne.symm hne)
  have hbound := iterParent_chain_bound t hacyc hwf.depIdx_lt v (k₁ + k₂) hfull_chain hv_lt
  have hfalse := follow_false_of_cycle t v (k₁ + k₂ - 1) (t.words.length + 1)
    (by omega)
    (by intro i hi; exact hfull_chain i (by omega))
    (by show iterParent_uh t v (k₁ + k₂ - 1 + 1) = v
        rw [show k₁ + k₂ - 1 + 1 = k₁ + k₂ from by omega]; exact hcycle)
  have htrue := isAcyclic_follow_uh t hacyc v hv_lt
  rw [hfalse] at htrue
  exact absurd htrue (by decide)

/-- If v dominates c (with v ≠ c) and every edge into c has head = a,
    then v dominates a.

    **Key proof technique**: induction on the `Dominates` derivation.
    The last edge in the path v → ... → c terminates at c, so its head
    endpoint must be c's unique parent a. Dropping this last edge gives
    v dominates a.

    Used in `projective_implies_planar` to extract dominance cycles from
    crossing edges under unique heads. -/
theorem dominates_to_parent {deps : List Dependency} {v c a : Nat}
    (hdom : Dominates deps v c) (hne : v ≠ c)
    (hparent : ∀ d ∈ deps, d.depIdx = c → d.headIdx = a) :
    Dominates deps v a := by
  induction hdom with
  | refl => exact absurd rfl hne
  | step u w x hedge hdom_wc ih =>
    -- edge(u, w) and Dominates deps w x, need Dominates deps u a
    -- x is the target node (= c from original statement)
    by_cases hw_eq_x : w = x
    · -- w = x: edge(u, x), so u = a by unique parent
      obtain ⟨d, hd_mem, hd_head, hd_dep⟩ := hedge
      have hu_eq_a : u = a := by
        rw [← hd_head]; exact hparent d hd_mem (hw_eq_x ▸ hd_dep)
      exact hu_eq_a ▸ Dominates.refl u
    · -- w ≠ x: by IH, Dominates deps w a; then step gives Dominates deps u a
      exact Dominates.step u w a hedge (ih hw_eq_x hparent)

end DominanceUnderUniqueHeads

section AgreementChecking

/-- Check subject-verb number agreement. -/
def checkSubjVerbAgr (t : DepTree) : Bool :=
  t.deps.all λ d =>
    if d.depType == .nsubj then
      match t.words[d.depIdx]?, t.words[d.headIdx]? with
      | some subj, some verb =>
        match subj.features.number, verb.features.number with
        | some sn, some vn => sn == vn
        | _, _ => true
      | _, _ => true
    else true

/-- Check determiner-noun number agreement. -/
def checkDetNounAgr (t : DepTree) : Bool :=
  t.deps.all λ d =>
    if d.depType == .det then
      match t.words[d.depIdx]?, t.words[d.headIdx]? with
      | some det, some noun =>
        match det.features.number, noun.features.number with
        | some dn, some nn => dn == nn
        | _, _ => true
      | _, _ => true
    else true

end AgreementChecking

section SubcategorizationChecking

/-- Count dependents of a given type for a head. -/
def countDepsOfType (t : DepTree) (headIdx : Nat) (dtype : UD.DepRel) : Nat :=
  t.deps.filter (λ d => d.headIdx == headIdx && d.depType == dtype) |>.length

/-- Check if verb has correct argument structure. -/
def checkVerbSubcat (t : DepTree) : Bool :=
  List.range t.words.length |>.all λ i =>
    match t.words[i]? with
    | some w =>
      if w.cat == UD.UPOS.VERB then
        let subjCount := countDepsOfType t i .nsubj
        let objCount := countDepsOfType t i .obj
        let iobjCount := countDepsOfType t i .iobj
        match w.features.valence with
        | some .intransitive => subjCount >= 1 && objCount == 0
        | some .transitive => subjCount >= 1 && objCount == 1
        | some .ditransitive => subjCount >= 1 && objCount == 1 && iobjCount == 1
        | _ => true
      else true
    | none => true

end SubcategorizationChecking

/-- A dependency tree is well-formed if it satisfies all constraints. -/
def isWellFormed (t : DepTree) : Bool :=
  hasUniqueHeads t &&
  isAcyclic t &&
  isProjective t &&
  checkSubjVerbAgr t &&
  checkDetNounAgr t &&
  checkVerbSubcat t

section GrammarInstance

/-- Dependency grammar configuration. -/
structure DependencyGrammar where
  checkProjectivity : Bool := true
  checkAgreement : Bool := true
  checkSubcat : Bool := true

instance : Grammar DependencyGrammar where
  Derivation := DepTree
  realizes t ws _ := t.words = ws ∧ isWellFormed t = true
  derives _ ws _ := ∃ t : DepTree, t.words = ws ∧ isWellFormed t = true

def defaultGrammar : DependencyGrammar := {}

end GrammarInstance

section TreeConstructionHelpers

/-- Create a simple SV tree: subject -> verb. -/
def mkSVTree (subj verb : Word) : DepTree :=
  { words := [subj, verb]
    deps := [⟨1, 0, .nsubj⟩]
    rootIdx := 1 }

/-- Create a simple SVO tree: subject -> verb <- object. -/
def mkSVOTree (subj verb obj : Word) : DepTree :=
  { words := [subj, verb, obj]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1 }

/-- Create Det-N-V tree: det -> noun -> verb. -/
def mkDetNVTree (det noun verb : Word) : DepTree :=
  { words := [det, noun, verb]
    deps := [⟨1, 0, .det⟩, ⟨2, 1, .nsubj⟩]
    rootIdx := 2 }

/-- Create a ditransitive tree: subj -> verb <- iobj <- obj. -/
def mkDitransTree (subj verb iobj obj : Word) : DepTree :=
  { words := [subj, verb, iobj, obj]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .iobj⟩, ⟨1, 3, .obj⟩]
    rootIdx := 1 }

end TreeConstructionHelpers

end DepGrammar
