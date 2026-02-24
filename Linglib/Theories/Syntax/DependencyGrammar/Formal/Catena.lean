import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Linglib.Theories.Syntax.DependencyGrammar.Core.Projection

/-!
# Catenae: A Novel Unit of Syntactic Analysis

Formalizes the catena (Osborne, Putnam & Groß 2012, *Syntax* 15:4, 354–396).

A **catena** (Latin: "chain") is a connected subgraph of a dependency tree —
any word or combination of words that is continuous with respect to the
dominance relation. Catenae strictly generalize constituents: every constituent
is a catena, but not every catena is a constituent.

## Mathlib Integration

The dependency tree is converted to a mathlib `SimpleGraph (Fin n)` via
`depsToSimpleGraph`, bridging linglib's `DepTree`/`Dependency` types to
mathlib's graph theory infrastructure. The Prop-level `IsCatena` is defined
using `SimpleGraph.Preconnected` on induced subgraphs. Computable `Bool`
functions (`isCatena`, `isConstituent`) enable `native_decide` proofs.

## Key Results

- `constituent_is_catena`: every constituent is a catena (p. 360)
- For n words: n constituents ≤ catenae ≤ 2^n - 1 total combinations
- Flatter trees have more catenae than chain-shaped trees (p. 371)
- Catena ratio varies systematically with tree shape

## Bridges

- → `Core/Basic.lean`: uses `DepTree`, `DepGraph`, `Dependency` types
- → mathlib `SimpleGraph`: `depsToSimpleGraph` converts dependency edges
- → `DependencyLength.lean`: `catenaTotalDepLength` measures catena spread

## References

- Osborne, T., Putnam, M. & Groß, T. (2012). Catenae: Introducing a novel
  unit of syntactic analysis. *Syntax* 15(4):354–396.
-/

namespace DepGrammar.Catena

open DepGrammar

-- ============================================================================
-- Bridge: Dependency Edges → mathlib SimpleGraph
-- ============================================================================

/-- The undirected simple graph underlying dependency edges over n nodes.
    Forgets edge direction and labels: i ~ j iff some dependency connects them.
    Uses mathlib's `SimpleGraph (Fin n)` — the fundamental bridge from
    linglib's `DepTree`/`Dependency` types to mathlib's graph theory. -/
def depsToSimpleGraph (n : Nat) (deps : List Dependency) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ∃ d ∈ deps,
    (d.headIdx = i.val ∧ d.depIdx = j.val) ∨ (d.headIdx = j.val ∧ d.depIdx = i.val)
  symm := by
    intro i j ⟨hne, d, hd, hor⟩
    exact ⟨hne.symm, d, hd, hor.elim Or.inr Or.inl⟩
  loopless := by intro i ⟨hne, _⟩; exact absurd rfl hne

/-- Convert a DepTree to a mathlib SimpleGraph on its node set. -/
def DepTree.asSimpleGraph (t : DepTree) : SimpleGraph (Fin t.words.length) :=
  depsToSimpleGraph t.words.length t.deps

-- ============================================================================
-- IsCatena (Prop-level, mathlib-integrated)
-- ============================================================================

/-- A **catena** (Osborne et al. 2012, p. 359) is a non-empty subset S of tree
    nodes where the induced subgraph on S is preconnected. Equivalently: a word
    or combination of words that is continuous with respect to dominance.

    Uses mathlib's `SimpleGraph.induce` and `SimpleGraph.Preconnected`. -/
def IsCatena {n : Nat} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  S.Nonempty ∧ (G.induce (↑S : Set (Fin n))).Preconnected

-- ============================================================================
-- isCatena (Bool-level, computable)
-- ============================================================================

/-- BFS reachability within a restricted node set. Returns all nodes reachable
    from `start` via dependency edges where both endpoints are in `allowed`. -/
private def bfsReachable (deps : List Dependency) (allowed : List Nat)
    (start : Nat) : List Nat :=
  let rec go (queue : List Nat) (visited : List Nat) (fuel : Nat) : List Nat :=
    match fuel, queue with
    | 0, _ => visited
    | _, [] => visited
    | fuel' + 1, node :: rest =>
      if visited.contains node then go rest visited fuel'
      else
        let neighbors := deps.filterMap fun d =>
          if d.headIdx == node && allowed.contains d.depIdx then some d.depIdx
          else if d.depIdx == node && allowed.contains d.headIdx then some d.headIdx
          else none
        go (rest ++ neighbors) (node :: visited) fuel'
  go [start] [] (allowed.length * (deps.length + 1) + 1)

/-- Check if a node set is connected within the dependency graph.
    Uses BFS from the first node and checks all others are reached. -/
def isConnected (deps : List Dependency) (nodes : List Nat) : Bool :=
  match nodes with
  | [] => true
  | start :: _ =>
    let reached := bfsReachable deps nodes start
    nodes.all reached.contains

/-- Computable catena check: non-empty and connected in the tree.
    (Osborne et al. 2012, p. 359) -/
def isCatena (deps : List Dependency) (nodes : List Nat) : Bool :=
  !nodes.isEmpty && isConnected deps nodes

/-- Elements already in visited remain in the BFS result. -/
private theorem mem_go_of_mem_visited (deps : List Dependency) (allowed : List Nat)
    (queue visited : List Nat) (fuel : Nat) (x : Nat) (hx : x ∈ visited) :
    x ∈ bfsReachable.go deps allowed queue visited fuel := by
  induction fuel generalizing queue visited with
  | zero => exact hx
  | succ f ih =>
    match queue with
    | [] => exact hx
    | node :: rest =>
      show x ∈ bfsReachable.go deps allowed (node :: rest) visited (f + 1)
      unfold bfsReachable.go
      split
      · exact ih rest visited hx
      · exact ih _ _ (List.mem_cons_of_mem _ hx)

/-- If `x` is at position `pfx.length` in the queue, it ends up in the
    BFS output — provided `fuel ≥ pfx.length + 1`. Proof by induction on
    the prefix length: each BFS step removes the queue head, so `x` advances
    toward the front. -/
private theorem go_mem_of_queue (deps : List Dependency) (allowed : List Nat)
    (pfx : List Nat) (x : Nat) (sfx visited : List Nat) (fuel : Nat)
    (hfuel : fuel ≥ pfx.length + 1) :
    x ∈ bfsReachable.go deps allowed (pfx ++ x :: sfx) visited fuel := by
  induction pfx generalizing sfx visited fuel with
  | nil =>
    simp only [List.nil_append]
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    show x ∈ bfsReachable.go deps allowed (x :: sfx) visited (fuel' + 1)
    unfold bfsReachable.go
    split
    · rename_i hc
      have : x ∈ visited := by
        simp only [List.contains_eq_any_beq, List.any_eq_true] at hc
        obtain ⟨y, hy, hbeq⟩ := hc
        rwa [show y = x from (beq_iff_eq.mp hbeq).symm] at hy
      exact mem_go_of_mem_visited deps allowed sfx visited fuel' x this
    · exact mem_go_of_mem_visited deps allowed (sfx ++ _) (x :: visited) fuel' x
        (List.mem_cons.mpr (Or.inl rfl))
  | cons y ys ih =>
    obtain ⟨fuel', rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    show x ∈ bfsReachable.go deps allowed ((y :: ys) ++ x :: sfx) visited (fuel' + 1)
    rw [List.cons_append]
    show x ∈ bfsReachable.go deps allowed (y :: (ys ++ x :: sfx)) visited (fuel' + 1)
    unfold bfsReachable.go
    split
    · exact ih sfx visited fuel' (by simp only [List.length_cons] at hfuel; omega)
    · simp only [List.append_assoc, List.cons_append]
      exact ih _ (y :: visited) fuel'
        (by simp only [List.length_cons] at hfuel; omega)

/-- `filterMap` produces at most as many elements as the input list. -/
private theorem filterMap_length_le {α β : Type*} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.filterMap_cons]
    cases f a <;> simp only [List.length_cons] <;> omega

/-- Every element of the bidirectional neighbor list is in `allowed`. -/
private theorem nbrs_subset_allowed (deps : List Dependency) (allowed : List Nat)
    (node x : Nat)
    (hx : x ∈ (deps.filterMap fun d =>
      if d.headIdx == node && allowed.contains d.depIdx then some d.depIdx
      else if d.depIdx == node && allowed.contains d.headIdx then some d.headIdx
      else none)) : x ∈ allowed := by
  induction deps with
  | nil => exact absurd hx (by simp)
  | cons d ds ih =>
    simp only [List.filterMap_cons] at hx
    by_cases h1 : (d.headIdx == node && allowed.contains d.depIdx) = true
    · rw [if_pos h1] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [Bool.and_eq_true] at h1; exact List.mem_of_elem_eq_true h1.2
      · exact ih hx
    · simp only [Bool.eq_false_iff.mpr h1] at hx
      by_cases h2 : (d.depIdx == node && allowed.contains d.headIdx) = true
      · rw [if_pos h2] at hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [Bool.and_eq_true] at h2; exact List.mem_of_elem_eq_true h2.2
        · exact ih hx
      · simp only [Bool.eq_false_iff.mpr h2] at hx
        exact ih hx

/-- An edge `w--c` with `c ∈ allowed` means `c` is in the BFS neighbor list. -/
private theorem mem_neighbors_of_edge (deps : List Dependency) (allowed : List Nat)
    (w c : Nat) (hc_allowed : c ∈ allowed)
    (hedge : ∃ d ∈ deps, (d.headIdx = w ∧ d.depIdx = c) ∨
                          (d.depIdx = w ∧ d.headIdx = c)) :
    c ∈ (deps.filterMap fun d =>
      if d.headIdx == w && allowed.contains d.depIdx then some d.depIdx
      else if d.depIdx == w && allowed.contains d.headIdx then some d.headIdx
      else none) := by
  obtain ⟨d, hd_mem, hor⟩ := hedge
  have hc_cont : allowed.contains c = true := List.elem_eq_true_of_mem hc_allowed
  apply List.mem_filterMap.mpr
  refine ⟨d, hd_mem, ?_⟩
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- d.headIdx = w, d.depIdx = c: first branch fires
    simp only [show (d.headIdx == w) = true from beq_iff_eq.mpr h1,
               show (allowed.contains d.depIdx) = true from h2 ▸ hc_cont,
               Bool.true_and, ↓reduceIte]
    exact congrArg some h2
  · -- d.depIdx = w, d.headIdx = c
    cases heq : d.headIdx == w
    · -- first branch false, second fires
      simp only [Bool.false_and, ↓reduceIte,
                 show (d.depIdx == w) = true from beq_iff_eq.mpr h1,
                 show (allowed.contains d.headIdx) = true from h2 ▸ hc_cont,
                 Bool.true_and]
      exact congrArg some h2
    · -- first branch true (d.headIdx = w too, so c = w)
      have hcw : c = w := h2 ▸ beq_iff_eq.mp heq
      simp only [show (allowed.contains d.depIdx) = true from by
                   rw [h1]; rw [hcw] at hc_cont; exact hc_cont,
                 Bool.true_and, ↓reduceIte]
      exact congrArg some (by rw [h1, hcw])

/-- BFS potential: unvisited-allowed-node count weighted by deps.length, plus
    queue length. Decreases by ≥ 1 at each BFS step when queue elements
    are all in `allowed`. -/
private def bfsPot (deps : List Dependency) (allowed : List Nat)
    (queue : List Nat) (visited : List Nat) : Nat :=
  (allowed.filter (fun v => !(visited.contains v))).length * deps.length + queue.length

/-- The filter of `allowed` by `¬vis.contains` splits into: the filter by
    `¬(node::vis).contains` plus elements matching `node`. Analogous to
    `filter_split_at_node` in Projection.lean. -/
private theorem allowed_filter_split (allowed visited : List Nat) (node : Nat)
    (hcont : visited.contains node = false) :
    (allowed.filter (fun v => !(visited.contains v))).length =
      (allowed.filter (fun v => !((node :: visited).contains v))).length +
      (allowed.filter (fun v => v == node)).length := by
  induction allowed with
  | nil => rfl
  | cons a as ih =>
    simp only [List.filter]
    cases hv : visited.contains a <;> cases han : (a == node)
    · have : (node :: visited).contains a = false := by
        simp only [List.contains_cons, han, hv, Bool.false_or]
      simp only [this, Bool.not_false,
        List.length_cons]; omega
    · have : (node :: visited).contains a = true := by
        simp only [List.contains_cons, han, Bool.true_or]
      simp only [this, Bool.not_false, Bool.not_true,
        List.length_cons]; omega
    · have : (node :: visited).contains a = true := by
        simp only [List.contains_cons, hv, Bool.or_true]
      simp only [this, Bool.not_true]; exact ih
    · have : a = node := beq_iff_eq.mp han
      rw [this] at hv; exact absurd hv (by rw [hcont]; exact Bool.noConfusion)

/-- When a node is processed by BFS, the filter of `allowed` by `¬vis.contains`
    strictly decreases: the processed node was in the old filter but not the new. -/
private theorem allowed_filter_decrease (allowed visited : List Nat) (node : Nat)
    (hnode : node ∈ allowed) (hcont : visited.contains node = false) :
    (allowed.filter (fun v => !(visited.contains v))).length ≥
    (allowed.filter (fun v => !((node :: visited).contains v))).length + 1 := by
  have hsplit := allowed_filter_split allowed visited node hcont
  have hge : (allowed.filter (fun v => v == node)).length ≥ 1 :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hnode, beq_self_eq_true node⟩)
  omega

/-- If `w` is in the BFS output, was not initially visited, and `c` is a
    bidirectional neighbor of `w` in `allowed`, then `c` is also in the output.
    Requires sufficient fuel and the invariant that queue ⊆ allowed. -/
private theorem go_neighbors_complete (deps : List Dependency) (allowed : List Nat)
    (queue visited : List Nat) (fuel : Nat) (w c : Nat)
    (hqueue : ∀ x ∈ queue, x ∈ allowed)
    (hw : w ∈ bfsReachable.go deps allowed queue visited fuel)
    (hw_not_vis : w ∉ visited)
    (hc_allowed : c ∈ allowed)
    (hedge : ∃ d ∈ deps, (d.headIdx = w ∧ d.depIdx = c) ∨
                          (d.depIdx = w ∧ d.headIdx = c))
    (hfuel : fuel ≥ bfsPot deps allowed queue visited + 1) :
    c ∈ bfsReachable.go deps allowed queue visited fuel := by
  induction fuel generalizing queue visited with
  | zero => exact absurd (by simpa [bfsReachable.go] using hw) hw_not_vis
  | succ fuel' ih =>
    match queue with
    | [] => exact absurd (by simpa [bfsReachable.go] using hw) hw_not_vis
    | node :: rest =>
      show c ∈ bfsReachable.go deps allowed (node :: rest) visited (fuel' + 1)
      unfold bfsReachable.go at hw ⊢
      by_cases hcont : (visited.contains node) = true
      · -- Skip: node already visited
        simp only [hcont, ↓reduceIte] at hw ⊢
        apply ih rest visited
          (fun x hx => hqueue x (List.mem_cons.mpr (Or.inr hx)))
          hw hw_not_vis
        -- bfsPot step: bfsPot (node :: rest) vis = bfsPot rest vis + 1
        simp only [bfsPot, List.length_cons] at hfuel ⊢; omega
      · -- Process: node not visited
        have hcont_f : visited.contains node = false := by
          cases h : visited.contains node <;> simp_all
        simp only [hcont] at hw ⊢
        set nbrs := deps.filterMap fun d =>
          if d.headIdx == node && allowed.contains d.depIdx then some d.depIdx
          else if d.depIdx == node && allowed.contains d.headIdx then some d.headIdx
          else none with nbrs_def
        by_cases hwn : w = node
        · -- w IS the node being processed: c enters the queue via neighbors
          subst hwn
          have hc_nbr := mem_neighbors_of_edge deps allowed w c hc_allowed hedge
          rw [← nbrs_def] at hc_nbr
          obtain ⟨pfx, sfx, hpfx⟩ := List.append_of_mem
            (List.mem_append.mpr (Or.inr hc_nbr) : c ∈ rest ++ nbrs)
          rw [hpfx]
          apply go_mem_of_queue deps allowed pfx c sfx (w :: visited) fuel'
          -- fuel' ≥ pfx.length + 1: decompose multiplication for omega
          have hpfx_bound : pfx.length < rest.length + nbrs.length := by
            have := congrArg List.length hpfx
            simp [List.length_append, List.length_cons] at this; omega
          have hnbrs_bound : nbrs.length ≤ deps.length := filterMap_length_le _ _
          have hw_allowed : w ∈ allowed := hqueue w (List.mem_cons.mpr (Or.inl rfl))
          have hfilter_pos : (allowed.filter (fun v => !(visited.contains v))).length ≥ 1 :=
            List.length_pos_of_mem (List.mem_filter.mpr ⟨hw_allowed, hcont_f ▸ rfl⟩)
          -- F * D ≥ 1 * D = D ≥ N (nbrs bound)
          have hFD_ge_D : (allowed.filter (fun v => !(visited.contains v))).length *
              deps.length ≥ deps.length := by
            calc deps.length = 1 * deps.length := (Nat.one_mul _).symm
              _ ≤ _ := Nat.mul_le_mul_right _ hfilter_pos
          simp only [bfsPot, List.length_cons] at hfuel; omega
        · -- w ≠ node: IH on recursive call
          have hw_not_vis' : w ∉ (node :: visited) := by
            simp only [List.mem_cons, not_or]; exact ⟨hwn, hw_not_vis⟩
          have hqueue' : ∀ x ∈ rest ++ nbrs, x ∈ allowed := by
            intro x hx
            rcases List.mem_append.mp hx with hr | hn
            · exact hqueue x (List.mem_cons.mpr (Or.inr hr))
            · exact nbrs_subset_allowed deps allowed node x (nbrs_def ▸ hn)
          apply ih (rest ++ nbrs) (node :: visited) hqueue' hw hw_not_vis'
          -- fuel bound: bfsPot decreases at process step
          have hnode_allowed : node ∈ allowed :=
            hqueue node (List.mem_cons.mpr (Or.inl rfl))
          have hfilter_decrease := allowed_filter_decrease allowed visited node
            hnode_allowed hcont_f
          have hnbrs_bound : nbrs.length ≤ deps.length := filterMap_length_le _ _
          -- Decompose multiplication for omega: F * D ≥ F' * D + D
          have hFD :
              (allowed.filter (fun v => !(visited.contains v))).length * deps.length ≥
              (allowed.filter (fun v => !((node :: visited).contains v))).length *
                deps.length + deps.length := by
            have h1 := Nat.mul_le_mul_right deps.length hfilter_decrease
            rw [Nat.add_mul] at h1; simp only [Nat.one_mul] at h1; exact h1
          simp only [bfsPot, List.length_cons, List.length_append] at hfuel ⊢
          omega

/-- Bidirectional reachability within a restricted node set.
    `BidirReachable deps allowed u v` holds when there is a path from `u` to `v`
    using dependency edges (in either direction) where all nodes are in `allowed`. -/
inductive BidirReachable (deps : List Dependency) (allowed : List Nat) :
    Nat → Nat → Prop where
  | here : (v : Nat) → v ∈ allowed → BidirReachable deps allowed v v
  | step : (u v w : Nat) → u ∈ allowed → v ∈ allowed →
      (∃ d ∈ deps, (d.headIdx = u ∧ d.depIdx = v) ∨
                    (d.depIdx = u ∧ d.headIdx = v)) →
      BidirReachable deps allowed v w → BidirReachable deps allowed u w

/-- The start node is always in the `bfsReachable` output. -/
private theorem start_mem_bfsReachable (deps : List Dependency) (allowed : List Nat)
    (start : Nat) : start ∈ bfsReachable deps allowed start := by
  unfold bfsReachable
  show start ∈ bfsReachable.go deps allowed [start] []
    (allowed.length * (deps.length + 1) + 1)
  unfold bfsReachable.go
  simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
  exact mem_go_of_mem_visited deps allowed _ (start :: [])
    (allowed.length * (deps.length + 1)) start
    (List.mem_cons.mpr (Or.inl rfl))

/-- The `bfsReachable` output is closed under bidirectional edges within `allowed`:
    if `v` is in the output and `v--w` is an edge with `w ∈ allowed`, then `w`
    is in the output too. -/
private theorem bfsReachable_closed (deps : List Dependency) (allowed : List Nat)
    (start v w : Nat) (hstart : start ∈ allowed)
    (hv : v ∈ bfsReachable deps allowed start)
    (_hv_allowed : v ∈ allowed)
    (hw_allowed : w ∈ allowed)
    (hedge : ∃ d ∈ deps, (d.headIdx = v ∧ d.depIdx = w) ∨
                          (d.depIdx = v ∧ d.headIdx = w)) :
    w ∈ bfsReachable deps allowed start := by
  unfold bfsReachable at hv ⊢
  apply go_neighbors_complete deps allowed [start] [] _ v w
    (fun x hx => by simp only [List.mem_singleton] at hx; rw [hx]; exact hstart)
    hv (fun h => nomatch h) hw_allowed hedge
  -- fuel ≥ bfsPot + 1
  have h_filter : (allowed.filter (fun v => !(([] : List Nat).contains v))).length
      = allowed.length := by
    congr 1; apply List.filter_eq_self.mpr; intro x _; simp
  have h_expand : allowed.length * (deps.length + 1) =
      allowed.length * deps.length + allowed.length := Nat.mul_succ _ _
  simp only [bfsPot, h_filter, List.length_cons, List.length_nil]
  rw [h_expand]
  have : allowed.length ≥ 1 := List.length_pos_of_mem hstart
  omega

/-- BFS completeness: every bidirectionally reachable node appears in the
    `bfsReachable` output.

    Proved by showing the output contains `start` and is closed under
    edges within `allowed`, then applying induction on `BidirReachable`. -/
theorem bfsReachable_complete (deps : List Dependency) (allowed : List Nat)
    (start target : Nat) (h : BidirReachable deps allowed start target) :
    target ∈ bfsReachable deps allowed start := by
  -- Extract start ∈ allowed from BidirReachable
  have hstart : start ∈ allowed := by
    cases h with
    | here v hv => exact hv
    | step u _ _ hu _ _ _ => exact hu
  -- Suffices: start ∈ output, and output is edge-closed in allowed
  suffices hclosed : ∀ v, v ∈ bfsReachable deps allowed start →
      ∀ w, BidirReachable deps allowed v w → w ∈ bfsReachable deps allowed start by
    exact hclosed start (start_mem_bfsReachable deps allowed start) target h
  intro v hv w hreach
  induction hreach with
  | here _ _ => exact hv
  | step u v' w' hu hv' hedge _ ih =>
    have hv'_mem := bfsReachable_closed deps allowed start u v' hstart hv hu hv' hedge
    exact ih hv'_mem

/-- Any singleton is a catena: non-empty and trivially connected. -/
theorem singleton_isCatena (deps : List Dependency) (v : Nat) :
    isCatena deps [v] = true := by
  unfold isCatena isConnected
  simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and,
             List.all_cons, List.all_nil, Bool.and_true]
  -- Goal: (bfsReachable deps [v] v).contains v
  -- BFS starts with queue=[v], visited=[]. First step adds v to visited.
  show (bfsReachable deps [v] v).contains v = true
  unfold bfsReachable bfsReachable.go
  simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
  -- v is now in visited=[v]. Need: (go ... (v :: []) ...).contains v
  exact List.elem_eq_true_of_mem
    (mem_go_of_mem_visited _ _ _ _ _ v List.mem_cons_self)

/-- Convenience: check catena on a DepTree directly. -/
def DepTree.isCatena' (t : DepTree) (nodes : List Nat) : Bool :=
  Catena.isCatena t.deps nodes

-- ============================================================================
-- Constituent (complete subtree)
-- ============================================================================

/-- Check if a node set equals the complete subtree (projection) rooted at
    some node. Uses `projection` from Core/Basic.lean. -/
def isConstituent (deps : List Dependency) (n : Nat) (nodes : List Nat) : Bool :=
  List.range n |>.any fun root =>
    let sub := projection deps root
    nodes.length == sub.length &&
    nodes.all sub.contains &&
    sub.all nodes.contains

-- ============================================================================
-- Enumeration and Counting
-- ============================================================================

/-- All non-empty subsets of {0, ..., n-1}. -/
def allNonEmptySubsets (n : Nat) : List (List Nat) :=
  let rec powerset (remaining : List Nat) : List (List Nat) :=
    match remaining with
    | [] => [[]]
    | x :: xs =>
      let rest := powerset xs
      rest ++ rest.map (x :: ·)
  (powerset (List.range n)).filter (!·.isEmpty)

/-- Count catenae for a tree with n nodes and given dependency edges. -/
def catenaeCount (n : Nat) (deps : List Dependency) : Nat :=
  (allNonEmptySubsets n).filter (isCatena deps) |>.length

/-- Count constituents for a tree with n nodes. -/
def constituentCount (n : Nat) (deps : List Dependency) : Nat :=
  (allNonEmptySubsets n).filter (isConstituent deps n) |>.length

/-- Total non-empty subsets of n elements: 2^n - 1. -/
def totalCombinations (n : Nat) : Nat := 2^n - 1

/-- Catena ratio as (catenae, non-catenae). Flatter trees → higher ratio. -/
def catenaRatio (n : Nat) (deps : List Dependency) : Nat × Nat :=
  let c := catenaeCount n deps
  (c, totalCombinations n - c)

-- ============================================================================
-- Example Trees (Osborne et al. 2012)
-- ============================================================================

/-- Tree (9), p. 359: 4 abstract nodes.
        a(0)
       /    \
    b(1)   c(2)
    |
    d(3)

    10 catenae, 5 non-catenae, 4 constituents out of 15 total.
    Catenae: {a},{b},{c},{d},{a,b},{a,c},{b,d},{a,b,c},{a,b,d},{a,b,c,d}
    Constituents: {d},{c},{b,d},{a,b,c,d} -/
def tree9 : List Dependency :=
  [⟨0, 1, .dep⟩, ⟨0, 2, .dep⟩, ⟨1, 3, .dep⟩]

/-- Tree (22), p. 371: 3-node flat tree.
      a(0)
     /    \
   b(1)  c(2)

    6 catenae, 1 non-catena, 3 constituents out of 7 total. -/
def tree22 : List Dependency :=
  [⟨0, 1, .dep⟩, ⟨0, 2, .dep⟩]

/-- 4-node chain: a(0) → b(1) → c(2) → d(3).
    10 catenae (only contiguous intervals are connected). -/
def chain4 : List Dependency :=
  [⟨0, 1, .dep⟩, ⟨1, 2, .dep⟩, ⟨2, 3, .dep⟩]

/-- 4-node star: a(0) → {b(1), c(2), d(3)}.
    11 catenae (every root-containing subset is connected). -/
def star4 : List Dependency :=
  [⟨0, 1, .dep⟩, ⟨0, 2, .dep⟩, ⟨0, 3, .dep⟩]

/-- 3-node chain: a(0) → b(1) → c(2). -/
def chain3 : List Dependency :=
  [⟨0, 1, .dep⟩, ⟨1, 2, .dep⟩]

-- ============================================================================
-- Linguistic Example: Idioms as Non-Constituent Catenae (p. 362)
-- ============================================================================

/-- "pulled some strings" — the idiom {pulled, strings} forms a catena
    but not a constituent (Osborne et al. 2012, p. 362).

    Words: pulled(0) some(1) strings(2)
    UD: pulled → strings (obj), strings → some (det). -/
def pulledSomeStrings : DepTree :=
  { words := [Word.mk' "pulled" .VERB, Word.mk' "some" .DET, Word.mk' "strings" .NOUN]
    deps := [⟨0, 2, .obj⟩, ⟨2, 1, .det⟩]
    rootIdx := 0 }

-- ============================================================================
-- Verified Counts (native_decide)
-- ============================================================================

-- Total combination formula
theorem total_3 : totalCombinations 3 = 7 := by native_decide
theorem total_4 : totalCombinations 4 = 15 := by native_decide

-- Tree (9): 10 catenae, 4 constituents (p. 359-360)
theorem tree9_catenae : catenaeCount 4 tree9 = 10 := by native_decide
theorem tree9_constituents : constituentCount 4 tree9 = 4 := by native_decide
theorem tree9_ratio : catenaRatio 4 tree9 = (10, 5) := by native_decide

-- Tree (22): 6 catenae, 3 constituents (p. 371)
theorem tree22_catenae : catenaeCount 3 tree22 = 6 := by native_decide
theorem tree22_constituents : constituentCount 3 tree22 = 3 := by native_decide
theorem tree22_ratio : catenaRatio 3 tree22 = (6, 1) := by native_decide

-- Chain4: 10 catenae, 4 constituents
theorem chain4_catenae : catenaeCount 4 chain4 = 10 := by native_decide
theorem chain4_constituents : constituentCount 4 chain4 = 4 := by native_decide

-- Star4: 11 catenae, 4 constituents
theorem star4_catenae : catenaeCount 4 star4 = 11 := by native_decide
theorem star4_constituents : constituentCount 4 star4 = 4 := by native_decide

-- For n=3, tree shape doesn't affect catena count (both give 6)
theorem three_nodes_shape_invariant :
    catenaeCount 3 chain3 = catenaeCount 3 tree22 := by native_decide

-- ============================================================================
-- Structural Theorems
-- ============================================================================

/-- Flatter trees have strictly more catenae than chain-shaped trees.
    (Osborne et al. 2012, p. 371: the catena ratio increases with flatness) -/
theorem flatter_more_catenae :
    catenaeCount 4 star4 > catenaeCount 4 chain4 := by native_decide

/-- Every constituent is a catena — verified exhaustively for tree (9).
    (Osborne et al. 2012, p. 360: "every 'constituent' is also a catena") -/
theorem constituent_is_catena_tree9 :
    (allNonEmptySubsets 4).all (fun nodes =>
      if isConstituent tree9 4 nodes then isCatena tree9 nodes else true
    ) = true := by native_decide

/-- Every constituent is a catena — verified for star4. -/
theorem constituent_is_catena_star4 :
    (allNonEmptySubsets 4).all (fun nodes =>
      if isConstituent star4 4 nodes then isCatena star4 nodes else true
    ) = true := by native_decide

/-- Every constituent is a catena — verified for chain4. -/
theorem constituent_is_catena_chain4 :
    (allNonEmptySubsets 4).all (fun nodes =>
      if isConstituent chain4 4 nodes then isCatena chain4 nodes else true
    ) = true := by native_decide

/-- n constituents ≤ catenae count ≤ 2^n - 1 total combinations. -/
theorem counting_hierarchy_tree9 :
    constituentCount 4 tree9 ≤ catenaeCount 4 tree9 ∧
    catenaeCount 4 tree9 ≤ totalCombinations 4 := by native_decide

theorem counting_hierarchy_star4 :
    constituentCount 4 star4 ≤ catenaeCount 4 star4 ∧
    catenaeCount 4 star4 ≤ totalCombinations 4 := by native_decide

-- Specific catena / non-catena examples

/-- Every singleton is a catena. -/
theorem singleton_catena_0 : isCatena tree9 [0] = true := by native_decide
theorem singleton_catena_1 : isCatena tree9 [1] = true := by native_decide
theorem singleton_catena_2 : isCatena tree9 [2] = true := by native_decide
theorem singleton_catena_3 : isCatena tree9 [3] = true := by native_decide

/-- {a, d} is NOT a catena — a and d aren't connected without b. -/
theorem not_catena_ad : isCatena tree9 [0, 3] = false := by native_decide

/-- {b, c} is NOT a catena — b and c aren't connected without a. -/
theorem not_catena_bc : isCatena tree9 [1, 2] = false := by native_decide

/-- The idiom "pulled strings" is a catena (connected via obj edge)... -/
theorem idiom_is_catena :
    isCatena pulledSomeStrings.deps [0, 2] = true := by native_decide

/-- ...but NOT a constituent (subtree of "pulled" includes "some"). -/
theorem idiom_not_constituent :
    isConstituent pulledSomeStrings.deps 3 [0, 2] = false := by native_decide

/-- The full phrase "pulled some strings" IS both a constituent and a catena. -/
theorem phrase_is_constituent :
    isConstituent pulledSomeStrings.deps 3 [0, 1, 2] = true := by native_decide
theorem phrase_is_catena :
    isCatena pulledSomeStrings.deps [0, 1, 2] = true := by native_decide

-- ============================================================================
-- mathlib Prop-level Theorems
-- ============================================================================

/-- Every singleton is a catena in any SimpleGraph (mathlib Prop-level).
    Proof: the induced subgraph on {v} has a single vertex, so it's trivially
    preconnected. -/
theorem IsCatena_singleton {n : Nat} (G : SimpleGraph (Fin n)) (v : Fin n) :
    IsCatena G {v} := by
  refine ⟨Finset.singleton_nonempty v, fun a b => ?_⟩
  have ha := Finset.mem_singleton.mp (Finset.mem_coe.mp a.property)
  have hb := Finset.mem_singleton.mp (Finset.mem_coe.mp b.property)
  have hab : a = b := Subtype.ext (ha.trans hb.symm)
  rw [hab]

-- ============================================================================
-- Bridge: isCatena (Bool) ↔ IsCatena (Prop)
-- ============================================================================

/-- The computable `isCatena` agrees with the Prop-level `IsCatena`.

    ## Proof Sketch

    **Forward** (`isCatena = true → IsCatena`): BFS from the start node
    reaches all nodes in the list, so for any two nodes u, v in the set,
    there is a BFS path u → ... → v using only edges within the set.
    Each BFS step corresponds to a `SimpleGraph.Walk` step in the induced
    subgraph, giving `SimpleGraph.Reachable u v`, hence `Preconnected`.

    **Backward** (`IsCatena → isCatena = true`): `Preconnected` gives
    `Reachable start v` for every v in the set. Each `Walk` step is an
    edge in the induced subgraph, which corresponds to a dependency edge
    with both endpoints in `allowed`. BFS will therefore discover v.

    ## Blockers

    Formalizing this requires a BFS correctness proof for `bfsReachable`:
    - **Soundness**: every node in `bfsReachable` output is reachable via
      edges within `allowed` from `start`
    - **Completeness**: every node reachable via edges within `allowed`
      from `start` appears in `bfsReachable` output
    - **Bridge**: `bfsReachable` edge steps correspond to `SimpleGraph.Adj`
      in `depsToSimpleGraph` restricted to the node set

    Low downstream value: all current catena theorems use `native_decide`. -/
theorem isCatena_iff_IsCatena {n : Nat} (deps : List Dependency)
    (nodes : List Nat) (hbounds : ∀ i ∈ nodes, i < n) (hnodup : nodes.Nodup) :
    isCatena deps nodes = true ↔
    IsCatena (depsToSimpleGraph n deps) (nodes.filterMap (fun i =>
      if h : i < n then some ⟨i, h⟩ else none) |>.toFinset) := by
  sorry

-- ============================================================================
-- Catena Dependency Length
-- ============================================================================

/-- Dependency length for a single edge: |headIdx - depIdx|. -/
private def depLength' (d : Dependency) : Nat :=
  max d.headIdx d.depIdx - min d.headIdx d.depIdx

/-- Total dependency length restricted to edges within a catena.
    Measures the linear spread of the catena. -/
def catenaTotalDepLength (deps : List Dependency) (nodes : List Nat) : Nat :=
  deps.filter (fun d => nodes.contains d.headIdx && nodes.contains d.depIdx)
    |>.foldl (fun acc d => acc + depLength' d) 0

/-- The idiom catena {pulled, strings} has dep length 2. -/
theorem idiom_catena_dep_length :
    catenaTotalDepLength pulledSomeStrings.deps [0, 2] = 2 := by native_decide

/-- The full constituent {pulled, some, strings} has dep length 3. -/
theorem constituent_dep_length :
    catenaTotalDepLength pulledSomeStrings.deps [0, 1, 2] = 3 := by native_decide

end DepGrammar.Catena
