import Linglib.Syntax.DependencyGrammar.Projection

/-!
# Catenae

[osborne-gross-2012]

Formalizes the catena (Osborne, Putnam & Groß 2012, *Syntax* 15:4, 354–396):
a connected subgraph of a dependency tree — any word or combination of
words that is continuous with respect to the dominance relation. Catenae
strictly generalize constituents: every constituent is a catena, but not
every catena is a constituent.

## Main declarations

* `bfsReachable` — BFS within a restricted node set; the computable core
  of catena-membership checking.
* `isConnected`, `isCatena`, `isConstituent` — Bool-valued predicates over
  a node list and a dependency list.
* `BidirReachable` — Prop-level bidirectional reachability matching
  `bfsReachable`, with `bidir_symm` / `bidir_trans`.
* `bfsReachable_complete` — every `BidirReachable` node appears in the
  BFS output. Used by downstream files to convert structural reachability
  proofs into computable catena membership.
* `singleton_isCatena` — singletons are catenae.

## Implementation notes

* Predicate-shape definitions return `Bool` to integrate with downstream
  `decide`-style theorems; a substrate-wide migration to
  `Prop` + `[DecidablePred]` is deferred.
* The original `IsCatena` mathlib-Prop bridge (via `SimpleGraph.Preconnected`
  on induced subgraphs) and the worked numerical examples (`tree9`, `tree22`,
  `chain4`, `star4`, counting / ratio API) were removed during the
  mathlib-quality pass; they had no external consumers.

-/

namespace DepGrammar.Catena

open DepGrammar

/-! ### Computable BFS over dependency edges -/

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
    BFS from the first node and check that all others are reached. -/
def isConnected (deps : List Dependency) (nodes : List Nat) : Bool :=
  match nodes with
  | [] => true
  | start :: _ =>
    let reached := bfsReachable deps nodes start
    nodes.all reached.contains

/-- Computable catena check: non-empty and connected in the tree. -/
def isCatena (deps : List Dependency) (nodes : List Nat) : Bool :=
  !nodes.isEmpty && isConnected deps nodes

/-- Check if a node set equals the complete subtree (projection) rooted at
    some node. -/
def isConstituent (deps : List Dependency) (n : Nat) (nodes : List Nat) : Bool :=
  List.range n |>.any fun root =>
    let sub := projection deps root
    nodes.length == sub.length &&
    nodes.all sub.contains &&
    sub.all nodes.contains

/-! ### BFS invariants -/

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
    BFS output — provided `fuel ≥ pfx.length + 1`. -/
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
  · simp only [show (d.headIdx == w) = true from beq_iff_eq.mpr h1,
               show (allowed.contains d.depIdx) = true from h2 ▸ hc_cont,
               Bool.true_and, ↓reduceIte]
    exact congrArg some h2
  · cases heq : d.headIdx == w
    · simp only [Bool.false_and, ↓reduceIte,
                 show (d.depIdx == w) = true from beq_iff_eq.mpr h1,
                 show (allowed.contains d.headIdx) = true from h2 ▸ hc_cont,
                 Bool.true_and]
      exact congrArg some h2
    · have hcw : c = w := h2 ▸ beq_iff_eq.mp heq
      simp only [show (allowed.contains d.depIdx) = true from by
                   rw [h1]; rw [hcw] at hc_cont; exact hc_cont,
                 Bool.true_and, ↓reduceIte]
      exact congrArg some (by rw [h1, hcw])

/-- BFS potential: unvisited-allowed-node count weighted by deps.length, plus
    queue length. Decreases by ≥ 1 at each BFS step when queue elements are
    all in `allowed`. -/
private def bfsPot (deps : List Dependency) (allowed : List Nat)
    (queue visited : List Nat) : Nat :=
  (allowed.filter (fun v => !(visited.contains v))).length * deps.length + queue.length

/-- The filter of `allowed` by `¬vis.contains` splits into: the filter by
    `¬(node::vis).contains` plus elements matching `node`. -/
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
      simp only [this, Bool.not_false, List.length_cons]; omega
    · have : (node :: visited).contains a = true := by
        simp only [List.contains_cons, han, Bool.true_or]
      simp only [this, Bool.not_false, Bool.not_true, List.length_cons]; omega
    · have : (node :: visited).contains a = true := by
        simp only [List.contains_cons, hv, Bool.or_true]
      simp only [this, Bool.not_true]; exact ih
    · have : a = node := beq_iff_eq.mp han
      rw [this] at hv; exact absurd hv (by rw [hcont]; exact Bool.noConfusion)

/-- When a node is processed by BFS, the filter of `allowed` by `¬vis.contains`
    strictly decreases. -/
private theorem allowed_filter_decrease (allowed visited : List Nat) (node : Nat)
    (hnode : node ∈ allowed) (hcont : visited.contains node = false) :
    (allowed.filter (fun v => !(visited.contains v))).length ≥
    (allowed.filter (fun v => !((node :: visited).contains v))).length + 1 := by
  have hsplit := allowed_filter_split allowed visited node hcont
  have hge : (allowed.filter (fun v => v == node)).length ≥ 1 :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨hnode, beq_self_eq_true node⟩)
  omega

/-- If `w` is in the BFS output, was not initially visited, and `c` is a
    bidirectional neighbor of `w` in `allowed`, then `c` is also in the output. -/
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
      · simp only [hcont, ↓reduceIte] at hw ⊢
        apply ih rest visited
          (fun x hx => hqueue x (List.mem_cons.mpr (Or.inr hx)))
          hw hw_not_vis
        simp only [bfsPot, List.length_cons] at hfuel ⊢; omega
      · have hcont_f : visited.contains node = false := by
          cases h : visited.contains node <;> simp_all
        simp only [hcont] at hw ⊢
        set nbrs := deps.filterMap fun d =>
          if d.headIdx == node && allowed.contains d.depIdx then some d.depIdx
          else if d.depIdx == node && allowed.contains d.headIdx then some d.headIdx
          else none with nbrs_def
        by_cases hwn : w = node
        · subst hwn
          have hc_nbr := mem_neighbors_of_edge deps allowed w c hc_allowed hedge
          rw [← nbrs_def] at hc_nbr
          obtain ⟨pfx, sfx, hpfx⟩ := List.append_of_mem
            (List.mem_append.mpr (Or.inr hc_nbr) : c ∈ rest ++ nbrs)
          rw [hpfx]
          apply go_mem_of_queue deps allowed pfx c sfx (w :: visited) fuel'
          have hpfx_bound : pfx.length < rest.length + nbrs.length := by
            have := congrArg List.length hpfx
            simp [List.length_append, List.length_cons] at this; omega
          have hnbrs_bound : nbrs.length ≤ deps.length := filterMap_length_le _ _
          have hw_allowed : w ∈ allowed := hqueue w (List.mem_cons.mpr (Or.inl rfl))
          have hfilter_pos : (allowed.filter (fun v => !(visited.contains v))).length ≥ 1 :=
            List.length_pos_of_mem (List.mem_filter.mpr ⟨hw_allowed, hcont_f ▸ rfl⟩)
          have hFD_ge_D : (allowed.filter (fun v => !(visited.contains v))).length *
              deps.length ≥ deps.length := by
            calc deps.length = 1 * deps.length := (Nat.one_mul _).symm
              _ ≤ _ := Nat.mul_le_mul_right _ hfilter_pos
          simp only [bfsPot, List.length_cons] at hfuel; omega
        · have hw_not_vis' : w ∉ (node :: visited) := by
            simp only [List.mem_cons, not_or]; exact ⟨hwn, hw_not_vis⟩
          have hqueue' : ∀ x ∈ rest ++ nbrs, x ∈ allowed := by
            intro x hx
            rcases List.mem_append.mp hx with hr | hn
            · exact hqueue x (List.mem_cons.mpr (Or.inr hr))
            · exact nbrs_subset_allowed deps allowed node x (nbrs_def ▸ hn)
          apply ih (rest ++ nbrs) (node :: visited) hqueue' hw hw_not_vis'
          have hnode_allowed : node ∈ allowed :=
            hqueue node (List.mem_cons.mpr (Or.inl rfl))
          have hfilter_decrease := allowed_filter_decrease allowed visited node
            hnode_allowed hcont_f
          have hnbrs_bound : nbrs.length ≤ deps.length := filterMap_length_le _ _
          have hFD :
              (allowed.filter (fun v => !(visited.contains v))).length * deps.length ≥
              (allowed.filter (fun v => !((node :: visited).contains v))).length *
                deps.length + deps.length := by
            have h1 := Nat.mul_le_mul_right deps.length hfilter_decrease
            rw [Nat.add_mul] at h1; simp only [Nat.one_mul] at h1; exact h1
          simp only [bfsPot, List.length_cons, List.length_append] at hfuel ⊢
          omega

/-! ### Bidirectional reachability (Prop level) -/

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

/-- Append a step to the end of a bidirectional path. -/
theorem bidir_step_append {deps : List Dependency} {allowed : List Nat}
    {u v w : Nat}
    (h : BidirReachable deps allowed u v) (hv : v ∈ allowed) (hw : w ∈ allowed)
    (hedge : ∃ d ∈ deps, (d.headIdx = v ∧ d.depIdx = w) ∨
                          (d.depIdx = v ∧ d.headIdx = w)) :
    BidirReachable deps allowed u w := by
  revert hv hedge
  induction h with
  | here _ hq =>
    intro hqmem hedge
    exact .step _ _ w hqmem hw hedge (.here w hw)
  | step a b _ ha hb hedgeAB _ ih =>
    intro hcmem hedge
    exact .step a b w ha hb hedgeAB (ih hcmem hedge)

/-- Bidirectional reachability is symmetric. -/
theorem bidir_symm {deps : List Dependency} {allowed : List Nat}
    {u v : Nat} (h : BidirReachable deps allowed u v) :
    BidirReachable deps allowed v u := by
  induction h with
  | here w hw => exact .here w hw
  | step a b _ ha hb hedge _ ih =>
    have hedge' : ∃ d ∈ deps, (d.headIdx = b ∧ d.depIdx = a) ∨
                                (d.depIdx = b ∧ d.headIdx = a) := by
      obtain ⟨d, hd, hor⟩ := hedge
      exact ⟨d, hd, hor.elim (fun ⟨h1, h2⟩ => Or.inr ⟨h2, h1⟩)
                              (fun ⟨h1, h2⟩ => Or.inl ⟨h2, h1⟩)⟩
    exact bidir_step_append ih hb ha hedge'

/-- Bidirectional reachability is transitive. -/
theorem bidir_trans {deps : List Dependency} {allowed : List Nat}
    {u v w : Nat} (h1 : BidirReachable deps allowed u v)
    (h2 : BidirReachable deps allowed v w) :
    BidirReachable deps allowed u w := by
  induction h1 with
  | here _ _ => exact h2
  | step a b _ ha hb hedge _ ih => exact .step a b w ha hb hedge (ih h2)

/-! ### BFS completeness -/

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

/-- The `bfsReachable` output is closed under bidirectional edges within `allowed`. -/
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
    `bfsReachable` output. -/
theorem bfsReachable_complete (deps : List Dependency) (allowed : List Nat)
    (start target : Nat) (h : BidirReachable deps allowed start target) :
    target ∈ bfsReachable deps allowed start := by
  have hstart : start ∈ allowed := by
    cases h with
    | here v hv => exact hv
    | step u _ _ hu _ _ _ => exact hu
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
  show (bfsReachable deps [v] v).contains v = true
  unfold bfsReachable bfsReachable.go
  simp only [List.contains_nil, Bool.false_eq_true, ↓reduceIte]
  exact List.elem_eq_true_of_mem
    (mem_go_of_mem_visited _ _ _ _ _ v List.mem_cons_self)

end DepGrammar.Catena
