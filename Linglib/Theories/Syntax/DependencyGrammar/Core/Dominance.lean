import Linglib.Theories.Syntax.DependencyGrammar.Core.Projection

/-!
Dominance properties under the unique-heads constraint: parent-pointer
tracing, iterParent chains, antisymmetry of dominance, and `dominates_to_parent`.

These results require `hasUniqueHeads` and/or `isAcyclic` from Basic.lean
and the Dominates inductive + projection bridge theorems from Projection.lean.
-/

namespace DepGrammar

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

end DepGrammar
