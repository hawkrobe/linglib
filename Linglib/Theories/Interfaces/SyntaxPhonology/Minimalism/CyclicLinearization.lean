/-!
# Cyclic Linearization of Syntactic Structure
@cite{fox-pesetsky-2005}

Formalizes the core of @cite{fox-pesetsky-2005}'s theory of the
syntax-phonology interface. The key claims:

1. **Spell-out domains**: linearization applies at the end of each phase
   (Spell-out domain), establishing the relative order of overt terminals.

2. **Order Preservation**: ordering established at Spell-out of a domain
   is never deleted or contradicted by later Spell-out.

3. **Successive cyclicity as a consequence**: movement from a phase must
   proceed through the phase edge (leftmost position) to avoid
   contradicting ordering established at earlier Spell-out.

4. **Ordering contradiction → ungrammaticality**: if the ordering
   statements accumulated across phases form a cycle, the structure
   cannot be coherently linearized and the derivation crashes.

The formalization here provides the minimal infrastructure needed to
derive the *meN*-deletion effect in Malayic languages
(@cite{erlewine-sommerlot-2025}), Holmberg's Generalization
(Object Shift requires verb movement), and successive-cyclicity
requirements. All three are formalized as concrete theorems.

## Key definitions

- `Prec`: a precedence statement (α precedes β)
- `allPrecs`: generates all pairwise precedences from a terminal sequence
- `hasContradiction`: checks for direct ordering cycles (a < b ∧ b < a)
- `hasCycle`: checks for cycles of any length via BFS reachability
- `spelloutAndCheck`: accumulates ordering across phases and checks consistency
-/

-- ============================================================================
-- § 1: Precedence Statements
-- ============================================================================

/-- A precedence statement: `before` must linearly precede `after` in PF.
    Corresponds to @cite{fox-pesetsky-2005}'s "α < β" notation (their (10)). -/
structure Prec where
  before : String
  after  : String
  deriving DecidableEq, Repr

/-- Generate all pairwise precedences from a left-to-right sequence of
    overt terminal labels. Given terminals [a, b, c], produces
    [a < b, a < c, b < c]. -/
def allPrecs : List String → List Prec
  | [] => []
  | x :: xs => (xs.map fun y => ⟨x, y⟩) ++ allPrecs xs

-- ============================================================================
-- § 2: Ordering Table and Consistency
-- ============================================================================

/-- An Ordering Table is the accumulated set of precedence statements
    across all Spell-out domains in a derivation.
    Corresponds to @cite{fox-pesetsky-2005}'s Ordering Table ((52)). -/
abbrev OrderingTable := List Prec

/-- Whether an Ordering Table contains a direct contradiction: some α, β
    such that both α < β and β < α appear. A contradiction means the
    derivation cannot be coherently linearized and crashes.

    Note: for the Malayic voice/extraction application, all contradictions
    are direct (no transitive closure needed). A more general implementation
    would compute the transitive closure; we leave that as future work. -/
def hasContradiction (table : OrderingTable) : Bool :=
  table.any fun s =>
    table.any fun t => s.before == t.after && s.after == t.before

/-- An Ordering Table is consistent iff it contains no contradictions. -/
def isConsistent (table : OrderingTable) : Bool := !hasContradiction table

-- ============================================================================
-- § 3: Spell-out
-- ============================================================================

/-- Spell-out a phase: generate ordering statements from the left-to-right
    sequence of overt terminals in the phase, and add them to the existing
    Ordering Table.

    This implements Order Preservation: existing statements are kept
    (never deleted), and new statements are added.
    Corresponds to @cite{fox-pesetsky-2005}'s Linearize operation ((52)). -/
def spellout (existing : OrderingTable) (phaseTerminals : List String) : OrderingTable :=
  existing ++ allPrecs phaseTerminals

/-- Check whether a multi-phase derivation is consistently linearizable.
    Each element of `phases` is the left-to-right sequence of overt
    terminals at the corresponding Spell-out domain. Ordering statements
    accumulate across phases via Order Preservation. -/
def spelloutAndCheck (phases : List (List String)) : Bool :=
  isConsistent (phases.foldl spellout [])

/-- Order Preservation: existing ordering statements are never deleted
    by Spell-out. All precedences from earlier phases persist.
    Formal content of @cite{fox-pesetsky-2005}'s Order Preservation. -/
theorem spellout_preserves (existing : OrderingTable) (phase : List String)
    (p : Prec) (hp : p ∈ existing) : p ∈ spellout existing phase := by
  unfold spellout; exact List.mem_append_left _ hp

-- ============================================================================
-- § 4: Core Theorems
-- ============================================================================

/-- Every element of `allPrecs ts` has its `after` field drawn from `ts`. -/
theorem allPrecs_after_mem {p : Prec} {ts : List String}
    (h : p ∈ allPrecs ts) : p.after ∈ ts := by
  induction ts with
  | nil => simp [allPrecs] at h
  | cons x xs ih =>
    simp only [allPrecs, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact List.mem_cons_of_mem x hy
    · exact List.mem_cons_of_mem x (ih h)

/-- Every element of `allPrecs ts` has its `before` field drawn from `ts`. -/
theorem allPrecs_before_mem {p : Prec} {ts : List String}
    (h : p ∈ allPrecs ts) : p.before ∈ ts := by
  induction ts with
  | nil => simp [allPrecs] at h
  | cons x xs ih =>
    simp only [allPrecs, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem x (ih h)

/-- In a `Nodup` list, `allPrecs` never contains both `⟨a,b⟩` and `⟨b,a⟩`:
    if `a` precedes `b`, then `b` does not precede `a`. -/
theorem allPrecs_antisym : ∀ (ts : List String), ts.Nodup →
    ∀ (s : Prec), s ∈ allPrecs ts → ∀ (t : Prec), t ∈ allPrecs ts →
    s.before = t.after → s.after ≠ t.before := by
  intro ts
  induction ts with
  | nil => intro _ s hs; simp [allPrecs] at hs
  | cons x xs ih =>
    intro hnd s hs t ht h1
    rw [List.nodup_cons] at hnd; obtain ⟨hx, hnd'⟩ := hnd
    simp only [allPrecs, List.mem_append] at hs ht
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · -- Both from map: s = ⟨x, ys⟩, t = ⟨x, yt⟩
      obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hs
      obtain ⟨yt, hyt, rfl⟩ := List.mem_map.mp ht
      dsimp at h1
      rw [← h1] at hyt
      exact absurd hyt hx
    · -- s from map, t from allPrecs xs
      obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp hs
      dsimp at h1
      have hta := allPrecs_after_mem ht
      rw [← h1] at hta
      exact absurd hta hx
    · -- s from allPrecs xs, t from map
      obtain ⟨yt, hyt, rfl⟩ := List.mem_map.mp ht
      dsimp at h1 ⊢
      intro heq
      have hsa := allPrecs_after_mem hs
      rw [heq] at hsa
      exact hx hsa
    · -- Both from allPrecs xs: use IH
      exact ih hnd' s hs t ht h1

/-- A single phase is always consistent: no ordering contradiction can arise
    within a single left-to-right linearization of distinct terminals.
    Requires `Nodup` because duplicate terminals create trivial self-loops
    (α < α), which `hasContradiction` correctly flags. -/
theorem single_phase_consistent (ts : List String) (hnd : ts.Nodup) :
    isConsistent (allPrecs ts) = true := by
  unfold isConsistent
  suffices h : hasContradiction (allPrecs ts) = false by simp [h]
  rcases Bool.eq_false_or_eq_true (hasContradiction (allPrecs ts)) with hc | hc
  · exfalso
    unfold hasContradiction at hc
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨s, hs, t, ht, h1, h2⟩ := hc
    exact allPrecs_antisym _ hnd s hs t ht h1 h2
  · exact hc

/-- Leftward movement from the phase edge preserves ordering.
    Scenario 1 of @cite{fox-pesetsky-2005} (their (13)):
    X was at the left edge of D; when D' is spelled out, X moves further
    left. The new ordering X < α is consistent with X < Y from D. -/
theorem edge_movement_consistent :
    spelloutAndCheck [["X", "Y", "Z"], ["X", "α", "Y", "Z"]] = true := by native_decide

/-- Leftward movement from a non-edge position creates contradiction.
    Scenario 2 of @cite{fox-pesetsky-2005} (their (14)):
    Y was NOT at the left edge of D (X < Y at D Spell-out). When Y moves
    left in D', it must precede α, but α < X and X < Y yield a cycle. -/
theorem non_edge_movement_contradiction :
    spelloutAndCheck [["X", "Y", "Z"], ["Y", "α", "X", "Z"]] = false := by native_decide

/-- Successive-cyclic *wh*-movement avoids ordering contradiction.
    @cite{fox-pesetsky-2005} (their (6)–(8)): *to whom* moves through
    Spec,VP before moving to Spec,CP, preserving VP-internal order. -/
theorem successive_cyclic_ok :
    spelloutAndCheck [["to_whom", "gave", "the_book"],
                      ["to_whom", "that", "Mary", "gave", "the_book"]] = true := by
  native_decide

/-- Non-successive-cyclic movement creates ordering contradiction.
    @cite{fox-pesetsky-2005} (their (3)–(5)): *to whom* skips Spec,VP
    and moves directly to Spec,CP, contradicting VP-internal order. -/
theorem non_successive_cyclic_bad :
    spelloutAndCheck [["gave", "the_book", "to_whom"],
                      ["to_whom", "that", "Mary", "gave", "the_book"]] = false := by
  native_decide

/-- Order-preserving simultaneous movement: two elements moving out of a
    phase in their original relative order creates no contradiction.
    This is the key configuration for Malayic object extraction
    (@cite{erlewine-sommerlot-2025} ex. 55–56). -/
theorem simultaneous_order_preserving :
    spelloutAndCheck [["A", "B", "C"], ["A", "B", "D", "C"]] = true := by native_decide

/-- Simultaneous movement that reverses relative order contradicts. -/
theorem simultaneous_order_reversing :
    spelloutAndCheck [["A", "B", "C"], ["B", "A", "D", "C"]] = false := by native_decide

-- ============================================================================
-- § 5: Holmberg's Generalization
-- ============================================================================

/-! ### Object Shift and verb movement

@cite{fox-pesetsky-2005} derive Holmberg's Generalization: Object Shift
in Scandinavian is only possible when the verb has also moved out of VP.

VP Spell-out establishes V < Obj. If the verb stays in VP and the object
shifts leftward, the higher Spell-out domain orders Obj < V — directly
contradicting V < Obj. When the verb also moves, V < Obj is preserved.
-/

/-- Baseline: no Object Shift, verb moves to I. Consistent.
    VP contains only [V, Obj]; Neg is above VP. -/
theorem no_object_shift :
    spelloutAndCheck [["V", "Obj"],
                      ["Subj", "V", "Neg", "Obj"]] = true := by native_decide

/-- Object Shift WITH verb movement: both V and Obj move past Neg.
    VP-internal ordering V < Obj is preserved at IP. Consistent.
    @cite{fox-pesetsky-2005} §3. -/
theorem object_shift_with_verb_movement :
    spelloutAndCheck [["V", "Obj"],
                      ["Subj", "V", "Obj", "Neg"]] = true := by native_decide

/-- Object Shift WITHOUT verb movement: Obj moves past Neg but V stays.
    VP: V < Obj. IP: Obj < ... < V. Direct contradiction → crash.
    This IS Holmberg's Generalization, derived from cyclic linearization.
    @cite{fox-pesetsky-2005} §3. -/
theorem object_shift_without_verb_movement :
    spelloutAndCheck [["V", "Obj"],
                      ["Subj", "Obj", "Neg", "V"]] = false := by native_decide

-- ============================================================================
-- § 6: Transitive Cycle Detection
-- ============================================================================

/-! ### Full cycle detection via reachability

`hasContradiction` detects direct ordering cycles (a < b ∧ b < a).
For completeness, `hasCycle` detects cycles of any length via BFS
reachability. For all current applications (Malayic voice, Holmberg's
Generalization), contradictions are direct, so both functions agree.
`hasCycle` is provided for future applications involving transitive cycles.
-/

/-- BFS step for reachability in the directed precedence graph.
    Implementation detail for `reachable`. -/
def reachGo (table : OrderingTable) (dst : String) :
    Nat → List String → List String → Bool
  | 0, _, _ => false
  | fuel + 1, worklist, visited =>
    match worklist with
    | [] => false
    | x :: rest =>
      if x == dst then true
      else if visited.contains x then reachGo table dst fuel rest visited
      else
        let next := (table.filter (·.before == x)).map (·.after)
        reachGo table dst fuel (rest ++ next) (x :: visited)

/-- Whether `dst` is reachable from `src` via directed edges in `table`. -/
def reachable (table : OrderingTable) (src dst : String) : Bool :=
  reachGo table dst (2 * table.length + 1) [src] []

/-- Whether an Ordering Table contains a directed cycle of any length.
    For each edge a → b, checks if b can reach a via other edges. -/
def hasCycle (table : OrderingTable) : Bool :=
  table.any fun edge => reachable table edge.after edge.before

/-- `hasCycle` detects the transitive cycle a < b, b < c, c < a
    which `hasContradiction` misses (no direct a < b ∧ b < a pair). -/
theorem hasCycle_detects_transitive :
    hasCycle [⟨"a", "b"⟩, ⟨"b", "c"⟩, ⟨"c", "a"⟩] = true ∧
    hasContradiction [⟨"a", "b"⟩, ⟨"b", "c"⟩, ⟨"c", "a"⟩] = false := by native_decide

/-- On the Malayic meN-deletion example, both checks agree
    (the contradiction is direct). -/
theorem cycle_direct_agree_malayic :
    let t := allPrecs ["theme", "me-", "agent", "NV"] ++
             allPrecs ["theme", "agent", "Aux", "me-", "NV"]
    hasCycle t = hasContradiction t := by native_decide
