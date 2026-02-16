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

/-- The output of `projection` is non-empty (root is always included). -/
theorem projection_nonempty (deps : List Dependency) (root : Nat) :
    projection deps root ≠ [] := by
  unfold projection; intro h
  have hmem := (List.mergeSort_perm _ (· ≤ ·)).mem_iff.mpr (root_mem_go deps root)
  rw [h] at hmem; simp at hmem

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

end WellFormedness

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
