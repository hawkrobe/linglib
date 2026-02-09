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
def blocks (sorted : List Nat) : List (List Nat) :=
  match sorted with
  | [] => []
  | first :: rest =>
    let (result, current) := rest.foldl (λ (acc, cur) n =>
      match cur.getLast? with
      | some last => if n == last + 1 then (acc, cur ++ [n])
                     else (acc ++ [cur], [n])
      | none => (acc, [n])
    ) ([], [first])
    result ++ [current]

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
-- Projection Axioms (properties of BFS output)
-- ============================================================================

/-- The output of `projection` is strictly increasing (sorted, no duplicates).
    Proof sketch: BFS visits each node at most once (visited check), then
    `mergeSort` produces a sorted list. Since visited prevents duplicates,
    the sorted list is strictly increasing. -/
theorem projection_chain' (deps : List Dependency) (root : Nat) :
    (projection deps root).IsChain (· < ·) := by
  sorry -- TODO: prove from BFS visited-set dedup + mergeSort properties

/-- The output of `projection` is non-empty (root is always included).
    Proof sketch: root is the initial queue element, and since visited starts
    empty, root is always added to visited on the first step. -/
theorem projection_nonempty (deps : List Dependency) (root : Nat) :
    projection deps root ≠ [] := by
  sorry -- TODO: prove root ∈ go [root] [] fuel, then mergeSort preserves non-emptiness

-- ============================================================================
-- List Helper Lemmas (for hierarchy theorem proofs)
-- ============================================================================

/-- For a strictly increasing list, `isInterval = true` iff `gaps` is empty.

    Forward: `isInterval` says `last - first + 1 = length`. For Chain' lists,
    consecutive elements differ by ≥ 1. If any gap exists (diff > 1), the total
    span exceeds length - 1, contradicting isInterval.
    Backward: no gaps + Chain' → all consecutive diffs = 1 → span = length - 1. -/
theorem isInterval_iff_gaps_nil (ls : List Nat) (h : ls.IsChain (· < ·)) :
    isInterval ls = true ↔ gaps ls = [] := by
  sorry -- TODO: induction on ls; arithmetic on sorted lists

/-- For a non-empty strictly increasing list,
    `(blocks ls).length = (gaps ls).length + 1`.

    Proof sketch: induction following the `foldl` in `blocks`. Starting with one
    block, each gap starts a new block (acc grows by 1) while no-gap extends the
    current block (acc unchanged). So #blocks = 1 + #gaps. -/
theorem blocks_length_eq_gaps_length_succ (ls : List Nat)
    (hne : ls ≠ []) (hc : ls.IsChain (· < ·)) :
    (blocks ls).length = (gaps ls).length + 1 := by
  sorry -- TODO: induction on ls following foldl structure

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

end Projection

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
