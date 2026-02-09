/-
Word Grammar (Dependency Grammar): nodes are words, edges are typed dependencies.
Auxiliaries are heads; lexical rules derive new entries; argument structures specify direction.

Dependency relations use UD.DepRel from Core/UD.lean (Universal Dependencies v2).

References: Hudson (1984, 1990, 2007), Gibson (2025) Syntax, MIT Press.
-/

import Linglib.Core.Basic

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
