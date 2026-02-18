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

/-- Bundled well-formedness: unique heads + valid index bounds.
    Collects the three hypotheses that most dominance/planarity theorems need. -/
structure DepTree.WF (t : DepTree) : Prop where
  uniqueHeads : hasUniqueHeads t = true
  depIdx_lt : ∀ d ∈ t.deps, d.depIdx < t.words.length
  headIdx_lt : ∀ d ∈ t.deps, d.headIdx < t.words.length

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
