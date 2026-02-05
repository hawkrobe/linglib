/-
Word Grammar (Dependency Grammar): nodes are words, edges are typed dependencies.
Auxiliaries are heads; lexical rules derive new entries; argument structures specify direction.

References: Hudson (1984, 1990, 2007), Gibson (2025) Syntax, MIT Press.
-/

import Linglib.Core.Basic

namespace DepGrammar

section DependencyTypes

/-- Types of dependency relations. -/
inductive DepType where
  | subj      -- subject (noun → verb)
  | obj       -- direct object (noun → verb)
  | iobj      -- indirect object (noun → verb)
  | det       -- determiner (det → noun)
  | amod      -- adjectival modifier (adj → noun)
  | advmod    -- adverbial modifier (adv → verb)
  | aux       -- auxiliary (aux → verb)
  | case_     -- case marker / preposition (prep → noun)
  | obl       -- oblique argument (prep phrase → verb)
  | nmod      -- nominal modifier (noun → noun, via prep)
  | comp      -- complement clause (clause → verb)
  | mark      -- subordinator/complementizer (comp → verb)
  | conj      -- conjunction
  | root      -- root of the sentence (no head)
  deriving Repr, DecidableEq, Inhabited

instance : ToString DepType where
  toString
    | .subj => "subj"
    | .obj => "obj"
    | .iobj => "iobj"
    | .det => "det"
    | .amod => "amod"
    | .advmod => "advmod"
    | .aux => "aux"
    | .case_ => "case"
    | .obl => "obl"
    | .nmod => "nmod"
    | .comp => "comp"
    | .mark => "mark"
    | .conj => "conj"
    | .root => "root"

end DependencyTypes

section DependenciesAndTrees

/-- A dependency: directed edge from head to dependent. -/
structure Dependency where
  headIdx : Nat
  depIdx : Nat
  depType : DepType
  deriving Repr, DecidableEq

/-- A dependency tree for a sentence. -/
structure DepTree where
  words : List Word
  deps : List Dependency
  rootIdx : Nat
  deriving Repr

end DependenciesAndTrees

section ArgumentStructure

/-- Direction of a dependent relative to head. -/
inductive Direction where
  | left
  | right
  deriving Repr, DecidableEq

/-- A single argument requirement. -/
structure ArgReq where
  depType : DepType
  direction : Direction
  required : Bool := true
  category : Option Cat := none
  deriving Repr, DecidableEq

/-- Argument structure: what dependents a word requires/allows. -/
structure ArgStructure where
  args : List ArgReq
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

/-- Check projectivity: no crossing dependencies. -/
def isProjective (t : DepTree) : Bool :=
  t.deps.all λ d1 =>
    t.deps.all λ d2 =>
      if d1 == d2 then true
      else
        if d1.headIdx == d2.headIdx then true
        else
          let (h1, d1i) := (d1.headIdx, d1.depIdx)
          let (h2, d2i) := (d2.headIdx, d2.depIdx)
          let (min1, max1) := (min h1 d1i, max h1 d1i)
          let (min2, max2) := (min h2 d2i, max h2 d2i)
          max1 <= min2 || max2 <= min1 ||
          (min1 <= min2 && max2 <= max1) ||
          (min2 <= min1 && max1 <= max2)

end WellFormedness

section AgreementChecking

/-- Check subject-verb number agreement. -/
def checkSubjVerbAgr (t : DepTree) : Bool :=
  t.deps.all λ d =>
    if d.depType == .subj then
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
def countDepsOfType (t : DepTree) (headIdx : Nat) (dtype : DepType) : Nat :=
  t.deps.filter (λ d => d.headIdx == headIdx && d.depType == dtype) |>.length

/-- Check if verb has correct argument structure. -/
def checkVerbSubcat (t : DepTree) : Bool :=
  List.range t.words.length |>.all λ i =>
    match t.words[i]? with
    | some w =>
      if w.cat == Cat.V then
        let subjCount := countDepsOfType t i .subj
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
    deps := [⟨1, 0, .subj⟩]
    rootIdx := 1 }

/-- Create a simple SVO tree: subject -> verb <- object. -/
def mkSVOTree (subj verb obj : Word) : DepTree :=
  { words := [subj, verb, obj]
    deps := [⟨1, 0, .subj⟩, ⟨1, 2, .obj⟩]
    rootIdx := 1 }

/-- Create Det-N-V tree: det -> noun -> verb. -/
def mkDetNVTree (det noun verb : Word) : DepTree :=
  { words := [det, noun, verb]
    deps := [⟨1, 0, .det⟩, ⟨2, 1, .subj⟩]
    rootIdx := 2 }

/-- Create a ditransitive tree: subj -> verb <- iobj <- obj. -/
def mkDitransTree (subj verb iobj obj : Word) : DepTree :=
  { words := [subj, verb, iobj, obj]
    deps := [⟨1, 0, .subj⟩, ⟨1, 2, .iobj⟩, ⟨1, 3, .obj⟩]
    rootIdx := 1 }

end TreeConstructionHelpers

end DepGrammar
