module

public import Mathlib.Tactic.DeriveFintype

/-!
# Universal Dependencies: dependency relations
[de-marneffe-zeman-2021]

The universal dependency relations of UD v2 and the arcs of a dependency tree, the
vocabulary of the dependency grammars and of the dependency-length data.

Official site: <https://universaldependencies.org/>
-/

@[expose] public section

namespace UD

/-- Universal dependency relations.

    Organized by function following the UD documentation.
    These encode grammatical relations between a head and its dependent.

    Reference: https://universaldependencies.org/u/dep/ -/
inductive DepRel where
  -- Core arguments
  | nsubj      -- nominal subject: "He works"
  | nsubjPass  -- passive nominal subject: "He was seen"
  | csubj      -- clausal subject: "What he said is true"
  | csubjPass  -- passive clausal subject
  | obj        -- direct object: "sees her"
  | iobj       -- indirect object: "gave him a book"
  | ccomp      -- clausal complement: "said that..."
  | xcomp      -- open clausal complement: "wants to go"

  -- Non-core dependents
  | obl        -- oblique nominal: "in the morning"
  | vocative   -- vocative: "John, come here"
  | expl       -- expletive: "It rains"
  | dislocated -- dislocated element
  | advcl      -- adverbial clause modifier: "when he arrived"

  -- Nominal dependents
  | nmod       -- nominal modifier: "cup of tea"
  | appos      -- appositional modifier: "Sam, my brother"
  | nummod     -- numeric modifier: "three books"
  | acl        -- adnominal clause: "the man sitting there" (relative clause)

  -- Modifier words
  | amod       -- adjectival modifier: "big house"
  | advmod     -- adverbial modifier: "very fast"
  | discourse  -- discourse element: "well, ..."

  -- Function words
  | aux        -- auxiliary: "has eaten"
  | auxPass    -- passive auxiliary: "was eaten"
  | cop        -- copula: "is happy"
  | mark       -- marker: "that" in "said that..."
  | det        -- determiner: "the book"
  | clf        -- classifier
  | case_      -- case marking: "to" in "go to school"

  -- Compounding and multiword expressions
  | compound   -- compound: "ice cream"
  | flat       -- flat multiword expression: "New York"
  | fixed      -- fixed multiword expression: "in spite of"

  -- Loose joining
  | list       -- list
  | parataxis  -- parataxis: loosely joined clauses
  | orphan     -- orphan in ellipsis
  | goesWith   -- goes with (incorrectly split tokens)
  | reparandum -- reparandum (disfluency)

  -- Coordination
  | conj       -- conjunct: "bread and butter" (butter depends on bread)
  | cc         -- coordinating conjunction: "and" in above

  -- Special relations
  | punct      -- punctuation
  | root       -- root of the sentence
  | dep        -- unspecified dependency

  deriving DecidableEq, Repr, Inhabited

/-- String representation matching UD conventions -/
def DepRel.toString : DepRel → String
  | .nsubj      => "nsubj"
  | .nsubjPass  => "nsubj:pass"
  | .csubj      => "csubj"
  | .csubjPass  => "csubj:pass"
  | .obj        => "obj"
  | .iobj       => "iobj"
  | .ccomp      => "ccomp"
  | .xcomp      => "xcomp"
  | .obl        => "obl"
  | .vocative   => "vocative"
  | .expl       => "expl"
  | .dislocated => "dislocated"
  | .advcl      => "advcl"
  | .nmod       => "nmod"
  | .appos      => "appos"
  | .nummod     => "nummod"
  | .acl        => "acl"
  | .amod       => "amod"
  | .advmod     => "advmod"
  | .discourse  => "discourse"
  | .aux        => "aux"
  | .auxPass    => "aux:pass"
  | .cop        => "cop"
  | .mark       => "mark"
  | .det        => "det"
  | .clf        => "clf"
  | .case_      => "case"
  | .compound   => "compound"
  | .flat       => "flat"
  | .fixed      => "fixed"
  | .list       => "list"
  | .parataxis  => "parataxis"
  | .orphan     => "orphan"
  | .goesWith   => "goeswith"
  | .reparandum => "reparandum"
  | .conj       => "conj"
  | .cc         => "cc"
  | .punct      => "punct"
  | .root       => "root"
  | .dep        => "dep"

instance : ToString DepRel := ⟨DepRel.toString⟩

/-- Is this a core argument relation? -/
def DepRel.isCoreArg : DepRel → Bool
  | .nsubj | .nsubjPass | .csubj | .csubjPass
  | .obj | .iobj | .ccomp | .xcomp => true
  | _ => false

/-- Is this a valency-bearing dependency? Extends `isCoreArg` with
    `.obl` (oblique nominals), which valency frameworks (e.g.
    [osborne-li-2023] on dependency-grammar valent typology)
    treat as a valency role even though UD classifies it as
    non-core. -/
def DepRel.isValencyArg : DepRel → Bool
  | .nsubj | .nsubjPass | .csubj | .csubjPass
  | .obj | .iobj | .ccomp | .xcomp | .obl => true
  | _ => false

/-- Is this a subject relation? -/
def DepRel.isSubject : DepRel → Bool
  | .nsubj | .nsubjPass | .csubj | .csubjPass => true
  | _ => false

/-- Is this an object relation? -/
def DepRel.isObject : DepRel → Bool
  | .obj | .iobj => true
  | _ => false

/-- Is this a modifier relation? -/
def DepRel.isModifier : DepRel → Bool
  | .amod | .advmod | .nmod | .nummod | .advcl | .acl => true
  | _ => false

/-- Is this a function word relation? -/
def DepRel.isFunctionWord : DepRel → Bool
  | .aux | .auxPass | .cop | .mark | .det | .case_ | .clf => true
  | _ => false

/-- A single dependency arc in a UD tree -/
structure DepArc where
  /-- Index of the dependent word (1-indexed) -/
  dependent : Nat
  /-- Index of the head word (0 = root) -/
  head : Nat
  /-- The dependency relation -/
  deprel : DepRel
  deriving DecidableEq, Repr


end UD
