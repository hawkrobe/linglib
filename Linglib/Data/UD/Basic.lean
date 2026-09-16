import Mathlib.Tactic.DeriveFintype
import Linglib.Core.Order.Flat

/-!
# Universal Dependencies Types
[de-marneffe-zeman-2021]

Universal part-of-speech tags (UPOS), morphological features, and dependency
relations from UD v2.

The categories are the library's word-class vocabulary (`Morphology.Word.cat`); the
morphological annotation is the treebank record a token's analytical features realize as
and ingest from (`Morphology/Word/UD.lean`); the relations are read by the dependency
grammars.

Official site: <https://universaldependencies.org/>

## Provenance

UD is an external annotation standard ([de-marneffe-zeman-2021]); this file is
the linglib mirror of its v2 surface, and `Data/UD/` is the standard's area —
treebank data (CoNLL-U) belongs here beside the vocabulary, paralleling
`Data/WALS/` (schema + datapoints). Its types are the foundational
substrate every other layer builds on: the analytical inventories realize as its tags in
`Morphology/Word/UD.lean` and `Morphology/Word/Basic.lean` builds the ms-word token over
its categories.
The bare `UD` namespace (no `Data.` prefix) is intentional — UD is its own
external project. Feature slots are `Flat`-valued (`Core/Order/Flat.lean`).
-/

namespace UD

-- ============================================================================
-- Part-of-Speech Tags (UPOS)
-- ============================================================================

/-- Universal part-of-speech tags (UPOS).

    17 coarse-grained categories designed for cross-linguistic consistency.
    Every word in every language can be assigned one of these tags. -/
inductive UPOS where
  -- Open class words (content words)
  | ADJ    -- adjective: big, old, green, first
  | ADV    -- adverb: very, tomorrow, down, where, there
  | INTJ   -- interjection: psst, ouch, bravo, hello
  | NOUN   -- noun: girl, cat, tree, air, beauty
  | PROPN  -- proper noun: Mary, John, London, NATO
  | VERB   -- verb: run, runs, running, eat, ate

  -- Closed class words (function words)
  | ADP    -- adposition: in, to, during (preposition/postposition)
  | AUX    -- auxiliary: has, is, should, was, will
  | CCONJ  -- coordinating conjunction: and, or, but
  | DET    -- determiner: a, an, the, this, which
  | NUM    -- numeral: 1, 2, one, two, first
  | PART   -- particle: 's, not, to (infinitive marker)
  | PRON   -- pronoun: I, you, he, she, myself, who
  | SCONJ  -- subordinating conjunction: if, while, that

  -- Other
  | PUNCT  -- punctuation: . , ; : ! ?
  | SYM    -- symbol: $, %, @, +, :), 😀
  | X      -- other: foreign words, typos, abbreviations
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- String representation matching UD conventions -/
def UPOS.toString : UPOS → String
  | .ADJ   => "ADJ"
  | .ADV   => "ADV"
  | .INTJ  => "INTJ"
  | .NOUN  => "NOUN"
  | .PROPN => "PROPN"
  | .VERB  => "VERB"
  | .ADP   => "ADP"
  | .AUX   => "AUX"
  | .CCONJ => "CCONJ"
  | .DET   => "DET"
  | .NUM   => "NUM"
  | .PART  => "PART"
  | .PRON  => "PRON"
  | .SCONJ => "SCONJ"
  | .PUNCT => "PUNCT"
  | .SYM   => "SYM"
  | .X     => "X"

instance : ToString UPOS := ⟨UPOS.toString⟩

/-- Is this an open class (content) word? -/
def UPOS.isOpenClass : UPOS → Bool
  | .ADJ | .ADV | .INTJ | .NOUN | .PROPN | .VERB => true
  | _ => false

/-- Is this a closed class (function) word? -/
def UPOS.isClosedClass : UPOS → Bool
  | .ADP | .AUX | .CCONJ | .DET | .NUM | .PART | .PRON | .SCONJ => true
  | _ => false

/-- Is this a nominal (entity-denoting) category? -/
def UPOS.isNominal : UPOS → Bool
  | .NOUN | .PROPN | .PRON | .NUM => true
  | _ => false

/-- Is this a predicate (event-denoting) category? -/
def UPOS.isPredicate : UPOS → Bool
  | .VERB | .AUX => true
  | _ => false

/-- Is this a modifier category? -/
def UPOS.isModifier : UPOS → Bool
  | .ADJ | .ADV => true
  | _ => false

-- ============================================================================
-- Morphological Features
-- ============================================================================

-- Nominal Features

/-- Grammatical number -/
inductive Number where
  | Sing   -- singular: cat, I
  | Plur   -- plural: cats, we
  | Dual   -- dual (two): eyes (in some languages)
  | Tri    -- trial (three)
  | Pauc   -- paucal (few)
  | Grpa   -- greater paucal
  | Grpl   -- greater plural
  | Inv    -- inverse number
  | Coll   -- collective
  | Count  -- count form
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical gender -/
inductive Gender where
  | Masc   -- masculine
  | Fem    -- feminine
  | Neut   -- neuter
  | Com    -- common (masc or fem)
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical case (UD `Case` feature, https://universaldependencies.org/u/feat/Case.html).

    Battle-tested annotation tagset shared across all UD treebanks. The 28
    constructors below cover the standard UD values. This is the
    *realization* vocabulary; the canonical analytical inventory is the
    root-namespace `Case` (`Syntax/Case/Basic.lean`), realized and ingested in
    `Morphology/Word/UD.lean`. -/
inductive Case where
  | Nom    -- nominative: subject
  | Acc    -- accusative: direct object
  | Gen    -- genitive: possessor
  | Dat    -- dative: indirect object
  | Ins    -- instrumental
  | Loc    -- locative
  | Voc    -- vocative
  | Abl    -- ablative
  | Erg    -- ergative
  | Abs    -- absolutive
  -- Additional cases for specific languages
  | Par    -- partitive
  | Ess    -- essive
  | Tra    -- translative
  | Com    -- comitative
  | Ade    -- adessive
  | Ine    -- inessive
  | Ill    -- illative
  | Ela    -- elative
  | All    -- allative
  | Sub    -- sublative
  | Sup    -- superessive
  | Del    -- delative
  | Ter    -- terminative
  | Tem    -- temporal
  | Cau    -- causative
  | Ben    -- benefactive
  | Per    -- perlative: path, motion through
  | Abe    -- abessive/privative: 'without X'
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Definiteness -/
inductive Definite where
  | Def    -- definite: the cat
  | Ind    -- indefinite: a cat
  | Spec   -- specific indefinite
  | Cons   -- construct state
  deriving DecidableEq, Repr, Inhabited

/-- Degree of comparison (for adjectives/adverbs) -/
inductive Degree where
  | Pos    -- positive: big
  | Cmp    -- comparative: bigger
  | Sup    -- superlative: biggest
  | Abs    -- absolute superlative
  | Equ    -- equative
  deriving DecidableEq, Repr, Inhabited

-- Pronominal Features

/-- Pronoun type -/
inductive PronType where
  | Prs    -- personal: I, you, he
  | Rcp    -- reciprocal: each other
  | Art    -- article
  | Int    -- interrogative: who, what
  | Rel    -- relative: who, which
  | Dem    -- demonstrative: this, that
  | Emp    -- emphatic
  | Tot    -- total/collective: all, every
  | Neg    -- negative: nobody, nothing
  | Ind    -- indefinite: somebody, something
  | Exc    -- exclamative
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical person -/
inductive Person where
  | first  -- 1st person: I, we
  | second -- 2nd person: you
  | third  -- 3rd person: he, she, it, they
  | zero   -- 0 person (impersonal)
  deriving DecidableEq, Repr, Inhabited

-- Verbal Features

/-- Verb form -/
inductive VerbForm where
  | Fin    -- finite
  | Inf    -- infinitive
  | Part   -- participle
  | Ger    -- gerund
  | Gdv    -- gerundive
  | Sup    -- supine
  | Conv   -- converb/adverbial participle
  | Vnoun  -- verbal noun (masdar)
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical tense -/
inductive Tense where
  | Past   -- past: walked
  | Pres   -- present: walks
  | Fut    -- future: will walk
  | Imp    -- imperfect
  | Pqp    -- pluperfect
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical aspect -/
inductive Aspect where
  | Imp    -- imperfective
  | Perf   -- perfective
  | Prog   -- progressive
  | Prosp  -- prospective
  | Hab    -- habitual
  | Iter   -- iterative
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical mood -/
inductive Mood where
  | Ind    -- indicative
  | Sub    -- subjunctive
  | Imp    -- imperative
  | Cnd    -- conditional
  | Opt    -- optative
  | Jus    -- jussive
  | Pot    -- potential
  | Qot    -- quotative
  | Adm    -- admirative
  | Nec    -- necessitative
  | Irr    -- irrealis
  deriving DecidableEq, Repr, Inhabited

/-- Grammatical voice -/
inductive Voice where
  | Act    -- active
  | Pass   -- passive
  | Mid    -- middle
  | Rcp    -- reciprocal
  | Cau    -- causative
  | Antip  -- antipassive
  | Dir    -- direct
  | Inv    -- inverse
  | Lfoc   -- location-focus
  | Bfoc   -- beneficiary-focus
  deriving DecidableEq, Repr, Inhabited

/-- Polarity -/
inductive Polarity where
  | Pos    -- positive/affirmative
  | Neg    -- negative
  deriving DecidableEq, Repr, Inhabited

-- Feature Bundle

/-- A morphological annotation record, a tag or `⊥` in each feature. -/
structure MorphFeatures where
  number   : Flat Number   := ⊥
  gender   : Flat Gender   := ⊥
  case_    : Flat Case     := ⊥
  definite : Flat Definite := ⊥
  degree   : Flat Degree   := ⊥
  pronType : Flat PronType := ⊥
  /-- Reflexive, `Reflex=Yes`; `false` when the feature is absent. -/
  reflex   : Bool          := false
  person   : Flat Person   := ⊥
  verbForm : Flat VerbForm := ⊥
  tense    : Flat Tense    := ⊥
  aspect   : Flat Aspect   := ⊥
  mood     : Flat Mood     := ⊥
  voice    : Flat Voice    := ⊥
  polarity : Flat Polarity := ⊥
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- Dependency Relations
-- ============================================================================

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
