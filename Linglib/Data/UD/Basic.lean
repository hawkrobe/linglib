import Mathlib.Tactic.DeriveFintype

/-!
# Universal Dependencies Types
[de-marneffe-zeman-2021]

Universal part-of-speech tags (UPOS), morphological features, and dependency
relations from UD v2.

These provide theory-neutral lexical categories, morphological annotations,
and grammatical relations that can be used throughout the library and mapped
to/from theory-specific categories (CCG.Cat, Minimalism features, DG trees, etc.).

Official site: <https://universaldependencies.org/>

## Provenance

UD is an external annotation standard ([de-marneffe-zeman-2021]); this file is
the linglib mirror of its v2 surface, and `Data/UD/` is the standard's area —
treebank data (CoNLL-U) belongs here beside the vocabulary, paralleling
`Data/WALS/` (schema + datapoints). Its types are the foundational
substrate every other layer builds on: `Features/` aliases the feature types
(e.g. `Number.fromUD`/`Number.toUD`, …) and `Morphology/Word.lean` builds the
ms-word token over the vocabulary.
The bare `UD` namespace (no `Data.` prefix) is intentional — UD is its own
external project. Subsumption-order theory over `MorphFeatures` lives in
`Morphology/Unification.lean` (mathlib-importing); this file stays mathlib-light.
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
    root-namespace `Case` (`Features/Case/Basic.lean`), reachable by
    `Case.toUD`/`Case.fromUD`. -/
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

/-- A morphological feature bundle (partial assignment).
    Uses Option to represent unspecified features. -/
structure MorphFeatures where
  number   : Option Number   := none
  gender   : Option Gender   := none
  case_    : Option Case     := none
  definite : Option Definite := none
  degree   : Option Degree   := none
  pronType : Option PronType := none
  /-- Reflexive (UD `Reflex=Yes`); `false` = feature absent. Distinguishes a reflexive
      anaphor from a plain personal pronoun; not an agreement feature, so not consulted
      by `compatible`. -/
  reflex   : Bool            := false
  person   : Option Person   := none
  verbForm : Option VerbForm := none
  tense    : Option Tense    := none
  aspect   : Option Aspect   := none
  mood     : Option Mood     := none
  voice    : Option Voice    := none
  polarity : Option Polarity := none
  deriving DecidableEq, Repr, Inhabited

/-- Empty feature bundle -/
def MorphFeatures.empty : MorphFeatures := {}

/-- Is this bundle wh-marked — an interrogative or relative pro-form? Derived from
    `pronType` (UD has no standalone wh feature; wh-ness *is* `PronType ∈ {Int, Rel}`). -/
def MorphFeatures.isWh (f : MorphFeatures) : Bool :=
  f.pronType == some .Int || f.pronType == some .Rel

/-- Are two feature bundles compatible — bounded above in the subsumption order
    ([shieber-1986] §3.2.3)? Total over *all* option-valued fields: a conflict in any
    committed feature makes unification fail. (`reflex` needs no clause — a `Bool` slot
    with `false` = absent is always joinable by `||`.) The order-theoretic
    characterization is proved in `Morphology/Unification.lean`. -/
def MorphFeatures.compatible (f1 f2 : MorphFeatures) : Bool :=
  (f1.number.isNone   || f2.number.isNone   || f1.number == f2.number) &&
  (f1.gender.isNone   || f2.gender.isNone   || f1.gender == f2.gender) &&
  (f1.case_.isNone    || f2.case_.isNone    || f1.case_ == f2.case_) &&
  (f1.definite.isNone || f2.definite.isNone || f1.definite == f2.definite) &&
  (f1.degree.isNone   || f2.degree.isNone   || f1.degree == f2.degree) &&
  (f1.pronType.isNone || f2.pronType.isNone || f1.pronType == f2.pronType) &&
  (f1.person.isNone   || f2.person.isNone   || f1.person == f2.person) &&
  (f1.verbForm.isNone || f2.verbForm.isNone || f1.verbForm == f2.verbForm) &&
  (f1.tense.isNone    || f2.tense.isNone    || f1.tense == f2.tense) &&
  (f1.aspect.isNone   || f2.aspect.isNone   || f1.aspect == f2.aspect) &&
  (f1.mood.isNone     || f2.mood.isNone     || f1.mood == f2.mood) &&
  (f1.voice.isNone    || f2.voice.isNone    || f1.voice == f2.voice) &&
  (f1.polarity.isNone || f2.polarity.isNone || f1.polarity == f2.polarity)

/-- Feature compatibility is reflexive: every bundle is compatible with itself
    (each feature matches itself). -/
@[simp] theorem MorphFeatures.compatible_self (f : MorphFeatures) :
    f.compatible f = true := by
  simp only [MorphFeatures.compatible, beq_self_eq_true, Bool.or_true, Bool.and_true]

private theorem MorphFeatures.compatible_clause_comm {α : Type _} [BEq α] [LawfulBEq α]
    (a b : Option α) :
    (a.isNone || b.isNone || a == b) = (b.isNone || a.isNone || b == a) := by
  cases a <;> cases b <;> simp [eq_comm]

/-- Feature compatibility is symmetric. -/
theorem MorphFeatures.compatible_comm (f1 f2 : MorphFeatures) :
    f1.compatible f2 = f2.compatible f1 := by
  unfold MorphFeatures.compatible
  rw [compatible_clause_comm f1.number, compatible_clause_comm f1.gender,
      compatible_clause_comm f1.case_, compatible_clause_comm f1.definite,
      compatible_clause_comm f1.degree, compatible_clause_comm f1.pronType,
      compatible_clause_comm f1.person, compatible_clause_comm f1.verbForm,
      compatible_clause_comm f1.tense, compatible_clause_comm f1.aspect,
      compatible_clause_comm f1.mood, compatible_clause_comm f1.voice,
      compatible_clause_comm f1.polarity]

/-! ### Per-slot projections of `compatible`

φ-compatibility is a conjunction over all slots; these project it onto a single
slot's clause. They confine the coupling to `compatible`'s clause layout to this
one site, beside the definition, so the per-feature faithfulness theorems
(`HasX.compatible_hasX` in `Features/{Person,Number,Gender,Case}/Capabilities.lean`)
consume a named edge rather than each re-`unfold`ing the definition. Only the
four φ-slots that carry a `HasX` mixin are projected. -/

/-- Project φ-compatibility onto its number clause. -/
theorem MorphFeatures.compatible_number {f1 f2 : MorphFeatures}
    (h : f1.compatible f2 = true) :
    (f1.number.isNone || f2.number.isNone || f1.number == f2.number) = true := by
  grind [MorphFeatures.compatible]

/-- Project φ-compatibility onto its gender clause. -/
theorem MorphFeatures.compatible_gender {f1 f2 : MorphFeatures}
    (h : f1.compatible f2 = true) :
    (f1.gender.isNone || f2.gender.isNone || f1.gender == f2.gender) = true := by
  grind [MorphFeatures.compatible]

/-- Project φ-compatibility onto its case clause. -/
theorem MorphFeatures.compatible_case {f1 f2 : MorphFeatures}
    (h : f1.compatible f2 = true) :
    (f1.case_.isNone || f2.case_.isNone || f1.case_ == f2.case_) = true := by
  grind [MorphFeatures.compatible]

/-- Project φ-compatibility onto its person clause. -/
theorem MorphFeatures.compatible_person {f1 f2 : MorphFeatures}
    (h : f1.compatible f2 = true) :
    (f1.person.isNone || f2.person.isNone || f1.person == f2.person) = true := by
  grind [MorphFeatures.compatible]

/-- The information-join of two bundles, field-by-field: keep every committed value
    (left-biased per field, which on `compatible` inputs is symmetric since doubly
    committed fields agree). Only meaningful under `compatible`; `unify` adds the guard. -/
def MorphFeatures.merge (f1 f2 : MorphFeatures) : MorphFeatures where
  number   := f1.number   <|> f2.number
  gender   := f1.gender   <|> f2.gender
  case_    := f1.case_    <|> f2.case_
  definite := f1.definite <|> f2.definite
  degree   := f1.degree   <|> f2.degree
  pronType := f1.pronType <|> f2.pronType
  reflex   := f1.reflex   || f2.reflex
  person   := f1.person   <|> f2.person
  verbForm := f1.verbForm <|> f2.verbForm
  tense    := f1.tense    <|> f2.tense
  aspect   := f1.aspect   <|> f2.aspect
  mood     := f1.mood     <|> f2.mood
  voice    := f1.voice    <|> f2.voice
  polarity := f1.polarity <|> f2.polarity

/-- Unify two feature bundles ([shieber-1986] §3.2.3): the least upper bound in the
    subsumption order when the bundles are compatible (`Morphology/Unification.lean` proves
    the lub laws), failure (`none`) on conflicting information. -/
def MorphFeatures.unify (f1 f2 : MorphFeatures) : Option MorphFeatures :=
  if f1.compatible f2 then some (f1.merge f2) else none

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
