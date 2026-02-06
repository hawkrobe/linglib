/-
# Universal Dependencies Types

Universal part-of-speech tags (UPOS) and morphological features from UD v2.

These provide theory-neutral lexical categories and morphological annotations
that can be used in Phenomena/ and mapped to/from theory-specific categories
(CCG.Cat, Minimalism features, etc.).

## References

- de Marneffe, M.-C., C. Manning, J. Nivre, & D. Zeman (2021).
  "Universal Dependencies." Computational Linguistics 47(2):255-308.
- https://universaldependencies.org/u/pos/
- https://universaldependencies.org/u/feat/
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
  deriving DecidableEq, BEq, Repr, Inhabited, Hashable

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
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Grammatical gender -/
inductive Gender where
  | Masc   -- masculine
  | Fem    -- feminine
  | Neut   -- neuter
  | Com    -- common (masc or fem)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Grammatical case -/
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
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Definiteness -/
inductive Definite where
  | Def    -- definite: the cat
  | Ind    -- indefinite: a cat
  | Spec   -- specific indefinite
  | Cons   -- construct state
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Degree of comparison (for adjectives/adverbs) -/
inductive Degree where
  | Pos    -- positive: big
  | Cmp    -- comparative: bigger
  | Sup    -- superlative: biggest
  | Abs    -- absolute superlative
  | Equ    -- equative
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Grammatical person -/
inductive Person where
  | first  -- 1st person: I, we
  | second -- 2nd person: you
  | third  -- 3rd person: he, she, it, they
  | zero   -- 0 person (impersonal)
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Grammatical tense -/
inductive Tense where
  | Past   -- past: walked
  | Pres   -- present: walks
  | Fut    -- future: will walk
  | Imp    -- imperfect
  | Pqp    -- pluperfect
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Grammatical aspect -/
inductive Aspect where
  | Imp    -- imperfective
  | Perf   -- perfective
  | Prog   -- progressive
  | Prosp  -- prospective
  | Hab    -- habitual
  | Iter   -- iterative
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

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
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Polarity -/
inductive Polarity where
  | Pos    -- positive/affirmative
  | Neg    -- negative
  deriving DecidableEq, BEq, Repr, Inhabited

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
  person   : Option Person   := none
  verbForm : Option VerbForm := none
  tense    : Option Tense    := none
  aspect   : Option Aspect   := none
  mood     : Option Mood     := none
  voice    : Option Voice    := none
  polarity : Option Polarity := none
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Empty feature bundle -/
def MorphFeatures.empty : MorphFeatures := {}

/-- Check if two feature bundles are compatible (unify where both specified) -/
def MorphFeatures.compatible (f1 f2 : MorphFeatures) : Bool :=
  (f1.number.isNone   || f2.number.isNone   || f1.number == f2.number) &&
  (f1.gender.isNone   || f2.gender.isNone   || f1.gender == f2.gender) &&
  (f1.case_.isNone    || f2.case_.isNone    || f1.case_ == f2.case_) &&
  (f1.definite.isNone || f2.definite.isNone || f1.definite == f2.definite) &&
  (f1.person.isNone   || f2.person.isNone   || f1.person == f2.person) &&
  (f1.tense.isNone    || f2.tense.isNone    || f1.tense == f2.tense)

/-- Unify two feature bundles, preferring specified values -/
def MorphFeatures.unify (f1 f2 : MorphFeatures) : Option MorphFeatures :=
  if f1.compatible f2 then
    some {
      number   := f1.number   <|> f2.number
      gender   := f1.gender   <|> f2.gender
      case_    := f1.case_    <|> f2.case_
      definite := f1.definite <|> f2.definite
      degree   := f1.degree   <|> f2.degree
      pronType := f1.pronType <|> f2.pronType
      person   := f1.person   <|> f2.person
      verbForm := f1.verbForm <|> f2.verbForm
      tense    := f1.tense    <|> f2.tense
      aspect   := f1.aspect   <|> f2.aspect
      mood     := f1.mood     <|> f2.mood
      voice    := f1.voice    <|> f2.voice
      polarity := f1.polarity <|> f2.polarity
    }
  else
    none

end UD
