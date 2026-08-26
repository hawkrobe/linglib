/-!
# Noun categorization devices

This file defines the vocabulary of Aikhenvald's typology of noun categorization devices: the
nine classifier types individuated by morphosyntactic locus, the scopes, assignment principles
and surface realizations by which a system is described, the semantic parameters classifiers
encode, a lexical schema for individual classifiers, and the competing compositional strategies
attributed to classifier constructions. Per-language values of the typological parameters are
recorded field by field in each Fragment's `ClassifierSystem.lean` (`classifierType`,
`classifierScopes`, `classifierAssignment`, `classifierRealizations`, `classifierAgreement`,
`classifierObligatory`, `classifierDefault`, `classifierSemantics`, `obligatoryNumber`); the
record assembling them is study-local (`Aikhenvald2000.Parameters`). The `nounClass` type
collapses the finer gender structure of `Features/Gender`.

## Main definitions

* `ClassifierType`, `ClassifierType.locus` — the device types and the scope defining each.
* `CategorizationScope`, `AssignmentPrinciple`, `SurfaceRealization` — the descriptive axes.
* `SemanticParameter`, `ShapeDimension` — the semantic parameters of noun categorization.
* `ClassifierEntry`, `ClassifierEntry.Encodes`, `collectSemantics` — the per-classifier schema.
* `ClassifierStrategy` — the compositional strategies a framework may attribute to classifiers.

## References

* [aikhenvald-2000], §1.5, §2.3, §4.4.1, §10.5, §11.1, Tables 15.1–15.3
* [corbett-1991]
* [downing-1996]
* [allan-1977]
* [little-moroney-royer-2022]
-/

namespace NounCategorization

/-! ### Classifier types -/

/-- The nine classifier types, focal points on a continuum individuated by morphosyntactic
locus and scope rather than discrete classes. -/
inductive ClassifierType where
  /-- Noun class or gender: a closed obligatory system realized by agreement inside and
  sometimes outside the noun phrase, with an inventory often of two to ten. -/
  | nounClass
  /-- Noun classifier: characterizes the head noun itself, independently of other NP elements,
  as a free form or an affix on the noun. -/
  | nounClassifier
  /-- Numeral classifier: characterizes nouns in numeral and quantifier phrases, as a free form
  or an affix on the numeral, with an often large inventory. -/
  | numeralClassifier
  /-- Relational classifier: characterizes the possessive relation in a possessive NP. -/
  | relationalClassifier
  /-- Possessed classifier: characterizes the possessed noun in a possessive NP. -/
  | possessedClassifier
  /-- Possessor classifier: characterizes the possessor; very rare. -/
  | possessorClassifier
  /-- Verbal classifier: marks agreement on the verb with an S or O argument, as an
  incorporated classifier, an affix, or a suppletive classificatory stem. -/
  | verbalClassifier
  /-- Locative classifier: marks agreement with the head noun in an adpositional NP. -/
  | locativeClassifier
  /-- Deictic classifier: occurs with articles and demonstratives, marking spatial location
  or determination. -/
  | deicticClassifier
  deriving DecidableEq, Repr

/-! ### Scope, assignment, and realization -/

/-- The morphosyntactic scope a noun categorization device operates in. -/
inductive CategorizationScope where
  /-- Inside a head-modifier NP: head-modifier agreement. -/
  | headModifierNP
  /-- Outside the NP: predicate-argument agreement. -/
  | predicateArgument
  /-- The noun itself. -/
  | noun
  /-- A numeral or quantifier NP. -/
  | numeralNP
  /-- A possessive NP. -/
  | possessiveNP
  /-- The clause. -/
  | clause
  /-- An adpositional NP. -/
  | adpositionalNP
  /-- An attributive NP with a deictic. -/
  | attributiveNP
  deriving DecidableEq, Repr

/-- The scope defining each classifier type: noun classes inside a head-modifier NP (clause
scope is a further option), numeral classifiers in the numeral NP, and so on. -/
def ClassifierType.locus : ClassifierType → CategorizationScope
  | .nounClass => .headModifierNP
  | .nounClassifier => .noun
  | .numeralClassifier => .numeralNP
  | .relationalClassifier | .possessedClassifier | .possessorClassifier => .possessiveNP
  | .verbalClassifier => .clause
  | .locativeClassifier => .adpositionalNP
  | .deicticClassifier => .attributiveNP

/-- The principle by which nouns are assigned to classes or classifiers. -/
inductive AssignmentPrinciple where
  /-- By the meaning of the referent. -/
  | semantic
  /-- By morphological properties of the noun such as declension or derivational affix. -/
  | morphological
  /-- By phonological properties of the noun such as its initial segment or final vowel. -/
  | phonological
  /-- A semantic core with a morphological or phonological overlay. -/
  | mixed
  deriving DecidableEq, Repr

/-- The surface realization of a classifier morpheme. -/
inductive SurfaceRealization where
  /-- Prefix or proclitic. -/
  | prefix
  /-- Suffix or enclitic. -/
  | suffix
  /-- Clitic. -/
  | clitic
  /-- An independent lexeme. -/
  | freeForm
  /-- Stem-internal vowel change. -/
  | apophony
  /-- A suppletive stem. -/
  | suppletion
  /-- Stress. -/
  | stress
  /-- Reduplication. -/
  | reduplication
  /-- Noun incorporation. -/
  | nounIncorporation
  /-- A repeater: the noun itself, or part of it, serving as its classifier. -/
  | repeater
  deriving DecidableEq, Repr

/-! ### Semantic parameters -/

/-- The semantic parameters noun categorization devices encode, in three large classes —
animacy, physical properties, and function — with type-specific preferences. Speech register
is distinguished from the referent's social status, since honorific classifiers can index the
style of speech rather than the rank of the referent. -/
inductive SemanticParameter where
  /-- Animate versus inanimate. -/
  | animacy
  /-- Human versus non-human. -/
  | humanness
  /-- Male versus female. -/
  | sex
  /-- The social status or rank of a human referent. -/
  | socialStatus
  /-- The kinship relationship of a human referent. -/
  | kinship
  /-- The speech register (honorific, common, humiliative) rather than the referent's status. -/
  | register
  /-- Shape and dimensionality. -/
  | shape
  /-- Vertical versus horizontal orientation. -/
  | direction
  /-- Differentiation of inside from outside, as between rings and holes. -/
  | interioricity
  /-- Whether an outlined entity is delimited. -/
  | boundedness
  /-- Large versus small. -/
  | size
  /-- Plasticity under manipulation: flexible versus rigid. -/
  | consistency
  /-- Physical state, such as liquid or solid. -/
  | constitution
  /-- The material an object is made of. -/
  | material
  /-- Other inherent, time-stable nature, often realized by classifiers specific to one noun. -/
  | nature
  /-- How an object is used or handled. -/
  | function
  /-- The configuration of objects, such as a coil or a row. -/
  | arrangement
  /-- A quantity of objects, such as a cluster or a flock. -/
  | quanta
  /-- Colour: perceptually salient but never a basis for noun categorization. -/
  | colour
  deriving DecidableEq, Repr

/-- The three values of dimensionality: one-dimensional (long), two-dimensional (flat), and
three-dimensional (spherical). -/
inductive ShapeDimension where
  | oneD
  | twoD
  | threeD
  deriving DecidableEq, Repr

/-! ### Classifier entries -/

/-- A classifier lexical entry: its form and gloss, the semantic parameters motivating its
choice, whether it is the general classifier of its system, whether it is mensural rather than
sortal, and its dimensionality when shape-based. -/
structure ClassifierEntry where
  /-- Surface form. -/
  form : String
  /-- Gloss. -/
  gloss : String := ""
  /-- The semantic parameters motivating the choice of this classifier. -/
  semantics : List SemanticParameter := []
  /-- Whether this is the general classifier that can replace the specific ones. -/
  isDefault : Bool := false
  /-- Whether the classifier individuates by measure rather than by inherent properties. -/
  isMensural : Bool := false
  /-- Dimensionality, when the classifier is shape-based. -/
  shapeDimension : Option ShapeDimension := none
  deriving Repr, DecidableEq

/-- `c.Encodes p` when the classifier `c` is motivated by the parameter `p`. -/
def ClassifierEntry.Encodes (c : ClassifierEntry) (p : SemanticParameter) : Prop :=
  p ∈ c.semantics

instance (c : ClassifierEntry) (p : SemanticParameter) : Decidable (c.Encodes p) :=
  inferInstanceAs (Decidable (p ∈ c.semantics))

/-- The distinct semantic parameters attested across an inventory of classifiers. -/
def collectSemantics (cls : List ClassifierEntry) : List SemanticParameter :=
  (cls.flatMap (·.semantics)).eraseDups

/-! ### Compositional strategies -/

/-- The compositional strategy a framework attributes to classifier constructions. Strategy
assignments to particular languages are made in the study files of the papers that make them
(`Chierchia1998`, `LittleMoroneyRoyer2022`, `Sudo2016`), never in the Fragments. -/
inductive ClassifierStrategy where
  /-- The classifier is a measure function required by the numeral, which takes it as its
  first argument ([krifka-1995b], [bale-coon-2014]); predicts classifier–plural co-occurrence
  and classifiers in counting contexts without a noun. -/
  | forNumeral
  /-- The classifier atomizes the noun denotation so that the numeral can count
  ([chierchia-1998]); predicts classifiers beyond numerals and complementary distribution with
  plural marking. -/
  | forNoun
  /-- Numerals are type-`n` singular terms shifted to predicates by a silent ∪-operator that
  overt classifiers in the lexicon block ([sudo-2016]); predicts classifiers with numerals only
  and no numeral or noun idiosyncrasies. -/
  | sudoBlocking
  deriving DecidableEq, Repr

end NounCategorization
