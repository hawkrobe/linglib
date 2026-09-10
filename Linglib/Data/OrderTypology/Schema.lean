import Mathlib.Tactic.DeriveFintype

/-!
# Basic order typology samples: schema

Typed schema for the language samples of the basic order typology: a paper's classification of
each language of its sample by dominant clause order, adposition type, and the orders of a noun
with its genitive, adjective, demonstrative, and numeral, together with the further properties
the paper records per language, and its table of order types with the languages attesting each.
Generated rows live in `Data/OrderTypology/<Paper>.lean`, emitted from the canonical
`<Paper>.json` by `scripts/gen_order_typology.py`.

This is data: it imports nothing from `Linglib/` and states no theorems. A property the paper
does not record for a language is `none`.

## References

* [greenberg-1963]
-/

namespace Data.OrderTypology

/-- The dominant order of verb, nominal subject, and nominal object, by the verb's position:
verb-subject-object, subject-verb-object, subject-object-verb. -/
inductive VerbPosition where
  | initial
  | medial
  | final
  deriving DecidableEq, Repr, Fintype

/-- Prepositions or postpositions. -/
inductive Adposition where
  | prepositions
  | postpositions
  deriving DecidableEq, Repr, Fintype

/-- The order of a noun and one of its dependents: the noun first, the dependent first, or both
orders found. -/
inductive NounOrder where
  | nounFirst
  | dependentFirst
  | both
  deriving DecidableEq, Repr, Fintype

/-- The place of an element fixed by reference to the sentence as a whole. -/
inductive SentencePlace where
  | initial
  | final
  deriving DecidableEq, Repr, Fintype

/-- The place of an element fixed by reference to a particular word. -/
inductive Placement where
  | precedes
  | follows
  deriving DecidableEq, Repr, Fintype

/-- The order of an adverb and the adjective it modifies. -/
inductive AdverbOrder where
  | adverbAdjective
  | adjectiveAdverb
  | both
  deriving DecidableEq, Repr, Fintype

/-- The order of adjective, marker, and standard in a comparison of superiority. -/
inductive ComparisonOrder where
  | adjectiveMarkerStandard
  | standardMarkerAdjective
  | both
  deriving DecidableEq, Repr, Fintype

/-- The order of a common noun and a proper noun in apposition. -/
inductive Apposition where
  | commonProper
  | properCommon
  deriving DecidableEq, Repr, Fintype

/-- A language whose affixes are all suffixes, or all prefixes. -/
inductive Affixing where
  | suffixingOnly
  | prefixingOnly
  deriving DecidableEq, Repr, Fintype

/-- One language of the sample. -/
structure SampleRow where
  /-- The language name as the paper prints it. -/
  language : String
  verbPosition : VerbPosition
  adposition : Adposition
  /-- The governing noun and its dependent genitive. -/
  genitive : NounOrder
  /-- The noun and its qualifying adjective. -/
  adjective : NounOrder
  demonstrative : NounOrder
  numeral : NounOrder
  /-- The verb follows all its modifiers, with at most object-subject-verb as an alternative
  order. -/
  rigidVerbFinal : Bool
  /-- A yes-no question particle or affix placed by reference to the sentence. -/
  questionParticleSentence : Option SentencePlace
  /-- A yes-no question particle or affix placed by reference to a word. -/
  questionParticleWord : Option Placement
  /-- Interrogative words or phrases come first. -/
  questionWordFirst : Bool
  /-- An inflected auxiliary relative to the main verb. -/
  auxiliary : Option Placement
  adverbAdjective : Option AdverbOrder
  comparison : Option ComparisonOrder
  apposition : Option Apposition
  /-- The nominal antecedent and its relative expression. -/
  relative : Option NounOrder
  affixing : Option Affixing
  deriving DecidableEq, Repr

/-- One of the paper's order types, with the languages the paper lists as attesting it. -/
structure OrderType where
  /-- The paper's number for the type. -/
  index : Nat
  verbPosition : VerbPosition
  adposition : Adposition
  genitive : NounOrder
  adjective : NounOrder
  attested : List String
  deriving DecidableEq, Repr

end Data.OrderTypology
