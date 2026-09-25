module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.NP
public import Linglib.Semantics.Quantification.Lexicon
public import Linglib.Semantics.Denotation

/-!
# English determiners

This file records the English determiner lexicon. The quantificational determiners are the
carrier `QuantityWord`. A word projects to its `Quantifier` record by
`QuantityWord.toQuantifier`, which carries only what the readings leave open, the selected
number and whether mass nouns are selected, and denotes the set of readings the literature makes
available for it through the `Denotes` instance, each a `Quantifier.GQ.Family`. A word with one
consensus reading denotes a singleton, so `⟦QuantityWord.all⟧` is `{every}`, and *many*,
whose standard [barwise-cooper-1981] leave to context, denotes `∅` until the theory hub has a
reading for it. A study takes a stand by membership, and everything a reading fixes, force,
monotonicity, strength and conservativity, is a theorem about the member chosen
(`Studies/BarwiseCooper1981.lean`). The textbook labels of [barwise-cooper-1981]'s Table II are
the metadata `QuantityWord.entry` for the studies that want the descriptive classification. The
articles, demonstratives and possessives are the other determiner kinds, and the numerical
determiners of [van-de-pol-etal-2023] are parameterized by their threshold.

## Main declarations

* `QuantityWord` is the carrier of the quantificational determiners, with the six-word scale
  `QuantityWord.scale` of [van-tiel-franke-sauerland-2021] inside it;
  `QuantityWord.form`, `QuantityWord.numberRestriction` and `QuantityWord.selectsMass` are its
  lexical data and `QuantityWord.toQuantifier` its record.
* The `Denotes` instance gives each word its available readings from
  `Quantification/Basic.lean` and `Quantification/Counting.lean`.
* `QuantityWord.entry` is the [barwise-cooper-1981] Table II classification.
* `inventory` is the English determiner inventory, and `marking` derives its [moroney-2021]
  cell.

## References

* [barwise-cooper-1981]
* [horn-1972]
* [van-de-pol-etal-2023]
* [van-tiel-franke-sauerland-2021]
* [von-fintel-1993]
* [harbour-2014]
* [jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]
* [schwarz-2009]
* [moroney-2021]
-/

@[expose] public section

namespace English.Determiners

export Quantifier.Lexicon
  (QForce Monotonicity Strength)

/-! ## Quantificational determiners -/

/-- The quantificational determiners of English: the six-word quantity scale *none*, *few*,
*some*, *half*, *most* and *all*, and *every*, *each*, *many*, *both* and *neither*. -/
inductive QuantityWord where
  | none_ | few | some_ | half | most | all | every | each | many | both | neither
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The surface form. -/
def form : QuantityWord → String
  | .none_ => "none"
  | .few => "few"
  | .some_ => "some"
  | .half => "half"
  | .most => "most"
  | .all => "all"
  | .every => "every"
  | .each => "each"
  | .many => "many"
  | .both => "both"
  | .neither => "neither"

/-- The grammatical number a word selects, which the denotation leaves open: *every* and *all*
share a denotation and differ here. *Both* and *neither* select the dual, the core concept
`[−atomic, +minimal]` of [harbour-2014], whose cardinality clause the denotation reflects
([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]). -/
def numberRestriction : QuantityWord → Option Number
  | .few | .most | .all | .many => some .plural
  | .every | .each => some .singular
  | .both | .neither => some .dual
  | .none_ | .some_ | .half => none

/-- Whether a word selects mass nouns, which the denotation likewise leaves open. -/
def selectsMass : QuantityWord → Bool
  | .none_ | .some_ | .half | .most | .all => true
  | .few | .every | .each | .many | .both | .neither => false

/-- The word as a determiner record. -/
def toQuantifier (w : QuantityWord) : Quantifier :=
  { form := w.form, numberRestriction := w.numberRestriction, selectsMass := w.selectsMass }

/-- The six-word quantity scale of [van-tiel-franke-sauerland-2021], the cross-paper scale on
which quantifier theories are evaluated ([barwise-cooper-1981], [von-fintel-1993]). -/
def scale : List QuantityWord := [.none_, .few, .some_, .half, .most, .all]

/-- All the words. -/
def toList : List QuantityWord :=
  [.none_, .few, .some_, .half, .most, .all, .every, .each, .many, .both, .neither]

theorem mem_toList (w : QuantityWord) : w ∈ toList := by cases w <;> decide

/-! ### The available readings -/

universe u

/-- The readings the literature makes available for a word, as generalized quantifiers on every
finite domain. *None* reads as `no`, *some* as `Quantifier.GQ.some`, *all*, *every* and *each* as
`every`, *most* as `most`, *few* as `few`, *half* as `half`, *both* as
`both` and *neither* as `neither`; *many* has no reading, since
[barwise-cooper-1981] leave its standard to context. -/
noncomputable instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .none_ => {Quantifier.GQ.Family.no}
    | .some_ => {Quantifier.GQ.Family.some}
    | .all | .every | .each => {Quantifier.GQ.Family.every}
    | .most => {Quantifier.GQ.Family.most}
    | .few => {Quantifier.GQ.Family.few}
    | .half => {Quantifier.GQ.Family.half}
    | .both => {Quantifier.GQ.Family.both}
    | .neither => {Quantifier.GQ.Family.neither}
    | .many => ∅

/-! ### The Table II classification -/

/-- The textbook labels a word carries, its force, its monotonicity and its weak or strong
strength, which are not the denotation but the descriptive classification the GQT model
([van-tiel-franke-sauerland-2021]) and the exceptive-licensing bridge ([von-fintel-1993])
consume. -/
structure Metadata where
  /-- The quantificational force. -/
  qforce : QForce
  /-- The monotonicity. -/
  monotonicity : Monotonicity := .increasing
  /-- The weak or strong strength. -/
  strength : Strength := .weak
  deriving Repr, DecidableEq

/-- The [barwise-cooper-1981] Table II classification of each word, with *half* after
[van-de-pol-etal-2023]. -/
def entry : QuantityWord → Metadata
  | .none_ => { qforce := .negative, monotonicity := .decreasing }
  | .few => { qforce := .proportional, monotonicity := .decreasing }
  | .some_ => { qforce := .existential }
  | .half => { qforce := .proportional, monotonicity := .nonMonotone }
  | .most => { qforce := .proportional, strength := .strong }
  | .all | .every | .each => { qforce := .universal, strength := .strong }
  | .many => { qforce := .proportional }
  | .both => { qforce := .universal, strength := .strong }
  | .neither => { qforce := .negative, monotonicity := .decreasing, strength := .strong }

end QuantityWord

/-! ## Articles and demonstratives

The definites/indefinites and demonstratives are *not* quantifiers: their
denotation is definiteness, not a generalized quantifier. -/

/-- "the" — definite article, syncretic over both [schwarz-2009] strengths. -/
def the : Article :=
  { form := "the", definiteness := .definite, exponent := .dedicatedMorpheme
  , uses := {.immediateSituation, .largerSituation, .anaphoric, .donkey} }

/-- "a" — indefinite article, singular. -/
def a : Article :=
  { form := "a", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- "an" — indefinite article, singular (phonological allomorph of *a*). -/
def an : Article :=
  { form := "an", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- "this" — proximal demonstrative determiner, singular. -/
def this : DemonstrativeDeterminer := { form := "this", deictic := .proximal }

/-- "that" — distal demonstrative determiner, singular. -/
def that : DemonstrativeDeterminer := { form := "that", deictic := .distal }

/-- "these" — proximal demonstrative determiner, plural. -/
def these : DemonstrativeDeterminer := { form := "these", deictic := .proximal }

/-- "those" — distal demonstrative determiner, plural. -/
def those : DemonstrativeDeterminer := { form := "those", deictic := .distal }

/-- "my" — first-person possessive determiner. -/
def my : PossessiveDeterminer := { form := "my" }

/-- "your" — second-person possessive determiner. -/
def your : PossessiveDeterminer := { form := "your" }

/-! ## Numerical Determiners
[barwise-cooper-1981] [van-de-pol-etal-2023]

Parameterized by a numerical threshold `n`. These are the class of
determiners [van-de-pol-etal-2023] show satisfy all three semantic
universals (and have low MDL).
-/

/-- Numerical determiner entry. -/
structure NumericalDetEntry where
  form : String
  qforce : QForce
  monotonicity : Monotonicity
  /-- The numerical threshold -/
  threshold : Nat
  deriving Repr, BEq

/-- "at least n" — upward monotone in scope, conservative, quantity -/
def atLeast (n : Nat) : NumericalDetEntry :=
  { form := s!"at least {n}", qforce := .proportional
  , monotonicity := .increasing, threshold := n }

/-- "at most n" — downward monotone in scope, conservative, quantity -/
def atMost (n : Nat) : NumericalDetEntry :=
  { form := s!"at most {n}", qforce := .proportional
  , monotonicity := .decreasing, threshold := n }

/-- "exactly n" — non-monotone (neither UE nor DE), conservative, quantity -/
def exactlyN (n : Nat) : NumericalDetEntry :=
  { form := s!"exactly {n}", qforce := .proportional
  , monotonicity := .nonMonotone, threshold := n }

/-- "more than n" — upward monotone, conservative, quantity -/
def moreThan (n : Nat) : NumericalDetEntry :=
  { form := s!"more than {n}", qforce := .proportional
  , monotonicity := .increasing, threshold := n }

/-- "fewer than n" — downward monotone, conservative, quantity -/
def fewerThan (n : Nat) : NumericalDetEntry :=
  { form := s!"fewer than {n}", qforce := .proportional
  , monotonicity := .decreasing, threshold := n }

/-! ## Lexicon Access -/

/-- All quantificational determiner entries. -/
def allQuantifiers : List Quantifier := QuantityWord.toList.map QuantityWord.toQuantifier

/-- All article entries. -/
def allArticles : List Article := [the, a, an]

/-- All demonstrative-determiner entries. -/
def allDemonstratives : List DemonstrativeDeterminer := [this, that, these, those]

/-- All possessive-determiner entries. -/
def allPossessives : List PossessiveDeterminer := [my, your]

/-- The full inventory as a heterogeneous `Determiner.Inventory`
    (the per-language form a Fragment declares). -/
def inventory : Determiner.Inventory :=
  allArticles.map .article ++ allDemonstratives.map .demonstrative ++
    allQuantifiers.map .quantifier ++ allPossessives.map .possessive

/-- English's inventory derives the `.generallyMarked` [moroney-2021] cell: the
    syncretic *the* covers both [schwarz-2009] use types. -/
theorem marking : inventory.markingStrategy = .generallyMarked := by decide

end English.Determiners
