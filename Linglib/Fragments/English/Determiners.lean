import Linglib.Data.UD.Basic
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Semantics.Quantification.Quantifier
import Linglib.Semantics.Quantification.Lexicon

/-!
# English Determiners
[horn-1972] [barwise-cooper-1981]

English-specific determiner lexicon. Each entry is *marked* like a `Pronoun`
(a decidable record carrying only the morphosyntax synonyms diverge on) and
typed by the standard determiner taxonomy in `Syntax/Category/Determiner/Basic.lean`:

- the genuinely quantificational words (every, some, no, most, few, half, all,
  each, many, both, neither) are `Syntax.Determiner.Quantifier`;
- the definites/indefinites (the, a, an) are `Article`s and the demonstratives
  (this, that, these, those) are `DemonstrativeDeterminer`s.

A determiner's **denotation** is a generalized quantifier supplied externally —
the marked record carries no `GQ`, exactly as `Pronoun` carries no referent.
For the six-word quantity scale the form↦`GQ` map is `QuantityWord.gqDenotation`
(`Semantics/Quantification`); everything a meaning *fixes* (force, monotonicity,
strength, conservativity) is a theorem about that denotation, not a stored field
(see `Studies/BarwiseCooper1981.lean`).

The cross-paper typological labels (B&C Table II strength/monotonicity, K&S
force) are kept as the textbook-consensus `QuantityWord.entry : QuantityWord.Metadata`
metadata table (a small local record over the `Quantification.Lexicon` enums),
consumed by GQT and exceptive studies that need the descriptive classification
rather than the denotation.

## Scope

This file carries descriptive lexical data, its projection to GQ denotations,
and the typological metadata table. Per-paper model parameters (GQT thresholds,
prototype-theory prototypes/spreads) and theory-bridge theorems live elsewhere:

- Compositional GQ denotations (`every_sem`, `both_sem`, `neither_sem`, …):
  `Semantics/Quantification/Quantifier.lean`.
- GQT/PT meaning operators consuming numerical parameters:
  `Studies/VanTielEtAl2021.lean` (`gqtMeaning`, van Tiel's threshold scale-model),
  `Semantics/Probabilistic/PrototypeTheory.lean` (`ptMeaning`).
- Per-paper parameter values: `Studies/VanTielEtAl2021.lean`.
-/

namespace English.Determiners

export Quantification.Lexicon
  (QForce Monotonicity Strength)

/-! ## Quantificational determiners

Marked `Quantifier` records: `form`, the selectional `numberRestriction`
(root `Number`), and `selectsMass`. The meaning leaves these open — *every* and
*all* can share a denotation yet differ in `numberRestriction`. -/

/-- "none" — negative, accepts mass NPs. -/
def none_ : Quantifier := { form := "none", selectsMass := true }

/-- "few" — proportional, plural. -/
def few : Quantifier := { form := "few", numberRestriction := some .plural }

/-- "some" — existential, accepts mass NPs. -/
def some_ : Quantifier := { form := "some", selectsMass := true }

/-- "half" — proportional, accepts mass NPs. -/
def half : Quantifier := { form := "half", selectsMass := true }

/-- "most" — proportional, plural, accepts mass NPs. -/
def most : Quantifier :=
  { form := "most", numberRestriction := some .plural, selectsMass := true }

/-- "all" — universal, plural, accepts mass NPs. -/
def all : Quantifier :=
  { form := "all", numberRestriction := some .plural, selectsMass := true }

/-- "every" — universal, singular. -/
def every : Quantifier := { form := "every", numberRestriction := some .singular }

/-- "each" — universal, distributive, singular. -/
def each : Quantifier := { form := "each", numberRestriction := some .singular }

/-- "many" — proportional, plural. -/
def many : Quantifier := { form := "many", numberRestriction := some .plural }

/-- "both" — universal dual, presupposes exactly 2.
    K&S (83a): [_Det each of the two] ⇒ both. Compositional denotation
    `both_sem` lives in `Quantification.Quantifier`.

    `numberRestriction := some .dual` carries the dual core concept
    ([harbour-2014] `[−atomic, +minimal]`); the cardinality clause `|R| ≥ 2`
    on the denotation side reflects the Harbour `dualPredOnLattice` reading
    ([jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025]). -/
def both : Quantifier := { form := "both", numberRestriction := some .dual }

/-- "neither" — negative dual, presupposes exactly 2.
    K&S (83b): [_Det (not one) of the two] ⇒ neither. Compositional denotation
    `neither_sem` lives in `Quantification.Quantifier`. -/
def neither : Quantifier := { form := "neither", numberRestriction := some .dual }

/-! ## Articles and demonstratives

The definites/indefinites and demonstratives are *not* quantifiers: their
denotation is definiteness, not a generalized quantifier. -/

/-- "the" — definite article, syncretic over both [schwarz-2009] strengths. -/
def the : Article :=
  { form := "the", definiteness := .definite, exponent := .dedicatedMorpheme
  , uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] }

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

/-! ## The Canonical Quantity Scale
[barwise-cooper-1981] [van-tiel-franke-sauerland-2021]

The 6-element ⟨none, few, some, half, most, all⟩ scale used cross-paper
to evaluate quantifier theories — empirical implicature studies
([van-tiel-franke-sauerland-2021]), GQ universals ([barwise-cooper-1981]),
and polarity bridges ([von-fintel-1993]).
-/

/-- The canonical 6-element quantity scale. -/
inductive QuantityWord where
  | none_ | few | some_ | half | most | all
  deriving Repr, DecidableEq, Inhabited

instance : Fintype QuantityWord where
  elems := {.none_, .few, .some_, .half, .most, .all}
  complete := fun x => by cases x <;> simp

/-- B&C Table II typological metadata: the textbook-consensus descriptive
    labels (force, monotonicity, weak/strong strength) a quantity word carries.
    A small local record over the `Quantification.Lexicon` enums — *not* the
    lexical marking (that is `Quantifier`, above) and *not* the denotation
    (that is `QuantityWord.gqDenotation`). -/
structure QuantityWord.Metadata where
  /-- Quantificational force. -/
  qforce : QForce
  /-- Monotonicity (typological label). -/
  monotonicity : Monotonicity := .increasing
  /-- Weak/strong (B&C Table II). -/
  strength : Strength := .weak
  deriving Repr, BEq, DecidableEq

/-- B&C Table II typological metadata for each quantity word: force,
    monotonicity, and weak/strong strength. This is the textbook-consensus
    descriptive classification ([barwise-cooper-1981] Table II,
    [van-de-pol-etal-2023] for *half*), *not* the denotation — the denotation
    is `QuantityWord.gqDenotation`, and the properties this table labels are
    theorems about it (`Studies/BarwiseCooper1981.lean`). Consumed by the GQT
    model ([van-tiel-franke-sauerland-2021]) and the exceptive-licensing bridge
    ([von-fintel-1993]) that want the descriptive label. -/
def QuantityWord.entry : QuantityWord → QuantityWord.Metadata
  | .none_ => { qforce := .negative, monotonicity := .decreasing, strength := .weak }
  | .few   => { qforce := .proportional, monotonicity := .decreasing, strength := .weak }
  | .some_ => { qforce := .existential, monotonicity := .increasing, strength := .weak }
  | .half  => { qforce := .proportional, monotonicity := .nonMonotone, strength := .weak }
  | .most  => { qforce := .proportional, monotonicity := .increasing, strength := .strong }
  | .all   => { qforce := .universal, monotonicity := .increasing, strength := .strong }

/-- Convenience accessor. -/
def QuantityWord.monotonicity (q : QuantityWord) : Monotonicity :=
  q.entry.monotonicity

/-- All quantity words as a list. -/
def QuantityWord.toList : List QuantityWord :=
  [.none_, .few, .some_, .half, .most, .all]

/-- Canonical model-theoretic generalized-quantifier denotation
    (B&C-style), built on `every_sem`/`some_sem`/`no_sem`/etc. from
    `Quantification.Quantifier`. -/
noncomputable def QuantityWord.gqDenotation (q : QuantityWord)
    {α : Type*} [Fintype α] : Quantification.GQ α :=
  open Quantification in
  match q with
  | .none_ => no_sem
  | .some_ => some_sem
  | .all   => every_sem
  | .most  => most_sem
  | .few   => few_sem
  | .half  => half_sem

/-! ## Lexicon Access -/

/-- All quantificational determiner entries (excluding definites). -/
def allQuantifiers : List Quantifier := [
  none_, few, some_, half, most, all, every, each, many, both, neither
]

/-- All article entries. -/
def allArticles : List Article := [the, a, an]

/-- All demonstrative-determiner entries. -/
def allDemonstratives : List DemonstrativeDeterminer := [this, that, these, those]

/-- The full inventory as a heterogeneous `List Determiner.Entry`
    (the per-language form a Fragment declares). -/
def inventory : List Determiner.Entry :=
  allArticles.map .article ++ allDemonstratives.map .demonstrative ++
    allQuantifiers.map .quantifier

end English.Determiners
