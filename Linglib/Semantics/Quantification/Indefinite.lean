module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Polarity.LicensingContext

/-!
# The implicational map of indefinite series

An indefinite series (English *some-*, Russian *-nibud'*) is used in some of nine functions,
which [haspelmath-1997] arranges on an implicational map: a graph on the functions whose
adjacency requirement says that the functions a series covers form a connected region. The map
is `implicationalMap` and a region's connectedness is `Contiguous`, the connectedness of the
induced subgraph, so the book's requirement is a statement of graph theory. A series is further
described by the ontological category it belongs to (person, thing, place, …) and the
morphological basis it is built from (an interrogative, a generic noun, a dedicated marker or an
existential construction); the carrier bundling these with a form is `IndefinitePronoun` in
`Syntax/Category/Pronoun/Indefinite.lean`.

## Main declarations

* `Indefinite.HaspelmathFunction`: the nine functions, with the book's numbering `number` and the
  neighbours `adjacent` of each on the map.
* `Indefinite.implicationalMap`: the map as a `SimpleGraph`.
* `Indefinite.Contiguous`: a region of the map induces a connected subgraph; decidable.
* `Indefinite.SpecificityFunction`: the specific known, specific unknown and non-specific
  functions, with their embedding `toFunction` in the map and the ones a region covers,
  `specificityFunctions`.
* `Indefinite.npiRegion`: the functions of the map in which negative polarity items occur.
* `Polarity.LicensingContext.haspelmathFunction`: the function a licensing environment realizes.
* `Indefinite.OntologicalCategory`, `Indefinite.MorphologicalBasis`: the two further dimensions
  of a series.

## Implementation notes

The empty region is not contiguous, as `SimpleGraph.Connected` requires a vertex; a series
covers at least one function. The book counts the possible regions of the map differently from
the graph encoded here; see the TODO of `Studies/Haspelmath1997.lean`.

## References

* [haspelmath-1997]
* [hoeksema-1983]
* [wals-2013]
-/

@[expose] public section

namespace Indefinite

/-! ### The functions and the map -/

/-- The nine functions of [haspelmath-1997]'s implicational map. -/
inductive HaspelmathFunction where
  /-- Specific known: the speaker has a referent in mind. -/
  | specificKnown
  /-- Specific unknown: the speaker presupposes a referent but cannot identify it. -/
  | specificUnknown
  /-- Irrealis non-specific: no specific referent is intended. -/
  | irrealis
  /-- Questions. -/
  | question
  /-- The protasis of a conditional. -/
  | conditional
  /-- The standard of a comparative. -/
  | comparative
  /-- Indirect negation: superordinate or implicit negation (*without*, *doubt*, *deny*). -/
  | indirectNeg
  /-- Direct, clause-mate negation. -/
  | directNeg
  /-- Free choice. -/
  | freeChoice
  deriving DecidableEq, Fintype, Repr

namespace HaspelmathFunction

/-- The book's numbering of the functions, in which it states the distribution of a series. -/
def number : HaspelmathFunction → ℕ
  | .specificKnown => 1
  | .specificUnknown => 2
  | .irrealis => 3
  | .question => 4
  | .conditional => 5
  | .indirectNeg => 6
  | .directNeg => 7
  | .comparative => 8
  | .freeChoice => 9

/-- The neighbours of a function on the map: a chain from specific known through specific
unknown to irrealis, which feeds two parallel tracks, question to indirect negation to direct
negation and conditional to comparative to free choice, the tracks joined at question and
conditional and at indirect negation and comparative.

```
                      (4) question —— (6) indirect neg —— (7) direct neg
                           |                |
(1) SK — (2) SU — (3) irr <
                           |                |
                      (5) conditional — (8) comparative — (9) free choice
```
-/
def adjacent : HaspelmathFunction → List HaspelmathFunction
  | .specificKnown   => [.specificUnknown]
  | .specificUnknown => [.specificKnown, .irrealis]
  | .irrealis        => [.specificUnknown, .question, .conditional]
  | .question        => [.irrealis, .conditional, .indirectNeg]
  | .conditional     => [.irrealis, .question, .comparative]
  | .indirectNeg     => [.question, .directNeg, .comparative]
  | .directNeg       => [.indirectNeg]
  | .comparative     => [.conditional, .indirectNeg, .freeChoice]
  | .freeChoice      => [.comparative]

end HaspelmathFunction

/-- The implicational map: the graph on the functions with the edges of
`HaspelmathFunction.adjacent`. -/
def implicationalMap : SimpleGraph HaspelmathFunction where
  Adj f g := g ∈ f.adjacent
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel implicationalMap.Adj :=
  fun f g ↦ inferInstanceAs (Decidable (g ∈ f.adjacent))

/-- A region of the map is **contiguous** when it induces a connected subgraph: the adjacency
requirement on the functions a series covers. -/
def Contiguous (s : Finset HaspelmathFunction) : Prop :=
  (implicationalMap.induce (s : Set HaspelmathFunction)).Connected

instance (s : Finset HaspelmathFunction) : Decidable (Contiguous s) :=
  inferInstanceAs (Decidable (implicationalMap.induce (s : Set HaspelmathFunction)).Connected)

/-! ### The specificity functions -/

/-- The three functions at the specific end of the map, which differ in whether the indefinite
has a specific referent and in whether the speaker can identify it. -/
inductive SpecificityFunction where
  | specificKnown
  | specificUnknown
  | nonSpecific
  deriving DecidableEq, Fintype, Repr

/-- The function of the map a specificity function is: the non-specific function is the
irrealis one. -/
def SpecificityFunction.toFunction : SpecificityFunction → HaspelmathFunction
  | .specificKnown => .specificKnown
  | .specificUnknown => .specificUnknown
  | .nonSpecific => .irrealis

theorem SpecificityFunction.toFunction_injective : Function.Injective toFunction := by decide

/-- The specificity functions a region of the map covers. -/
def specificityFunctions (s : Finset HaspelmathFunction) : Finset SpecificityFunction :=
  Finset.univ.filter (·.toFunction ∈ s)

@[simp]
theorem mem_specificityFunctions {s : Finset HaspelmathFunction} {u : SpecificityFunction} :
    u ∈ specificityFunctions s ↔ u.toFunction ∈ s := by
  simp [specificityFunctions]

/-- The region of the map in which negative polarity items occur: questions, conditionals and
the two negations. -/
def npiRegion : Finset HaspelmathFunction :=
  {.question, .conditional, .indirectNeg, .directNeg}

/-- The function a licensing environment realizes, for the polarity-relevant reading of an
indefinite in it, and `none` for an environment outside the map's inventory: the rows of the
Ladusaw tradition (*few*, *at most*, superlatives, focus *only*, *too … to*, the restrictor of a
universal, temporal *since*), and *nobody*, *before*-clauses and adversatives, whose placement
between direct and indirect negation the book does not settle. The modal, imperative, generic
and free-relative rows realize free choice, their polarity-relevant use, although the same
environments host plain irrealis uses of other indefinites; both comparatives realize the
standard of comparison, although the phrasal comparative licenses no polarity item
([hoeksema-1983]). -/
def _root_.Polarity.LicensingContext.haspelmathFunction :
    Polarity.LicensingContext → Option HaspelmathFunction
  | .negation => some .directNeg
  | .withoutClause | .doubtVerb | .denyVerb => some .indirectNeg
  | .question => some .question
  | .conditionalAntecedent => some .conditional
  | .clausalComparative | .phrasalComparative => some .comparative
  | .modalPossibility | .modalNecessity | .imperative | .generic
  | .freeRelative => some .freeChoice
  | _ => none

/-! ### Ontological category and morphological basis -/

/-- The ontological categories of a series. Person, thing, property, place, time, manner and
amount are the seven the book finds expressed by simple means in most languages, the cut
between person and thing (*somebody* against *something*) being made nearly everywhere; the
category fixes the word class of the member, a pronoun for person and thing and a pro-adverb
for place, time and manner. Determiners (*some* N) and reasons (*for some reason*) are common but
not universal: English and German have no *somewhy*. -/
inductive OntologicalCategory where
  /-- Person: *somebody*, *someone*, interrogative *who*. -/
  | person
  /-- Thing: *something*, interrogative *what*. -/
  | thing
  /-- Property or kind: *some kind of*, interrogative *what kind*. -/
  | property
  /-- Place: *somewhere*, interrogative *where*. -/
  | place
  /-- Time: *sometime*, interrogative *when*. -/
  | time
  /-- Manner: *somehow*, interrogative *how*. -/
  | manner
  /-- Amount: *some amount*, interrogative *how much*. -/
  | amount
  /-- Determiner: *some* N, interrogative *which*. -/
  | determiner
  /-- Reason: *for some reason*, interrogative *why*. -/
  | reason
  deriving DecidableEq, Repr

/-- The four ways a series is built: from an interrogative pronoun (Russian *kto-nibud'*), from
a generic noun (English *somebody*), with a dedicated indefinite marker (German *irgend-*), or
by an existential construction. These are the four single-basis cells of chapter 46 of
[wals-2013]; its fifth cell, mixed, describes a paradigm using several bases. -/
inductive MorphologicalBasis where
  /-- Built from an interrogative pronoun. -/
  | interrogative
  /-- Built from a generic noun for person, thing or place. -/
  | genericNoun
  /-- Built with a dedicated indefinite marker. -/
  | special
  /-- An existential construction. -/
  | existentialConstruction
  deriving DecidableEq, Repr

end Indefinite
