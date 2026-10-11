module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Tactic.DeriveFintype

/-!
# The implicational map of indefinite series

An indefinite series (English *some-*, Russian *-nibud'*) is used in some of nine functions,
which Haspelmath arranges on an implicational map: a graph on the functions whose adjacency
requirement says that the functions a series covers form a connected region. The map is
`implicationalMap`, and a region `s` meets the requirement when
`(implicationalMap.induce ↑s).Connected`, so the book's requirement is a statement of graph
theory. A series is further described by the ontological category it belongs to (person, thing,
place, …) and the morphological basis it is built from (an interrogative, a generic noun, a
dedicated marker or an existential construction); the carrier bundling these with a form is
`IndefinitePronoun` in `Syntax/Category/Pronoun/Indefinite.lean`.

## Main declarations

* `Indefinite.HaspelmathFunction`: the nine functions, with the book's numbering `number` and the
  neighbours `adjacent` of each on the map.
* `Indefinite.implicationalMap`: the map as a `SimpleGraph`.
* `Indefinite.SpecificityFunction`: the specific known, specific unknown and non-specific
  functions, with their embedding `toFunction` in the map and the ones a region covers,
  `specificityFunctions`.
* `Indefinite.OntologicalCategory`, `Indefinite.MorphologicalBasis`: the two further dimensions
  of a series.

## Implementation notes

The empty region is not connected, as `SimpleGraph.Connected` requires a vertex; a series covers
at least one function. The book counts the possible regions of the map differently from the
graph encoded here; see the TODO of `Studies/Haspelmath1997.lean`.

## References

* [haspelmath-1997]
* [wals-2013]
-/

@[expose] public section

namespace Indefinite

/-! ### The functions and the map -/

/-- The nine functions of [haspelmath-1997]'s implicational map. -/
inductive HaspelmathFunction where
  /-- In the specific known function the speaker has a referent in mind. -/
  | specificKnown
  /-- In the specific unknown function the speaker presupposes a referent but cannot identify
  it. -/
  | specificUnknown
  /-- In the irrealis non-specific function no specific referent is intended. -/
  | irrealis
  /-- The indefinite stands in a question. -/
  | question
  /-- The indefinite stands in the protasis of a conditional. -/
  | conditional
  /-- The indefinite stands in the standard of a comparative. -/
  | comparative
  /-- Indirect negation is superordinate or implicit negation (*without*, *doubt*, *deny*). -/
  | indirectNeg
  /-- Direct negation is clause-mate negation. -/
  | directNeg
  /-- The indefinite is a free-choice item. -/
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

/-- `adjacent f` lists the neighbours of `f` on the map. The map is a chain from specific known
through specific unknown to irrealis, which feeds two parallel tracks, question to indirect
negation to direct negation and conditional to comparative to free choice, the tracks joined at
question and conditional and at indirect negation and comparative.

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

/-- The implicational map is the graph on the functions with the edges of
`HaspelmathFunction.adjacent`. -/
def implicationalMap : SimpleGraph HaspelmathFunction where
  Adj f g := g ∈ f.adjacent
  symm.symm := by decide
  loopless.irrefl := by decide

instance : DecidableRel implicationalMap.Adj :=
  fun f g ↦ inferInstanceAs (Decidable (g ∈ f.adjacent))

@[simp]
theorem implicationalMap_adj {f g : HaspelmathFunction} :
    implicationalMap.Adj f g ↔ g ∈ f.adjacent :=
  Iff.rfl

/-! ### The specificity functions -/

/-- The three functions at the specific end of the map, which differ in whether the indefinite
has a specific referent and in whether the speaker can identify it. -/
inductive SpecificityFunction where
  | specificKnown
  | specificUnknown
  | nonSpecific
  deriving DecidableEq, Fintype, Repr

/-- `toFunction` embeds the specificity functions in the map, the non-specific function as the
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

/-! ### Ontological category and morphological basis -/

/-- The ontological categories of a series. Person, thing, property, place, time, manner and
amount are the seven the book finds expressed by simple means in most languages, the cut
between person and thing (*somebody* against *something*) being made nearly everywhere; the
category fixes the word class of the member, a pronoun for person and thing and a pro-adverb
for place, time and manner. Determiners (*some* N) and reasons (*for some reason*) are common but
not universal, English and German having no *somewhy*. -/
inductive OntologicalCategory where
  /-- Person is the category of *somebody*, *someone* and interrogative *who*. -/
  | person
  /-- Thing is the category of *something* and interrogative *what*. -/
  | thing
  /-- Property or kind is the category of *some kind of* and interrogative *what kind*. -/
  | property
  /-- Place is the category of *somewhere* and interrogative *where*. -/
  | place
  /-- Time is the category of *sometime* and interrogative *when*. -/
  | time
  /-- Manner is the category of *somehow* and interrogative *how*. -/
  | manner
  /-- Amount is the category of *some amount* and interrogative *how much*. -/
  | amount
  /-- Determiner is the category of *some* N and interrogative *which*. -/
  | determiner
  /-- Reason is the category of *for some reason* and interrogative *why*. -/
  | reason
  deriving DecidableEq, Repr

/-- A series is built in one of four ways, from an interrogative pronoun (Russian *kto-nibud'*),
from a generic noun (English *somebody*), with a dedicated indefinite marker (German *irgend-*),
or by an existential construction. These are the four single-basis cells of chapter 46 of
[wals-2013]; its fifth cell, mixed, describes a paradigm using several bases. -/
inductive MorphologicalBasis where
  /-- The series is built from an interrogative pronoun. -/
  | interrogative
  /-- The series is built from a generic noun for person, thing or place. -/
  | genericNoun
  /-- The series is built with a dedicated indefinite marker. -/
  | special
  /-- The series is an existential construction. -/
  | existentialConstruction
  deriving DecidableEq, Repr

end Indefinite
