module

public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# English complementizers

English has three complementizers: *that*, which introduces a declarative complement in the
indicative and is omissible under most verbs, and *if* and *whether*, which introduce an
embedded polar question, *if* also introducing a conditional protasis. The adverbial
subordinators *because*, *although* and *while* are not complementizers, adverbial
subordination lying outside complementation in Noonan's sense, and are recorded as
subordinating conjunctions. The preposition *to* is `English.Adpositions.to_` and the
infinitival particle *to* is `English.Auxiliaries.toInf`.

## Main definitions

* `English.Complementizers.that`, `English.Complementizers.if_`,
  `English.Complementizers.whether`, `English.Complementizers.complementizers`: the
  complementizers.
* `English.Complementizers.because`, `English.Complementizers.although`,
  `English.Complementizers.while_`: the adverbial subordinators.

## References

* [noonan-2007]
-/

@[expose] public section

open Morphology (Word)

namespace English.Complementizers

/-- *that*, the declarative complementizer, omissible under most verbs. -/
def that : Complementizer where
  morphs := [.free "that"]
  coding := some .indicative
  types := .only .declarative

/-- *if*, the embedded polar-question complementizer, also the conditional subordinator. -/
def if_ : Complementizer where
  morphs := [.free "if"]
  types := .only .polar

/-- *whether*, the embedded polar-question complementizer. -/
def whether : Complementizer where
  morphs := [.free "whether"]
  types := .only .polar

/-- The complementizers. -/
def complementizers : List Complementizer := [that, if_, whether]

/-! ### Adverbial subordinators -/

/-- *because*, a subordinating conjunction. -/
def because : Word := { form := "because", cat := .SCONJ }

/-- *although*, a subordinating conjunction. -/
def although : Word := { form := "although", cat := .SCONJ }

/-- *while*, a subordinating conjunction. -/
def while_ : Word := { form := "while", cat := .SCONJ }

end English.Complementizers
