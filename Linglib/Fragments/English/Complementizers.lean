import Linglib.Syntax.Category.Complementizer.Basic

open Morphology (Word)

/-!
# English Complementizers Lexicon Fragment

Lexical entries for the English complementizers *that*, *if*, *whether*,
as root `Complementizer` entries extended with the English-specific
flags (`conditional`, `optional`). *if* is split between conditional and
embedded-question uses; the single entry carries both.

The adverbial subordinators *because*, *although*, *while* are not
complementizers (adverbial subordination is outside complementation,
[noonan-2007]); they are plain `SCONJ` words below. The morphologically
distinct preposition *to* and the infinitival particle *to* live in
`Auxiliaries.lean` and `FunctionWords.lean` respectively.
-/

namespace English.Complementizers


/-- An English complementizer entry: the root schema plus the
English-specific flags. -/
structure CompEntry extends Complementizer where
  /-- Introduces a conditional protasis (*if*)? -/
  conditional : Bool := false
  /-- Can be omitted (that-drop)? -/
  optional : Bool := false
  deriving Repr, BEq, DecidableEq

/-- *that* — declarative complementizer, omissible (that-drop). -/
def that : CompEntry :=
  { morphs := [.free "that"],
    coding := some .indicative, force := some .declarative,
    optional := true }

/-- *if* — conditional protasis marker and embedded polar-question
complementizer. -/
def if_ : CompEntry :=
  { morphs := [.free "if"],
    force := some .interrogative, conditional := true }

/-- *whether* — embedded polar-question complementizer. -/
def whether : CompEntry :=
  { morphs := [.free "whether"],
    force := some .interrogative }

/-- The complementizer inventory (adverbial subordinators excluded). -/
def allComplementizers : List CompEntry := [that, if_, whether]

/-! ### Adverbial subordinators

Not complementizers ([noonan-2007] excludes adverbial subordination);
recorded as plain subordinating-conjunction words. -/

def because : Word := { form := "because", cat := .SCONJ }
def although : Word := { form := "although", cat := .SCONJ }
def while_ : Word := { form := "while", cat := .SCONJ }

end English.Complementizers
