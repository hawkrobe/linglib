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

def that : CompEntry :=
  { form := "that", position := some .detached,
    noonanType := some .indicative, clauseForm := some .declarative,
    optional := true }

def if_ : CompEntry :=
  { form := "if", position := some .detached,
    clauseForm := some .embeddedQuestion, conditional := true }

def whether : CompEntry :=
  { form := "whether", position := some .detached,
    clauseForm := some .embeddedQuestion }

/-- The complementizer inventory (adverbial subordinators excluded). -/
def allComplementizers : List CompEntry := [that, if_, whether]

/-! ### Adverbial subordinators

Not complementizers ([noonan-2007] excludes adverbial subordination);
recorded as plain subordinating-conjunction words. -/

def because : Word := { form := "because", cat := .SCONJ }
def although : Word := { form := "although", cat := .SCONJ }
def while_ : Word := { form := "while", cat := .SCONJ }

end English.Complementizers
