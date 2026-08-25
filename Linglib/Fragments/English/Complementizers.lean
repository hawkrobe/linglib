import Linglib.Syntax.Category.Complementizer.Basic

open Morphology (Word)

/-!
# English Complementizers Lexicon Fragment

The English complementizers *that*, *if*, *whether* as `Complementizer`
entries; *if* doubles as the conditional subordinator and *that* drops
under most verbs.

The adverbial subordinators *because*, *although*, *while* are not
complementizers (adverbial subordination is outside complementation,
[noonan-2007]); they are plain `SCONJ` words below. The morphologically
distinct preposition *to* and the infinitival particle *to* live in
`Auxiliaries.lean` and `FunctionWords.lean` respectively.
-/

namespace English.Complementizers

/-- *that* — declarative complementizer; omissible under most verbs
(that-drop). -/
def that : Complementizer where
  morphs := [.free "that"]
  coding := some .indicative
  force := some .declarative

/-- *if* — embedded polar-question complementizer; the same word
introduces conditional protases. -/
def if_ : Complementizer where
  morphs := [.free "if"]
  force := some .interrogative

/-- *whether* — embedded polar-question complementizer. -/
def whether : Complementizer where
  morphs := [.free "whether"]
  force := some .interrogative

/-- The complementizer inventory (adverbial subordinators excluded). -/
def complementizers : List Complementizer := [that, if_, whether]

/-! ### Adverbial subordinators

Not complementizers ([noonan-2007] excludes adverbial subordination);
recorded as plain subordinating-conjunction words. -/

def because : Word := { form := "because", cat := .SCONJ }
def although : Word := { form := "although", cat := .SCONJ }
def while_ : Word := { form := "while", cat := .SCONJ }

end English.Complementizers
