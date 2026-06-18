import Linglib.Semantics.Tense.Basic

/-!
# Hungarian Temporal Deictic Adverbs
[zhao-2025] [tsilia-zhao-2026]

Lexical entries for Hungarian temporal-deictic adverbs.

## *akkor* 'then'

*akkor* is the Hungarian member of the cross-linguistic "*then*-present
incompatibility" inventory ([zhao-2025], [tsilia-zhao-2026]): a
perspective-shifting temporal deictic (like English *then*, German *damals*)
anchored to a perspective time P ≠ S, so it is incompatible with a deictic
present.
-/

namespace Hungarian.TemporalDeictic

open Tense

/-- Hungarian *akkor* 'then' — perspective-shifting temporal deictic.
    Part of the cross-linguistic "then"-present incompatibility
    inventory ([zhao-2025], [tsilia-zhao-2026]). -/
def akkor : ThenAdverb where
  language := "Hungarian"
  form := "akkor"
  gloss := "then"
  shiftsPerspective := true

/-- Hungarian *akkor* 'then' shifts perspective, like all cross-linguistic
    "then" adverbs. -/
theorem akkor_shifts :
    akkor.shiftsPerspective = true := rfl


end Hungarian.TemporalDeictic
