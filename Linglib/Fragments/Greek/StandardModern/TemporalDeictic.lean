import Linglib.Semantics.Tense.Basic

/-!
# Greek Temporal Deictic Adverbs
[tsilia-zhao-2026]

Lexical entry for Greek τότε "tóte" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility.

-/

namespace Greek.StandardModern.TemporalDeictic

open Tense

/-- Greek τότε "tóte" -/
def tote : ThenAdverb where
  language := "Greek"
  form := "τότε"
  gloss := "then"
  shiftsPerspective := true

end Greek.StandardModern.TemporalDeictic
