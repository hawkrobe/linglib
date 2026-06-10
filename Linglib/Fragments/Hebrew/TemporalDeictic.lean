import Linglib.Semantics.Tense.Basic

/-!
# Hebrew Temporal Deictic Adverbs
[tsilia-zhao-2026]

Lexical entry for Hebrew אז "az" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility.

-/

namespace Hebrew.TemporalDeictic

open Tense

/-- Hebrew אז "az" -/
def az : ThenAdverb where
  language := "Hebrew"
  form := "אז"
  gloss := "then"
  shiftsPerspective := true

end Hebrew.TemporalDeictic
