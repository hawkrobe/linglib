import Linglib.Semantics.Tense.Basic

/-!
# Russian Temporal Deictic Adverbs
[tsilia-zhao-2026]

Lexical entry for Russian тогда "togda" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility.

-/

namespace Russian.TemporalDeictic

open Tense

/-- Russian тогда "togda" -/
def togda : ThenAdverb where
  language := "Russian"
  form := "тогда"
  gloss := "then"
  shiftsPerspective := true

end Russian.TemporalDeictic
