import Linglib.Theories.Semantics.Tense.Basic

/-!
# Russian Temporal Deictic Adverbs
@cite{tsilia-zhao-sharvit-2026}

Lexical entry for Russian тогда "togda" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility.

-/

namespace Fragments.Russian.TemporalDeictic

open Semantics.Tense

/-- Russian тогда "togda" -/
def togda : ThenAdverb where
  language := "Russian"
  form := "тогда"
  gloss := "then"
  shiftsPerspective := true

end Fragments.Russian.TemporalDeictic
