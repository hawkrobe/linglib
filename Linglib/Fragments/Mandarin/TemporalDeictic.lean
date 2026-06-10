import Linglib.Semantics.Tense.Basic

/-!
# Mandarin Temporal Deictic Adverbs
[zhao-2025]

Lexical entry for Mandarin 那时 "nà-shí" (that time), typed by `ThenAdverb`.

-/

namespace Mandarin.TemporalDeictic

open Tense

/-- Mandarin 那时 "nà-shí" -/
def nashi : ThenAdverb where
  language := "Mandarin"
  form := "那时"
  gloss := "that time"
  shiftsPerspective := true

end Mandarin.TemporalDeictic
