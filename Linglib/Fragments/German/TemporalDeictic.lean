import Linglib.Semantics.Tense.Basic

/-!
# German Temporal Deictic Adverbs
@cite{zhao-2025}

Lexical entry for German "damals" (back then), typed by `ThenAdverb`.

-/

namespace German.TemporalDeictic

open Semantics.Tense

/-- German "damals" (back-then) -/
def damals : ThenAdverb where
  language := "German"
  form := "damals"
  gloss := "back then"
  shiftsPerspective := true

end German.TemporalDeictic
