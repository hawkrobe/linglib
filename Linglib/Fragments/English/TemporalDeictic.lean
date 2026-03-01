import Linglib.Theories.Semantics.Tense.Basic

/-!
# English Temporal Deictic Adverbs
@cite{zhao-2025}

Lexical entry for English temporal "then", typed by `ThenAdverb`.

-/

namespace Fragments.English.TemporalDeictic

open Semantics.Tense

/-- English "then" -/
def then_ : ThenAdverb where
  language := "English"
  form := "then"
  gloss := "then"
  shiftsPerspective := true

end Fragments.English.TemporalDeictic
