import Linglib.Theories.Semantics.Tense.Basic

/-!
# Japanese Temporal Deictic Adverbs
@cite{zhao-2025}

Lexical entry for Japanese その時 "sono-toki" (that time), typed by `ThenAdverb`.

-/

namespace Fragments.Japanese.TemporalDeictic

open Semantics.Tense

/-- Japanese その時 "sono-toki" -/
def sonotoki : ThenAdverb where
  language := "Japanese"
  form := "その時"
  gloss := "that time"
  shiftsPerspective := true

end Fragments.Japanese.TemporalDeictic
