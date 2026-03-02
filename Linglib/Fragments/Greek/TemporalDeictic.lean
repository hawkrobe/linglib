import Linglib.Theories.Semantics.Tense.Basic

/-!
# Greek Temporal Deictic Adverbs
@cite{tsilia-zhao-sharvit-2026}

Lexical entry for Greek τότε "tóte" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility.

-/

namespace Fragments.Greek.TemporalDeictic

open Semantics.Tense

/-- Greek τότε "tóte" -/
def tote : ThenAdverb where
  language := "Greek"
  form := "τότε"
  gloss := "then"
  shiftsPerspective := true

end Fragments.Greek.TemporalDeictic
