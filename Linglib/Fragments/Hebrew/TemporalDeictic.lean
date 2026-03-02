import Linglib.Theories.Semantics.Tense.Basic

/-!
# Hebrew Temporal Deictic Adverbs
@cite{tsilia-zhao-sharvit-2026}

Lexical entry for Hebrew אז "az" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility.

-/

namespace Fragments.Hebrew.TemporalDeictic

open Semantics.Tense

/-- Hebrew אז "az" -/
def az : ThenAdverb where
  language := "Hebrew"
  form := "אז"
  gloss := "then"
  shiftsPerspective := true

end Fragments.Hebrew.TemporalDeictic
