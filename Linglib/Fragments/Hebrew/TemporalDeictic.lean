import Linglib.Theories.Semantics.Tense.Basic

/-!
# Hebrew Temporal Deictic Adverbs

Lexical entry for Hebrew אז "az" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility
(Tsilia, Zhao & Sharvit 2026).

## References

- Tsilia, D., Zhao, Z. & Sharvit, Y. (2026). Tense and perspective.
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
