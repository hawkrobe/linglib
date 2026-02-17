import Linglib.Theories.Semantics.Tense.Basic

/-!
# Greek Temporal Deictic Adverbs

Lexical entry for Greek τότε "tóte" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility
(Tsilia, Zhao & Sharvit 2026).

## References

- Tsilia, D., Zhao, Z. & Sharvit, Y. (2026). Tense and perspective.
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
