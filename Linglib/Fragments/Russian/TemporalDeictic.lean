import Linglib.Theories.Semantics.Tense.Basic

/-!
# Russian Temporal Deictic Adverbs

Lexical entry for Russian тогда "togda" (then), typed by `ThenAdverb`.
Cross-linguistic evidence for the then-present incompatibility
(Tsilia, Zhao & Sharvit 2026).

## References

- Tsilia, D., Zhao, Z. & Sharvit, Y. (2026). Tense and perspective.
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
