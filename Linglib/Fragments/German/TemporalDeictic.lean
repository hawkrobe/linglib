import Linglib.Theories.Semantics.Tense.Basic

/-!
# German Temporal Deictic Adverbs

Lexical entry for German "damals" (back then), typed by `ThenAdverb`.

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation, Part I.
-/

namespace Fragments.German.TemporalDeictic

open Semantics.Tense

/-- German "damals" (back-then) -/
def damals : ThenAdverb where
  language := "German"
  form := "damals"
  gloss := "back then"
  shiftsPerspective := true

end Fragments.German.TemporalDeictic
