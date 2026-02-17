import Linglib.Theories.Semantics.Tense.Basic

/-!
# English Temporal Deictic Adverbs

Lexical entry for English temporal "then", typed by `ThenAdverb`.

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation, Part I.
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
