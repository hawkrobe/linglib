import Linglib.Theories.Semantics.Tense.Basic

/-!
# Mandarin Temporal Deictic Adverbs

Lexical entry for Mandarin 那时 "nà-shí" (that time), typed by `ThenAdverb`.

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation, Part I.
-/

namespace Fragments.Mandarin.TemporalDeictic

open Semantics.Tense

/-- Mandarin 那时 "nà-shí" -/
def nashi : ThenAdverb where
  language := "Mandarin"
  form := "那时"
  gloss := "that time"
  shiftsPerspective := true

end Fragments.Mandarin.TemporalDeictic
