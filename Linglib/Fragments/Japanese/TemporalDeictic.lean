import Linglib.Theories.Semantics.Tense.Basic

/-!
# Japanese Temporal Deictic Adverbs

Lexical entry for Japanese その時 "sono-toki" (that time), typed by `ThenAdverb`.

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation, Part I.
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
