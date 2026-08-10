import Linglib.Semantics.Tense.Perspective

/-!
# Japanese temporal deictic adverbs

Lexical entry for Japanese 当時 *tōji* 'at that time', typed by
`Tense.Perspective.ThenAdverb` — the Japanese member of the ⌈then⌉ class
of temporal pronouns presupposing disjointness from the perspective time π
([zhao-2025], [tsilia-zhao-2026]). *tōji* is restricted to past-oriented
contexts (see the tense-shift typology in `Studies/TsiliaZhao2026.lean`).
-/

namespace Japanese.TemporalDeictic

open Tense.Perspective

/-- Japanese 当時 *tōji* 'at that time' -/
def tooji : ThenAdverb where
  form := "当時"
  gloss := "at that time"

end Japanese.TemporalDeictic
