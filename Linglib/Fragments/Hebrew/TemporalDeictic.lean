import Linglib.Semantics.Tense.Perspective

/-!
# Hebrew temporal deictic adverbs

Lexical entry for Modern Hebrew אז *az* 'then', typed by
`Tense.Perspective.ThenAdverb` — [tsilia-zhao-2026]'s ⌈then⌉ class of
temporal pronouns presupposing disjointness from the perspective time π.
-/

namespace Hebrew.TemporalDeictic

open Tense.Perspective

/-- Hebrew אז *az* 'then' -/
def az : ThenAdverb where
  form := "אז"
  gloss := "then"

end Hebrew.TemporalDeictic
