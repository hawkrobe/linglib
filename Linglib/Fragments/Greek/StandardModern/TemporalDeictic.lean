import Linglib.Semantics.Tense.Perspective

/-!
# Greek temporal deictic adverbs

Lexical entry for Modern Greek τότε *tóte* 'then', typed by
`Tense.Perspective.ThenAdverb` — [tsilia-zhao-2026]'s ⌈then⌉ class of
temporal pronouns presupposing disjointness from the perspective time π.
-/

namespace Greek.StandardModern.TemporalDeictic

open Tense.Perspective

/-- Greek τότε *tóte* 'then' -/
def tote : ThenAdverb where
  form := "τότε"
  gloss := "then"

end Greek.StandardModern.TemporalDeictic
