import Linglib.Semantics.Tense.Perspective

/-!
# Russian temporal deictic adverbs

Lexical entry for Russian тогда *togda* 'then', typed by
`Tense.Perspective.ThenAdverb` — [tsilia-zhao-2026]'s ⌈then⌉ class of
temporal pronouns presupposing disjointness from the perspective time π.
-/

namespace Russian.TemporalDeictic

open Tense.Perspective

/-- Russian тогда *togda* 'then' -/
def togda : ThenAdverb where
  form := "тогда"
  gloss := "then"

end Russian.TemporalDeictic
