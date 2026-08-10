import Linglib.Semantics.Tense.Perspective

/-!
# English temporal deictic adverbs

Lexical entry for English *then*, typed by `Tense.Perspective.ThenAdverb` —
[zhao-2025]'s ⌈then⌉ class of temporal pronouns presupposing disjointness
from the perspective time π.
-/

namespace English.TemporalDeictic

open Tense.Perspective

/-- English *then* -/
def then_ : ThenAdverb where
  form := "then"
  gloss := "then"

end English.TemporalDeictic
