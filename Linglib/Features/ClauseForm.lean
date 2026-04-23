/-!
# ClauseForm

Surface clause-form distinctions relevant to word order.

`ClauseForm` is a *syntactic* form distinction (matrix question vs
embedded question vs declarative) — what conditions inversion and other
word-order alternations. Echo questions are *not* a constructor here;
they are declarative-form sentences with question force in discourse,
handled via `Core.InformationStructure`. Distinct from
`Core.Mood.ClauseType`, which pairs illocutionary force with verbal
mood. The two complement each other: a polar question has
`ClauseForm = matrixQuestion` and `Core.Mood.ClauseType =
⟨interrogative, indicative⟩`.
-/

namespace Features

inductive ClauseForm where
  | declarative
  | matrixQuestion      -- requires inversion in English
  | embeddedQuestion    -- no inversion in English
  deriving Repr, DecidableEq

end Features
