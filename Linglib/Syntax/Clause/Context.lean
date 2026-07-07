/-!
# Clause contexts

This file defines `Clause.Context`, the [sadock-zwicky-1985] sentence types
with the interrogative split into polar, alternative, and constituent
subtypes. `Clause.Embedding` is the orthogonal embedding axis;
`Mood.Illocutionary`, `Mood.ClauseType`, and
`Features.ClauseForm` are coarser cuts.
-/

namespace Clause

/-- A [sadock-zwicky-1985] sentence type, with interrogatives subtyped. -/
inductive Context where
  | declarative
  | polarInterrogative
  /-- Alternative question ("Is it A or B?"). -/
  | alternativeInterrogative
  /-- Constituent (wh-) question. -/
  | constituentInterrogative
  | imperative
  | exclamative
  deriving DecidableEq, Repr

namespace Context

/-- The interrogative cells. -/
def IsInterrogative : Context → Prop
  | polarInterrogative | alternativeInterrogative | constituentInterrogative => True
  | _ => False

instance : DecidablePred IsInterrogative := fun c => by
  cases c <;> simp only [IsInterrogative] <;> infer_instance

end Context

end Clause
