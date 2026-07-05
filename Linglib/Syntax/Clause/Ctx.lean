/-!
# Clause contexts

This file defines `Clause.Ctx`, the [sadock-zwicky-1985] sentence types
with the interrogative split into polar, alternative, and constituent
subtypes. `Clause.Embedding` is the orthogonal embedding axis;
`Semantics.Mood.IllocutionaryMood`, `Semantics.Mood.ClauseType`, and
`Features.ClauseForm` are coarser cuts.
-/

namespace Clause

/-- A [sadock-zwicky-1985] sentence type, with interrogatives subtyped. -/
inductive Ctx where
  | declarative
  | polarInterrogative
  /-- Alternative question ("Is it A or B?"). -/
  | alternativeInterrogative
  /-- Constituent (wh-) question. -/
  | constituentInterrogative
  | imperative
  | exclamative
  deriving DecidableEq, Repr

namespace Ctx

/-- The interrogative cells. -/
def IsInterrogative : Ctx → Prop
  | polarInterrogative | alternativeInterrogative | constituentInterrogative => True
  | _ => False

instance : DecidablePred IsInterrogative := fun c => by
  cases c <;> simp only [IsInterrogative] <;> infer_instance

end Ctx

end Clause
