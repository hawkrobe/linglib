/-!
# Clause-Context Feature
[sadock-zwicky-1985]

The clause-type inventory particles are distributed over, following
[sadock-zwicky-1985]'s cross-linguistic typology of sentence types:
the major forces (declarative, interrogative, imperative, exclamative)
with the interrogative refined into polar, alternative, and constituent
subtypes. The polar/alternative/constituent split is load-bearing for
particle distribution (German *denn* is licensed in polar and constituent
questions; Hindi-Urdu *ya: nahii:* forms specifically alternative
questions).

Lives in `Features/` (sibling of `QParticleLayer`) because it is a
feature taxonomy with no semantic commitments. Neighboring inventories
cut differently and complement it: `Semantics.Mood.IllocutionaryMood`
collapses the three interrogative cells; `Semantics.Mood.ClauseType`
crosses force with verbal mood; `Features.ClauseForm` distinguishes
matrix from embedded questions (the word-order/embedding axis,
orthogonal to the sentence-type axis here).
-/

namespace Features

/-- A clause context a particle may be distributed over:
[sadock-zwicky-1985]'s sentence types, with the interrogative split
into its polar / alternative / constituent subtypes. -/
inductive ClauseCtx where
  | declarative
  | polarInterrogative
  /-- Alternative question ("Is it A or B?"; Hindi-Urdu *ya: nahii:*). -/
  | alternativeInterrogative
  /-- Constituent (wh-) question. -/
  | constituentInterrogative
  | imperative
  | exclamative
  deriving DecidableEq, Repr

namespace ClauseCtx

/-- The interrogative cells. -/
def IsInterrogative : ClauseCtx → Prop
  | polarInterrogative | alternativeInterrogative | constituentInterrogative => True
  | _ => False

instance : DecidablePred IsInterrogative := fun c => by
  cases c <;> simp only [IsInterrogative] <;> infer_instance

end ClauseCtx

end Features
