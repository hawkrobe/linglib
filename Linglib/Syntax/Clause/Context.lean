import Linglib.Semantics.Mood.Defs

/-!
# Clause context axes

The two orthogonal context axes of a clause: its [sadock-zwicky-1985]
sentence type (`Clause.SentenceType`, with the interrogative split into
polar, alternative, and constituent subtypes) and the embedding context
it occurs in (`Clause.EmbeddingContext`, the [bhatt-dayal-2020] /
[dayal-2025] question-embedding cells). The coarse cut of the first
axis is `Mood.Illocutionary` — `SentenceType.force` is the projection.
`Features.QParticleLayer` is defined over the second axis, so a
particle's layer is derivable from its embedding distribution
(`Studies/BhattDayal2020`).
-/

namespace Clause

/-- A [sadock-zwicky-1985] sentence type, with interrogatives
    subtyped. -/
inductive SentenceType where
  | declarative
  | polarInterrogative
  /-- Alternative question ("Is it A or B?"). -/
  | alternativeInterrogative
  /-- Constituent (wh-) question. -/
  | constituentInterrogative
  | imperative
  | exclamative
  deriving DecidableEq, Repr

namespace SentenceType

/-- The illocutionary force of a sentence type — the coarse
    [sadock-zwicky-1985] cut, collapsing the interrogative subtypes. -/
def force : SentenceType → Mood.Illocutionary
  | declarative => .declarative
  | polarInterrogative | alternativeInterrogative
  | constituentInterrogative => .interrogative
  | imperative => .imperative
  | exclamative => .exclamative

end SentenceType

/-- A [bhatt-dayal-2020] interrogative-embedding context: where the
    interrogative occurs. -/
inductive EmbeddingContext where
  | matrix
  | subordinated
  /-- Embedded root-like interrogatives (Hindi-Urdu *kya:*). -/
  | quasiSubordinated
  | quotation
  deriving DecidableEq, Repr

end Clause
