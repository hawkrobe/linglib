/-!
# Clause embedding contexts

This file defines `Clause.Embedding`, the [bhatt-dayal-2020] /
[dayal-2025] question-embedding contexts. `Features.QParticleLayer` is
defined over these cells, so a particle's layer is derivable from its
embedding distribution (`Studies/BhattDayal2020`).
-/

namespace Clause

/-- A [bhatt-dayal-2020] interrogative-embedding context. -/
inductive Embedding where
  | matrix
  | subordinated
  /-- Embedded root-like interrogatives (Hindi-Urdu *kya:*). -/
  | quasiSubordinated
  | quotation
  deriving DecidableEq, Repr

end Clause
