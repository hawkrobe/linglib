/-!
# Features.CoreferenceStatus

Cross-framework coreference verdict enum. Syntactic frameworks (HPSG,
Dependency Grammar, Minimalism) each provide a
`computeCoreferenceStatus : ... → CoreferenceStatus` function — the shared
return type is what makes their predictions comparable rather than each
framework's verdict living in a private namespace.
-/

namespace Features

/-- The possible coreference relationships between two positions. -/
inductive CoreferenceStatus where
  /-- Coreference is obligatory (reflexives with local antecedent) -/
  | obligatory
  /-- Coreference is possible but not required -/
  | possible
  /-- Coreference is blocked (Principle B/C violations) -/
  | blocked
  /-- No prediction (positions not in relevant configuration) -/
  | unspecified
  deriving Repr, DecidableEq

/-- The binding-theoretic class of a nominal expression, shared across the
    syntactic frameworks (HPSG, Dependency Grammar, Minimalism) so their
    `classifyNominal` functions return the same type. The per-language
    realization (which forms are which) lives in a Fragment helper (e.g.
    `Fragments.English.NominalClassification`). -/
inductive NominalType where
  /-- Reflexive anaphor (*himself*, *herself*, *themselves*). -/
  | reflexive
  /-- Reciprocal anaphor (*each other*, *one another*). -/
  | reciprocal
  /-- Personal/other pronoun (*he*, *she*, *they*, …). -/
  | pronoun
  /-- Referring expression (proper name, full NP). -/
  | rExpression
  deriving Repr, DecidableEq

end Features
