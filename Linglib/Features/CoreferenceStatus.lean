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

end Features
