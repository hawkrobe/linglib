/-!
# Core Negation Types

Framework-agnostic types for negation phenomena shared across
fragments and phenomena layers.
-/

namespace Core

/-- Cross-linguistic reasons why a trigger class may not license
    expletive negation in a particular language (@cite{jin-koenig-2021} §7). -/
inductive ENBlockingReason where
  /-- Language disprefers modal operators in complement clauses -/
  | modalRestriction
  /-- Comparative complements only allow NPs, not clauses -/
  | npOnlyComplement
  /-- Concept expressed analytically with necessary (non-expletive) negation -/
  | analyticNegation
  deriving DecidableEq, Repr

end Core
