/-!
# Q-Particle Layer Type
@cite{dayal-2025}


Where in the left periphery a Q-particle resides.

Extracted from `Phenomena.Questions.Typology` so that Fragment files
can reference the type without importing empirical data.
-/

namespace Semantics.Questions

/-- Where in the left periphery a Q-particle resides. -/
inductive QParticleLayer where
  | cp      -- Clause-typing particle: obligatory in subordinated interrogatives
  | perspP  -- Polar question particle (PQP): matrix + quasi-subordinated, not subordinated
  | sap     -- Meta question particle (MQP): matrix + quotation only
  | polP    -- Clause-internal polarity head (Turkish mI; Turk, Hirsch & İnce 2026)
  deriving DecidableEq, Repr, BEq

end Semantics.Questions
