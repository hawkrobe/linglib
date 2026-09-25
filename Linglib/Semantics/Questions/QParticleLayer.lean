module

/-!
# Question-particle layers

This file defines the layer of the left periphery a question particle sits in, Dayal's three
points at which question meaning is built, clause typing at C, centering at PerspP and the
speech act at SAP, together with the clause-internal polarity head that Türk and Hirsch argue
Turkish *mI* occupies. A particle's layer is derived from its distribution over embedding
contexts in the study of Dayal's proposal, not stored.

## References

* [dayal-2025]
* [turk-hirsch-2026]
-/

@[expose] public section

namespace Question

/-- Where in the left periphery a Q-particle resides. -/
inductive QParticleLayer where
  | cp      -- Clause-typing particle: obligatory in subordinated interrogatives
  | perspP  -- Polar question particle (PQP): matrix + quasi-subordinated, not subordinated
  | sap     -- Meta question particle (MQP): matrix + quotation only
  | polP    -- Clause-internal polarity head (Turkish mI; [turk-hirsch-2026])
  deriving DecidableEq, Repr

end Question
