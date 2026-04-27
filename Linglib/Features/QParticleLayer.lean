/-!
# Q-Particle Layer Feature
@cite{dayal-2025} @cite{turk-hirsch-2026}

A typological feature classifying Q-particles by their position in the
left periphery. Used cross-paper by typological work on question
particles (Bhatt-Dayal 2020, Theiler 2021, Simik 2024, Zheng 2025,
Seeliger-Repp 2018).

Lives in `Features/` (not `Theories/Semantics/Questions/`) because it
is a feature taxonomy with no semantic commitments — sibling of
`Polarity`, `Mood`, `Evidentiality`.
-/

namespace Features

/-- Where in the left periphery a Q-particle resides. -/
inductive QParticleLayer where
  | cp      -- Clause-typing particle: obligatory in subordinated interrogatives
  | perspP  -- Polar question particle (PQP): matrix + quasi-subordinated, not subordinated
  | sap     -- Meta question particle (MQP): matrix + quotation only
  | polP    -- Clause-internal polarity head (Turkish mI; @cite{turk-hirsch-2026})
  deriving DecidableEq, Repr

end Features
