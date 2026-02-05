/-!
# Hindi-Urdu Interrogative Particles

Particles related to question formation in Hindi-Urdu, following
Bhatt & Dayal (2014, 2020) and Dayal (2025: §§1.3, 4.4).

Hindi-Urdu lacks a dedicated *wh*-complementizer for polar questions (unlike
English *whether* or Italian *se*). Instead, it uses:

1. *kya:* — a polar question particle (PQP), placed at PerspP (not CP).
   Appears in matrix and quasi-subordinated questions, but NOT subordinated.
2. *ki* — a general subordinator (like Hungarian *hogy*), compatible with
   both declarative and interrogative complements.

The absence of a clause-typing particle means:
- Simplex polar questions (just *p*, no "or not") cannot be subordinated
  (clause-typing cannot be forced at CP).
- *kya:* in embedded position is the hallmark of quasi-subordination.

## References

- Bhatt, R. & V. Dayal (2014). Polar kyaa: Y/N or speech act operator.
- Bhatt, R. & V. Dayal (2020). Polar question particles: Hindi-Urdu kya:.
- Dayal, V. (2025). The Interrogative Left Periphery. Linguistic Inquiry 56(4).
-/

namespace Fragments.HindiUrdu.Particles

/-- A Hindi-Urdu particle entry. -/
structure ParticleEntry where
  form : String
  gloss : String
  /-- Is this a clause-typing particle (CP-level)? -/
  clauseTyping : Bool
  /-- Is this a polar question particle (PerspP-level)? -/
  polarQuestion : Bool
  /-- Can it appear in subordinated interrogatives? -/
  inSubordinated : Bool
  /-- Can it appear in quasi-subordinated interrogatives? -/
  inQuasiSub : Bool
  /-- Compatible with responsive predicates? -/
  withResponsive : Bool
  /-- Compatible with rogative predicates? -/
  withRogative : Bool
  deriving Repr, BEq

/-- *ki* — general subordinator. Compatible with both declarative and
    interrogative complements. NOT a clause-typing particle. -/
def ki : ParticleEntry :=
  { form := "ki", gloss := "SUB (subordinator)"
  , clauseTyping := false, polarQuestion := false
  , inSubordinated := true, inQuasiSub := true
  , withResponsive := true, withRogative := true }

/-- *kya:* — polar question particle (PQP). Sits at PerspP, not CP.
    Appears in matrix and quasi-subordinated contexts only.
    Incompatible with *nirbhar kar-na:* "depend on" (rogativeCP: selects CP only).
    Compatible with *pu:ch-na:* "ask" (rogativeSAP) and
    *sava:l yeh hai* "the question is" (rogativePerspP). -/
def kya : ParticleEntry :=
  { form := "kya:", gloss := "PQP (polar question particle)"
  , clauseTyping := false, polarQuestion := true
  , inSubordinated := false, inQuasiSub := true
  , withResponsive := false, withRogative := true }

/-- *ya: nahii:* — "or not", provides overt alternative for polar questions.
    Required in subordinated polar questions (since *kya:* is unavailable). -/
def ya_nahi : ParticleEntry :=
  { form := "ya: nahii:", gloss := "or not"
  , clauseTyping := false, polarQuestion := false
  , inSubordinated := true, inQuasiSub := true
  , withResponsive := true, withRogative := true }

def allParticles : List ParticleEntry := [ki, kya, ya_nahi]

end Fragments.HindiUrdu.Particles
