import Linglib.Syntax.Particle.Basic

/-!
# Hindi-Urdu Interrogative Particles
[bhatt-dayal-2014] [bhatt-dayal-2020] [dayal-2025]

Particles related to question formation in Hindi-Urdu, as `Particle`
values with embedding-distribution facets, following [bhatt-dayal-2014]
and [dayal-2025].

Hindi-Urdu lacks a dedicated *wh*-complementizer for polar questions
(unlike English *whether* or Italian *se*). Instead, it uses:

1. *kya:* — analyzed by [bhatt-dayal-2020] as a polar question particle
   at PerspP (not CP); the layer is derived from the embedding facet in
   `BhattDayal2020`, together with its predicate-selection profile.
2. *ki* — a general subordinator (like Hungarian *hogy*), compatible
   with both declarative and interrogative complements.

The absence of a clause-typing particle means:
- Simplex polar questions (just *p*, no "or not") cannot be subordinated
  (clause-typing cannot be forced at CP).
- *kya:* in embedded position is the hallmark of quasi-subordination.
-/

namespace HindiUrdu.Particles

/-- *ki* — general subordinator. Compatible with both declarative and
interrogative complements (and with responsive and rogative predicates
alike). NOT a clause-typing particle. -/
def ki : Particle where
  form := "ki"
  position := some .clauseInitial
  embedding := some
    { matrix := some .excluded
      subordinated := some .optional
      quasiSubordinated := some .optional }

/-- *kya:* — [bhatt-dayal-2020]'s polar question particle: occurs in
polar questions but not wh-questions, optionally in matrix and in a
restricted way in embedded questions, with flexible clause-internal
positioning ("can occur almost anywhere within a clause", §2).
Selectionally: incompatible with *nirbhar kar-na:* "depend on" (a
responsive selecting CP only); compatible with *pu:ch-na:* "ask" and
*sava:l yeh hai* "the question is" (rogatives). Its PerspP layer is
derived in `BhattDayal2020`. -/
def kya : Particle where
  form := "kya:"
  position := some .free
  distribution := some
    { polarInterrogative := some .optional
      constituentInterrogative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded
      quasiSubordinated := some .optional
      quotation := some .excluded }

/-- *ya: nahii:* — "or not", provides an overt alternative for polar
questions. Required in subordinated polar questions (since *kya:* is
unavailable there); forms specifically alternative questions. -/
def ya_nahi : Particle where
  form := "ya: nahii:"
  position := some .clauseFinal
  distribution := some
    { alternativeInterrogative := some .optional }
  embedding := some
    { subordinated := some .obligatory
      quasiSubordinated := some .optional }

def allParticles : List Particle := [ki, kya, ya_nahi]

end HindiUrdu.Particles
