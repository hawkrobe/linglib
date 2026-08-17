import Linglib.Syntax.Category.Particle.Basic

/-!
# Hindi-Urdu interrogative particles

Hindi-Urdu has no polar *wh*-complementizer (English *whether*, Italian
*se*): finite complements of every clause type are introduced by the
general subordinator *ki* (compare Hungarian *hogy*), and matrix polar
questions are marked by rising intonation plus the optional particle
*kya:*. *kya:* occurs in polar and alternative but not constituent
questions and occupies a projection above CP (Bhatt and Dayal's ForceP,
Dayal's later PerspP); it embeds only in quasi-subordination. Since
nothing clause-types a bare embedded polar clause, subordinated polar
questions require the overt alternative *ya: nahii:* "or not". This file
provides the three particles as `Particle` values with clause-type and
embedding facets.

## Main declarations

* `HindiUrdu.Particles.kya` — the polar question particle.
* `HindiUrdu.Particles.ki` — the general subordinator.
* `HindiUrdu.Particles.ya_nahi` — the overt polar alternative.

## References

* [bhatt-dayal-2014]
* [bhatt-dayal-2020], §2, §5
* [dayal-2025], §1.3, ex. 70–71
-/

namespace HindiUrdu.Particles

/-- *ki* — the general subordinator: introduces finite complements of
any clause type, under responsive and rogative predicates alike, and
does no clause-typing. Distinct from the homophonous disjunction *ki*,
which is restricted to alternative questions. -/
def ki : Particle where
  form := "ki"
  position := some .clauseInitial
  embedding := some
    { matrix := some .excluded
      subordinated := some .optional
      quasiSubordinated := some .optional }

/-- *kya:* — the polar question particle: optional in matrix polar
questions, excluded from constituent questions, acceptable in
alternative questions (parsed as *kya:* on a disjoined polar question),
with no fixed clause-internal position. It embeds only in
quasi-subordination: under rogatives like *pu:ch-na:* "ask", not under
responsives or CP-only rogatives like *nirbhar kar-na:* "depend on". -/
def kya : Particle where
  form := "kya:"
  position := some .free
  distribution := some
    { polarInterrogative := some .optional
      alternativeInterrogative := some .optional
      constituentInterrogative := some .excluded }
  embedding := some
    { matrix := some .optional
      subordinated := some .excluded
      quasiSubordinated := some .optional }

/-- *ya: nahii:* — "or not", the overt disjunct that turns a polar
question into a polar alternative question: optional in matrix and
quasi-subordinated positions, obligatory under subordination, where a
simplex polar cannot be clause-typed. -/
def ya_nahi : Particle where
  form := "ya: nahii:"
  position := some .clauseFinal
  distribution := some
    { alternativeInterrogative := some .optional }
  embedding := some
    { matrix := some .optional
      subordinated := some .obligatory
      quasiSubordinated := some .optional }

/-- All Hindi-Urdu question-formation particles indexed in this file. -/
def allParticles : List Particle := [ki, kya, ya_nahi]

end HindiUrdu.Particles
