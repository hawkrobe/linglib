import Linglib.Semantics.Presupposition.TriggerTypology

/-!
# Cantonese *again*-elements

The Cantonese iterative presupposition triggers, following [matthews-yip-1994]: the preverbal
adverbs *jau* 又 and *zoi* 再, the counterparts of Mandarin *you* and *zai*
(`Fragments/Mandarin/Particles.lean`), the postverbal suffix *-faan* 返 'again, back', and the
postverbal repetitive *-gwo* 過 'again, anew', homophonous with the experiential aspect suffix of
`Fragments/Cantonese/Aspect.lean`. Their
association with the outer and inner aspect projections and their scope behaviour are the
analysis of [liu-yip-2026] and live in `Studies/LiuYip2026.lean`.

## References

* [matthews-yip-1994]
* [liu-yip-2026]
* [lee-yip-to-appear]
-/

namespace Cantonese.Particles

open Presupposition.TriggerTypology

/-- A Cantonese presupposition trigger: its character, its jyutping, its gloss and its trigger
class. -/
structure PresupParticle where
  /-- The character. -/
  hanzi : String
  /-- The jyutping form with tone number. -/
  jyutping : String
  /-- The gloss. -/
  gloss : String
  /-- The trigger class. -/
  trigger : PresupTrigger
  deriving Repr, DecidableEq

/-- The preverbal *jau* 又 'again'. -/
def jau : PresupParticle :=
  { hanzi := "又", jyutping := "jau6", gloss := "again", trigger := .iterative }

/-- The preverbal *zoi* 再 'again'. -/
def zoi : PresupParticle :=
  { hanzi := "再", jyutping := "zoi3", gloss := "again", trigger := .iterative }

/-- The postverbal *-faan* 返 'again, back'. -/
def faan : PresupParticle :=
  { hanzi := "返", jyutping := "faan1", gloss := "again", trigger := .iterative }

/-- The postverbal repetitive *-gwo* 過 'again, anew', redoing an event to set its outcome right. -/
def gwo : PresupParticle :=
  { hanzi := "過", jyutping := "gwo3", gloss := "again", trigger := .iterative }

/-- The *again*-elements. -/
def all : List PresupParticle := [jau, zoi, faan, gwo]

end Cantonese.Particles
