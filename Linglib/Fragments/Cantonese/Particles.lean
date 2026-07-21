import Linglib.Semantics.Presupposition.TriggerTypology

/-!
# Cantonese Presuppositional Particles
[matthews-yip-1994] [liu-yip-2026] [lee-yip-to-appear]

Lexical entries for Cantonese preverbal *again*-elements *jau* and *zoi*,
parallel to the Mandarin entries in `Fragments/Mandarin/Particles.lean`.
Per [liu-yip-2026] §5, these are the Cantonese counterparts of
Mandarin *you* and *zai* respectively, but unlike Mandarin *you*, the
preverbal Cantonese *jau* does NOT exhibit the scope-skipping pattern
(see `Studies/LiuYip2026.lean` for the analytical
discussion).

This file commits the consensus lexical data only; the analytical claim that
*jau* lacks the [u+D] feature borne by Mandarin *you* — and therefore cannot
trigger movement to matrix AspP_outer — lives in the Studies file.
-/

namespace Cantonese.Particles

open Semantics.Presupposition.TriggerTypology (PresupTrigger)

/-- A Cantonese presuppositional particle entry. -/
structure PresupParticle where
  hanzi : String
  jyutping : String
  gloss : String
  trigger : PresupTrigger
  notes : String := ""
  deriving Repr

/-- 又 *jau* — preverbal 'again' (iterative). Cantonese counterpart of
    Mandarin *you*. Per [liu-yip-2026] §5, *jau* lacks the
    scope-skipping property of Mandarin *you* (see `LiuYip2026.lean`
    for the analysis). -/
def jau : PresupParticle :=
  { hanzi := "又", jyutping := "jau6", gloss := "again"
  , trigger := .iterative
  , notes := "Mandarin you's counterpart; no scope-skipping per Liu&Yip2026" }

/-- 再 *zoi* — preverbal 'again' (iterative, lower position). Cantonese
    counterpart of Mandarin *zai*. Per [liu-yip-2026] §5, *zoi* is
    AspP_inner-associated, paralleling Mandarin *zai*. -/
def zoi : PresupParticle :=
  { hanzi := "再", jyutping := "zoi3", gloss := "again"
  , trigger := .iterative
  , notes := "Mandarin zai's counterpart; AspP_inner-associated per Liu&Yip2026" }

def all : List PresupParticle := [jau, zoi]

/-- Drift sentry: the inventory covers exactly *jau* and *zoi*. -/
theorem all_membership :
    all.map (·.jyutping) = ["jau6", "zoi3"] := by decide

/-- Both Cantonese preverbal *again*-elements are iterative-class
    presupposition triggers. -/
theorem both_iterative :
    jau.trigger = .iterative ∧ zoi.trigger = .iterative := ⟨rfl, rfl⟩

end Cantonese.Particles
