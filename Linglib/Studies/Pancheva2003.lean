import Linglib.Data.Examples.Schema
import Linglib.Semantics.Aspect.Basic
import Linglib.Studies.Kiparsky2002
import Linglib.Data.Examples.Pancheva2003

/-!
# Pancheva (2003): The Aspectual Makeup of Perfect Participles
[pancheva-2003] [kiparsky-2002] [iatridou-anagnostopoulou-izvorski-2001]

Pancheva (in *Perfect Explorations*, Alexiadou-Rathert-von Stechow
eds., 2003) argues that the three perfect interpretations
(Universal, Experiential, Resultative) arise from the aspectual makeup
of the perfect participle — specifically the interaction of
Aktionsart with grammatical aspect (perfective vs imperfective)
inside the participial VP.

## Verified content (vs PDF; § refs from the paper)

- **Three perfect types** (§1, ex 1): Universal (U), Experiential
  (EXP), Resultative (RES). EXP and RES are commonly grouped under
  the EXISTENTIAL umbrella (McCawley 1971, Mittwoch 1988).
- **Aspectual makeup determines reading availability** (§2 thesis):
  Universal and Resultative interpretations depend on participial
  aspect, Experiential does not. States/progressives → U or EXP;
  non-progressive activities → EXP only; non-progressive telic →
  RES or EXP.
- **Resultative requires telic predicates** (§2, ex 5–6, citing
  Kratzer 1994): only telic events have a natural (lexically
  inherent) result state. *I have run* (5a, atelic) lacks RES; *I
  have lost my glasses* (6a, telic) has both EXP and RES.
- **Cross-linguistic aspectual restrictions** (§2): Greek perfect
  participles are obligatorily perfective → no Universal perfect;
  Bulgarian allows non-perfective participles → Universal possible.

## Relation to companion files

- `Studies/IatridouEtAl2001.lean` — Pancheva builds on IAI 2001's
  PTS framework and U/E distinction. Her contribution is the
  participle-aspect mechanism.
- `Studies/Kiparsky2002.lean` — Kiparsky's event-structure account
  is an independent proposal for the same polysemy. The
  `toKiparsky` bridge below embeds Pancheva's 3-type taxonomy into
  Kiparsky's 4-reading enum (Kiparsky adds present-state, which
  Pancheva does not distinguish).

The operators of (7b) and (9b), the inner viewpoints NEUTRAL (`INIT_OVERLAP`)
and BOUNDED and the interval-level PERFECT (`PERF_P`), and the three perfect
readings they compose to (`universalPerfect`, `experientialPerfect`,
`resultativePerfect`), are this file's; the non-strict imperfective UNBOUNDED
is shared substrate, `Aspect.UNBOUNDED`.

-/

namespace Pancheva2003

open Data.Examples (LinguisticExample)
open Aspect
open Kiparsky2002 (PerfectReading)

/-! ### The aspectual makeup of the participle, (7) and (9) -/

variable {T : Type*} [LinearOrder T] {W : Type*}

/-- The neutral inner viewpoint of (7b), p. 282: the reference interval overlaps the beginning
of the event, which may extend beyond it. -/
def INIT_OVERLAP (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t.initialOverlap e.τ ∧ P w e

/-- The bounded inner viewpoint of (7b): the run time of the event is properly contained in the
reference interval. -/
def BOUNDED (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, e.τ < t ∧ P w e

/-- The interval-level PERFECT of (9b), p. 284: some perfect time span of which the reference
interval is a final subinterval satisfies the predicate. -/
def PERF_P (p : IntervalPred W T) : IntervalPred W T :=
  λ w i => ∃ pts : NonemptyInterval T, i.finalSubinterval pts ∧ p w pts

/-- The point-based `Aspect.PERF` is `PERF_P` at a degenerate reference interval. -/
theorem perf_p_pure_iff_perf (p : IntervalPred W T) (w : W) (t : T) :
    PERF_P p w (NonemptyInterval.pure t) ↔ PERF p ⟨w, t⟩ := by
  constructor
  · intro ⟨pts, hFin, hp⟩
    exact ⟨pts, hFin.2.symm, hp⟩
  · intro ⟨pts, hRB, hp⟩
    exact ⟨pts, ⟨⟨le_trans pts.fst_le_snd (le_of_eq hRB), le_of_eq hRB.symm⟩, hRB.symm⟩, hp⟩

/-- The three readings of the perfect, (1). -/
inductive PerfectType
  | universal
  | experiential
  | resultative
  deriving DecidableEq, Repr

/-- The universal perfect, (11): PERFECT over UNBOUNDED. -/
abbrev universalPerfect (P : W → Event T → Prop) : IntervalPred W T := PERF_P (UNBOUNDED P)

/-- The experiential perfect, (12): PERFECT over NEUTRAL. -/
abbrev experientialPerfect (P : W → Event T → Prop) : IntervalPred W T :=
  PERF_P (INIT_OVERLAP P)

/-- The resultative perfect, (15): PERFECT over BOUNDED, without the result state of p. 288. -/
abbrev resultativePerfect (P : W → Event T → Prop) : IntervalPred W T := PERF_P (BOUNDED P)

/-! ### The readings in Kiparsky's terms -/

/-- Map [pancheva-2003]'s perfect types to Kiparsky's readings.
    - experiential → existential (Pancheva's EXP and Kiparsky's
      existential both denote ∃-event-in-PTS without a result-state
      requirement)
    - universal → universal
    - resultative → resultative -/
def toKiparsky : PerfectType → PerfectReading
  | .experiential => .existential
  | .universal => .universal
  | .resultative => .resultative

/-- Pancheva's classification embeds into Kiparsky's: every Pancheva
    type maps to a distinct Kiparsky reading. -/
theorem pancheva_injective :
    Function.Injective toKiparsky := by
  intro a b h
  cases a <;> cases b <;> simp_all [toKiparsky]

/-- Pancheva's types are a proper subset of Kiparsky's: Kiparsky adds
    the present-state reading which Pancheva does not distinguish. -/
theorem pancheva_subset_kiparsky :
    ∀ pt : PerfectType, toKiparsky pt ∈
      [PerfectReading.existential, .universal, .resultative, .presentState] := by
  intro pt; cases pt <;> simp [toKiparsky]

end Pancheva2003
