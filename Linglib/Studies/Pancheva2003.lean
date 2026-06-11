import Linglib.Data.Examples.Schema
import Linglib.Semantics.Aspect.Basic
import Linglib.Studies.Kiparsky2002
import Linglib.Data.Examples.Pancheva2003

/-!
# [pancheva-2003]: The aspectual makeup of Perfect participles and the interpretations of the Perfect
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

The Lean substrate `Semantics/Aspect/Core.lean` already
provides `PerfectType` (Pancheva's 3-type enum) plus the
`universalPerfect` / `experientialPerfect` / `resultativePerfect`
operators built on `PERF_P` over `UNBOUNDED` / `INIT_OVERLAP` /
`BOUNDED` aspect; these are the general substrate Pancheva's
analysis uses.

-/

namespace Pancheva2003

open Data.Examples (LinguisticExample)
open Semantics.Aspect (PerfectType)
open Kiparsky2002 (PerfectReading)

-- ════════════════════════════════════════════════════════════════
-- § Pancheva → Kiparsky bridge (moved from Studies/Kiparsky2002.lean)
-- ════════════════════════════════════════════════════════════════

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
