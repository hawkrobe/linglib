import Linglib.Data.Examples.Schema
import Linglib.Theories.Semantics.Aspect.Basic
import Linglib.Phenomena.TenseAspect.Studies.Kiparsky2002

/-!
# @cite{pancheva-2003}: The aspectual makeup of Perfect participles and the interpretations of the Perfect
@cite{pancheva-2003} @cite{kiparsky-2002} @cite{iatridou-anagnostopoulou-izvorski-2001}

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

The Lean substrate `Theories/Semantics/Aspect/Core.lean` already
provides `PerfectType` (Pancheva's 3-type enum) plus the
`universalPerfect` / `experientialPerfect` / `resultativePerfect`
operators built on `PERF_P` over `UNBOUNDED` / `INIT_OVERLAP` /
`BOUNDED` aspect; these are the general substrate Pancheva's
analysis uses.

-/

namespace Phenomena.TenseAspect.Studies.Pancheva2003

open Data.Examples (LinguisticExample)
open Semantics.Aspect (PerfectType)
open Phenomena.TenseAspect.Studies.Kiparsky2002 (PerfectReading)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/Pancheva2003.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def ex1a_U : LinguisticExample :=
  { id := "pancheva2003_ex1a_U"
    source := ⟨"pancheva-2003", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 2000, Alexandra has lived in LA."
    discourseSegments := []
    glossedTokens := []
    translation := "Since 2000, Alexandra has lived in LA."
    context := "Universal (U) perfect. Asserts that the underlying eventuality (live in LA) holds throughout an interval delimited by 2000 (LB) and the utterance time (RB). Requires adverbial modification (here: `since 2000`)."
    judgment := .acceptable
    alternatives := []
    readings := [("universal (live-in-LA holds throughout 2000-now)", .acceptable)]
    paperFeatures := []
    comment := "Pancheva 2003 §1 ex (1a). One of the three canonical perfect-reading exemplars. Universal reading requires stative or progressive participial aspect (Pancheva §2 thesis)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1b_EXP : LinguisticExample :=
  { id := "pancheva2003_ex1b_EXP"
    source := ⟨"pancheva-2003", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alexandra has been in LA (before)."
    discourseSegments := []
    glossedTokens := []
    translation := "Alexandra has been in LA (before)."
    context := "Experiential (EXP) perfect. Asserts that the underlying eventuality holds at a proper subset of an interval extending back from the utterance time. No claim about the eventuality holding now."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (LA-being at some past subinterval)", .acceptable)]
    paperFeatures := []
    comment := "Pancheva 2003 §1 ex (1b). Subsumed under EXISTENTIAL by McCawley 1971, Mittwoch 1988 (umbrella for Experiential + Resultative); Pancheva keeps the finer Experiential/Resultative distinction."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1c_RES : LinguisticExample :=
  { id := "pancheva2003_ex1c_RES"
    source := ⟨"pancheva-2003", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alexandra has (just) arrived in LA."
    discourseSegments := []
    glossedTokens := []
    translation := "Alexandra has (just) arrived in LA."
    context := "Resultative (RES) perfect. Same temporal assertion as Experiential, with the added meaning that the result state (be in LA) holds at the utterance time."
    judgment := .acceptable
    alternatives := []
    readings := [("resultative (arrived + still in LA at utterance)", .acceptable)]
    paperFeatures := []
    comment := "Pancheva 2003 §1 ex (1c). The Resultative reading requires a telic predicate (Kratzer 1994: only telic events have a natural result state); see (5)/(6) for the telic vs atelic contrast."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex5a_atelic : LinguisticExample :=
  { id := "pancheva2003_ex5a_atelic"
    source := ⟨"pancheva-2003", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have run."
    discourseSegments := []
    glossedTokens := []
    translation := "I have run."
    context := "Atelic activity participle (`run`). Cannot yield a Resultative reading because activities have no inherent result state (Kratzer 1994). Only the Experiential reading is available."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (running at some past time)", .acceptable), ("resultative", .ungrammatical)]
    paperFeatures := []
    comment := "Pancheva 2003 §2 ex (5a). Diagnostic for the telic-only restriction on Resultative reading."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex6a_telic : LinguisticExample :=
  { id := "pancheva2003_ex6a_telic"
    source := ⟨"pancheva-2003", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have lost my glasses."
    discourseSegments := []
    glossedTokens := []
    translation := "I have lost my glasses."
    context := "Telic achievement participle (`lose my glasses`). Has both Experiential and Resultative readings. On the Resultative reading, the glasses must still be lost at the utterance time; on the Experiential reading, no such requirement."
    judgment := .acceptable
    alternatives := []
    readings := [("experiential (lost at some past time)", .acceptable), ("resultative (lost + still missing now)", .acceptable)]
    paperFeatures := []
    comment := "Pancheva 2003 §2 ex (6a). The telic contrast partner to (5a). Demonstrates that telic predicates license both readings; atelic predicates only EXP."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1a_U, ex1b_EXP, ex1c_RES, ex5a_atelic, ex6a_telic]

end Examples
-- END GENERATED EXAMPLES


-- ════════════════════════════════════════════════════════════════
-- § Pancheva → Kiparsky bridge (moved from Studies/Kiparsky2002.lean)
-- ════════════════════════════════════════════════════════════════

/-- Map @cite{pancheva-2003}'s perfect types to Kiparsky's readings.
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

end Phenomena.TenseAspect.Studies.Pancheva2003
