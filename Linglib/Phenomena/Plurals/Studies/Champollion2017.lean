import Linglib.Theories.Semantics.Events.StratifiedReference
import Linglib.Theories.Semantics.Events.Mereology
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Phenomena.TenseAspect.Diagnostics

/-!
# Stratified Reference: Distributivity → Fragment Verbs
@cite{champollion-2017}

Eponymous study file connecting strata theory to concrete English
verb entries and empirical distributivity/atelicity data. Targets the
two SR specializations on which this file's data bears:

- `SSR_univ` — for-adverbial diagnostic, dim = τ runtime (atelicity)
- `SDR_univ` — adverbial-each, dim = θ role (role-distributivity)

@cite{champollion-2017} §1.2 catalogues four oppositions
(atelic/telic, stative/non-stative, distributive/collective, mass/count)
under one SR umbrella, but only the two above are exercised in the
present substrate; `SMR_univ` (mass) has no current consumer, and the
τ-dimension stativity primitive in linglib is the witness-universal
form `HasSubintervalProp` in `Tense/Aspect/SubintervalProperty.lean`,
not an SR-decomposition form.

The Fragment-side `agentSDR`/`themeSDR` Bool fields below are per-verb
typology tags; the substrate-side proof obligation `SDR_univ agentOf
seePred` requires a verb predicate denotation `Event Time → Prop`,
which Fragment files don't currently provide. Bridging tags to
substrate predicates is theory-hub denotation discipline (CLAUDE.md)
and is follow-up work; this file demonstrates the API at the *naming*
level.

## Structure

1. **Distributivity profiles** — per-verb agent/theme distributivity tags
2. **Distributivity data** — empirical collective/distributive judgments
3. **Profile → data alignment** — profiles predict empirical data
4. **VerbDistributivity postulate alignment** — tags match `SDR_univ` postulates
5. **`SSR_univ` ↔ Vendler bridge** — atelicity predictions per verb class
-/

namespace Champollion2017

open Fragments.English.Predicates.Verbal
open Semantics.Verb
open Features
open Phenomena.TenseAspect.Diagnostics (forXPrediction inXPrediction)

-- ════════════════════════════════════════════════════
-- § 1. Distributivity Profiles
-- ════════════════════════════════════════════════════

/-- Per-verb distributivity profile: whether the verb distributes
    over atomic agents and/or themes. Mirrors the postulates in
    `VerbDistributivity` from `Events/StratifiedReference.lean`. -/
structure DistProfile where
  verb : String
  agentSDR : Bool   -- distributes over atomic agents?
  themeSDR : Bool   -- distributes over atomic themes?
  deriving Repr, DecidableEq

/-- "see" distributes on both agent and theme.
    "The boys saw the movies" → each boy saw each movie. -/
def seeProfile : DistProfile :=
  { verb := "see", agentSDR := true, themeSDR := true }

/-- "kill" distributes on theme only.
    "The boys killed the chicken" → the chicken was killed (by the group). -/
def killProfile : DistProfile :=
  { verb := "kill", agentSDR := false, themeSDR := true }

/-- "meet" does NOT distribute on agent (inherently collective).
    "The boys met" does NOT entail each boy met. -/
def meetProfile : DistProfile :=
  { verb := "meet", agentSDR := false, themeSDR := false }

/-- "eat" distributes on agent (each ate something).
    "The boys ate the pizza" → each boy ate (some) the pizza. -/
def eatProfile : DistProfile :=
  { verb := "eat", agentSDR := true, themeSDR := true }

def distProfiles : List DistProfile :=
  [seeProfile, killProfile, meetProfile, eatProfile]

-- ════════════════════════════════════════════════════
-- § 2. Distributivity Data
-- ════════════════════════════════════════════════════

/-- Empirical collective/distributive ambiguity judgments. -/
structure DistDatum where
  sentence : String
  distributiveOK : Bool
  collectiveOK : Bool
  deriving Repr, DecidableEq

def seeDistDatum : DistDatum :=
  { sentence := "The boys saw the movie",
    distributiveOK := true, collectiveOK := true }

def killDistDatum : DistDatum :=
  { sentence := "The boys killed the chicken",
    distributiveOK := false, collectiveOK := true }

def meetDistDatum : DistDatum :=
  { sentence := "The boys met",
    distributiveOK := false, collectiveOK := true }

def eatDistDatum : DistDatum :=
  { sentence := "The boys ate the pizza",
    distributiveOK := true, collectiveOK := true }

def distData : List DistDatum :=
  [seeDistDatum, killDistDatum, meetDistDatum, eatDistDatum]

-- ════════════════════════════════════════════════════
-- § 3. Profile → Data Alignment
-- ════════════════════════════════════════════════════

/-! Verify that the distributivity profiles predict the empirical data:
    agentSDR = true ↔ distributive reading available. -/

/-- Agent SDR predicts distributive reading availability. -/
theorem profiles_predict_data :
    (seeProfile.agentSDR = seeDistDatum.distributiveOK) ∧
    (killProfile.agentSDR = killDistDatum.distributiveOK) ∧
    (meetProfile.agentSDR = meetDistDatum.distributiveOK) ∧
    (eatProfile.agentSDR = eatDistDatum.distributiveOK) := ⟨rfl, rfl, rfl, rfl⟩

/-- All data consistently shows collective reading is available. -/
theorem all_collective_ok :
    distData.all (λ d => d.collectiveOK) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. VerbDistributivity Postulate Alignment
-- ════════════════════════════════════════════════════

/-! The `VerbDistributivity` class from `Events/StratifiedReference.lean`
    axiomatizes `SDR_univ` for specific verbs.
    Verify our profiles match:
    - `see_agent_sdr`, `see_theme_sdr` ↔ seeProfile = (true, true)
    - `kill_theme_sdr`, `kill_agent_not_sdr` ↔ killProfile = (false, true)
    - `meet_agent_not_sdr` ↔ meetProfile.agentSDR = false -/

/-- See profile matches VerbDistributivity postulates. -/
theorem see_matches_postulates :
    seeProfile.agentSDR = true ∧ seeProfile.themeSDR = true := ⟨rfl, rfl⟩

/-- Kill profile matches VerbDistributivity postulates. -/
theorem kill_matches_postulates :
    killProfile.agentSDR = false ∧ killProfile.themeSDR = true := ⟨rfl, rfl⟩

/-- Meet profile matches VerbDistributivity postulates. -/
theorem meet_matches_postulates :
    meetProfile.agentSDR = false := rfl

/-- Fragment verb entries have the right Vendler class for SDR alignment. -/
theorem verb_vendler_for_sdr :
    see.toVerbCore.vendlerClass = some .state ∧
    kill.toVerbCore.vendlerClass = some .accomplishment ∧
    meet.toVerbCore.vendlerClass = some .achievement ∧
    eat.toVerbCore.vendlerClass = some .accomplishment :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. `SSR_univ` ↔ Vendler Bridge
-- ════════════════════════════════════════════════════

/-! `SSR_univ` connects to Vendlerian atelicity via
    `qua_incompatible_with_ssr` and `forAdverbial_requires_ssr`:
    QUA(P) + `SSR_univ` P → ⊥ at any P-event, so telic predicates
    can't have `SSR_univ`. The atelic Vendler classes (states/activities)
    are expected to have `SSR_univ` and to accept *for X*; the telic
    classes (achievements/accomplishments) are not and accept *in X*.

    We verify this through the Vendler classification of fragment verbs.
    The Bool-valued `predictsSSR` below is the per-class typology
    prediction; bridging to the substrate-side `SSR_univ` predicate on
    a verb's denotation requires a verb-side `Event Time → Prop` denotation
    (theory-hub denotation discipline; follow-up work). -/

/-- Per-verb prediction of `SSR_univ` based on Vendler class:
    state / activity → atelic; achievement / accomplishment /
    semelfactive → not atelic. -/
def predictsSSR : Option VendlerClass → Bool
  | some .state => true
  | some .activity => true
  | some .achievement => false
  | some .accomplishment => false
  | some .semelfactive => false  -- punctual, no subinterval property
  | none => false

/-- States and activities are atelic → predict SSR → accept "for X". -/
theorem atelic_classes_accept_forX :
    forXPrediction .state = .accept ∧
    forXPrediction .activity = .accept := ⟨rfl, rfl⟩

/-- Achievements and accomplishments are telic → no SSR → accept "in X". -/
theorem telic_classes_accept_inX :
    inXPrediction .achievement = .accept ∧
    inXPrediction .accomplishment = .accept := ⟨rfl, rfl⟩

/-- "sleep" (state) → SSR expected. -/
theorem sleep_ssr : predictsSSR sleep.toVerbCore.vendlerClass = true := rfl

/-- "run" (activity) → SSR expected. -/
theorem run_ssr : predictsSSR run.toVerbCore.vendlerClass = true := rfl

/-- "arrive" (achievement) → no SSR. -/
theorem arrive_no_ssr : predictsSSR arrive.toVerbCore.vendlerClass = false := rfl

/-- "eat" (accomplishment) → no SSR. -/
theorem eat_no_ssr : predictsSSR eat.toVerbCore.vendlerClass = false := rfl

/-- "see" (state) → SSR expected. -/
theorem see_ssr : predictsSSR see.toVerbCore.vendlerClass = true := rfl

end Champollion2017
