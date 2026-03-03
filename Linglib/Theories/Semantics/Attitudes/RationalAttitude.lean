import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Theories.Semantics.Events.Basic
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# Rational Attitude Semantics @cite{fusco-sgrizzi-2025}
@cite{dowty-1979}

Unified semantics for attitude verbs that support both belief and intention
readings. The key insight: these are not two separate verb types but a single
verb whose interpretation is determined by complement structure.

## Core Idea

A *rational attitude* is a mental state that can be either:
- **Belief**: a propositional attitude evaluated via CONTENT (doxastic modal base)
- **Intention**: a sub-propositional attitude evaluated via INERTIA (inertial modal base)

The difference is determined by **complement size**:
- CP complement → CLOSURE applies → propositional content → belief
- Sub-CP complement → event variable open → intention

## Denotation (@cite{fusco-sgrizzi-2025}, ex. 24)

⟦convincere⟧ = λP.λx.λy.λe. ∃e'. Convince(e) ∧ Agent(e,y) ∧ Patient(e,x)
                                   ∧ CAUSE(e,e') ∧ RATIONAL-ATTITUDE(e')
                                   ∧ Experiencer(x,e') ∧ P(e')

The parameter P is determined by complement size:
- *di*-infinitive (CP): P = CLOSURE(λe. VP(e)) — existentially closed
- *a*-infinitive (aP): P = λe. VP(e) — event variable open

-/

namespace Semantics.Attitudes.RationalAttitude

open Semantics.Events (Ev EvPredW existsClosureW EventSort)
open Minimalism (ComplementSize fValue)

-- ════════════════════════════════════════════════════════════════
-- § 1. Rational Attitude Reading
-- ════════════════════════════════════════════════════════════════

/-- The two readings of a rational attitude verb, determined by complement size.

    - `belief`: complement is propositional (existentially closed by CLOSURE);
      evaluated via CONTENT modal base (doxastic alternatives)
    - `intention`: complement is sub-propositional (event variable open);
      evaluated via INERTIA modal base (normal continuation) -/
inductive Reading where
  | belief
  | intention
  deriving DecidableEq, Repr, BEq

/-- Map complement size to rational attitude reading.

    CP-sized complements (fLevel ≥ 6) trigger CLOSURE, yielding a propositional
    content suitable for belief evaluation. Sub-CP complements leave the event
    variable unsaturated, producing an intention reading via INERTIA. -/
def readingFromSize (cs : ComplementSize) : Reading :=
  if cs.fLevel ≥ 6 then .belief else .intention

-- ════════════════════════════════════════════════════════════════
-- § 2. Complement Size → Reading Theorems
-- ════════════════════════════════════════════════════════════════

theorem cp_yields_belief : readingFromSize .cP = .belief := by decide
theorem tp_yields_intention : readingFromSize .tP = .intention := by decide
theorem vp_yields_intention : readingFromSize .vP = .intention := by decide
theorem belief_ne_intention : Reading.belief ≠ Reading.intention := nofun

/-- Complement size determines reading: CP boundary is the threshold.
    This formalizes Fusco & Sgrizzi's structural size hypothesis. -/
theorem size_determines_reading (cs : ComplementSize) :
    readingFromSize cs = .belief ↔ cs.fLevel ≥ 6 := by
  constructor
  · intro h
    unfold readingFromSize at h
    split at h
    · assumption
    · exact absurd h nofun
  · intro h
    unfold readingFromSize
    simp [h]

-- ════════════════════════════════════════════════════════════════
-- § 3. CLOSURE Operator
-- ════════════════════════════════════════════════════════════════

/-- CLOSURE: existential closure of the event variable at the CP level.

    For CP complements, CLOSURE converts an event predicate P(e) into a
    proposition ∃e. P(e), yielding a belief-compatible propositional content.

    This is `existsClosureW` from event semantics, re-exported under the
    name used in @cite{fusco-sgrizzi-2025}. -/
abbrev closure {W Time : Type*} [LE Time] := @existsClosureW W Time _

-- ════════════════════════════════════════════════════════════════
-- § 4. Causative Attitude Verb (convincere-type)
-- ════════════════════════════════════════════════════════════════

/-- A causative attitude verb: Agent causes Experiencer to enter a rational
    attitude state whose content is determined by complement P.

    ⟦convincere⟧ = λP.λx.λy.λe. ∃e'. VerbPred(e) ∧ Agent(e,y)
      ∧ Patient(e,x) ∧ CAUSE(e,e') ∧ RATIONAL-ATTITUDE(e')
      ∧ Experiencer(x,e') ∧ P(e')

    The parameter P is supplied by the complement:
    - CP (*di*): CLOSURE applied → P is propositional (belief)
    - Sub-CP (*a*): P is an event predicate (intention) -/
structure CausativeAttitude (E Time : Type*) [LE Time] where
  /-- The verb's descriptive predicate (e.g., Convince) -/
  verbPred : Ev Time → Prop
  /-- The agent of the matrix event -/
  agent : E
  /-- The patient/experiencer who enters the attitude -/
  experiencer : E
  /-- Agent thematic role -/
  isAgent : Ev Time → E → Prop
  /-- Patient thematic role -/
  isPatient : Ev Time → E → Prop
  /-- Experiencer thematic role (on the attitude event) -/
  isExperiencer : Ev Time → E → Prop
  /-- CAUSE(e, e'): the matrix event e causally brings about the attitude
      state e'. Abstract relation; instantiated per verb/scenario. -/
  cause : Ev Time → Ev Time → Prop

/-- Semantics of a causative attitude verb applied to complement P.

    Returns a proposition existentially closed over both the matrix
    event and the resulting attitude event. -/
def CausativeAttitude.denote {E Time : Type*} [LE Time]
    (v : CausativeAttitude E Time) (P : Ev Time → Prop) : Prop :=
  ∃ e e' : Ev Time,
    v.verbPred e ∧
    v.isAgent e v.agent ∧
    v.isPatient e v.experiencer ∧
    v.cause e e' ∧
    e'.sort = .state ∧  -- Rational attitudes are stative
    v.isExperiencer e' v.experiencer ∧
    P e'

/-- Belief reading: CLOSURE applies to the embedded VP, yielding a proposition.
    The attitude is evaluated via CONTENT (doxastic alternatives). -/
def CausativeAttitude.beliefReading {E Time : Type*} [LE Time]
    (v : CausativeAttitude E Time) (embeddedVP : Ev Time → Prop) : Prop :=
  v.denote (λ _ => ∃ e'' : Ev Time, embeddedVP e'')

/-- Intention reading: no CLOSURE — the embedded VP is applied directly as an
    event predicate. The attitude is evaluated via INERTIA. -/
def CausativeAttitude.intentionReading {E Time : Type*} [LE Time]
    (v : CausativeAttitude E Time) (embeddedVP : Ev Time → Prop) : Prop :=
  v.denote embeddedVP

/-- Both readings are instances of the same `denote` applied to different P.
    This is the paper's central formal claim (ex. 24): *convincere* has ONE
    denotation; the belief/intention split is compositional, arising from
    complement size (CP triggers CLOSURE, sub-CP does not). -/
theorem CausativeAttitude.readings_from_single_denote {E Time : Type*} [LE Time]
    (v : CausativeAttitude E Time) (VP : Ev Time → Prop) :
    v.beliefReading VP = v.denote (fun _ => ∃ e, VP e) ∧
    v.intentionReading VP = v.denote VP :=
  ⟨rfl, rfl⟩

-- TODO: Formalize CAUSE*(s, e, w') — causal self-referentiality (Searle 1983;
-- Grano 2024). In the paper's (25), *a* contributes CAUSE*(s, e, w') requiring
-- the attitude state s to causally bring about event e in inertia world w'.
-- This distinguishes intentions (world-to-mind fit) from beliefs (mind-to-world).
-- Requires world-parameterized events; deferred until Events/ supports this.

-- ════════════════════════════════════════════════════════════════
-- § 5. Diagnostics
-- ════════════════════════════════════════════════════════════════

/-- Truth assessment is available for belief readings but not intention readings.
    "It's true/false" can felicitously evaluate a belief but not an intention. -/
def truthAssessable : Reading → Bool
  | .belief => true
  | .intention => false

/-- Modal auxiliaries can appear in CP complements (belief) but not in
    sub-CP complements (intention). The CP provides the structural space
    to host modal heads (Mod, F-level 2). -/
def allowsModalAux : Reading → Bool
  | .belief => true
  | .intention => false

/-- Intention readings are obligatorily future-oriented: the intended event
    is projected into inertia worlds (future continuation). Belief readings
    have no temporal constraint (they can be about past, present, or future). -/
def forcedFutureOrientation : Reading → Bool
  | .belief => false
  | .intention => true

/-- Object control is obligatory for intention readings: the experiencer
    must be the agent of the intended event. Belief readings allow both
    subject and object control configurations. -/
def objectControlOnly : Reading → Bool
  | .belief => false
  | .intention => true

theorem diagnostics_distinguish_readings :
    truthAssessable .belief = true ∧
    allowsModalAux .belief = true ∧
    forcedFutureOrientation .belief = false ∧
    objectControlOnly .belief = false ∧
    truthAssessable .intention = false ∧
    allowsModalAux .intention = false ∧
    forcedFutureOrientation .intention = true ∧
    objectControlOnly .intention = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Semantics.Attitudes.RationalAttitude
