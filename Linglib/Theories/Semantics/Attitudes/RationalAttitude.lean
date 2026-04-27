import Linglib.Core.Discourse.IllocutionaryForce
import Linglib.Core.Discourse.Intentionality
import Linglib.Core.Discourse.Commitment
import Linglib.Theories.Semantics.Attitudes.Doxastic
import Linglib.Theories.Semantics.Events.Basic
import Linglib.Theories.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Rational Attitude Semantics @cite{fusco-sgrizzi-2026}
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

## Denotation (@cite{fusco-sgrizzi-2026}, ex. 24)

⟦convincere⟧ = λP.λx.λy.λe. ∃e'. Convince(e) ∧ Agent(e,y) ∧ Patient(e,x)
                                   ∧ CAUSE(e,e') ∧ RATIONAL-ATTITUDE(e')
                                   ∧ Experiencer(x,e') ∧ P(e')

The parameter P is determined by complement size:
- *di*-infinitive (CP): P = CLOSURE(λe. VP(e)) — existentially closed
- *a*-infinitive (aP): P = λe. VP(e) — event variable open

-/

namespace Semantics.Attitudes.RationalAttitude

open Semantics.Events (Ev EvPredW existsClosureW EventSort)
open Minimalist (ComplementSize fValue)

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
  deriving DecidableEq, Repr

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
    name used in @cite{fusco-sgrizzi-2026}. -/
abbrev closure {W Time : Type*} [LinearOrder Time] := @existsClosureW W Time _

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
structure CausativeAttitude (E Time : Type*) [LinearOrder Time] where
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
def CausativeAttitude.denote {E Time : Type*} [LinearOrder Time]
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
def CausativeAttitude.beliefReading {E Time : Type*} [LinearOrder Time]
    (v : CausativeAttitude E Time) (embeddedVP : Ev Time → Prop) : Prop :=
  v.denote (λ _ => ∃ e'' : Ev Time, embeddedVP e'')

/-- Intention reading: no CLOSURE — the embedded VP is applied directly as an
    event predicate. The attitude is evaluated via INERTIA. -/
def CausativeAttitude.intentionReading {E Time : Type*} [LinearOrder Time]
    (v : CausativeAttitude E Time) (embeddedVP : Ev Time → Prop) : Prop :=
  v.denote embeddedVP

/-- Both readings are instances of the same `denote` applied to different P.
    This is the paper's central formal claim (ex. 24): *convincere* has ONE
    denotation; the belief/intention split is compositional, arising from
    complement size (CP triggers CLOSURE, sub-CP does not). -/
theorem CausativeAttitude.readings_from_single_denote {E Time : Type*} [LinearOrder Time]
    (v : CausativeAttitude E Time) (VP : Ev Time → Prop) :
    v.beliefReading VP = v.denote (fun _ => ∃ e, VP e) ∧
    v.intentionReading VP = v.denote VP :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 3b. CAUSE* — Causal Self-Reference (@cite{grano-2024})
-- ════════════════════════════════════════════════════════════════

/-- CAUSE*(s, e, w): causal self-reference relation (@cite{grano-2024}, (79);
    @cite{searle-1983}).

    The attitude state `s` causally brings about event `e` in world `w`
    "in the right way." Distinguished from plain CAUSE by requiring that
    the causation proceed via the agent's intention-in-action, not via
    a deviant causal chain (@cite{harman-1976}; @cite{chisholm-1966}).

    Example (Harman): Betty aims her gun intending to kill the target.
    Her intention makes her nervous; nervousness causes her to pull the
    trigger; the target is killed. The outcome was caused by the intention,
    but not "in the right way" — the causal chain was deviant. CAUSE*
    would not hold, correctly predicting that Betty did not carry out
    her intention. -/
abbrev CauseStar (W Time : Type*) [LinearOrder Time] := Ev Time → Ev Time → W → Prop

/-- Semantics for intention reports with causal self-reference
    (@cite{grano-2024}, version 4, (79)).

    ⟦Kim intends to leave⟧ᵂ·ᵗ =
      ∃s. INTENTION(s,w) ∧ HOLDER(k,s,w)
        ∧ ∀⟨w',x⟩ ∈ CONTENT(s):
            ∃e. CAUSE*(s,e,w') ∧ P(x,w',e)

    The complement `P` has type `(E → W → Ev Time → Prop)` — an event
    predicate with an open eventuality argument. This is the formal
    correlate of @cite{grano-2024}'s Premise 3: IND would existentially
    close the event argument, yielding `(E → W → Prop)`, which is
    type-incompatible with CAUSE*. The type system enforces that
    intention reports require eventuality abstraction. -/
def intentionHolds {E W Time : Type*} [LinearOrder Time]
    (isIntention : Ev Time → W → Prop)
    (holder : E → Ev Time → W → Prop)
    (content : Ev Time → Set (W × E))
    (causeStar : CauseStar W Time)
    (agent : E) (P : E → W → Ev Time → Prop) (w : W) : Prop :=
  ∃ s : Ev Time,
    s.sort = .state ∧
    isIntention s w ∧
    holder agent s w ∧
    ∀ p ∈ content s, ∃ e : Ev Time, causeStar s e p.1 ∧ P p.2 p.1 e

/-- Plain belief reports do NOT require CAUSE*: the complement is a
    proposition (event argument already closed by IND), so there is no
    event for CAUSE* to bind.

    ⟦Kim believes that Sandy left⟧ᵂ =
      ∀w' ∈ DOX(k,w): P(w')

    The contrast in complement type — `(W → Prop)` for belief vs
    `(E → W → Ev Time → Prop)` for intention — is what makes 'believe'
    indicative-selecting and 'intend' subjunctive-selecting. -/
def beliefHolds {E W : Type*}
    (dox : E → W → Set W)
    (agent : E) (P : W → Prop) (w : W) : Prop :=
  ∀ w' ∈ dox agent w, P w'

/-! ### Premise 3: Type-Level Enforcement (@cite{grano-2024}, §4.3)

Intention reports require eventuality abstraction: `intentionHolds`
demands a complement with an open event argument (`P : E → W → Ev Time → Prop`),
while `beliefHolds` takes a closed proposition (`P : W → Prop`).

Indicative mood existentially closes the event argument ((87)),
yielding `W → Prop`, which is type-incompatible with `intentionHolds`.
Only subjunctive/nonfinite clauses leave the event argument open,
enabling the `E → W → Ev Time → Prop` type that CAUSE* requires.

The distinction is enforced by construction — no theorem is needed
because you literally cannot pass a `W → Prop` where
`E → W → Ev Time → Prop` is expected. The Lean type checker is the proof.
-/

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

-- ════════════════════════════════════════════════════════════════
-- § 6. Bridge: Reading → @cite{searle-1983} Direction of Fit
-- ════════════════════════════════════════════════════════════════

open Core.Discourse (DirectionOfFit PsychMode)

/-- Map rational attitude readings to @cite{searle-1983}'s direction of fit.

    Belief readings have mind-to-world fit: the propositional content must
    match independently existing reality. Intention readings have
    world-to-mind fit: reality must be changed to match the content. -/
def Reading.directionOfFit : Reading → DirectionOfFit
  | .belief    => .mindToWorld
  | .intention => .worldToMind

/-- Map rational attitude readings to @cite{searle-1983}'s psychological mode.

    This connects @cite{fusco-sgrizzi-2026}'s complement-size analysis to
    Searle's theory of Intentional states: the same verb produces different
    psychological modes depending on syntactic complement structure. -/
def Reading.psychMode : Reading → PsychMode
  | .belief    => .belief
  | .intention => .intention

/-- The direction of fit derived from the reading matches the direction
    derived from the corresponding psychological mode. -/
theorem reading_direction_matches_psychMode :
    ∀ r : Reading, r.directionOfFit = r.psychMode.directionOfFit := by
  intro r; cases r <;> rfl

/-- Belief readings are not causally self-referential; intention readings are.
    This is the formal correlate of @cite{fusco-sgrizzi-2026}'s CONTENT vs
    INERTIA modal base distinction: INERTIA worlds are those where the agent's
    intentions *cause* the events to come about. -/
theorem intention_self_referential_belief_not :
    Reading.intention.psychMode.causalSelfRef = .stateToWorld ∧
    Reading.belief.psychMode.causalSelfRef = .none :=
  ⟨rfl, rfl⟩

end Semantics.Attitudes.RationalAttitude
