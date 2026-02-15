/-
# Agentivity Decomposition (Cruse 1973)

Cruse (1973) "Some Thoughts on Agentivity" argues that agentivity is not a
single feature but decomposes into 4 independent sub-features:

| Feature    | Cruse's gloss                         | Example              |
|------------|---------------------------------------|----------------------|
| volitive   | an act of will is stated or implied   | John deliberately…   |
| effective  | force from position/motion/energy     | The bullet smashed…  |
| initiative | initiating action by command          | The warder marched…  |
| agentive   | using own body's internal energy      | John ran             |

The **do-test** ("NP did something") passes iff at least one feature is
present. Parsons' (1990) neo-Davidsonian `agent` role captures specifically
the `agentive` sub-feature (own energy + dynamic), which is strictly
narrower than passing the do-test.

This module formalizes the decomposition and connects it to:
- `ThematicRoles.ThematicFrame.agent` (Parsons 1990)
- `CoerciveImplication.ActionType` (Nadathur & Lauer 2020)
- `CausativeBuilder` (initiative ↔ causative constructions)
- `VendlerClass` / `DiagnosticResult` (aspect diagnostics)

## References

- Cruse, D. A. (1973). Some Thoughts on Agentivity. Journal of
  Linguistics 9(1), 11–23.
- Parsons, T. (1990). Events in the Semantics of English.
- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. Glossa 5(1), 49.
-/

import Linglib.Theories.EventSemantics.ThematicRoles
import Linglib.Theories.IntensionalSemantics.Causative.CoerciveImplication
import Linglib.Theories.IntensionalSemantics.Causative.Builder
import Linglib.Phenomena.Aspect.DiagnosticsBridge

namespace EventSemantics.Agentivity

open EventSemantics
open EventSemantics.ThematicRoles
open NadathurLauer2020.CoerciveImplication
open NadathurLauer2020.Builder
open Core.Time
open TruthConditional.Verb.Aspect
open Phenomena.Aspect.Diagnostics

-- ════════════════════════════════════════════════════
-- § 1. Agentivity Features (Cruse 1973 §pp.17–21)
-- ════════════════════════════════════════════════════

/-- The four independent sub-features of agentivity (Cruse 1973 §pp.17–21).

    Cruse argues that "agentivity" is not a single binary feature but
    decomposes into at least four independent components, each with
    distinct linguistic diagnostics. -/
inductive AgentivityFeature where
  /-- **Volitive**: an act of will is stated or implied (Cruse p.18).
      "John deliberately drifted downstream." -/
  | volitive
  /-- **Effective**: force deriving from position, motion, or kinetic
      energy (Cruse p.19). "The bullet smashed the collar-bone." -/
  | effective
  /-- **Initiative**: initiating action by command or instruction to
      another agent (Cruse p.19). "The warder marched the prisoners." -/
  | initiative
  /-- **Agentive**: use of one's own body's internal energy source
      (Cruse p.20). "John ran." The prototypical agent feature. -/
  | agentive_
  deriving DecidableEq, Repr, BEq

/-- An agentivity profile assigns Prop-valued feature predicates over
    entity–event pairs for each of Cruse's four sub-features.

    Each field `hasF x e` means "entity x exhibits feature F in event e". -/
structure AgentivityProfile (Entity Time : Type*) [LE Time] where
  /-- Does x exhibit an act of will in e? -/
  hasVolitive : Entity → Ev Time → Prop
  /-- Does x exert force (from position/motion/energy) in e? -/
  hasEffective : Entity → Ev Time → Prop
  /-- Does x initiate action by command/instruction in e? -/
  hasInitiative : Entity → Ev Time → Prop
  /-- Does x use own body's internal energy in e? -/
  hasAgentive : Entity → Ev Time → Prop

-- ════════════════════════════════════════════════════
-- § 2. The Do-Test (Cruse 1973 §pp.13–14)
-- ════════════════════════════════════════════════════

/-- The do-test (Cruse 1973 §pp.13–14): "NP VP" entails "NP did something"
    iff at least one agentivity sub-feature is present.

    This is the disjunction of all four features. -/
def passesDoTest {Entity Time : Type*} [LE Time]
    (x : Entity) (e : Ev Time)
    (profile : AgentivityProfile Entity Time) : Prop :=
  profile.hasVolitive x e ∨ profile.hasEffective x e ∨
  profile.hasInitiative x e ∨ profile.hasAgentive x e

/-- The do-test is equivalent to the 4-way disjunction (definitional). -/
theorem passesDo_iff_or {Entity Time : Type*} [LE Time]
    (x : Entity) (e : Ev Time) (p : AgentivityProfile Entity Time) :
    passesDoTest x e p ↔
    (p.hasVolitive x e ∨ p.hasEffective x e ∨
     p.hasInitiative x e ∨ p.hasAgentive x e) :=
  Iff.rfl

-- ════════════════════════════════════════════════════
-- § 3. Feature Independence (Cruse's key examples)
-- ════════════════════════════════════════════════════

/-- Axiom class witnessing that the four agentivity features are
    logically independent: each can be present without the others.

    - `volitive_without_agentive`: "John deliberately drifted downstream"
      (will present, no own-energy expenditure)
    - `effective_without_volitive`: "The bullet smashed the collar-bone"
      (force present, no will)
    - `initiative_without_agentive_`: "The warder marched the prisoners"
      (command present, prisoners do the marching)
    - `agentive_without_initiative`: "John ran"
      (own energy, no command to another) -/
class CruseIndependence (Entity Time : Type*) [LE Time]
    (profile : AgentivityProfile Entity Time) where
  /-- Volitive without agentive: "John deliberately drifted downstream" -/
  volitive_without_agentive :
    ∃ (x : Entity) (e : Ev Time),
      profile.hasVolitive x e ∧ ¬ profile.hasAgentive x e
  /-- Effective without volitive: "The bullet smashed the collar-bone" -/
  effective_without_volitive :
    ∃ (x : Entity) (e : Ev Time),
      profile.hasEffective x e ∧ ¬ profile.hasVolitive x e
  /-- Initiative without agentive: "The warder marched the prisoners" -/
  initiative_without_agentive_ :
    ∃ (x : Entity) (e : Ev Time),
      profile.hasInitiative x e ∧ ¬ profile.hasAgentive x e
  /-- Agentive without initiative: "John ran" -/
  agentive_without_initiative :
    ∃ (x : Entity) (e : Ev Time),
      profile.hasAgentive x e ∧ ¬ profile.hasInitiative x e

-- ════════════════════════════════════════════════════
-- § 4. Bridge to ThematicFrame.agent (Parsons 1990)
-- ════════════════════════════════════════════════════

/-- Link between Parsons' `agent` role and Cruse's `agentive_` sub-feature.

    The Parsonian `agent(x,e)` captures specifically the own-energy
    sub-feature: an agent uses its own body's internal energy source.
    This is strictly narrower than the full do-test. -/
class AgentAgentiveLink (Entity Time : Type*) [LE Time]
    (frame : ThematicFrame Entity Time)
    (profile : AgentivityProfile Entity Time) where
  /-- Parsons' agent implies Cruse's agentive_ feature. -/
  agent_implies_agentive : ∀ (x : Entity) (e : Ev Time),
    frame.agent x e → profile.hasAgentive x e

/-- Parsons' agent(x,e) entails passesDoTest(x,e), since agentive_ is
    one of the four disjuncts.

    In any model where agent → hasAgentive, the result follows
    immediately from the fact that agentive_ is the fourth disjunct. -/
theorem agent_implies_passesDo {Entity Time : Type*} [LE Time]
    {frame : ThematicFrame Entity Time}
    {profile : AgentivityProfile Entity Time}
    [link : AgentAgentiveLink Entity Time frame profile]
    (x : Entity) (e : Ev Time)
    (h : frame.agent x e) :
    passesDoTest x e profile := by
  exact Or.inr (Or.inr (Or.inr (link.agent_implies_agentive x e h)))

/-- Parsons' `agent` role captures specifically Cruse's `agentive_`
    sub-feature (own energy, dynamic), not the full do-test notion.

    This is stated as: any model satisfying `AgentAgentiveLink` and
    `ThematicAxioms` has agent entail agentive_ (from the link) and
    agent entail action (from the axioms). Together these characterize
    the prototypical "own-energy + dynamic" combination. -/
theorem agent_is_agentive_subfeature {Entity Time : Type*} [LE Time]
    {frame : ThematicFrame Entity Time}
    {profile : AgentivityProfile Entity Time}
    [link : AgentAgentiveLink Entity Time frame profile]
    [ax : ThematicAxioms Entity Time frame]
    (x : Entity) (e : Ev Time)
    (h : frame.agent x e) :
    profile.hasAgentive x e ∧ e.sort = .action :=
  ⟨link.agent_implies_agentive x e h, ax.agent_selects_action x e h⟩

-- ════════════════════════════════════════════════════
-- § 5. Bridge to ActionType (CoerciveImplication)
-- ════════════════════════════════════════════════════

/-- Map agentivity features to CoerciveImplication's ActionType.

    - volitive → Volitional (Cruse: act of will ↔ N&L: volitional action)
    - effective → NonVolitional (force without will)
    - initiative → Volitional (initiating by command is volitional for initiator)
    - agentive_ → Ambiguous (own energy can be volitional or habitual) -/
def AgentivityFeature.toActionType : AgentivityFeature → ActionType
  | .volitive   => .Volitional
  | .effective   => .NonVolitional
  | .initiative  => .Volitional
  | .agentive_   => .Ambiguous

/-- Volitive maps to Volitional. -/
theorem volitive_toActionType :
    AgentivityFeature.volitive.toActionType = .Volitional := rfl

/-- Effective maps to NonVolitional. -/
theorem effective_toActionType :
    AgentivityFeature.effective.toActionType = .NonVolitional := rfl

/-- Initiative maps to Volitional. -/
theorem initiative_toActionType :
    AgentivityFeature.initiative.toActionType = .Volitional := rfl

/-- Agentive maps to Ambiguous. -/
theorem agentive_toActionType :
    AgentivityFeature.agentive_.toActionType = .Ambiguous := rfl

/-- Coercive implication (N&L 2020) arises exactly when the causee's
    action is volitional — i.e., when the causee has at least the
    volitive sub-feature.

    This bridges Cruse's agentivity decomposition to N&L's coercion
    analysis: "X made Y do Z" implies coercion when Z is volitional
    for Y, which Cruse would analyze as Y having the volitive feature. -/
theorem coercion_requires_volitive :
    ∀ (f : AgentivityFeature),
      f.toActionType = .Volitional ↔
      (f = .volitive ∨ f = .initiative) := by
  intro f
  cases f <;> simp [AgentivityFeature.toActionType]

-- ════════════════════════════════════════════════════
-- § 6. Bridge to CausativeBuilder (Initiative)
-- ════════════════════════════════════════════════════

/-- Cruse's initiative feature (initiating action by command) corresponds
    to causative constructions where the subject causes an agentive action
    by the object.

    "The warder marched the prisoners" → the warder has initiative,
    the prisoners are the agentive doers. This pattern is lexicalized by
    `CausativeBuilder.make` and `.force`: the subject (causer) initiates,
    the object (causee) performs the action.

    The bridge: initiative ↔ {make, force} builders, where the causer
    has initiative and the causee has agentive_. -/
structure InitiativeCausativeLink (Entity Time : Type*) [LE Time]
    (profile : AgentivityProfile Entity Time) where
  /-- In a causative construction, the causer has initiative. -/
  causer_has_initiative : ∀ (causer causee : Entity) (e : Ev Time),
    profile.hasInitiative causer e → ¬ profile.hasAgentive causer e →
    -- The causee is the one with agentive_ (doing the action)
    profile.hasAgentive causee e

/-- The force builder is coercive — it lexicalizes coercion of a
    volitional causee, which is precisely the initiative pattern
    where the initiator overrides the causee's will. -/
theorem force_lexicalizes_coercive_initiative :
    CausativeBuilder.force.isCoercive = true := rfl

/-- The make builder asserts sufficiency — the initiator's action
    is sufficient for the causee to act. -/
theorem make_lexicalizes_sufficient_initiative :
    CausativeBuilder.make.assertsSufficiency = true := rfl

-- ════════════════════════════════════════════════════
-- § 7. Stative Do-Verbs (Challenge to agent_selects_action)
-- ════════════════════════════════════════════════════

/-- There exist stative eventualities that pass the do-test.

    Witness: "John is standing" — volitive (John can stop standing)
    but stative (no change over the interval). The do-test passes
    via the volitive feature, even though e.sort = .state.

    This shows the do-test is strictly broader than Parsons' `agent`
    role, which requires e.sort = .action. -/
theorem stative_can_pass_doTest :
    ∃ (profile : AgentivityProfile Unit ℤ) (x : Unit) (e : Ev ℤ),
      e.sort = .state ∧ passesDoTest x e profile := by
  -- Witness: a profile where () has volitive in a stative event
  refine ⟨⟨λ _ _ => True, λ _ _ => False, λ _ _ => False, λ _ _ => False⟩,
          (), ⟨⟨0, 10, by omega⟩, .state⟩, rfl, ?_⟩
  exact Or.inl trivial

/-- Parsons' `agent_selects_action` is NOT contradicted by stative
    do-verbs, because `agent` captures the narrower `agentive_`
    feature (own energy → dynamic), while the do-test also detects
    `volitive` which can apply to states.

    Formally: given `ThematicAxioms` (which assert agent → action),
    and `AgentAgentiveLink` (which assert agent → agentive_), if an
    entity is agent of a stative event we get a contradiction — so
    no stative event has a Parsonian agent. The do-test still passes
    for statives via other features (volitive, effective). -/
theorem agent_selects_action_consistent {Entity Time : Type*} [LE Time]
    {frame : ThematicFrame Entity Time}
    [ax : ThematicAxioms Entity Time frame]
    (x : Entity) (e : Ev Time)
    (hState : e.sort = .state)
    (hAgent : frame.agent x e) :
    False := by
  have hAction := ax.agent_selects_action x e hAgent
  rw [hState] at hAction
  exact absurd hAction (by decide)

-- ════════════════════════════════════════════════════
-- § 8. Diagnostic Predictions
-- ════════════════════════════════════════════════════

/-- Predict the do-test result for each Vendler class.

    - **State** → marginal: some pass (stand, sit, hold — via volitive)
      but most don't (know, love — no agentivity features)
    - **Activity** → accept: paradigmatic do-sentences ("John ran" →
      "What John did was run")
    - **Achievement** → marginal: some pass ("die in order to save…"
      — arguably volitive), most don't
    - **Accomplishment** → accept: all dynamic + extended → do-test -/
def doTestPrediction : VendlerClass → DiagnosticResult
  | .state         => .marginal
  | .activity      => .accept
  | .achievement   => .marginal
  | .accomplishment => .accept

/-- The do-test accepts exactly the durative dynamic classes
    (activity, accomplishment). -/
theorem doTest_accepts_durative_dynamic (c : VendlerClass) :
    doTestPrediction c = .accept ↔
    (c.duration = .durative ∧ c.dynamicity = .dynamic) := by
  cases c <;> simp [doTestPrediction, VendlerClass.duration, VendlerClass.dynamicity]

/-- Passing the do-test (for a whole Vendler class, not marginal)
    implies either a dynamic event or a volitive state.

    Formally: if a Vendler class fully accepts the do-test (not just
    marginally), then it must be dynamic. Statives only get marginal
    because the do-test passes only for select volitive statives. -/
theorem doTest_accept_implies_dynamic (c : VendlerClass) :
    doTestPrediction c = .accept → c.dynamicity = .dynamic := by
  cases c <;> simp [doTestPrediction, VendlerClass.dynamicity]

/-- The do-test and imperative test agree on activities and
    accomplishments (both diagnostics accept dynamic durative events).
    They diverge on states (do-test: marginal; imperative: reject)
    and achievements (do-test: marginal; imperative: marginal — but
    for different reasons). -/
theorem doTest_agrees_imperative_for_dynamic_durative (c : VendlerClass)
    (hDyn : c.dynamicity = .dynamic) (hDur : c.duration = .durative) :
    doTestPrediction c = imperativePrediction c := by
  cases c <;> simp_all [doTestPrediction, imperativePrediction,
    VendlerClass.dynamicity, VendlerClass.duration]

end EventSemantics.Agentivity
