/-
# Event Structure Templates (Rappaport Hovav & Levin 1998, 2010, 2024)

Verbs decompose into **templates** (structural meaning that determines
argument realization) filled by **roots** (idiosyncratic content).
Templates compose via CAUSE; which sub-predicate determines argument
realization yields different syntactic frames.

Key insight from R&L (2024): verbs of motion + sustained contact (sweep,
rub, scrape) have two grammatically relevant predicates — MOVE and CONTACT.
Which predicate determines argument realization yields variable agentivity
and distinct syntactic frames.

## Bridges

- `Template.vendlerClass` → `VendlerClass` (aspect)
- `motionContact_variable_agentivity` → `sweepBasicSubjectProfile` (proto-roles)
- `contact_determines_implies_effector_subject` → `isEffector` (proto-roles)
- `lexicalize_increases_agentivity` → `pAgentScore` ordering (proto-roles)

## References

- Rappaport Hovav, M. & Levin, B. (1998). Building verb meanings.
  In M. Butt & W. Geuder (eds.), *The Projection of Arguments*, 97–134.
- Rappaport Hovav, M. & Levin, B. (2010). Reflections on manner/result
  complementarity. In M. Rappaport Hovav et al. (eds.),
  *Lexical Semantics, Syntax, and Event Structure*, 21–38.
- Rappaport Hovav, M. & Levin, B. (2024). Variable agentivity: Polysemy
  or underspecification? In *The Landscape of Verb Classes*.
-/

import Linglib.Theories.EventSemantics.ProtoRoles

namespace EventSemantics.EventStructure

open EventSemantics.ProtoRoles
open TruthConditional.Verb.Aspect

-- ════════════════════════════════════════════════════
-- § 1. Event Structure Primitives (R&L 1998 + 2024)
-- ════════════════════════════════════════════════════

/-- Primitive event structure operators.
    ACT, CAUSE, BECOME, STATE are from R&L (1998).
    MOVE and CONTACT are from R&L (2024), decomposing manner verbs
    more finely than the original ACT-based templates. -/
inductive Primitive where
  | ACT      -- agentive activity
  | CAUSE    -- causal relation between sub-events
  | BECOME   -- change of state (transition)
  | STATE    -- simple state holding
  | MOVE     -- motion (possibly non-agentive)
  | CONTACT  -- force through sustained contact
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Event Structure Templates (R&L 1998 + 2024)
-- ════════════════════════════════════════════════════

/-- Canonical event structure templates.
    The first four are from R&L (1998). `motionContact` is from R&L (2024)
    for the sweep/rub/scrape class: [x MOVE y] WHILE [x CONTACT y]. -/
inductive Template where
  | state          -- [x ⟨STATE⟩]
  | activity       -- [x ACT]
  | achievement    -- [BECOME [x ⟨STATE⟩]]
  | accomplishment -- [[x ACT] CAUSE [BECOME [y ⟨STATE⟩]]]
  | motionContact  -- [x MOVE y] WHILE [x CONTACT y]
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 3. Template Properties
-- ════════════════════════════════════════════════════

/-- Does the template involve CAUSE? -/
def Template.hasCause : Template → Bool
  | .accomplishment => true
  | _ => false

/-- Does the template have an external causer position? -/
def Template.hasExternalCauser : Template → Bool
  | .accomplishment => true
  | _ => false

/-- How many grammatically relevant predicates? -/
def Template.predicateCount : Template → Nat
  | .state => 1
  | .activity => 1
  | .achievement => 1
  | .accomplishment => 2  -- ACT + BECOME
  | .motionContact => 2   -- MOVE + CONTACT

/-- Predicted Vendler class for each template. -/
def Template.vendlerClass : Template → VendlerClass
  | .state => .state
  | .activity => .activity
  | .achievement => .achievement
  | .accomplishment => .accomplishment
  | .motionContact => .activity  -- Atelic by default (sweep is an activity)

-- ════════════════════════════════════════════════════
-- § 4. Argument Realization from Templates
-- ════════════════════════════════════════════════════

/-- Predicted subject entailment profile for each template. -/
def Template.subjectProfile : Template → EntailmentProfile
  | .state =>
    -- State holder: sentience + IE only
    ⟨false, true, false, false, true, false, false, false, false, false⟩
  | .activity =>
    -- Agentive activity: V+S+C+M+IE (full proto-agent)
    ⟨true, true, true, true, true, false, false, false, false, false⟩
  | .achievement =>
    -- Achievement subject: M+IE+CoS (undergoes change)
    ⟨false, false, false, true, true, true, false, false, false, false⟩
  | .accomplishment =>
    -- Accomplishment subject: V+S+C+M+IE (full proto-agent, causes result)
    ⟨true, true, true, true, true, false, false, false, false, false⟩
  | .motionContact =>
    -- Motion+contact subject: M+IE only (underspecified for agentivity)
    sweepBasicSubjectProfile

/-- Predicted object entailment profile (if any). -/
def Template.objectProfile : Template → Option EntailmentProfile
  | .state => none
  | .activity => none
  | .achievement => none
  | .accomplishment =>
    -- Result patient: CoS+IT+CA (undergoes caused change)
    some ⟨false, false, false, false, false, true, true, true, false, false⟩
  | .motionContact =>
    -- Force recipient: CA+St (causally affected, stationary surface)
    some ⟨false, false, false, false, false, false, false, true, true, false⟩

/-- Accomplishment subject is a full agent (5 P-Agent entailments). -/
theorem accomplishment_subject_is_agent :
    (Template.subjectProfile .accomplishment).pAgentScore = 5 := by native_decide

/-- motionContact subject has the same profile as basic sweep
    (movement + IE, underspecified for agentivity). -/
theorem motionContact_variable_agentivity :
    Template.subjectProfile .motionContact = sweepBasicSubjectProfile := rfl

-- ════════════════════════════════════════════════════
-- § 5. Which Predicate Determines Argument Realization
-- ════════════════════════════════════════════════════

/-- For motionContact verbs, which sub-predicate determines argument
    realization (R&L 2024 §3.3–3.4). -/
inductive DeterminingPredicate where
  | motion   -- MOVE determines: unaccusative/transitive+PP frames
  | contact  -- CONTACT determines: simple transitive frame
  deriving DecidableEq, Repr, BEq

/-- When CONTACT determines argument realization, the subject is an
    effector (movement + IE → external argument). This yields the simple
    transitive frame: "The wind swept the deck". -/
theorem contact_determines_implies_effector_subject :
    isEffector (Template.subjectProfile .motionContact) = true := by native_decide

/-- The motionContact object profile exists and is a force recipient. -/
theorem motionContact_object_is_forceRecipient :
    ∃ p, Template.objectProfile .motionContact = some p ∧
    isForceRecipient p = true := ⟨_, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Instrument Lexicalization (R&L 2024 §3.5)
-- ════════════════════════════════════════════════════

/-- Instrument lexicalization adds agentivity to a template by restricting
    the moving entity to a specific instrument, forcing volition + sentience
    + causation. The result is the broom-sweep subject profile. -/
def Template.lexicalizeInstrument : Template → EntailmentProfile
  | .motionContact => sweepBroomSubjectProfile
  | t => t.subjectProfile  -- No-op for other templates

/-- Instrument lexicalization strictly increases agentivity for motionContact
    templates (R&L 2024 §3.5: broom-sweep is more agentive than basic sweep). -/
theorem lexicalize_increases_agentivity :
    (Template.lexicalizeInstrument .motionContact).pAgentScore >
    (Template.subjectProfile .motionContact).pAgentScore := by native_decide

/-- Lexicalized motionContact has full proto-agent profile (5 entailments). -/
theorem lexicalized_is_full_agent :
    (Template.lexicalizeInstrument .motionContact).pAgentScore = 5 := by native_decide

end EventSemantics.EventStructure
