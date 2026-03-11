import Linglib.Core.Lexical.ThetaRole

/-!
# Entailment Profiles and the Argument Selection Principle

@cite{dowty-1991} @cite{davis-koenig-2000} @cite{grimm-2011} @cite{levin-2019}

Entailment profiles encode the lexical entailments a verb imposes on each of
its arguments. Proto-Agent and Proto-Patient are **cluster concepts**: each is
defined by a set of independent entailments, and an argument's "degree of
agenthood/patienthood" is determined by which entailments it satisfies.

## Modern ASP (lattice-based)

@cite{dowty-1991}'s original Argument Selection Principle used flat counting
(more P-Agent entailments → subject). Subsequent work (@cite{davis-koenig-2000},
@cite{grimm-2011}, @cite{levin-2019}) identified two problems:

1. **Entailment non-independence**: causation↔changeOfState, movement↔stationary,
   and independentExistence↔dependentExistence are paired across arguments;
   volition presupposes sentience within an argument.
2. **Priority**: causation outranks other P-Agent entailments for subject selection.

The modern ASP uses **lattice comparison** (@cite{grimm-2011}): argument A outranks
argument B for subjecthood iff A's P-Agent feature set dominates (is a superset of)
B's. When P-Agent features are incomparable, P-Patient features break the tie.
This naturally handles priority because feature-set inclusion respects the
entailment dependencies.

For unaccusativity, the priority-based approach checks whether the sole argument
has core agentive features (volition/causation) rather than flat-counting.
-/

namespace Semantics.Events.ProtoRoles

-- ════════════════════════════════════════════════════
-- § 1. Entailment Profile (@cite{dowty-1991} pp.572–573)
-- ════════════════════════════════════════════════════

/-- The 10 entailments defining Proto-Agent and Proto-Patient
    (@cite{dowty-1991} pp.572–573).

    Proto-Agent entailments (a)–(e):
    - volition, sentience, causation, movement, independent existence

    Proto-Patient entailments (a)–(e):
    - change of state, incremental theme, causally affected, stationary,
      dependent existence -/
structure EntailmentProfile where
  -- Proto-Agent entailments
  /-- (a) volitional involvement in the event -/
  volition            : Bool
  /-- (b) sentience/perception -/
  sentience           : Bool
  /-- (c) causing an event or change of state in another participant -/
  causation           : Bool
  /-- (d) movement (relative to another participant) -/
  movement            : Bool
  /-- (e) exists independently of the event named by the verb -/
  independentExistence : Bool
  -- Proto-Patient entailments
  /-- (a) undergoes change of state -/
  changeOfState       : Bool
  /-- (b) incremental theme (Krifka's SINC) -/
  incrementalTheme    : Bool
  /-- (c) causally affected by another participant -/
  causallyAffected    : Bool
  /-- (d) stationary relative to another participant -/
  stationary          : Bool
  /-- (e) does not exist independently of the event -/
  dependentExistence  : Bool
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Feature Counting (informational, NOT used for ASP)
-- ════════════════════════════════════════════════════

/-- Count of Proto-Agent entailments. Informational — the modern ASP
    uses lattice comparison, not counting. Retained for bridge theorems
    and backward compatibility with study files. -/
def EntailmentProfile.pAgentScore (p : EntailmentProfile) : Nat :=
  p.volition.toNat + p.sentience.toNat + p.causation.toNat +
  p.movement.toNat + p.independentExistence.toNat

/-- Count of Proto-Patient entailments. -/
def EntailmentProfile.pPatientScore (p : EntailmentProfile) : Nat :=
  p.changeOfState.toNat + p.incrementalTheme.toNat +
  p.causallyAffected.toNat + p.stationary.toNat +
  p.dependentExistence.toNat

-- ════════════════════════════════════════════════════
-- § 3. Lattice Comparison (@cite{grimm-2011})
-- ════════════════════════════════════════════════════

/-- P-Agent feature dominance: `p` has every P-Agent feature that `q` has.
    This is the subset ordering on P-Agent feature sets. -/
def pAgentDominates (p q : EntailmentProfile) : Bool :=
  (!q.volition || p.volition) &&
  (!q.sentience || p.sentience) &&
  (!q.causation || p.causation) &&
  (!q.movement || p.movement) &&
  (!q.independentExistence || p.independentExistence)

/-- P-Patient feature dominance: `p` has every P-Patient feature that `q` has. -/
def pPatientDominates (p q : EntailmentProfile) : Bool :=
  (!q.changeOfState || p.changeOfState) &&
  (!q.incrementalTheme || p.incrementalTheme) &&
  (!q.causallyAffected || p.causallyAffected) &&
  (!q.stationary || p.stationary) &&
  (!q.dependentExistence || p.dependentExistence)

/-- Strict P-Agent dominance: `p` dominates `q` but not vice versa.
    Means `p` has a strict superset of `q`'s P-Agent features. -/
def pAgentStrictlyDominates (p q : EntailmentProfile) : Bool :=
  pAgentDominates p q && !pAgentDominates q p

/-- Strict P-Patient dominance. -/
def pPatientStrictlyDominates (p q : EntailmentProfile) : Bool :=
  pPatientDominates p q && !pPatientDominates q p

-- ════════════════════════════════════════════════════
-- § 4. Argument Selection Principle (lattice-based)
-- ════════════════════════════════════════════════════

/-- Modern ASP: `subj` outranks `obj` for subjecthood iff:
    (1) `subj` strictly dominates `obj` on P-Agent features
        (subj's P-Agent set ⊃ obj's P-Agent set), OR
    (2) Neither strictly dominates the other on P-Agent, AND `obj`
        strictly dominates `subj` on P-Patient (obj is a "better"
        object, hence subj wins by exclusion).

    This replaces @cite{dowty-1991}'s flat counting with lattice
    comparison (@cite{grimm-2011}, @cite{davis-koenig-2000}). Priority
    of causation is captured structurally: {causation, IE} ⊃ {IE} but
    {causation, IE} ⊥ {sentience, IE} (incomparable). -/
def outranksForSubject (subj obj : EntailmentProfile) : Bool :=
  pAgentStrictlyDominates subj obj ||
  (!pAgentStrictlyDominates subj obj && !pAgentStrictlyDominates obj subj &&
   pPatientStrictlyDominates obj subj)

/-- Corollary 1 (@cite{dowty-1991} p.579): Neither argument outranks
    the other → alternation is possible (buy/sell, like/please). -/
def allowsAlternation (arg1 arg2 : EntailmentProfile) : Bool :=
  !outranksForSubject arg1 arg2 && !outranksForSubject arg2 arg1

-- ════════════════════════════════════════════════════
-- § 5. Unaccusativity (priority-based)
-- ════════════════════════════════════════════════════

/-- Predicts unaccusativity for intransitive verbs.

    An intransitive subject is unaccusative iff it lacks core agentive
    features (volition AND causation) and has at least one P-Patient
    feature. This matches @cite{dowty-1991}'s Table 1 cell 4 and fixes
    the `arrive` anomaly that flat counting gets wrong.

    @cite{davis-koenig-2000}: causation and volition are the priority
    P-Agent entailments. Their absence signals non-agentivity. -/
def predictsUnaccusative (p : EntailmentProfile) : Bool :=
  !p.volition && !p.causation && p.pPatientScore > 0

/-- Predicts unergative for intransitive verbs.

    An intransitive subject is unergative iff it has at least one core
    agentive feature (volition or causation) and no P-Patient features. -/
def predictsUnergative (p : EntailmentProfile) : Bool :=
  (p.volition || p.causation) && p.pPatientScore == 0

-- ════════════════════════════════════════════════════
-- § 6. Well-Formedness Constraints (@cite{levin-2019}, @cite{davis-koenig-2000})
-- ════════════════════════════════════════════════════

/-- Intra-profile well-formedness: volition presupposes sentience.
    Only sentient entities can be volitional (@cite{dowty-1991} p.607,
    @cite{levin-2019} §2.1). -/
def EntailmentProfile.wellFormedInternal (p : EntailmentProfile) : Bool :=
  !p.volition || p.sentience

/-- Inter-argument well-formedness (@cite{davis-koenig-2000},
    @cite{primus-1999}): three P-Agent entailments are paired with
    P-Patient entailments in asymmetric relations.

    - causation (subject) → changeOfState (object)
    - movement (subject) → stationary (object)
    - independentExistence (subject) → dependentExistence (object) -/
def wellFormedPair (subj obj : EntailmentProfile) : Bool :=
  (!subj.causation || obj.changeOfState) &&
  (!subj.movement || obj.stationary) &&
  (!subj.independentExistence || obj.dependentExistence)

-- ════════════════════════════════════════════════════
-- § 7. Do-Test (@cite{cruse-1973} via @cite{dowty-1991})
-- ════════════════════════════════════════════════════

/-- Source of do-test acceptability. -/
inductive DoTestSource where
  | semantic    -- Profile-based: verb entails volition/causation/movement
  | pragmatic   -- Complement-based: complement evokes agentivity
  deriving DecidableEq, Repr, BEq

/-- The do-test passes (semantically) iff at least one of
    {volition, causation, movement} holds. -/
def passesDoTestFromProfile (p : EntailmentProfile) : Bool :=
  p.volition || p.causation || p.movement

/-- Passing the do-test is equivalent to having at least one
    P-Agent entailment from {volition, causation, movement}. -/
theorem doTest_from_profile_iff_hasAgentEntailment
    (p : EntailmentProfile) :
    passesDoTestFromProfile p = true ↔
    (p.volition = true ∨ p.causation = true ∨ p.movement = true) := by
  simp [passesDoTestFromProfile, Bool.or_eq_true, or_assoc]

-- ════════════════════════════════════════════════════
-- § 8. Effector / Force Recipient
-- ════════════════════════════════════════════════════

/-- An effector (@cite{van-valin-wilkins-1996}) is a self-energetic force
    bearer: movement + independent existence. Realized as external argument. -/
def isEffector (p : EntailmentProfile) : Bool :=
  p.movement && p.independentExistence

/-- A force recipient is causally affected or stationary.
    Realized as internal argument. -/
def isForceRecipient (p : EntailmentProfile) : Bool :=
  p.causallyAffected || p.stationary

/-- Effectors have at least 2 P-Agent entailments (movement + IE). -/
theorem effector_has_pAgent (p : EntailmentProfile) (h : isEffector p = true) :
    p.pAgentScore ≥ 2 := by
  simp [isEffector, Bool.and_eq_true] at h
  obtain ⟨hm, hie⟩ := h
  simp [EntailmentProfile.pAgentScore, hm, hie]

-- ════════════════════════════════════════════════════
-- § 9. ThetaRole → Canonical Profile
-- ════════════════════════════════════════════════════

/-- Map each ThetaRole to its canonical entailment profile.

    Traditional role labels are cluster concepts: each name picks out a
    typical combination of entailments. This mapping derives the labels
    from the underlying entailment space. -/
def ThetaRole.canonicalProfile : ThetaRole → EntailmentProfile
  | .agent       => ⟨true, true, true, true, true,     false, false, false, false, false⟩
  | .patient     => ⟨false, false, false, false, false, true, false, true, true, false⟩
  | .theme       => ⟨false, false, false, false, true,  false, false, false, true, false⟩
  | .experiencer => ⟨false, true, false, false, true,   false, false, false, false, false⟩
  | .instrument  => ⟨false, false, true, false, true,   false, false, false, false, false⟩
  | .stimulus    => ⟨false, false, true, false, true,   false, false, false, false, false⟩
  | .goal        => ⟨false, false, false, false, true,  false, false, false, false, false⟩
  | .source      => ⟨false, false, false, false, true,  false, false, false, false, false⟩

-- ════════════════════════════════════════════════════
-- § 10. Canonical Verb Profiles
-- ════════════════════════════════════════════════════

-- These profiles define the canonical entailment content for specific
-- verb senses. Used by EventStructure, RootTypology, and study files.

/-- "kick" subject: V+S+C+M+IE (prototypical agent, 5 P-Ag) -/
def kickSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

/-- "kick" object: CoS+CA+St (3 P-Pat) -/
def kickObjectProfile : EntailmentProfile :=
  ⟨false, false, false, false, false, true, false, true, true, false⟩

/-- "build" subject: V+S+C+M+IE (5 P-Ag) -/
def buildSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

/-- "build" object: CoS+IT+CA+DE (4 P-Pat, incremental theme, dependent existence) -/
def buildObjectProfile : EntailmentProfile :=
  ⟨false, false, false, false, false, true, true, true, false, true⟩

/-- "see" subject: S+IE (experiencer, 2 P-Ag) -/
def seeSubjectProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, false, false, false, false, false⟩

/-- "run" subject: V+S+M+IE (4 P-Ag, unergative) -/
def runSubjectProfile : EntailmentProfile :=
  ⟨true, true, false, true, true, false, false, false, false, false⟩

/-- "arrive" subject: M+IE+CoS (2 P-Ag, 1 P-Pat — unaccusative) -/
def arriveSubjectProfile : EntailmentProfile :=
  ⟨false, false, false, true, true, true, false, false, false, false⟩

/-- "die" subject: CoS+CA+DE (0 P-Ag, 3 P-Pat — unaccusative) -/
def dieSubjectProfile : EntailmentProfile :=
  ⟨false, false, false, false, false, true, false, true, false, true⟩

/-- "eat" subject: V+S+C+M+IE (5 P-Ag) -/
def eatSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

/-- "eat" object: CoS+IT+CA (3 P-Pat, incremental theme) -/
def eatObjectProfile : EntailmentProfile :=
  ⟨false, false, false, false, false, true, true, true, false, false⟩

/-- "buy" subject: V+S+C+IE (4 P-Ag) -/
def buySubjectProfile : EntailmentProfile :=
  ⟨true, true, true, false, true, false, false, false, false, false⟩

/-- "sell" subject: V+S+C+IE (same as buy — 4 P-Ag) -/
def sellSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, false, true, false, false, false, false, false⟩

/-- "sweep" basic-sense subject: M+IE (movement + independent existence).
    Underspecified for volition — agentivity is pragmatically resolved. -/
def sweepBasicSubjectProfile : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, false, false, false⟩

/-- "sweep" broom-sense subject: V+S+C+M+IE (obligatory agent, 5 P-Ag).
    Instrument lexicalization forces volition, sentience, causation. -/
def sweepBroomSubjectProfile : EntailmentProfile :=
  ⟨true, true, true, true, true, false, false, false, false, false⟩

-- ════════════════════════════════════════════════════
-- § 11. Verification Theorems
-- ════════════════════════════════════════════════════

-- Between-argument ASP

/-- Agent outranks patient for subjecthood (lattice: {V,S,C,M,IE} ⊃ {}). -/
theorem agent_outranks_patient :
    outranksForSubject
      (ThetaRole.canonicalProfile .agent)
      (ThetaRole.canonicalProfile .patient) = true := by native_decide

/-- Agent outranks instrument (lattice: {V,S,C,M,IE} ⊃ {C,IE}). -/
theorem agent_outranks_instrument :
    outranksForSubject
      (ThetaRole.canonicalProfile .agent)
      (ThetaRole.canonicalProfile .instrument) = true := by native_decide

/-- Agent outranks experiencer (lattice: {V,S,C,M,IE} ⊃ {S,IE}). -/
theorem agent_outranks_experiencer :
    outranksForSubject
      (ThetaRole.canonicalProfile .agent)
      (ThetaRole.canonicalProfile .experiencer) = true := by native_decide

/-- Experiencer and instrument have incomparable P-Agent sets ({S,IE} ⊥ {C,IE}),
    but also equal P-Patient (both 0) → alternation predicted. -/
theorem experiencer_instrument_alternation :
    allowsAlternation
      (ThetaRole.canonicalProfile .experiencer)
      (ThetaRole.canonicalProfile .instrument) = true := by native_decide

/-- Experiencer and stimulus have equal profiles → alternation (like/please). -/
theorem experiencer_stimulus_alternation :
    allowsAlternation
      (ThetaRole.canonicalProfile .experiencer)
      (ThetaRole.canonicalProfile .stimulus) = true := by native_decide

-- Role hierarchy (informational)

theorem agent_pAgent_score :
    (ThetaRole.canonicalProfile .agent).pAgentScore = 5 := by native_decide

theorem patient_pAgent_score :
    (ThetaRole.canonicalProfile .patient).pAgentScore = 0 := by native_decide

theorem agent_pPatient_score :
    (ThetaRole.canonicalProfile .agent).pPatientScore = 0 := by native_decide

theorem patient_pPatient_score :
    (ThetaRole.canonicalProfile .patient).pPatientScore = 3 := by native_decide

-- Well-formedness of canonical profiles

theorem canonical_agent_wellformed :
    (ThetaRole.canonicalProfile .agent).wellFormedInternal = true := by native_decide

theorem canonical_experiencer_wellformed :
    (ThetaRole.canonicalProfile .experiencer).wellFormedInternal = true := by native_decide

theorem canonical_patient_wellformed :
    (ThetaRole.canonicalProfile .patient).wellFormedInternal = true := by native_decide

-- Dominance is reflexive

theorem pAgentDominates_refl (p : EntailmentProfile) :
    pAgentDominates p p = true := by
  simp [pAgentDominates]

theorem pPatientDominates_refl (p : EntailmentProfile) :
    pPatientDominates p p = true := by
  simp [pPatientDominates]

end Semantics.Events.ProtoRoles
