/-!
# Entailment Profiles and the Argument Selection Principle

@cite{dowty-1991} @cite{davis-koenig-2000} @cite{grimm-2011} @cite{levin-2019}
@cite{beavers-2010}

Entailment profiles encode the lexical entailments a verb imposes on each of
its arguments, reflecting the modern consensus on proto-roles
(@cite{levin-2019}). Proto-Agent and Proto-Patient are **cluster concepts**:
each is a set of entailments, and an argument's "degree of agenthood/patienthood"
is determined by which entailments it satisfies.

## Entailment structure

The 10 entailments are not fully independent (@cite{levin-2019} §2.1):

- **P-Agent pairing**: three P-Agent entailments are paired with P-Patient
  entailments in asymmetric relations (causation↔changeOfState,
  movement↔stationary, independentExistence↔dependentExistence).
- **P-Agent dependency**: volition presupposes sentience.
- **P-Agent priority**: causation outranks other P-Agent entailments for
  subject selection (@cite{davis-koenig-2000}).
- **P-Patient implicational structure**: the affectedness-related entailments
  (changeOfState, incrementalTheme, causallyAffected) form an implicational
  hierarchy (@cite{beavers-2010}).

These dependencies are exploited by the modern ASP (lattice comparison, §3–4)
and formalized algebraically in `AgentivityLattice.lean`:
- **P-Agent** → `AgentivityNode` (4 privative features on a lattice;
  @cite{grimm-2011})
- **P-Patient** → `PersistenceLevel` (4 persistence dimensions;
  @cite{grimm-2011}), and `AffectednessDegree` (implicational hierarchy
  of truth-conditional strength; @cite{beavers-2010})

## Argument Selection Principle (lattice-based)

The ASP uses **lattice comparison** (@cite{grimm-2011}): argument A outranks
argument B for subjecthood iff A's P-Agent feature set dominates (is a superset of)
B's. When P-Agent features are incomparable, P-Patient features break the tie.
This naturally handles priority because feature-set inclusion respects the
entailment dependencies.

For unaccusativity, the priority-based approach checks whether the sole argument
has core agentive features (volition/causation) rather than flat-counting.

@cite{dowty-1991}'s original flat-counting ASP is preserved in
`Phenomena/ArgumentStructure/Studies/Dowty1991.lean` for comparison.
-/

namespace Semantics.Verb.EntailmentProfile

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
  deriving DecidableEq, Repr

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
def PAgentDominates (p q : EntailmentProfile) : Prop :=
  (q.volition = true → p.volition = true) ∧
  (q.sentience = true → p.sentience = true) ∧
  (q.causation = true → p.causation = true) ∧
  (q.movement = true → p.movement = true) ∧
  (q.independentExistence = true → p.independentExistence = true)

instance (p q : EntailmentProfile) : Decidable (PAgentDominates p q) := by
  unfold PAgentDominates; infer_instance

/-- P-Patient feature dominance: `p` has every P-Patient feature that `q` has. -/
def PPatientDominates (p q : EntailmentProfile) : Prop :=
  (q.changeOfState = true → p.changeOfState = true) ∧
  (q.incrementalTheme = true → p.incrementalTheme = true) ∧
  (q.causallyAffected = true → p.causallyAffected = true) ∧
  (q.stationary = true → p.stationary = true) ∧
  (q.dependentExistence = true → p.dependentExistence = true)

instance (p q : EntailmentProfile) : Decidable (PPatientDominates p q) := by
  unfold PPatientDominates; infer_instance

/-- Strict P-Agent dominance: `p` dominates `q` but not vice versa.
    Means `p` has a strict superset of `q`'s P-Agent features. -/
def PAgentStrictlyDominates (p q : EntailmentProfile) : Prop :=
  PAgentDominates p q ∧ ¬ PAgentDominates q p

instance (p q : EntailmentProfile) : Decidable (PAgentStrictlyDominates p q) := by
  unfold PAgentStrictlyDominates; infer_instance

/-- Strict P-Patient dominance. -/
def PPatientStrictlyDominates (p q : EntailmentProfile) : Prop :=
  PPatientDominates p q ∧ ¬ PPatientDominates q p

instance (p q : EntailmentProfile) : Decidable (PPatientStrictlyDominates p q) := by
  unfold PPatientStrictlyDominates; infer_instance

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
def OutranksForSubject (subj obj : EntailmentProfile) : Prop :=
  PAgentStrictlyDominates subj obj ∨
  (¬ PAgentStrictlyDominates subj obj ∧ ¬ PAgentStrictlyDominates obj subj ∧
   PPatientStrictlyDominates obj subj)

instance (subj obj : EntailmentProfile) : Decidable (OutranksForSubject subj obj) := by
  unfold OutranksForSubject; infer_instance

/-- Corollary 1 (@cite{dowty-1991} p.579): Neither argument outranks
    the other → alternation is possible (buy/sell, like/please). -/
def AllowsAlternation (arg1 arg2 : EntailmentProfile) : Prop :=
  ¬ OutranksForSubject arg1 arg2 ∧ ¬ OutranksForSubject arg2 arg1

instance (arg1 arg2 : EntailmentProfile) : Decidable (AllowsAlternation arg1 arg2) := by
  unfold AllowsAlternation; infer_instance

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
def PredictsUnaccusative (p : EntailmentProfile) : Prop :=
  p.volition = false ∧ p.causation = false ∧ p.pPatientScore > 0

instance (p : EntailmentProfile) : Decidable (PredictsUnaccusative p) := by
  unfold PredictsUnaccusative; infer_instance

/-- Predicts unergative for intransitive verbs.

    An intransitive subject is unergative iff it has at least one core
    agentive feature (volition or causation) and no P-Patient features. -/
def PredictsUnergative (p : EntailmentProfile) : Prop :=
  (p.volition = true ∨ p.causation = true) ∧ p.pPatientScore = 0

instance (p : EntailmentProfile) : Decidable (PredictsUnergative p) := by
  unfold PredictsUnergative; infer_instance

-- ════════════════════════════════════════════════════
-- § 6. Well-Formedness Constraints (@cite{levin-2019}, @cite{davis-koenig-2000})
-- ════════════════════════════════════════════════════

/-- Intra-profile well-formedness: volition presupposes sentience.
    Only sentient entities can be volitional (@cite{dowty-1991} p.607,
    @cite{levin-2019} §2.1). -/
def EntailmentProfile.WellFormedInternal (p : EntailmentProfile) : Prop :=
  p.volition = true → p.sentience = true

instance (p : EntailmentProfile) : Decidable p.WellFormedInternal := by
  unfold EntailmentProfile.WellFormedInternal; infer_instance

/-- Inter-argument well-formedness (@cite{davis-koenig-2000},
    @cite{primus-1999}): three P-Agent entailments are paired with
    P-Patient entailments in asymmetric relations.

    - causation (subject) → changeOfState (object)
    - movement (subject) → stationary (object)
    - independentExistence (subject) → dependentExistence (object) -/
def WellFormedPair (subj obj : EntailmentProfile) : Prop :=
  (subj.causation = true → obj.changeOfState = true) ∧
  (subj.movement = true → obj.stationary = true) ∧
  (subj.independentExistence = true → obj.dependentExistence = true)

instance (subj obj : EntailmentProfile) : Decidable (WellFormedPair subj obj) := by
  unfold WellFormedPair; infer_instance

-- ════════════════════════════════════════════════════
-- § 7. Do-Test (@cite{cruse-1973} via @cite{dowty-1991})
-- ════════════════════════════════════════════════════

/-- Source of do-test acceptability. -/
inductive DoTestSource where
  | semantic    -- Profile-based: verb entails volition/causation/movement
  | pragmatic   -- Complement-based: complement evokes agentivity
  deriving DecidableEq, Repr

/-- The do-test passes (semantically) iff at least one of
    {volition, causation, movement} holds. -/
def PassesDoTestFromProfile (p : EntailmentProfile) : Prop :=
  p.volition = true ∨ p.causation = true ∨ p.movement = true

instance (p : EntailmentProfile) : Decidable (PassesDoTestFromProfile p) := by
  unfold PassesDoTestFromProfile; infer_instance

-- ════════════════════════════════════════════════════
-- § 8. Effector / Force Recipient
-- ════════════════════════════════════════════════════

/-- An effector (@cite{van-valin-wilkins-1996}) is a self-energetic force
    bearer: movement + independent existence. Realized as external argument. -/
def IsEffector (p : EntailmentProfile) : Prop :=
  p.movement = true ∧ p.independentExistence = true

instance (p : EntailmentProfile) : Decidable (IsEffector p) := by
  unfold IsEffector; infer_instance

/-- A force recipient is causally affected or stationary.
    Realized as internal argument. -/
def IsForceRecipient (p : EntailmentProfile) : Prop :=
  p.causallyAffected = true ∨ p.stationary = true

instance (p : EntailmentProfile) : Decidable (IsForceRecipient p) := by
  unfold IsForceRecipient; infer_instance

/-- Effectors have at least 2 P-Agent entailments (movement + IE). -/
theorem effector_has_pAgent (p : EntailmentProfile) (h : IsEffector p) :
    p.pAgentScore ≥ 2 := by
  obtain ⟨hm, hie⟩ := h
  simp [EntailmentProfile.pAgentScore, hm, hie]

-- ════════════════════════════════════════════════════
-- § 9. Canonical Verb Profiles
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
-- § 10. Verification Theorems
-- ════════════════════════════════════════════════════

-- Dominance is reflexive

theorem pAgentDominates_refl (p : EntailmentProfile) :
    PAgentDominates p p :=
  ⟨id, id, id, id, id⟩

theorem pPatientDominates_refl (p : EntailmentProfile) :
    PPatientDominates p p :=
  ⟨id, id, id, id, id⟩

end Semantics.Verb.EntailmentProfile
