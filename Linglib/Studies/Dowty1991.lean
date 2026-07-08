import Linglib.Semantics.ArgumentStructure.Projection
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Data.ProtoRoles.Dowty1991
import Linglib.Fragments.English.Predicates.Verbal

/-!
# [dowty-1991] Thematic Proto-Roles and Argument Selection

Study file connecting the proto-role theory
(`Semantics/ArgumentStructure/EntailmentProfile.lean` and the Levin-class
role-list map, `Semantics/Verb/Class.lean`) to argument
selection phenomena. The paper's explicit per-argument entailment
attributions are typed data rows in `Data/ProtoRoles/Dowty1991.json`
(generated module `Data.ProtoRoles.Dowty1991`), checked against the class
templates in the final section — including the divergences the templates do
NOT encode (build-object stationary, break-object incremental themehood,
the eat-object dependent-existence tension).

## Dowty's original flat-counting ASP

[dowty-1991]'s Argument Selection Principle uses flat counting: the argument
with the greatest number of Proto-Agent entailments is subject. The library's
default ASP uses lattice comparison ([grimm-2011], [davis-koenig-2000]),
which handles priority and fixes anomalies like `arrive`. This study file
preserves Dowty's original counting-based predictions to document where they
succeed and where they diverge from the modern approach.

## Key predictions formalized

- §9.1: Partially symmetric interactive predicates — volition as asymmetric P-Agent
- §9.2: Psych verb doublets — inchoative change-of-state breaks ties
- §9.3: Three verb classes (spray/load, break, hit) — CoS symmetry predicts alternation
- §12: Agentivity × telicity → unaccusativity (Table 1)
-/

namespace Dowty1991

open ArgumentStructure
open ArgumentStructure
open ArgumentStructure
open English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 0. Dowty's Original Flat-Counting ASP ([dowty-1991] p.576)
-- ════════════════════════════════════════════════════

/-- [dowty-1991]'s original single-argument ASP (flat counting):
    an argument selects for subjecthood iff its P-Agent count exceeds
    its P-Patient count. Superseded by lattice-based `OutranksForSubject`
    in `EntailmentProfile.lean`. -/
def flatSelectsSubject (p : EntailmentProfile) : Bool :=
  p.pAgentScore > p.pPatientScore

def flatSelectsObject (p : EntailmentProfile) : Bool :=
  p.pPatientScore > p.pAgentScore

/-- [dowty-1991]'s between-argument comparison (flat counting):
    arg1 outranks arg2 for subjecthood iff arg1 has strictly more
    P-Agent entailments, OR they tie on P-Agent but arg2 has
    strictly more P-Patient entailments. -/
def flatOutranksForSubject (arg1 arg2 : EntailmentProfile) : Bool :=
  arg1.pAgentScore > arg2.pAgentScore ||
  (arg1.pAgentScore == arg2.pAgentScore &&
   arg2.pPatientScore > arg1.pPatientScore)

/-- Corollary 1 (flat counting): neither argument outranks the other → alternation. -/
def flatAllowsAlternation (arg1 arg2 : EntailmentProfile) : Bool :=
  !flatOutranksForSubject arg1 arg2 && !flatOutranksForSubject arg2 arg1

/-- [dowty-1991] Corollary 2 (flat counting): unaccusative iff pPatient > pAgent. -/
def flatPredictsUnaccusative (p : EntailmentProfile) : Bool :=
  p.pPatientScore > p.pAgentScore

/-- Complement: unergative iff pAgent > pPatient. -/
def flatPredictsUnergative (p : EntailmentProfile) : Bool :=
  p.pAgentScore > p.pPatientScore

-- ════════════════════════════════════════════════════
-- § 1. Partially Symmetric Interactive Predicates (§9.1, pp.583–586)
-- ════════════════════════════════════════════════════

/-! Verbs like *kiss*, *embrace*, *marry* denote actions requiring volitional
    involvement of two parties, but only the SUBJECT is entailed to be
    volitional. This single asymmetric P-Agent entailment predicts the
    transitive argument configuration. -/

/-- "kiss" subject: V+M+IE — volitional, in motion, independently existing. -/
def kissSubjectProfile : EntailmentProfile :=
  ⟨true, false, false, true, true, false, false, false, false, false⟩

/-- "kiss" object: M+IE only — same minus volition. -/
def kissObjectProfile : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, false, false, false⟩

/-- The subject outranks the object (lattice: {V,M,IE} ⊃ {M,IE}). -/
theorem kiss_subject_outranks :
    OutranksForSubject kissSubjectProfile kissObjectProfile := by decide

/-- Same result under Dowty's flat counting. -/
theorem kiss_subject_outranks_flat :
    flatOutranksForSubject kissSubjectProfile kissObjectProfile = true := by decide

/-- Volition adds exactly 1 to the subject's P-Agent score. -/
theorem kiss_asymmetry_is_volition :
    kissSubjectProfile.pAgentScore = kissObjectProfile.pAgentScore + 1 := by
  decide

/-- The collective intransitive ("Kim and Sandy kissed") is predicted:
    when both participants have symmetric volition, neither outranks. -/
theorem kiss_collective_alternation :
    AllowsAlternation kissSubjectProfile kissSubjectProfile := by decide

-- ════════════════════════════════════════════════════
-- § 2. Psych Verb Doublets (§9.2, pp.579–581)
-- ════════════════════════════════════════════════════

/-! Psych verbs come in doublets (like/please, fear/frighten) with reversed
    argument configurations. Under the stative reading, Experiencer and
    Stimulus have equal P-Agent scores → alternation is predicted. -/

/-- Stative: Experiencer and Stimulus have incomparable P-Agent sets
    ({S,IE} ⊥ {C,IE}) and equal P-Patient (both 0) → alternation. -/
theorem psychStative_alternation :
    AllowsAlternation
      (ThetaRole.canonicalProfile .experiencer)
      (ThetaRole.canonicalProfile .stimulus) := by decide

/-- Under inchoative interpretation, the Experiencer enters a new mental
    state → gains changeOfState (P-Patient entailment a). -/
def expInchoativeProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, true, false, false, false, false⟩

def stimProfile : EntailmentProfile := ThetaRole.canonicalProfile .stimulus

/-- Inchoative breaks the tie: Stimulus outranks Experiencer for subject
    because the Experiencer now has more P-Patient → Experiencer is a
    "better" object → Stimulus is subject. Predicts StimExp frame. -/
theorem psych_inchoative_stimulus_is_subject :
    OutranksForSubject stimProfile expInchoativeProfile := by decide

-- ════════════════════════════════════════════════════
-- § 3. Three Verb Classes (§9.3, pp.587–597)
-- ════════════════════════════════════════════════════

/-! [dowty-1991] identifies three classes based on CoS distribution
    across non-subject arguments. When CoS is symmetric (both or neither),
    alternation is possible. When asymmetric, the CoS argument is fixed as DO.
    The comparison with [levin-1993]'s alternation judgments lives in
    `Studies/Levin1993.lean` (`dowty_*` theorems). -/

def cosSymmetric (arg1 arg2 : EntailmentProfile) : Bool :=
  arg1.changeOfState == arg2.changeOfState

-- ── spray/load class ──

def sprayLoadTheme : EntailmentProfile :=
  ⟨false, false, false, false, true, true, false, true, false, false⟩

def sprayLoadLocation : EntailmentProfile :=
  ⟨false, false, false, false, true, true, false, true, true, false⟩

theorem sprayLoad_cos_symmetric :
    cosSymmetric sprayLoadTheme sprayLoadLocation = true := by decide

-- ── break class ──

def breakDirectObject : EntailmentProfile :=
  ⟨false, false, false, false, false, true, true, true, true, false⟩

def breakInstrument : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, false, false, false⟩

theorem break_cos_asymmetric :
    cosSymmetric breakDirectObject breakInstrument = false := by decide

theorem break_DO_more_patient :
    breakDirectObject.pPatientScore > breakInstrument.pPatientScore := by decide

-- ── hit class ──

def hitArg1 : EntailmentProfile :=
  ⟨false, false, false, false, true, false, false, true, true, false⟩

def hitArg2 : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, true, false, false⟩

theorem hit_cos_symmetric :
    cosSymmetric hitArg1 hitArg2 = true := by decide

theorem hit_no_cos :
    hitArg1.changeOfState = false ∧ hitArg2.changeOfState = false := ⟨rfl, rfl⟩

theorem hit_no_IT :
    hitArg1.incrementalTheme = false ∧ hitArg2.incrementalTheme = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Table 1: Agentivity × Telicity → Unaccusativity (§12, p.607)
-- ════════════════════════════════════════════════════

/-! [dowty-1991] Table 1: the interaction of agentivity (most salient
    P-Agent property) and telicity (most salient P-Patient property) predicts
    the unergative/unaccusative split. Only the two "pure" cells are stable;
    the mixed cells are where cross-linguistic variation occurs. -/

inductive IntransClass where
  | unergative    -- cell 1: agentive + atelic (run, walk, swim)
  | unaccusative  -- cell 4: non-agentive + telic (die, arrive, melt)
  | unstable      -- cells 2, 3: mixed — cross-linguistic variation
  deriving DecidableEq, Repr

def table1 (agentive telic : Bool) : IntransClass :=
  match agentive, telic with
  | true, false  => .unergative
  | false, true  => .unaccusative
  | _, _         => .unstable

theorem cell1_unergative : table1 true false = .unergative := rfl
theorem cell4_unaccusative : table1 false true = .unaccusative := rfl
theorem cell2_unstable : table1 true true = .unstable := rfl
theorem cell3_unstable : table1 false false = .unstable := rfl

theorem run_cell1 :
    table1 selfMotion.subjectProfile.volition selfMotion.subjectProfile.changeOfState
    = .unergative := rfl

theorem die_cell4 :
    table1 disappearance.subjectProfile.volition disappearance.subjectProfile.changeOfState
    = .unaccusative := by decide

-- ════════════════════════════════════════════════════
-- § 5. Flat Counting vs Modern ASP: The Arrive Anomaly
-- ════════════════════════════════════════════════════

/-! The key divergence between [dowty-1991]'s flat counting and the
    modern priority-based ASP. Flat counting gets arrive wrong because it
    counts movement + IE (2 P-Agent) > changeOfState (1 P-Patient), predicting
    unergative. The modern ASP correctly identifies arrive as unaccusative
    because it lacks the priority features (volition, causation). -/

/-- Flat counting predicts arrive is NOT unaccusative (2 P-Ag > 1 P-Pat). -/
theorem arrive_flat_wrong :
    flatPredictsUnaccusative directedMotion.subjectProfile = false := by decide

/-- Modern priority-based ASP correctly predicts arrive IS unaccusative. -/
theorem arrive_modern_correct :
    PredictsUnaccusative directedMotion.subjectProfile := by decide

/-- Table 1 also correctly predicts arrive as unaccusative
    (non-agentive + telic = cell 4). -/
theorem arrive_table1_correct :
    table1 directedMotion.subjectProfile.volition directedMotion.subjectProfile.changeOfState
    = .unaccusative := by decide

/-- Agreement: Table 1 and the modern ASP converge on arrive being
    unaccusative. Flat counting diverges — this is the anomaly that
    motivated [davis-koenig-2000]'s priority refinement. -/
theorem arrive_anomaly_summary :
    -- Table 1: unaccusative (correct)
    table1 directedMotion.subjectProfile.volition directedMotion.subjectProfile.changeOfState
      = .unaccusative ∧
    -- Modern ASP: unaccusative (correct)
    PredictsUnaccusative directedMotion.subjectProfile ∧
    -- Flat counting: NOT unaccusative (WRONG)
    flatPredictsUnaccusative directedMotion.subjectProfile = false ∧
    -- Fragment annotation: unaccusative (ground truth)
    arrive.unaccusative = true := ⟨by decide, by decide, by decide, rfl⟩

/-- Flat counting gets die right (both methods agree). -/
theorem die_both_agree :
    flatPredictsUnaccusative disappearance.subjectProfile = true ∧
    PredictsUnaccusative disappearance.subjectProfile := ⟨by decide, by decide⟩

/-- Flat counting gets run right (both methods agree). -/
theorem run_both_agree :
    flatPredictsUnergative selfMotion.subjectProfile = true ∧
    PredictsUnergative selfMotion.subjectProfile := ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 6. Fragment Bridge: Profiles Match Verb Fields
-- ════════════════════════════════════════════════════

/-! These theorems verify that the English Fragment verb entries store
    exactly the Levin-class role-list profiles of `RoleList.lean` —
    the stored fields are derivable from the class map (`sweep_instr` is the
    deliberate instrument-sense override). -/

theorem kick_subject_profile_matches :
    kick.toVerb.subjectEntailments = some mannerContact.subjectProfile := rfl

theorem kick_object_profile_matches :
    kick.toVerb.objectEntailments = some contactObject := rfl

theorem eat_subject_profile_matches :
    eat.toVerb.subjectEntailments = some consumption.subjectProfile := rfl

theorem eat_object_profile_matches :
    eat.toVerb.objectEntailments = some consumptionObject := rfl

theorem build_subject_profile_matches :
    build.toVerb.subjectEntailments = some creation.subjectProfile := rfl

theorem build_object_profile_matches :
    build.toVerb.objectEntailments = some creationObject := rfl

theorem run_subject_profile_matches :
    run.toVerb.subjectEntailments = some selfMotion.subjectProfile := rfl

theorem arrive_subject_profile_matches :
    arrive.toVerb.subjectEntailments = some directedMotion.subjectProfile := rfl

theorem see_subject_profile_matches :
    see.toVerb.subjectEntailments = some perception.subjectProfile := rfl

theorem sweep_subject_profile_matches :
    sweep.toVerb.subjectEntailments = some wipeManner.subjectProfile := rfl

theorem sweep_instr_subject_profile_matches :
    sweep_instr.toVerb.subjectEntailments = some wipeInstrument.subjectProfile := rfl

/-- The stored fragment profiles coincide with the Levin-class fallback —
    `effectiveSubjectEntailments`/`effectiveObjectEntailments` would be
    unchanged without them. `sweep_instr` is the deliberate exception: its
    instrument sense overrides the wipe-class (manner-subclass) default. -/
theorem stored_profiles_derivable_from_class :
    kick.toVerb.objectEntailments
      = kick.toVerb.levinClass.bind (·.objectProfile) ∧
    eat.toVerb.objectEntailments
      = eat.toVerb.levinClass.bind (·.objectProfile) ∧
    build.toVerb.objectEntailments
      = build.toVerb.levinClass.bind (·.objectProfile) ∧
    see.toVerb.subjectEntailments
      = see.toVerb.levinClass.bind (·.subjectProfile) ∧
    sweep.toVerb.subjectEntailments
      = sweep.toVerb.levinClass.bind (·.subjectProfile) ∧
    sweep_instr.toVerb.subjectEntailments
      ≠ sweep_instr.toVerb.levinClass.bind (·.subjectProfile) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 7. Fragment Bridge: Predictions Match Annotations
-- ════════════════════════════════════════════════════

/-- Agreement: arrive prediction matches the fragment annotation. -/
theorem arrive_prediction_matches_fragment :
    decide (PredictsUnaccusative directedMotion.subjectProfile) =
    arrive.unaccusative := by decide

/-- Agreement: run prediction matches the fragment annotation. -/
theorem run_prediction_matches_fragment :
    decide (PredictsUnaccusative selfMotion.subjectProfile) =
    English.Predicates.Verbal.run.unaccusative := by decide

-- ════════════════════════════════════════════════════
-- § 8. Dowty's Explicit Attributions vs the Class Templates
-- ════════════════════════════════════════════════════

/-! The paper's explicit per-argument attributions (generated rows in
    `Data.ProtoRoles.Dowty1991`, one per stated entailment, with locators)
    checked against the class-template profiles. Positive checks confirm the
    templates encode what Dowty states; the divergence theorems record what
    they deliberately do NOT encode. -/

/-- Every entailment a data row explicitly attributes agrees with profile
    `p`; fields the paper is silent or hedged about are unconstrained. -/
def matchesProfile (d : ProtoRoleDatum) (p : EntailmentProfile) : Bool :=
  d.volition.all (· == p.volition) &&
  d.sentience.all (· == p.sentience) &&
  d.causation.all (· == p.causation) &&
  d.movement.all (· == p.movement) &&
  d.independentExistence.all (· == p.independentExistence) &&
  d.changeOfState.all (· == p.changeOfState) &&
  d.incrementalTheme.all (· == p.incrementalTheme) &&
  d.causallyAffected.all (· == p.causallyAffected) &&
  d.stationary.all (· == p.stationary) &&
  d.dependentExistence.all (· == p.dependentExistence)

-- § 8a. Positive checks: the templates encode Dowty's attributions

/-- The (35) primary transitive verbs: each stated subject attribution
    (V+S+C+M, no P-Patient, p. 577) holds of the accomplishment template
    subject, and each stated object attribution (CoS+CA) holds of the
    accomplishment/creation/consumption objects. -/
theorem primary_transitives_match_templates :
    matchesProfile Rows.buildSubject accomplishmentSubjectProfile = true ∧
    matchesProfile Rows.writeSubject accomplishmentSubjectProfile = true ∧
    matchesProfile Rows.murderSubject accomplishmentSubjectProfile = true ∧
    matchesProfile Rows.eatSubject accomplishmentSubjectProfile = true ∧
    matchesProfile Rows.washSubject accomplishmentSubjectProfile = true ∧
    matchesProfile Rows.murderObject accomplishmentObjectProfile = true ∧
    matchesProfile Rows.washObject accomplishmentObjectProfile = true ∧
    matchesProfile Rows.writeObject creationObject = true ∧
    matchesProfile Rows.eatObject consumptionObject = true := by decide

/-- The hit-class attributions ((64 III), §9.3.3): the direct object is
    non-moving, unchanged, and a non-incremental-theme — exactly consistent
    with the `mannerContact`/`wipeManner` contacted object (CA+St, no CoS)
    and with this file's §3 hit-class argument profiles. -/
theorem hit_class_matches_contact_object :
    matchesProfile Rows.hitObject contactObject = true ∧
    matchesProfile Rows.hitObject hitArg1 = true ∧
    matchesProfile Rows.hitInstrument hitArg2 = true := by decide

/-- The (29)/(30) single-entailment exemplars land in the right templates:
    *see* (29b) in the perception subject, *need* (29e) in the desire
    subject, *need*'s de dicto object (30e) in the desire object. -/
theorem exemplars_match_templates :
    matchesProfile Rows.seeSubject perception.subjectProfile = true ∧
    matchesProfile Rows.needSubject desire.subjectProfile = true ∧
    (desire.objectProfile.map (matchesProfile Rows.needObject)) = some true ∧
    (desire.objectProfile.map (matchesProfile Rows.seekObject)) = some true := by
  decide

-- § 8b. The psych-state / desire split ([dowty-1991] (38) vs (29e))

/-- The split of the former single state-subject profile is Dowty's own:
    admire-class experiencers are sentience-entailed ((38): *like*), so
    `psychState` fits them; want-class subjects are NOT ((29e)/p. 573:
    *need* entails subject existence "but none of (a)-(d)"), so the
    sentient profile mis-states them — `desire` fits instead. -/
theorem psych_desire_split_justified :
    matchesProfile Rows.likeSubject psychState.subjectProfile = true ∧
    matchesProfile Rows.needSubject desire.subjectProfile = true ∧
    matchesProfile Rows.needSubject psychState.subjectProfile = false := by
  decide

/-- The (38) doublet tie: the experiencer ({S,IE}) and stimulus ({C,IE})
    profiles are Proto-Agent-incomparable with no Proto-Patient difference,
    so neither outranks — Corollary 1 predicts both lexicalizations
    (*like*/*please*). The stated stimulus attributions (causation, no
    sentience) hold of the template's stimulus object. -/
theorem psych_doublet_tie :
    AllowsAlternation psychState.subjectProfile stimulusProfile ∧
    (psychState.objectProfile.map (matchesProfile Rows.likeObject))
      = some true ∧
    matchesProfile Rows.pleaseSubject stimulusProfile = true := by
  refine ⟨by decide, by decide, by decide⟩

/-- Croft's inchoative restriction (p. 580): under the inchoative reading
    the experiencer gains a change of state — the stated attribution matches
    this file's §2 inchoative experiencer profile, which the stimulus then
    outranks for subject. -/
theorem inchoative_experiencer_matches :
    matchesProfile Rows.surpriseObjectInchoative expInchoativeProfile = true ∧
    OutranksForSubject stimProfile expInchoativeProfile := by
  refine ⟨by decide, by decide⟩

-- § 8c. The buy/sell tie (§3.2, §8.3)

/-- §3.2: buyer and seller are both attributed volition and nothing
    distinguishes them ("nor are they different in any proto-role
    entailments", §8.3 p. 579) — the class map gives give-class and
    obtain-class subjects one shared profile, and Corollary 1 licenses the
    doublet: a profile never outranks itself. -/
theorem buy_sell_tie :
    matchesProfile Rows.buySubject possessionTransfer.subjectProfile = true ∧
    matchesProfile Rows.buySeller possessionTransfer.subjectProfile = true ∧
    matchesProfile Rows.sellSubject possessionTransfer.subjectProfile = true ∧
    matchesProfile Rows.sellBuyer possessionTransfer.subjectProfile = true ∧
    AllowsAlternation possessionTransfer.subjectProfile
      possessionTransfer.subjectProfile := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

-- § 8d. Divergences the templates do not encode

/-- Build-object stationary divergence: "all of 28" (pp. 572–573) includes
    (28d) stationary, but the `creation` template object (CoS+IT+CA+DE)
    deliberately omits St — the row disagrees with the template on exactly
    that field. Recorded as data, not flipped: the class-level template
    follows the (35)/p. 577 hedge ("(mostly) ... stationary"), which does
    not commit every creation object to (28d). -/
theorem build_object_stationary_divergence :
    matchesProfile Rows.buildObject creationObject = false ∧
    matchesProfile Rows.buildObject
      { creationObject with stationary := true } = true := by
  refine ⟨by decide, by decide⟩

/-- Break-object incremental-themehood divergence: (64 II) attributes
    "change of state (and Incremental Themehood)" to the break-class direct
    object, but the `resultChange`/accomplishment object template carries no
    IT (per-verb addition by design). The row disagrees with the template on
    exactly that field. -/
theorem break_object_it_divergence :
    matchesProfile Rows.breakObject accomplishmentObjectProfile = false ∧
    matchesProfile Rows.breakObject
      { accomplishmentObjectProfile with incrementalTheme := true } = true := by
  refine ⟨by decide, by decide⟩

/-- Eat-object dependent-existence tension: (30e)(i) counts destruction —
    the argument "will not exist after the event" — as dependent existence,
    which would put DE on *eat*'s object; the paper never states this for
    *eat* (the (35) hedge leaves DE open), and the `consumption` template
    omits DE because the Grimm bridge disambiguation is load-bearing:
    adding DE to an incremental theme flips
    `PersistenceLevel.fromPatientProfile` from `exPersBeginning`
    (consumption) to `exPersEnd` (creation), misclassifying *eat* as a
    creation verb. Recorded, not flipped. -/
theorem eat_object_de_tension :
    matchesProfile Rows.eatObject consumptionObject = true ∧
    PersistenceLevel.fromPatientProfile
      consumptionObject = .exPersBeginning ∧
    PersistenceLevel.fromPatientProfile
      { consumptionObject with dependentExistence := true } = .exPersEnd := by
  refine ⟨by decide, by decide, by decide⟩

/-- The spray/load rows ((64 I), p. 594): both nonsubject arguments are
    attributed a change of state, matching this file's §3 profiles. -/
theorem spray_load_rows_match :
    matchesProfile Rows.loadTheme sprayLoadTheme = true ∧
    matchesProfile Rows.loadLocation sprayLoadLocation = true := by
  refine ⟨by decide, by decide⟩

end Dowty1991
