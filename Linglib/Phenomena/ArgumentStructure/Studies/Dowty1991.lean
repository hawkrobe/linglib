import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Theories.Semantics.Lexical.Verb.AgentivityLattice
import Linglib.Theories.Interfaces.SyntaxSemantics.Linking
import Linglib.Phenomena.ArgumentStructure.DiathesisAlternations.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{dowty-1991} Thematic Proto-Roles and Argument Selection

Study file connecting the proto-role theory (`Theories/Semantics/Events/ProtoRoles.lean`)
to argument selection phenomena.

## Dowty's original flat-counting ASP

@cite{dowty-1991}'s Argument Selection Principle uses flat counting: the argument
with the greatest number of Proto-Agent entailments is subject. The library's
default ASP uses lattice comparison (@cite{grimm-2011}, @cite{davis-koenig-2000}),
which handles priority and fixes anomalies like `arrive`. This study file
preserves Dowty's original counting-based predictions to document where they
succeed and where they diverge from the modern approach.

## Key predictions formalized

- §9.1: Partially symmetric interactive predicates — volition as asymmetric P-Agent
- §9.2: Psych verb doublets — inchoative change-of-state breaks ties
- §9.3: Three verb classes (spray/load, break, hit) — CoS symmetry predicts alternation
- §12: Agentivity × telicity → unaccusativity (Table 1)
-/

namespace Phenomena.ArgumentStructure.Studies.Dowty1991

open Semantics.Lexical.Verb.EntailmentProfile
open Phenomena.ArgumentStructure.DiathesisAlternations.Data
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 0. Dowty's Original Flat-Counting ASP (@cite{dowty-1991} p.576)
-- ════════════════════════════════════════════════════

/-- @cite{dowty-1991}'s original single-argument ASP (flat counting):
    an argument selects for subjecthood iff its P-Agent count exceeds
    its P-Patient count. Superseded by lattice-based `outranksForSubject`
    in `EntailmentProfile.lean`. -/
def flatSelectsSubject (p : EntailmentProfile) : Bool :=
  p.pAgentScore > p.pPatientScore

def flatSelectsObject (p : EntailmentProfile) : Bool :=
  p.pPatientScore > p.pAgentScore

/-- @cite{dowty-1991}'s between-argument comparison (flat counting):
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

/-- @cite{dowty-1991} Corollary 2 (flat counting): unaccusative iff pPatient > pAgent. -/
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
    outranksForSubject kissSubjectProfile kissObjectProfile = true := by native_decide

/-- Same result under Dowty's flat counting. -/
theorem kiss_subject_outranks_flat :
    flatOutranksForSubject kissSubjectProfile kissObjectProfile = true := by native_decide

/-- Volition adds exactly 1 to the subject's P-Agent score. -/
theorem kiss_asymmetry_is_volition :
    kissSubjectProfile.pAgentScore = kissObjectProfile.pAgentScore + 1 := by
  native_decide

/-- The collective intransitive ("Kim and Sandy kissed") is predicted:
    when both participants have symmetric volition, neither outranks. -/
theorem kiss_collective_alternation :
    allowsAlternation kissSubjectProfile kissSubjectProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 2. Psych Verb Doublets (§9.2, pp.579–581)
-- ════════════════════════════════════════════════════

/-! Psych verbs come in doublets (like/please, fear/frighten) with reversed
    argument configurations. Under the stative reading, Experiencer and
    Stimulus have equal P-Agent scores → alternation is predicted. -/

/-- Stative: Experiencer and Stimulus have incomparable P-Agent sets
    ({S,IE} ⊥ {C,IE}) and equal P-Patient (both 0) → alternation. -/
theorem psychStative_alternation :
    allowsAlternation
      (ThetaRole.canonicalProfile .experiencer)
      (ThetaRole.canonicalProfile .stimulus) = true := by native_decide

/-- Under inchoative interpretation, the Experiencer enters a new mental
    state → gains changeOfState (P-Patient entailment a). -/
def expInchoativeProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, true, false, false, false, false⟩

def stimProfile : EntailmentProfile := ThetaRole.canonicalProfile .stimulus

/-- Inchoative breaks the tie: Stimulus outranks Experiencer for subject
    because the Experiencer now has more P-Patient → Experiencer is a
    "better" object → Stimulus is subject. Predicts StimExp frame. -/
theorem psych_inchoative_stimulus_is_subject :
    outranksForSubject stimProfile expInchoativeProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Three Verb Classes (§9.3, pp.587–597)
-- ════════════════════════════════════════════════════

/-! @cite{dowty-1991} identifies three classes based on CoS distribution
    across non-subject arguments. When CoS is symmetric (both or neither),
    alternation is possible. When asymmetric, the CoS argument is fixed as DO. -/

def cosSymmetric (arg1 arg2 : EntailmentProfile) : Bool :=
  arg1.changeOfState == arg2.changeOfState

-- ── spray/load class ──

def sprayLoadTheme : EntailmentProfile :=
  ⟨false, false, false, false, true, true, false, true, false, false⟩

def sprayLoadLocation : EntailmentProfile :=
  ⟨false, false, false, false, true, true, false, true, true, false⟩

theorem sprayLoad_cos_symmetric :
    cosSymmetric sprayLoadTheme sprayLoadLocation = true := by native_decide

theorem sprayLoad_locative_data :
    loc_spray.result = .participates ∧ loc_load.result = .participates := ⟨rfl, rfl⟩

theorem sprayLoad_fragment :
    spray.levinClass = some .sprayLoad ∧
    load.levinClass = some .sprayLoad := ⟨rfl, rfl⟩

-- ── break class ──

def breakDirectObject : EntailmentProfile :=
  ⟨false, false, false, false, false, true, true, true, true, false⟩

def breakInstrument : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, false, false, false⟩

theorem break_cos_asymmetric :
    cosSymmetric breakDirectObject breakInstrument = false := by native_decide

theorem break_DO_more_patient :
    breakDirectObject.pPatientScore > breakInstrument.pPatientScore := by native_decide

theorem break_no_locative :
    LevinClass.break_.participatesIn .locative = false := by native_decide

-- ── hit class ──

def hitArg1 : EntailmentProfile :=
  ⟨false, false, false, false, true, false, false, true, true, false⟩

def hitArg2 : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, true, false, false⟩

theorem hit_cos_symmetric :
    cosSymmetric hitArg1 hitArg2 = true := by native_decide

theorem hit_no_cos :
    hitArg1.changeOfState = false ∧ hitArg2.changeOfState = false := ⟨rfl, rfl⟩

theorem hit_no_IT :
    hitArg1.incrementalTheme = false ∧ hitArg2.incrementalTheme = false := ⟨rfl, rfl⟩

theorem hit_alternation_data :
    con_hit.result = .participates ∧
    ci_hit.result = .blocked ∧
    mid_hit.result = .blocked := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Table 1: Agentivity × Telicity → Unaccusativity (§12, p.607)
-- ════════════════════════════════════════════════════

/-! @cite{dowty-1991} Table 1: the interaction of agentivity (most salient
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
    table1 runSubjectProfile.volition runSubjectProfile.changeOfState
    = .unergative := rfl

theorem die_cell4 :
    table1 dieSubjectProfile.volition dieSubjectProfile.changeOfState
    = .unaccusative := by native_decide

-- ════════════════════════════════════════════════════
-- § 5. Flat Counting vs Modern ASP: The Arrive Anomaly
-- ════════════════════════════════════════════════════

/-! The key divergence between @cite{dowty-1991}'s flat counting and the
    modern priority-based ASP. Flat counting gets arrive wrong because it
    counts movement + IE (2 P-Agent) > changeOfState (1 P-Patient), predicting
    unergative. The modern ASP correctly identifies arrive as unaccusative
    because it lacks the priority features (volition, causation). -/

/-- Flat counting predicts arrive is NOT unaccusative (2 P-Ag > 1 P-Pat). -/
theorem arrive_flat_wrong :
    flatPredictsUnaccusative arriveSubjectProfile = false := by native_decide

/-- Modern priority-based ASP correctly predicts arrive IS unaccusative. -/
theorem arrive_modern_correct :
    predictsUnaccusative arriveSubjectProfile = true := by native_decide

/-- Table 1 also correctly predicts arrive as unaccusative
    (non-agentive + telic = cell 4). -/
theorem arrive_table1_correct :
    table1 arriveSubjectProfile.volition arriveSubjectProfile.changeOfState
    = .unaccusative := by native_decide

/-- Agreement: Table 1 and the modern ASP converge on arrive being
    unaccusative. Flat counting diverges — this is the anomaly that
    motivated @cite{davis-koenig-2000}'s priority refinement. -/
theorem arrive_anomaly_summary :
    -- Table 1: unaccusative (correct)
    table1 arriveSubjectProfile.volition arriveSubjectProfile.changeOfState
      = .unaccusative ∧
    -- Modern ASP: unaccusative (correct)
    predictsUnaccusative arriveSubjectProfile = true ∧
    -- Flat counting: NOT unaccusative (WRONG)
    flatPredictsUnaccusative arriveSubjectProfile = false ∧
    -- Fragment annotation: unaccusative (ground truth)
    arrive.unaccusative = true := ⟨by native_decide, by native_decide, by native_decide, rfl⟩

/-- Flat counting gets die right (both methods agree). -/
theorem die_both_agree :
    flatPredictsUnaccusative dieSubjectProfile = true ∧
    predictsUnaccusative dieSubjectProfile = true := ⟨by native_decide, by native_decide⟩

/-- Flat counting gets run right (both methods agree). -/
theorem run_both_agree :
    flatPredictsUnergative runSubjectProfile = true ∧
    predictsUnergative runSubjectProfile = true := ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 6. Fragment Bridge: Profiles Match VerbCore Fields
-- ════════════════════════════════════════════════════

/-! These theorems verify that the canonical verb profiles in
    `ProtoRoles.lean` match the entailment profiles stored on the
    English Fragment verb entries. -/

theorem kick_subject_profile_matches :
    kick.toVerbCore.subjectEntailments = some kickSubjectProfile := rfl

theorem kick_object_profile_matches :
    kick.toVerbCore.objectEntailments = some kickObjectProfile := rfl

theorem eat_subject_profile_matches :
    eat.toVerbCore.subjectEntailments = some eatSubjectProfile := rfl

theorem eat_object_profile_matches :
    eat.toVerbCore.objectEntailments = some eatObjectProfile := rfl

theorem build_subject_profile_matches :
    build.toVerbCore.subjectEntailments = some buildSubjectProfile := rfl

theorem build_object_profile_matches :
    build.toVerbCore.objectEntailments = some buildObjectProfile := rfl

theorem run_subject_profile_matches :
    run.toVerbCore.subjectEntailments = some runSubjectProfile := rfl

theorem arrive_subject_profile_matches :
    arrive.toVerbCore.subjectEntailments = some arriveSubjectProfile := rfl

theorem see_subject_profile_matches :
    see.toVerbCore.subjectEntailments = some seeSubjectProfile := rfl

theorem sweep_subject_profile_matches :
    sweep.toVerbCore.subjectEntailments = some sweepBasicSubjectProfile := rfl

theorem sweep_instr_subject_profile_matches :
    sweep_instr.toVerbCore.subjectEntailments = some sweepBroomSubjectProfile := rfl

-- ════════════════════════════════════════════════════
-- § 7. Fragment Bridge: Predictions Match Annotations
-- ════════════════════════════════════════════════════

/-- Agreement: arrive prediction matches the fragment annotation. -/
theorem arrive_prediction_matches_fragment :
    predictsUnaccusative arriveSubjectProfile =
    arrive.unaccusative := by native_decide

/-- Agreement: run prediction matches the fragment annotation. -/
theorem run_prediction_matches_fragment :
    predictsUnaccusative runSubjectProfile =
    Fragments.English.Predicates.Verbal.run.unaccusative := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Cross-Theory: @cite{grimm-2011} Lattice Predictions
-- ════════════════════════════════════════════════════

/-! @cite{grimm-2011}'s agentivity lattice reformulates Dowty's proto-roles
    with lattice structure and connects them to case assignment. Here we
    verify that Grimm's lattice predictions are consistent with the ASP
    predictions above, and that it also resolves the arrive anomaly. -/

open Semantics.Lexical.Verb.AgentivityLattice

/-- Grimm's lattice handles the arrive anomaly: arrive's subject has
    motion but not instigation → not in the NOM/ERG region. Consistent
    with the priority-based ASP and Table 1, but not flat counting. -/
theorem arrive_grimm_not_nom :
    (GrimmNode.fromSubjectProfile arriveSubjectProfile).toCaseRegion ≠ .nomErg := by
  native_decide

/-- Full cross-theory convergence on arrive: Table 1, modern ASP, and
    @cite{grimm-2011}'s lattice all predict unaccusative/non-agent.
    Only flat counting diverges. -/
theorem arrive_cross_theory :
    table1 arriveSubjectProfile.volition arriveSubjectProfile.changeOfState
      = .unaccusative ∧
    predictsUnaccusative arriveSubjectProfile = true ∧
    flatPredictsUnaccusative arriveSubjectProfile = false ∧
    (GrimmNode.fromSubjectProfile arriveSubjectProfile).toCaseRegion ≠ .nomErg ∧
    arrive.unaccusative = true :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide, rfl⟩

/-- Kick: ASP outranking and @cite{grimm-2011}'s case regions converge.
    Subject → NOM, object → ACC in an accusative system. -/
theorem kick_asp_grimm_consistent :
    outranksForSubject kickSubjectProfile kickObjectProfile = true ∧
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion.toAccusativeCase
      = .nom ∧
    (GrimmNode.fromObjectProfile kickObjectProfile).toCaseRegion.toAccusativeCase
      = .acc :=
  ⟨by native_decide, by native_decide, by native_decide⟩

/-- Die: ASP, flat counting, and @cite{grimm-2011} all agree on unaccusative.
    Grimm's lattice maps the sole argument to ACC/ABS (patient region). -/
theorem die_asp_grimm_consistent :
    predictsUnaccusative dieSubjectProfile = true ∧
    flatPredictsUnaccusative dieSubjectProfile = true ∧
    (GrimmNode.fromObjectProfile dieSubjectProfile).toCaseRegion = .accAbs :=
  ⟨by native_decide, by native_decide, by native_decide⟩

end Phenomena.ArgumentStructure.Studies.Dowty1991
