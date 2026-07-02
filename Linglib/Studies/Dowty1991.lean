import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.ArgumentStructure.Agentivity.CaseRegions
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Fragments.English.Predicates.Verbal

/-!
# [dowty-1991] Thematic Proto-Roles and Argument Selection

Study file connecting the proto-role theory (`Semantics/Events/ProtoRoles.lean`)
to argument selection phenomena.

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

open Semantics.Lexical
open ArgumentStructure (EntailmentProfile)
open ArgumentStructure.EntailmentProfile
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
    table1 runSubjectProfile.volition runSubjectProfile.changeOfState
    = .unergative := rfl

theorem die_cell4 :
    table1 dieSubjectProfile.volition dieSubjectProfile.changeOfState
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
    flatPredictsUnaccusative arriveSubjectProfile = false := by decide

/-- Modern priority-based ASP correctly predicts arrive IS unaccusative. -/
theorem arrive_modern_correct :
    PredictsUnaccusative arriveSubjectProfile := by decide

/-- Table 1 also correctly predicts arrive as unaccusative
    (non-agentive + telic = cell 4). -/
theorem arrive_table1_correct :
    table1 arriveSubjectProfile.volition arriveSubjectProfile.changeOfState
    = .unaccusative := by decide

/-- Agreement: Table 1 and the modern ASP converge on arrive being
    unaccusative. Flat counting diverges — this is the anomaly that
    motivated [davis-koenig-2000]'s priority refinement. -/
theorem arrive_anomaly_summary :
    -- Table 1: unaccusative (correct)
    table1 arriveSubjectProfile.volition arriveSubjectProfile.changeOfState
      = .unaccusative ∧
    -- Modern ASP: unaccusative (correct)
    PredictsUnaccusative arriveSubjectProfile ∧
    -- Flat counting: NOT unaccusative (WRONG)
    flatPredictsUnaccusative arriveSubjectProfile = false ∧
    -- Fragment annotation: unaccusative (ground truth)
    arrive.unaccusative = true := ⟨by decide, by decide, by decide, rfl⟩

/-- Flat counting gets die right (both methods agree). -/
theorem die_both_agree :
    flatPredictsUnaccusative dieSubjectProfile = true ∧
    PredictsUnaccusative dieSubjectProfile := ⟨by decide, by decide⟩

/-- Flat counting gets run right (both methods agree). -/
theorem run_both_agree :
    flatPredictsUnergative runSubjectProfile = true ∧
    PredictsUnergative runSubjectProfile := ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 6. Fragment Bridge: Profiles Match Verb Fields
-- ════════════════════════════════════════════════════

/-! These theorems verify that the canonical verb profiles in
    `ProtoRoles.lean` match the entailment profiles stored on the
    English Fragment verb entries. -/

theorem kick_subject_profile_matches :
    kick.toVerb.subjectEntailments = some kickSubjectProfile := rfl

theorem kick_object_profile_matches :
    kick.toVerb.objectEntailments = some kickObjectProfile := rfl

theorem eat_subject_profile_matches :
    eat.toVerb.subjectEntailments = some eatSubjectProfile := rfl

theorem eat_object_profile_matches :
    eat.toVerb.objectEntailments = some eatObjectProfile := rfl

theorem build_subject_profile_matches :
    build.toVerb.subjectEntailments = some buildSubjectProfile := rfl

theorem build_object_profile_matches :
    build.toVerb.objectEntailments = some buildObjectProfile := rfl

theorem run_subject_profile_matches :
    run.toVerb.subjectEntailments = some runSubjectProfile := rfl

theorem arrive_subject_profile_matches :
    arrive.toVerb.subjectEntailments = some arriveSubjectProfile := rfl

theorem see_subject_profile_matches :
    see.toVerb.subjectEntailments = some seeSubjectProfile := rfl

theorem sweep_subject_profile_matches :
    sweep.toVerb.subjectEntailments = some sweepBasicSubjectProfile := rfl

theorem sweep_instr_subject_profile_matches :
    sweep_instr.toVerb.subjectEntailments = some sweepBroomSubjectProfile := rfl

-- ════════════════════════════════════════════════════
-- § 7. Fragment Bridge: Predictions Match Annotations
-- ════════════════════════════════════════════════════

/-- Agreement: arrive prediction matches the fragment annotation. -/
theorem arrive_prediction_matches_fragment :
    decide (PredictsUnaccusative arriveSubjectProfile) =
    arrive.unaccusative := by decide

/-- Agreement: run prediction matches the fragment annotation. -/
theorem run_prediction_matches_fragment :
    decide (PredictsUnaccusative runSubjectProfile) =
    English.Predicates.Verbal.run.unaccusative := by decide

-- ════════════════════════════════════════════════════
-- § 8. Cross-Theory: [grimm-2011] Lattice Predictions
-- ════════════════════════════════════════════════════

/-! [grimm-2011]'s agentivity lattice reformulates Dowty's proto-roles
    with lattice structure and connects them to case assignment. Here we
    verify that Grimm's lattice predictions are consistent with the ASP
    predictions above, and that it also resolves the arrive anomaly. -/

open ArgumentStructure.AgentivityLattice

/-- Grimm's lattice handles the arrive anomaly: arrive's subject has
    motion but not instigation → not in the NOM/ERG region. Consistent
    with the priority-based ASP and Table 1, but not flat counting. -/
theorem arrive_grimm_not_nom :
    (GrimmNode.fromSubjectProfile arriveSubjectProfile).toCaseRegion ≠ .nomErg := by
  decide

/-- Full cross-theory convergence on arrive: Table 1, modern ASP, and
    [grimm-2011]'s lattice all predict unaccusative/non-agent.
    Only flat counting diverges. -/
theorem arrive_cross_theory :
    table1 arriveSubjectProfile.volition arriveSubjectProfile.changeOfState
      = .unaccusative ∧
    PredictsUnaccusative arriveSubjectProfile ∧
    flatPredictsUnaccusative arriveSubjectProfile = false ∧
    (GrimmNode.fromSubjectProfile arriveSubjectProfile).toCaseRegion ≠ .nomErg ∧
    arrive.unaccusative = true :=
  ⟨by decide, by decide, by decide, by decide, rfl⟩

/-- Kick: ASP outranking and [grimm-2011]'s case regions converge.
    Subject → NOM, object → ACC in an accusative system. -/
theorem kick_asp_grimm_consistent :
    OutranksForSubject kickSubjectProfile kickObjectProfile ∧
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion.toAccusativeCase
      = .nom ∧
    (GrimmNode.fromObjectProfile kickObjectProfile).toCaseRegion.toAccusativeCase
      = .acc :=
  ⟨by decide, by decide, by decide⟩

/-- Die: ASP, flat counting, and [grimm-2011] all agree on unaccusative.
    Grimm's lattice maps the sole argument to ACC/ABS (patient region). -/
theorem die_asp_grimm_consistent :
    PredictsUnaccusative dieSubjectProfile ∧
    flatPredictsUnaccusative dieSubjectProfile = true ∧
    (GrimmNode.fromObjectProfile dieSubjectProfile).toCaseRegion = .accAbs :=
  ⟨by decide, by decide, by decide⟩

/-- Kiss on [grimm-2011]'s Fig. 1 lattice: the object's agentivity node
    {motion} sits strictly below the subject's {volition, motion} — the §1
    asymmetry restated as strict lattice dominance. -/
theorem kiss_subject_dominates :
    AgentivityNode.fromEntailmentProfile kissObjectProfile <
    AgentivityNode.fromEntailmentProfile kissSubjectProfile := by decide

/-- Corollary: the flat-count direction follows from lattice dominance via
    `featureCount_monotone` and `pAgentScore_decomposition` — Dowty's
    counting comparison (`kiss_asymmetry_is_volition`) is demoted to a
    consequence of Grimm's order. -/
theorem kiss_flat_count_from_lattice :
    kissObjectProfile.pAgentScore ≤ kissSubjectProfile.pAgentScore := by
  rw [pAgentScore_decomposition, pAgentScore_decomposition]
  exact Nat.add_le_add
    (AgentivityNode.featureCount_monotone kiss_subject_dominates.le) le_rfl

end Dowty1991
