import Linglib.Theories.Semantics.Events.ProtoRoles
import Linglib.Phenomena.ArgumentStructure.DiathesisAlternations.Data
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{dowty-1991} Thematic Proto-Roles and Argument Selection

Study file connecting the proto-role theory (`Theories/Semantics/Events/ProtoRoles.lean`)
to argument selection phenomena.

## Key predictions formalized

- §9.1: Partially symmetric interactive predicates — volition as asymmetric P-Agent
- §9.2: Psych verb doublets — inchoative change-of-state breaks ties
- §9.3: Three verb classes (spray/load, break, hit) — CoS symmetry predicts alternation
- §12: Agentivity × telicity → unaccusativity (Table 1)
-/

namespace Phenomena.ArgumentStructure.Studies.Dowty1991

open Semantics.Events.ProtoRoles
open Phenomena.ArgumentStructure.DiathesisAlternations.Data
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. Between-Argument ASP (@cite{dowty-1991} p.576, ex.31)
-- ════════════════════════════════════════════════════

/-- @cite{dowty-1991}'s ASP stated as a between-argument comparison:
    arg1 outranks arg2 for subjecthood iff arg1 has strictly more
    P-Agent entailments, OR they tie on P-Agent but arg2 has
    strictly more P-Patient entailments (making arg2 the "better"
    object, hence arg1 the subject by exclusion). -/
def outranksForSubject (arg1 arg2 : EntailmentProfile) : Bool :=
  arg1.pAgentScore > arg2.pAgentScore ||
  (arg1.pAgentScore == arg2.pAgentScore &&
   arg2.pPatientScore > arg1.pPatientScore)

/-- Corollary 1: neither argument outranks the other → alternation. -/
def aspAlternation (arg1 arg2 : EntailmentProfile) : Bool :=
  !outranksForSubject arg1 arg2 && !outranksForSubject arg2 arg1

-- ════════════════════════════════════════════════════
-- § 2. Partially Symmetric Interactive Predicates (§9.1, pp.583–586)
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

/-- The subject outranks the object: volition is the sole asymmetric entailment. -/
theorem kiss_subject_outranks :
    outranksForSubject kissSubjectProfile kissObjectProfile = true := by native_decide

/-- Volition adds exactly 1 to the subject's P-Agent score. -/
theorem kiss_asymmetry_is_volition :
    kissSubjectProfile.pAgentScore = kissObjectProfile.pAgentScore + 1 := by
  native_decide

/-- The collective intransitive ("Kim and Sandy kissed") is predicted:
    when both participants have symmetric volition, neither outranks
    the other → the transitive form is not required. -/
theorem kiss_collective_alternation :
    aspAlternation kissSubjectProfile kissSubjectProfile = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Psych Verb Doublets (§9.2, pp.579–581)
-- ════════════════════════════════════════════════════

/-! Psych verbs come in doublets (like/please, fear/frighten) with reversed
    argument configurations. Under the stative reading, Experiencer and
    Stimulus have equal P-Agent scores → alternation is predicted. Under
    the inchoative reading (available only for Stimulus-subject verbs),
    the Experiencer gains a P-Patient entailment (change of state) that
    breaks the tie. -/

/-- Stative: Experiencer (S+IE) and Stimulus (C+IE) have equal P-Agent
    scores (both 2) and equal P-Patient scores (both 0) → alternation. -/
theorem psychStative_alternation :
    aspAlternation
      (ThetaRole.canonicalProfile .experiencer)
      (ThetaRole.canonicalProfile .stimulus) = true := by native_decide

/-- Under inchoative interpretation, the Experiencer enters a new mental
    state → gains changeOfState (P-Patient entailment a). -/
def expInchoativeProfile : EntailmentProfile :=
  ⟨false, true, false, false, true, true, false, false, false, false⟩

/-- The Stimulus profile is unchanged under inchoative reading. -/
def stimProfile : EntailmentProfile := ThetaRole.canonicalProfile .stimulus

/-- Inchoative breaks the tie: Stimulus outranks Experiencer for subject
    because the Experiencer now has more P-Patient (CoS) → Experiencer
    is a "better" object → Stimulus is subject. Predicts StimExp frame. -/
theorem psych_inchoative_stimulus_is_subject :
    outranksForSubject stimProfile expInchoativeProfile = true := by native_decide

/-- The mechanism: P-Agent remains tied; P-Patient diverges. -/
theorem psych_inchoative_mechanism :
    stimProfile.pAgentScore = expInchoativeProfile.pAgentScore ∧
    expInchoativeProfile.pPatientScore > stimProfile.pPatientScore := by
  exact ⟨by native_decide, by native_decide⟩

/-- Bridge: fragment records frighten/surprise as stimulus-subject. -/
theorem stimExp_fragment :
    frighten.subjectTheta = some .stimulus ∧
    surprise.subjectTheta = some .stimulus := ⟨rfl, rfl⟩

/-- Bridge: fragment records like/fear as experiencer-subject. -/
theorem expStim_fragment :
    like.subjectTheta = some .experiencer ∧
    fear.subjectTheta = some .experiencer := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Three Verb Classes (§9.3, pp.587–597)
-- ════════════════════════════════════════════════════

/-! @cite{dowty-1991} identifies three classes of verbs with multiple possible
    argument configurations, each predicted by how change-of-state (CoS)
    is distributed across non-subject arguments:

    | Class | CoS distribution | Alternation |
    |------------|------------------|-------------|
    | spray/load | both args | yes |
    | break | one arg only | no |
    | hit | neither arg | yes |

    When CoS is symmetric (both or neither), alternation is possible.
    When CoS is asymmetric, the CoS argument is fixed as direct object. -/

/-- CoS symmetry predicts alternation possibility for three-place verbs:
    alternation is blocked only when exactly one argument has CoS. -/
def cosSymmetric (arg1 arg2 : EntailmentProfile) : Bool :=
  arg1.changeOfState == arg2.changeOfState

-- ── spray/load class ──

/-- spray/load Theme argument (hay in "load hay onto the truck"):
    undergoes CoS (changes location) and is causally affected. -/
def sprayLoadTheme : EntailmentProfile :=
  ⟨false, false, false, false, true, true, false, true, false, false⟩

/-- spray/load Location argument (truck in "load hay onto the truck"):
    undergoes CoS (changes from empty to loaded), stationary. -/
def sprayLoadLocation : EntailmentProfile :=
  ⟨false, false, false, false, true, true, false, true, true, false⟩

/-- spray/load: both non-subject args have CoS → symmetric → alternation. -/
theorem sprayLoad_cos_symmetric :
    cosSymmetric sprayLoadTheme sprayLoadLocation = true := by native_decide

/-- Bridge: spray and load participate in the locative alternation. -/
theorem sprayLoad_locative_data :
    loc_spray.result = .participates ∧ loc_load.result = .participates := ⟨rfl, rfl⟩

/-- Bridge: spray and load are sprayLoad class in the fragment. -/
theorem sprayLoad_fragment :
    spray.levinClass = some .sprayLoad ∧
    load.levinClass = some .sprayLoad := ⟨rfl, rfl⟩

-- ── break class ──

/-- break direct object (fence in "broke the fence with the stick"):
    undergoes visible, permanent CoS. Is incremental theme. -/
def breakDirectObject : EntailmentProfile :=
  ⟨false, false, false, false, false, true, true, true, true, false⟩

/-- break instrument (stick): no CoS, no IT — it's a P-Agent (moves). -/
def breakInstrument : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, false, false, false⟩

/-- break: CoS is asymmetric → the CoS argument is fixed as DO → no alternation. -/
theorem break_cos_asymmetric :
    cosSymmetric breakDirectObject breakInstrument = false := by native_decide

/-- The CoS argument has strictly more P-Patient → ASP fixes it as DO. -/
theorem break_DO_more_patient :
    breakDirectObject.pPatientScore > breakInstrument.pPatientScore := by native_decide

/-- Bridge: break does NOT participate in the locative alternation. -/
theorem break_no_locative :
    LevinClass.break_.participatesIn .locative = false := by native_decide

-- ── hit class ──

/-- hit non-subject arguments: neither undergoes CoS or is IT.
    @cite{dowty-1991} (p.595): "No difference in proto-role entailments
    between arguments (but concerning motion)." Motion/stationarity
    creates asymmetry but Dowty argues it is irrelevant for DO
    selection (p.596). -/
def hitArg1 : EntailmentProfile :=
  ⟨false, false, false, false, true, false, false, true, true, false⟩

def hitArg2 : EntailmentProfile :=
  ⟨false, false, false, true, true, false, false, true, false, false⟩

/-- hit: neither arg has CoS → symmetric → alternation. -/
theorem hit_cos_symmetric :
    cosSymmetric hitArg1 hitArg2 = true := by native_decide

/-- Neither argument undergoes change of state. -/
theorem hit_no_cos :
    hitArg1.changeOfState = false ∧ hitArg2.changeOfState = false := ⟨rfl, rfl⟩

/-- Neither argument is an incremental theme. -/
theorem hit_no_IT :
    hitArg1.incrementalTheme = false ∧ hitArg2.incrementalTheme = false := ⟨rfl, rfl⟩

/-- Bridge: hit participates in conative (motion/contact) but not in CI
    or middle (both require CoS, which hit lacks). -/
theorem hit_alternation_data :
    con_hit.result = .participates ∧
    ci_hit.result = .blocked ∧
    mid_hit.result = .blocked := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Table 1: Agentivity × Telicity → Unaccusativity (§12, p.607)
-- ════════════════════════════════════════════════════

/-! @cite{dowty-1991} Table 1: the interaction of agentivity (most salient
    P-Agent property) and telicity (most salient P-Patient property) predicts
    the unergative/unaccusative split. Only the two "pure" cells are stable;
    the mixed cells are where cross-linguistic variation occurs. -/

/-- Table 1 as a function: volition (most diagnostic P-Agent entailment)
    × change-of-state (most diagnostic P-Patient entailment). -/
inductive IntransClass where
  | unergative    -- cell 1: agentive + atelic (run, walk, swim)
  | unaccusative  -- cell 4: non-agentive + telic (die, arrive, melt)
  | unstable      -- cells 2, 3: mixed — cross-linguistic variation
  deriving DecidableEq, Repr, BEq

def table1 (agentive telic : Bool) : IntransClass :=
  match agentive, telic with
  | true, false  => .unergative
  | false, true  => .unaccusative
  | _, _         => .unstable

theorem cell1_unergative : table1 true false = .unergative := rfl
theorem cell4_unaccusative : table1 false true = .unaccusative := rfl
theorem cell2_unstable : table1 true true = .unstable := rfl
theorem cell3_unstable : table1 false false = .unstable := rfl

/-- run: volitional + no CoS → cell 1 (unergative). -/
theorem run_cell1 :
    table1 runSubjectProfile.volition runSubjectProfile.changeOfState
    = .unergative := rfl

/-- die: no volition + CoS → cell 4 (unaccusative). -/
theorem die_cell4 :
    table1 dieSubjectProfile.volition dieSubjectProfile.changeOfState
    = .unaccusative := by native_decide

/-- Agreement: Table 1 predictions match the entailment-counting predictions. -/
theorem cell1_agrees_predictsUnergative :
    predictsUnergative runSubjectProfile = true := by native_decide

theorem cell4_agrees_predictsUnaccusative :
    predictsUnaccusative dieSubjectProfile = true := by native_decide

/-- Arrive illustrates the coarser Table 1 vs finer entailment counting:
    Table 1 puts it in cell 4 (non-agentive + telic → unaccusative),
    but full counting gives P-Ag=2, P-Pat=1 → unergative prediction.
    The fragment records it as unaccusative, siding with Table 1. -/
theorem arrive_table1_vs_counting :
    table1 arriveSubjectProfile.volition arriveSubjectProfile.changeOfState
      = .unaccusative ∧
    predictsUnaccusative arriveSubjectProfile = false ∧
    arrive.unaccusative = true := ⟨rfl, by native_decide, rfl⟩

end Phenomena.ArgumentStructure.Studies.Dowty1991
