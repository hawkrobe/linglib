import Linglib.Phenomena.Complementation.Typology
import Linglib.Theories.Montague.Question.LeftPeriphery
import Linglib.Theories.Montague.Sentence.Mood.Basic

/-! # Complementation Bridge Theorems

Interconnection theorems linking Noonan's (2007) complementation typology
to existing linglib infrastructure:

1. CTPClass ↔ VerbEntry (Verbal.lean) — derive CTP class from verb features
2. CTPClass ↔ SelectionClass (LeftPeriphery.lean) — map CTP to question embedding
3. CTPClass ↔ MoodSelector (Mood/Basic.lean) — map CTP to mood selection
4. ComplementType ↔ NoonanCompType — map English-specific to typological categories
5. VerbEntry → MoodSelector — derive mood selection from verb features

## References

- Noonan, M. (2007). Complementation. In T. Shopen (ed.), Language Typology
  and Syntactic Description, vol. 2, 2nd ed. Cambridge University Press.
- Dayal, V. (2025). The Interrogative Left Periphery.
- Mendes, A. (2025). Indefiniteness in future reference.
-/

namespace Phenomena.Complementation.Bridge

open Phenomena.Complementation.Typology
open Fragments.English.Predicates.Verbal
open Montague.Question.LeftPeriphery
open Montague.Sentence.Mood

-- ============================================================================
-- A. Bridge 1: CTPClass ↔ VerbEntry
-- ============================================================================

/-! ## A1. Derive CTPClass from VerbEntry fields

CTPClass is DERIVED from existing VerbEntry fields — not added as a new field.
This follows the `deriveSelectionClass` pattern from LeftPeriphery.lean. -/

/-- Derive Noonan's CTP class from a VerbEntry's structural properties.

    The mapping uses `verbClass`, `complementType`, and `attitudeBuilder`:
    - .factive → knowledge (know, regret, realize)
    - .semifactive → knowledge (discover, notice)
    - .perception → perception (see)
    - .communication → utterance (say, tell)
    - .changeOfState → phasal (stop, start, continue)
    - .causative → manipulative (cause, make, force)
    - .implicative → achievement (manage, fail)
    - .attitude + doxastic → propAttitude (believe, think)
    - .attitude + preferential positive → desiderative (want, hope)
    - .attitude + preferential negative → propAttitude (fear: reacts to, doesn't desire)
    - .attitude + preferential uncertaintyBased → propAttitude (worry)
    - Otherwise → none -/
def deriveCTPClass (v : VerbEntry) : Option CTPClass :=
  match v.verbClass, v.complementType, v.attitudeBuilder with
  | .factive, _, _ => some .knowledge
  | .semifactive, _, _ => some .knowledge
  | .perception, _, _ => some .perception
  | .communication, _, _ => some .utterance
  | .changeOfState, _, _ => some .phasal
  | .causative, _, _ => some .manipulative
  | .implicative, _, _ => some .achievement
  | .attitude, _, some (.doxastic _) => some .propAttitude
  | .attitude, _, some (.preferential (.degreeComparison .positive)) => some .desiderative
  | .attitude, _, some (.preferential (.degreeComparison .negative)) => some .propAttitude
  | .attitude, _, some (.preferential .uncertaintyBased) => some .propAttitude
  | .attitude, _, some (.preferential (.relevanceBased _)) => some .propAttitude
  | _, _, _ => none

/-! ## A2. Per-verb verification theorems

Each theorem is proved by `native_decide`. Changing one VerbEntry field
breaks exactly one theorem. -/

-- Knowledge CTPs (factive/semifactive)
theorem know_is_knowledge :
    deriveCTPClass know = some .knowledge := by native_decide
theorem regret_is_knowledge :
    deriveCTPClass regret = some .knowledge := by native_decide
theorem realize_is_knowledge :
    deriveCTPClass realize = some .knowledge := by native_decide
theorem discover_is_knowledge :
    deriveCTPClass discover = some .knowledge := by native_decide
theorem notice_is_knowledge :
    deriveCTPClass notice = some .knowledge := by native_decide
theorem remember_q_is_knowledge :
    deriveCTPClass remember_q = some .knowledge := by native_decide
theorem forget_q_is_knowledge :
    deriveCTPClass forget_q = some .knowledge := by native_decide

-- Perception CTPs
theorem see_is_perception :
    deriveCTPClass see = some .perception := by native_decide

-- Utterance CTPs (communication)
theorem say_is_utterance :
    deriveCTPClass say = some .utterance := by native_decide
theorem tell_is_utterance :
    deriveCTPClass tell = some .utterance := by native_decide
theorem claim_is_utterance :
    deriveCTPClass claim = some .utterance := by native_decide
theorem ask_is_utterance :
    deriveCTPClass ask = some .utterance := by native_decide

-- PropAttitude CTPs (doxastic)
theorem believe_is_propAttitude :
    deriveCTPClass believe = some .propAttitude := by native_decide
theorem think_is_propAttitude :
    deriveCTPClass think = some .propAttitude := by native_decide

-- Desiderative CTPs (preferential positive)
theorem want_is_desiderative :
    deriveCTPClass want = some .desiderative := by native_decide
theorem hope_is_desiderative :
    deriveCTPClass hope = some .desiderative := by native_decide
theorem expect_is_desiderative :
    deriveCTPClass expect = some .desiderative := by native_decide
theorem wish_is_desiderative :
    deriveCTPClass wish = some .desiderative := by native_decide

-- PropAttitude via negative preferential (fear, dread react to rather than desire)
theorem fear_is_propAttitude :
    deriveCTPClass fear = some .propAttitude := by native_decide
theorem dread_is_propAttitude :
    deriveCTPClass dread = some .propAttitude := by native_decide
theorem worry_is_propAttitude :
    deriveCTPClass worry = some .propAttitude := by native_decide

-- Phasal CTPs (changeOfState)
theorem stop_is_phasal :
    deriveCTPClass stop = some .phasal := by native_decide
theorem quit_is_phasal :
    deriveCTPClass quit = some .phasal := by native_decide
theorem start_is_phasal :
    deriveCTPClass start = some .phasal := by native_decide
theorem begin_is_phasal :
    deriveCTPClass begin_ = some .phasal := by native_decide
theorem continue_is_phasal :
    deriveCTPClass continue_ = some .phasal := by native_decide
theorem keep_is_phasal :
    deriveCTPClass keep = some .phasal := by native_decide

-- Manipulative CTPs (causative)
theorem cause_is_manipulative :
    deriveCTPClass cause = some .manipulative := by native_decide
theorem make_is_manipulative :
    deriveCTPClass make = some .manipulative := by native_decide
theorem let_is_manipulative :
    deriveCTPClass let_ = some .manipulative := by native_decide
theorem have_causative_is_manipulative :
    deriveCTPClass have_causative = some .manipulative := by native_decide
theorem get_causative_is_manipulative :
    deriveCTPClass get_causative = some .manipulative := by native_decide
theorem force_is_manipulative :
    deriveCTPClass force = some .manipulative := by native_decide

-- Achievement CTPs (implicative)
theorem manage_is_achievement :
    deriveCTPClass manage = some .achievement := by native_decide
theorem fail_is_achievement :
    deriveCTPClass fail = some .achievement := by native_decide
theorem remember_inf_is_achievement :
    deriveCTPClass remember = some .achievement := by native_decide
theorem forget_inf_is_achievement :
    deriveCTPClass forget = some .achievement := by native_decide

-- Simple verbs have no CTP class (not complement-taking)
theorem sleep_no_ctp :
    deriveCTPClass sleep = none := by native_decide
theorem run_no_ctp :
    deriveCTPClass run = none := by native_decide
theorem arrive_no_ctp :
    deriveCTPClass arrive = none := by native_decide
theorem eat_no_ctp :
    deriveCTPClass eat = none := by native_decide
theorem kick_no_ctp :
    deriveCTPClass kick = none := by native_decide

-- ============================================================================
-- B. Bridge 2: CTPClass ↔ SelectionClass (LeftPeriphery.lean)
-- ============================================================================

/-! ## B1. Map Noonan's CTP classes to Dayal's selection classes

This connects two independent typological systems:
- Noonan (2007): CTP semantics → complement type
- Dayal (2025): Predicate semantics → left-peripheral selection -/

/-- Default mapping from CTP class to selection class.

    - Knowledge → responsive (know, remember: entail knowledge of answer)
    - Utterance → rogativeSAP (ask, tell: speech-act layer)
    - PropAttitude → uninterrogative (believe, think: no question embedding)
    - Desiderative → uninterrogative (want, hope: anti-rogative)
    - Perception → responsive (see: factive perception of answer)
    - Achievement → uninterrogative (manage: no question embedding)
    - Phasal → uninterrogative (stop: no question embedding)
    - Manipulative → uninterrogative (make: no question embedding)
    - Others → uninterrogative -/
def ctpToDefaultSelectionClass : CTPClass → SelectionClass
  | .knowledge => .responsive
  | .utterance => .rogativeSAP
  | .propAttitude => .uninterrogative
  | .desiderative => .uninterrogative
  | .perception => .responsive
  | .achievement => .uninterrogative
  | .phasal => .uninterrogative
  | .manipulative => .uninterrogative
  | .commentative => .uninterrogative
  | .pretence => .uninterrogative
  | .modal => .uninterrogative
  | .negative => .uninterrogative

/-! ## B2. Consistency with deriveSelectionClass

Verify that for verbs where CTP class is defined AND the verb takes questions,
the two derivations agree. Note: many CTPs don't embed questions at all,
so the comparison is only meaningful for question-taking verbs. -/

/-- For question-embedding verbs with a CTP class, the CTP-based mapping
    matches the structural derivation from LeftPeriphery.lean.

    This covers: know, discover, remember_q, forget_q (knowledge → responsive),
    ask (utterance → rogativeSAP). -/
theorem ctp_selection_consistent_know :
    ctpToDefaultSelectionClass .knowledge = deriveSelectionClass know := by native_decide
theorem ctp_selection_consistent_discover :
    ctpToDefaultSelectionClass .knowledge = deriveSelectionClass discover := by native_decide
theorem ctp_selection_consistent_remember_q :
    ctpToDefaultSelectionClass .knowledge = deriveSelectionClass remember_q := by native_decide
theorem ctp_selection_consistent_forget_q :
    ctpToDefaultSelectionClass .knowledge = deriveSelectionClass forget_q := by native_decide
theorem ctp_selection_consistent_ask :
    ctpToDefaultSelectionClass .utterance = deriveSelectionClass ask := by native_decide

-- ============================================================================
-- C. Bridge 3: CTPClass ↔ MoodSelector (Mood/Basic.lean)
-- ============================================================================

/-! ## C1. Map CTP classes to mood selection

This connects Noonan's semantic CTP classes to Mendes' (2025) mood semantics.
The realis/irrealis split predicts mood selection. -/

/-- Map CTP class to mood selection.
    Realis CTPs select indicative; irrealis select subjunctive.
    Some are language-dependent (moodNeutral). -/
def ctpToMoodSelector : CTPClass → MoodSelector
  | .knowledge => .indicativeSelecting
  | .utterance => .moodNeutral        -- "say" varies: IND in English, SUBJ in some Romance
  | .propAttitude => .indicativeSelecting
  | .commentative => .indicativeSelecting
  | .perception => .indicativeSelecting
  | .desiderative => .subjunctiveSelecting
  | .manipulative => .subjunctiveSelecting
  | .modal => .subjunctiveSelecting
  | .achievement => .moodNeutral      -- "manage" varies
  | .phasal => .moodNeutral           -- "start" varies
  | .pretence => .subjunctiveSelecting
  | .negative => .subjunctiveSelecting

/-- Realis CTPs select indicative or are mood-neutral (never subjunctive-selecting). -/
theorem realis_not_subjunctive :
    ∀ c : CTPClass,
      ctpRealityStatus c = .realis →
      ctpToMoodSelector c ≠ .subjunctiveSelecting := by
  intro c h
  cases c <;> simp_all [ctpRealityStatus, ctpToMoodSelector]

/-- Irrealis CTPs select subjunctive or are mood-neutral (never indicative-selecting). -/
theorem irrealis_not_indicative :
    ∀ c : CTPClass,
      ctpRealityStatus c = .irrealis →
      ctpToMoodSelector c ≠ .indicativeSelecting := by
  intro c h
  cases c <;> simp_all [ctpRealityStatus, ctpToMoodSelector]

-- ============================================================================
-- D. Bridge 4: English ComplementType ↔ NoonanCompType
-- ============================================================================

/-! ## D1. Map linglib's English-specific complement types to Noonan's
typological categories -/

/-- Map English fragment complement types to Noonan's universal categories.
    Returns `none` for types that don't correspond to a clausal complement. -/
def englishToNoonan : ComplementType → Option NoonanCompType
  | .finiteClause => some .indicative
  | .infinitival => some .infinitive
  | .gerund => some .nominalized
  | .smallClause => some .paratactic
  | .none => none           -- Not complement-taking
  | .np => none             -- NP complement, not clausal
  | .np_np => none          -- Ditransitive, not clausal
  | .np_pp => none          -- NP+PP, not clausal
  | .question => some .indicative  -- Embedded questions are finite in English

/-- Every English verb that takes a clausal complement maps to a Noonan type. -/
theorem clausal_complements_have_noonan_type :
    englishToNoonan .finiteClause ≠ none ∧
    englishToNoonan .infinitival ≠ none ∧
    englishToNoonan .gerund ≠ none ∧
    englishToNoonan .smallClause ≠ none := by decide

-- ============================================================================
-- E. Gap fix: VerbEntry → MoodSelector (derived function)
-- ============================================================================

/-! ## E1. Derive MoodSelector from VerbEntry fields

This is placed in Bridge.lean (not Verbal.lean) to avoid circular imports:
it needs both Verbal and Mood/Basic. Follows the `deriveSelectionClass` pattern. -/

/-- Derive mood selection from a VerbEntry's structural properties.

    The logic:
    - Attitude + preferential positive → subjunctive (want, hope)
    - Attitude + preferential negative → indicative (fear: evaluates what IS)
    - Attitude + preferential uncertainty → indicative (worry)
    - Attitude + doxastic → indicative (believe, think)
    - Factive/semifactive → indicative (know: presupposes truth)
    - Perception → indicative (see: factive perception)
    - Communication → moodNeutral (say: varies cross-linguistically)
    - ChangeOfState → moodNeutral (stop: varies)
    - Causative → subjunctive (make: irrealis)
    - Implicative → moodNeutral (manage: varies)
    - Simple → moodNeutral -/
def deriveMoodSelector (v : VerbEntry) : MoodSelector :=
  match v.verbClass, v.attitudeBuilder with
  | .attitude, some (.preferential (.degreeComparison .positive)) => .subjunctiveSelecting
  | .attitude, some (.preferential _) => .indicativeSelecting
  | .attitude, some (.doxastic _) => .indicativeSelecting
  | .factive, _ => .indicativeSelecting
  | .semifactive, _ => .indicativeSelecting
  | .perception, _ => .indicativeSelecting
  | .communication, _ => .moodNeutral
  | .changeOfState, _ => .moodNeutral
  | .causative, _ => .subjunctiveSelecting
  | .implicative, _ => .moodNeutral
  | _, _ => .moodNeutral

/-! ## E2. Per-verb mood selector verification -/

-- Indicative-selecting verbs
theorem know_selects_indicative :
    deriveMoodSelector know = .indicativeSelecting := by native_decide
theorem believe_selects_indicative :
    deriveMoodSelector believe = .indicativeSelecting := by native_decide
theorem think_selects_indicative :
    deriveMoodSelector think = .indicativeSelecting := by native_decide
theorem realize_selects_indicative :
    deriveMoodSelector realize = .indicativeSelecting := by native_decide
theorem see_selects_indicative :
    deriveMoodSelector see = .indicativeSelecting := by native_decide
theorem fear_selects_indicative :
    deriveMoodSelector fear = .indicativeSelecting := by native_decide
theorem worry_selects_indicative :
    deriveMoodSelector worry = .indicativeSelecting := by native_decide

-- Subjunctive-selecting verbs
theorem want_selects_subjunctive :
    deriveMoodSelector want = .subjunctiveSelecting := by native_decide
theorem hope_selects_subjunctive :
    deriveMoodSelector hope = .subjunctiveSelecting := by native_decide
theorem wish_selects_subjunctive :
    deriveMoodSelector wish = .subjunctiveSelecting := by native_decide
theorem expect_selects_subjunctive :
    deriveMoodSelector expect = .subjunctiveSelecting := by native_decide
theorem cause_selects_subjunctive :
    deriveMoodSelector cause = .subjunctiveSelecting := by native_decide
theorem make_selects_subjunctive :
    deriveMoodSelector make = .subjunctiveSelecting := by native_decide

-- Mood-neutral verbs
theorem say_mood_neutral :
    deriveMoodSelector say = .moodNeutral := by native_decide
theorem tell_mood_neutral :
    deriveMoodSelector tell = .moodNeutral := by native_decide
theorem stop_mood_neutral :
    deriveMoodSelector stop = .moodNeutral := by native_decide
theorem start_mood_neutral :
    deriveMoodSelector start = .moodNeutral := by native_decide
theorem manage_mood_neutral :
    deriveMoodSelector manage = .moodNeutral := by native_decide

-- ============================================================================
-- F. Cross-bridge consistency
-- ============================================================================

/-! ## F1. CTP class → mood selector consistency

For verbs with a derivable CTP class, the mood selector derived directly
from VerbEntry should be consistent with the CTP-based derivation. -/

/-- The CTP-based mood mapping agrees with the direct derivation for
    representative verbs from each CTP class. -/
theorem ctp_mood_consistent_knowledge :
    ctpToMoodSelector .knowledge = deriveMoodSelector know := by native_decide
theorem ctp_mood_consistent_propAttitude :
    ctpToMoodSelector .propAttitude = deriveMoodSelector believe := by native_decide
theorem ctp_mood_consistent_desiderative :
    ctpToMoodSelector .desiderative = deriveMoodSelector want := by native_decide
theorem ctp_mood_consistent_manipulative :
    ctpToMoodSelector .manipulative = deriveMoodSelector cause := by native_decide
theorem ctp_mood_consistent_perception :
    ctpToMoodSelector .perception = deriveMoodSelector see := by native_decide

/-! ## F2. Three-way agreement for key verbs

For important verbs, all three classification systems agree:
1. deriveCTPClass → CTP class
2. deriveSelectionClass → question embedding
3. deriveMoodSelector → mood selection -/

/-- "know" is classified consistently across all three bridges:
    knowledge CTP, responsive selection, indicative mood. -/
theorem know_triple_consistency :
    deriveCTPClass know = some .knowledge ∧
    deriveSelectionClass know = .responsive ∧
    deriveMoodSelector know = .indicativeSelecting := by native_decide

/-- "believe" is classified consistently:
    propAttitude CTP, uninterrogative, indicative mood. -/
theorem believe_triple_consistency :
    deriveCTPClass believe = some .propAttitude ∧
    deriveSelectionClass believe = .uninterrogative ∧
    deriveMoodSelector believe = .indicativeSelecting := by native_decide

/-- "want" is classified consistently:
    desiderative CTP, uninterrogative (anti-rogative), subjunctive mood. -/
theorem want_triple_consistency :
    deriveCTPClass want = some .desiderative ∧
    deriveSelectionClass want = .uninterrogative ∧
    deriveMoodSelector want = .subjunctiveSelecting := by native_decide

/-- "ask" is classified consistently:
    utterance CTP, rogativeSAP, mood-neutral. -/
theorem ask_triple_consistency :
    deriveCTPClass ask = some .utterance ∧
    deriveSelectionClass ask = .rogativeSAP ∧
    deriveMoodSelector ask = .moodNeutral := by native_decide

end Phenomena.Complementation.Bridge
