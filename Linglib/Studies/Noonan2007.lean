import Linglib.Data.Complementation.Noonan2007
import Linglib.Syntax.Clause.Complementation
import Linglib.Syntax.Minimalist.LeftPeriphery
import Linglib.Semantics.Mood.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-! # Noonan (2007): Complementation Typology + Bridge Theorems
[noonan-2007]

Noonan's complementation typology (six complement types, twelve CTP classes,
realis/irrealis split, equi-deletion restriction, indicative implicational
hierarchy) plus interconnection theorems linking it to existing linglib
infrastructure.

## Part I: Noonan's generalizations over the generated CTP sample

Data rows are generated from `Data/Complementation/Noonan2007.json`
(module `Data.Complementation.Noonan2007`): a 7-language sample
(English §1.1 / Latin §1.3 / Turkish §1.4 / Irish §1.5 / Persian §2.3 /
Hindi-Urdu §2.3 / Japanese) testing three Noonan generalizations:

- G2: Equi-deletion restricted to reduced complement types (§2.1)
- G3: Negative raising restricted to propAttitude/desiderative (gap-filler)
- G4: Per-language indicative-desiderative implies indicative-propAttitude (§2.4)

Analytic caveats carried over from the hand-typed rows: Persian *khastan* and
Hindi-Urdu *chaahna* have `hasEquiDeletion := false` because their subjunctive
subject omission is pro-drop, not Noonan-equi; English *hope* has
`hasNegativeRaising := true` per §2.7's restriction of NR to
{propAttitude, desiderative, modal} (Horn 1989).

## Part II: Bridge theorems

Five bridges connecting CTPClass to existing infrastructure:
1. CTPClass ↔ VerbEntry (Verbal.lean) — derive CTP class from verb features
2. CTPClass ↔ SelectionClass (LeftPeriphery.lean) — map CTP to question embedding
3. CTPClass ↔ Selector (Mood/Basic.lean) — map CTP to mood selection
4. ComplementType ↔ NoonanCompType — via the substrate adapter
   `ComplementType.toNoonan` (`Syntax/Clause/Complementation.lean`)
5. VerbEntry → Selector — derive mood selection from verb features

-/

namespace Noonan2007

open Data.Complementation Data.Complementation.Noonan2007
open English.Predicates.Verbal
open Minimalist.LeftPeriphery
open Semantics.Mood

-- ============================================================================
-- Part I: Noonan's generalizations over the generated CTP sample
-- ============================================================================

-- ============================================================================
-- G2: Equi-deletion restriction ([noonan-2007] §2.1)
-- ============================================================================

/-- Equi-deletion only occurs when some attested complement type is reduced. -/
theorem equi_requires_reduced :
    ∀ d ∈ all,
      d.hasEquiDeletion = true →
      d.compTypes.any NoonanCompType.isReduced = true := by decide

-- ============================================================================
-- G3: Negative raising data (fills a gap in linglib)
-- ============================================================================

/-- Negative raising verbs are exclusively propAttitude or desiderative. -/
theorem negative_raising_class_restriction :
    ∀ d ∈ all,
      d.hasNegativeRaising = true →
      d.ctpClass = .propAttitude ∨ d.ctpClass = .desiderative := by decide

/-- Knowledge CTPs never support negative raising. -/
theorem knowledge_no_negative_raising :
    ∀ d ∈ all,
      d.ctpClass = .knowledge → d.hasNegativeRaising = false := by decide

-- ============================================================================
-- G4: Per-language indicative implicational hierarchy ([noonan-2007] §2.4)
-- ============================================================================

/-- Does some row of this language's list attest an indicative complement
    for CTP class `cls`? -/
def hasIndicativeFor (rows : List Datum) (cls : CTPClass) : Bool :=
  rows.any fun d => d.ctpClass == cls && d.compTypes.any (· == .indicative)

/-- [noonan-2007] §2.4: any sampled language using indicative with
    desideratives also uses it with propositional attitudes.

    English is the only language in the sample with indicative-desiderative
    (`hope` and `wish`), so English is the only place this implication has
    nontrivial content. To extend this generalization further, add a
    language with indicative-desiderative attestation (Modern Greek
    *thélo na + indicative-mood form*; Bulgarian *iskam da +
    present-indicative form*). -/
theorem indicative_hierarchy :
    ∀ rows ∈ sample, hasIndicativeFor rows .desiderative →
      hasIndicativeFor rows .propAttitude := by decide

-- ============================================================================
-- Part II: Bridge Theorems
-- ============================================================================

-- ============================================================================
-- A. Bridge 1: CTPClass ↔ VerbEntry
-- ============================================================================

/-! ## A1. Derive CTPClass from VerbEntry fields

CTPClass is DERIVED from existing VerbEntry fields — not added as a new field.
This follows the `deriveSelectionClass` pattern from LeftPeriphery.lean. -/

/-- Derive Noonan's CTP class from a VerbEntry's primitive fields.

    The mapping uses `levinClass`, `factivePresup`, `causative`,
    `implicative`, `cosType`, `speechActVerb`, and `attitude`:
    - levinClass ==.see → perception (see)
    - factivePresup → knowledge (know, realize, regret)
    - causative.isSome → manipulative (cause, make, force)
    - implicative.isSome → achievement (manage, fail)
    - cosType.isSome → phasal (stop, start, continue)
    - speechActVerb → utterance (say, tell)
    - attitude doxastic → propAttitude (believe, think)
    - attitude preferential positive → desiderative (want, hope)
    - attitude preferential other → propAttitude (fear, worry)
    - Otherwise → none -/
def deriveCTPClass (v : VerbEntry) : Option CTPClass :=
  if v.levinClass == some .see then some .perception
  else if v.factivePresup then some .knowledge
  else if v.causative.isSome then some .manipulative
  else if v.implicative.isSome then some .achievement
  else if v.cosType.isSome then some .phasal
  else if v.speechActVerb then some .utterance
  else match v.attitude with
  | some (.doxastic _) => some .propAttitude
  | some (.preferential (.degreeComparison .positive)) => some .desiderative
  | some (.preferential _) => some .propAttitude
  | none => none

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
theorem remember_rog_is_knowledge :
    deriveCTPClass remember_rog = some .knowledge := by native_decide
theorem forget_rog_is_knowledge :
    deriveCTPClass forget_rog = some .knowledge := by native_decide

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
theorem decide_is_desiderative :
    deriveCTPClass decide_ = some .desiderative := by native_decide

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
theorem have_caus_is_manipulative :
    deriveCTPClass have_caus = some .manipulative := by native_decide
theorem get_caus_is_manipulative :
    deriveCTPClass get_caus = some .manipulative := by native_decide
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
- [noonan-2007]: CTP semantics → complement type
- [dayal-2025]: Predicate semantics → left-peripheral selection -/

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

    This covers: know, discover, remember_rog, forget_rog (knowledge → responsive),
    ask (utterance → rogativeSAP). -/
theorem ctp_selection_consistent_know :
    ctpToDefaultSelectionClass .knowledge = deriveSelectionClass know := by native_decide
theorem ctp_selection_consistent_discover :
    ctpToDefaultSelectionClass .knowledge = deriveSelectionClass discover := by native_decide
theorem ctp_selection_consistent_remember_rog :
    ctpToDefaultSelectionClass .knowledge = deriveSelectionClass remember_rog := by native_decide
theorem ctp_selection_consistent_forget_rog :
    ctpToDefaultSelectionClass .knowledge = deriveSelectionClass forget_rog := by native_decide
theorem ctp_selection_consistent_ask :
    ctpToDefaultSelectionClass .utterance = deriveSelectionClass ask := by native_decide

-- ============================================================================
-- C. Bridge 3: CTPClass ↔ Selector (Mood/Basic.lean)
-- ============================================================================

/-! ## C1. Map CTP classes to mood selection

This connects Noonan's semantic CTP classes to [mendes-2025]'s mood semantics.
The realis/irrealis split predicts mood selection. -/

/-- Map CTP class to mood selection.
    Realis CTPs select indicative; irrealis select subjunctive.
    Some are language-dependent (moodNeutral). -/
def ctpToSelector : CTPClass → Selector
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
      ctpToSelector c ≠ .subjunctiveSelecting := by
  intro c h
  cases c <;> simp_all [ctpRealityStatus, ctpToSelector]

/-- Irrealis CTPs select subjunctive or are mood-neutral (never indicative-selecting). -/
theorem irrealis_not_indicative :
    ∀ c : CTPClass,
      ctpRealityStatus c = .irrealis →
      ctpToSelector c ≠ .indicativeSelecting := by
  intro c h
  cases c <;> simp_all [ctpRealityStatus, ctpToSelector]

-- ============================================================================
-- D. Bridge 4: English ComplementType ↔ NoonanCompType
-- ============================================================================

/-! ## D1. Map linglib's English-specific complement types to Noonan's
typological categories

The adapter itself is substrate: `ComplementType.toNoonan` in
`Syntax/Clause/Complementation.lean`. The clausal-coverage check stays here. -/

/-- Every English verb that takes a clausal complement maps to a Noonan type. -/
theorem clausal_complements_have_noonan_type :
    ComplementType.toNoonan .finiteClause ≠ none ∧
    ComplementType.toNoonan .infinitival ≠ none ∧
    ComplementType.toNoonan .gerund ≠ none ∧
    ComplementType.toNoonan .smallClause ≠ none := by decide

-- ============================================================================
-- E. Gap fix: VerbEntry → Selector (derived function)
-- ============================================================================

/-! ## E1. Derive Selector from VerbEntry fields

This is placed in Bridge.lean (not Verbal.lean) to avoid circular imports:
it needs both Verbal and Mood/Basic. Follows the `deriveSelectionClass` pattern. -/

/-- Derive mood selection from a VerbEntry's primitive fields.

    The logic:
    - Preferential positive + Levin want-class → subjunctive (want, wish)
    - Preferential positive + non-want-class → crossLinguisticallyVariable
      (hope, expect: SBJV in some languages, IND in others;
      [grano-2024] Table 1)
    - Preferential negative/uncertainty attitude → indicative (fear, worry)
    - Doxastic attitude → indicative (believe, think)
    - Factive → indicative (know: presupposes truth)
    - Perception (levinClass ==.see) → indicative (see)
    - Speech-act verb → moodNeutral (say: varies cross-linguistically)
    - Change-of-state → moodNeutral (stop: varies)
    - Causative → subjunctive (make: irrealis)
    - Implicative → moodNeutral (manage: varies)
    - Otherwise → moodNeutral -/
def deriveSelector (v : VerbEntry) : Selector :=
  match v.attitude with
  | some (.preferential (.degreeComparison .positive)) =>
    if v.levinClass == some .want then .subjunctiveSelecting
    else .crossLinguisticallyVariable
  | some (.preferential _) => .indicativeSelecting
  | some (.doxastic _) => .indicativeSelecting
  | none =>
    if v.factivePresup then .indicativeSelecting
    else if v.levinClass == some .see then .indicativeSelecting
    else if v.speechActVerb then .moodNeutral
    else if v.cosType.isSome then .moodNeutral
    else if v.causative.isSome then .subjunctiveSelecting
    else if v.implicative.isSome then .moodNeutral
    else .moodNeutral

/-! ## E2. Per-verb mood selector verification -/

-- Indicative-selecting verbs
theorem know_selects_indicative :
    deriveSelector know = .indicativeSelecting := by native_decide
theorem believe_selects_indicative :
    deriveSelector believe = .indicativeSelecting := by native_decide
theorem think_selects_indicative :
    deriveSelector think = .indicativeSelecting := by native_decide
theorem realize_selects_indicative :
    deriveSelector realize = .indicativeSelecting := by native_decide
theorem see_selects_indicative :
    deriveSelector see = .indicativeSelecting := by native_decide
theorem fear_selects_indicative :
    deriveSelector fear = .indicativeSelecting := by native_decide
theorem worry_selects_indicative :
    deriveSelector worry = .indicativeSelecting := by native_decide

-- Subjunctive-selecting verbs (robustly SBJV cross-linguistically)
theorem want_selects_subjunctive :
    deriveSelector want = .subjunctiveSelecting := by native_decide
theorem wish_selects_subjunctive :
    deriveSelector wish = .subjunctiveSelecting := by native_decide
theorem intend_selects_subjunctive :
    deriveSelector intend = .subjunctiveSelecting := by native_decide
theorem cause_selects_subjunctive :
    deriveSelector cause = .subjunctiveSelecting := by native_decide
theorem make_selects_subjunctive :
    deriveSelector make = .subjunctiveSelecting := by native_decide
theorem decide_selects_subjunctive :
    deriveSelector decide_ = .subjunctiveSelecting := by native_decide

-- Cross-linguistically variable verbs ([grano-2024], Table 1:
-- 'hope' is SBJV in Spanish, IND/%SBJV in French, IND/SBJV in Portuguese,
-- %IND in Italian, IND/SBJV in Greek/Romanian, IND/for-to in English)
theorem hope_mood_variable :
    deriveSelector hope = .crossLinguisticallyVariable := by native_decide
theorem expect_mood_variable :
    deriveSelector expect = .crossLinguisticallyVariable := by native_decide

-- Mood-neutral verbs
theorem say_mood_neutral :
    deriveSelector say = .moodNeutral := by native_decide
theorem tell_mood_neutral :
    deriveSelector tell = .moodNeutral := by native_decide
theorem stop_mood_neutral :
    deriveSelector stop = .moodNeutral := by native_decide
theorem start_mood_neutral :
    deriveSelector start = .moodNeutral := by native_decide
theorem manage_mood_neutral :
    deriveSelector manage = .moodNeutral := by native_decide

-- ============================================================================
-- F. Cross-bridge consistency
-- ============================================================================

/-! ## F1. CTP class → mood selector consistency

For verbs with a derivable CTP class, the mood selector derived directly
from VerbEntry should be consistent with the CTP-based derivation. -/

/-- The CTP-based mood mapping agrees with the direct derivation for
    representative verbs from each CTP class. -/
theorem ctp_mood_consistent_knowledge :
    ctpToSelector .knowledge = deriveSelector know := by native_decide
theorem ctp_mood_consistent_propAttitude :
    ctpToSelector .propAttitude = deriveSelector believe := by native_decide
theorem ctp_mood_consistent_desiderative :
    ctpToSelector .desiderative = deriveSelector want := by native_decide
theorem ctp_mood_consistent_manipulative :
    ctpToSelector .manipulative = deriveSelector cause := by native_decide
theorem ctp_mood_consistent_perception :
    ctpToSelector .perception = deriveSelector see := by native_decide

/-! ## F2. Three-way agreement for key verbs

For important verbs, all three classification systems agree:
1. deriveCTPClass → CTP class
2. deriveSelectionClass → question embedding
3. deriveSelector → mood selection -/

/-- "know" is classified consistently across all three bridges:
    knowledge CTP, responsive selection, indicative mood. -/
theorem know_triple_consistency :
    deriveCTPClass know = some .knowledge ∧
    deriveSelectionClass know = .responsive ∧
    deriveSelector know = .indicativeSelecting := by native_decide

/-- "believe" is classified consistently:
    propAttitude CTP, uninterrogative, indicative mood. -/
theorem believe_triple_consistency :
    deriveCTPClass believe = some .propAttitude ∧
    deriveSelectionClass believe = .uninterrogative ∧
    deriveSelector believe = .indicativeSelecting := by native_decide

/-- "want" is classified consistently:
    desiderative CTP, uninterrogative (anti-rogative), subjunctive mood. -/
theorem want_triple_consistency :
    deriveCTPClass want = some .desiderative ∧
    deriveSelectionClass want = .uninterrogative ∧
    deriveSelector want = .subjunctiveSelecting := by native_decide

/-- "ask" is classified consistently:
    utterance CTP, rogativeSAP, mood-neutral. -/
theorem ask_triple_consistency :
    deriveCTPClass ask = some .utterance ∧
    deriveSelectionClass ask = .rogativeSAP ∧
    deriveSelector ask = .moodNeutral := by native_decide

-- ============================================================================
-- G. Bridge 5: CTPClass → ComplementSize ([egressy-2026])
-- ============================================================================

/-! ## G1. Complement size by CTP class

[egressy-2026] shows that complement size determines SOT availability
in Hungarian. This bridge maps Noonan's CTP classes to their typical
complement sizes, connecting the complementation typology to the
clause-size infrastructure.

These are **default** sizes — individual languages may override
(e.g., in Hungarian, *hogy* forces CP regardless of CTP class). -/

open Minimalist (ComplementSize)

/-- Default complement size for a CTP class.

    Finite declarative complements are typically CP-sized.
    Restructuring predicates select smaller complements.

    - utterance → CP (full finite with complementizer)
    - propAttitude → CP (full finite *that*-clause)
    - knowledge → CP (factive *that*-clause)
    - perception → TP (small clause / reduced complement)
    - desiderative → TP (subjunctive / infinitival)
    - manipulative → TP (ECM / small clause)
    - phasal → vP (restructuring)
    - achievement → vP (restructuring)
    - modal → TP (functional, shares T domain)
    - commentative → CP (factive *that*-clause)
    - pretence → CP (finite complement)
    - negative → vP (restructuring) -/
def ctpDefaultComplementSize : CTPClass → ComplementSize
  | .utterance    => .cP
  | .propAttitude => .cP
  | .knowledge    => .cP
  | .commentative => .cP
  | .pretence     => .cP
  | .perception   => .tP
  | .desiderative => .tP
  | .manipulative => .tP
  | .modal        => .tP
  | .phasal       => .vP
  | .achievement  => .vP
  | .negative     => .vP

-- ── Per-class verification ──

/-- Utterance CTPs default to CP. -/
theorem utterance_default_cp :
    ctpDefaultComplementSize .utterance = .cP := rfl

/-- Propositional attitude CTPs default to CP. -/
theorem propAttitude_default_cp :
    ctpDefaultComplementSize .propAttitude = .cP := rfl

/-- Perception CTPs default to TP (small clause). -/
theorem perception_default_tp :
    ctpDefaultComplementSize .perception = .tP := rfl

/-- Phasal CTPs default to vP (restructuring). -/
theorem phasal_default_vp :
    ctpDefaultComplementSize .phasal = .vP := rfl

/-- CP-selecting CTPs are opaque to tense Agree. -/
theorem cp_ctps_opaque :
    (ctpDefaultComplementSize .utterance).transparentToTenseAgree = false ∧
    (ctpDefaultComplementSize .propAttitude).transparentToTenseAgree = false ∧
    (ctpDefaultComplementSize .knowledge).transparentToTenseAgree = false := by
  decide

/-- TP-selecting and vP-selecting CTPs are transparent to tense Agree. -/
theorem small_ctps_transparent :
    (ctpDefaultComplementSize .perception).transparentToTenseAgree = true ∧
    (ctpDefaultComplementSize .desiderative).transparentToTenseAgree = true ∧
    (ctpDefaultComplementSize .phasal).transparentToTenseAgree = true := by
  decide

end Noonan2007
