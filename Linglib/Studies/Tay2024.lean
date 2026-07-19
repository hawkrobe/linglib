import Linglib.Semantics.Causation.Resultatives
import Linglib.Morphology.Word.Term
import Linglib.Studies.GoldbergJackendoff2004
import Linglib.Fragments.Mandarin.Resultatives

/-!
# Tay (2024): Resultative Expressions in Mandarin Chinese
[tay-2024]

UCL PhD dissertation on why Mandarin V-V resultatives are more flexible in
argument realisation than English resultatives and Mandarin V-*de* resultatives.

## Thesis's core proposal

V-V compounds are morphological (built in word syntax, not phrasal syntax),
so their components are **inaccessible to syntactic operations** — modification,
questioning, A-not-A.  The null affix ∅ in V1-∅-V2 inherits all of V2's
arguments but **none** of V1's.  This predicts:
- **Syntactic opacity**: V-V components cannot be independently modified (§3)
- **No DOR** in Mandarin: subject-oriented resultatives are productive (§2)
- **The Onset Condition**: the CCF must participate in V1's event (§4)

## What we formalize

1. **No DOR**: subject-oriented compounds (kū-lèi, chī-bǎo, hē-zuì) coexist
   with object-oriented ones; cross-linguistic contrast with English data
2. **V-V vs V-de opacity**: V-V blocks independent modification of V1/V2;
   V-de allows it (thesis's central structural prediction)
3. **Onset Condition**: the CCF must be a V1 participant (agent, subject matter,
   or source); pure causers are ungrammatical — derived from data via
   `CcfRole.isV1Participant`, not stipulated
4. **V-V morphology**: `Word.Term.compound` captures the binary V1-V2 structure
5. **Causal dynamics**: direct CAUSE (single causal law, `completesForEffect`)
6. **Phase complements**: grammaticalized V2 subset with fixed `CoSType`
   (standard Mandarin grammar, supplementing the thesis's V-V analysis)

## Architecture

Connects:
- `Causation.Resultatives`: causal dynamics, CC-selection,
  tightness, cross-linguistic parameters (`ResultativeRealization`,
  `ResultOrientation`, `PhaseComplement`)
- `Morphology.Word.Term`: `Word.Term.compound` for V-V
- `Mandarin.Resultatives`: compound and phase complement lexical entries
- `GoldbergJackendoff2004`: English
  data for cross-linguistic contrast
-/

namespace Tay2024

open Intensional (WorldTimeIndex)

open Causation.Resultatives
open Morphology
open Features.ChangeOfState (CoSType priorStatePresup)
open Mandarin.Resultatives

-- ════════════════════════════════════════════════════
-- § 1. Fragment Data — DOR Failure
-- ════════════════════════════════════════════════════

/-! ## Direct Object Restriction does NOT hold for Mandarin

English resultatives enforce DOR: *"She ran tired"* is ungrammatical;
only *"She ran herself ragged"* (fake reflexive) is acceptable.

Mandarin V-V compounds productively allow subject-oriented resultatives
without reflexivization: kū-lèi "cry-tired", chī-bǎo "eat-full",
pǎo-lèi "run-tired", hē-zuì "drink-drunk".

Compound data lives in `Mandarin.Resultatives`; theorems here
derive from those Fragment entries. -/

/-- Subject-oriented Mandarin resultatives exist in the Fragment data. -/
theorem mandarin_has_subject_oriented :
    (allCompounds.any (·.orientation == .subjectOriented)) = true := by
  native_decide

/-- Both orientations are attested. -/
theorem mandarin_has_both_orientations :
    (allCompounds.any (·.orientation == .objectOriented)) = true ∧
    (allCompounds.any (·.orientation == .subjectOriented)) = true := by
  constructor <;> native_decide

/-- Four of eight compounds are subject-oriented. -/
theorem subject_oriented_count :
    (allCompounds.filter (·.orientation == .subjectOriented)).length = 4 := by
  native_decide

/-- Contrast with English: the English data in `Data.lean` uses fake
    reflexives for subject-result patterns. All fake reflexives are
    grammatical, but require the reflexive pronoun. -/
theorem english_subject_result_requires_reflexive :
    (GoldbergJackendoff2004.allExamples.filter
      (·.resType == .fakeReflexive)).all
      (·.judgment == .ok) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 2. V-V vs V-de: Syntactic Opacity
-- ════════════════════════════════════════════════════

/-! ## V-V compounds are syntactically opaque; V-*de* is transparent

[tay-2024]'s central structural prediction (Ch. 2 §2.1): because V-V
compounds are built in morphology, their components are inaccessible to
syntactic operations like independent modification.  V-*de* resultatives,
built in syntax, allow V1 and V2 to be independently modified.

Three kinds of independent modification tested:
- **Locative**: V1 modified by *zài jiā lǐ* "at home"
- **Manner**: V2 modified by *mímíhūhūde* "in a daze"
- **Temporal**: V2 modified by *jīntiān* "today"

Each test yields a minimal pair: V-*de* ✓, V-V ✗. -/

/-- A syntactic opacity test datum. -/
structure OpacityDatum where
  sentence : String
  construction : ResultativeRealization
  modTarget : String      -- "V1" or "V2"
  modifierType : String   -- "locative", "manner", "temporal"
  grammatical : Bool
  deriving Repr, BEq

/-- V-*de*: V1 locatively modified — ✓.
    "The baby cried at home until the neighbours woke up." -/
def opacity_vde_v1_locative : OpacityDatum :=
  { sentence := "Bǎobao zài jiā lǐ kū de [línjū xǐng-le]"
  , construction := .deComplement, modTarget := "V1"
  , modifierType := "locative", grammatical := true }

/-- V-V: V1 locatively modified — ✗. -/
def opacity_vv_v1_locative : OpacityDatum :=
  { sentence := "*Bǎobao zài jiā lǐ kū-xǐng-le línjū"
  , construction := .verbCompound, modTarget := "V1"
  , modifierType := "locative", grammatical := false }

/-- V-*de*: V2 manner-modified — ✓.
    "The baby cried and Mother woke up in a daze." -/
def opacity_vde_v2_manner : OpacityDatum :=
  { sentence := "Bǎobao kū de [māma mímíhūhūde xǐng-le]"
  , construction := .deComplement, modTarget := "V2"
  , modifierType := "manner", grammatical := true }

/-- V-V: V2 manner-modified — ✗. -/
def opacity_vv_v2_manner : OpacityDatum :=
  { sentence := "*Bǎobao kū-mímíhūhūde-xǐng-le māma"
  , construction := .verbCompound, modTarget := "V2"
  , modifierType := "manner", grammatical := false }

/-- V-*de*: V2 temporally modified — ✓.
    "Mother sang (last night) until her throat became hoarse today." -/
def opacity_vde_v2_temporal : OpacityDatum :=
  { sentence := "Māma chàng de [sǎngzi jīntiān yǎ-le]"
  , construction := .deComplement, modTarget := "V2"
  , modifierType := "temporal", grammatical := true }

/-- V-V: V2 temporally modified — ✗. -/
def opacity_vv_v2_temporal : OpacityDatum :=
  { sentence := "*Māma chàng-jīntiān-yǎ-le sǎngzi"
  , construction := .verbCompound, modTarget := "V2"
  , modifierType := "temporal", grammatical := false }

def allOpacityData : List OpacityDatum :=
  [ opacity_vde_v1_locative, opacity_vv_v1_locative
  , opacity_vde_v2_manner, opacity_vv_v2_manner
  , opacity_vde_v2_temporal, opacity_vv_v2_temporal ]

/-- V-*de* allows independent modification of components. -/
theorem vde_allows_modification :
    (allOpacityData.filter (·.construction == .deComplement)).all
      (·.grammatical) = true := by native_decide

/-- V-V blocks independent modification of components. -/
theorem vv_blocks_modification :
    (allOpacityData.filter (·.construction == .verbCompound)).all
      (!·.grammatical) = true := by native_decide

/-- Grammaticality of independent modification tracks construction type exactly:
    V-*de* → grammatical, V-V → ungrammatical. -/
theorem opacity_tracks_construction :
    allOpacityData.all (λ d =>
      d.grammatical == (d.construction == .deComplement)) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 3. The Onset Condition
-- ════════════════════════════════════════════════════

/-! ## The Onset Condition ([tay-2024], Ch. 3)

The external argument (CCF) of a transitive V-V resultative must be
interpreted as a **participant** in the event denoted by V1: an agent, a
subject matter, or a source.  "Pure causers" — entities that plausibly
cause V1's event but do not participate in it — are ungrammatical.

Key data:
- ✓ Zhāngsān dǎ-sǐ Lǐsì: Zhangsan = **agent** of hitting
- ✓ Movie kū-hóng eyes: movie = **subject matter** of crying
- ✓ Wine zuì-dǎo Zhangsan: wine = **source** of intoxication
- ✗ Onions kū-hóng eyes: onions = **pure causer** (not participant of crying)
- ✗ Boss zuì-dǎo subordinate: boss = **agentive causer** (not participant of
  becoming drunk)

The Onset Condition is **derived** from the data: grammaticality in every
datum matches `CcfRole.isV1Participant`. -/

/-- How the external argument (CCF) relates to V1's event. -/
inductive CcfRole where
  | agent           -- CCF performs V1 (Zhāngsān in dǎ-sǐ)
  | subjectMatter   -- CCF is what V1 is about (movie for crying)
  | source          -- CCF is non-agentive source of V1 (wine for drunk)
  | pureCauser      -- CCF causes but doesn't participate (onions for cry)
  deriving DecidableEq, Repr

/-- A CCF is a participant of V1 iff it is an agent, subject matter,
    or source — NOT a pure causer. -/
def CcfRole.isV1Participant : CcfRole → Bool
  | .agent => true
  | .subjectMatter => true
  | .source => true
  | .pureCauser => false

/-- An Onset Condition test datum. -/
structure OnsetDatum where
  sentence : String
  v1v2 : String
  ccfEntity : String
  ccfRole : CcfRole
  grammatical : Bool
  deriving Repr, BEq

/-- Zhāngsān dǎ-sǐ-le Lǐsì: Zhangsan = agent of hitting. ✓ -/
def onset_agent : OnsetDatum :=
  { sentence := "Zhāngsān dǎ-sǐ-le Lǐsì"
  , v1v2 := "dǎ-sǐ", ccfEntity := "Zhāngsān"
  , ccfRole := .agent, grammatical := true }

/-- Movie kū-hóng eyes: movie = subject matter of crying. ✓ -/
def onset_subj_matter_cry : OnsetDatum :=
  { sentence := "Zhè bù diànyǐng kū-hóng-le wǒ de yǎnjīng"
  , v1v2 := "kū-hóng", ccfEntity := "movie"
  , ccfRole := .subjectMatter, grammatical := true }

/-- Joke xiào-téng belly: joke = subject matter of laughing. ✓ -/
def onset_subj_matter_laugh : OnsetDatum :=
  { sentence := "Nèi ge xiàohuà xiào-téng-le Zhāngsān de dùzi"
  , v1v2 := "xiào-téng", ccfEntity := "joke"
  , ccfRole := .subjectMatter, grammatical := true }

/-- Wine zuì-dǎo Zhangsan: wine = source of intoxication. ✓ -/
def onset_source : OnsetDatum :=
  { sentence := "Nèi bēi jiǔ zuì-dǎo-le Zhāngsān"
  , v1v2 := "zuì-dǎo", ccfEntity := "wine"
  , ccfRole := .source, grammatical := true }

/-- *Onions kū-hóng eyes: onions = pure causer (not participant of crying). ✗ -/
def onset_pure_causer_onions : OnsetDatum :=
  { sentence := "*Zhè xiē yángcōng kū-hóng-le wǒ de yǎnjīng"
  , v1v2 := "kū-hóng", ccfEntity := "onions"
  , ccfRole := .pureCauser, grammatical := false }

/-- *Laughing gas xiào-téng belly: laughing gas = pure causer. ✗ -/
def onset_pure_causer_gas : OnsetDatum :=
  { sentence := "*Xiàoqì xiào-téng-le wǒ de dùzi"
  , v1v2 := "xiào-téng", ccfEntity := "laughing gas"
  , ccfRole := .pureCauser, grammatical := false }

/-- *Boss zuì-dǎo subordinate: boss = agentive causer
    (causes intoxication but doesn't participate in becoming-drunk). ✗ -/
def onset_agentive_causer : OnsetDatum :=
  { sentence := "*Lǎobǎn zuì-dǎo-le xiàshǔ"
  , v1v2 := "zuì-dǎo", ccfEntity := "boss"
  , ccfRole := .pureCauser, grammatical := false }

def allOnsetData : List OnsetDatum :=
  [ onset_agent, onset_subj_matter_cry, onset_subj_matter_laugh
  , onset_source, onset_pure_causer_onions, onset_pure_causer_gas
  , onset_agentive_causer ]

/-- The Onset Condition: grammaticality matches V1 participation in every datum.
    Derived from the data, not stipulated. -/
theorem onset_condition :
    allOnsetData.all (λ d =>
      d.grammatical == d.ccfRole.isV1Participant) = true := by
  native_decide

/-- All grammatical onset examples have a V1-participating CCF. -/
theorem onset_grammatical_implies_participant :
    (allOnsetData.filter (·.grammatical)).all
      (·.ccfRole.isV1Participant) = true := by
  native_decide

/-- All V1-non-participants are ungrammatical. -/
theorem onset_nonparticipant_implies_ungrammatical :
    (allOnsetData.filter (!·.ccfRole.isV1Participant)).all
      (!·.grammatical) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 4. V-V Compound Morphology
-- ════════════════════════════════════════════════════

/-! ## Morphological structure: V1-∅-V2

[tay-2024] proposes that V-V compounds have the morphological structure
V1-∅-V2: the null affix ∅ inherits all of V2's arguments but none of V1's.
We capture the binary V1-V2 compound using `Word.Term.compound` from
`Morphology/Word/Term.lean`.

V-V resultatives are **synthetic** compounds: their components stand in a
predictable CAUSE relation. This contrasts with root compounds like
*cài-dāo* "vegetable-knife" (= "a knife for cutting vegetables") whose
semantic relation is idiosyncratic and must be listed in the lexicon
([tay-2024], Ch. 3 §3.1). -/

/-- Morphological structure of dǎ-sǐ "hit-die". -/
def dasi_morph : Word.Term Morphology.Morph :=
  .compound (.root (.root "da")) (.root (.root "si"))

/-- Surface form is concatenation of V1 + V2. -/
theorem dasi_surface :
    String.join (dasi_morph.toList.map Morphology.Morph.form) = "dasi" := rfl

/-- V-V compounds have exactly 2 morphs. -/
theorem dasi_morph_count : dasi_morph.toList.length = 2 := rfl

/-- Morphological structure of kū-lèi "cry-tired" (subject-oriented). -/
def kulei_morph : Word.Term Morphology.Morph :=
  .compound (.root (.root "ku")) (.root (.root "lei"))

theorem kulei_surface :
    String.join (kulei_morph.toList.map Morphology.Morph.form) = "kulei" := rfl

-- ════════════════════════════════════════════════════
-- § 5. Causal Models (V2 BoolSEM)
-- ════════════════════════════════════════════════════

/-! ## V-V compound causal models on BoolSEM

Each V-V compound maps to a 2-vertex BoolSEM where V1 directly causes V2.
Direct causation = single edge, no intermediate with an independent
energy source. This is the same tightness constraint identified for
English resultatives by [levin-2019] — formalized via the canonical
`completesForEffect` predicate from `Causation.CCSelection`. -/

open Causation Causation.Mechanism Causation.SEM
open Causation.CCSelection (completesForEffect completesForEffect_of_developDetOn)

namespace Dasi

inductive V | hitting | death deriving DecidableEq, Fintype, Repr
def varList : List V := [.hitting, .death]
def graph : CausalGraph V := ⟨fun | .hitting => ∅ | .death => {.hitting}⟩

instance : CausalGraph.IsDAG graph :=
  CausalGraph.IsDAG.of_depth graph (fun | .hitting => 0 | .death => 1)
    (by intro u v h; revert h; cases u <;> cases v <;> decide)

/-- dǎ-sǐ "hit-die": hitting → death. Direct causation. -/
noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .hitting => const (G := graph) false
      | .death => deterministic (fun ρ => ρ ⟨.hitting, by simp [graph]⟩) }

instance : CausalGraph.IsDAG model.graph := inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .hitting => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .death => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem sufficient :
    BoolSEM.causallySufficient model Valuation.empty .hitting .death :=
  SEM.developDet_hasValue_of_developDetOn_hasValue (vs := varList) (n := 1) (by decide)

theorem tight :
    completesForEffect model Valuation.empty .hitting true false .death true :=
  completesForEffect_of_developDetOn varList 1 (by decide) (by decide)

end Dasi

namespace Kulei

inductive V | crying | tired deriving DecidableEq, Fintype, Repr
def varList : List V := [.crying, .tired]
def graph : CausalGraph V := ⟨fun | .crying => ∅ | .tired => {.crying}⟩

instance : CausalGraph.IsDAG graph :=
  CausalGraph.IsDAG.of_depth graph (fun | .crying => 0 | .tired => 1)
    (by intro u v h; revert h; cases u <;> cases v <;> decide)

/-- kū-lèi "cry-tired": crying → tired. Subject-oriented, direct. -/
noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .crying => const (G := graph) false
      | .tired => deterministic (fun ρ => ρ ⟨.crying, by simp [graph]⟩) }

instance : CausalGraph.IsDAG model.graph := inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .crying => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .tired => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem tight :
    completesForEffect model Valuation.empty .crying true false .tired true :=
  completesForEffect_of_developDetOn varList 1 (by decide) (by decide)

end Kulei

namespace Tuikai

inductive V | pushing | openV deriving DecidableEq, Fintype, Repr
def varList : List V := [.pushing, .openV]
def graph : CausalGraph V := ⟨fun | .pushing => ∅ | .openV => {.pushing}⟩

instance : CausalGraph.IsDAG graph :=
  CausalGraph.IsDAG.of_depth graph (fun | .pushing => 0 | .openV => 1)
    (by intro u v h; revert h; cases u <;> cases v <;> decide)

/-- tuī-kāi "push-open": pushing → open. Mandarin parallel to
    English "push X open". -/
noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .pushing => const (G := graph) false
      | .openV => deterministic (fun ρ => ρ ⟨.pushing, by simp [graph]⟩) }

instance : CausalGraph.IsDAG model.graph := inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .pushing => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .openV => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem tight :
    completesForEffect model Valuation.empty .pushing true false .openV true :=
  completesForEffect_of_developDetOn varList 1 (by decide) (by decide)

end Tuikai

-- ════════════════════════════════════════════════════
-- § 6. Phase Complement Theorems
-- ════════════════════════════════════════════════════

/-! ## Phase complement CoS bridge

Phase complement lexical entries live in `Mandarin.Resultatives`.
Here we prove theorems connecting them to `CoSType` infrastructure. -/

/-- Phase complements connect to all three CoS types. -/
theorem phase_covers_all_cos :
    (allPhaseComplements.any (·.phase.cosType == .inception)) = true ∧
    (allPhaseComplements.any (·.phase.cosType == .cessation)) = true ∧
    (allPhaseComplements.any (·.phase.cosType == .continuation)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The CoS presupposition for inceptive phase complements (dǎo, hǎo, diào):
    the result state was NOT holding before the event.
    Connects to `priorStatePresup .inception P w = ¬ P w` from
    `ChangeOfState.Theory`. -/
theorem inceptive_phase_presup {W : Type*} (P : W → Prop) (w : W) :
    priorStatePresup PhaseComplement.dao.cosType P w = ¬ P w := rfl

/-- The CoS presupposition for the cessative phase complement (wán):
    the activity WAS happening before the event. -/
theorem cessative_phase_presup {W : Type*} (P : W → Prop) :
    priorStatePresup PhaseComplement.wan.cosType P = P := rfl

/-- The continuation phase complement (zhù) presupposes P and asserts P. -/
theorem continuation_phase_presup {W : Type*} (P : W → Prop) :
    priorStatePresup PhaseComplement.zhu.cosType P = P := rfl

-- ════════════════════════════════════════════════════
-- § 7. Realization and orientation parameters
-- ════════════════════════════════════════════════════

/-! ## All Mandarin compounds use verb-compound realization -/

theorem all_compounds_are_verb_compounds :
    allCompounds.all (·.realization == .verbCompound) = true := by
  native_decide

/-! ## Constructional BECOME = inception

V-V resultative compounds, like English resultatives, have constructional
BECOME mapping to `CoSType.inception` (¬P → P). V2 denotes the result
state that newly obtains as a consequence of V1. -/

/-- V-V resultative BECOME = inception, same as English. -/
theorem vv_compound_become :
    resultStateMapsToCoS = .inception := rfl

-- ════════════════════════════════════════════════════
-- § 8. End-to-end summary
-- ════════════════════════════════════════════════════

/-! ## End-to-end: the V-V compound resultative architecture

1. V1 denotes causing event, V2 denotes result state
2. Connected by direct CAUSE (single causal law, tight)
3. Morphologically realized as `Word.Term.compound` (V1-∅-V2)
4. Subject-oriented resultatives are productive (no DOR)
5. V-V is syntactically opaque; V-*de* is transparent
6. Onset Condition: CCF must be a V1 participant (derived from data)
7. Phase complements are a grammaticalized subset with fixed CoSType
8. Constructional BECOME = inception (shared with English) -/

theorem vv_compound_architecture :
    -- Tight causation (direct, single edge)
    completesForEffect Dasi.model Valuation.empty .hitting true false .death true ∧
    -- Morphological compound
    (dasi_morph matches Word.Term.compound _ _) = true ∧
    -- Subject-oriented resultatives exist (no DOR)
    (allCompounds.any (·.orientation == .subjectOriented)) = true ∧
    -- V-V is opaque, V-de is transparent
    allOpacityData.all (λ d =>
      d.grammatical == (d.construction == .deComplement)) = true ∧
    -- Onset Condition: grammaticality = V1 participation
    allOnsetData.all (λ d =>
      d.grammatical == d.ccfRole.isV1Participant) = true ∧
    -- Phase complements cover all CoS types
    (allPhaseComplements.any (·.phase.cosType == .inception)) = true ∧
    (allPhaseComplements.any (·.phase.cosType == .cessation)) = true ∧
    -- Constructional BECOME = inception
    resultStateMapsToCoS = .inception := by
  refine ⟨Dasi.tight, by decide, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> native_decide

end Tay2024
