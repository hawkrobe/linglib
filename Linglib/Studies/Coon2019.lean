import Linglib.Semantics.ArgumentStructure.Root.Classification
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Fragments.Mayan.Chuj.RootClasses
import Linglib.Fragments.Mayan.Chuj.VoiceSystem
import Linglib.Data.Examples.Coon2019

/-!
# Building verbs in Chuj

[coon-2019]'s analysis of Chuj verb stems: roots determine internal
arguments, the four v/Voice⁰ heads (Ø, -ch, -j, -w) determine external
arguments. The root lexicon lives in
`Fragments/Mayan/Chuj/RootClasses.lean`, the attested examples in
`Data.Examples.Coon2019`.

## Main declarations

* `Chuj.RootClass.toClassification` — Coon's coordinates for the root
  classes, as a derived projection.
* `vØ`, `v_w`, `v_ch`, `v_j` — the voice heads, on substrate
  `Voice.Flavor` cells.
* `paradigm_predicts_attestation` — the root × voice paradigm agrees
  with the attested data.
-/

namespace Coon2019

open Chuj
open Verb.Root

/-! ### External-argument fate (ex. (78), p. 76) -/

/-- The fate of the external argument under each voice suffix, in
    Creissels's coding-frame coordinates (`Voice.ParticipantFate`):
    -ch denucleativizes the agent (demoted but maintained in participant
    structure — by-phrases and agent adverbs live, §4.1.1), -j
    suppresses it entirely (§4.1.2), Ø and -w keep it as a core term.
    The ERG (Ø) vs ABS (-w) case split is a separate axis, carried by
    phasehood (`only_vØ_is_phase`). -/
def _root_.Chuj.VoiceSuffix.participantFate : VoiceSuffix → Voice.ParticipantFate
  | .null => .maintained
  | .ch   => .denucleativized
  | .j    => .suppressed
  | .w    => .maintained

/-! ### Paradigm grammaticality (§§2–4) -/

/-- Whether a root class combines with one of (78)'s four v/Voice⁰
    heads to form a grammatical verb stem:
    - √TV: all four voices (Ø, -ch, -j, -w) — ex. (78)
    - √ITV: null v only (§2.1, p. 40)
    - √POS: -w only (§3.1, (20)/(22), p. 47)
    - √NOM: -w only (§3.1, p. 46)

    The table ranges over root + v/Voice⁰ combinations only. It does not
    cover derived transitive stems in -ej, which all four classes form
    (§2.2, p. 42; p. 45), nor the isolated -j forms on non-transitive
    roots (p. 71, ex. (71)). -/
def isGrammatical (rc : RootClass) (vs : VoiceSuffix) : Bool :=
  match rc, vs with
  | .tv,  _     => true   -- √TV combines with all four
  | .itv, .null => true   -- √ITV takes null v (§2.1)
  | .pos, .w    => true   -- √POS takes -w ((20)/(22), p. 47)
  | .nom, .w    => true   -- √NOM takes -w (§3.1)
  | _,    _     => false

/-- √TV is the only class that forms bare transitive stems (§2.2, p. 41). -/
def formsBareTransitive (rc : RootClass) : Bool :=
  match rc with
  | .tv => true
  | _   => false

/-! ### -aj distribution (§4.2)

-aj marks the presence of an implicit argument on a √TV stem
(ex. (78), p. 76; §4.2, p. 72) — [coon-2019] (p. 73) proposes it is
an overt reflex of Existential Closure ([diesing-1992]):
- Ø: no implicit arg → no -aj
- -ch: implicit external arg → -aj on stem (§4.1.1, p. 68)
- -j: no external arg at all → no -aj
- -w (absolutive): implicit internal arg → -aj (ex. (55c), p. 65)
- -w (incorporation): overt bare NP internal arg → no -aj (ex. (54a), p. 64) -/

/-- The two antipassive (-w) subtypes: absolutive (implicit theme,
    ex. (55b–c), p. 65) vs incorporation (overt bare-NP theme,
    ex. (54a), p. 64). -/
inductive AntipassiveType where
  /-- Theme is implicit (suppressed). -/
  | absolutive
  /-- Theme is an overt bare NP (incorporated). -/
  | incorporation
  deriving DecidableEq, Repr

/-- -aj on √TV stems in passive/agentless contexts (-w is handled by
    `ajOnAntipassive`, since -aj there tracks the antipassive subtype). -/
def ajOnPassive (vs : VoiceSuffix) : Bool :=
  match vs with
  | .null => false  -- no implicit arg
  | .ch   => true   -- implicit agent (ex. 62: -ch-aj passive)
  | .j    => false  -- no agent at all
  | .w    => false  -- see `ajOnAntipassive`

/-- -aj on √TV stems in antipassive (-w) contexts. -/
def ajOnAntipassive (apt : AntipassiveType) : Bool :=
  match apt with
  | .absolutive    => true   -- implicit theme (ex. 55b: Ix-mak'-waj)
  | .incorporation => false  -- overt bare NP (ex. 54a: Ix-in-jax-w-i ixim)

/-! ### Agent diagnostics (§4.1) -/

/-- Agent-oriented adverb test (§4.1.1–4.1.2): "on purpose" adverbs are
    grammatical with -chaj (ex. (63a), p. 68) but not -j (ex. (67a),
    p. 70). -/
def agentAdverbOK (vs : VoiceSuffix) : Bool :=
  match vs with
  | .null => true   -- active: agent is overt
  | .ch   => true   -- passive: implicit agent licenses adverb (ex. 63a)
  | .j    => false  -- agentless: no agent to orient (ex. 67a)
  | .w    => true   -- antipassive: agent is overt

/-- By-phrase test (§4.1.1–4.1.2): oblique agents (*yuj* DPs) are
    grammatical with -chaj (ex. (62), p. 68) but not -j, where -uj
    phrases are causal, not agentive (exx. (65)–(66), pp. 69–70). -/
def byPhraseOK (vs : VoiceSuffix) : Bool :=
  match vs with
  | .null => false  -- active: agent is already overt
  | .ch   => true   -- passive: by-phrase identifies implicit agent (ex. 62)
  | .j    => false  -- agentless: -uj phrase is causal, not agentive
  | .w    => false  -- antipassive: agent is already overt

/-! ### Root-class coordinates -/

/-- [coon-2019]'s theoretical coordinates for each root class, as a
    derived projection off the distributional class label ((3), p. 37):
    √TV and √ITV share type ⟨e,⟨s,t⟩⟩ and internal-argument valency
    ([davis-1997]; √ITV is unaccusative, §3.3), split by
    transitive-Voice licensing; √POS is the measure-function type
    ⟨e,⟨s,d⟩⟩ ([coon-2019] following [henderson-2017]); √NOM the entity
    predicate ⟨e,t⟩.

    The `changeType` column is NOT fixed by Coon's classes — each class
    mixes change-of-state and non-change roots (p. 60: √ITV includes
    *k'ib'* "grow" and *cham* "die") — so the values here are
    representative placeholders; [beavers-etal-2021] subdivides √TV on
    exactly this axis (`Studies/BeaversEtAl2021.lean`). -/
def _root_.Chuj.RootClass.toClassification : RootClass → Classification
  | .tv  => { valency := {.internal}, changeType := .result,
              denotationType := some (.e ⇒ .s ⇒ .t),
              licensesTransitiveVoice := true }
  | .itv => { valency := {.internal}, changeType := .propertyConcept,
              denotationType := some (.e ⇒ .s ⇒ .t) }
  | .pos => { valency := ∅, changeType := .propertyConcept,
              denotationType := some (.e ⇒ .s ⇒ .d) }
  | .nom => { valency := ∅, changeType := .propertyConcept,
              denotationType := some (.e ⇒ .t) }

/-! ### Paradigm data (§§2–5)

Attested examples live in `Data/Examples/Coon2019.json` (generated
module `Data.Examples.Coon2019`); each row carries the root form and
[coon-2019]'s voice segmentation as `paperFeatures`. -/

/-- Parse a row's `voice` feature. -/
def readVoice : String → Option VoiceSuffix
  | "null" => some .null
  | "ch"   => some .ch
  | "j"    => some .j
  | "w"    => some .w
  | _      => none

/-- The root a row attests, looked up in the fragment lexicon by the
    `rootForm` feature — the root's class comes from the fragment, not
    from the data row. -/
def rowRoot (e : Data.Examples.LinguisticExample) : Option ChujRoot :=
  e.feature? "rootForm" >>= λ f => allRoots.find? (·.form == f)

/-- Root class × voice × grammaticality for each attestation row.
    Adverb-diagnostic rows are excluded: their grammaticality is an
    agent-diagnostic fact, not a root × voice fact
    (`adverb_pair_predicted`). -/
def paradigmData : List (RootClass × VoiceSuffix × Bool) :=
  Examples.all.filterMap λ e =>
    if (e.feature? "diagnostic").isSome then none
    else do
      let r ← rowRoot e
      let vs ← e.feature? "voice" >>= readVoice
      pure (r.class', vs, e.judgment != .ungrammatical)

/-- The adapter loses no attestation rows: all eight root × voice
    examples project to data. -/
theorem paradigmData_complete : paradigmData.length = 8 := by decide

/-- The paradigm predicts the attested data: `isGrammatical` agrees
    with the recorded judgment of every root × voice example. -/
theorem paradigm_predicts_attestation :
    paradigmData.all (λ (rc, vs, g) => isGrammatical rc vs == g) = true := by
  decide

/-- The agent-adverb minimal pair (63a)/(67a): same root, same intended
    translation, -ch vs -j — predicted by `agentAdverbOK`. -/
theorem adverb_pair_predicted :
    agentAdverbOK .ch = (Examples.ex_63a.judgment != .ungrammatical) ∧
    agentAdverbOK .j = (Examples.ex_67a.judgment != .ungrammatical) := by
  exact ⟨by decide, by decide⟩

/-! ### Minimalist voice heads (ex. (78)) -/

open Minimalist Minimalist.Voice

/-- Active transitive v/Voice⁰ (Ø): introduces overt agent in Spec,VoiceP,
    assigns ergative case, phase head (v*). -/
def vØ : Head :=
  { flavor := .agentive, hasD := true }

/-- Agentive intransitive v/Voice⁰ (-w): introduces overt agent in
    Spec,VoiceP but assigns absolutive (not ergative) case (p. 54) —
    the substrate's `.antipassive` cell, which is non-phasal by default.
    Merges directly with the root — cannot attach to derived stems
    (p. 54, (34b)). Used with √NOM and √POS to verbalize roots, and with
    √TV in antipassives. Also models the null intransitive v/Voice⁰ for
    √ITV roots (p. 40): both introduce an agent and assign absolutive,
    differing only in overt (-w) vs null morphological realization. -/
def v_w : Head :=
  { flavor := .antipassive, hasD := true }

/-- Passive v/Voice⁰ (-ch): the agent is implicit — existentially bound,
    not projected to a specifier (pp. 68–69) — the substrate's
    `.impersonal` cell [−D, +∃x]. Agent-oriented adverbs and by-phrases
    are licensed, confirming the agent's semantic presence
    (`params.assignsTheta? = some true`). Only combines with √TV roots. -/
def v_ch : Head :=
  { flavor := .impersonal, hasD := false }

/-- Agentless passive v/Voice⁰ (-j): verbalizes the stem but introduces
    no external argument — neither overt nor implicit (p. 70: "does not
    assign a thematic role and does not merge an external argument").
    No agent-oriented adverbs, no agentive by-phrases. `hasD := false`
    diverges from `.nonThematic`'s [+D] cell, which models SE-type PF
    marking (Romance anticausatives); Chuj -j projects no specifier at
    all (`v_j_not_dCoherent`). -/
def v_j : Head :=
  { flavor := .nonThematic, hasD := false }

/-! ### Voice head properties -/

/-- Ø and -w project an overt agent specifier (θ-marked); -ch has a
    semantically present but existentially bound agent — θ-assignment in
    the broad `params.assignsTheta?` sense, not the specifier sense. -/
theorem agent_presence :
    vØ.AssignsTheta ∧ v_w.AssignsTheta ∧
    ¬ v_ch.AssignsTheta ∧ v_ch.params.assignsTheta? = some true := by
  refine ⟨by decide, by decide, by decide, rfl⟩

/-- -j does NOT have an agent in any sense: no θ-marked specifier and no
    implicit agent (p. 70). -/
theorem v_j_no_theta : ¬ v_j.AssignsTheta ∧ v_j.params.assignsTheta? = some false :=
  ⟨by decide, rfl⟩

/-- The -ch vs -j contrast on the parametric axis: -ch's agent is
    existentially bound (present), -j's is absent. This is the paper's
    central empirical result stated in substrate coordinates. -/
theorem ch_j_params_contrast :
    v_ch.params.extArgSemantics = some .thematicExistential ∧
    v_j.params.assignsTheta? = some false := ⟨rfl, rfl⟩

/-- Only Ø is a phase head (assigns ergative case). Non-phasality of -w
    and -ch now follows from their flavor defaults (`.antipassive`,
    `.impersonal`) with no per-construction override. -/
theorem only_vØ_is_phase :
    vØ.IsPhasal ∧ ¬ v_w.IsPhasal ∧ ¬ v_ch.IsPhasal ∧ ¬ v_j.IsPhasal := by decide

/-- Ø, -w, and -ch are [D]-coherent; -j diverges (nonThematic's [+D]
    cell models SE-type PF marking, which Chuj -j lacks). -/
theorem v_j_not_dCoherent :
    vØ.DCoherent ∧ v_w.DCoherent ∧ v_ch.DCoherent ∧ ¬ v_j.DCoherent := by decide

/-! ### Event decomposition -/

/-- Lower event structure for result roots: cause + change + result state. -/
def resultLower : List VerbHead := [.vCAUSE, .vGO, .vBE]

/-- Lower event structure for activity roots (√TV PC, √ITV, √NOM):
    no sub-eventive decomposition below Voice. -/
def activityLower : List VerbHead := []

/-- Lower event structure for positional roots (√POS): stative. -/
def positionalLower : List VerbHead := [.vBE]

/-- √TV result + Ø → causative [vDO, vCAUSE, vGO, vBE] (active transitive). -/
theorem tv_res_active :
    isCausative (buildDecomposition vØ resultLower) = true := by decide

/-- √TV result + -ch: CAUSE persists in the root structure and the agent
    is semantically present (∃-bound), but Voice projects no specifier,
    so no vDO layer — the implicit agent lives in the parametric
    coordinates, not the decomposition. -/
theorem tv_res_passive_ch :
    hasCause (buildDecomposition v_ch resultLower) = true ∧
    v_ch.params.assignsTheta? = some true := ⟨by decide, rfl⟩

/-- √TV result + -j → inchoative [vGO, vBE] (agentless passive /
    anticausative). No agent at all — a pure change-of-state (p. 70). -/
theorem tv_res_agentless :
    isInchoative (buildDecomposition v_j resultLower) = true := by decide

/-- √ITV + v/Voice⁰ → activity [vDO] (intransitive). Uses v_w, which
    shares formal properties with the null intransitive v/Voice⁰ for
    √ITV (both agentive, non-ERG-assigning; p. 40). -/
theorem itv_intransitive :
    isActivity (buildDecomposition v_w activityLower) = true := by decide

/-- √POS + -w → [vDO, vBE]: agent assumes a position (agentive stative).
    (p. 48, (23)): chot-w-i "The frog hopped." -/
theorem pos_agentive :
    buildDecomposition v_w positionalLower = [.vDO, .vBE] := by decide

/-- √NOM + -w → activity [vDO] (denominal agentive intransitive).
    (p. 45, (16b)): chanhal-w-i "I danced." -/
theorem nom_agentive :
    isActivity (buildDecomposition v_w activityLower) = true := by decide

/-! ### Existential closure (-aj) -/

/-- -aj (Existential Closure, [diesing-1992]) surfaces when there is any
    implicit argument: an implicit external (∃-bound agent, as in -ch —
    read off `params.extArgSemantics`) or an implicit internal (theme
    suppression in the absolutive antipassive -w-aj). -/
def triggersAj (v : Head) (implicitInternal : Bool) : Bool :=
  v.params.extArgSemantics == some .thematicExistential || implicitInternal

/-- -ch-aj: passive of √TV with implicit agent (ex. (58), p. 66). -/
theorem ch_aj_passive :
    triggersAj v_ch false = true := by decide

/-- Ø, -w, -j have no implicit external: Ø and -w project overt agents,
    -j has no agent at all (p. 70). -/
theorem no_implicit_external :
    triggersAj vØ false = false ∧
    triggersAj v_w false = false ∧
    triggersAj v_j false = false := by decide

/-- -w-aj: absolutive antipassive (√TV theme is implicit; ex. (58), p. 66). -/
theorem w_aj_antipassive :
    triggersAj v_w true = true := by decide

/-- -w incorporation antipassive: theme is overt bare NP → no -aj
    (ex. (58), p. 66; cf. (26b), p. 50). -/
theorem w_incorporation_no_aj :
    triggersAj v_w false = false := by decide

/-! ### Division of labor -/

/-- Division of labor ([coon-2019], ex. (2)/(77), p. 75): the root
    determines whether a theme is present; Voice determines whether an
    agent is present. -/
theorem minimalist_division_of_labor :
    -- Same result root: Ø gives causative, -j gives inchoative
    isCausative (buildDecomposition vØ resultLower) = true ∧
    isInchoative (buildDecomposition v_j resultLower) = true ∧
    -- √TV licenses transitive Voice, √ITV does not (both take a theme)
    (RootClass.tv.toClassification).licensesTransitiveVoice = true ∧
    (RootClass.itv.toClassification).licensesTransitiveVoice = false :=
  ⟨by decide, by decide, rfl, rfl⟩

/-- The causative alternation in Chuj is determined by Voice, not by the
    root (instantiation of `voice_determines_causativity` for Chuj
    heads): for result roots, causativity tracks specifier-θ-assignment. -/
theorem chuj_causative_alternation_result :
    (isCausative (buildDecomposition vØ resultLower) = true ↔ vØ.AssignsTheta) ∧
    (isCausative (buildDecomposition v_w resultLower) = true ↔ v_w.AssignsTheta) ∧
    (isCausative (buildDecomposition v_ch resultLower) = true ↔ v_ch.AssignsTheta) ∧
    (isCausative (buildDecomposition v_j resultLower) = true ↔ v_j.AssignsTheta) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### Fragment bridge -/

/-- √TV maps to a theme-selecting root; √ITV is unaccusative, so it also
    combines with an internal argument (§3.3); √POS and √NOM introduce
    no core positions. -/
theorem root_class_valency_alignment :
    (RootClass.tv.toClassification).valency = {.internal} ∧
    (RootClass.itv.toClassification).valency = {.internal} ∧
    (RootClass.pos.toClassification).valency = ∅ ∧
    (RootClass.nom.toClassification).valency = ∅ := ⟨rfl, rfl, rfl, rfl⟩

/-- `formsBareTransitive` matches transitive-Voice licensing — not
    internal-argument valency, which unaccusative √ITV shares with √TV
    (§3.3). -/
theorem bare_transitive_iff_voice (rc : RootClass) :
    formsBareTransitive rc = true ↔
      rc.toClassification.licensesTransitiveVoice = true := by
  cases rc <;> decide

/-! ### Voice suffix ↔ Head -/

/-- Map each voice suffix to its Minimalist Head. -/
def toVoiceHead : VoiceSuffix → Head
  | .null => vØ
  | .ch   => v_ch
  | .j    => v_j
  | .w    => v_w

/-- External argument status matches the D feature: overt external
    argument ↔ hasD. -/
theorem d_feature_alignment :
    (toVoiceHead .null).hasD = true ∧
    (toVoiceHead .w).hasD = true ∧
    (toVoiceHead .ch).hasD = false ∧
    (toVoiceHead .j).hasD = false := ⟨rfl, rfl, rfl, rfl⟩

/-- The coding-frame fate of the external argument matches the head's
    parametric semantics: maintained ↔ θ-marked specifier,
    denucleativized ↔ ∃-bound implicit agent, suppressed ↔ no agent. -/
theorem participant_fate_alignment (vs : VoiceSuffix) :
    (vs.participantFate = .maintained ↔
      (toVoiceHead vs).params.extArgSemantics = some .thematicArgument) ∧
    (vs.participantFate = .denucleativized ↔
      (toVoiceHead vs).params.extArgSemantics = some .thematicExistential) := by
  cases vs <;> exact ⟨by decide, by decide⟩

/-- Only Ø is a phase head (assigns ERG case). -/
theorem phase_head_alignment :
    (toVoiceHead .null).IsPhasal ∧
    ¬ (toVoiceHead .ch).IsPhasal ∧
    ¬ (toVoiceHead .j).IsPhasal ∧
    ¬ (toVoiceHead .w).IsPhasal := by decide

/-! ### Agent diagnostic alignment -/

/-- The agent-adverb diagnostic matches semantic agent presence
    (`params.assignsTheta?`): adverbs need an agent, overt or implicit. -/
theorem agent_adverb_matches_theta (vs : VoiceSuffix) :
    agentAdverbOK vs = true ↔
      (toVoiceHead vs).params.assignsTheta? = some true := by
  cases vs <;> decide

/-- The -ch vs -j contrast is the critical test: both lack an overt
    external argument, but they differ in implicit-agent presence, and
    the diagnostics track it. -/
theorem passive_contrast :
    v_ch.params.assignsTheta? = some true ∧
    agentAdverbOK .ch = true ∧
    byPhraseOK .ch = true ∧
    v_j.params.assignsTheta? = some false ∧
    agentAdverbOK .j = false ∧
    byPhraseOK .j = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### -aj distribution alignment -/

/-- The -aj table matches the heads on the passive axis: -aj appears
    exactly where the head has an ∃-bound implicit external. -w is
    excluded — its -aj tracks the antipassive subtype
    (`ajOnAntipassive`), not the external argument. -/
theorem aj_passive_matches_implicit :
    ajOnPassive .null = triggersAj (toVoiceHead .null) false ∧
    ajOnPassive .ch = triggersAj (toVoiceHead .ch) false ∧
    ajOnPassive .j = triggersAj (toVoiceHead .j) false := by decide

/-- `triggersAj` predicts the full -aj distribution:
    -ch (implicit external) → -aj; -j (no external) → no -aj;
    -w absolutive (implicit internal) → -aj;
    -w incorporation (overt internal) → no -aj. -/
theorem aj_full_distribution :
    triggersAj v_ch false = true ∧
    ajOnPassive .ch = true ∧
    triggersAj v_j false = false ∧
    ajOnPassive .j = false ∧
    triggersAj v_w true = true ∧
    ajOnAntipassive .absolutive = true ∧
    triggersAj v_w false = false ∧
    ajOnAntipassive .incorporation = false := by
  refine ⟨by decide, rfl, by decide, rfl, by decide, rfl, by decide, rfl⟩

/-! ### Division of labor in the data -/

/-- The core empirical claim (ex. (2)/(77), p. 75): roots determine
    internal arguments, Voice determines external arguments. -/
theorem division_of_labor_matches_data :
    -- Root determines internal: only √TV forms bare transitives
    formsBareTransitive .tv = true ∧
    (RootClass.tv.toClassification).licensesTransitiveVoice = true ∧
    formsBareTransitive .itv = false ∧
    (RootClass.itv.toClassification).licensesTransitiveVoice = false ∧
    -- Voice determines external: same root, different agent fate
    VoiceSuffix.participantFate .null = .maintained ∧
    VoiceSuffix.participantFate .ch = .denucleativized ∧
    VoiceSuffix.participantFate .j = .suppressed :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Theme persistence across all four voice forms for √TV: the paradigm
    attests √TV under Ø, -ch, -j, and -w, and the root's internal
    argument is a root property (valency), so it holds throughout. -/
theorem theme_persists_all_voices :
    isGrammatical .tv .null = true ∧
    isGrammatical .tv .ch = true ∧
    isGrammatical .tv .j = true ∧
    isGrammatical .tv .w = true ∧
    (RootClass.tv.toClassification).valency = {.internal} :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Denotation type alignment -/

/-- The four root classes have distinct denotation types ((3), p. 37):
    √TV and √ITV = ⟨e,⟨s,t⟩⟩, √POS = ⟨e,⟨s,d⟩⟩, √NOM = ⟨e,t⟩. -/
theorem denotation_type_alignment :
    (RootClass.tv.toClassification).denotationType = some (.e ⇒ .s ⇒ .t) ∧
    (RootClass.itv.toClassification).denotationType = some (.e ⇒ .s ⇒ .t) ∧
    (RootClass.pos.toClassification).denotationType = some (.e ⇒ .s ⇒ .d) ∧
    (RootClass.nom.toClassification).denotationType = some (.e ⇒ .t) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- √TV and √ITV share both semantic type and internal-argument valency
    ([davis-1997]; §3.3) — what separates them is transitive-Voice
    licensing alone, whose source Coon expressly declines to formalize. -/
theorem tv_itv_same_type_different_voice :
    (RootClass.tv.toClassification).denotationType =
      (RootClass.itv.toClassification).denotationType ∧
    (RootClass.tv.toClassification).valency =
      (RootClass.itv.toClassification).valency ∧
    (RootClass.tv.toClassification).licensesTransitiveVoice ≠
      (RootClass.itv.toClassification).licensesTransitiveVoice :=
  ⟨rfl, rfl, by decide⟩

/-- The -w suffix cross-class generalization: -w verbalizes √POS and
    √NOM roots, with different event structures depending on the root's
    lower structure (pp. 54–56). -/
theorem w_verbalization_cross_class :
    isGrammatical .pos .w = true ∧
    isGrammatical .nom .w = true ∧
    buildDecomposition v_w positionalLower = [.vDO, .vBE] ∧
    isActivity (buildDecomposition v_w activityLower) = true :=
  ⟨rfl, rfl, by decide, by decide⟩

/-! ### Root classes in the salience coordinates -/

/-- Chuj root classes through the annotation-level salience hom
    (`Classification.salienceClass`): √TV occupies the agent-patient
    salient cell — the same root-transitivity coordinate that
    [lucy-1994]'s Yucatec `=∅` class instantiates — while the three
    intransitive classes are underdetermined by the manner-blind
    annotation coordinates. -/
theorem salience_of_root_classes :
    (RootClass.tv.toClassification).salienceClass = some .agentPatient ∧
    (RootClass.itv.toClassification).salienceClass = none ∧
    (RootClass.pos.toClassification).salienceClass = none ∧
    (RootClass.nom.toClassification).salienceClass = none :=
  ⟨rfl, rfl, rfl, rfl⟩

end Coon2019
