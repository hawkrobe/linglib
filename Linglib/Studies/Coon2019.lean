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

/-- The fate of the external argument under each voice suffix
    (`Voice.ParticipantFate`, §4.1). -/
def _root_.Chuj.VoiceSuffix.participantFate : VoiceSuffix → Voice.ParticipantFate
  | .null => .maintained        -- overt ERG agent
  | .ch   => .denucleativized   -- demoted, maintained: by-phrases live (§4.1.1)
  | .j    => .suppressed        -- removed from participant structure (§4.1.2)
  | .w    => .maintained        -- overt ABS agent

/-! ### Paradigm grammaticality (§§2–4) -/

/-- Whether a root class combines with one of (78)'s four v/Voice⁰
    heads to form a grammatical verb stem. Does not cover derived
    transitive stems in -ej, which all four classes form (§2.2), or the
    isolated -j forms on non-transitive roots (ex. (71), p. 71). -/
def isGrammatical (rc : RootClass) (vs : VoiceSuffix) : Bool :=
  match rc, vs with
  | .tv,  _     => true   -- all four voices — ex. (78)
  | .itv, .null => true   -- null v only (§2.1, p. 40)
  | .pos, .w    => true   -- -w only ((20)/(22), p. 47)
  | .nom, .w    => true   -- -w only (§3.1, p. 46)
  | _,    _     => false

/-- √TV is the only class that forms bare transitive stems (§2.2, p. 41). -/
def formsBareTransitive (rc : RootClass) : Bool :=
  match rc with
  | .tv => true
  | _   => false

/-! ### -aj distribution (§4.2)

-aj marks an implicit argument on a √TV stem — an overt reflex of
Existential Closure ([diesing-1992]) per [coon-2019] (p. 73). -/

/-- The two antipassive (-w) subtypes: absolutive (implicit theme,
    ex. (55b–c)) vs incorporation (overt bare-NP theme, ex. (54a)). -/
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

/-- [coon-2019]'s coordinates for each root class ((3), p. 37), as a
    derived projection off the class label. The `changeType` column is a
    representative placeholder — Coon's classes mix change-of-state and
    non-change roots (p. 60), and [beavers-etal-2021] subdivides √TV on
    exactly this axis. -/
def _root_.Chuj.RootClass.toClassification : RootClass → Classification
  | .tv  => { valency := {.internal}, changeType := .result,
              denotationType := some (.e ⇒ .s ⇒ .t),
              licensesTransitiveVoice := true }
  | .itv => { valency := {.internal}, changeType := .propertyConcept,
              denotationType := some (.e ⇒ .s ⇒ .t) }   -- unaccusative (§3.3)
  | .pos => { valency := ∅, changeType := .propertyConcept,
              denotationType := some (.e ⇒ .s ⇒ .d) }   -- [henderson-2017] measure fn
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

/-- The root a row attests, looked up in the fragment lexicon by its
    `rootForm` feature. -/
def rowRoot (e : Data.Examples.LinguisticExample) : Option ChujRoot :=
  e.feature? "rootForm" >>= λ f => allRoots.find? (·.form == f)

/-- Root class, voice, and grammaticality for each attestation row;
    the adverb-diagnostic rows are excluded. -/
def paradigmData : List (RootClass × VoiceSuffix × Bool) :=
  Examples.all.filterMap λ e =>
    if (e.feature? "diagnostic").isSome then none
    else do
      let r ← rowRoot e
      let vs ← e.feature? "voice" >>= readVoice
      pure (r.class', vs, e.judgment != .ungrammatical)

/-- All eight attestation rows survive the adapter. -/
theorem paradigmData_complete : paradigmData.length = 8 := by decide

/-- `isGrammatical` agrees with the recorded judgment of every attested
    example. -/
theorem paradigm_predicts_attestation :
    paradigmData.all (λ (rc, vs, g) => isGrammatical rc vs == g) = true := by
  decide

/-- `agentAdverbOK` predicts the (63a)/(67a) minimal pair. -/
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

/-- Agentive intransitive v/Voice⁰ (-w): overt agent, absolutive case
    (p. 54) — the substrate's `.antipassive` cell, non-phasal by
    default. Verbalizes √NOM and √POS, forms √TV antipassives, and
    models the null intransitive v/Voice⁰ of √ITV (p. 40). -/
def v_w : Head :=
  { flavor := .antipassive, hasD := true }

/-- Passive v/Voice⁰ (-ch): implicit, existentially bound agent
    (pp. 68–69) — the substrate's `.impersonal` cell [−D, +∃x]. Agent
    adverbs and by-phrases confirm the agent's semantic presence. -/
def v_ch : Head :=
  { flavor := .impersonal, hasD := false }

/-- Agentless passive v/Voice⁰ (-j): verbalizes the stem, introduces no
    external argument, overt or implicit (p. 70). `hasD := false`
    diverges from `.nonThematic`'s [+D] SE cell (`v_j_not_dCoherent`). -/
def v_j : Head :=
  { flavor := .nonThematic, hasD := false }

/-! ### Voice head properties -/

/-- Ø and -w project an overt θ-marked agent; -ch's agent is present
    only in the broad `params.assignsTheta?` sense. -/
theorem agent_presence :
    vØ.AssignsTheta ∧ v_w.AssignsTheta ∧
    ¬ v_ch.AssignsTheta ∧ v_ch.params.assignsTheta? = some true := by
  refine ⟨by decide, by decide, by decide, rfl⟩

/-- -j has no agent in any sense (p. 70). -/
theorem v_j_no_theta : ¬ v_j.AssignsTheta ∧ v_j.params.assignsTheta? = some false :=
  ⟨by decide, rfl⟩

/-- -ch's agent is existentially bound, -j's is absent (§4.1). -/
theorem ch_j_params_contrast :
    v_ch.params.extArgSemantics = some .thematicExistential ∧
    v_j.params.assignsTheta? = some false := ⟨rfl, rfl⟩

/-- Only Ø is a phase head (assigns ergative case). -/
theorem only_vØ_is_phase :
    vØ.IsPhasal ∧ ¬ v_w.IsPhasal ∧ ¬ v_ch.IsPhasal ∧ ¬ v_j.IsPhasal := by decide

/-- Ø, -w, and -ch are [D]-coherent; -j diverges from `.nonThematic`'s
    SE-type [+D] cell. -/
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

/-- Active transitives built from result roots are causative. -/
theorem tv_res_active :
    isCausative (buildDecomposition vØ resultLower) = true := by decide

/-- In the -ch passive of a result root, CAUSE persists and the agent
    stays semantically present, but no specifier is projected. -/
theorem tv_res_passive_ch :
    hasCause (buildDecomposition v_ch resultLower) = true ∧
    v_ch.params.assignsTheta? = some true := ⟨by decide, rfl⟩

/-- The -j form of a result root is a pure change of state — an
    inchoative (p. 70). -/
theorem tv_res_agentless :
    isInchoative (buildDecomposition v_j resultLower) = true := by decide

/-- Intransitive roots with their v/Voice⁰ head form activities (p. 40). -/
theorem itv_intransitive :
    isActivity (buildDecomposition v_w activityLower) = true := by decide

/-- Positional roots verbalized by -w describe an agent assuming a
    position ((23), p. 48). -/
theorem pos_agentive :
    buildDecomposition v_w positionalLower = [.vDO, .vBE] := by decide

/-- Nominal roots verbalized by -w form activities ((16b), p. 45). -/
theorem nom_agentive :
    isActivity (buildDecomposition v_w activityLower) = true := by decide

/-! ### Existential closure (-aj) -/

/-- -aj surfaces when the stem has an implicit argument: the
    existentially bound agent of -ch, or the suppressed theme of the
    absolutive antipassive. -/
def triggersAj (v : Head) (implicitInternal : Bool) : Bool :=
  v.params.extArgSemantics == some .thematicExistential || implicitInternal

/-- The -ch passive triggers -aj: its agent is implicit (ex. (58), p. 66). -/
theorem ch_aj_passive :
    triggersAj v_ch false = true := by decide

/-- Ø, -w, -j have no implicit external: Ø and -w project overt agents,
    -j has no agent at all (p. 70). -/
theorem no_implicit_external :
    triggersAj vØ false = false ∧
    triggersAj v_w false = false ∧
    triggersAj v_j false = false := by decide

/-- The absolutive antipassive triggers -aj: its theme is implicit
    (ex. (58), p. 66). -/
theorem w_aj_antipassive :
    triggersAj v_w true = true := by decide

/-- The incorporation antipassive has no -aj: its theme is an overt
    bare NP (ex. (58), p. 66). -/
theorem w_incorporation_no_aj :
    triggersAj v_w false = false := by decide

/-! ### Division of labor -/

/-- The root determines whether a theme is present; Voice determines
    whether an agent is present (ex. (2)/(77), p. 75). -/
theorem minimalist_division_of_labor :
    -- Same result root: Ø gives causative, -j gives inchoative
    isCausative (buildDecomposition vØ resultLower) = true ∧
    isInchoative (buildDecomposition v_j resultLower) = true ∧
    -- √TV licenses transitive Voice, √ITV does not (both take a theme)
    (RootClass.tv.toClassification).licensesTransitiveVoice = true ∧
    (RootClass.itv.toClassification).licensesTransitiveVoice = false :=
  ⟨by decide, by decide, rfl, rfl⟩

/-- For result roots, causativity is determined by the voice head's
    θ-assignment, not by the root. -/
theorem chuj_causative_alternation_result :
    (isCausative (buildDecomposition vØ resultLower) = true ↔ vØ.AssignsTheta) ∧
    (isCausative (buildDecomposition v_w resultLower) = true ↔ v_w.AssignsTheta) ∧
    (isCausative (buildDecomposition v_ch resultLower) = true ↔ v_ch.AssignsTheta) ∧
    (isCausative (buildDecomposition v_j resultLower) = true ↔ v_j.AssignsTheta) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ### Fragment bridge -/

/-- Transitive and unaccusative intransitive roots both take an
    internal argument (§3.3); positional and nominal roots take none. -/
theorem root_class_valency_alignment :
    (RootClass.tv.toClassification).valency = {.internal} ∧
    (RootClass.itv.toClassification).valency = {.internal} ∧
    (RootClass.pos.toClassification).valency = ∅ ∧
    (RootClass.nom.toClassification).valency = ∅ := ⟨rfl, rfl, rfl, rfl⟩

/-- A root class forms bare transitive stems exactly when it licenses
    transitive Voice. -/
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

/-- A voice suffix has an overt external argument exactly when its head
    carries [D]. -/
theorem d_feature_alignment :
    (toVoiceHead .null).hasD = true ∧
    (toVoiceHead .w).hasD = true ∧
    (toVoiceHead .ch).hasD = false ∧
    (toVoiceHead .j).hasD = false := ⟨rfl, rfl, rfl, rfl⟩

/-- The external argument is maintained exactly when the head projects
    a θ-marked specifier, and denucleativized exactly when the head has
    an existentially bound implicit agent. -/
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

/-- Agent-oriented adverbs are licensed exactly where the head supplies
    an agent, overt or implicit. -/
theorem agent_adverb_matches_theta (vs : VoiceSuffix) :
    agentAdverbOK vs = true ↔
      (toVoiceHead vs).params.assignsTheta? = some true := by
  cases vs <;> decide

/-- Both passives lack an overt external argument, but -ch has an
    implicit agent and -j none, and both diagnostics track the
    difference. -/
theorem passive_contrast :
    v_ch.params.assignsTheta? = some true ∧
    agentAdverbOK .ch = true ∧
    byPhraseOK .ch = true ∧
    v_j.params.assignsTheta? = some false ∧
    agentAdverbOK .j = false ∧
    byPhraseOK .j = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### -aj distribution alignment -/

/-- -aj appears exactly where the head has an implicit external
    argument. The -w cell is excluded: its -aj tracks the antipassive
    subtype instead. -/
theorem aj_passive_matches_implicit :
    ajOnPassive .null = triggersAj (toVoiceHead .null) false ∧
    ajOnPassive .ch = triggersAj (toVoiceHead .ch) false ∧
    ajOnPassive .j = triggersAj (toVoiceHead .j) false := by decide

/-- `triggersAj` predicts the full -aj distribution across the passives
    and both antipassive subtypes. -/
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

/-- In the data: roots determine internal arguments, Voice determines
    external arguments (ex. (2)/(77), p. 75). -/
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

/-- Transitive roots keep their internal argument in all four voice
    forms. -/
theorem theme_persists_all_voices :
    isGrammatical .tv .null = true ∧
    isGrammatical .tv .ch = true ∧
    isGrammatical .tv .j = true ∧
    isGrammatical .tv .w = true ∧
    (RootClass.tv.toClassification).valency = {.internal} :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Denotation type alignment -/

/-- Each root class carries the semantic type of Coon's (3), p. 37. -/
theorem denotation_type_alignment :
    (RootClass.tv.toClassification).denotationType = some (.e ⇒ .s ⇒ .t) ∧
    (RootClass.itv.toClassification).denotationType = some (.e ⇒ .s ⇒ .t) ∧
    (RootClass.pos.toClassification).denotationType = some (.e ⇒ .s ⇒ .d) ∧
    (RootClass.nom.toClassification).denotationType = some (.e ⇒ .t) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- √TV and √ITV share semantic type and valency ([davis-1997]; §3.3);
    transitive-Voice licensing alone separates them. -/
theorem tv_itv_same_type_different_voice :
    (RootClass.tv.toClassification).denotationType =
      (RootClass.itv.toClassification).denotationType ∧
    (RootClass.tv.toClassification).valency =
      (RootClass.itv.toClassification).valency ∧
    (RootClass.tv.toClassification).licensesTransitiveVoice ≠
      (RootClass.itv.toClassification).licensesTransitiveVoice :=
  ⟨rfl, rfl, by decide⟩

/-- -w verbalizes both positional and nominal roots; the event
    structure differs with the root's lower structure (pp. 54–56). -/
theorem w_verbalization_cross_class :
    isGrammatical .pos .w = true ∧
    isGrammatical .nom .w = true ∧
    buildDecomposition v_w positionalLower = [.vDO, .vBE] ∧
    isActivity (buildDecomposition v_w activityLower) = true :=
  ⟨rfl, rfl, by decide, by decide⟩

/-! ### Root classes in the salience coordinates -/

/-- Only √TV determines a salience class — agent-patient, the cell of
    [lucy-1994]'s Yucatec `=∅` roots; the intransitive classes are
    underdetermined. -/
theorem salience_of_root_classes :
    (RootClass.tv.toClassification).salienceClass = some .agentPatient ∧
    (RootClass.itv.toClassification).salienceClass = none ∧
    (RootClass.pos.toClassification).salienceClass = none ∧
    (RootClass.nom.toClassification).salienceClass = none :=
  ⟨rfl, rfl, rfl, rfl⟩

end Coon2019
