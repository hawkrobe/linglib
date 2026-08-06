import Linglib.Semantics.ArgumentStructure.Root.Classification
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Morphology.DM.Categorizer
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
* `selects`, `isGrammatical` — each head's selection condition on the
  root coordinates; the paradigm table is derived, not stipulated
  (`isGrammatical_table`), and checked against the attested data
  (`paradigm_predicts_attestation`).
* `vØ`, `v_w`, `v_ch`, `v_j` — the voice heads, on substrate
  `Voice.Flavor` cells; the agent diagnostics and the -aj distribution
  are derived from their parametric semantics.
-/

namespace Coon2019

open Chuj
open Verb.Root

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

/-- A root is unaccusative when it takes an internal argument but does
    not license transitive Voice (§3.3). -/
def unaccusative (r : Classification) : Bool :=
  r.valency == {.internal} && !r.licensesTransitiveVoice

/-! ### Selection and the paradigm -/

/-- The selection condition each voice suffix imposes on the root's
    coordinates: the Ø slot covers transitive vØ (requires transitive
    licensing) and the null intransitive v (selects unaccusatives); the
    passives -ch and -j presuppose a transitive stem; -w introduces an
    external argument and rejects exactly the unaccusative class
    (p. 45). -/
def selects (vs : VoiceSuffix) (r : Classification) : Bool :=
  match vs with
  | .null    => r.licensesTransitiveVoice || unaccusative r
  | .ch | .j => r.licensesTransitiveVoice
  | .w       => !unaccusative r

/-- A root class forms a grammatical stem with a voice suffix exactly
    when the suffix selects the class's coordinates. Does not cover
    derived transitive stems in -ej, which all four classes form (§2.2),
    or the isolated -j forms on non-transitive roots (ex. (71), p. 71). -/
def isGrammatical (rc : RootClass) (vs : VoiceSuffix) : Bool :=
  selects vs rc.toClassification

/-- Coon's paradigm table, derived: √TV takes all four voices, √ITV
    only null v, √POS and √NOM only -w. -/
theorem isGrammatical_table :
    (∀ vs, isGrammatical .tv vs = true) ∧
    (∀ vs, isGrammatical .itv vs = (vs == .null)) ∧
    (∀ vs, isGrammatical .pos vs = (vs == .w)) ∧
    (∀ vs, isGrammatical .nom vs = (vs == .w)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro vs; cases vs <;> decide)

/-- Every root class verbalizes under some v/Voice⁰ head:
    categorization is free at category grain
    (`Morphology.DM.same_root_different_category`); the paradigm gaps
    are flavor-level selection (`selects`). -/
theorem every_class_verbalizes (rc : RootClass) :
    ∃ vs, isGrammatical rc vs = true := by
  cases rc
  exacts [⟨.null, by decide⟩, ⟨.null, by decide⟩, ⟨.w, by decide⟩, ⟨.w, by decide⟩]

/-- Each v/Voice⁰ head is a verbal categorizer in the DM sense
    ([coon-2019] treats all four as bundled v/Voice⁰). -/
def _root_.Chuj.VoiceSuffix.categorizer : VoiceSuffix → Morphology.DM.Categorizer :=
  λ _ => .v

/-- A root class forms bare transitive stems exactly when it licenses
    transitive Voice (§2.2, p. 41). -/
def formsBareTransitive (rc : RootClass) : Bool :=
  rc.toClassification.licensesTransitiveVoice

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

/-- The derived paradigm agrees with the recorded judgment of every
    attested example. -/
theorem paradigm_predicts_attestation :
    paradigmData.all (λ (rc, vs, g) => isGrammatical rc vs == g) = true := by
  decide

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

/-- Map each voice suffix to its Minimalist Head. -/
def toVoiceHead : VoiceSuffix → Head
  | .null => vØ
  | .ch   => v_ch
  | .j    => v_j
  | .w    => v_w

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

/-! ### Derived diagnostics (§4.1)

The agent diagnostics are predictions read off the heads' parametric
semantics, checked against the attested minimal pair
(`adverb_pair_predicted`). -/

/-- The fate of the external argument, read off the head's parametric
    semantics (§4.1). -/
def _root_.Chuj.VoiceSuffix.participantFate (vs : VoiceSuffix) : Voice.ParticipantFate :=
  match (toVoiceHead vs).params.extArgSemantics with
  | some .thematicArgument    => .maintained
  | some .thematicExistential => .denucleativized
  | _                         => .suppressed

/-- Agent-oriented adverbs are predicted grammatical exactly where the
    head supplies an agent, overt or implicit (§4.1). -/
def agentAdverbOK (vs : VoiceSuffix) : Bool :=
  (toVoiceHead vs).params.assignsTheta? == some true

/-- Agentive by-phrases are predicted grammatical exactly where the
    head's agent is implicit (§4.1); with an overt agent the by-phrase
    has nothing to identify. -/
def byPhraseOK (vs : VoiceSuffix) : Bool :=
  (toVoiceHead vs).params.extArgSemantics == some .thematicExistential

/-- `agentAdverbOK` predicts the (63a)/(67a) minimal pair. -/
theorem adverb_pair_predicted :
    agentAdverbOK .ch = (Examples.ex_63a.judgment != .ungrammatical) ∧
    agentAdverbOK .j = (Examples.ex_67a.judgment != .ungrammatical) := by
  exact ⟨by decide, by decide⟩

/-- Both passives lack an overt external argument, but -ch has an
    implicit agent and -j none, and both diagnostics track the
    difference. -/
theorem passive_contrast :
    agentAdverbOK .ch = true ∧ byPhraseOK .ch = true ∧
    agentAdverbOK .j = false ∧ byPhraseOK .j = false := by decide

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

/-- -aj surfaces when the stem has an implicit argument: the
    existentially bound agent of -ch, or the suppressed theme of the
    absolutive antipassive. -/
def triggersAj (v : Head) (implicitInternal : Bool) : Bool :=
  v.params.extArgSemantics == some .thematicExistential || implicitInternal

/-- -aj on stems in passive/agentless contexts (-w is handled by
    `ajOnAntipassive`). -/
def ajOnPassive (vs : VoiceSuffix) : Bool :=
  triggersAj (toVoiceHead vs) false

/-- -aj on antipassive (-w) stems: present exactly in the absolutive
    subtype. -/
def ajOnAntipassive (apt : AntipassiveType) : Bool :=
  triggersAj v_w (apt == .absolutive)

/-- The -ch passive triggers -aj: its agent is implicit (ex. (58), p. 66). -/
theorem ch_aj_passive : ajOnPassive .ch = true := by decide

/-- Ø, -w, and -j alone trigger no -aj: none has an implicit external
    argument. -/
theorem no_implicit_external :
    ajOnPassive .null = false ∧ ajOnPassive .w = false ∧
    ajOnPassive .j = false := by decide

/-- The absolutive antipassive triggers -aj: its theme is implicit
    (ex. (55b–c), p. 65); the incorporation antipassive does not — its
    theme is an overt bare NP (ex. (54a), p. 64). -/
theorem aj_antipassive_split :
    ajOnAntipassive .absolutive = true ∧
    ajOnAntipassive .incorporation = false := by decide

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

/-! ### Root-class contrasts -/

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
