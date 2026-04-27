import Linglib.Phenomena.Causation.Studies.BeaversEtAl2021
import Linglib.Theories.Morphology.RootTypology
import Linglib.Theories.Syntax.Minimalist.Voice
import Linglib.Fragments.Chuj.VerbBuilding

/-!
# Chuj Verb Building: Empirical Data and Bridge Theorems
@cite{coon-2019}

Minimalist analysis and bridge theorems for @cite{coon-2019} "Building verbs
in Chuj: Consequences for the nature of roots." *Journal of Linguistics*
55(1): 35–81.

Theory-neutral data (root classes, voice morphology, paradigm grammaticality,
-aj distribution, agent diagnostics, root lexicon) lives in the Chuj fragment
(`Fragments/Chuj/VerbBuilding.lean`). This file provides:

## Paradigm examples (§§1–2)

Glossed Chuj sentences with root, voice suffix, and grammaticality.

## Minimalist analysis (§§3–9)

Voice heads as `Minimalist.VoiceHead` instances, event decomposition via
`buildDecomposition`, existential closure (-aj), and division of labor /
causative alternation proved from the Voice–root split.

## Bridge theorems (§§10–16)

Connect the fragment's theory-neutral types (`CRootClass`, `ChujVoiceSuffix`,
`isGrammatical`, etc.) to Minimalist VoiceHead properties and to the
@cite{beavers-etal-2021} root typology.

### Chuj fragment bridge (§§10–15)

1. **Root class ↔ Root arity**: `CRootClass` maps to `RootClassification` values.
   √TV = selectsTheme, others = noTheme.
2. **Voice suffix ↔ VoiceHead**: theta assignment, D feature, phase head.
3. **Paradigm predictions**: `isGrammatical` matches data attestation.
4. **-aj predictions**: `hasImplicitExternal` / `triggersAj` match -aj
   distribution.
5. **Agent diagnostics**: `assignsTheta` matches agent adverb / by-phrase.
6. **Division of labor**: `formsBareTransitive` aligns with arity.

### Root typology bridge (§§17–23)

Connects `Theories/Morphology/RootTypology.lean` (@cite{beavers-etal-2021})
to empirical data in `Phenomena/Causation/Studies/BeaversEtAl2021.lean`.

1. **Classification isomorphism**: The theory's `RootType` and the phenomena's
   `CoSRootClass` are provably isomorphic — they describe the same partition.

2. **Diagnostic alignment**: The phenomena's semantic diagnostics
   (`changeDenialTest`, `restitutiveAgainTest`) agree exactly with the theory's
   Boolean correlates (`entailsChange`, `allowsRestitutiveAgain`).

3. **Prediction ↔ attestation**: The theory predicts PC roots HAVE simple
   statives and result roots LACK them; the empirical data confirms this
   (PC: 7/8 sample roots ≥ 50%; result: all 10 sample roots ≤ 10%).

4. **Markedness prediction**: The theory predicts PC verbs are marked and result
   verbs are unmarked; the statistical comparison confirms PC median (56.01%)
   exceeds result median (15.20%).

5. **Fragment grounding**: The Chuj fragment's `RootClassification` values instantiate the
   theory's predictions — e.g., `rootTV_res.entailsChange = true` matches the
   theory's `RootType.entailsChange.result = true`.

-/

namespace Coon2019

open Fragments.Chuj

-- ════════════════════════════════════════════════════
-- § 1. Paradigm Examples (§§2–5)
-- ════════════════════════════════════════════════════

/-- A glossed Chuj example sentence. -/
structure ChujExample where
  /-- Example number in the paper -/
  exNumber : Nat
  /-- Page number -/
  page : Nat
  /-- Chuj form -/
  chuj : String
  /-- English translation -/
  english : String
  /-- Root used (from the Chuj fragment lexicon) -/
  verb : Fragments.Chuj.ChujRoot
  /-- Voice suffix -/
  voice : ChujVoiceSuffix
  /-- Whether the example is grammatical -/
  grammatical : Bool
  deriving Repr

-- Key paradigm examples from §§2–5

/-- (10a) Active transitive: √TV + Ø (§2.2, p. 41). -/
def ex10a : ChujExample :=
  ⟨10, 41, "Ix-ach-ko-chel-a'",
   "We hugged you.", chel, .null, true⟩

/-- (7a) √ITV + null v (§2.1, p. 40). -/
def ex7a : ChujExample :=
  ⟨7, 40, "Ix-onh-way-i",
   "We slept.", way, .null, true⟩

/-- (23a) √POS + -w (§3, p. 48). -/
def ex23a : ChujExample :=
  ⟨23, 48, "Ix-chot-w-i nok' k'ok'on",
   "The frog hopped.", chot, .w, true⟩

/-- (16b) √NOM + -w (§2.5, p. 45). -/
def ex16b : ChujExample :=
  ⟨16, 45, "Ix-in-chanhal-w-i",
   "I danced.", chanhal, .w, true⟩

/-- (62) √TV + -chaj (passive, §4.1.1, p. 68). -/
def ex62 : ChujExample :=
  ⟨62, 68, "tz-b'o'-ch-aj ... winh nhulej tik",
   "The brother's food is made by them.", b'o', .ch, true⟩

/-- (59) √TV + -j (agentless passive, §4.1.2, p. 67). -/
def ex59 : ChujExample :=
  ⟨59, 67, "tz-man-j-i ... / tz-choj-j-i ixim",
   "It is bought. / It is ground.", man, .j, true⟩

/-- (63a) Agent adverb with -chaj: grammatical (§4.1.1, p. 68). -/
def ex63a : ChujExample :=
  ⟨63, 68, "sk'annhej sk'o'ol winh ix-ch'ak-chaj te' te'",
   "The tree was felled on purpose.", ch'ak, .ch, true⟩

/-- (67a) Agent adverb with -j: ungrammatical (§4.1.2, p. 70). -/
def ex67a : ChujExample :=
  ⟨67, 70, "*sk'annhej sk'o'ol winh ix-ch'ak-j-i te' te'",
   "The tree was felled on purpose.", ch'ak, .j, false⟩

/-- (54a) √TV + -w incorporation antipassive (§4, p. 64). -/
def ex54a : ChujExample :=
  ⟨54, 64, "Ix-in-jax-w-i ixim",
   "I corn-ground.", jax, .w, true⟩

/-- (55b) √TV + -w absolutive antipassive (§4, p. 65). -/
def ex55 : ChujExample :=
  ⟨55, 65, "Ix-mak'-waj ix Malin t'a waj Xun",
   "Maria did some hitting to John.", mak', .w, true⟩

-- ════════════════════════════════════════════════════
-- § 2. Example Verification
-- ════════════════════════════════════════════════════

/-- Grammatical examples are predicted grammatical;
    ungrammatical examples are predicted ungrammatical. -/
theorem examples_grammaticality :
    ex10a.grammatical = true ∧     -- √TV + Ø
    ex7a.grammatical = true ∧    -- √ITV + null
    ex23a.grammatical = true ∧   -- √POS + -w
    ex16b.grammatical = true ∧   -- √NOM + -w
    ex62.grammatical = true ∧    -- √TV + -ch
    ex59.grammatical = true ∧    -- √TV + -j
    ex63a.grammatical = true ∧   -- agent adverb + -ch (OK)
    ex67a.grammatical = false ∧  -- agent adverb + -j (blocked)
    ex54a.grammatical = true ∧   -- -w incorporation antipassive
    ex55.grammatical = true :=   -- -w absolutive antipassive
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Minimalist Voice Analysis (@cite{coon-2019}, ex. (78))
-- ════════════════════════════════════════════════════

open Minimalist

/-- Active transitive v/Voice⁰ (Ø): introduces overt agent in Spec,VoiceP,
    assigns ergative case, phase head (v*). -/
def vØ : VoiceHead :=
  { flavor := .agentive, hasD := true, phaseHead := true }

/-- Agentive intransitive v/Voice⁰ (-w): introduces overt agent in
    Spec,VoiceP but assigns absolutive (not ergative) case (p. 54).
    Merges directly with root — cannot attach to derived stems (p. 54, (34b)).
    Used with √NOM and √POS to verbalize roots, and with √TV
    in incorporation antipassives (where the theme is a bare NP).
    Also models the null intransitive v/Voice⁰ for √ITV roots (p. 40):
    both introduce an agent and assign absolutive, differing only in
    overt (-w) vs null morphological realization. -/
def v_w : VoiceHead :=
  { flavor := .agentive, hasD := true, phaseHead := false }

/-- Passive v/Voice⁰ (-ch): assigns θ-role to an implicit (existentially
    bound) external argument (p. 68–69). Agent-oriented adverbs and
    by-phrases are licensed, confirming semantic presence of agent.
    Only combines with √TV roots. -/
def v_ch : VoiceHead :=
  { flavor := .agentive, hasD := false, phaseHead := false }

/-- Agentless passive v/Voice⁰ (-j): verbalizes stem but introduces
    no external argument — neither overt nor implicit (p. 70:
    "does not assign a thematic role and does not merge an external
    argument"). No agent-oriented adverbs, no agentive by-phrases.
    Used with √TV (agentless passive) and non-transitive roots
    (inchoative/stative readings). -/
def v_j : VoiceHead :=
  { flavor := .nonThematic, hasD := false, phaseHead := false }

-- ════════════════════════════════════════════════════
-- § 4. Event Decomposition
-- ════════════════════════════════════════════════════

/-- Lower event structure for result roots: cause + change + result state. -/
def resultLower : List VerbHead := [.vCAUSE, .vGO, .vBE]

/-- Lower event structure for activity roots (√TV PC, √ITV, √NOM):
    no sub-eventive decomposition below Voice. -/
def activityLower : List VerbHead := []

/-- Lower event structure for positional roots (√POS): stative. -/
def positionalLower : List VerbHead := [.vBE]

-- ════════════════════════════════════════════════════
-- § 5. Voice Head Properties
-- ════════════════════════════════════════════════════

/-- All three agentive voices (Ø, -w, -ch) assign a θ-role. -/
theorem agentive_voices_assign_theta :
    vØ.assignsTheta = true ∧
    v_w.assignsTheta = true ∧
    v_ch.assignsTheta = true := ⟨rfl, rfl, rfl⟩

/-- -j does NOT assign a θ-role: agentless (p. 70). -/
theorem v_j_no_theta : v_j.assignsTheta = false := rfl

/-- Only Ø is a phase head (assigns ergative case). -/
theorem only_vØ_is_phase :
    vØ.phaseHead = true ∧
    v_w.phaseHead = false ∧
    v_ch.phaseHead = false ∧
    v_j.phaseHead = false := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Verb Building (buildDecomposition)
-- ════════════════════════════════════════════════════

/-- √TV result + Ø → causative [vDO, vGO, vBE] (active transitive). -/
theorem tv_res_active :
    isCausative (buildDecomposition vØ resultLower) = true := by native_decide

/-- √TV result + -ch → causative [vDO, vGO, vBE] (passive with implicit agent).
    Event structure is still causative — the agent is semantically present. -/
theorem tv_res_passive_ch :
    isCausative (buildDecomposition v_ch resultLower) = true := by native_decide

/-- √TV result + -j → inchoative [vGO, vBE] (agentless passive / anticausative).
    No agent at all — the event is a pure change-of-state (p. 70). -/
theorem tv_res_agentless :
    isInchoative (buildDecomposition v_j resultLower) = true := by native_decide

/-- √ITV + v/Voice⁰ → activity [vDO] (intransitive).
    Uses v_w, which shares formal properties with the null intransitive
    v/Voice⁰ for √ITV (both are agentive, non-ERG-assigning; p. 40). -/
theorem itv_intransitive :
    isActivity (buildDecomposition v_w activityLower) = true := by native_decide

/-- √POS + -w → [vDO, vBE]: agent assumes a position (agentive stative).
    (p. 48, (23)): chot-w-i "The frog hopped." -/
theorem pos_agentive :
    buildDecomposition v_w positionalLower = [.vDO, .vBE] := by native_decide

/-- √NOM + -w → activity [vDO] (denominal agentive intransitive).
    (p. 45, (16b)): chanhal-w-i "I danced." -/
theorem nom_agentive :
    isActivity (buildDecomposition v_w activityLower) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. Existential Closure (-aj)
-- ════════════════════════════════════════════════════

/-- Does this Voice head have an implicit (existentially bound) external
    argument? True when Voice assigns θ but has no overt specifier. -/
def hasImplicitExternal (v : VoiceHead) : Bool :=
  v.assignsTheta && !v.hasD

/-- -aj (Existential Closure) surfaces when there is any implicit argument:
    implicit external (from Voice, as in -ch) or implicit internal (from
    theme suppression in absolutive antipassive -w-aj).

    `implicitInternal` is true when a √TV root's theme is not filled
    by an overt DP (absolutive antipassive, not incorporation antipassive). -/
def triggersAj (v : VoiceHead) (implicitInternal : Bool) : Bool :=
  hasImplicitExternal v || implicitInternal

/-- -ch always triggers -aj (implicit external agent; p. 69). -/
theorem ch_triggers_aj : hasImplicitExternal v_ch = true := by native_decide

/-- Ø never has an implicit external (agent is overt ERG DP). -/
theorem vØ_no_implicit : hasImplicitExternal vØ = false := by native_decide

/-- -w never has an implicit external (agent is overt ABS DP; p. 54). -/
theorem v_w_no_implicit : hasImplicitExternal v_w = false := by native_decide

/-- -j has no implicit external (there is no agent at all, not even
    implicit; p. 70: "no thematic agent, implicit or otherwise"). -/
theorem v_j_no_implicit : hasImplicitExternal v_j = false := by native_decide

/-- -ch-aj: passive of √TV with implicit agent (ex. (58), p. 66). -/
theorem ch_aj_passive :
    triggersAj v_ch false = true := by native_decide

/-- -w-aj: absolutive antipassive (√TV theme is implicit; ex. (58), p. 66). -/
theorem w_aj_antipassive :
    triggersAj v_w true = true := by native_decide

/-- -w incorporation antipassive: theme is overt bare NP → no -aj
    (ex. (58), p. 66; cf. (26b), p. 50). -/
theorem w_incorporation_no_aj :
    triggersAj v_w false = false := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. -w Cross-Class Generalization
-- ════════════════════════════════════════════════════

/-- -w serves the same structural function across three root classes:
    it merges directly with the root, verbalizes it, and introduces an
    agent without assigning ERG (p. 54–56). The only difference is the
    root's lower event structure. -/
theorem w_cross_class :
    -- √TV (incorporation antipassive): activity
    isActivity (buildDecomposition v_w activityLower) = true ∧
    -- √POS (positional verbalization): agent + state
    buildDecomposition v_w positionalLower = [.vDO, .vBE] ∧
    -- √NOM (denominal verbalization): activity
    isActivity (buildDecomposition v_w activityLower) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 9. Minimalist Division of Labor
-- ════════════════════════════════════════════════════

/-- Division of labor (@cite{coon-2019}, ex. (2)/(77), p. 75): the root
    determines whether a theme is present; Voice determines whether an
    agent is present. Same root with different Voice → different event type;
    same Voice with different root → same external argument status. -/
theorem minimalist_division_of_labor :
    -- Same result root: Ø gives causative, -j gives inchoative
    isCausative (buildDecomposition vØ resultLower) = true ∧
    isInchoative (buildDecomposition v_j resultLower) = true ∧
    -- √TV has theme, √ITV does not — root determines internal arg
    rootTV_res.arity.hasInternalArg = true ∧
    rootITV.arity.hasInternalArg = false := ⟨by native_decide, by native_decide, rfl, rfl⟩

/-- The causative alternation in Chuj is determined by Voice, not by the root
    (instantiation of `voice_determines_causativity_go_be` for Chuj heads).
    For result roots, causativity tracks exactly with θ-assignment. -/
theorem chuj_causative_alternation_result :
    isCausative (buildDecomposition vØ resultLower) = vØ.assignsTheta ∧
    isCausative (buildDecomposition v_w resultLower) = v_w.assignsTheta ∧
    isCausative (buildDecomposition v_ch resultLower) = v_ch.assignsTheta ∧
    isCausative (buildDecomposition v_j resultLower) = v_j.assignsTheta :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 10. Chuj Fragment Bridge Theorems
-- ════════════════════════════════════════════════════

/-- Map the phenomena's root class to the fragment's RootClassification.
    This connects theory-neutral distributional classes to the
    theoretically analyzed RootClassification structure.
    √TV maps to `rootTV_res` as a representative — the choice between
    `rootTV_res` and `rootTV_pc` is arbitrary for arity (both are
    `selectsTheme`); only changeType differs. -/
def toFragmentRoot : CRootClass → RootClassification
  | .tv  => rootTV_res
  | .itv => rootITV
  | .pos => rootPOS
  | .nom => rootNOM

/-- √TV maps to a theme-selecting root; all others map to non-theme roots.
    This is the formal content of the observation that only √TV forms
    bare transitive stems (§2.2). -/
theorem root_class_arity_alignment :
    (toFragmentRoot .tv).arity = .selectsTheme ∧
    (toFragmentRoot .itv).arity = .noTheme ∧
    (toFragmentRoot .pos).arity = .noTheme ∧
    (toFragmentRoot .nom).arity = .noTheme := ⟨rfl, rfl, rfl, rfl⟩

/-- The data's `formsBareTransitive` matches the fragment's `hasInternalArg`.
    Only roots that select a theme can form bare transitive stems. -/
theorem bare_transitive_iff_theme (rc : CRootClass) :
    formsBareTransitive rc = (toFragmentRoot rc).arity.hasInternalArg := by
  cases rc <;> rfl

-- ════════════════════════════════════════════════════
-- § 11. Voice Suffix ↔ VoiceHead
-- ════════════════════════════════════════════════════

/-- Map the phenomena's voice suffix to the Minimalist VoiceHead. -/
def toVoiceHead : ChujVoiceSuffix → VoiceHead
  | .null => vØ
  | .ch   => v_ch
  | .j    => v_j
  | .w    => v_w

/-- Theta assignment matches: the data's `hasAgent` agrees with the
    fragment's `assignsTheta` for all four voice suffixes. -/
theorem theta_alignment (vs : ChujVoiceSuffix) :
    vs.hasAgent = (toVoiceHead vs).assignsTheta := by
  cases vs <;> rfl

/-- External argument status matches D feature:
    overt external arg ↔ hasD = true. -/
theorem d_feature_alignment :
    -- Ø: overt ERG → hasD
    (toVoiceHead .null).hasD = true ∧
    -- -w: overt ABS → hasD
    (toVoiceHead .w).hasD = true ∧
    -- -ch: implicit → no D
    (toVoiceHead .ch).hasD = false ∧
    -- -j: absent → no D
    (toVoiceHead .j).hasD = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Only Ø is a phase head (assigns ERG case). -/
theorem phase_head_alignment :
    (toVoiceHead .null).phaseHead = true ∧
    (toVoiceHead .ch).phaseHead = false ∧
    (toVoiceHead .j).phaseHead = false ∧
    (toVoiceHead .w).phaseHead = false := ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 12. Agent Diagnostic Alignment
-- ════════════════════════════════════════════════════

/-- The data's agent adverb diagnostic matches the fragment's theta assignment.
    Agent-oriented adverbs require a theta-role-bearing Voice head. -/
theorem agent_adverb_matches_theta (vs : ChujVoiceSuffix) :
    agentAdverbOK vs = (toVoiceHead vs).assignsTheta := by
  cases vs <;> rfl

/-- The -ch vs -j contrast is the critical test: both are passives (no overt
    external arg), but they differ in theta assignment. The agent diagnostic
    data confirms the fragment's distinction. -/
theorem passive_contrast :
    -- -ch: assigns theta, agent adverbs OK, by-phrases OK
    (toVoiceHead .ch).assignsTheta = true ∧
    agentAdverbOK .ch = true ∧
    byPhraseOK .ch = true ∧
    -- -j: no theta, agent adverbs blocked, by-phrases blocked
    (toVoiceHead .j).assignsTheta = false ∧
    agentAdverbOK .j = false ∧
    byPhraseOK .j = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 13. -aj Distribution Alignment
-- ════════════════════════════════════════════════════

/-- The data's -aj on passives matches the fragment's `hasImplicitExternal`.
    -aj appears when there is an implicit (but not absent) external argument. -/
theorem aj_passive_matches_implicit (vs : ChujVoiceSuffix) :
    ajOnPassive vs = hasImplicitExternal (toVoiceHead vs) := by
  cases vs <;> native_decide

/-- The fragment's `triggersAj` predicts the data's full -aj distribution:
    - -ch (implicit ext) → -aj
    - -j (no ext) → no -aj
    - -w absolutive (implicit int) → -aj
    - -w incorporation (overt int) → no -aj -/
theorem aj_full_distribution :
    -- Passive -ch: implicit external → -aj
    triggersAj v_ch false = true ∧
    ajOnPassive .ch = true ∧
    -- Agentless -j: no external → no -aj
    triggersAj v_j false = false ∧
    ajOnPassive .j = false ∧
    -- Antipassive -w (absolutive): implicit internal → -aj
    triggersAj v_w true = true ∧
    ajOnAntipassive .absolutive = true ∧
    -- Antipassive -w (incorporation): overt internal → no -aj
    triggersAj v_w false = false ∧
    ajOnAntipassive .incorporation = false :=
  ⟨by native_decide, rfl, by native_decide, rfl,
   by native_decide, rfl, by native_decide, rfl⟩

-- ════════════════════════════════════════════════════
-- § 14. Verb Building Predictions
-- ════════════════════════════════════════════════════

/-- The fragment predicts correct event decompositions for each
    root×voice combination attested in the data.

    √TV result + Ø → causative (active transitive)
    √TV result + -j → inchoative (agentless passive / anticausative)
    √TV result + -ch → causative (passive with implicit agent)
    √ITV + -w → activity (intransitive) -/
theorem event_decomposition_matches_data :
    -- ex10a: √TV + Ø → causative
    isCausative (buildDecomposition vØ resultLower) = true ∧
    -- ex59: √TV + -j → inchoative
    isInchoative (buildDecomposition v_j resultLower) = true ∧
    -- ex62: √TV + -ch → causative (agent still present)
    isCausative (buildDecomposition v_ch resultLower) = true ∧
    -- ex7a: √ITV + v_w → activity
    isActivity (buildDecomposition v_w activityLower) = true :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 15. Division of Labor
-- ════════════════════════════════════════════════════

/-- The core empirical claim (ex. (2)/(77), p. 75): roots determine
    internal arguments, Voice determines external arguments.

    The data confirms this in two ways:
    1. Theme persistence: √TV always has an internal arg regardless of Voice
    2. Voice determines agent: same root with Ø has overt agent,
       with -ch has implicit agent, with -j has no agent -/
theorem division_of_labor_matches_data :
    -- Root determines internal: √TV always selects theme
    formsBareTransitive .tv = true ∧
    rootTV_res.arity.hasInternalArg = true ∧
    -- Root determines internal: √ITV never selects theme
    formsBareTransitive .itv = false ∧
    rootITV.arity.hasInternalArg = false ∧
    -- Voice determines external: same root, different agent status
    ChujVoiceSuffix.extArgStatus .null = .overt_erg ∧
    ChujVoiceSuffix.extArgStatus .ch = .implicit ∧
    ChujVoiceSuffix.extArgStatus .j = .absent :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Theme persistence across all four voice forms for √TV.
    The data shows √TV maintains its internal argument in active (Ø),
    passive (-ch), agentless passive (-j), and antipassive (-w).
    The fragment encodes this as a root property (arity), not a
    derived property — so it holds by construction. -/
theorem theme_persists_all_voices :
    -- √TV is grammatical with all four voice suffixes (data)
    isGrammatical .tv .null = true ∧
    isGrammatical .tv .ch = true ∧
    isGrammatical .tv .j = true ∧
    isGrammatical .tv .w = true ∧
    -- And the root always selects a theme (fragment)
    rootTV_res.arity.hasInternalArg = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 16. Denotation Type Alignment
-- ════════════════════════════════════════════════════

/-- The four root classes have distinct denotation types (@cite{coon-2019}, (3)).
    The fragment's `denotationType` field captures these:
    √TV/√ITV = indivStatePred ⟨e,⟨s,t⟩⟩, √POS = measureFn ⟨e,⟨s,d⟩⟩,
    √NOM = entityPred ⟨e,t⟩. -/
theorem denotation_type_alignment :
    (toFragmentRoot .tv).denotationType = some .indivStatePred ∧
    (toFragmentRoot .itv).denotationType = some .indivStatePred ∧
    (toFragmentRoot .pos).denotationType = some .measureFn ∧
    (toFragmentRoot .nom).denotationType = some .entityPred := ⟨rfl, rfl, rfl, rfl⟩

/-- √TV and √ITV share semantic type (event predicate) but differ in arity.
    This is the formal content of the observation that both compose with
    an entity argument per @cite{davis-1997}, but only √TV projects a syntactic
    complement. -/
theorem tv_itv_same_type_different_arity :
    (toFragmentRoot .tv).denotationType = (toFragmentRoot .itv).denotationType ∧
    (toFragmentRoot .tv).arity ≠ (toFragmentRoot .itv).arity := by
  exact ⟨rfl, by decide⟩

/-- The -w suffix cross-class generalization: -w verbalizes √POS and √NOM
    roots (data: both take -w), and the fragment predicts different event
    structures depending on the root's lower structure. -/
theorem w_verbalization_cross_class :
    -- Both √POS and √NOM take -w (data)
    isGrammatical .pos .w = true ∧
    isGrammatical .nom .w = true ∧
    -- √POS + -w → [vDO, vBE] (fragment)
    buildDecomposition v_w positionalLower = [.vDO, .vBE] ∧
    -- √NOM + -w → activity [vDO] (fragment)
    isActivity (buildDecomposition v_w activityLower) = true :=
  ⟨rfl, rfl, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 17. Root Typology Bridge (BeaversEtAl2021)
-- ════════════════════════════════════════════════════

open BeaversEtAl2021

/-- Map the theory's root type to the phenomena's root class.
    These are parallel enums — the bridge makes the correspondence explicit. -/
def toCoSRootClass : RootType → CoSRootClass
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- Map back from phenomena to theory. -/
def fromCoSRootClass : CoSRootClass → RootType
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- The mapping is a bijection (left inverse). -/
theorem roundtrip_left (rt : RootType) :
    fromCoSRootClass (toCoSRootClass rt) = rt := by
  cases rt <;> rfl

/-- The mapping is a bijection (right inverse). -/
theorem roundtrip_right (rc : CoSRootClass) :
    toCoSRootClass (fromCoSRootClass rc) = rc := by
  cases rc <;> rfl

-- ════════════════════════════════════════════════════
-- § 18. Diagnostic Alignment (Root Typology)
-- ════════════════════════════════════════════════════

/-- The phenomena's `changeDenialTest` agrees with the theory's `entailsChange`.

    Theory: `RootType.entailsChange.result = true` (result roots entail change)
    Phenomena: `changeDenialTest.result =.negative` ("#The shattered vase
    has never shattered" is contradictory — the state entails prior change)

    The relationship is: entailsChange = true ↔ changeDenial = negative.
    That is, entailing change means the change-denial test FAILS. -/
theorem change_denial_matches_entailsChange (rc : CoSRootClass) :
    changeDenialTest rc = .positive ↔
    (fromCoSRootClass rc).entailsChange = false := by
  cases rc <;> simp [changeDenialTest, fromCoSRootClass, RootType.entailsChange]

/-- The phenomena's `restitutiveAgainTest` agrees with the theory's
    `allowsRestitutiveAgain`. -/
theorem restitutive_again_matches (rc : CoSRootClass) :
    restitutiveAgainTest rc = .positive ↔
    (fromCoSRootClass rc).allowsRestitutiveAgain = true := by
  cases rc <;> simp [restitutiveAgainTest, fromCoSRootClass,
    RootType.allowsRestitutiveAgain]

/-- Both diagnostics jointly align with the full semantic correlate package.
    This is the bridge version of `semantic_determines_morphosyntax`. -/
theorem diagnostics_align_with_theory (rc : CoSRootClass) :
    let rt := fromCoSRootClass rc
    (changeDenialTest rc = .negative ↔ rt.entailsChange = true) ∧
    (restitutiveAgainTest rc = .negative ↔ rt.allowsRestitutiveAgain = false) := by
  cases rc <;> simp [changeDenialTest, restitutiveAgainTest, fromCoSRootClass,
    RootType.entailsChange, RootType.allowsRestitutiveAgain]

-- ════════════════════════════════════════════════════
-- § 19. Simple Stative Prediction ↔ Attestation
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC roots have simple statives.
    **Data confirms**: 7 of 8 PC sample roots have ≥ 50% attestation.
    The one exception (oldRoot, age class) has 0 — noted by Beavers et al.
    as a crosslinguistic outlier. -/
theorem pc_stative_prediction_matches_data :
    -- Theory prediction
    RootType.hasSimpleStative .propertyConcept = true ∧
    -- Empirical confirmation (all but one PC root)
    (pcRoots.filter (λ r => r.nSimpleStative * 2 ≥ r.nLanguages)).length ≥
    pcRoots.length - 1 := by
  exact ⟨rfl, by native_decide⟩

/-- **Theory predicts**: result roots LACK simple statives.
    **Data confirms**: all 10 result sample roots have ≤ 10% attestation. -/
theorem result_no_stative_prediction_matches_data :
    -- Theory prediction
    RootType.hasSimpleStative .result = false ∧
    -- Empirical confirmation (ALL result roots)
    resultRoots.all (λ r => r.nSimpleStative * 10 ≤ r.nLanguages) = true := by
  exact ⟨rfl, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 20. Markedness Prediction ↔ Statistical Comparison
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC verbs are morphologically marked; result verbs
    are unmarked (Markedness Generalization, @cite{beavers-etal-2021}).
    **Data confirms**: PC median marked % (56.01) > result median (15.20). -/
theorem markedness_prediction_matches_statistics :
    -- Theory: PC verbs are marked
    verbalMarkedness .propertyConcept = .marked ∧
    -- Theory: result verbs are unmarked
    verbalMarkedness .result = .unmarked ∧
    -- Data: PC marked rate exceeds result marked rate
    simpleStativeComparison.pcMedian > simpleStativeComparison.resultMedian ∧
    verbalMarkednessComparison.pcMedian > verbalMarkednessComparison.resultMedian := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════
-- § 21. Unattested Language Type
-- ════════════════════════════════════════════════════

/-- The theory's markedness complementarity predicts that if a language
    marks PC verbs, it should NOT also show result verbs as more marked
    than PC verbs. The fourth logically possible language type (result
    marked, PC unmarked) is unattested — exactly 3 types are attested.
    This matches the theory: `markedness_complementarity` says verbal and
    stative markedness are always opposite. -/
theorem unattested_type_matches_complementarity :
    -- Exactly three types attested
    LanguageType.allAttested.length = 3 ∧
    -- Theory: verbal and stative markedness always differ
    (∀ rt : RootType, verbalMarkedness rt ≠ stativeMarkedness rt) := by
  refine ⟨by native_decide, ?_⟩
  intro rt; cases rt <;> simp [verbalMarkedness, stativeMarkedness,
    RootType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 22. Fragment Grounding: Chuj Roots Instantiate Theory
-- ════════════════════════════════════════════════════

/-- Chuj √TV result roots instantiate the theory's result root predictions:
    entails change, no simple stative, unmarked verb. -/
theorem chuj_tv_res_is_result_root :
    rootTV_res.entailsChange = true ∧
    rootTV_res.changeType.hasSimpleStative = false ∧
    rootTV_res.verbalMarkedness = .unmarked := by
  exact ⟨rfl, rfl, rfl⟩

/-- Chuj √TV PC roots instantiate the theory's PC root predictions:
    no change entailment, has simple stative, marked verb. -/
theorem chuj_tv_pc_is_pc_root :
    rootTV_pc.entailsChange = false ∧
    rootTV_pc.changeType.hasSimpleStative = true ∧
    rootTV_pc.verbalMarkedness = .marked := by
  exact ⟨rfl, rfl, rfl⟩

/-- The Chuj fragment witnesses the full orthogonality theorem:
    all four cells of the (arity × changeType) matrix are inhabited. -/
theorem chuj_witnesses_orthogonality :
    -- selectsTheme + result (√TV result)
    rootTV_res.arity = .selectsTheme ∧ rootTV_res.changeType = .result ∧
    -- selectsTheme + PC (√TV PC)
    rootTV_pc.arity = .selectsTheme ∧ rootTV_pc.changeType = .propertyConcept ∧
    -- noTheme + PC (√ITV, √POS, √NOM)
    rootITV.arity = .noTheme ∧ rootITV.changeType = .propertyConcept :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Per-root class verification: each Chuj root's change entailment matches
    its predicted morphosyntactic correlates via `grand_unification`. -/
theorem chuj_roots_satisfy_grand_unification :
    -- Result root (√TV res): entails change → full result package
    (rootTV_res.changeType.hasSimpleStative = false ∧
     rootTV_res.changeType.verbalFormIsMarked = false ∧
     rootTV_res.changeType.allowsRestitutiveAgain = false) ∧
    -- PC root (√TV PC): no change → full PC package
    (rootTV_pc.changeType.hasSimpleStative = true ∧
     rootTV_pc.changeType.verbalFormIsMarked = true ∧
     rootTV_pc.changeType.allowsRestitutiveAgain = true) ∧
    -- PC root (√ITV): no change → full PC package
    (rootITV.changeType.hasSimpleStative = true ∧
     rootITV.changeType.verbalFormIsMarked = true ∧
     rootITV.changeType.allowsRestitutiveAgain = true) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

-- ════════════════════════════════════════════════════
-- § 23. Per-Root Data ↔ Theory Agreement
-- ════════════════════════════════════════════════════

/-- Every PC root in the empirical sample is classified as PC, and the theory
    predicts PC roots should have simple statives — they do. -/
theorem pc_roots_classified_and_predicted :
    -- Data: all sample PC roots are classified as PC
    pcRoots.all (·.rootClass == .propertyConcept) = true ∧
    -- Theory: PC has simple stative
    RootType.hasSimpleStative .propertyConcept = true := by
  exact ⟨by native_decide, rfl⟩

/-- Every result root in the empirical sample is classified as result, and the
    theory predicts result roots lack simple statives — they do. -/
theorem result_roots_classified_and_predicted :
    -- Data: all sample result roots are classified as result
    resultRoots.all (·.rootClass == .result) = true ∧
    -- Theory: result lacks simple stative
    RootType.hasSimpleStative .result = false := by
  exact ⟨by native_decide, rfl⟩

/-- The subclass taxonomies are aligned: B&KG's `PCSubclass` has 6
    categories (matching their Table 2); the theory's `PCClass` has 7
    (adding `humanPropensity` from @cite{dixon-1982}, attested in
    @cite{hanink-koontz-garboden-2025}). `ResultClass` and `ResultSubclass`
    match exactly (8 subclasses). -/
theorem subclass_counts_match :
    -- B&KG's 6 PC subclasses are a subset of the theory's 7
    [PCSubclass.dimension, .age, .value, .color, .physicalProperty, .speed].length = 6 ∧
    [PCClass.dimension, .age, .value, .color, .physicalProperty, .humanPropensity, .speed].length = 7 ∧
    -- 8 result subclasses in both
    [ResultClass.entitySpecificCoS, .cooking, .breaking, .bending,
     .killing, .destroying, .calibratableCoS, .inherentlyDirectedMotion].length =
    [ResultSubclass.entitySpecificCoS, .cooking, .breaking, .bending,
     .killing, .destroying, .calibratableCoS, .inherentlyDirectedMotion].length :=
  ⟨rfl, rfl, rfl⟩

end Coon2019
