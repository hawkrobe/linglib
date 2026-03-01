import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Morphology.RootTypology
import Linglib.Core.Interfaces.VoiceSystem

/-!
# Chuj Verb Building Fragment (Coon 2019) @cite{coon-2019}
@cite{davis-1997}

Formalization of the core claims from Coon (2019) "Building verbs in Chuj:
Consequences for the nature of roots."

## Key Claims

1. **Four root classes** (√TV, √ITV, √POS, √NOM) distinguished primarily
   by complement projection. √TV projects a complement DP; the others
   do not. Semantically, Coon (2019, (3)) assigns:
   √TV ⟨e, ⟨s,t⟩⟩, √ITV ⟨e, ⟨s,t⟩⟩, √POS ⟨e, ⟨s,d⟩⟩, √NOM ⟨e,t⟩.
   Note: √TV and √ITV share the same semantic type following Davis (1997),
   but differ in whether their entity argument surfaces as a complement (√TV)
   or becomes the subject (√ITV).
2. **Four v/Voice⁰ heads** (Ø, -w, -ch, -j) distinguished by whether
   they assign a θ-role and whether the external argument is overt,
   implicit, or absent.
3. **Division of labor** (Table (2)/(77)): Roots determine internal
   arguments (complement selection); Voice heads determine external
   arguments. The causative alternation follows from this split.
4. **-aj as Existential Closure** (p. 76): The suffix -aj is the overt
   morphological reflex of existential binding of an implicit argument.
5. **Voice alternations are root-derived** (p. 77, citing Alexiadou et al.
   2006): each voice form is built independently from root + v/Voice⁰,
   not derived from another voice form (e.g., passive is not derived
   from active).

## Chuj Voice Morphology (Table 58)

| Suffix | Type              | θ-role | Agent status  | Case on EA |
|--------|-------------------|--------|---------------|------------|
| Ø      | Active transitive | ✓      | Overt (ERG)   | Ergative   |
| -w     | Agentive intrans. | ✓      | Overt (ABS)   | Absolutive |
| -ch    | Passive           | ✓      | Implicit (x∃) | —          |
| -j     | Agentless passive | ✗      | None          | —          |

## Modeling Notes

**RootArity captures complement projection, not semantic type.**
Coon's semantic types (3) group {√TV, √ITV} together as ⟨e, ⟨s,t⟩⟩ — both
compose with an entity argument per Davis (1997). But syntactically, only
√TV projects a complement DP that persists across voice alternations; √ITV's
entity argument becomes the subject. Our `RootArity.selectsTheme` captures
the syntactic complement projection, giving {√TV} vs {√ITV, √POS, √NOM}.
This matches the -aj diagnostic: -aj marks implicit arguments, and only √TV
stems show -aj (the theme can be implicit), not √ITV.

-/

namespace Fragments.Chuj

open Minimalism

-- ============================================================================
-- § 1: Chuj Voice Heads
-- ============================================================================

/-- Active transitive v/Voice⁰ (Ø): introduces overt agent in Spec,VoiceP,
    assigns ergative case, phase head (v*). -/
def vØ : VoiceHead :=
  { flavor := .agentive, hasD := true, phaseHead := true }

/-- Agentive intransitive v/Voice⁰ (-w): introduces overt agent in
    Spec,VoiceP but assigns absolutive (not ergative) case (p. 54).
    Merges directly with root — cannot attach to derived stems (p. 55, (34a)).
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

-- ============================================================================
-- § 2: Chuj Root Classes
-- ============================================================================

/-- √TV root (PC): selects theme, no entailed change-of-state.
    Semantic type ⟨e, ⟨s,t⟩⟩ (Coon 2019, (3)).
    Examples: mak' "hit", tek' "kick". -/
def rootTV_pc : Root :=
  { arity := .selectsTheme, changeType := .propertyConcept,
    denotationType := some .eventPred }

/-- √TV root (result): selects theme, entails change-of-state.
    Semantic type ⟨e, ⟨s,t⟩⟩ (Coon 2019, (3)).
    Examples: jatz' "hit (breaking)", tzak' "wrap". -/
def rootTV_res : Root :=
  { arity := .selectsTheme, changeType := .result,
    denotationType := some .eventPred }

/-- √ITV root: semantic type ⟨e, ⟨s,t⟩⟩ (same as √TV per Davis 1997),
    but does NOT project a complement — the entity argument becomes the
    subject. The class is morphologically defined: roots that appear
    with null v/Voice⁰ in intransitive stems (p. 40).
    Examples: way "sleep", ok' "cry", jaw "arrive", b'at "go".
    Distinguished from √POS and √NOM by `denotationType`: all three
    lack a syntactic complement, but √ITV is an event predicate,
    √POS a measure function, and √NOM an entity predicate. -/
def rootITV : Root :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .eventPred }

/-- √POS root: positional/stative. Semantic type ⟨e, ⟨s,d⟩⟩ — a
    measure function, not a truth-value predicate (Henderson 2017).
    Examples: chot "sit", kot "on all fours", watz "lie face down". -/
def rootPOS : Root :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .measureFn }

/-- √NOM root: nominal base. Semantic type ⟨e,t⟩ — entity predicate
    with no event argument (Coon 2019, (3)).
    Examples: a' "water", ixim "corn", chanhal "dance". -/
def rootNOM : Root :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .entityPred }

-- ============================================================================
-- § 3: Root Lower Event Structures
-- ============================================================================

-- The root determines the lower event structure (below Voice).
-- This is independent of which Voice head attaches.

/-- Lower event structure for result roots: change + result state. -/
def resultLower : List VerbHead := [.vGO, .vBE]

/-- Lower event structure for activity roots (√TV PC, √ITV, √NOM):
    no sub-eventive decomposition below Voice. -/
def activityLower : List VerbHead := []

/-- Lower event structure for positional roots (√POS): stative. -/
def positionalLower : List VerbHead := [.vBE]

-- ============================================================================
-- § 4: Voice Head Properties
-- ============================================================================

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

/-- All three agentive voices contribute vDO to the event decomposition. -/
theorem agentive_voices_contribute_vDO :
    vØ.flavor.eventContribution = some .vDO ∧
    v_w.flavor.eventContribution = some .vDO ∧
    v_ch.flavor.eventContribution = some .vDO := ⟨rfl, rfl, rfl⟩

/-- -j contributes no subevent (no external cause). -/
theorem v_j_no_event : v_j.flavor.eventContribution = none := rfl

-- ============================================================================
-- § 5: Verb Building (buildDecomposition)
-- ============================================================================

-- Core combinations from Coon (2019) §4–5.
-- Each voice form is built independently from root + v/Voice⁰ (p. 77,
-- citing Alexiadou et al. 2006): passive is not derived from active.

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
    (p. 52, (23b)): chot-w-i "hopped along crouched-down". -/
theorem pos_agentive :
    buildDecomposition v_w positionalLower = [.vDO, .vBE] := by native_decide

/-- √NOM + -w → activity [vDO] (denominal agentive intransitive).
    (p. 46, (16b)): chanhal-w-i "danced". -/
theorem nom_agentive :
    isActivity (buildDecomposition v_w activityLower) = true := by native_decide

-- ============================================================================
-- § 6: Existential Closure (-aj)
-- ============================================================================

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

/-- -ch-aj: passive of √TV with implicit agent (Table 58). -/
theorem ch_aj_passive :
    triggersAj v_ch false = true := by native_decide

/-- -w-aj: absolutive antipassive (√TV theme is implicit; Table 58). -/
theorem w_aj_antipassive :
    triggersAj v_w true = true := by native_decide

/-- -w incorporation antipassive: theme is overt bare NP → no -aj
    (Table 58; p. 56, (26b)). -/
theorem w_incorporation_no_aj :
    triggersAj v_w false = false := by native_decide

-- ============================================================================
-- § 7: -w Cross-Class Generalization
-- ============================================================================

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

-- ============================================================================
-- § 8: Division of Labor Theorems
-- ============================================================================

/-- Division of labor (Coon 2019, Table (2)/(77), p. 76): the root
    determines whether a theme is present; Voice determines whether an
    agent is present. Same root with different Voice → different event type;
    same Voice with different root → same external argument status. -/
theorem division_of_labor :
    -- Same result root: Ø gives causative, -j gives inchoative
    isCausative (buildDecomposition vØ resultLower) = true ∧
    isInchoative (buildDecomposition v_j resultLower) = true ∧
    -- √TV has theme, √ITV does not — root determines internal arg
    rootTV_res.arity.hasInternalArg = true ∧
    rootITV.arity.hasInternalArg = false := ⟨by native_decide, by native_decide, rfl, rfl⟩

/-- Theme persistence (p. 76: "there is no option in which the transitive
    root selects no complement"): a root's complement projection is invariant
    across voice alternation. By construction, `arity` is a field on `Root`,
    not on the root+voice combination, so this is structural. -/
theorem theme_persistence :
    rootTV_res.arity.hasInternalArg = true ∧
    rootTV_pc.arity.hasInternalArg = true ∧
    rootITV.arity.hasInternalArg = false ∧
    rootPOS.arity.hasInternalArg = false ∧
    rootNOM.arity.hasInternalArg = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The causative alternation in Chuj is determined by Voice, not by the root
    (instantiation of `voice_determines_causativity_go_be` for Chuj heads).
    For result roots, causativity tracks exactly with θ-assignment. -/
theorem chuj_causative_alternation_result :
    isCausative (buildDecomposition vØ resultLower) = vØ.assignsTheta ∧
    isCausative (buildDecomposition v_w resultLower) = v_w.assignsTheta ∧
    isCausative (buildDecomposition v_ch resultLower) = v_ch.assignsTheta ∧
    isCausative (buildDecomposition v_j resultLower) = v_j.assignsTheta :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

-- ============================================================================
-- § 9: Four-Way Root Classification Recovery (Coon 2019, (3))
-- ============================================================================

/-- Coon's four root classes are recovered as (arity × denotationType) pairs.
    This is the formal content of the claim that arity and denotation type
    jointly determine root class:
    √TV = selectsTheme + eventPred, √ITV = noTheme + eventPred,
    √POS = noTheme + measureFn, √NOM = noTheme + entityPred. -/
theorem four_way_classification :
    -- √TV: selects theme, event predicate
    rootTV_res.arity = .selectsTheme ∧
    rootTV_res.denotationType = some .eventPred ∧
    -- √ITV: no theme, event predicate (same semantic type as √TV)
    rootITV.arity = .noTheme ∧
    rootITV.denotationType = some .eventPred ∧
    -- √POS: no theme, measure function
    rootPOS.arity = .noTheme ∧
    rootPOS.denotationType = some .measureFn ∧
    -- √NOM: no theme, entity predicate
    rootNOM.arity = .noTheme ∧
    rootNOM.denotationType = some .entityPred := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The four root classes are pairwise distinguishable: no two share
    both arity and denotationType. -/
theorem root_classes_pairwise_distinct :
    -- √TV ≠ √ITV (different arity)
    (rootTV_res.arity ≠ rootITV.arity) ∧
    -- √ITV ≠ √POS (different denotationType)
    (rootITV.denotationType ≠ rootPOS.denotationType) ∧
    -- √ITV ≠ √NOM (different denotationType)
    (rootITV.denotationType ≠ rootNOM.denotationType) ∧
    -- √POS ≠ √NOM (different denotationType)
    (rootPOS.denotationType ≠ rootNOM.denotationType) := by
  exact ⟨by decide, by decide, by decide, by decide⟩

-- ============================================================================
-- § 10: Voice System Profile
-- ============================================================================

/-- Chuj voice system: four-way asymmetrical (Ø, -w, -ch, -j).

    Unlike pivot systems (Toba Batak, Tagalog), Chuj voices don't
    promote arguments to a privileged position. Instead, Voice controls
    whether an external argument is overt, implicit, or absent.
    Each voice form is built independently from root + v/Voice⁰
    (Alexiadou et al. 2006): passive is not derived from active. -/
def chujVoiceSystem : Interfaces.VoiceSystemProfile :=
  { language := "Chuj"
    voices := [ ⟨"Active (Ø)", .agent⟩
              , ⟨"Agentive intransitive (-w)", .agent⟩
              , ⟨"Passive (-ch)", .patient⟩
              , ⟨"Agentless passive (-j)", .patient⟩ ]
    symmetry := .asymmetrical
    notes := "Non-pivot system; Voice controls EA status (Coon 2019)" }

theorem chuj_voice_system_asymmetrical :
    chujVoiceSystem.symmetry = .asymmetrical := rfl

theorem chuj_voice_count :
    chujVoiceSystem.voiceCount = 4 := rfl

/-- Chuj is NOT a simple active/passive: it has 4 voices, not 2. -/
theorem chuj_not_simple_active_passive :
    chujVoiceSystem.isActivePassive = false := rfl

theorem chuj_no_oblique_pivots :
    chujVoiceSystem.distinguishesObliques = false := rfl

end Fragments.Chuj
