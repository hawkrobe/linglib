import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Semantics.Events.RootTypology

/-!
# Chuj Verb Building Fragment (Coon 2019) @cite{coon-2019}

Formalization of the core claims from Coon (2019) "Building verbs in Chuj:
Consequences for the nature of roots."

## Key Claims

1. **Four root classes** (√TV, √ITV, √POS, √NOM) distinguished by arity:
   √TV selects a theme (⟨e, ⟨s,t⟩⟩); the others do not (⟨s,t⟩).
2. **Four v/Voice⁰ heads** (Ø, -w, -ch, -j) distinguished by whether
   they assign a θ-role and whether the external argument is overt,
   implicit, or absent.
3. **Division of labor**: Roots determine internal arguments (theme
   selection); Voice heads determine external arguments. The causative
   alternation follows from this split.
4. **-aj as Existential Closure**: The suffix -aj is the overt
   morphological reflex of existential binding of an implicit argument.

## Chuj Voice Morphology (Table 58)

| Suffix | Type              | θ-role | Agent status  | Case on EA |
|--------|-------------------|--------|---------------|------------|
| Ø      | Active transitive | ✓      | Overt (ERG)   | Ergative   |
| -w     | Agentive intrans. | ✓      | Overt (ABS)   | Absolutive |
| -ch    | Passive           | ✓      | Implicit (x∃) | —          |
| -j     | Agentless passive | ✗      | None          | —          |

## References

- Coon, J. (2019). Building verbs in Chuj: Consequences for the nature
  of roots. *Glossa* 4(1): 74.
-/

namespace Fragments.Chuj

open Minimalism
open Semantics.Events.RootTypology

-- ============================================================================
-- § 1: Chuj Voice Heads
-- ============================================================================

/-- Active transitive v/Voice⁰ (Ø): introduces overt agent in Spec,VoiceP,
    assigns ergative case, phase head (v*). -/
def vØ : VoiceHead :=
  { flavor := .agentive, hasD := true, phaseHead := true }

/-- Agentive intransitive v/Voice⁰ (-w): introduces overt agent in
    Spec,VoiceP but assigns absolutive (not ergative) case.
    Used with √NOM and √POS to verbalize roots, and with √TV
    in incorporation antipassives (where the theme is a bare NP). -/
def v_w : VoiceHead :=
  { flavor := .agentive, hasD := true, phaseHead := false }

/-- Passive v/Voice⁰ (-ch): assigns θ-role to an implicit (existentially
    bound) external argument. Agent-oriented adverbs and by-phrases
    are licensed, confirming semantic presence of agent.
    Only combines with √TV roots. -/
def v_ch : VoiceHead :=
  { flavor := .agentive, hasD := false, phaseHead := false }

/-- Agentless passive v/Voice⁰ (-j): verbalizes stem but introduces
    no external argument — neither overt nor implicit. No agent-oriented
    adverbs, no agentive by-phrases. Used with √TV (agentless passive)
    and non-transitive roots (inchoative/stative readings). -/
def v_j : VoiceHead :=
  { flavor := .expletive, hasD := false, phaseHead := false }

-- ============================================================================
-- § 2: Chuj Root Classes
-- ============================================================================

/-- √TV root (PC): selects theme, no entailed change-of-state.
    Examples: mak' "hit", tek' "kick". -/
def rootTV_pc : Root :=
  { arity := .selectsTheme, changeType := .propertyConcept }

/-- √TV root (result): selects theme, entails change-of-state.
    Examples: jatz' "hit (breaking)", tzak' "wrap". -/
def rootTV_res : Root :=
  { arity := .selectsTheme, changeType := .result }

/-- √ITV root: no theme, activity. Examples: way "sleep", ok' "cry".
    Same Root coordinates as √POS and √NOM — the distinction is
    categorical (verbal base) not arity/change. -/
def rootITV : Root :=
  { arity := .noTheme, changeType := .propertyConcept }

/-- √POS root: no theme, positional/stative. Examples: chot "sit",
    kot "on all fours", watz "lie face down". -/
def rootPOS : Root :=
  { arity := .noTheme, changeType := .propertyConcept }

/-- √NOM root: no theme, nominal base. Examples: a' "water",
    ixim "corn", chanhal "dance". -/
def rootNOM : Root :=
  { arity := .noTheme, changeType := .propertyConcept }

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

/-- -j does NOT assign a θ-role: agentless. -/
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

-- Core combinations from Coon (2019) §4–5:

/-- √TV result + Ø → causative [vDO, vGO, vBE] (active transitive). -/
theorem tv_res_active :
    isCausative (buildDecomposition vØ resultLower) = true := by native_decide

/-- √TV result + -ch → causative [vDO, vGO, vBE] (passive with implicit agent).
    Event structure is still causative — the agent is semantically present. -/
theorem tv_res_passive_ch :
    isCausative (buildDecomposition v_ch resultLower) = true := by native_decide

/-- √TV result + -j → inchoative [vGO, vBE] (agentless passive / anticausative).
    No agent at all — the event is a pure change-of-state. -/
theorem tv_res_agentless :
    isInchoative (buildDecomposition v_j resultLower) = true := by native_decide

/-- √ITV + Ø → activity [vDO] (unergative intransitive). -/
theorem itv_active :
    isActivity (buildDecomposition vØ activityLower) = true := by native_decide

/-- √POS + -w → [vDO, vBE]: agent assumes a position (agentive stative). -/
theorem pos_agentive :
    buildDecomposition v_w positionalLower = [.vDO, .vBE] := by native_decide

/-- √NOM + -w → activity [vDO] (denominal agentive intransitive). -/
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

/-- -ch always triggers -aj (implicit external agent). -/
theorem ch_triggers_aj : hasImplicitExternal v_ch = true := by native_decide

/-- Ø never has an implicit external (agent is overt ERG DP). -/
theorem vØ_no_implicit : hasImplicitExternal vØ = false := by native_decide

/-- -w never has an implicit external (agent is overt ABS DP). -/
theorem v_w_no_implicit : hasImplicitExternal v_w = false := by native_decide

/-- -j has no implicit external (there is no agent at all, not even implicit). -/
theorem v_j_no_implicit : hasImplicitExternal v_j = false := by native_decide

/-- -ch-aj: passive of √TV with implicit agent. -/
theorem ch_aj_passive :
    triggersAj v_ch false = true := by native_decide

/-- -w-aj: absolutive antipassive (√TV theme is implicit). -/
theorem w_aj_antipassive :
    triggersAj v_w true = true := by native_decide

/-- -w incorporation antipassive: theme is overt bare NP → no -aj. -/
theorem w_incorporation_no_aj :
    triggersAj v_w false = false := by native_decide

-- ============================================================================
-- § 7: Division of Labor Theorems
-- ============================================================================

/-- Division of labor (Coon 2019, core claim): the root determines whether
    a theme is present; Voice determines whether an agent is present.
    Same root with different Voice → different argument count. -/
theorem division_of_labor :
    -- Same result root: Ø gives causative, -j gives inchoative
    isCausative (buildDecomposition vØ resultLower) = true ∧
    isInchoative (buildDecomposition v_j resultLower) = true ∧
    -- Root's arity is invariant across voice alternations
    rootTV_res.arity = .selectsTheme ∧
    rootTV_res.arity = .selectsTheme := ⟨by native_decide, by native_decide, rfl, rfl⟩

/-- Theme persistence: a root's internal argument selection does not change
    under voice alternation. Whether the theme surfaces as a full DP, bare NP,
    or is existentially closed, the root still selects it. -/
theorem theme_persistence :
    rootTV_res.arity.hasInternalArg = true ∧
    rootTV_pc.arity.hasInternalArg = true ∧
    rootITV.arity.hasInternalArg = false ∧
    rootPOS.arity.hasInternalArg = false ∧
    rootNOM.arity.hasInternalArg = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The causative alternation in Chuj is determined by Voice, not by the root
    (generalization of `voice_determines_causativity_go_be` to Chuj heads).
    For result roots, causativity tracks exactly with θ-assignment. -/
theorem chuj_causative_alternation_result :
    isCausative (buildDecomposition vØ resultLower) = vØ.assignsTheta ∧
    isCausative (buildDecomposition v_w resultLower) = v_w.assignsTheta ∧
    isCausative (buildDecomposition v_ch resultLower) = v_ch.assignsTheta ∧
    isCausative (buildDecomposition v_j resultLower) = v_j.assignsTheta :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

end Fragments.Chuj
