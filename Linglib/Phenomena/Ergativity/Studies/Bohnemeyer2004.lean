import Linglib.Fragments.Mayan.Yukatek.VerbClasses
import Linglib.Theories.Semantics.Lexical.Verb.EventStructure
import Linglib.Theories.Semantics.Lexical.Verb.EntailmentProfile
import Linglib.Theories.Semantics.Causation.MorphologicalCausation

/-!
# Bohnemeyer 2004: Split Intransitivity in Yukatek Maya

@cite{bohnemeyer-2004}

Split intransitivity in Yukatek Maya is governed by **event structure** —
specifically the distinction between internally- and externally-caused
events — rather than by lexical aspect alone (contra @cite{kraemer-wunderlich-1999}).

## Core Claims

1. **Three semantic information structures**: event structure, participant
   structure, and lexical aspect. Event structure partially determines both;
   linking rules operate on event structure directly.

2. **Internal causation determines transitivization type**: internally-caused
   bases → applicative *-t* (add applied object as U); externally-caused
   bases → causative *-s* (add instigator as A).

3. **Linking-by-viewpoint**: imperfective aspect aligns with the head of the
   causal chain (accusative default); perfective aligns with the tail
   (ergative default).

## Against Aspect-Based Linking

@cite{kraemer-wunderlich-1999} propose lexical aspect as the sole
linking-relevant property. Two classes of counterevidence:

- **Degree achievements** (grow, darken): aspectually like processes (atelic)
  but transitivize like state-change verbs (causative pattern).
- **Non-internally-caused active verbs** (roll, buzz): same stem class and
  aspect as internally-caused actives (work, play) but show causative
  linking under transitivization.
-/

namespace Phenomena.Ergativity.Studies.Bohnemeyer2004

open Semantics.Lexical.Verb.EventStructure (EventType CausationType Template)
open Semantics.Tense.Aspect.Core (ViewpointAspectB)
open Fragments.Mayan (MarkerSet)
open Fragments.Mayan.Yukatek

-- ════════════════════════════════════════════════════
-- § 1. Causal Chain and Thematic Hierarchy
-- ════════════════════════════════════════════════════

/-- Position in the causal chain of subevents.
    A complex event decomposes into subevents ordered in a causal chain.
    Thematic relations are projected from this chain. -/
inductive CausalChainPosition where
  | head  -- causing subevent (first in causal chain)
  | tail  -- caused subevent (last in causal chain)
  deriving DecidableEq, Repr

/-- Thematic hierarchy from causal chain position.
    rule (31): participant of a causing subevent
    outranks participant of the caused subevent. -/
def outranks : CausalChainPosition → CausalChainPosition → Bool
  | .head, .tail => true
  | _, _ => false

theorem head_outranks_tail : outranks .head .tail = true := rfl
theorem tail_does_not_outrank_head : outranks .tail .head = false := rfl

-- ════════════════════════════════════════════════════
-- § 2. Linking-by-Viewpoint
-- ════════════════════════════════════════════════════

/-- Which end of the causal chain provides the linking default.
    §7 rule (32):

    - Imperfective viewpoints align with the initial (causing) subevent →
      the highest-ranking role defines the default → accusative pattern.
    - Perfective viewpoints align with the final (caused) subevent or
      the chain as a whole → the lowest-ranking role defines the default →
      ergative pattern. -/
def linkingDefault : ViewpointAspectB → CausalChainPosition
  | .imperfective => .head
  | .perfective => .tail

/-- Under linking-by-viewpoint, which marker set does the sole argument
    (S) of an intransitive receive?

    - Head default (imperfective): S patterns with A → set-A
    - Tail default (perfective): S patterns with U → set-B -/
def sMarkerFromViewpoint : ViewpointAspectB → MarkerSet
  | .imperfective => .setA  -- accusative: S = A
  | .perfective => .setB    -- ergative: S = U

-- ════════════════════════════════════════════════════
-- § 3. Linking-by-Viewpoint Derives the Split
-- ════════════════════════════════════════════════════

/-- The linking-by-viewpoint mechanism derives the Yukatek split:
    perfective status → ergative (set-B), imperfective → accusative (set-A).
    This matches the observed pattern in the fragment. -/
theorem linking_derives_completive :
    some (sMarkerFromViewpoint .perfective) = sArgumentMarker .completive := rfl

theorem linking_derives_subjunctive :
    some (sMarkerFromViewpoint .perfective) = sArgumentMarker .subjunctive := rfl

theorem linking_derives_incompletive :
    some (sMarkerFromViewpoint .imperfective) = sArgumentMarker .incompletive := rfl

-- ════════════════════════════════════════════════════
-- § 4. Transitivization Type
-- ════════════════════════════════════════════════════

/-- Type of transitivization operation, determined by the causation type
    of the intransitive base (§6, rules 26–27). -/
inductive TransitivizationType where
  | applicative  -- internally caused: *-t*, add applied object linked to U
  | causative    -- externally caused: *-s*, add instigator linked to A
  deriving DecidableEq, Repr

/-- The causation type of the intransitive base determines which
    transitivization operation applies.

    rules (26)–(27):
    - Internally caused base (sing, walk, play): *-t* applicative, adding
      an applied object. The original S keeps its position.
    - Externally caused base (die, fall, roll): *-s* causative, adding
      an instigator as A. The original S is reassigned to U. -/
def predictTransitivization : CausationType → TransitivizationType
  | .internal => .applicative
  | .external => .causative

/-- Under applicative transitivization, the added participant is linked
    to U (set-B) and the original S keeps A (set-A). Under causative
    transitivization, the added instigator takes A (set-A) and the
    original S moves to U (set-B). -/
def TransitivizationType.addedArgMarker : TransitivizationType → MarkerSet
  | .applicative => .setB   -- added applied object → U → set-B
  | .causative => .setA     -- added instigator → A → set-A

def TransitivizationType.originalArgMarker : TransitivizationType → MarkerSet
  | .applicative => .setA   -- original S stays as A → set-A
  | .causative => .setB     -- original S demoted to U → set-B

-- ════════════════════════════════════════════════════
-- § 5. Predictions for Individual Verbs
-- ════════════════════════════════════════════════════

/-- Predict transitivization for a Yukatek verb from its causation type. -/
def verbTransitivization (v : YukatekVerb) : TransitivizationType :=
  predictTransitivization v.causationType

-- § 5a. Internally caused active verbs → applicative

/-- "work" (internally caused active) → applicative transitivization.
    ex. (4):
    Túun meyah ich u=kòol → 'He's working on his milpa'
    Túun meyah-t-ik u=kòol → 'He's making his milpa' -/
theorem meyah_applicative : verbTransitivization meyah = .applicative := rfl

/-- "play" (internally caused active) → applicative.
    ex. (5). -/
theorem baaxal_applicative : verbTransitivization baaxal = .applicative := rfl

-- § 5b. Externally caused verbs → causative (regardless of stem class)

/-- "die" (inactive, externally caused) → causative.
    ex. (6):
    Túun kim-il Pedro → 'Pedro's dying'
    Juan=e' túun kim-s-ik Pedro → 'Juan is killing Pedro' -/
theorem kim_causative : verbTransitivization kim = .causative := rfl

/-- "fall" (inactive, externally caused) → causative.
    ex. (7). -/
theorem luub_causative : verbTransitivization luub = .causative := rfl

-- § 5c. Non-internally-caused ACTIVE verbs → causative (not applicative!)
-- This is the critical evidence against aspect-based linking.

/-- "roll" (active class but externally caused) → causative transitivization.
    Despite being an active verb (same stem class as "work"), balak' shows
    causative linking because its base is not internally caused.
    ex. (10), (22): the original S is linked to U,
    and the added participant is the instigator linked to A. -/
theorem balak_causative : verbTransitivization balak = .causative := rfl

/-- "buzz" (active class but externally caused) → causative.
    ex. (11). -/
theorem tsiirin_causative : verbTransitivization tsiirin = .causative := rfl

-- § 5d. Positional verbs → causative

/-- All positional verbs transitivize with causative linking, since they
    denote externally-caused state changes at the event-structure level.
    Control is a participant-structure property, not an event-structure one.
    ex. (25), §6. -/
theorem kulTal_causative : verbTransitivization kulTal = .causative := rfl
theorem waalTal_causative : verbTransitivization waalTal = .causative := rfl

-- ════════════════════════════════════════════════════
-- § 6. Degree Achievements: Event Type vs Aspect
-- ════════════════════════════════════════════════════

/-- Degree achievements are event-structurally state changes, not processes,
    even though they behave atelically.

    §5: ka'n 'get tired' passes state-change
    diagnostics (resultative *-a'n*, universal quantifier *láah*) despite
    being atelic in the realization-under-cessation test. -/
theorem kaan_is_state_change :
    kaan.stemClass.eventType = .stateChange := rfl

theorem naak_is_state_change :
    naak.stemClass.eventType = .stateChange := rfl

/-- Degree achievements transitivize like state-change verbs (causative),
    not like process verbs.

    This is the first direct counterevidence against @cite{kraemer-wunderlich-1999}'s
    aspect-based linking: rule (14) predicts applicative for degree achievements
    (since they are [-perf] bases), but they exclusively causativize.
    ex. (21). -/
theorem degree_achievements_causativize :
    verbTransitivization kaan = .causative ∧
    verbTransitivization naak = .causative := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 7. The Crosscutting: Causation ⊥ Stem Class
-- ════════════════════════════════════════════════════

/-- Active verbs are processes regardless of causation type. -/
theorem active_is_process :
    VerbStemClass.eventType .active = .process := rfl

/-- All non-active intransitive classes are state changes. -/
theorem nonactive_are_state_changes :
    VerbStemClass.eventType .inactive = .stateChange ∧
    VerbStemClass.eventType .inchoative = .stateChange ∧
    VerbStemClass.eventType .positional = .stateChange := ⟨rfl, rfl, rfl⟩

/-- The process/state-change distinction is orthogonal to causation type
    for active verbs: both internally-caused (meyah) and externally-caused
    (balak') actives are processes, but they differ in transitivization.

    This is the core argument of: linking under
    transitivization depends on causation type, not event type or aspect. -/
theorem causation_orthogonal_to_event_type :
    meyah.stemClass.eventType = balak.stemClass.eventType ∧
    verbTransitivization meyah ≠ verbTransitivization balak := by
  exact ⟨rfl, by decide⟩

/-- Conversely, verbs with the same causation type but different stem
    classes get the same transitivization — because it is causation,
    not class membership, that determines linking.

    kim (inactive) and balak (active) are both externally caused →
    both causativize. -/
theorem same_causation_same_transitivization :
    verbTransitivization kim = verbTransitivization balak := rfl

-- § 7a. hàan "eat" — the key exception proving the rule

/-- hàan "eat" is inactive by stem class but internally caused.
    ex. (9): hàan takes applicative *-t* (not
    causative *-s*), exactly as predicted by internal causation.

    This directly refutes stem-class-based linking: if stem class
    determined transitivization, hàan (inactive) would causativize
    like kim "die". Instead, it applicativizes like meyah "work". -/
theorem haan_applicative_despite_inactive :
    haan.stemClass = .inactive ∧
    verbTransitivization haan = .applicative := ⟨rfl, rfl⟩

/-- hàan patterns with internally-caused active verbs, not with
    its own (inactive) stem class, for transitivization. -/
theorem haan_patterns_with_actives :
    verbTransitivization haan = verbTransitivization meyah := rfl

/-- hàan and kim are both inactive but get different transitivization
    because they differ in causation type. -/
theorem inactive_split_by_causation :
    haan.stemClass = kim.stemClass ∧
    verbTransitivization haan ≠ verbTransitivization kim := by
  exact ⟨rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Proto-Role Entailments
-- ════════════════════════════════════════════════════

open Semantics.Lexical.Verb.EntailmentProfile (EntailmentProfile)

/-- Internal causation corresponds to the Proto-Agent "causation"
    entailment in @cite{dowty-1991}'s framework: an internally-caused
    event has a participant who causes (instigates) the event.

    §2: internal causation is "closely correlated
    with the properties of control and agentivity." -/
def CausationType.impliesCausationEntailment : CausationType → Bool
  | .internal => true   -- instigator causes the event
  | .external => false  -- no instigator

/-- Internally caused verbs predict a Proto-Agent subject (has causation
    entailment); externally caused verbs predict a Proto-Patient subject
    (lacks causation entailment). This connects Bohnemeyer's event-structure
    analysis to Dowty's ASP. -/
theorem internal_implies_agent_causation :
    CausationType.impliesCausationEntailment .internal = true := rfl

theorem external_lacks_causation :
    CausationType.impliesCausationEntailment .external = false := rfl

-- ════════════════════════════════════════════════════
-- § 9. Bridge to Detransitivization
-- ════════════════════════════════════════════════════

open Semantics.Causation.MorphologicalCausation (IntransitivizationType)

/-- Detransitivization type in Yukatek, from
    rules (28)–(30).

    - Antipassive (rule 28): removes the caused event, retaining the
      causing process. Active intransitives inflect like antipassive stems.
    - Anticausative (rule 29): removes the causing event, retaining the
      caused state/change. Inactive intransitives inflect like anticausative
      stems.
    - Passive (rule 30): like anticausative but adds PROC_C and instigator
      to the caused event. -/
inductive DetransitivizationType where
  | antipassive   -- retain causing process, remove caused event
  | anticausative -- retain caused event, remove causing process
  | passive       -- retain caused event, add instigator
  deriving DecidableEq, Repr

/-- Map Yukatek detransitivization to the general intransitivization
    typology from `MorphologicalCausation.lean`. Anticausatives remove
    the external cause (monoeventive); antipassives retain it. -/
def DetransitivizationType.toGeneral : DetransitivizationType → IntransitivizationType
  | .anticausative => .anticausative
  | .antipassive => .unmarked  -- antipassive is not causative-alternation
  | .passive => .anticausative -- passive also removes the causing participant

/-- Active transitive stems detransitivize like antipassive; inactive
    transitive stems detransitivize like anticausative or passive.
    ex. (12): p'eh "chip" → antipassive p'èeh,
    passive p'e'h-el, anticausative p'éeh-el. -/
theorem antipassive_active_pattern :
    DetransitivizationType.toGeneral .antipassive = .unmarked := rfl

theorem anticausative_removes_cause :
    (DetransitivizationType.toGeneral .anticausative).isBieventive = false := rfl

-- ════════════════════════════════════════════════════
-- § 10. Template-Level Detransitivization
-- ════════════════════════════════════════════════════

/-- Detransitivization as a template-level operation.
    rules (28)–(30) decompose detransitivization
    in terms of which subevent is retained:

    - Antipassive: retain the causing process → accomplishment → activity
    - Anticausative: retain the caused change → accomplishment → achievement
    - Passive: like anticausative but adds PROC_C + instigator (same template
      output as anticausative, with additional participant structure) -/
def DetransitivizationType.templateResult : DetransitivizationType → Option Template
  | .antipassive => some .activity       -- retain PROC, remove CAUSE+CHANGE
  | .anticausative => some .achievement  -- remove PROC+CAUSE, retain CHANGE
  | .passive => some .achievement        -- retain CHANGE, add instigator

/-- Antipassive yields a process (activity); anticausative/passive yield
    a state change (achievement). This connects to the event type distinction
    that governs verb class membership. -/
theorem antipassive_yields_process :
    (DetransitivizationType.templateResult .antipassive).map Template.eventType
    = some .process := rfl

theorem anticausative_yields_stateChange :
    (DetransitivizationType.templateResult .anticausative).map Template.eventType
    = some .stateChange := rfl

/-- Anticausative template result matches `Template.intransitiveVariant`
    from `EventStructure.lean`: both yield achievement from accomplishment. -/
theorem anticausative_matches_intransitiveVariant :
    DetransitivizationType.templateResult .anticausative
    = Template.intransitiveVariant .accomplishment := rfl

-- ════════════════════════════════════════════════════
-- § 11. Additional Verb Predictions
-- ════════════════════════════════════════════════════

/-- All externally-caused manner-of-motion verbs causativize,
    regardless of their active stem class. -/
theorem manner_of_motion_all_causative :
    verbTransitivization chiik = .causative ∧
    verbTransitivization haarax = .causative ∧
    verbTransitivization huuy = .causative ∧
    verbTransitivization mosoon = .causative ∧
    verbTransitivization pirik = .causative ∧
    verbTransitivization walak = .causative := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Additional positional verbs causativize (externally caused). -/
theorem additional_positionals_causative :
    verbTransitivization chilTal = .causative ∧
    verbTransitivization xolTal = .causative := ⟨rfl, rfl⟩

/-- Degree achievements in the inactive class causativize despite
    lacking discrete end states — additional evidence beyond ka'n and na'k. -/
theorem additional_degree_achievements_causative :
    verbTransitivization lab = .causative ∧
    verbTransitivization tiil = .causative ∧
    verbTransitivization tsuuk = .causative := ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 12. Bridge to SplitErgativity
-- ════════════════════════════════════════════════════

/-- The linking-by-viewpoint mechanism derives the same alignment
    as the `SplitErgativity` system parameterized by status category. -/
theorem linking_consistent_with_split :
    (yukatekSplit.alignment .completive = .ergative) ∧
    (yukatekSplit.alignment .incompletive = .accusative) := ⟨rfl, rfl⟩

/-- Yukatek's split is aspect-conditioned, like Hindi and Georgian.
    All three use perfective → ergative, imperfective → accusative
    (modulo language-specific factor types). -/
theorem aspect_conditioned_split_family :
    yukatekSplit.alignment .completive =
      Core.hindiSplit.alignment .perfective := rfl

end Phenomena.Ergativity.Studies.Bohnemeyer2004
