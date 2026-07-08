import Linglib.Fragments.Mayan.Yukatek.VerbClasses
import Linglib.Semantics.Lexical.EventStructure
import Linglib.Syntax.Voice.Alternation

/-!
# Bohnemeyer 2004: Split intransitivity, linking, and lexical representation

[bohnemeyer-2004]

Split intransitivity in Yukatek Maya is governed by **event structure** —
specifically the distinction between internally- and externally-caused events
(in the sense of [levin-hovav-1995]) — rather than by lexical aspect
alone (contra [kraemer-wunderlich-1999]).

## Core Claims

1. **Three semantic information structures**: event structure, participant
   structure, and lexical aspect. Event structure partially determines both;
   linking rules operate on event structure directly.

2. **Internal causation determines the linking pattern under
   transitivization**: internally-caused bases get *applicative* linking
   (added applied object → U, original S stays A); externally-caused bases get
   *causative* linking (added instigator → A, original S → U). The overt
   transitivizing suffix (*-t* ~ *-s*) usually tracks the linking pattern but
   can dissociate from it — see below.

3. **Linking-by-viewpoint**: imperfective aspect aligns with the head of the
   causal chain (accusative default); perfective aligns with the tail
   (ergative default).

## Against aspect-based linking

[kraemer-wunderlich-1999] propose lexical aspect as the sole
linking-relevant property. Two classes of counterevidence:

- **Degree achievements** (grow, darken): aspectually like processes (atelic)
  but transitivize like state-change verbs (causative linking).
- **Non-internally-caused active verbs** (roll, buzz): take the *applicative*
  suffix *-t* (like internally-caused actives) yet show *causative* linking,
  because their bases are externally caused. Suffix and linking dissociate —
  which a purely aspect-based account cannot predict.
-/

namespace Bohnemeyer2004

open Semantics.Lexical.EventStructure (EventType InternalExternalCause Template)
open Semantics.Aspect (ViewpointAspectB)
open Mayan (MarkerSet)
open Yukatek

/-! ### Causal chain and thematic hierarchy -/

/-- Position in the causal chain of subevents.
    A complex event decomposes into subevents ordered in a causal chain.
    Thematic relations are projected from this chain. -/
inductive CausalChainPosition where
  | head  -- causing subevent (first in causal chain)
  | tail  -- caused subevent (last in causal chain)
  deriving DecidableEq, Repr

/-- Thematic hierarchy from causal-chain position (rule 31): the participant
    of a causing subevent (`head`) outranks the participant of the caused
    subevent (`tail`) for linking. -/
def Outranks : CausalChainPosition → CausalChainPosition → Prop
  | .head, .tail => True
  | _, _ => False

/-- The marker set the rule-31 hierarchy projects onto each causal-chain
    position: the highest-ranked position (`head`, the causer/A role) takes
    set-A; the outranked position (`tail`, the U role) takes set-B. -/
def CausalChainPosition.marker : CausalChainPosition → MarkerSet
  | .head => .setA
  | .tail => .setB

/-- The thematic hierarchy is asymmetric: no position both outranks and is
    outranked by the same position. -/
theorem outranks_asymm {a b : CausalChainPosition} (h : Outranks a b) :
    ¬ Outranks b a := by
  cases a <;> cases b <;> simp_all [Outranks]

/-- The marker assignment respects the hierarchy: an outranking position takes
    the subject marker (set-A) and the position it outranks takes the object
    marker (set-B). The split thus *follows from* rule (31) rather than being
    stipulated. -/
theorem marker_respects_outranks {a b : CausalChainPosition} (h : Outranks a b) :
    a.marker = .setA ∧ b.marker = .setB := by
  cases a <;> cases b <;> simp_all [Outranks, CausalChainPosition.marker]

/-! ### Linking by viewpoint -/

/-- §7 rule (32): viewpoint aspect selects which end of the causal chain
    provides the linking default.

    - Imperfective viewpoints align with the initial (causing) subevent →
      the highest-ranking role (`head`) is the default → accusative pattern.
    - Perfective viewpoints align with the final (caused) subevent or the
      chain as a whole → the lowest-ranking role (`tail`) is the default →
      ergative pattern. -/
def linkingDefault : ViewpointAspectB → CausalChainPosition
  | .imperfective => .head
  | .perfective => .tail

/-- The marker the sole argument (S) of an intransitive receives, derived by
    composing rule (32) (viewpoint → default position) with rule (31)'s
    hierarchy projection (position → marker, `CausalChainPosition.marker`).
    The split *falls out* of the causal chain rather than being stipulated
    per viewpoint.

    - Head default (imperfective): S patterns with A → set-A
    - Tail default (perfective): S patterns with U → set-B -/
def sMarkerFromViewpoint (v : ViewpointAspectB) : MarkerSet :=
  (linkingDefault v).marker

/-! ### Linking by viewpoint derives the split

The composed mechanism reproduces the Yukatek split recorded in the Fragment's
`sArgumentMarker`: perfective status → ergative (set-B), imperfective →
accusative (set-A). -/

theorem linking_derives_completive :
    some (sMarkerFromViewpoint .perfective) = sArgumentMarker .completive := rfl

theorem linking_derives_subjunctive :
    some (sMarkerFromViewpoint .perfective) = sArgumentMarker .subjunctive := rfl

theorem linking_derives_incompletive :
    some (sMarkerFromViewpoint .imperfective) = sArgumentMarker .incompletive := rfl

/-! ### Linking pattern under transitivization -/

/-- The argument-realization (linking) pattern produced by transitivization,
    determined by the causation type of the intransitive base (rules 26–27).
    This is the *linking* dimension — which participant is added and how the
    original S is realized — NOT the overt suffix (see `TransitivizerSuffix`).

    - `applicative`: internally caused. The added applied object links to U
      (set-B); the original S keeps A (set-A).
    - `causative`: externally caused. The added instigator links to A (set-A);
      the original S is demoted to U (set-B). -/
inductive LinkingPattern where
  | applicative
  | causative
  deriving DecidableEq, Repr

/-- The causation type of the intransitive base determines the linking pattern
    (rules 26–27): internally caused → applicative linking; externally caused
    → causative linking. -/
def predictLinking : InternalExternalCause → LinkingPattern
  | .internal => .applicative
  | .external => .causative

/-- Predict the linking pattern of a Yukatek verb under transitivization from
    its causation type. -/
def verbLinking (v : YukatekVerb) : LinkingPattern :=
  predictLinking v.causationType

/-- Marker assigned to the *added* participant under each linking pattern. -/
def LinkingPattern.addedArgMarker : LinkingPattern → MarkerSet
  | .applicative => .setB   -- added applied object → U
  | .causative => .setA     -- added instigator → A

/-- Marker assigned to the *original* S under each linking pattern. -/
def LinkingPattern.originalArgMarker : LinkingPattern → MarkerSet
  | .applicative => .setA   -- original S stays A
  | .causative => .setB     -- original S demoted to U

/-- Applicative and causative linking are mirror images: each assigns to the
    added argument the marker the other assigns to the original S. The two
    patterns exhaust how a transitivized clause distributes set-A and set-B. -/
theorem linking_patterns_swap_markers :
    LinkingPattern.applicative.addedArgMarker = LinkingPattern.causative.originalArgMarker ∧
    LinkingPattern.applicative.originalArgMarker = LinkingPattern.causative.addedArgMarker :=
  ⟨rfl, rfl⟩

/-! ### Transitivizing suffix vs linking

The overt transitivizing suffix is lexically specified and *usually* tracks
the linking pattern, but the two can dissociate — the paper's central argument
against aspect-based linking. The suffix is paper-specific lexical data, so it
lives here rather than in the Fragment. -/

/-- The overt transitivizing suffix ([bohnemeyer-2004]): applicative *-t*
    or causative *-s*. Distinct from `LinkingPattern`. -/
inductive TransitivizerSuffix where
  | applicativeT   -- *-t*
  | causativeS     -- *-s*
  deriving DecidableEq, Repr

/-- The suffix each verb the paper documents takes under transitivization.
    Lexically idiosyncratic — not a function of causation type or stem class
    (cf. balak' vs péek, both active and externally caused, yet *-t* vs *-s*).
    Verbs the paper does not document return `none`. -/
def transitivizerSuffix (v : YukatekVerb) : Option TransitivizerSuffix :=
  match v.gloss with
  | "work" | "play" | "eat" | "roll" | "buzz" => some .applicativeT
  | "die" | "fall" | "move/wiggle" => some .causativeS
  | _ => none

/-- For an internally-caused base the suffix tracks the linking: applicative
    *-t* with applicative linking. -/
theorem meyah_suffix_tracks_linking :
    transitivizerSuffix meyah = some .applicativeT ∧
    verbLinking meyah = .applicative := by decide

/-- For an externally-caused inactive base the suffix tracks the linking:
    causative *-s* with causative linking. -/
theorem kim_suffix_tracks_linking :
    transitivizerSuffix kim = some .causativeS ∧
    verbLinking kim = .causative := by decide

/-- The paper's key argument against aspect-based linking: balak' "roll" and
    tsiirin "buzz" take the *applicative* suffix *-t* (like the internally-caused
    actives) yet show *causative* linking, because their bases are externally
    caused (ex. 10, 11, 22). Suffix and linking dissociate — a contrast a
    purely aspect-based account cannot predict. -/
theorem balak_tsiirin_suffix_linking_dissociate :
    (transitivizerSuffix balak = some .applicativeT ∧ verbLinking balak = .causative) ∧
    (transitivizerSuffix tsiirin = some .applicativeT ∧ verbLinking tsiirin = .causative) := by
  decide

/-- péek "move" is active and externally caused like balak', yet takes the
    *causative* suffix *-s* — the suffix is lexically idiosyncratic,
    dissociating from causation type and stem class in the opposite direction
    from balak'. -/
theorem peek_causative_suffix_active_external :
    transitivizerSuffix peek = some .causativeS ∧
    peek.stemClass = .active ∧
    peek.causationType = .external ∧
    verbLinking peek = .causative := by decide

/-! ### Predictions for individual verbs -/

-- Internally caused active verbs → applicative

/-- "work" (internally caused active) → applicative linking.
    ex. (4):
    Túun meyah ich u=kòol → 'He's working on his milpa'
    Túun meyah-t-ik u=kòol → 'He's making his milpa' -/
theorem meyah_applicative : verbLinking meyah = .applicative := rfl

/-- "play" (internally caused active) → applicative.
    ex. (5). -/
theorem baaxal_applicative : verbLinking baaxal = .applicative := rfl

-- Externally caused verbs → causative (regardless of stem class)

/-- "die" (inactive, externally caused) → causative.
    ex. (6):
    Túun kim-il Pedro → 'Pedro's dying'
    Juan=e' túun kim-s-ik Pedro → 'Juan is killing Pedro' -/
theorem kim_causative : verbLinking kim = .causative := rfl

/-- "fall" (inactive, externally caused) → causative.
    ex. (7). -/
theorem luub_causative : verbLinking luub = .causative := rfl

-- Non-internally-caused ACTIVE verbs → causative (not applicative linking!)
-- This is the critical evidence against aspect-based linking.

/-- "roll" (active class but externally caused) → causative linking.
    Despite being an active verb (same stem class as "work"), balak' shows
    causative linking because its base is not internally caused.
    ex. (10), (22): the original S is linked to U, and the added participant
    is the instigator linked to A. -/
theorem balak_causative : verbLinking balak = .causative := rfl

/-- "buzz" (active class but externally caused) → causative.
    ex. (11). -/
theorem tsiirin_causative : verbLinking tsiirin = .causative := rfl

-- Positional verbs → causative

/-- All positional verbs transitivize with causative linking, since they
    denote externally-caused state changes at the event-structure level.
    Control is a participant-structure property, not an event-structure one.
    ex. (25), §6. -/
theorem kulTal_causative : verbLinking kulTal = .causative := rfl
theorem waalTal_causative : verbLinking waalTal = .causative := rfl

/-! ### Degree achievements: event type vs aspect -/

/-- Degree achievements are event-structurally state changes, not processes,
    even though they behave atelically.

    §5: ka'n 'get tired' passes state-change diagnostics (resultative *-a'n*,
    universal quantifier *láah*) despite being atelic in the
    realization-under-cessation test. -/
theorem kaan_is_state_change :
    kaan.stemClass.eventType = .stateChange := rfl

theorem naak_is_state_change :
    naak.stemClass.eventType = .stateChange := rfl

/-- Degree achievements transitivize like state-change verbs (causative
    linking), not like process verbs.

    This is the first direct counterevidence against
    [kraemer-wunderlich-1999]'s aspect-based linking: rule (14) predicts
    applicative for degree achievements (since they are atelic, hence [-perf]
    bases), but they exclusively causativize. ex. (21). -/
theorem degree_achievements_causativize :
    verbLinking kaan = .causative ∧
    verbLinking naak = .causative := ⟨rfl, rfl⟩

/-! ### Causation is orthogonal to stem class -/

/-- Active verbs are processes regardless of causation type. -/
theorem active_is_process :
    VerbStemClass.eventType .active = .process := rfl

/-- All non-active intransitive classes are state changes. -/
theorem nonactive_are_state_changes :
    VerbStemClass.eventType .inactive = .stateChange ∧
    VerbStemClass.eventType .inchoative = .stateChange ∧
    VerbStemClass.eventType .positional = .stateChange := ⟨rfl, rfl, rfl⟩

/-- The process/state-change distinction is orthogonal to causation type for
    active verbs: both internally-caused (meyah) and externally-caused (balak')
    actives are processes, but they differ in linking.

    This is the core argument: linking under transitivization depends on
    causation type, not event type or aspect. -/
theorem causation_orthogonal_to_event_type :
    meyah.stemClass.eventType = balak.stemClass.eventType ∧
    verbLinking meyah ≠ verbLinking balak :=
  ⟨rfl, by decide⟩

/-- Conversely, verbs with the same causation type but different stem classes
    get the same linking — because it is causation, not class membership, that
    determines linking.

    kim (inactive) and balak (active) are both externally caused → both
    causativize. -/
theorem same_causation_same_linking :
    verbLinking kim = verbLinking balak := rfl

-- hàan "eat" — the key exception proving the rule

/-- hàan "eat" is inactive by stem class but internally caused.
    ex. (9): hàan takes applicative *-t* (not causative *-s*), exactly as
    predicted by internal causation.

    This directly refutes stem-class-based linking: if stem class determined
    transitivization, hàan (inactive) would causativize like kim "die".
    Instead, it applicativizes like meyah "work". -/
theorem haanEat_applicative_despite_inactive :
    haanEat.stemClass = .inactive ∧
    verbLinking haanEat = .applicative := ⟨rfl, rfl⟩

/-- hàan patterns with internally-caused active verbs, not with its own
    (inactive) stem class, for linking. -/
theorem haanEat_patterns_with_actives :
    verbLinking haanEat = verbLinking meyah := rfl

/-- hàan and kim are both inactive but get different linking because they
    differ in causation type. -/
theorem inactive_split_by_causation :
    haanEat.stemClass = kim.stemClass ∧
    verbLinking haanEat ≠ verbLinking kim :=
  ⟨rfl, by decide⟩

/-! ### Bridge to detransitivization

The three Yukatek detransitivizations are instances of the cross-linguistic
valency-alternation typology (`Syntax/Voice/Alternation.lean`).
That substrate keeps passive and anticausative distinct by the fate of the
initial A — passive *denucleativizes* it (retained in participant structure as
a possible oblique agent), anticausative *suppresses* it (removed entirely). -/

open Voice
  (ValencyAlternation antipassivization decausativization passivization)

/-- Detransitivization type in Yukatek, from rules (28)–(30).

    - Antipassive (rule 28): removes the caused event, retaining the causing
      process. Active intransitives inflect like antipassive stems.
    - Anticausative (rule 29): removes the causing event, retaining the caused
      state/change. Inactive intransitives inflect like anticausative stems.
    - Passive (rule 30): like anticausative but adds PROC_C and instigator to
      the caused event. -/
inductive DetransitivizationType where
  | antipassive   -- retain causing process, remove caused event
  | anticausative -- retain caused event, remove causing process
  | passive       -- retain caused event, add instigator
  deriving DecidableEq, Repr

/-- Map each Yukatek detransitivization to its cross-linguistic valency
    alternation: antipassive → antipassivization (P denucleativized, A → S),
    anticausative → decausativization (A suppressed, P → S), passive →
    passivization (A denucleativized but retained, P → S). -/
def DetransitivizationType.toAlternation : DetransitivizationType → ValencyAlternation
  | .antipassive => antipassivization
  | .anticausative => decausativization
  | .passive => passivization

/-- All three detransitivizations are valency-decreasing.
    ex. (12): p'eh "chip" → antipassive p'èeh, passive p'e'h-el,
    anticausative p'éeh-el. -/
theorem detransitivizations_decrease_valency :
    (DetransitivizationType.toAlternation .antipassive).isValencyDecreasing = true ∧
    (DetransitivizationType.toAlternation .anticausative).isValencyDecreasing = true ∧
    (DetransitivizationType.toAlternation .passive).isValencyDecreasing = true :=
  ⟨rfl, rfl, rfl⟩

/-- The fate of the initial A separates passive from anticausative — the
    distinction the coarser intransitivization typology collapses: passive
    denucleativizes A (kept in participant structure), anticausative suppresses
    it (removed). -/
theorem passive_anticausative_distinct_by_A_fate :
    (DetransitivizationType.toAlternation .passive).fateOfA = .denucleativized ∧
    (DetransitivizationType.toAlternation .anticausative).fateOfA = .suppressed :=
  ⟨rfl, rfl⟩

/-! ### Template-level detransitivization -/

/-- Detransitivization as a template-level operation. rules (28)–(30)
    decompose detransitivization in terms of which subevent is retained:

    - Antipassive: retain the causing process → accomplishment → activity
    - Anticausative: retain the caused change → accomplishment → achievement
    - Passive: like anticausative but adds PROC_C + instigator (same template
      output as anticausative, with additional participant structure) -/
def DetransitivizationType.templateResult : DetransitivizationType → Option Template
  | .antipassive => some .activity       -- retain PROC, remove CAUSE+CHANGE
  | .anticausative => some .achievement  -- remove PROC+CAUSE, retain CHANGE
  | .passive => some .achievement        -- retain CHANGE, add instigator

/-- Antipassive yields a process (activity); anticausative/passive yield a
    state change (achievement). This connects to the event type distinction
    that governs verb class membership. -/
theorem antipassive_yields_process :
    (DetransitivizationType.templateResult .antipassive).map Template.eventType
    = some .process := rfl

theorem anticausative_yields_stateChange :
    (DetransitivizationType.templateResult .anticausative).map Template.eventType
    = some .stateChange := rfl

/-- Anticausative template result matches `Template.intransitiveVariant` from
    `EventStructure.lean`: both yield achievement from accomplishment. -/
theorem anticausative_matches_intransitiveVariant :
    DetransitivizationType.templateResult .anticausative
    = Template.intransitiveVariant .accomplishment := rfl

/-! ### Additional verb predictions -/

/-- All externally-caused manner-of-motion verbs causativize, regardless of
    their active stem class. -/
theorem manner_of_motion_all_causative :
    verbLinking chiik = .causative ∧
    verbLinking haarax = .causative ∧
    verbLinking huuy = .causative ∧
    verbLinking mosoon = .causative ∧
    verbLinking pirik = .causative ∧
    verbLinking walak = .causative := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Additional positional verbs causativize (externally caused). -/
theorem additional_positionals_causative :
    verbLinking chilTal = .causative ∧
    verbLinking xolTal = .causative := ⟨rfl, rfl⟩

/-- Degree achievements in the inactive class causativize despite lacking
    discrete end states — additional evidence beyond ka'n and na'k. -/
theorem additional_degree_achievements_causative :
    verbLinking lab = .causative ∧
    verbLinking tiil = .causative ∧
    verbLinking tsuuk = .causative := ⟨rfl, rfl, rfl⟩

/-! ### Bridge to split ergativity -/

/-- The linking-by-viewpoint mechanism derives the same alignment as the
    `SplitErgativity` system parameterized by status category. -/
theorem linking_consistent_with_split :
    (yukatekSplit.alignment .completive = .ergative) ∧
    (yukatekSplit.alignment .incompletive = .accusative) := ⟨rfl, rfl⟩

/-- Yukatek's split is aspect-conditioned, like Hindi and Georgian. All three
    use perfective → ergative, imperfective → accusative (modulo
    language-specific factor types). -/
theorem aspect_conditioned_split_family :
    yukatekSplit.alignment .completive =
      Alignment.hindiSplit.alignment .perfective := rfl

end Bohnemeyer2004
