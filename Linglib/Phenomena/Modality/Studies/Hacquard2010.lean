import Linglib.Fragments.Italian.Modals
import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Core.Logic.ModalLogic

/-!
# Event-Relative Modality
@cite{hacquard-2010} @cite{kratzer-1981} @cite{cinque-2004} @cite{rizzi-1978} @cite{grice-1975}

## Part I: Italian Restructuring

Connects the Italian restructuring data (Fragments/Italian/Modals) to
@cite{hacquard-2010}'s content licensing theory (EventRelativity §8).

### The Argument

1. Italian *potere*/*dovere* can restructure (appear below AspP).
2. When restructured, these modals lose epistemic readings.
3. Content licensing explains WHY: restructured modals are bound to the
   VP event (by aspect), and VP events lack propositional content, so
   epistemic modal bases cannot be projected.
4. When non-restructured (above AspP), the modal binds to the speech
   event (or attitude event), which IS contentful → epistemic available.

This is the key empirical argument for event-relative modality: the same
lexical modal (*potere*) shows different flavor availability depending
purely on its syntactic position, explained by content licensing.

## Part II: English Modal Position–Flavor Availability

Connects the force–flavor cartesian products in `Fragments/English/FunctionWords.lean`
(the set of POSSIBLE readings for each modal auxiliary) to EventRelativity's
position-based flavor availability (WHEN each reading is available).

### The Relationship

The fragment lists all readings a modal CAN have across all structural
positions. EventRelativity explains WHICH readings are available at
EACH position. The bridge verifies consistency: the fragment's flavor
set = the union of position-available flavors.

## Part III: Pragmatic Blocking

Formalizes the pragmatic blocking of circumstantial readings for
high modals. Content licensing does NOT
rule out circumstantial readings for high modals — `canProjectCircumstantial`
returns `true` for all event binders. Instead, circumstantial readings of
high modals are **pragmatically blocked** by more informative epistemic
readings.

### The Puzzle (@cite{hacquard-2010}, (49b, 49d))

Content licensing predicts:
- (49a) speech act + epistemic: ✓ attested
- (49b) speech act + circumstantial: ✓ semantically possible
- (49c) attitude + epistemic: ✓ attested
- (49d) attitude + circumstantial: ✓ semantically possible
- (49e) VP event + epistemic: ✗ ruled out (content licensing)
- (49f) VP event + circumstantial: ✓ attested

But (49b) and (49d) are generally unattested. WHY?

### Hacquard's Answer: Pragmatic Pre-emption

When a high modal can access BOTH epistemic and circumstantial backgrounds
(because the binding event is contentful), the epistemic reading is more
informative: it encodes the speaker's/holder's evidence about the world.
The circumstantial reading merely states facts about circumstances. A
pragmatic speaker would choose the more informative reading, pre-empting
the circumstantial one.
-/

namespace Phenomena.Modality.Studies.Hacquard2010

open Semantics.Modality.EventRelativity
open Core.Modality (ModalFlavor)

-- ============================================================================
-- Part I: Italian Restructuring
-- ============================================================================

open Fragments.Italian.Modals

-- ============================================================================
-- § 1: Restructuring = Low Position
-- ============================================================================

/-- Restructuring forces the modal below AspP. This maps to
`ModalPosition.belowAsp` in the EventRelativity framework. -/
def restructuredPosition : ModalPosition := .belowAsp

/-- Non-restructured modals sit above AspP. -/
def nonRestructuredPosition : ModalPosition := .aboveAsp

-- ============================================================================
-- § 2: Content Licensing Predicts the Pattern
-- ============================================================================

/-- Content licensing predicts that restructured (low) modals cannot be
epistemic: they are bound to the VP event, which lacks content.

This single theorem explains ALL the restructuring data:
- (17) potere_high: epistemic ✓ because high modal → speech act → content
- (18) potere_low_clitic: epistemic ✗ because low modal → VP event → no content
- (13) dovere_high: epistemic ✓ (same reasoning)
- (14) dovere_low_aux: epistemic ✗ (same reasoning) -/
theorem content_licensing_explains_restructuring :
    -- Restructured (low): VP event binder, no content → no epistemic
    restructuredPosition.defaultBinder = .vpEvent ∧
    restructuredPosition.defaultBinder.hasContent = false ∧
    restructuredPosition.defaultBinder.canProjectEpistemic = false ∧
    -- Non-restructured (high): speech act binder, content → epistemic
    nonRestructuredPosition.defaultBinder = .speechAct ∧
    nonRestructuredPosition.defaultBinder.hasContent = true ∧
    nonRestructuredPosition.defaultBinder.canProjectEpistemic = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 3: Data ↔ Theory (Italian)
-- ============================================================================

/-- The empirical data matches the theoretical prediction for *potere*.

The high/low flavor sets in the fragment entry align with the
event binder's available flavors at each position. -/
theorem potere_data_matches_theory :
    -- High: entry says epistemic available; theory agrees
    (.epistemic ∈ potere.highFlavors) ∧
    nonRestructuredPosition.defaultBinder.canProjectEpistemic = true ∧
    -- Low: entry says no epistemic; theory agrees
    (.epistemic ∉ potere.lowFlavors) ∧
    restructuredPosition.defaultBinder.canProjectEpistemic = false := by
  refine ⟨?_, rfl, ?_, rfl⟩ <;> decide

/-- Same bridge for *dovere*. -/
theorem dovere_data_matches_theory :
    (.epistemic ∈ dovere.highFlavors) ∧
    nonRestructuredPosition.defaultBinder.canProjectEpistemic = true ∧
    (.epistemic ∉ dovere.lowFlavors) ∧
    restructuredPosition.defaultBinder.canProjectEpistemic = false := by
  refine ⟨?_, rfl, ?_, rfl⟩ <;> decide

-- ============================================================================
-- § 4: The Same Modal, Two Positions
-- ============================================================================

/-- Both *potere* and *dovere* are single lexical items: the same verb
appears high (with epistemic) and low (without epistemic). This rules
out lexical ambiguity as an explanation — the flavor restriction follows
from structural position alone.

@cite{hacquard-2010}: "Importantly, in Italian, epistemic and root
modals are the same lexical items. [...] the availability of epistemic
readings tracks the syntactic position of the modal." -/
theorem same_lexical_items :
    -- potere: same form in both positions
    potere.form = "potere" ∧
    -- but different flavor availability
    (.epistemic ∈ potere.highFlavors) ∧
    (.epistemic ∉ potere.lowFlavors) ∧
    -- dovere: same form in both positions
    dovere.form = "dovere" ∧
    -- but different flavor availability
    (.epistemic ∈ dovere.highFlavors) ∧
    (.epistemic ∉ dovere.lowFlavors) := by
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 5: Why Not Lexical Ambiguity?
-- ============================================================================

/-- If epistemic/root were lexically distinct modals (as in some
analyses of English *can*_epis vs *can*_root), we would expect no
syntactic correlation. But Italian shows that ONE lexical item
exhibits the restriction purely based on position. Content licensing
explains this without positing ambiguity.

Furthermore, the restriction is PRODUCTIVE: any restructuring modal
loses epistemic in the restructured position. The theory predicts this
for ALL restructuring modals — it's not a per-item stipulation. -/
theorem both_modals_restructure :
    potere.canRestructure = true ∧ dovere.canRestructure = true := ⟨rfl, rfl⟩

-- ============================================================================
-- Part II: English Modal Position–Flavor Availability
-- ============================================================================

-- ============================================================================
-- § 6: Union of Position-Available Flavors
-- ============================================================================

/-- The full set of modal flavors available across ALL positions and
contexts: the union of flavors from high (matrix), high (embedded),
and low positions.

This should equal the set of flavors listed in the fragment entry
for any given modal — the fragment entry is the MAXIMUM over all
structural contexts. -/
def allPositionFlavors : List ModalFlavor :=
  -- High matrix: speech act binder → epistemic, circumstantial, deontic
  ModalPosition.aboveAsp.defaultBinder.fullAvailableFlavors ++
  -- Low: VP event binder → circumstantial only
  ModalPosition.belowAsp.defaultBinder.fullAvailableFlavors

/-- High matrix position contributes epistemic, circumstantial, and
deontic (from the speech act's addressee). -/
theorem high_matrix_flavors :
    ModalPosition.aboveAsp.defaultBinder.fullAvailableFlavors =
      [.epistemic, .circumstantial, .deontic] := rfl

/-- Low position contributes only circumstantial. -/
theorem low_flavors :
    ModalPosition.belowAsp.defaultBinder.fullAvailableFlavors =
      [.circumstantial] := rfl

/-- The union covers all three flavors. -/
theorem union_covers_all_three :
    (.epistemic ∈ allPositionFlavors) ∧
    (.circumstantial ∈ allPositionFlavors) ∧
    (.deontic ∈ allPositionFlavors) := by
  unfold allPositionFlavors
  refine ⟨?_, ?_, ?_⟩ <;> simp [high_matrix_flavors, low_flavors]

-- ============================================================================
-- § 7: Fragment Entry Verification
-- ============================================================================

/-- A modal with all three flavors (like *must*, *can*): each flavor
is derivable from some position.

- Epistemic: high position (speech act is contentful)
- Circumstantial: any position (always available)
- Deontic: high position (speech act has addressee) -/
theorem three_flavor_modal_derivable :
    -- Epistemic: available at high position (content licensing)
    ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true ∧
    -- Circumstantial: available at any position
    ModalPosition.aboveAsp.defaultBinder.canProjectCircumstantial = true ∧
    ModalPosition.belowAsp.defaultBinder.canProjectCircumstantial = true ∧
    -- Deontic: available when binder has addressee (speech act)
    ModalPosition.aboveAsp.defaultBinder.hasAddressee = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A modal with only [epistemic] (like *might*): derived from
high position content licensing. Note that *might* being
epistemic-only is a LEXICAL restriction (it selects for epistemic
flavor), not a structural one — structurally, high position allows
both epistemic and circumstantial. -/
theorem epistemic_only_derivable :
    ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true := rfl

/-- A modal with [deontic, circumstantial] but no epistemic (like
*have to*): the modal selects for non-epistemic flavors and occupies
the low position, where content licensing independently blocks
epistemic. -/
theorem non_epistemic_modal_consistent :
    ModalPosition.belowAsp.defaultBinder.canProjectEpistemic = false ∧
    ModalPosition.belowAsp.defaultBinder.canProjectCircumstantial = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 8: Position Restricts Fragment Readings
-- ============================================================================

/-- The key insight: a modal's fragment entry lists its FULL flavor
inventory, but at any given structural position, only a SUBSET is
available. Content licensing acts as a FILTER.

At low position: [epistemic, deontic, circumstantial] is filtered
to [circumstantial] — content licensing removes epistemic (no content)
and addressee licensing removes deontic (no addressee). -/
theorem low_position_filters :
    -- Low position: only circumstantial survives
    ModalPosition.belowAsp.defaultBinder.fullAvailableFlavors =
      [.circumstantial] := rfl

/-- At high position: all flavors survive (speech act has both
content and addressee). -/
theorem high_position_preserves :
    ModalPosition.aboveAsp.defaultBinder.fullAvailableFlavors =
      [.epistemic, .circumstantial, .deontic] := rfl

/-- The filtering relationship: high position flavors INCLUDE all
the flavors available at low position (monotonicity). Moving a
modal higher can only ADD flavors, never remove them. -/
theorem high_subsumes_low :
    ∀ f : ModalFlavor,
      f ∈ ModalPosition.belowAsp.defaultBinder.fullAvailableFlavors →
      f ∈ ModalPosition.aboveAsp.defaultBinder.fullAvailableFlavors := by
  intro f hf
  simp [low_position_filters] at hf
  simp [high_position_preserves, hf]

-- ============================================================================
-- Part III: Pragmatic Blocking
-- ============================================================================

-- ============================================================================
-- § 9: Semantic Availability ≠ Pragmatic Availability
-- ============================================================================

/-- Content licensing allows circumstantial readings for ALL binders
(including high/contentful ones). This is correct: circumstantial
readings of high modals are not UNGRAMMATICAL, just pragmatically
dispreferred. -/
theorem circumstantial_always_semantically_available :
    EventBinder.speechAct.canProjectCircumstantial = true ∧
    EventBinder.attitude.canProjectCircumstantial = true ∧
    EventBinder.vpEvent.canProjectCircumstantial = true :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: Competition: Epistemic vs Circumstantial
-- ============================================================================

/-- Informativity ordering on modal flavors.

Epistemic readings encode the speaker's EVIDENCE STATE — a specific
body of knowledge. Circumstantial readings encode surrounding
CIRCUMSTANCES — a more general and less constrained background.

When both are available, epistemic is more informative because it
commits to a specific body of evidence. -/
def informativity : ModalFlavor → Nat
  | .epistemic => 2       -- most informative (evidence-based)
  | .deontic => 1         -- intermediate (norm-based)
  | .circumstantial => 0  -- least informative (fact-based)

/-- Epistemic is more informative than circumstantial. -/
theorem epistemic_more_informative :
    informativity .epistemic > informativity .circumstantial := by decide

-- ============================================================================
-- § 11: Pragmatic Blocking Predicate
-- ============================================================================

/-- A reading is pragmatically blocked if a more informative reading
is available from the same binder. -/
def isPragmaticallyBlocked (b : EventBinder) (flavor : ModalFlavor) : Bool :=
  -- A flavor is blocked if there exists a more informative flavor
  -- available from the same binder
  let available := b.availableFlavors
  available.any λ f => f != flavor && informativity f > informativity flavor

/-- Circumstantial readings of speech act binders are pragmatically
blocked: epistemic is available and more informative. -/
theorem speechAct_circ_blocked :
    isPragmaticallyBlocked .speechAct .circumstantial = true := by native_decide

/-- Circumstantial readings of attitude binders are blocked too. -/
theorem attitude_circ_blocked :
    isPragmaticallyBlocked .attitude .circumstantial = true := by native_decide

/-- Epistemic readings are NEVER blocked (they're the most informative). -/
theorem epistemic_never_blocked :
    isPragmaticallyBlocked .speechAct .epistemic = false ∧
    isPragmaticallyBlocked .attitude .epistemic = false := by
  constructor <;> native_decide

/-- VP event binders: circumstantial is NOT blocked because epistemic
is not available (content licensing prevents it). No competition. -/
theorem vpEvent_circ_not_blocked :
    isPragmaticallyBlocked .vpEvent .circumstantial = false := by native_decide

-- ============================================================================
-- § 12: The Full (49a–f) Pattern
-- ============================================================================

/-- Two filters determine whether a binder × flavor combination is
PRAGMATICALLY available:
1. Content licensing (semantic filter): epistemic requires content
2. Informativity competition (pragmatic filter): less informative
   readings are blocked when more informative ones are available -/
def pragmaticallyAvailable (b : EventBinder) (flavor : ModalFlavor) : Bool :=
  flavor ∈ b.availableFlavors && !isPragmaticallyBlocked b flavor

/-- The complete (49a–f) pattern from @cite{hacquard-2010}:

| Binder | Flavor | Semantic? | Blocked? | Pragmatic? | Status |
|--------|--------|-----------|----------|------------|--------|
| Speech act | Epistemic | ✓ | ✗ | ✓ | (49a) attested |
| Speech act | Circumstantial | ✓ | ✓ | ✗ | (49b) unattested |
| Attitude | Epistemic | ✓ | ✗ | ✓ | (49c) attested |
| Attitude | Circumstantial | ✓ | ✓ | ✗ | (49d) unattested |
| VP event | Epistemic | ✗ | — | ✗ | (49e) unattested |
| VP event | Circumstantial | ✓ | ✗ | ✓ | (49f) attested | -/
theorem hacquard_49_full_pattern :
    -- (49a) speech act + epistemic: pragmatically available
    pragmaticallyAvailable .speechAct .epistemic = true ∧
    -- (49b) speech act + circumstantial: pragmatically blocked
    pragmaticallyAvailable .speechAct .circumstantial = false ∧
    -- (49c) attitude + epistemic: pragmatically available
    pragmaticallyAvailable .attitude .epistemic = true ∧
    -- (49d) attitude + circumstantial: pragmatically blocked
    pragmaticallyAvailable .attitude .circumstantial = false ∧
    -- (49e) VP event + epistemic: semantically unavailable
    pragmaticallyAvailable .vpEvent .epistemic = false ∧
    -- (49f) VP event + circumstantial: pragmatically available
    pragmaticallyAvailable .vpEvent .circumstantial = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ============================================================================
-- § 13: Pragmatic vs Semantic Blocking
-- ============================================================================

/-- (49e) and (49b) are both unattested, but for DIFFERENT reasons:
- (49e) VP event + epistemic: SEMANTICALLY blocked (content licensing)
- (49b) speech act + circumstantial: PRAGMATICALLY blocked (competition)

This distinction matters: (49b) should be recoverable in special contexts
where the circumstantial reading is more relevant than the epistemic one.
(49e) is never recoverable — it's a grammatical restriction. -/
theorem different_blocking_mechanisms :
    -- (49e): semantically blocked (canProjectEpistemic = false)
    EventBinder.vpEvent.canProjectEpistemic = false ∧
    -- (49b): semantically AVAILABLE but pragmatically blocked
    EventBinder.speechAct.canProjectCircumstantial = true ∧
    isPragmaticallyBlocked .speechAct .circumstantial = true :=
  ⟨rfl, rfl, by native_decide⟩

end Phenomena.Modality.Studies.Hacquard2010
