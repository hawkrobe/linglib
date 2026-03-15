import Linglib.Fragments.Italian.Modals
import Linglib.Theories.Semantics.Modality.EventRelativity

/-!
# Event-Relative Modality
@cite{hacquard-2010} @cite{kratzer-1981} @cite{cinque-1999} @cite{cinque-2004} @cite{rizzi-1978}

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

## Part II: Event Projection and Unattested Pairs

@cite{hacquard-2010}, §4.2: modals are keyed to (individual, time) pairs,
but not all combinations are attested. A modal must be keyed to the
participants and running time of the MOST LOCAL event. Event projection
(holder(e), τ(e)) derives the correct pair for each event binder,
explaining why certain pairs are systematically absent.
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
- potere_high: epistemic ✓ because high modal → speech act → content
- potere_low_clitic: epistemic ✗ because low modal → VP event → no content
- dovere_high: epistemic ✓ (same reasoning)
- dovere_low_aux: epistemic ✗ (same reasoning) -/
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

@cite{hacquard-2010}, §1: Italian *potere* and *dovere* express both
epistemic and root modality with the same lexical item, and the
availability of epistemic readings tracks the syntactic position. -/
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
-- Part II: Event Projection and Unattested Pairs
-- ============================================================================

-- ============================================================================
-- § 6: The Unattested Pairs Restriction
-- ============================================================================

/-! @cite{hacquard-2010}, §4.2: modals are keyed to (individual, time)
pairs, but not all combinations of individuals and times are attested.

| Individual | Time | Attested? | Example |
|-----------|------|-----------|---------|
| speaker | speech time | ✓ | epistemic *have to* |
| attitude holder | attitude time | ✓ | embedded epistemic |
| VP participant | VP time | ✓ | root *have to* |
| speaker | VP time | ✗ | — |
| VP participant | speech time | ✗ | — |

The missing diagonal pairs (speaker + VP time, subject + speech time)
are explained by event projection: each event binder projects a FIXED
(individual, time) pair. There is no event that pairs the speaker with
the VP time, or the subject with the speech time. -/

/-- The three event binders each project a specific (individual, time)
pair. This is why not all combinations are attested — pairs not
projected by any event are systematically absent.

@cite{hacquard-2010}, §4.2: "a modal seems to be relative to an
individual and a time, but not all time/individual pairs are attested.
Instead, the modal has to be keyed to the participants and running
time of the most local event." -/
theorem event_projection_constrains_pairs :
    -- Speech event → speaker-oriented, speech time
    ModalPosition.aboveAsp.defaultBinder = .speechAct ∧
    -- Attitude event → attitude holder, attitude time
    ModalPosition.aboveAsp.withAttitude = .attitude ∧
    -- VP event → VP participant, VP time
    ModalPosition.belowAsp.defaultBinder = .vpEvent :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Content Licensing Derives Position–Flavor Correlation
-- ============================================================================

/-- The paper's central claim: the position → flavor correlation
is DERIVED from content licensing, not stipulated.

High modals (above AspP) bind to contentful events → epistemic
available. Low modals (below AspP) bind by aspect to the VP event →
no content → no epistemic. This dissolves @cite{cinque-1999}'s puzzle
without dedicated functional heads for each modal flavor.

@cite{hacquard-2010}, §6.3: "high modals tend to be epistemic and
low modals circumstantial, without having to stipulate two separate
entries for each modal." -/
theorem position_flavor_derived_not_stipulated :
    -- Low: VP event is contentless → no epistemic (content licensing)
    ModalPosition.belowAsp.defaultBinder.hasContent = false ∧
    ModalPosition.belowAsp.defaultBinder.canProjectEpistemic = false ∧
    -- High: speech act is contentful → epistemic available
    ModalPosition.aboveAsp.defaultBinder.hasContent = true ∧
    ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true ∧
    -- Embedded high: attitude is contentful → epistemic still available
    ModalPosition.aboveAsp.withAttitude.hasContent = true ∧
    ModalPosition.aboveAsp.withAttitude.canProjectEpistemic = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Events Carry More Than (Individual, Time) Pairs
-- ============================================================================

/-- Events carry propositional content that (individual, time) pairs
do not. This is the key advantage of event-relative modality over
pair-relative modality: the content licensing predicate `hasContent`
discriminates events even when they project to similar pairs.

@cite{hacquard-2010}, §6: "what sets speech and attitude events
apart from ordinary events is (what I am calling) their associated
propositional 'content', which I take to be crucial for licensing
epistemic modal bases." -/
theorem events_richer_than_pairs :
    -- Content licensing discriminates event binders
    EventBinder.speechAct.hasContent = true ∧
    EventBinder.attitude.hasContent = true ∧
    EventBinder.vpEvent.hasContent = false ∧
    -- Yet speech acts and attitudes yield the SAME available flavors
    -- (both are contentful). Pairs would lose this shared structure.
    EventBinder.speechAct.availableFlavors =
      EventBinder.attitude.availableFlavors :=
  ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.Modality.Studies.Hacquard2010
