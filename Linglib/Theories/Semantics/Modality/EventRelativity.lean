import Linglib.Core.Semantics.Proposition
import Linglib.Core.Logic.ModalLogic

/-!
# Event-Relative Modality
  @cite{hacquard-2006} @cite{hacquard-2009} @cite{hacquard-2010} @cite{alonso-ovalle-royer-2024} @cite{kratzer-1981}Modal domains are projected from event arguments, not stipulated at the @cite{heim-1999}
clause level. An **anchoring function** maps events to conversational
backgrounds: the event type determines the modal flavor.

## Core Architecture

Kratzer's `ConvBackground` (`World → List (BProp World)`) gives the modal
base for a world. Hacquard adds a layer: modal bases are not
context-global but event-local. An anchoring function
`f : Ev → W → List (BProp W)` first selects the event, then produces a
Kratzer background.

## Content Licensing (§8–9)

The position → flavor correlation is DERIVED from a single predicate:
**content licensing**. Epistemic modal bases require
a contentful event — one with propositional content. Three event binders:

| Binder | Event | Content? | Epistemic? |
|--------|-------|----------|------------|
| ASSERT | speech act (e₀) | ✓ | ✓ |
| Attitude verb | attitude (e₁) | ✓ | ✓ |
| Aspect (IMPF/PRFV) | VP event (e₂) | ✗ | ✗ |

High modals (above AspP) are bound to contentful events → epistemic
available. Low modals (below AspP) are bound by aspect to the VP
event → circumstantial only. The binary `AnchorType` (§1) captures the
A-O&R application; `EventBinder` (§8) captures the full three-way
distinction needed for embedded contexts.

## Application: Modal Indefinites (§3–7)

Modal indefinites are existential quantifiers
carrying a modal component whose domain is projected from an event
argument via an anchoring function.

-/

namespace Semantics.Modality.EventRelativity

open Core.Proposition
open Core.ModalLogic (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Anchoring Functions
-- ════════════════════════════════════════════════════

/-- An anchoring function maps events to conversational backgrounds.

This is @cite{hacquard-2006}'s central innovation: modal bases are not
global context parameters but projected from event arguments.

The type `AnchoringFn Ev W = Ev → W → List (BProp W)` specializes
to Kratzer's `ConvBackground = World → List (BProp World)` when
applied to a specific event. -/
abbrev AnchoringFn (Ev W : Type*) := Ev → W → List (BProp W)

/-- An anchoring function applied to a specific event yields a
Kratzer-style conversational background. -/
def anchor {Ev W : Type*} (f : AnchoringFn Ev W) (e : Ev) : W → List (BProp W) :=
  f e

/-- The type of modal anchor: a binary coarsening of `EventBinder` (§8)
that collapses the contentful cases (speech act, attitude) into
`speechEvent` and the contentless case (VP event) into `describedEvent`.

This captures the matrix-clause application
where only two anchor types matter. For the full three-way distinction
needed for embedded contexts, use `EventBinder` directly.

@cite{hacquard-2006}: the speech event projects epistemic modality;
the described event projects circumstantial/root modality.
@cite{alonso-ovalle-royer-2024} refine circumstantial to include
random choice as a subtype. -/
inductive AnchorType where
  /-- Anchored to a contentful event (speech act or attitude) → epistemic available -/
  | speechEvent
  /-- Anchored to the VP event → circumstantial modal base -/
  | describedEvent
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Map anchor type to modal flavor.

Speech event anchoring yields epistemic modality; described event
anchoring yields circumstantial modality (which subsumes random
choice, teleological, ability, etc. per Kratzer 1981). -/
def AnchorType.toFlavor : AnchorType → ModalFlavor
  | .speechEvent => .epistemic
  | .describedEvent => .circumstantial

theorem speech_is_epistemic :
    AnchorType.speechEvent.toFlavor = .epistemic := rfl

theorem described_is_circumstantial :
    AnchorType.describedEvent.toFlavor = .circumstantial := rfl


-- ════════════════════════════════════════════════════
-- § 2. Event-Relative Modal Evaluation
-- ════════════════════════════════════════════════════

/-- Accessibility: world w' is accessible from w given anchoring
function f applied to event e.

NB: This omits Kratzer's ordering source g (cf. Hacquard 2010, (29):
`max_g(e)(∩f(e))`). The ordering source is orthogonal to the
content-licensing analysis and not needed for the MI application. -/
def accessible {Ev W : Type*} (f : AnchoringFn Ev W) (e : Ev)
    (allW : List W) (w : W) : List W :=
  allW.filter λ w' => (f e w).all λ p => p w'

/-- Existential modal: ◇_{f(e)} p at world w.
True iff some world accessible via f(e) satisfies p. -/
def possibility {Ev W : Type*} (f : AnchoringFn Ev W) (e : Ev)
    (allW : List W) (p : BProp W) (w : W) : Bool :=
  (accessible f e allW w).any p

/-- Universal modal: □_{f(e)} p at world w.
True iff all worlds accessible via f(e) satisfy p. -/
def necessity {Ev W : Type*} (f : AnchoringFn Ev W) (e : Ev)
    (allW : List W) (p : BProp W) (w : W) : Bool :=
  (accessible f e allW w).all p

/-- Duality: □_{f(e)} p ↔ ¬◇_{f(e)} ¬p. -/
private theorem list_all_not_any_not {W : Type*}
    (L : List W) (p : BProp W) :
    (L.all p == !L.any λ w => !p w) = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

theorem duality {Ev W : Type*} (f : AnchoringFn Ev W) (e : Ev)
    (allW : List W) (p : BProp W) (w : W) :
    (necessity f e allW p w == !possibility f e allW (λ w' => !p w') w) = true := by
  unfold necessity possibility
  exact list_all_not_any_not (accessible f e allW w) p


-- ════════════════════════════════════════════════════
-- §§ 3–7. Modal Indefinites (extracted to ModalIndefinites.lean)
-- ════════════════════════════════════════════════════

/-! The modal indefinite denotation (A-O&R 2024), upper-boundedness,
non-maximality, and harmonic interpretation types have been extracted to
`Theories/Semantics/Modality/ModalIndefinites.lean`. That file imports
this one for `AnchoringFn` and `possibility`. -/


-- ════════════════════════════════════════════════════
-- § 8. Event Binders and Content Licensing
--      (Hacquard 2010, §5–6)
-- ════════════════════════════════════════════════════

/-! @cite{hacquard-2010} identifies THREE event binders that can supply a
modal's event argument. The closest c-commanding binder determines
which event the modal is relative to:

- e₀: the speech act event (bound by ASSERT / illocutionary force)
- e₁: an attitude event (bound by attitude verbs: *believe*, *want*,...)
- e₂: the VP event (bound by aspect: IMPF/PRFV)

The binary `AnchorType` (§1) omits e₁ (irrelevant in A-O&R's
matrix-clause data), keeping only the speech event (e₀) / VP event (e₂)
distinction. `EventBinder` adds e₁, which matters because attitude
events are **contentful** (like speech events), not contentless (like
VP events).

The key insight: epistemic modal bases require a
contentful event — one with propositional content CON(e). Speech acts
and attitudes have content; VP events (running, screaming) do not.
This single predicate derives the position → flavor correlation. -/

/-- The three event binders (Hacquard 2010, (38), (48)). -/
inductive EventBinder where
  /-- e₀: the utterance event (bound by ASSERT) -/
  | speechAct
  /-- e₁: an attitude verb's event (believe, want, think,...) -/
  | attitude
  /-- e₂: the VP's described event (bound by aspect) -/
  | vpEvent
  deriving DecidableEq, BEq, Repr

/-- Whether an event has propositional content.

⟦f_epis(e)⟧ = {w' : w' compatible with CON(e)} — but CON(e) is
only defined for events with propositional content. Speech acts
carry assertive content; attitudes carry doxastic/bouletic content;
VP events (running, screaming, swimming) carry none. -/
def EventBinder.hasContent : EventBinder → Bool
  | .speechAct => true
  | .attitude  => true
  | .vpEvent   => false

/-- Epistemic modal bases require contentful events. -/
def EventBinder.canProjectEpistemic (b : EventBinder) : Bool :=
  b.hasContent

/-- Circumstantial modal bases need only the event's surrounding
circumstances — available for any event type. -/
def EventBinder.canProjectCircumstantial (_ : EventBinder) : Bool :=
  true

/-- Whether an event has an addressee with a to-do list.

Deontic accessibility relations (Hacquard 2006, (235c)) require the
binding event to have an addressee: `f_deontic(e) = λw. {w' : w'
compatible with TO-DO-LIST(ADDR(e))}`. Speech acts are directed at
an addressee; VP events are not.

NB: Whether an attitude event has an addressee depends on the verb:
*order*, *tell*, *permit* do; *think*, *believe* do not. This field
captures the default case (non-directive attitude). -/
def EventBinder.hasAddressee : EventBinder → Bool
  | .speechAct => true
  | .attitude  => false
  | .vpEvent   => false

/-- Available modal flavors DERIVED from content licensing.

Contentful events (speech acts, attitudes): epistemic + circumstantial.
Contentless events (VP events): circumstantial only.

NB: This captures the epistemic/non-epistemic divide from content
licensing but omits deontic. Deontic licensing
depends on a separate predicate — addressee availability (Hacquard
2006, (235c)) — not on content. See `hasAddressee` and
`fullAvailableFlavors` for the complete picture. -/
def EventBinder.availableFlavors (b : EventBinder) : List ModalFlavor :=
  if b.hasContent then [.epistemic, .circumstantial]
  else [.circumstantial]

/-- Full available flavors including deontic (Hacquard 2006, (235)).

Three accessibility relation types, each with different licensing:
- **Epistemic** `f_epis(e)`: worlds compatible with CON(e). Requires content.
- **Circumstantial** `f_circ(e)`: worlds compatible with CIRC(e). Any event.
- **Deontic** `f_deontic(e)`: worlds compatible with TO-DO-LIST(ADDR(e)).
  Requires an addressee.

This extends `availableFlavors` with the deontic dimension. -/
def EventBinder.fullAvailableFlavors (b : EventBinder) : List ModalFlavor :=
  let base := b.availableFlavors
  if b.hasAddressee then base ++ [.deontic] else base

-- Content licensing theorems

theorem speechAct_has_content : EventBinder.speechAct.hasContent = true := rfl
theorem attitude_has_content : EventBinder.attitude.hasContent = true := rfl
theorem vpEvent_lacks_content : EventBinder.vpEvent.hasContent = false := rfl

/-- Content licensing: epistemic availability ↔ content. -/
theorem epistemic_iff_content (b : EventBinder) :
    b.canProjectEpistemic = b.hasContent := rfl

-- Addressee licensing theorems

theorem speechAct_has_addressee : EventBinder.speechAct.hasAddressee = true := rfl
theorem vpEvent_no_addressee : EventBinder.vpEvent.hasAddressee = false := rfl

/-- Speech acts license all three accessibility types (Hacquard 2006, (235)):
epistemic (content), circumstantial (circumstances), and deontic (addressee). -/
theorem speechAct_full_flavors :
    EventBinder.speechAct.fullAvailableFlavors =
      [.epistemic, .circumstantial, .deontic] := rfl

/-- VP events license only circumstantial: no content (→ no epistemic),
no addressee (→ no deontic). -/
theorem vpEvent_full_flavors :
    EventBinder.vpEvent.fullAvailableFlavors = [.circumstantial] := rfl

/-- The three licensing conditions (Hacquard 2006, (235)):
- Epistemic needs content (CON(e))
- Circumstantial needs nothing (CIRC(e) is always available)
- Deontic needs an addressee (TO-DO-LIST(ADDR(e))) -/
theorem three_accessibility_types :
    -- Epistemic: content-licensed
    EventBinder.speechAct.canProjectEpistemic = true ∧
    EventBinder.vpEvent.canProjectEpistemic = false ∧
    -- Circumstantial: always available
    EventBinder.speechAct.canProjectCircumstantial = true ∧
    EventBinder.vpEvent.canProjectCircumstantial = true ∧
    -- Deontic: addressee-licensed
    EventBinder.speechAct.hasAddressee = true ∧
    EventBinder.vpEvent.hasAddressee = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- High modals (bound to speech act or attitude event) can be epistemic. -/
theorem high_modal_epistemic :
    EventBinder.speechAct.canProjectEpistemic = true ∧
    EventBinder.attitude.canProjectEpistemic = true := ⟨rfl, rfl⟩

/-- Low modals (bound to VP event by aspect) cannot be epistemic.
This is the core prediction: Italian restructuring forces modals low
(below Asp), blocking epistemic readings. -/
theorem low_modal_not_epistemic :
    EventBinder.vpEvent.canProjectEpistemic = false := rfl

/-- Contentful events yield both flavors; contentless events yield
only circumstantial. Derives the pattern in @cite{hacquard-2010}'s (49a–f). -/
theorem content_determines_flavors :
    EventBinder.speechAct.availableFlavors = [.epistemic, .circumstantial] ∧
    EventBinder.attitude.availableFlavors = [.epistemic, .circumstantial] ∧
    EventBinder.vpEvent.availableFlavors = [.circumstantial] := ⟨rfl, rfl, rfl⟩

/-- Attitude verbs pattern with speech acts, not VP events — both are
contentful. "John believes Mary might be pregnant" (Hacquard 2010,
(48b)): the embedded epistemic *might* is bound to the attitude event
e₁ of *believe*, which has content, licensing epistemic. -/
theorem attitudes_pattern_with_speech :
    EventBinder.attitude.availableFlavors =
    EventBinder.speechAct.availableFlavors := rfl

/-- VP events differ from both contentful event types. The three-way
distinction is invisible to the binary AnchorType but crucial for
embedded contexts (attitude verbs license epistemic; VP events do not). -/
theorem vpEvent_differs_from_contentful :
    EventBinder.vpEvent.availableFlavors ≠
      EventBinder.speechAct.availableFlavors ∧
    EventBinder.vpEvent.availableFlavors ≠
      EventBinder.attitude.availableFlavors := by
  constructor <;> decide

/-- Map the binary anchor type to the corresponding event binder.
`speechEvent` → `speechAct` (matrix clause default).
`describedEvent` → `vpEvent` (VP event bound by aspect). -/
def AnchorType.toEventBinder : AnchorType → EventBinder
  | .speechEvent => .speechAct
  | .describedEvent => .vpEvent

/-- Project an event binder to the binary anchor type.

This collapses the three-way `EventBinder` to the two-way `AnchorType`
by grouping contentful events (speech act, attitude) together as
`speechEvent` and contentless events (VP) as `describedEvent`.

The grouping is principled: it follows `hasContent`. Contentful binders
project to `speechEvent`; contentless to `describedEvent`. -/
def EventBinder.toAnchorType : EventBinder → AnchorType
  | .speechAct => .speechEvent
  | .attitude  => .speechEvent   -- attitude is contentful → groups with speech act
  | .vpEvent   => .describedEvent

/-- The projection groups by contentfulness: all contentful binders map
to `speechEvent`, the contentless binder maps to `describedEvent`. -/
theorem toAnchorType_groups_by_content :
    ∀ b : EventBinder,
      (b.toAnchorType == .speechEvent) = b.hasContent := by
  intro b; cases b <;> rfl

/-- `toEventBinder` is a section of `toAnchorType`: round-tripping
through EventBinder and back recovers the original AnchorType. -/
theorem toEventBinder_section :
    ∀ a : AnchorType, a.toEventBinder.toAnchorType = a := by
  intro a; cases a <;> rfl

/-- `AnchorType.toFlavor` is derivable from content licensing: the
primary flavor for each anchor type is the head of the corresponding
event binder's available flavor list. This replaces a stipulation
with a derivation through `hasContent`. -/
theorem toFlavor_derived :
    ∀ a : AnchorType,
      a.toEventBinder.availableFlavors.head? = some a.toFlavor := by
  intro a; cases a <;> rfl

/-- `AnchorType.toFlavor` is also derivable via `toAnchorType`: the
primary flavor of any binder's anchor type equals the head of that
binder's available flavors (for binders that have a primary flavor). -/
theorem toFlavor_via_projection :
    ∀ b : EventBinder, b.hasContent = true →
      b.toAnchorType.toFlavor = .epistemic := by
  intro b hb; cases b <;> simp_all [EventBinder.hasContent, EventBinder.toAnchorType, AnchorType.toFlavor]

/-- The six binder × flavor combinations (Hacquard 2010, (49a–f)).
Content licensing explains (49e): VP events lack content → no epistemic.
The remaining unattested combinations (49b: speech act + circumstantial,
49d: attitude + circumstantial) are semantically possible but
pragmatically blocked — circumstantial readings of high modals are
pre-empted by the more informative epistemic reading. -/
theorem unattested_49e_explained :
    -- (49e) VP event + epistemic: ruled out by content licensing
    EventBinder.vpEvent.canProjectEpistemic = false ∧
    -- (49a) speech act + epistemic: attested ✓
    EventBinder.speechAct.canProjectEpistemic = true ∧
    -- (49c) attitude + epistemic: attested ✓
    EventBinder.attitude.canProjectEpistemic = true ∧
    -- (49f) VP event + circumstantial: attested ✓
    EventBinder.vpEvent.canProjectCircumstantial = true ∧
    -- (49b, 49d) high + circumstantial: semantically possible,
    -- pragmatically blocked (not ruled out by content licensing)
    EventBinder.speechAct.canProjectCircumstantial = true ∧
    EventBinder.attitude.canProjectCircumstantial = true := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 9. Syntactic Position and Event Binding
--      (Hacquard 2010, §5.3)
-- ════════════════════════════════════════════════════

/-! Syntactic position determines which event binder is closest to the
modal. Aspect (IMPF/PRFV) existentially quantifies over VP events and
binds the event variable of any modal in its scope. A modal ABOVE
AspP is bound by the speech act or attitude event (whichever is
closest); a modal BELOW AspP is bound by aspect's event quantifier.

The full clausal ordering derived in Hacquard (2006, (255), p.160):

    Mod_epis > T > CF > Asp > Mod_circ

Epistemic modals are above Tense and counterfactual morphology;
circumstantial/root modals are below Aspect. Our `ModalPosition`
captures the binary above/below Asp distinction, which is sufficient
for content licensing and actuality entailments. The finer-grained
ordering relative to T and CF would require syntactic tree structure.

This connects the clause structure formalized in
`Theories/Syntax/Minimalism/Core/Voice.lean` and the aspect operators
in `Theories/Semantics/Lexical/Verb/ViewpointAspect.lean` to the
event-relative framework. -/

/-- Position of a modal relative to Aspect in the clause.
@cite{hacquard-2010}: this is the structural correlate of the
@cite{cinque-1999} high/low modal distinction. -/
inductive ModalPosition where
  /-- Above AspP: bound by ASSERT (matrix) or attitude verb (embedded) -/
  | aboveAsp
  /-- Below AspP: bound by aspect's event quantifier (∃e[...]) -/
  | belowAsp
  deriving DecidableEq, BEq, Repr

/-- Default event binder for a modal in each position.
High modals default to the speech act (matrix) or attitude event
(embedded — see `withAttitude`). Low modals are bound to the VP
event by aspect. -/
def ModalPosition.defaultBinder : ModalPosition → EventBinder
  | .aboveAsp => .speechAct
  | .belowAsp => .vpEvent

/-- In an embedded context under an attitude verb, a high modal's
event is bound by the attitude event rather than the speech act. -/
def ModalPosition.withAttitude : ModalPosition → EventBinder
  | .aboveAsp => .attitude
  | .belowAsp => .vpEvent

/-- High modals can be epistemic; low modals cannot.
DERIVED from defaultBinder + content licensing — not stipulated. -/
theorem position_determines_epistemic :
    ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true ∧
    ModalPosition.belowAsp.defaultBinder.canProjectEpistemic = false := ⟨rfl, rfl⟩

/-- Embedded high modals under attitude verbs can still be epistemic,
because attitude events are contentful. -/
theorem embedded_high_still_epistemic :
    ModalPosition.aboveAsp.withAttitude.canProjectEpistemic = true := rfl

/-- Low modals remain circumstantial-only even under attitude verbs:
aspect binds them to the VP event regardless of embedding. -/
theorem embedded_low_still_root :
    ModalPosition.belowAsp.withAttitude.canProjectEpistemic = false := rfl

/-- Full flavor availability by position and embedding context.
Matrix high: epistemic + circumstantial (speech act).
Embedded high: epistemic + circumstantial (attitude event).
Low (either context): circumstantial only (VP event). -/
theorem full_position_flavor_table :
    ModalPosition.aboveAsp.defaultBinder.availableFlavors
      = [.epistemic, .circumstantial] ∧
    ModalPosition.aboveAsp.withAttitude.availableFlavors
      = [.epistemic, .circumstantial] ∧
    ModalPosition.belowAsp.defaultBinder.availableFlavors
      = [.circumstantial] := ⟨rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 10. Kratzer Bridge
-- ════════════════════════════════════════════════════

/-! An anchoring function applied to a specific event yields a function
`W → List (BProp W)` — structurally identical to Kratzer's
`ConvBackground = World → List (BProp World)` (in
`Theories/Semantics/Modality/Kratzer.lean`).

    anchor f e : W → List (BProp W) ≡ ConvBackground

This is definitional: `anchor f e = f e`. Event-relative modality
IS Kratzer modality with the conversational background projected
from an event argument rather than stipulated as a context parameter.
No bridge theorem is needed — the types unify by construction. -/

/-- `anchor f e` reduces to the anchoring function applied to the event.
This makes explicit that the result is a conversational background
(world → set of propositions) in Kratzer's sense. -/
theorem anchor_reduces {Ev W : Type*}
    (f : AnchoringFn Ev W) (e : Ev) :
    anchor f e = f e := rfl

/-- Event-relative accessibility reduces to Kratzer-style accessibility:
filtering worlds by the propositions in the background projected
from event e. The implementation parallels `Kratzer.accessibleWorlds`
(which computes `allWorlds.filter (λ w' => (f w).all (· w'))`). -/
theorem accessible_is_background_filter {Ev W : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W) (w : W) :
    accessible f e allW w = allW.filter (λ w' => (f e w).all (· w')) := rfl


-- ════════════════════════════════════════════════════
-- § 10b. Event-Relative Ordering Source
--        (Hacquard 2010, (29): max_g(e)(∩f(e)))
-- ════════════════════════════════════════════════════

/-! The modal evaluation in §2 omits Kratzer's ordering source g. The
full @cite{hacquard-2010} semantics (29) is:

    ⟦modal⟧(p)(e)(w) = ∀/∃ w' ∈ max_{g(e)(w)}(∩f(e)(w)). p(w')

where `max_{g(e)(w)}` selects the BEST worlds among the accessible
worlds, ranked by the ordering source projected from event e.

An **event-relative ordering source** maps events to ordering functions,
parallel to how the anchoring function maps events to modal bases.
Different events can yield different orderings — e.g., a speech event
might project the speaker's normative standards, while a VP event
might project stereotypical ordering (inertia). -/

/-- An event-relative ordering source: maps events to world-orderings.
The ordering source determines how accessible worlds are ranked. Applied to event e and world w, it yields the
set of propositions characterizing the ideal (norms, stereotypes, goals). -/
abbrev OrderingFn (Ev W : Type*) := Ev → W → List (BProp W)

/-- The best worlds among the accessible set, ranked by the event-relative
ordering source. Combines the anchoring function (modal base) with the
ordering function to select the maximally ideal accessible worlds.

This implements Hacquard's (29): `max_{g(e)}(∩f(e))`. -/
def bestAccessible {Ev W : Type*} [DecidableEq W]
    (f : AnchoringFn Ev W) (g : OrderingFn Ev W) (e : Ev)
    (allW : List W) (w : W) : List W :=
  let acc := accessible f e allW w
  let ordering := g e w
  acc.filter λ w' =>
    acc.all λ w'' =>
      -- w' is at least as good as w'' iff w' satisfies all ordering
      -- propositions that w'' satisfies (Kratzer's ≤_A relation)
      (ordering.filter (· w'')).all (· w')

/-- Event-relative necessity with ordering source:
    □_{f(e),g(e)} p at world w = ∀w' ∈ Best(f(e),g(e),w). p(w'). -/
def orderedNecessity {Ev W : Type*} [DecidableEq W]
    (f : AnchoringFn Ev W) (g : OrderingFn Ev W) (e : Ev)
    (allW : List W) (p : BProp W) (w : W) : Bool :=
  (bestAccessible f g e allW w).all p

/-- Event-relative possibility with ordering source:
    ◇_{f(e),g(e)} p at world w = ∃w' ∈ Best(f(e),g(e),w). p(w'). -/
def orderedPossibility {Ev W : Type*} [DecidableEq W]
    (f : AnchoringFn Ev W) (g : OrderingFn Ev W) (e : Ev)
    (allW : List W) (p : BProp W) (w : W) : Bool :=
  (bestAccessible f g e allW w).any p

/-- Empty ordering source: all accessible worlds are best (no ranking).
Reduces to the unordered evaluation in §2. -/
theorem empty_ordering_reduces {Ev W : Type*} [DecidableEq W]
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (p : BProp W) (w : W) :
    orderedNecessity f (λ _ _ => []) e allW p w =
      necessity f e allW p w := by
  unfold orderedNecessity bestAccessible necessity accessible
  have : ∀ (l : List W), l.all (fun (_ : W) => true) = true := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => exact ih
  simp [this]


-- ════════════════════════════════════════════════════
-- § 11. Individual-Time Pairs from Events
--       (Hacquard 2006, §4.1, pp.131–136)
-- ════════════════════════════════════════════════════

/-! @cite{hacquard-2006} proposes that accessibility relations take
EVENT arguments (193): `R_f := λe.λw. w is compatible with f(e)`.
Events project to (individual, time) pairs via two functions:

- `holder(e)`: the thematic participant — Agent, Experiencer, or
  speaker — determined by the event's thematic structure.
- `τ(e)`: the temporal trace — the time of the event.

This makes individual-time pairs (the traditional modal parameter per
Kratzer 1981, von Fintel & Heim 1999) DERIVED from events, not
primitive. Three advantages:

1. **Unification**: The same mechanism (event projection) applies
   to all three event types, deriving the right individual and time.
2. **Additional structure**: Events carry propositional content (§8),
   aspectual structure (ActualityEntailments.lean), and thematic
   structure. Individual-time pairs carry none of this.
3. **No stipulated parameters**: The modal doesn't need to be
   specified for a particular individual or time. These are projected
   from whichever event binds the modal (200): the closest binder. -/

/-- An individual-time pair: the traditional modal parameter.

@cite{kratzer-1981} relativizes accessibility to circumstances at a world.
@cite{von-fintel-1999} relativize to an (individual, time). Hacquard
derives the pair from events, making it redundant as a primitive. -/
structure IndTimePair (Individual TimePoint : Type*) where
  individual : Individual
  time : TimePoint
  deriving DecidableEq, BEq, Repr

/-- Event projection: how events map to individuals and times.

`holder` extracts the thematic participant:
"the agent and temporal trace of the event quantified by Aspect."
For speech events: the speaker. For attitudes: the experiencer.
For VP events: the agent or experiencer.

`time` extracts the temporal trace τ:
the time at which the event occurs, hence the time at which the
accessibility relation is evaluated. -/
structure EventProjection (Ev Individual TimePoint : Type*) where
  holder : Ev → Individual
  time : Ev → TimePoint

/-- Derive the individual-time pair from an event.

This is the core of §4.1: individual-time pairs are not stipulated
but projected from events. `toPair proj e = (holder(e), τ(e))`. -/
def EventProjection.toPair {Ev Individual TimePoint : Type*}
    (proj : EventProjection Ev Individual TimePoint) (e : Ev) :
    IndTimePair Individual TimePoint where
  individual := proj.holder e
  time := proj.time e

/-- An anchoring function that factors through event projection.

If `g` is an accessibility relation parameterized by (individual, time),
then `factoredAnchoring proj g` is the event-relative version:
`f(e)(w) = g(holder(e), τ(e))(w)`.

This shows that event-relative anchoring SUBSUMES individual-time
anchoring: any (individual, time)-parameterized R can be recovered by
composing with event projection. -/
def factoredAnchoring {Ev W Individual TimePoint : Type*}
    (proj : EventProjection Ev Individual TimePoint)
    (g : Individual → TimePoint → W → List (BProp W)) : AnchoringFn Ev W :=
  λ e w => g (proj.holder e) (proj.time e) w

/-- Factored anchoring reduces to the (individual, time)-parameterized
function applied to the event's projected pair. -/
theorem factored_reduces {Ev W Individual TimePoint : Type*}
    (proj : EventProjection Ev Individual TimePoint)
    (g : Individual → TimePoint → W → List (BProp W)) (e : Ev) (w : W) :
    factoredAnchoring proj g e w = g (proj.holder e) (proj.time e) w := rfl


-- ════════════════════════════════════════════════════
-- § 12. Worked Example: "Jane a dû prendre le train"
--       (Hacquard 2006, (201), pp.135–136)
-- ════════════════════════════════════════════════════

/-! (201) "Jane a dû prendre le train."
     Jane must-PST-PFV take the train.
  a. Given MY evidence NOW, Jane must have taken the train. [epistemic]
  b. Given JANE'S circumstances THEN, Jane had to take the train. [root]

The sentence is ambiguous between an epistemic and a goal-oriented
reading. The two readings differ in the event that anchors the modal:

| Reading | Event | holder(e) | τ(e) | Modal domain |
|---------|-------|-----------|------|-------------|
| Epistemic | speech act e₀ | speaker | now | speaker's evidence NOW |
| Root | VP event e₂ | Jane | then | Jane's circumstances THEN |

The same modal *devoir* gets different parameters from different
event bindings. No lexical ambiguity is needed. -/

/-- Two individuals in the train scenario. -/
inductive TrainPerson where | speaker | jane
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Two time points: speech time and the past event time. -/
inductive TrainTime where | now | then
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Two events: the speech act and Jane's train-taking. -/
inductive TrainEvent where | speechAct | janesTaking
  deriving DecidableEq, BEq, Repr

/-- The event projection for the train scenario.

Speech act event: holder = speaker, τ = speech time (now).
VP event (Jane's taking): holder = Jane, τ = past time (then). -/
def trainProjection : EventProjection TrainEvent TrainPerson TrainTime where
  holder
    | .speechAct => .speaker
    | .janesTaking => .jane
  time
    | .speechAct => .now
    | .janesTaking => .then

/-- Speech event projects to (speaker, now). -/
theorem speech_projects_to_speaker_now :
    trainProjection.toPair .speechAct = ⟨.speaker, .now⟩ := rfl

/-- VP event projects to (Jane, then). -/
theorem vp_projects_to_jane_then :
    trainProjection.toPair .janesTaking = ⟨.jane, .then⟩ := rfl

/-- The same modal (*devoir*) gets different individual-time pairs
from different event bindings. This is (201): the epistemic reading
relativizes to the speaker's evidence NOW; the root reading relativizes
to Jane's circumstances THEN. -/
theorem same_modal_different_params :
    trainProjection.toPair .speechAct ≠
    trainProjection.toPair .janesTaking := by decide

/-- Two worlds: one where Jane took the train, one where she didn't. -/
inductive TrainWorld where | took | didnt
  deriving DecidableEq, BEq, Repr, Inhabited

private def allTW : List TrainWorld := [.took, .didnt]

/-- Epistemic anchoring (via speech event): the speaker considers both
worlds possible (no decisive evidence either way).
All (individual, time) combinations yield an empty background here
because we only evaluate this at the speech event's projection
(speaker, now), where the speaker has no decisive evidence. -/
private def epistemicBg : TrainPerson → TrainTime → TrainWorld →
    List (BProp TrainWorld) :=
  λ _ _ _ => []

/-- Root/goal-oriented anchoring (via VP event): given Jane's
circumstances at the past time, only the took-world is compatible
(she was in a situation where she had to take the train). -/
private def rootBg : TrainPerson → TrainTime → TrainWorld →
    List (BProp TrainWorld)
  | .jane, .then, _ => [λ w => w == .took]  -- only took-world accessible
  | _, _, _ => []

/-- The epistemic anchoring function (factored through projection). -/
private def fEpistemicTrain : AnchoringFn TrainEvent TrainWorld :=
  factoredAnchoring trainProjection epistemicBg

/-- The root anchoring function (factored through projection). -/
private def fRootTrain : AnchoringFn TrainEvent TrainWorld :=
  factoredAnchoring trainProjection rootBg

/-- Epistemic reading: modal anchored to speech event.
The speaker's evidence is compatible with Jane taking the train.
`◇_{f(e₀)} (took)` holds because the speaker considers `took` possible. -/
theorem epistemic_reading_possible :
    possibility fEpistemicTrain .speechAct allTW
      (· == .took) .took = true := by native_decide

/-- Root reading: modal anchored to VP event.
Given Jane's circumstances, she HAD to take the train.
`□_{f(e₂)} (took)` holds because only `took` is accessible. -/
theorem root_reading_necessary :
    necessity fRootTrain .janesTaking allTW
      (· == .took) .took = true := by native_decide

/-- The root anchoring via VP event restricts the accessible worlds
more than the epistemic anchoring via speech event. Both readings
use the SAME modal; the different accessible worlds come entirely
from the different event bindings → different (individual, time)
projections → different conversational backgrounds. -/
theorem root_restricts_more :
    -- Epistemic: both worlds accessible from speech event
    (accessible fEpistemicTrain .speechAct allTW .took).length = 2 ∧
    -- Root: only took-world accessible from VP event
    (accessible fRootTrain .janesTaking allTW .took).length = 1 := by
  constructor <;> native_decide


-- ════════════════════════════════════════════════════
-- § 13. Events Carry More Than Pairs
-- ════════════════════════════════════════════════════

/-! Individual-time pairs capture WHO and WHEN, but events additionally
carry WHETHER-CONTENT. This extra dimension is what content licensing
(§8) exploits: epistemic R requires CON(e), which is a property of
events (speech acts and attitudes have content; VP events don't), not
a property of (individual, time) pairs.

Two events can project to the SAME individual-time pair yet differ in
content licensing. For instance, imagine a speech event and an attitude
event where the speaker = the attitude holder and the times coincide.
Both project to (speaker, now), but they are different events with
(potentially) different content. The event level is strictly richer. -/

/-- Events carry content information (§8) that individual-time pairs
do not. This theorem shows that `hasContent` discriminates events
even though pairs cannot: speech acts and attitudes are both
contentful, VP events are not.

An (individual, time) pair has no `hasContent` field. If we collapsed
events to pairs, we would LOSE the ability to derive content licensing.
This is why events, not pairs, are the right primitive. -/
theorem events_richer_than_pairs :
    -- Content licensing discriminates event binders
    EventBinder.speechAct.hasContent = true ∧
    EventBinder.attitude.hasContent = true ∧
    EventBinder.vpEvent.hasContent = false ∧
    -- Yet speech acts and attitudes project to the SAME kind of holder
    -- (a sentient individual with propositional attitudes).
    -- Pairs would conflate them; events distinguish them.
    EventBinder.speechAct.availableFlavors =
      EventBinder.attitude.availableFlavors := ⟨rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 14. Worked Example: Embedded Epistemic
--       "Jane thinks Mary might be pregnant"
--       (Hacquard 2006, (247)–(249), pp.155–156)
-- ════════════════════════════════════════════════════

/-! (248c) "Jane thinks Mary might be pregnant."

*Might* is a high modal (above the embedded AspP) bound to the
attitude event e₁ of *think*. Since thinking is contentful —
CON(e₁) = Jane's beliefs — epistemic R is available. The modal
domain is Jane's belief worlds, not the speaker's.

This contrasts with the matrix case (§12): in "Mary might be
pregnant" (no embedding), *might* binds to the speech event e₀
and the modal domain is the speaker's evidence.

| Context | Binding event | CON(e) | Epistemic domain |
|---------|-------------|--------|-----------------|
| Matrix | e₀ (speech act) | speaker's evidence | what speaker considers possible |
| Embedded | e₁ (attitude) | Jane's beliefs | what Jane considers possible |

The embedded case demonstrates that attitude events, like speech
acts, are contentful (§8) — this is why `attitudes_pattern_with_speech`
holds. -/

/-- Two worlds for the pregnancy scenario. -/
inductive PregWorld where | pregnant | notPregnant
  deriving DecidableEq, BEq, Repr, Inhabited

private def allPW : List PregWorld := [.pregnant, .notPregnant]

/-- Two events: the matrix speech act and Jane's embedded thinking. -/
inductive BeliefEvent where | speech | thinking
  deriving DecidableEq, BEq, Repr

/-- Anchoring function for the belief scenario.
- Speech event: speaker has no decisive evidence (empty background →
  both worlds accessible).
- Thinking event: Jane believes Mary is pregnant (only the
  pregnant-world is compatible with Jane's beliefs). -/
private def fBelief : AnchoringFn BeliefEvent PregWorld
  | .speech, _ => []  -- speaker uncertain
  | .thinking, _ => [λ w => w == .pregnant]  -- Jane believes pregnant

/-- Embedded epistemic: *might* bound to Jane's thinking event.
Jane's beliefs restrict to the pregnant-world only. Under Jane's
beliefs, Mary's being pregnant is necessary (Jane is certain). -/
theorem embedded_epistemic_necessity :
    necessity fBelief .thinking allPW (· == .pregnant) .notPregnant = true := by
  native_decide

/-- Matrix epistemic: *might* bound to the speech event.
The speaker considers both worlds possible, so Mary's NOT being
pregnant is also possible. -/
theorem matrix_epistemic_both_possible :
    possibility fBelief .speech allPW (· == .pregnant) .notPregnant = true ∧
    possibility fBelief .speech allPW (· == .notPregnant) .notPregnant = true := by
  constructor <;> native_decide

/-- Same modal (*might*), different event bindings, different epistemic
domains. Under Jane's beliefs, only the pregnant-world is accessible.
Under the speaker's evidence, both worlds are accessible.

This demonstrates that attitude events are contentful (§8):
the thinking event provides CON(e₁) = Jane's beliefs, licensing
epistemic R for the embedded modal. -/
theorem embedded_vs_matrix_epistemic :
    -- Under attitude event: only pregnant-world accessible (Jane's beliefs)
    (accessible fBelief .thinking allPW .notPregnant).length = 1 ∧
    -- Under speech event: both worlds accessible (speaker's uncertainty)
    (accessible fBelief .speech allPW .notPregnant).length = 2 := by
  constructor <;> native_decide


end Semantics.Modality.EventRelativity
