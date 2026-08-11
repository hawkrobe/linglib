import Linglib.Semantics.Modality.Kratzer.Operators
import Linglib.Semantics.Modality.ModalTypes

/-!
# Event-Relative Modality
[hacquard-2006] [hacquard-2009] [hacquard-2010] [alonso-ovalle-royer-2024] [kratzer-1981]

Modal domains are projected from event arguments, not stipulated at the
clause level. An **anchoring function** maps events to conversational
backgrounds: the event type determines the modal flavor.

## Core Architecture

Kratzer's `ConvBackground W` (`W → List (W → Prop)`) gives the modal
base for a world. Hacquard adds a layer: modal bases are not
context-global but event-local. An anchoring function
`f : Event → ConvBackground W` first selects the event, then produces a
Kratzer background — the `Semantics/Modality/Kratzer` operators apply
to `f e` directly.

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

namespace Modality

open Modality.Kratzer


-- ════════════════════════════════════════════════════
-- § 1. Anchoring Functions
-- ════════════════════════════════════════════════════

/-- An anchoring function maps events to conversational backgrounds.

This is [hacquard-2006]'s central innovation: modal bases are not
global context parameters but projected from event arguments. Applied
to a specific event it is exactly a Kratzer `ConvBackground`, so the
`Semantics/Modality/Kratzer` operators apply to `f e` directly. -/
abbrev AnchoringFn (Event W : Type*) := Event → ConvBackground W

/-- The type of modal anchor: a binary coarsening of `EventBinder` (§8)
that collapses the contentful cases (speech act, attitude) into
`speechEvent` and the contentless case (VP event) into `describedEvent`.

This captures the matrix-clause application
where only two anchor types matter. For the full three-way distinction
needed for embedded contexts, use `EventBinder` directly.

[hacquard-2006]: the speech event projects epistemic modality;
the described event projects circumstantial/root modality.
[alonso-ovalle-royer-2024] refine circumstantial to include
random choice as a subtype. -/
inductive AnchorType where
  /-- Anchored to a contentful event (speech act or attitude) → epistemic available -/
  | speechEvent
  /-- Anchored to the VP event → circumstantial modal base -/
  | describedEvent
  deriving DecidableEq, Repr, Inhabited

/-- Map anchor type to modal flavor.

Speech event anchoring yields epistemic modality; described event
anchoring yields circumstantial modality (which subsumes random
choice, teleological, ability, etc. per [kratzer-1981]). -/
def AnchorType.toFlavor : AnchorType → ModalFlavor
  | .speechEvent => .epistemic
  | .describedEvent => .circumstantial

theorem speech_is_epistemic :
    AnchorType.speechEvent.toFlavor = .epistemic := rfl

theorem described_is_circumstantial :
    AnchorType.describedEvent.toFlavor = .circumstantial := rfl



-- ════════════════════════════════════════════════════
-- §§ 3–7. Modal Indefinites (live in the study file)
-- ════════════════════════════════════════════════════

/-! The modal indefinite denotation ([alonso-ovalle-royer-2024]), upper-boundedness,
non-maximality, and harmonic interpretation types live in
`Studies/AlonsoOvalleRoyer2024.lean`, which imports this file for
`AnchoringFn` and applies the `Semantics/Modality/Kratzer` operators to
the anchored backgrounds. -/


-- ════════════════════════════════════════════════════
-- § 8. Event Binders and Content Licensing
--      ([hacquard-2010], §5–6)
-- ════════════════════════════════════════════════════

/-! [hacquard-2010] identifies THREE event binders that can supply a
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

/-- The three event binders ([hacquard-2010], (38), (48)). -/
inductive EventBinder where
  /-- e₀: the utterance event (bound by ASSERT) -/
  | speechAct
  /-- e₁: an attitude verb's event (believe, want, think,...) -/
  | attitude
  /-- e₂: the VP's described event (bound by aspect) -/
  | vpEvent
  deriving DecidableEq, Repr


-- ════════════════════════════════════════════════════
-- § 8a. CON(e): Propositional Content of Events
--       ([hacquard-2010], (51))
-- ════════════════════════════════════════════════════

/-! [hacquard-2010] (51) recasts the epistemic modal base as a function
of propositional content:

    ∩f_epis(e) = {w' : w' is compatible with CON(e)}

`CON(e)` is the propositional content of event e — the set of
propositions that constitute the "information state" of the event.
For speech acts, CON(e₀) = the speaker's doxastic alternatives.
For attitudes, CON(e₁) = the attitude holder's doxastic alternatives.
For VP events, CON(e₂) is **undefined**: running, screaming, and
swimming carry no propositional content.

`ContentFn` makes CON(e) a first-class function. The epistemic modal
base is DERIVED from it, and `hasContent` (below) is derivable from
whether CON(e) is defined — not stipulated as a lookup table. -/

/-- CON(e): the propositional content of an event.

Returns `some bg` when the event carries propositional content
(speech acts, attitudes), where `bg` is the conversational
background (propositions accessible from each world).
Returns `none` when the event lacks content (VP events). -/
abbrev ContentFn (Event W : Type*) := Event → Option (ConvBackground W)

/-- Derive the epistemic modal base from event content.

[hacquard-2010], (51): ∩f_epis(e) = {w' : w' compatible with CON(e)}.
The epistemic base IS the content — this is identity, not a bridge. -/
def epistemicFromContent {Event W : Type*} (con : ContentFn Event W) (e : Event) :
    Option (ConvBackground W) :=
  con e

/-- Whether CON(e) is defined for a given event.
Derived from the content function, not stipulated. -/
def contentDefined {Event W : Type*} (con : ContentFn Event W) (e : Event) : Bool :=
  (con e).isSome

/-- Epistemic modal base available iff CON(e) is defined.
This is definitional — not a bridge theorem but an architectural fact. -/
theorem epistemic_available_iff_content_defined {Event W : Type*}
    (con : ContentFn Event W) (e : Event) :
    (epistemicFromContent con e).isSome = contentDefined con e := rfl

/-- Concrete CON for the three event binder types.

Speech acts: CON(e₀) provides the speaker's doxastic alternatives.
Attitudes: CON(e₁) provides the holder's doxastic alternatives.
VP events: CON(e₂) is undefined — no propositional content.

The actual propositions depend on the specific event instance;
`binderContent` captures only definedness (some vs none). -/
def binderContent {W : Type*} : EventBinder → Option (ConvBackground W)
  | .speechAct => some (λ _ => [])  -- defined (content depends on instance)
  | .attitude  => some (λ _ => [])  -- defined (content depends on instance)
  | .vpEvent   => none              -- undefined: VP events lack content

/-- Whether an event has propositional content.

⟦f_epis(e)⟧ = {w' : w' compatible with CON(e)} — but CON(e) is
only defined for events with propositional content. Speech acts
carry assertive content; attitudes carry doxastic/bouletic content;
VP events (running, screaming, swimming) carry none. -/
def EventBinder.hasContent : EventBinder → Bool
  | .speechAct => true
  | .attitude  => true
  | .vpEvent   => false

/-- `hasContent` is derivable from `binderContent`: a binder has
content iff `CON(e)` is defined (returns `some`). This shows that
the Boolean predicate is a consequence of the deeper structure,
not a stipulation. -/
theorem hasContent_from_contentFn (b : EventBinder) :
    b.hasContent = (binderContent (W := Unit) b).isSome := by
  cases b <;> rfl

/-- Epistemic modal bases require contentful events. -/
def EventBinder.canProjectEpistemic (b : EventBinder) : Bool :=
  b.hasContent

/-- Circumstantial modal bases need only the event's surrounding
circumstances — available for any event type. -/
def EventBinder.canProjectCircumstantial (_ : EventBinder) : Bool :=
  true

/-- Whether an event has an addressee with a to-do list.

Deontic accessibility relations ([hacquard-2006], (235c)) require the
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
depends on a separate predicate — addressee availability ([hacquard-2006], (235c)) — not on content. See `hasAddressee` and
`fullAvailableFlavors` for the complete picture. -/
def EventBinder.availableFlavors (b : EventBinder) : List ModalFlavor :=
  if b.hasContent then [.epistemic, .circumstantial]
  else [.circumstantial]

/-- Full available flavors including deontic ([hacquard-2006], (235)).

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

/-- Speech acts license all three accessibility types ([hacquard-2006], (235)):
epistemic (content), circumstantial (circumstances), and deontic (addressee). -/
theorem speechAct_full_flavors :
    EventBinder.speechAct.fullAvailableFlavors =
      [.epistemic, .circumstantial, .deontic] := rfl

/-- VP events license only circumstantial: no content (→ no epistemic),
no addressee (→ no deontic). -/
theorem vpEvent_full_flavors :
    EventBinder.vpEvent.fullAvailableFlavors = [.circumstantial] := rfl

/-- The three licensing conditions ([hacquard-2006], (235)):
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
only circumstantial. Derives the pattern in [hacquard-2010]'s (49a–f). -/
theorem content_determines_flavors :
    EventBinder.speechAct.availableFlavors = [.epistemic, .circumstantial] ∧
    EventBinder.attitude.availableFlavors = [.epistemic, .circumstantial] ∧
    EventBinder.vpEvent.availableFlavors = [.circumstantial] := ⟨rfl, rfl, rfl⟩

/-- Attitude verbs pattern with speech acts, not VP events — both are
contentful. "John believes Mary might be pregnant" ([hacquard-2010],
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

/-- The six binder × flavor combinations ([hacquard-2010], (49a–f)).
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
--      ([hacquard-2010], §5.3)
-- ════════════════════════════════════════════════════

/-! Syntactic position determines which event binder is closest to the
modal. Aspect (IMPF/PRFV) existentially quantifies over VP events and
binds the event variable of any modal in its scope. A modal ABOVE
AspP is bound by the speech act or attitude event (whichever is
closest); a modal BELOW AspP is bound by aspect's event quantifier.

The full clausal ordering derived in [hacquard-2006]): -- UNVERIFIED: p.160

    Mod_epis > T > CF > Asp > Mod_circ

Epistemic modals are above Tense and counterfactual morphology;
circumstantial/root modals are below Aspect. Our `ModalPosition`
captures the binary above/below Asp distinction, which is sufficient
for content licensing and actuality entailments. The finer-grained
ordering relative to T and CF would require syntactic tree structure.

This connects the clause structure formalized in
`Syntax/Minimalism/Voice.lean` and the viewpoint-aspect operators
in `Semantics/Aspect/Basic.lean` to the event-relative framework. -/

/-- Position of a modal relative to Aspect in the clause.
[hacquard-2010]: this is the structural correlate of the
[cinque-1999] high/low modal distinction. -/
inductive ModalPosition where
  /-- Above AspP: bound by ASSERT (matrix) or attitude verb (embedded) -/
  | aboveAsp
  /-- Below AspP: bound by aspect's event quantifier (∃e[...]) -/
  | belowAsp
  deriving DecidableEq, Repr

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
-- § 9a. Aspect as Event Binder
--       ([hacquard-2010], §5.3.1)
-- ════════════════════════════════════════════════════

/-! Aspect is the event binder for low modals. Perfective and
imperfective both existentially quantify over events:

    ⟦PRFV⟧ = λP.λt.∃e[τ(e) ⊆ t ∧ P(e)]
    ⟦IMPF⟧ = λP.λt.∃e[t ⊂ τ(e) ∧ P(e)]

This ∃e binds the free event variable in the modal's restriction,
anchoring it to the VP event. Both perfective and imperfective
bind to VP events — they differ in temporal containment, not in
which event they bind.

This makes aspect the structural MECHANISM behind
`ModalPosition.belowAsp.defaultBinder = .vpEvent`: it is aspect's
existential quantification that performs the binding. -/

/-- Aspect binds the modal to the VP event regardless of
viewpoint (perfective or imperfective). The two viewpoints differ
in temporal containment (τ(e) ⊆ t vs t ⊂ τ(e)) but both bind
the same event variable — the VP event. -/
inductive Perfectivity' where
  | perfective
  | imperfective
  deriving DecidableEq, Repr

/-- Aspect always binds the modal's event variable to the VP event.
This is WHY low modals have `defaultBinder = .vpEvent`: the
structural source of that binding is aspect's ∃e quantification. -/
def Perfectivity'.bindsTo : Perfectivity' → EventBinder
  | .perfective => .vpEvent
  | .imperfective => .vpEvent

theorem aspect_always_binds_vp (asp : Perfectivity') :
    asp.bindsTo = .vpEvent := by cases asp <;> rfl

/-- Aspect binding entails the low-modal flavor restriction:
since aspect binds to VP events, and VP events lack content,
aspect-bound modals cannot be epistemic. -/
theorem aspect_bound_no_epistemic (asp : Perfectivity') :
    asp.bindsTo.canProjectEpistemic = false := by cases asp <;> rfl


-- ════════════════════════════════════════════════════
-- § 10b. Event-Relative Ordering Source
--        ([hacquard-2010], (29): max_g(e)(∩f(e)))
-- ════════════════════════════════════════════════════

/-! The full [hacquard-2010] semantics (29) is

    ⟦modal⟧(p)(e)(w) = ∀/∃ w' ∈ max_{g(e)(w)}(∩f(e)(w)). p(w')

— Kratzer's ordered operators applied to the anchored base and
ordering: `Kratzer.necessity (f e) (g e)` and
`Kratzer.possibility (f e) (g e)`. The only event-relative ingredient
is the ordering source projected from the event. -/

/-- An event-relative ordering source: applied to an event it is a
Kratzer `OrderingSource`. -/
abbrev OrderingFn (Event W : Type*) := Event → OrderingSource W


-- ════════════════════════════════════════════════════
-- § 10c. Doxastic Accessibility as Event-Relative Modality
--        ([hacquard-2010], (41), (51)–(52))
-- ════════════════════════════════════════════════════

/-! [hacquard-2010] unifies attitude semantics with modal semantics:
the epistemic modal base under an attitude verb IS the content of the
attitude event. Hintikka-style doxastic quantification — `∀w' ∈ DOX(x,w). p(w')`
— is a special case of event-relative necessity where the anchoring
function encodes the agent's doxastic alternatives.

[hacquard-2010], (41):

    ⟦believe⟧ = λe. λp. λx. λw. Exp(e,x) & belief'(e,w) &
                ∀w'∈ ∩CON(e): p(w') = 1
      where ∩CON(e) = DOX(ιx Holder(x,e), w)

The bridge: given an agent-indexed accessibility relation `R` and a
holder function extracting the agent from an event, we construct an
anchoring function whose event-relative necessity IS Hintikka's □. -/

/-- Construct an anchoring function from a doxastic accessibility relation.

Given `R : E → W → W → Prop` (agent → eval world → accessible world)
and `holder : Event → E`, the anchoring function
`f(e)(w) = [R(holder(e), w, ·)]` — a singleton background whose sole
premise is doxastic accessibility from w.

This implements [hacquard-2010]'s insight that CON(e) for an
attitude event e IS the set of doxastic alternatives of holder(e). -/
def doxasticAnchoring {Event W E : Type*}
    (R : E → W → W → Prop)
    (holder : Event → E) : AnchoringFn Event W :=
  λ e w => [R (holder e) w]

/-- Necessity over a doxastic anchoring is Hintikka-style universal
quantification over the holder's doxastic alternatives — attitude
verbs and modals share the same quantificational structure
([hacquard-2010], §6.1.3). -/
theorem doxastic_necessity_eq {Event W E : Type*}
    (R : E → W → W → Prop)
    (holder : Event → E) (e : Event) (p : W → Prop) (w : W) :
    simpleNecessity (doxasticAnchoring R holder e) p w ↔
      ∀ w', R (holder e) w w' → p w' := by
  simp [simpleNecessity, ModalLogic.box, kratzerR, doxasticAnchoring]

/-- Possibility dually: some doxastic alternative of the holder
satisfies p. -/
theorem doxastic_possibility_eq {Event W E : Type*}
    (R : E → W → W → Prop)
    (holder : Event → E) (e : Event) (p : W → Prop) (w : W) :
    simplePossibility (doxasticAnchoring R holder e) p w ↔
      ∃ w', R (holder e) w w' ∧ p w' := by
  simp [simplePossibility, ModalLogic.diamond, kratzerR, doxasticAnchoring]


-- ════════════════════════════════════════════════════
-- § 11. Individual-Time Pairs from Events
--       ([hacquard-2006], §4.1 -- UNVERIFIED: pp.131–136)
-- ════════════════════════════════════════════════════

/-! [hacquard-2006] proposes that accessibility relations take
EVENT arguments (193): `R_f := λe.λw. w is compatible with f(e)`.
Events project to (individual, time) pairs via two functions:

- `holder(e)`: the thematic participant — Agent, Experiencer, or
  speaker — determined by the event's thematic structure.
- `τ(e)`: the temporal trace — the time of the event.

This makes individual-time pairs (the traditional modal parameter per
[kratzer-1981]; [von-fintel-1999] generalizes to (individual, world) pairs) DERIVED from events, not
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

[kratzer-1981] relativizes accessibility to circumstances at a world.
[von-fintel-1999] §3.2 generalizes to (individual, world) pairs for
attitude predicates. Hacquard derives (individual, time) from events,
making stipulated parameters redundant. -/
structure IndTimePair (Individual TimePoint : Type*) where
  individual : Individual
  time : TimePoint
  deriving DecidableEq, Repr

/-- Event projection: how events map to individuals and times.

`holder` extracts the thematic participant:
"the agent and temporal trace of the event quantified by Aspect."
For speech events: the speaker. For attitudes: the experiencer.
For VP events: the agent or experiencer.

`time` extracts the temporal trace τ:
the time at which the event occurs, hence the time at which the
accessibility relation is evaluated. -/
structure EventProjection (Event Individual TimePoint : Type*) where
  holder : Event → Individual
  time : Event → TimePoint

/-- Derive the individual-time pair from an event.

This is the core of §4.1: individual-time pairs are not stipulated
but projected from events. `toPair proj e = (holder(e), τ(e))`. -/
def EventProjection.toPair {Event Individual TimePoint : Type*}
    (proj : EventProjection Event Individual TimePoint) (e : Event) :
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
def factoredAnchoring {Event W Individual TimePoint : Type*}
    (proj : EventProjection Event Individual TimePoint)
    (g : Individual → TimePoint → ConvBackground W) : AnchoringFn Event W :=
  λ e w => g (proj.holder e) (proj.time e) w

/-- Factored anchoring reduces to the (individual, time)-parameterized
function applied to the event's projected pair. -/
theorem factored_reduces {Event W Individual TimePoint : Type*}
    (proj : EventProjection Event Individual TimePoint)
    (g : Individual → TimePoint → ConvBackground W) (e : Event) (w : W) :
    factoredAnchoring proj g e w = g (proj.holder e) (proj.time e) w := rfl


-- ════════════════════════════════════════════════════
-- § 12. Events Carry More Than Pairs
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


end Modality
