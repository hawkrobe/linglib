import Linglib.Core.Semantics.Proposition
import Linglib.Core.Logic.ModalLogic

/-!
# Event-Relative Modality (Hacquard 2006, 2009, 2010) @cite{hacquard-2010}

Modal domains are projected from event arguments, not stipulated at the
clause level. An **anchoring function** maps events to conversational
backgrounds (Kratzer 1981): the event type determines the modal flavor.

## Core Architecture

Kratzer's `ConvBackground` (`World → List (BProp World)`) gives the modal
base for a world. Hacquard adds a layer: modal bases are not
context-global but event-local. An anchoring function
`f : Ev → W → List (BProp W)` first selects the event, then produces a
Kratzer background.

## Content Licensing (§8–9)

The position → flavor correlation is DERIVED from a single predicate:
**content licensing** (Hacquard 2010, §6). Epistemic modal bases require
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

Modal indefinites (Alonso-Ovalle & Royer 2024) are existential quantifiers
carrying a modal component whose domain is projected from an event
argument via an anchoring function.

## References

- Hacquard, V. (2006). Aspects of Modality. MIT dissertation.
- Hacquard, V. (2009). On the interaction of aspect and modal auxiliaries.
  Linguistics and Philosophy 32:279–315.
- Hacquard, V. (2010). On the event relativity of modal auxiliaries.
  Natural Language Semantics 18:79–114.
- Alonso-Ovalle, L. & Royer, J. (2024). Modal indefinites: Lessons from
  Chuj. Linguistics and Philosophy.
- Kratzer, A. (1981). The Notional Category of Modality.
-/

namespace Semantics.Modality.EventRelativity

open Core.Proposition
open Core.ModalLogic (ModalFlavor)


-- ════════════════════════════════════════════════════
-- § 1. Anchoring Functions
-- ════════════════════════════════════════════════════

/-- An anchoring function maps events to conversational backgrounds.

This is Hacquard's (2006) central innovation: modal bases are not
global context parameters but projected from event arguments.

The type `AnchoringFn Ev W = Ev → W → List (BProp W)` specializes
to Kratzer's `ConvBackground = World → List (BProp World)` when
applied to a specific event. -/
abbrev AnchoringFn (Ev W : Type*) := Ev → W → List (BProp W)

/-- An anchoring function applied to a specific event yields a
Kratzer-style conversational background. -/
def anchor {Ev W : Type*} (f : AnchoringFn Ev W) (e : Ev) : W → List (BProp W) :=
  f e

/-- The type of modal anchor: determines which event provides the
modal base and hence which modal flavor results.

Hacquard (2006): the speech event projects epistemic modality;
the described event projects circumstantial/root modality.
Alonso-Ovalle & Royer (2024) refine circumstantial to include
random choice as a subtype. -/
inductive AnchorType where
  /-- Anchored to the speech event → epistemic modal base -/
  | speechEvent
  /-- Anchored to the described event → circumstantial modal base -/
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
-- § 3. Modal Indefinite Denotation (A-O&R 2024, (59))
-- ════════════════════════════════════════════════════

/-- The modal component of a modal indefinite (A-O&R 2024, (59)):

    ∀y[P(y)(w) → ◇_{f(e₁)}(Q(y)(w'))]

For every individual y satisfying restrictor P in the actual world,
there exists an accessible world w' (via anchoring function f applied
to event e₁) where y satisfies scope predicate Q. This is the
"modal variation" inference: every domain member is a possible
witness. -/
def modalComponent {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Bool)
    (w : W) : Bool :=
  domain.all λ y => !(P y w) ||
    possibility f e allW (λ w' => Q y w') w

/-- Full modal indefinite denotation (A-O&R 2024, (59)):

    ⟦MI⟧^{f,e₁} = λP.λQ.λw.
      ∃x[P(x)(w) ∧ Q(x)(w)] ∧
      ∀y[P(y)(w) → ◇_{f(e₁)}(Q(y)(w'))]

The existential component asserts that some individual satisfies
both restrictor and scope. The universal modal component asserts
that EVERY restrictor individual is a possible scope-satisfier
in some accessible world — the free choice / modal variation
effect. -/
def modalIndefiniteSat {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Bool) (w : W) : Bool :=
  (domain.any λ x => P x w && Q x w) &&
    modalComponent f e allW domain P Q w


-- ════════════════════════════════════════════════════
-- § 4. Upper-Boundedness (A-O&R 2024, §5)
-- ════════════════════════════════════════════════════

/-- An upper-bounded modal indefinite additionally requires that NOT
every P is Q in the actual world — the speaker does not know/intend
for all domain members to satisfy Q.

    ⟦MI_UB⟧ = ⟦MI⟧ ∧ ¬∀x[P(x)(w) → Q(x)(w)]

This is the anti-singleton inference of *algún*
(Alonso-Ovalle & Menéndez-Benito 2010). Items like *yalnhej* lack
this condition and are compatible with all P being Q. -/
def upperBoundedSat {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Bool) (w : W) : Bool :=
  modalIndefiniteSat f e allW domain P Q w &&
    !(domain.all λ x => !(P x w) || Q x w)

/-- Upper-boundedness strengthens the modal indefinite:
if the UB version holds, the plain MI version holds. -/
theorem upperBounded_entails_plain {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Bool) (w : W)
    (h : upperBoundedSat f e allW domain P Q w = true) :
    modalIndefiniteSat f e allW domain P Q w = true := by
  unfold upperBoundedSat at h
  simp only [Bool.and_eq_true] at h
  exact h.1


-- ════════════════════════════════════════════════════
-- § 5. Worked Example: 3 Books
-- ════════════════════════════════════════════════════

/-- Three books for testing the modal indefinite semantics. -/
inductive Book where | a | b | c
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Three possible worlds varying in which books are available. -/
inductive BookWorld where
  | abc   -- all three available
  | ab    -- only a, b available
  | ac    -- only a, c available
  deriving DecidableEq, BEq, Repr, Inhabited

instance : Core.Proposition.FiniteWorlds BookWorld where
  worlds := [.abc, .ab, .ac]
  complete := λ w => by cases w <;> simp

private def allBooks : List Book := [.a, .b, .c]
private def allBW : List BookWorld := [.abc, .ab, .ac]

/-- "is a book": always true for our domain. -/
private def isBook : Book → BookWorld → Bool := λ _ _ => true

/-- "is available": varies by world. -/
private def isAvailable : Book → BookWorld → Bool
  | .a, _ => true           -- book a always available
  | .b, .abc => true
  | .b, .ab => true
  | .b, .ac => false
  | .c, .abc => true
  | .c, .ab => false
  | .c, .ac => true

/-- A speech event and a described event. -/
inductive SpeechOrDescribed where | speech | described
  deriving DecidableEq, BEq, Repr

/-- Epistemic anchoring: the speaker considers all three worlds possible. -/
private def fEPI : AnchoringFn SpeechOrDescribed BookWorld :=
  λ _ _ => []  -- empty background → all worlds accessible

/-- "Yalnhej bought a book" in world abc:
    ∃x[book(x) ∧ avail(x)] ∧ ∀y[book(y) → ◇_{EPI}(avail(y))]
    Every book is available in some accessible world. -/
theorem yalnhej_book_abc :
    modalIndefiniteSat fEPI .speech allBW allBooks isBook isAvailable .abc = true := by
  native_decide

/-- Not upper-bounded: in world abc, all three books ARE available,
    yet the MI denotation holds. The anti-singleton condition fails
    (all books satisfy the scope), showing yalnhej is non-UB. -/
theorem yalnhej_not_upper_bounded_abc :
    modalIndefiniteSat fEPI .speech allBW allBooks isBook isAvailable .abc = true ∧
    ¬(upperBoundedSat fEPI .speech allBW allBooks isBook isAvailable .abc = true) := by
  constructor
  · native_decide
  · native_decide


-- ════════════════════════════════════════════════════
-- § 6. Non-Maximality (A-O&R 2024, §3.2.4)
-- ════════════════════════════════════════════════════

/-! Yalnhej is compatible with partial-domain scenarios: the speaker
can felicitously use *yalnhej* even when not all P are Q. This
distinguishes it from maximal free relatives (*whatever*), which
require every domain member to satisfy the scope. Unlike
upper-boundedness (which blocks ∀P→Q), non-maximality is about
COMPATIBILITY with ¬∀P→Q — a weaker property.

We demonstrate non-maximality using the existing 3-book model:
in world `ab` (books a,b available but NOT c), the MI denotation
still holds because every book is available in SOME accessible world,
even though not every book is available in the actual world. -/

/-- MI holds in world ab where book c is NOT available.
    The existential component (∃x P∧Q) holds (book a is available).
    The modal component (∀y P→◇Q) holds (each book is available
    in some accessible world). Crucially, ¬∀y P→Q(y)(ab): book c
    is not available in ab. This shows yalnhej is compatible with
    not-all-P-being-Q — non-maximality. -/
theorem yalnhej_nonmaximal_ab :
    modalIndefiniteSat fEPI .speech allBW allBooks isBook isAvailable .ab = true := by
  native_decide

/-- Three-way contrast: maximality vs yalnhej vs *algún*.
    In world abc (all books available): MI holds + UB fails.
    In world ab (not all available): MI holds + UB holds.
    A maximal item (*whatever*) would require all books available
    (fail in ab). *Algún* (UB) would require not-all (fail in abc).
    *Yalnhej* (non-UB) succeeds in BOTH. -/
theorem yalnhej_three_way_contrast :
    -- yalnhej OK in abc (all available)
    modalIndefiniteSat fEPI .speech allBW allBooks isBook isAvailable .abc = true ∧
    -- yalnhej OK in ab (not all available) — non-maximal
    modalIndefiniteSat fEPI .speech allBW allBooks isBook isAvailable .ab = true ∧
    -- UB fails in abc (all satisfy scope → anti-singleton violated)
    upperBoundedSat fEPI .speech allBW allBooks isBook isAvailable .abc = false := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide


-- ════════════════════════════════════════════════════
-- § 7. Harmonic Interpretations (A-O&R 2024, §4.3)
-- ════════════════════════════════════════════════════

/-! When a modal indefinite occurs under an external modal (imperative,
deontic, attitude verb), the MI's anchoring event can be CO-INDEXED
with the external modal's event. This "harmonic" configuration
gives "any X is fine" readings — the MI's modal domain aligns with
the embedding modal's domain.

Non-harmonic: the MI's anchor is independent of the external modal.
  "Grab yalnhej card" = grab a random card (MI anchors to described event).
Harmonic: the MI's anchor is co-indexed with the imperative/deontic event.
  "Grab yalnhej card" = any card is fine (MI anchors to imperative event).

We model this with a card-grabbing scenario: three cards, worlds varying
in which cards are grabbable, and two event types (local vs imperative). -/

/-- Three cards for testing harmonic readings. -/
inductive Card where | c1 | c2 | c3
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Three worlds varying in which cards are grabbable. -/
inductive CardWorld where
  | all    -- all three grabbable
  | only1  -- only c1 grabbable
  | only2  -- only c2 grabbable
  deriving DecidableEq, BEq, Repr, Inhabited

private def allCards : List Card := [.c1, .c2, .c3]
private def allCW : List CardWorld := [.all, .only1, .only2]

/-- "is a card": always true in our domain. -/
private def isCard : Card → CardWorld → Bool := λ _ _ => true

/-- "can grab": which cards are grabbable in which worlds. -/
private def canGrab : Card → CardWorld → Bool
  | .c1, .all   => true
  | .c1, .only1 => true
  | .c1, .only2 => false
  | .c2, .all   => true
  | .c2, .only1 => false
  | .c2, .only2 => true
  | .c3, .all   => true
  | .c3, .only1 => false
  | .c3, .only2 => false

/-- Three event types: speech, local (described), imperative. -/
inductive GrabEvent where | speech | local | imperative
  deriving DecidableEq, BEq, Repr

/-- Anchoring function for the card scenario.
    - Speech event: empty background (all worlds accessible).
    - Local event: restricts to worlds where local circumstances hold
      (only world `only1` — current situation has only c1 available).
    - Imperative event: all worlds accessible (any card COULD be
      grabbed if permitted). -/
private def fGrab : AnchoringFn GrabEvent CardWorld
  | .speech, _ => []  -- all worlds accessible
  | .local, _ => [λ w => w == .only1]  -- only `only1` accessible
  | .imperative, _ => []  -- all worlds accessible (permission domain)

/-- Non-harmonic MI fails: when the MI anchors to the local event,
    only world `only1` is accessible. In `only1`, only c1 is grabbable.
    The modal component ∀y[card(y) → ◇_{local}(grab(y))] fails because
    c2 and c3 are not grabbable in any locally accessible world. -/
theorem nonharmonic_fails :
    modalIndefiniteSat fGrab .local allCW allCards isCard canGrab .only1 = false := by
  native_decide

/-- Harmonic MI succeeds: when the MI's anchor is co-indexed with the
    imperative event, all worlds are accessible. Every card is grabbable
    in some world (c1 in `only1`, c2 in `only2`, c3 in `all`). The
    modal component ∀y[card(y) → ◇_{imperative}(grab(y))] holds.
    This gives the "any card is fine" reading. -/
theorem harmonic_succeeds :
    modalIndefiniteSat fGrab .imperative allCW allCards isCard canGrab .only1 = true := by
  native_decide

/-- Harmonic ≠ non-harmonic: the two readings are formally distinct.
    Same world of evaluation (.only1), same domain, same predicates —
    only the anchoring event differs. -/
theorem harmonic_neq_nonharmonic :
    modalIndefiniteSat fGrab .local allCW allCards isCard canGrab .only1 = false ∧
    modalIndefiniteSat fGrab .imperative allCW allCards isCard canGrab .only1 = true := by
  constructor <;> native_decide


-- ════════════════════════════════════════════════════
-- § 8. Event Binders and Content Licensing
--      (Hacquard 2010, §5–6)
-- ════════════════════════════════════════════════════

/-! Hacquard (2010) identifies THREE event binders that can supply a
modal's event argument. The closest c-commanding binder determines
which event the modal is relative to:

- e₀: the speech act event (bound by ASSERT / illocutionary force)
- e₁: an attitude event (bound by attitude verbs: *believe*, *want*, ...)
- e₂: the VP event (bound by aspect: IMPF/PRFV)

The binary `AnchorType` (§1) omits e₁ (irrelevant in A-O&R's
matrix-clause data), keeping only the speech event (e₀) / VP event (e₂)
distinction. `EventBinder` adds e₁, which matters because attitude
events are **contentful** (like speech events), not contentless (like
VP events).

The key insight (Hacquard 2010, §6): epistemic modal bases require a
contentful event — one with propositional content CON(e). Speech acts
and attitudes have content; VP events (running, screaming) do not.
This single predicate derives the position → flavor correlation. -/

/-- The three event binders (Hacquard 2010, (38), (48)). -/
inductive EventBinder where
  /-- e₀: the utterance event (bound by ASSERT) -/
  | speechAct
  /-- e₁: an attitude verb's event (believe, want, think, ...) -/
  | attitude
  /-- e₂: the VP's described event (bound by aspect) -/
  | vpEvent
  deriving DecidableEq, BEq, Repr

/-- Whether an event has propositional content (Hacquard 2010, §6).

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
licensing (Hacquard 2010, §6) but omits deontic. Deontic licensing
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

/-- Content licensing: epistemic availability ↔ content (Hacquard 2010, §6). -/
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
(below Asp), blocking epistemic readings (Hacquard 2010, §3.2). -/
theorem low_modal_not_epistemic :
    EventBinder.vpEvent.canProjectEpistemic = false := rfl

/-- Contentful events yield both flavors; contentless events yield
only circumstantial. Derives the pattern in Hacquard's (2010) (49a–f). -/
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

/-- `AnchorType.toFlavor` is derivable from content licensing: the
primary flavor for each anchor type is the head of the corresponding
event binder's available flavor list. This replaces a stipulation
with a derivation through `hasContent`. -/
theorem toFlavor_derived :
    ∀ a : AnchorType,
      a.toEventBinder.availableFlavors.head? = some a.toFlavor := by
  intro a; cases a <;> rfl

/-- The six binder × flavor combinations (Hacquard 2010, (49a–f)).
Content licensing explains (49e): VP events lack content → no epistemic.
The remaining unattested combinations (49b: speech act + circumstantial,
49d: attitude + circumstantial) are semantically possible but
pragmatically blocked — circumstantial readings of high modals are
pre-empted by the more informative epistemic reading (Hacquard 2010,
pp.110–111). -/
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
Hacquard (2010, §5.3): this is the structural correlate of the
Cinque (1999) high/low modal distinction. -/
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

    anchor f e : W → List (BProp W)  ≡  ConvBackground

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
-- § 11. Individual-Time Pairs from Events
--       (Hacquard 2006, §4.1, pp.131–136)
-- ════════════════════════════════════════════════════

/-! Hacquard (2006, §4.1) proposes that accessibility relations take
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

Kratzer (1981) relativizes accessibility to circumstances at a world.
Von Fintel & Heim (1999) relativize to an (individual, time). Hacquard
derives the pair from events, making it redundant as a primitive. -/
structure IndTimePair (Individual TimePoint : Type*) where
  individual : Individual
  time : TimePoint
  deriving DecidableEq, BEq, Repr

/-- Event projection: how events map to individuals and times.

`holder` extracts the thematic participant (Hacquard 2006, p.134):
"the agent and temporal trace of the event quantified by Aspect."
For speech events: the speaker. For attitudes: the experiencer.
For VP events: the agent or experiencer.

`time` extracts the temporal trace τ (Hacquard 2006, p.135):
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
  a. Given MY evidence NOW, Jane must have taken the train.    [epistemic]
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
