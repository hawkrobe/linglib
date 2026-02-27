import Linglib.Core.Semantics.Proposition
import Linglib.Core.Logic.ModalLogic

/-!
# Event-Relative Modality (Hacquard 2006, 2009, 2010)

Modal domains are projected from event arguments, not stipulated at the
clause level. An **anchoring function** maps events to conversational
backgrounds (Kratzer 1981): the event type (speech event vs described
event) determines the modal flavor.

## Key Insight

Kratzer's `ConvBackground` (`World → List (BProp World)`) gives the modal
base for a world. Hacquard adds a layer: modal bases are not
context-global but event-local. An anchoring function
`f : Ev → W → List (BProp W)` first selects the event, then produces a
Kratzer background.

- Speech event → epistemic background: what is known at utterance time
- Described event → circumstantial background: relevant circumstances

## Application: Modal Indefinites

Modal indefinites (Alonso-Ovalle & Royer 2024) are existential quantifiers
carrying a modal component whose domain is projected from an event
argument via an anchoring function. Syntactic position constrains which
event (and hence which flavor) is available:

- External argument position → speech event → epistemic only
- Internal argument / adjunct (volitional verb) → described event
  → epistemic or random choice
- Internal argument / adjunct (non-volitional verb) → epistemic only

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
function f applied to event e. -/
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


end Semantics.Modality.EventRelativity
