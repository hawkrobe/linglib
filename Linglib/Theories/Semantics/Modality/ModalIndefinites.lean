import Linglib.Theories.Semantics.Modality.EventRelativity

/-!
# Modal Indefinite Semantics (Alonso-Ovalle & Royer 2024)

@cite{alonso-ovalle-royer-2024} @cite{alonso-ovalle-menendez-benito-2010} @cite{hacquard-2006}Formal denotation of modal indefinites: existential quantifiers carrying a
modal component whose domain is projected from an event argument via an
anchoring function (Hacquard 2006). Extracted from EventRelativity §§3–7.

## Core Denotation (A-O&R 2024, (59))

    ⟦MI⟧^{f,e₁} = λP.λQ.λw.
      ∃x[P(x)(w) ∧ Q(x)(w)] ∧
      ∀y[P(y)(w) → ◇_{f(e₁)}(Q(y)(w'))]

The existential component is standard; the universal modal component adds
**modal variation**: every restrictor member is a possible scope-satisfier
in some accessible world. The event argument e₁ and anchoring function f
determine the modal domain (epistemic, circumstantial, random choice).

## Upper-Boundedness (A-O&R 2024, §5)

Some modal indefinites (*algún*) impose an anti-singleton inference:
the speaker considers it possible that not all domain members satisfy
the scope. Others (*yalnhej*) lack this condition.

## Harmonic Interpretations (A-O&R 2024, §4.3)

Under external modals (imperatives, deontic), the MI's anchor can be
co-indexed with the external modal's event, yielding "any X is fine"
readings. Non-harmonic anchoring gives "a random X" readings.

-/

namespace Semantics.Modality.ModalIndefinites

open Core.Proposition
open Semantics.Modality.EventRelativity


-- ════════════════════════════════════════════════════
-- § 1. Modal Indefinite Denotation (A-O&R 2024, (59))
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
-- § 2. Upper-Boundedness (A-O&R 2024, §5)
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
-- § 3. Worked Example: 3 Books
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
-- § 4. Non-Maximality (A-O&R 2024, §3.2.4)
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
-- § 5. Harmonic Interpretations (A-O&R 2024, §4.3)
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


end Semantics.Modality.ModalIndefinites
