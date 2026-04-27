import Mathlib.Order.Basic

/-!
# Initial and Final Parts (via Precedence)
@cite{krifka-1998} @cite{krifka-1989}

A part `e'` of a whole `e` is INITIAL iff no other part precedes `e'`,
FINAL iff no other part follows `e'`. Generic over a partial order
and a precedence relation; specialize with `Ev.precedes` for events
(`Theories/Semantics/Events/EventAdjacency.lean`).

These are the substrate predicates for `MovementRelations.lean`'s
SOURCE/GOAL definitions (K98 §4.5 eq. 73), and for the planned
propositional `TEL` predicate that captures K98 §2.5 eq. 37
(*every part of a P-event that is also P is both initial and final*),
which is strictly weaker than `QUA`.

## Sections

1. `IsInitialPart` (K98 §2.5 eq. 36 INI)
2. `IsFinalPart` (K98 §2.5 eq. 36 FIN)
3. Self-as-initial / self-as-final corner cases
4. `IsTelic` — K98 §2.5 eq. 37 propositional telicity

-/

namespace Semantics.Events.InitialFinalParts

/-- K98 §2.5 eq. 36 INI: e' is an initial part of e iff e' ≤ e and
    no other part of e precedes e'. Generic over a part order and a
    precedence relation; specialize with `Ev.precedes` for events. -/
def IsInitialPart {β : Type*} [PartialOrder β]
    (precedes : β → β → Prop) (e' e : β) : Prop :=
  e' ≤ e ∧ ¬ ∃ e'', e'' ≤ e ∧ precedes e'' e'

/-- K98 §2.5 eq. 36 FIN: e' is a final part of e iff e' ≤ e and no
    other part of e follows e'. -/
def IsFinalPart {β : Type*} [PartialOrder β]
    (precedes : β → β → Prop) (e' e : β) : Prop :=
  e' ≤ e ∧ ¬ ∃ e'', e'' ≤ e ∧ precedes e' e''

/-- The whole is trivially an initial part of itself when no proper
    part precedes it (vacuously true if precedence is empty). -/
theorem isInitialPart_self {β : Type*} [PartialOrder β]
    (precedes : β → β → Prop) (e : β)
    (h : ¬ ∃ e'', e'' ≤ e ∧ precedes e'' e) :
    IsInitialPart precedes e e :=
  ⟨le_refl e, h⟩

/-- The whole is trivially a final part of itself when no proper part
    follows it. -/
theorem isFinalPart_self {β : Type*} [PartialOrder β]
    (precedes : β → β → Prop) (e : β)
    (h : ¬ ∃ e'', e'' ≤ e ∧ precedes e e'') :
    IsFinalPart precedes e e :=
  ⟨le_refl e, h⟩

/-- K98 §2.5 eq. 37 propositional telicity (TEL). A predicate `P` is
    telic iff every P-instance e' that is part of a P-instance e is
    both an initial part and a final part of e. K98 page 9: "all
    parts of e that fall under X are initial and final parts of e."

    Strictly weaker than `QUA`: every QUA predicate is TEL because it
    has no proper P-parts (vacuously initial-and-final), but not every
    TEL predicate is QUA — K98's run-time-3-4pm counterexample on
    page 9 is a telic predicate that isn't quantized. -/
def IsTelic {β : Type*} [PartialOrder β]
    (precedes : β → β → Prop) (P : β → Prop) : Prop :=
  ∀ e e' : β, P e → P e' → e' ≤ e → IsInitialPart precedes e' e ∧ IsFinalPart precedes e' e

end Semantics.Events.InitialFinalParts
