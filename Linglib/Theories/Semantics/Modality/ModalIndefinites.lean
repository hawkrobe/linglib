import Linglib.Theories.Semantics.Modality.EventRelativity
import Mathlib.Data.Fintype.Basic

/-!
# Modal Indefinite Semantics

@cite{alonso-ovalle-royer-2024} @cite{alonso-ovalle-menendez-benito-2010} @cite{hacquard-2006}

Formal denotation of modal indefinites: existential quantifiers carrying a
modal component whose domain is projected from an event argument via an
anchoring function. Extracted from EventRelativity §§3–7.

## Core Denotation (A-@cite{alonso-ovalle-royer-2024}, (59))

    ⟦MI⟧^{f,e₁} = λP.λQ.λw.
      ∃x[P(x)(w) ∧ Q(x)(w)] ∧
      ∀y[P(y)(w) → ◇_{f(e₁)}(Q(y)(w'))]

The existential component is standard; the universal modal component adds
**modal variation**: every restrictor member is a possible scope-satisfier
in some accessible world. The event argument e₁ and anchoring function f
determine the modal domain (epistemic, circumstantial, random choice).

## Upper-Boundedness (A-@cite{alonso-ovalle-royer-2024}, §5)

Some modal indefinites (*algún*) impose an anti-singleton inference:
the speaker considers it possible that not all domain members satisfy
the scope. Others (*yalnhej*) lack this condition.

Worked examples (Book/BookWorld and Card/CardWorld scenarios for
non-maximality and harmonic interpretations) live in the study file
`Phenomena/ModalIndefinites/Studies/AlonsoOvalleRoyer2024.lean`.

-/

namespace Semantics.Modality.ModalIndefinites

open Semantics.Modality.EventRelativity


-- ════════════════════════════════════════════════════
-- § 1. Modal Indefinite Denotation (A-@cite{alonso-ovalle-royer-2024}, (59))
-- ════════════════════════════════════════════════════

/-- The modal component of a modal indefinite (A-@cite{alonso-ovalle-royer-2024}, (59)):

    ∀y[P(y)(w) → ◇_{f(e₁)}(Q(y)(w'))]

For every individual y satisfying restrictor P in the actual world,
there exists an accessible world w' (via anchoring function f applied
to event e₁) where y satisfies scope predicate Q. This is the
"modal variation" inference: every domain member is a possible
witness. -/
def modalComponent {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Prop)
    (w : W) : Prop :=
  ∀ y ∈ domain, P y w → possibility f e allW (λ w' => Q y w') w

instance {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Prop)
    [∀ y, DecidablePred (P y)] [∀ y, DecidablePred (Q y)] (w : W) :
    Decidable (modalComponent f e allW domain P Q w) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Full modal indefinite denotation (A-@cite{alonso-ovalle-royer-2024}, (59)):

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
    (domain : List Entity) (P Q : Entity → W → Prop) (w : W) : Prop :=
  (∃ x ∈ domain, P x w ∧ Q x w) ∧
    modalComponent f e allW domain P Q w

instance {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Prop)
    [∀ y, DecidablePred (P y)] [∀ y, DecidablePred (Q y)] (w : W) :
    Decidable (modalIndefiniteSat f e allW domain P Q w) :=
  inferInstanceAs (Decidable (_ ∧ _))


-- ════════════════════════════════════════════════════
-- § 2. Upper-Boundedness (A-@cite{alonso-ovalle-royer-2024}, §5)
-- ════════════════════════════════════════════════════

/-- An upper-bounded modal indefinite additionally requires that NOT
every P is Q in the actual world — the speaker does not know/intend
for all domain members to satisfy Q.

    ⟦MI_UB⟧ = ⟦MI⟧ ∧ ¬∀x[P(x)(w) → Q(x)(w)]

This is the anti-singleton inference of *algún*. Items like *yalnhej* lack
this condition and are compatible with all P being Q. -/
def upperBoundedSat {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Prop) (w : W) : Prop :=
  modalIndefiniteSat f e allW domain P Q w ∧
    ¬ (∀ x ∈ domain, P x w → Q x w)

instance {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Prop)
    [∀ y, DecidablePred (P y)] [∀ y, DecidablePred (Q y)] (w : W) :
    Decidable (upperBoundedSat f e allW domain P Q w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Upper-boundedness strengthens the modal indefinite:
if the UB version holds, the plain MI version holds. -/
theorem upperBounded_entails_plain {Ev W Entity : Type*}
    (f : AnchoringFn Ev W) (e : Ev) (allW : List W)
    (domain : List Entity) (P Q : Entity → W → Prop) (w : W)
    (h : upperBoundedSat f e allW domain P Q w) :
    modalIndefiniteSat f e allW domain P Q w :=
  h.1


end Semantics.Modality.ModalIndefinites
