import Linglib.Theories.Semantics.Events.Mereology

/-!
# Event Adjacency and Temporal Precedence
@cite{krifka-1998} @cite{bach-1986} @cite{champollion-2017}

Two events are temporally adjacent (`∞_E` in @cite{krifka-1998}'s
notation) if their runtime intervals meet; one event temporally
precedes another (`«_E`) if its runtime is entirely before the
other's. These primitives are event-general — they're not specific
to movement relations or any particular thematic-role analysis — and
are consumed by:

- `MovementRelations.lean` for adjacency-respecting θ relations
- `InitialFinalParts.lean` (initial/final parts via precedence)
- `MeasureAdverbialDerivation.lean` (planned, K98 §3.5 cτ minimal-
  convex-time derivation)

## Sections

1. `Ev.adjacent` — event adjacency via runtime-meet
2. `Ev.precedes` — event temporal precedence via `Interval.isBefore`
3. `Ev.adjacent_symm` — adjacency is symmetric

-/

namespace Semantics.Events

/-- Two events are temporally adjacent (`∞_E` in @cite{krifka-1998}'s
    notation) if their runtime intervals meet: one's finish equals
    the other's start. The natural concrete instance of K98's
    abstract event-adjacency primitive (eq. 14) on the `Ev Time`
    structure where events have `runtime : Interval Time`. -/
def Ev.adjacent {Time : Type*} [LinearOrder Time]
    (e1 e2 : Ev Time) : Prop :=
  e1.runtime.finish = e2.runtime.start ∨ e2.runtime.finish = e1.runtime.start

/-- Event temporal precedence (`«_E` in K98 §2.5): one event's runtime
    is entirely before the other's. Defined via `Interval.isBefore`
    from `Core/Time/Interval/Basic.lean`. -/
def Ev.precedes {Time : Type*} [LinearOrder Time]
    (e1 e2 : Ev Time) : Prop :=
  e1.runtime.isBefore e2.runtime

/-- Event adjacency is symmetric. -/
theorem Ev.adjacent_symm {Time : Type*} [LinearOrder Time]
    (e1 e2 : Ev Time) :
    e1.adjacent e2 ↔ e2.adjacent e1 := by
  unfold Ev.adjacent
  exact ⟨Or.symm, Or.symm⟩

end Semantics.Events
