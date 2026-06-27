import Linglib.Semantics.Events.Basic

/-!
# Event Adjacency and Temporal Precedence
[krifka-1998] [bach-1986] [champollion-2017]

Two events are temporally adjacent (`∞_E` in [krifka-1998]'s
notation) if their runtime intervals meet; one event temporally
precedes another (`«_E`) if its runtime is entirely before the
other's. These primitives are event-general — they're not specific
to movement relations or any particular thematic-role analysis — and
are consumed by:

- `Studies/Krifka1998.lean` Part II for K98 §4
  adjacency-respecting θ relations (ADJ/SMR/MR)
- `InitialFinalParts.lean` (initial/final parts via precedence)
- `MeasureAdverbialDerivation.lean` (planned, K98 §3.5 cτ minimal-
  convex-time derivation)
-/

/-- Two events are temporally adjacent (`∞_E` in [krifka-1998]'s
    notation) if their runtime intervals meet: one's finish equals
    the other's start. The natural concrete instance of K98's
    abstract event-adjacency primitive (eq. 14) on the `Event Time`
    structure where events have `runtime : Interval Time`. -/
def Event.adjacent {Time : Type*} [LinearOrder Time]
    (e1 e2 : Event Time) : Prop :=
  e1.runtime.snd = e2.runtime.fst ∨ e2.runtime.snd = e1.runtime.fst

/-- Event temporal precedence (`«_E` in K98 §2.5): one event's runtime
    is entirely before the other's. Defined via `Interval.isBefore`
    from `Core/Time/Interval/Basic.lean`. -/
def Event.precedes {Time : Type*} [LinearOrder Time]
    (e1 e2 : Event Time) : Prop :=
  e1.runtime.isBefore e2.runtime

/-- Event adjacency is symmetric. -/
theorem Event.adjacent_symm {Time : Type*} [LinearOrder Time]
    (e1 e2 : Event Time) :
    e1.adjacent e2 ↔ e2.adjacent e1 := by
  unfold Event.adjacent
  exact ⟨Or.symm, Or.symm⟩
