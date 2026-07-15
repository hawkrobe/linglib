import Linglib.Semantics.Dynamic.ContextChange
import Linglib.Semantics.Dynamic.Possibility

/-!
# Register-form information states

Unbased information states over register-keyed possibilities
(`Assignment E := Nat → E`, i.e. the point object at `V := ℕ`) — the
state notion of the pre-based dynamic frameworks (PLA, BUS, file change
semantics). The based refinement lives in `State.lean`.

## Main definitions

- `InfoState W E`: sets of register-form possibilities.
- `InfoState.update`: propositional update (with the `s⟦φ⟧` notation).
- `InfoState.randomAssign`, `randomAssignFull`: discourse-referent
  introduction.

## References

- [kamp-vangenabith-reyle-2011]
- [heim-1982]
-/

namespace DynamicSemantics

open _root_.Core (Assignment)

/-- Information state: set of possibilities.

This is `InfoStateOf (Possibility W ℕ E)` — a specialization of the
generic `InfoStateOf` to world-assignment possibilities. -/
abbrev InfoState (W : Type*) (E : Type*) := Set (Possibility W ℕ E)

/-- State is consistent (non-empty). -/
def InfoState.consistent {W E : Type*} (s : InfoState W E) : Prop := s.Nonempty

/-- Update state with proposition: keep only possibilities where φ holds. -/
def InfoState.update {W E : Type*} (s : InfoState W E) (φ : W → Prop) : InfoState W E :=
  { p ∈ s | φ p.world }

notation:max s "⟦" φ "⟧" => InfoState.update s φ

/-- Random assignment: introduce new discourse referent at variable x. -/
def InfoState.randomAssign {W E : Type*} (s : InfoState W E) (x : Nat)
    (domain : Set E) : InfoState W E :=
  { p' | ∃ p ∈ s, ∃ e ∈ domain, p' = p.extend x e }

/-- Random assignment with full domain -/
def InfoState.randomAssignFull {W E : Type*} (s : InfoState W E) (x : Nat) : InfoState W E :=
  { p' | ∃ p ∈ s, ∃ e : E, p' = p.extend x e }

end DynamicSemantics
