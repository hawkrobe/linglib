import Linglib.Semantics.Dynamic.ContextChange
import Linglib.Semantics.Dynamic.Ty2

/-!
# Compositional DRT — states, drefs, and boxes
[muskens-1996]

CDRT instantiates Dynamic Ty2 at the concrete state type
`State E := Core.Assignment E` (`Nat → E`) — Muskens's type `s`. A
*register* (discourse referent, his type `se`) is a map *from* states —
here the projection `dref n` — not the state itself. Boxes (type `s(st)`)
are `DProp E := Update (State E)`: the relational algebra of
`Update.lean` specialized to CDRT states, so the connectives
*are* `dseq`/`test`/`dneg`/`dimpl`/`ddisj` by definition rather than
re-stipulation. Only `DProp.new` (ℕ-indexed random assignment) is a
CDRT-specific primitive: the abstract `AssignmentStructure` cannot be
instantiated at `Nat → E`.

The compositional fragment (T₀ translations, generalized coordination,
the paper's derivations) and the weakest-precondition calculus live in
`Studies/Muskens1996.lean`.
-/

namespace CDRT

open DynamicSemantics.DynProp

/-- CDRT state: Muskens's type `s`, concretely an assignment `Nat → E`.
His *registers* are the maps from states (see `dref`), not the states —
the earlier name `Register` for this type inverted the paper's
terminology. The alias shares mathlib's `Function.update` simp set with
H&K composition, DPL, Charlow continuations, and Spector's plural
substrate. -/
abbrev State (E : Type*) := Core.Assignment E

/-- Register lookup as a Dynamic Ty2 dref: Muskens's type `se`,
picking out the value stored at position `n`. -/
def dref {E : Type*} (n : Nat) : DynamicSemantics.Dref (State E) E :=
  λ r => r n

/-- Dynamic proposition (box, type `s(st)`): the relational `Update`
specialized to CDRT states. -/
abbrev DProp (E : Type*) := Update (State E)

/-- Static proposition: the spine's `Condition` at CDRT states. -/
abbrev SProp (E : Type*) := Condition (State E)

/-- Embed a static proposition as a dynamic one: the spine's `test`. -/
abbrev DProp.ofStatic {E : Type*} (p : SProp E) : DProp E := test p

/-- Dynamic conjunction: the spine's relational composition `dseq`. -/
abbrev DProp.seq {E : Type*} (φ ψ : DProp E) : DProp E := dseq φ ψ

infixl:65 " ;; " => DProp.seq

/-- New discourse referent: `[new n]` extends the state at position `n`
with an arbitrary value. CDRT's one native primitive. -/
def DProp.new {E : Type*} (n : Nat) : DProp E :=
  λ i o => ∃ e : E, o = λ m => if m = n then e else i m

/-- Dynamic negation: the spine's `dneg`, re-entering the update algebra
via `test`. -/
abbrev DProp.neg {E : Type*} (φ : DProp E) : DProp E := test (dneg φ)

/-- Dynamic implication: the spine's `dimpl` via `test`. -/
abbrev DProp.impl {E : Type*} (φ ψ : DProp E) : DProp E := test (dimpl φ ψ)

/-- Dynamic disjunction as a test (SEM2, [muskens-1996] p. 148): the
spine's `ddisj` via `test`. -/
abbrev DProp.ddisj {E : Type*} (φ ψ : DProp E) : DProp E :=
  test (DynamicSemantics.DynProp.ddisj φ ψ)

/-- Truth at a state: the spine's `closure`. -/
abbrev DProp.true_at {E : Type*} (φ : DProp E) (i : State E) : Prop :=
  closure φ i

/-- Dynamic entailment: every output of `φ` can be extended by `ψ`. -/
def DProp.entails {E : Type*} (φ ψ : DProp E) : Prop :=
  ∀ i o, φ i o → ψ.true_at o

/-! ### Reduction lemmas -/

/-- The output of a negated `DProp` always equals the input state. -/
theorem DProp.neg_output {E : Type*} {φ : DProp E} {i o : State E}
    (h : DProp.neg φ i o) : o = i := h.1.symm

/-- `DProp.impl` is true at `i` iff every antecedent extension satisfies
the consequent. -/
theorem DProp.impl_true_at {E : Type*} (φ ψ : DProp E) (i : State E) :
    DProp.true_at (DProp.impl φ ψ) i ↔ ∀ k, φ i k → DProp.true_at ψ k := by
  simp only [DProp.true_at, closure, DProp.impl, test, dimpl]
  exact ⟨λ ⟨_, rfl, h⟩ => h, λ h => ⟨i, rfl, h⟩⟩

/-- A static `DProp` is true at `i` iff its static content holds. -/
theorem DProp.ofStatic_true_at {E : Type*} (p : SProp E) (i : State E) :
    DProp.true_at (DProp.ofStatic p) i ↔ p i := by
  simp only [DProp.true_at, closure, DProp.ofStatic, test]
  exact ⟨λ ⟨_, rfl, h⟩ => h, λ h => ⟨i, rfl, h⟩⟩

end CDRT
