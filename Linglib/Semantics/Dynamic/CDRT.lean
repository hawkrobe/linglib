import Linglib.Core.Logic.Assignment
import Linglib.Semantics.Dynamic.Update

/-!
# Compositional DRT — registers, drefs, and boxes
[muskens-1996]

The substrate of Muskens' Logic of Change: states are atomic (his type
`s`), discourse referents are functions *from* states (`Dref S E`, his
type `se`), and boxes are the relational algebra of `Update.lean` at the
state type.

`RegisterStructure R S E` renders his register axioms: a carrier `R` of
*registers* (his type `π`) with a value function `val` (his `V`) and
register-wise update — AX1 ("having enough states"), skolemized as
`extend`, with the update relation `i[r]j` guarded by *register*
distinctness (his AX3 keeps distinct referents in distinct registers).
Constant registers (AX4's names) are constant `Dref`s, not members of
`R` — the VAR split of AX2. The canonical model instantiates registers
as coordinates of a function type: `RegisterStructure V (V → E) E`.

## Main definitions

- `Dref S E`: discourse referents, Muskens' type `se`.
- `RegisterStructure` with `randomAssign`, `dexists`, `dforall`, and the
  canonical instance at `V → E`.
- `atom1`, `atom2`, `eq'`: atomic conditions from predicates and drefs.
- `CDRT.State`, `CDRT.DProp`, `CDRT.SProp` and the box connectives:
  the concrete CDRT instance at `State E := Core.Assignment E`, with
  `DProp.new n` agreeing with the register structure's random assignment
  (`DProp.new_eq_randomAssign`).

The compositional fragment (T₀ translations, generalized coordination,
the paper's derivations) and the weakest-precondition calculus live in
`Studies/Muskens1996.lean`.
-/

namespace DynamicSemantics

open Update

/-- Discourse referent (Muskens' type `se`): a function from states to
individuals. Constant drefs (`Function.const`, AX4's names) are drefs
but not registers. -/
abbrev Dref (S E : Type*) := S → E

/-- Muskens' register structure: a carrier of registers (his type `π`)
with a value function (his `V`) and register-wise update. `extend`
skolemizes AX1 — for each state, register, and individual there is a
state that differs at most there — and the second law confines the
difference to the updated register. -/
class RegisterStructure (R S : Type*) (E : outParam Type*) where
  /-- The value of a register in a state (Muskens' `V`). -/
  val : R → S → E
  /-- Update a state at a register (AX1's witness). -/
  extend : S → R → E → S
  /-- The updated register holds the new value. -/
  val_extend_self : ∀ (i : S) (r : R) (e : E), val r (extend i r e) = e
  /-- Other registers are untouched. -/
  val_extend_of_ne : ∀ (i : S) (r r' : R) (e : E), r' ≠ r →
    val r' (extend i r e) = val r' i

/-- The canonical register structure: registers are the coordinates of a
function type, update is `Function.update`. -/
instance {V E : Type*} [DecidableEq V] : RegisterStructure V (V → E) E where
  val v g := g v
  extend g v e := Function.update g v e
  val_extend_self _ _ _ := Function.update_self ..
  val_extend_of_ne _ _ _ _ h := Function.update_of_ne h ..

namespace RegisterStructure

variable {R S E : Type*} [RegisterStructure R S E]

/-- Random assignment: `[r]` introduces the register `r` with an
arbitrary value. -/
def randomAssign (r : R) : Update S :=
  fun i j => ∃ e : E, j = extend i r e

/-- Existential update: `∃r(D) = [r]; D`. -/
def dexists (r : R) (D : Update S) : Update S :=
  seq (randomAssign r) D

/-- Universal condition: `∀r(D) = ¬∃r(¬D)`. -/
def dforall (r : R) (D : Update S) : Condition S :=
  neg (dexists r (test (neg D)))

end RegisterStructure

section Atomic

variable {S E : Type*}

/-- Atomic condition from a one-place predicate and a dref. -/
def atom1 (P : E → Prop) (u : Dref S E) : Condition S :=
  fun i => P (u i)

/-- Atomic condition from a two-place predicate and two drefs. -/
def atom2 (P : E → E → Prop) (u v : Dref S E) : Condition S :=
  fun i => P (u i) (v i)

/-- Equality condition on two drefs. -/
def eq' (u v : Dref S E) : Condition S :=
  fun i => u i = v i

end Atomic

end DynamicSemantics

namespace CDRT

open DynamicSemantics DynamicSemantics.Update

/-- CDRT state: Muskens' type `s`, concretely an assignment `Nat → E`.
His *registers* are register indices `n : ℕ` with values read by `dref`
(see the canonical `RegisterStructure` instance). -/
abbrev State (E : Type*) := Core.Assignment E

/-- Register lookup as a dref: Muskens' type `se`, picking out the value
stored at position `n`. -/
def dref {E : Type*} (n : Nat) : DynamicSemantics.Dref (State E) E :=
  fun r => r n

/-- Dynamic proposition (box, type `s(st)`): the relational `Update`
specialized to CDRT states. -/
abbrev DProp (E : Type*) := Update (State E)

/-- Static proposition: the spine's `Condition` at CDRT states. -/
abbrev SProp (E : Type*) := Condition (State E)

/-- Embed a static proposition as a dynamic one: the spine's `test`. -/
abbrev DProp.ofStatic {E : Type*} (p : SProp E) : DProp E := test p

/-- Dynamic conjunction: the spine's relational composition `seq`. -/
abbrev DProp.seq {E : Type*} (φ ψ : DProp E) : DProp E := Update.seq φ ψ

@[inherit_doc] infixl:65 " ;; " => DProp.seq

/-- New discourse referent: `[new n]` extends the state at position `n`
with an arbitrary value. -/
def DProp.new {E : Type*} (n : Nat) : DProp E :=
  fun i o => ∃ e : E, o = fun m => if m = n then e else i m

/-- `DProp.new` is the register structure's random assignment at the
canonical instance. -/
theorem DProp.new_eq_randomAssign {E : Type*} (n : Nat) :
    DProp.new (E := E) n = RegisterStructure.randomAssign n := by
  funext i o
  simp only [DProp.new, RegisterStructure.randomAssign, eq_iff_iff]
  exact exists_congr fun e => by
    constructor <;> (rintro rfl; funext m; simp [RegisterStructure.extend,
      Function.update_apply])

/-- Dynamic negation: the spine's `neg`, re-entering the update algebra
via `test`. -/
abbrev DProp.neg {E : Type*} (φ : DProp E) : DProp E := test (Update.neg φ)

/-- Dynamic implication: the spine's `impl` via `test`. -/
abbrev DProp.impl {E : Type*} (φ ψ : DProp E) : DProp E := test (Update.impl φ ψ)

/-- Dynamic disjunction as a test (SEM2, [muskens-1996] p. 148): the
spine's `disj` via `test`. -/
abbrev DProp.disj {E : Type*} (φ ψ : DProp E) : DProp E :=
  test (Update.disj φ ψ)

/-- Truth at a state: the spine's `closure`. -/
abbrev DProp.true_at {E : Type*} (φ : DProp E) (i : State E) : Prop :=
  closure φ i

/-! ### Reduction lemmas -/

/-- The output of a negated `DProp` always equals the input state. -/
theorem DProp.neg_output {E : Type*} {φ : DProp E} {i o : State E}
    (h : DProp.neg φ i o) : o = i := h.1.symm

/-- `DProp.impl` is true at `i` iff every antecedent extension satisfies
the consequent. -/
theorem DProp.impl_true_at {E : Type*} (φ ψ : DProp E) (i : State E) :
    DProp.true_at (DProp.impl φ ψ) i ↔ ∀ k, φ i k → DProp.true_at ψ k := by
  simp only [DProp.true_at, closure, DProp.impl, test, Update.impl]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨i, rfl, h⟩⟩

/-- A static `DProp` is true at `i` iff its static content holds. -/
theorem DProp.ofStatic_true_at {E : Type*} (p : SProp E) (i : State E) :
    DProp.true_at (DProp.ofStatic p) i ↔ p i := by
  simp only [DProp.true_at, closure, DProp.ofStatic, test]
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨i, rfl, h⟩⟩

end CDRT
