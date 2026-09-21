import Linglib.Logic.Assignment
import Linglib.Logic.CylindricAlgebra
import Linglib.Semantics.Dynamic.Update
import Mathlib.Data.Set.Function

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
- `RegisterStructure` with its canonical instance at `V → E`, and the
  updates it supports, `Update.randomAssign`, `Update.dexists`, `Update.dforall`.
- `Condition.atom1`, `Condition.atom2`, `Condition.eq`: atomic conditions
  from predicates and drefs.
- `Update.mem_randomAssign`, `Update.mem_randomAssign_iff_eqOn`, `Update.dom_dexists`: at the
  canonical register structure a random assignment is `Function.update` at an arbitrary value,
  agreement off the register, and, under the weakest precondition, cylindrification.
- `CDRT.State`, `CDRT.DProp`, `CDRT.dref`: the concrete CDRT instance at
  `State E := Assignment E`.

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

namespace Update

open SetRel

variable {R S E : Type*} [RegisterStructure R S E]

/-- Random assignment: `[r]` introduces the register `r` with an
arbitrary value. -/
def randomAssign (r : R) : Update S :=
  {(a, b) | ∃ e : E, b = RegisterStructure.extend a r e}

/-- Existential update: `∃r(D) = [r]; D`. -/
def dexists (r : R) (D : Update S) : Update S :=
  randomAssign r ○ D

/-- Universal condition: `∀r(D)` holds iff `D` has an output from every
`r`-variant — [groenendijk-stokhof-1991]'s clause for the universal. -/
def dforall (r : R) (D : Update S) : Condition S :=
  impl (randomAssign r) D

/-- The weakest precondition of a random assignment quantifies over the values of the
register. -/
theorem preimage_randomAssign (r : R) (t : Condition S) :
    (randomAssign r).preimage t = {i | ∃ e : E, RegisterStructure.extend i r e ∈ t} := by
  ext i
  exact ⟨fun ⟨_, hj, e, he⟩ => ⟨e, he ▸ hj⟩, fun ⟨e, he⟩ => ⟨_, he, e, rfl⟩⟩

end Update

namespace Update

open SetRel CylindricAlgebra

variable {V E : Type*} [DecidableEq V] {g h : V → E} {x : V}

@[simp] theorem _root_.DynamicSemantics.RegisterStructure.extend_eq_update (e : E) :
    RegisterStructure.extend g x e = Function.update g x e := rfl

@[simp] theorem _root_.DynamicSemantics.RegisterStructure.val_apply :
    RegisterStructure.val x g = g x := rfl

/-- At the canonical register structure, random assignment is
`Function.update` at an arbitrary value. -/
theorem mem_randomAssign : g ~[randomAssign x] h ↔ ∃ e, h = Function.update g x e := Iff.rfl

/-- At the canonical register structure, random assignment at `x` is
agreement off `x`. -/
theorem mem_randomAssign_iff_eqOn : g ~[randomAssign x] h ↔ Set.EqOn g h {x}ᶜ :=
  ⟨by rintro ⟨e, rfl⟩ v hv; exact (Function.update_of_ne hv e g).symm,
    fun hk => ⟨h x, (Function.update_eq_iff.mpr ⟨rfl, fun _ hv => hk hv⟩).symm⟩⟩

/-- At the canonical register structure, an existential runs its scope from some variant of the
input at `x`. -/
theorem mem_dexists {D : Update (V → E)} :
    g ~[dexists x D] h ↔ ∃ e, Function.update g x e ~[D] h :=
  ⟨by rintro ⟨_, ⟨e, rfl⟩, hD⟩; exact ⟨e, hD⟩, fun ⟨e, hD⟩ => ⟨_, ⟨e, rfl⟩, hD⟩⟩

/-- At the canonical register structure, a universal holds when its scope has an output from
every variant of the input at `x`. -/
theorem mem_dforall {D : Update (V → E)} :
    g ∈ dforall x D ↔ ∀ e, Function.update g x e ∈ D.dom :=
  ⟨fun hall e => hall ⟨e, rfl⟩, by rintro hall _ ⟨e, rfl⟩; exact hall e⟩

/-- The weakest precondition of a random assignment is cylindrification
([henkin-monk-tarski-1971]). -/
theorem preimage_randomAssign_eq_cyl (t : Condition (V → E)) :
    (randomAssign x).preimage t = cyl x t :=
  preimage_randomAssign x t

/-- An existential is true where the cylindrification of its scope's truth set is. -/
theorem dom_dexists (D : Update (V → E)) : (dexists x D).dom = cyl x D.dom := by
  rw [← preimage_randomAssign_eq_cyl, ← preimage_univ_right, ← preimage_univ_right, dexists,
    preimage_comp]

end Update

section Atomic

variable {S E : Type*}

/-- Atomic condition from a one-place predicate and a dref. -/
def Condition.atom1 (P : E → Prop) (u : Dref S E) : Condition S :=
  {i | P (u i)}

/-- Atomic condition from a two-place predicate and two drefs. -/
def Condition.atom2 (P : E → E → Prop) (u v : Dref S E) : Condition S :=
  {i | P (u i) (v i)}

/-- Equality condition on two drefs. -/
def Condition.eq (u v : Dref S E) : Condition S :=
  {i | u i = v i}

end Atomic

end DynamicSemantics

namespace CDRT

open DynamicSemantics DynamicSemantics.Update

/-- CDRT state: Muskens' type `s`, concretely an assignment `Nat → E`.
His *registers* are register indices `n : ℕ` with values read by `dref`
(see the canonical `RegisterStructure` instance). -/
abbrev State (E : Type*) := Assignment E

/-- Register lookup as a dref: Muskens' type `se`, picking out the value
stored at position `n`. -/
def dref {E : Type*} (n : Nat) : DynamicSemantics.Dref (State E) E :=
  fun r => r n

/-- Dynamic proposition (box, type `s(st)`): the relational `Update`
specialized to CDRT states. -/
abbrev DProp (E : Type*) := Update (State E)

end CDRT
