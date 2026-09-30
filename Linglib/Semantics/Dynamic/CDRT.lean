module

public import Linglib.Logic.Assignment
public import Linglib.Semantics.Dynamic.RegisterStructure

/-!
# Compositional DRT

The substrate of [muskens-1996]'s Logic of Change beyond its register axioms, which are
`RegisterStructure` (`Semantics/Dynamic/RegisterStructure.lean`): states are atomic (his type
`s`), discourse referents are functions *from* states (`Dref S E`, his type `se`), atomic
conditions are built from predicates and drefs, and boxes are the relational algebra of
`Update.lean` at the state type. Constant registers (AX4's names) are constant `Dref`s, not
registers: the VAR split of AX2.

## Main definitions

- `Dref S E`: discourse referents, Muskens' type `se`.
- `Condition.atom1`, `Condition.atom2`, `Condition.eq`: atomic conditions from predicates and
  drefs.
- `CDRT.State`, `CDRT.DProp`, `CDRT.dref`: the concrete CDRT instance at
  `State E := Assignment E`.

The compositional fragment (T₀ translations, generalized coordination, the paper's derivations)
and the weakest-precondition calculus live in `Studies/Muskens1996.lean`.

## References

* [R. Muskens, *Combining Montague semantics and discourse representation* (1996)][muskens-1996]
-/

@[expose] public section

namespace DynamicSemantics

/-- Discourse referent (Muskens' type `se`): a function from states to
individuals. Constant drefs (`Function.const`, AX4's names) are drefs
but not registers. -/
abbrev Dref (S E : Type*) := S → E

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
