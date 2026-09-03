import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.UpperLower.Closure
import Mathlib.Tactic.DeriveFintype

/-!
# Root kind signatures

The root typology of [beavers-koontz-garboden-2020] (§5.4.1) records which of
four kinds of lexical entailment a root carries — state, manner, result, cause —
under two collocational restrictions, that a change entails a state and a cause
entails a change. The restrictions are the partial order `state ≤ result ≤ cause`
on `Root.Kind`, with `manner` isolated. A root's kind signature is a
`Finset Root.Kind`; it is well-formed when it is a lower set of that order, and
`close` sends any signature to its lower closure. The named signatures are the
attested rows of the typology's display (12), and `changeType` is
[beavers-etal-2021]'s coarsening of the change-of-state rows into
property-concept roots, which name a state, and result roots, whose state
entails a prior change.

## Main declarations

* `Root.Kind`, with the collocational `PartialOrder`
* `Root.Kinds`, `Root.Kinds.close`, `Root.Kinds.WellFormed`
* `Root.Kinds.propertyConcept`, `pureResult`, `causativeResult`, `pureManner`,
  `fullSpec`
* `Root.ChangeType`, `Root.Kinds.changeType` — property-concept or result root

## References

* [beavers-koontz-garboden-2020]: The Roots of Verbal Meaning.
* [beavers-etal-2021]: States and changes of state.
-/

namespace Semantics

/-! ### Kinds -/

/-- The kinds of lexical entailment in the root typology of
[beavers-koontz-garboden-2020]. -/
inductive Root.Kind where
  | state
  | manner
  | result
  | cause
  deriving DecidableEq, Fintype, Repr

namespace Root.Kind

/-- The collocational order, `state ≤ result ≤ cause` with `manner` isolated, since a
change entails a state and a cause entails a change. -/
protected inductive LE : Kind → Kind → Prop
  | refl (a) : Kind.LE a a
  | state_result : Kind.LE state result
  | state_cause : Kind.LE state cause
  | result_cause : Kind.LE result cause

instance : LE Kind := ⟨Kind.LE⟩

instance : DecidableLE Kind := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

instance : PartialOrder Kind where
  le_refl := .refl
  le_trans := by decide
  le_antisymm := by decide

end Root.Kind

/-! ### Signatures -/

/-- A root kind signature, the set of kinds a root carries. -/
abbrev Root.Kinds := Finset Root.Kind

namespace Root.Kinds

open Finset

variable {s t : Kinds}

/-- The collocational closure of a signature, its lower closure in the kind order. -/
def close (s : Kinds) : Kinds := univ.filter (∃ j ∈ s, · ≤ j)

@[simp] theorem mem_close {k : Kind} : k ∈ close s ↔ ∃ j ∈ s, k ≤ j := by simp [close]

@[simp] theorem coe_close (s : Kinds) : (close s : Set Kind) = lowerClosure (s : Set Kind) := by
  ext; simp

theorem subset_close (s : Kinds) : s ⊆ close s := fun k hk => mem_close.2 ⟨k, hk, le_rfl⟩

theorem close_mono (h : s ⊆ t) : close s ⊆ close t := by
  simp only [subset_iff, mem_close] at h ⊢
  exact fun k ⟨j, hj, hkj⟩ => ⟨j, h hj, hkj⟩

theorem close_close (s : Kinds) : close (close s) = close s :=
  coe_injective <| by simp

/-- A signature is well-formed if it respects the collocational restrictions, that is,
if it is a lower set of the kind order. -/
def WellFormed (s : Kinds) : Prop := IsLowerSet (s : Set Kind)

instance : DecidablePred WellFormed := fun s =>
  inferInstanceAs (Decidable (∀ a b : Kind, b ≤ a → a ∈ s → b ∈ s))

theorem wellFormed_iff_close_eq : s.WellFormed ↔ close s = s := by
  rw [WellFormed, ← lowerClosure_eq, ← coe_close, coe_inj]

theorem close_wellFormed (s : Kinds) : (close s).WellFormed := by
  rw [WellFormed, coe_close]; exact (lowerClosure _).lower

/-! ### The attested rows of the typology -/

/-- The signature of property-concept roots (√flat). -/
def propertyConcept : Kinds := {.state}

/-- The signature of result roots without causation (√blossom). -/
def pureResult : Kinds := {.state, .result}

/-- The signature of caused-result roots (√crack). -/
def causativeResult : Kinds := {.state, .result, .cause}

/-- The signature of pure manner roots (√jog). -/
def pureManner : Kinds := {.manner}

/-- The signature of roots carrying every kind (√hand, √drown). -/
def fullSpec : Kinds := univ

end Root.Kinds

/-! ### Change type -/

/-- The two types of change-of-state root, property-concept roots naming a gradable
property (√flat, √red) and result roots naming the state an event brings about
(√crack, √shatter) ([beavers-etal-2021] §3.1). -/
inductive Root.ChangeType where
  | propertyConcept
  | result
  deriving DecidableEq, Repr

/-- The change type of a signature, `result` when it carries `result`,
`propertyConcept` when it carries `state` but not `result`, and undefined for
signatures naming no state. -/
def Root.Kinds.changeType (s : Root.Kinds) : Option Root.ChangeType :=
  if Root.Kind.result ∈ s then some .result
  else if Root.Kind.state ∈ s then some .propertyConcept
  else none

theorem Root.Kinds.changeType_eq_some_result {s : Root.Kinds} :
    s.changeType = some .result ↔ Root.Kind.result ∈ s := by
  unfold Root.Kinds.changeType; split_ifs <;> simp_all

theorem Root.Kinds.changeType_eq_some_propertyConcept {s : Root.Kinds} :
    s.changeType = some .propertyConcept ↔ Root.Kind.state ∈ s ∧ Root.Kind.result ∉ s := by
  unfold Root.Kinds.changeType; split_ifs <;> simp_all

end Semantics
