import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Finite-world test fixture for entailment

Thin shim over `Set` / `compl` / `∩` / `∪` from mathlib, specialized to a
4-element `World` enum. Consumers in `Linglib.Semantics.Entailment.*` use
the `World` type + a handful of test propositions to write `by decide`
test cases for monotonicity, polarity, and presupposition machinery.

The general (polymorphic) monotonicity theorems live in
`Linglib.Semantics.Quantification.Quantifier` (`every_scope_up`,
`some_scope_up`, `no_scope_down`, `every_restrictor_down`). This file
provides only the finite-world fixture.

Reference: @cite{van-benthem-1986}, @cite{ladusaw-1980},
@cite{barwise-cooper-1981}.
-/

namespace Semantics.Entailment

/-- A small finite set of worlds for decidable reasoning. -/
inductive World where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr

def allWorlds : List World := [.w0, .w1, .w2, .w3]

instance : Fintype World where
  elems := {.w0, .w1, .w2, .w3}
  complete := fun w => by cases w <;> decide

/-- Semantic entailment: thin alias for `Set` inclusion (`p ⊆ q`). -/
def entails : Set World → Set World → Prop := (· ⊆ ·)

instance (p q : Set World) [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    Decidable (entails p q) :=
  Fintype.decidableForallFintype

/-- Negation: thin alias for set complement. -/
def pnot : Set World → Set World := compl

/-- Conjunction: thin alias for set intersection. -/
def pand : Set World → Set World → Set World := (· ∩ ·)

/-- Disjunction: thin alias for set union. -/
def por : Set World → Set World → Set World := (· ∪ ·)

instance (p : Set World) [DecidablePred (· ∈ p)] : DecidablePred (· ∈ pnot p) :=
  fun w => inferInstanceAs (Decidable (¬ w ∈ p))

instance (p q : Set World) [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    DecidablePred (· ∈ pand p q) :=
  fun w => inferInstanceAs (Decidable (w ∈ p ∧ w ∈ q))

instance (p q : Set World) [DecidablePred (· ∈ p)] [DecidablePred (· ∈ q)] :
    DecidablePred (· ∈ por p q) :=
  fun w => inferInstanceAs (Decidable (w ∈ p ∨ w ∈ q))

/-- Proposition true only in w0. -/
def p0 : Set World := {.w0}

/-- Proposition true in w0 and w1. -/
def p01 : Set World := {.w0, .w1}

/-- Proposition true in w0, w1, w2. -/
def p012 : Set World := {.w0, .w1, .w2}

/-- Proposition true everywhere. -/
def pAll : Set World := Set.univ

/-- Proposition false everywhere. -/
def pNone : Set World := ∅

instance : DecidablePred (· ∈ p0) := fun w => by unfold p0; infer_instance
instance : DecidablePred (· ∈ p01) := fun w => by unfold p01; infer_instance
instance : DecidablePred (· ∈ p012) := fun w => by unfold p012; infer_instance
instance : DecidablePred (· ∈ pAll) := fun _ => isTrue trivial
instance : DecidablePred (· ∈ pNone) := fun _ => isFalse not_false

theorem p0_entails_p01 : entails p0 p01 := by decide
theorem p01_entails_p012 : entails p01 p012 := by decide

end Semantics.Entailment
