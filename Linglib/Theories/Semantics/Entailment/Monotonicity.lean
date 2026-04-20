/-
Upward and downward entailing contexts with monotonicity proofs.
UE: A |= B -> f(A) |= f(B). DE: A |= B -> f(B) |= f(A).
Reference: @cite{van-benthem-1986}, @cite{ladusaw-1980}, @cite{barwise-cooper-1981}.
-/

import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Theories.Semantics.Quantification.Quantifier

namespace Semantics.Entailment.Monotonicity

open Semantics.Entailment
open Semantics.Entailment.Polarity (IsUpwardEntailing IsDownwardEntailing)
open Semantics.Quantification.Quantifier

section QuantifierSemantics

/-! ## Bridge to Canonical GQ Denotations

The 4-element `World` type used in the entailment domain doubles as an
entity domain. We create a `Frame` + `Fintype` instance so that the
canonical GQ denotations from `Semantics.Quantification.Quantifier`
(`every_sem`, `some_sem`, `no_sem`) can be instantiated here.

This bridges the entailment-testing infrastructure (finite, decidable)
with the model-theoretic GQ definitions (proved conservative and monotone
for arbitrary finite models).

**Relation to general monotonicity theorems.** The `decide` proofs
below verify monotonicity over the 4-element `World` model. The general
theorems — `every_scope_up`, `no_scope_down`, `every_restrictor_down`,
`some_scope_up` — are proved for arbitrary `Fintype` in
`Quantifier.lean` and `Core.Logic.Quantification`. The results here are
consistent instances of those general proofs.
-/

/-- The entailment World type, viewed as a Frame entity domain. -/
def entailmentModel : Core.IntensionalLogic.Frame :=
  { Entity := World, Index := Unit }

instance : Fintype entailmentModel.Entity where
  elems := ({World.w0, World.w1, World.w2, World.w3} : Finset World)
  complete := fun x => by cases x <;> (unfold entailmentModel; simp)


instance (R S : entailmentModel.Entity → Prop) [DecidablePred R] [DecidablePred S] :
    Decidable (every_sem entailmentModel R S) := by
  unfold every_sem; exact inferInstance

instance (R S : entailmentModel.Entity → Prop) [DecidablePred R] [DecidablePred S] :
    Decidable (some_sem entailmentModel R S) := by
  unfold some_sem; exact inferInstance

instance (R S : entailmentModel.Entity → Prop) [DecidablePred R] [DecidablePred S] :
    Decidable (no_sem entailmentModel R S) := by
  unfold no_sem; exact inferInstance

/-- "Every A is B" — delegates to canonical `every_sem`. -/
def every (a b : Set World) : Prop :=
  every_sem entailmentModel a b

/-- "Some A is B" — delegates to canonical `some_sem`. -/
def some' (a b : Set World) : Prop :=
  some_sem entailmentModel a b

/-- "No A is B" — delegates to canonical `no_sem`. -/
def no (a b : Set World) : Prop :=
  no_sem entailmentModel a b

def fixedRestr : Set World := p01

/-- "Every student" as a function of scope. -/
def every_scope : Set World → Set World :=
  λ scope => λ _ => every fixedRestr scope

/-- "Some student" as a function of scope. -/
def some_scope : Set World → Set World :=
  λ scope => λ _ => some' fixedRestr scope

/-- "No student" as a function of scope. -/
def no_scope : Set World → Set World :=
  λ scope => λ _ => no fixedRestr scope

/-- "Every" is UE in scope. -/
theorem every_scope_UE : IsUpwardEntailing every_scope := by
  intro p q hpq _w h x hr
  exact hpq (h x hr)

/-- "Some" is UE in scope. -/
theorem some_scope_UE : IsUpwardEntailing some_scope := by
  intro p q hpq _w h
  obtain ⟨x, hr, hp⟩ := h
  exact ⟨x, hr, hpq hp⟩

/-- "No" is DE in scope. -/
theorem no_scope_DE : IsDownwardEntailing no_scope := by
  intro p q hpq _w h x hr hp
  exact h x hr (hpq hp)

/-- Fixed scope for testing restrictor monotonicity. -/
def fixedScope : Set World := p012

/-- "Every ___ smokes" as a function of restrictor. -/
def every_restr : Set World → Set World :=
  λ restr => λ _ => every restr fixedScope

/-- "Every" is DE in restrictor. -/
theorem every_restr_DE : IsDownwardEntailing every_restr := by
  intro p q hpq _w h x hr
  exact h x (hpq hr)

end QuantifierSemantics

end Semantics.Entailment.Monotonicity
