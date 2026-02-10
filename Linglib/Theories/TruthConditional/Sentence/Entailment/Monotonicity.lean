/-
Upward and downward entailing contexts with monotonicity proofs.
UE: A |= B -> f(A) |= f(B). DE: A |= B -> f(B) |= f(A).
Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981).
-/

import Linglib.Theories.TruthConditional.Sentence.Entailment.Basic
import Linglib.Theories.TruthConditional.Core.Polarity
import Linglib.Theories.TruthConditional.Determiner.Quantifier

namespace TruthConditional.Sentence.Entailment.Monotonicity

open TruthConditional.Sentence.Entailment
open TruthConditional.Core.Polarity (isUpwardEntailing isDownwardEntailing)
open TruthConditional.Determiner.Quantifier

section QuantifierSemantics

/-! ## Bridge to Canonical GQ Denotations

The 4-element `World` type used in the entailment domain doubles as an
entity domain. We create a `Model` + `FiniteModel` instance so that the
canonical GQ denotations from `TruthConditional.Determiner.Quantifier`
(`every_sem`, `some_sem`, `no_sem`) can be instantiated here.

This bridges the entailment-testing infrastructure (finite, decidable)
with the model-theoretic GQ definitions (proved conservative and monotone
for arbitrary finite models).
-/

/-- The entailment World type, viewed as a Model entity domain. -/
def entailmentModel : TruthConditional.Model :=
  { Entity := World, decEq := inferInstance }

instance : FiniteModel entailmentModel where
  elements := allWorlds
  complete := λ x => by cases x <;> simp [allWorlds]

/-- "Every A is B" — delegates to canonical `every_sem`. -/
abbrev every (a b : World → Bool) : Bool := every_sem entailmentModel a b

/-- "Some A is B" — delegates to canonical `some_sem`. -/
abbrev some' (a b : World → Bool) : Bool := some_sem entailmentModel a b

/-- "No A is B" — delegates to canonical `no_sem`. -/
abbrev no (a b : World → Bool) : Bool := no_sem entailmentModel a b

def fixedRestr : BProp World := p01

/-- "Every student" as a function of scope. -/
def every_scope : BProp World → BProp World :=
  λ scope => λ _ => every fixedRestr scope

/-- "Some student" as a function of scope. -/
def some_scope : BProp World → BProp World :=
  λ scope => λ _ => some' fixedRestr scope

/-- "No student" as a function of scope. -/
def no_scope : BProp World → BProp World :=
  λ scope => λ _ => no fixedRestr scope

/-- "Every" is UE in scope. -/
theorem every_scope_UE : isUpwardEntailing every_scope testCases = true := by
  native_decide

/-- "Some" is UE in scope. -/
theorem some_scope_UE : isUpwardEntailing some_scope testCases = true := by
  native_decide

/-- "No" is DE in scope. -/
theorem no_scope_DE : isDownwardEntailing no_scope testCases = true := by
  native_decide

/-- Fixed scope for testing restrictor monotonicity. -/
def fixedScope : BProp World := p012

/-- "Every ___ smokes" as a function of restrictor. -/
def every_restr : BProp World → BProp World :=
  λ restr => λ _ => every restr fixedScope

/-- "Every" is DE in restrictor. -/
theorem every_restr_DE : isDownwardEntailing every_restr testCases = true := by
  native_decide

end QuantifierSemantics

end TruthConditional.Sentence.Entailment.Monotonicity
