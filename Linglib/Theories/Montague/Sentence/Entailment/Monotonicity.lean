/-
Upward and downward entailing contexts with monotonicity proofs.
UE: A |= B -> f(A) |= f(B). DE: A |= B -> f(B) |= f(A).
Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981).
-/

import Linglib.Theories.Montague.Sentence.Entailment.Basic

namespace Montague.Sentence.Entailment.Monotonicity

open Montague.Sentence.Entailment

section Monotonicity

/-- Check if f is upward entailing on given test cases. -/
def isUpwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f p) (f q)

/-- Check if f is downward entailing on given test cases. -/
def isDownwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f q) (f p)

/-- Negation is DE: if P |= Q, then not Q |= not P. -/
theorem negation_is_DE : isDownwardEntailing pnot testCases = true := by
  native_decide

/-- p0 |= p01, so not p01 |= not p0. -/
theorem negation_reverses_example :
    entails p0 p01 = true ∧
    entails (pnot p01) (pnot p0) = true := by
  native_decide

/-- Conjunction (second arg) is UE: P |= Q -> (R & P) |= (R & Q). -/
theorem conjunction_second_UE : isUpwardEntailing (pand p01) testCases = true := by
  native_decide

/-- Disjunction (second arg) is UE: P |= Q -> (R | P) |= (R | Q). -/
theorem disjunction_second_UE : isUpwardEntailing (por p01) testCases = true := by
  native_decide

end Monotonicity

section QuantifierSemantics

/-- "Every A is B" = forall x. A(x) -> B(x). -/
def every (a b : World → Bool) : Bool :=
  allWorlds.all λ x => !a x || b x

/-- "Some A is B" = exists x. A(x) & B(x). -/
def some' (a b : World → Bool) : Bool :=
  allWorlds.any λ x => a x && b x

/-- "No A is B" = forall x. A(x) -> not B(x). -/
def no (a b : World → Bool) : Bool :=
  allWorlds.all λ x => !a x || !b x

def fixedRestr : Prop' := p01

/-- "Every student" as a function of scope. -/
def every_scope : Prop' → Prop' :=
  λ scope => λ _ => every fixedRestr scope

/-- "Some student" as a function of scope. -/
def some_scope : Prop' → Prop' :=
  λ scope => λ _ => some' fixedRestr scope

/-- "No student" as a function of scope. -/
def no_scope : Prop' → Prop' :=
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
def fixedScope : Prop' := p012

/-- "Every ___ smokes" as a function of restrictor. -/
def every_restr : Prop' → Prop' :=
  λ restr => λ _ => every restr fixedScope

/-- "Every" is DE in restrictor. -/
theorem every_restr_DE : isDownwardEntailing every_restr testCases = true := by
  native_decide

/-- DE contexts reverse scalar strength: p0 |= p01 but not p01 |= not p0. -/
theorem de_reverses_strength :
    entails p0 p01 = true ∧
    entails (pnot p01) (pnot p0) = true := by
  native_decide

/-- Material conditional with fixed consequent: "If _, then c". -/
def materialCond (c : Prop') : Prop' → Prop' :=
  λ p => λ w => !p w || c w

/-- Conditional antecedent is DE: P |= Q -> (Q -> C) |= (P -> C). -/
theorem conditional_antecedent_DE :
    isDownwardEntailing (materialCond fixedScope) testCases = true := by
  native_decide

/-- Conditional antecedent DE property verified on all test case pairs. -/
theorem conditional_antecedent_DE_test_cases :
    -- Check all test case pairs satisfy the DE property
    testCases.all (λ (p, q) =>
      !entails p q || entails (materialCond fixedScope q) (materialCond fixedScope p)) = true := by
  native_decide

/-- Consequent position is UE: P |= Q -> (A -> P) |= (A -> Q). -/
theorem implication_consequent_UE : isUpwardEntailing (λ c => materialCond c fixedRestr) testCases = true := by
  native_decide

/-- Antecedent is DE and consequent is UE. -/
theorem conditional_monotonicity_summary :
    isDownwardEntailing (materialCond fixedScope) testCases = true ∧
    isUpwardEntailing (λ c => materialCond c fixedRestr) testCases = true := by
  constructor
  · exact conditional_antecedent_DE
  · exact implication_consequent_UE

end QuantifierSemantics

end Montague.Sentence.Entailment.Monotonicity
