/-
Upward and downward entailing contexts with monotonicity proofs.
UE: A |= B -> f(A) |= f(B). DE: A |= B -> f(B) |= f(A).
Reference: van Benthem (1986), Ladusaw (1980), Barwise & Cooper (1981).
-/

import Linglib.Theories.TruthConditional.Sentence.Entailment.Basic
import Linglib.Theories.TruthConditional.Core.Polarity

namespace TruthConditional.Sentence.Entailment.Monotonicity

open TruthConditional.Sentence.Entailment
open TruthConditional.Core.Polarity (isUpwardEntailing isDownwardEntailing)

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
