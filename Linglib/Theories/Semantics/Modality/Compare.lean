/-
Modal Theory Comparison: Kratzer vs Simple semantics.

Kratzer with empty ordering source is equivalent to Simple; they diverge
when the ordering source is non-empty.

- Kratzer, A. (1991). Modality. In Semantics: An International Handbook.
- Portner, P. (2009). Modality. Oxford University Press.
-/

import Linglib.Theories.Semantics.Modality.Kratzer
import Linglib.Theories.Semantics.Modality.Simple

namespace IntensionalSemantics.Modal

open IntensionalSemantics.Attitude.Intensional
open IntensionalSemantics.Modal.Kratzer

section ComparisonFunctions

/-- Do two theories agree on modal force `f` for proposition `p` at world `w`? -/
def theoriesAgreeAt (T₁ T₂ : ModalTheory) (f : ModalForce) (p : Proposition) (w : World) : Bool :=
  T₁.eval f p w == T₂.eval f p w

/-- Do two theories agree on modal force `f` for proposition `p` across all worlds? -/
def theoriesAgreeOn (T₁ T₂ : ModalTheory) (f : ModalForce) (p : Proposition) : Bool :=
  allWorlds'.all λ w => theoriesAgreeAt T₁ T₂ f p w

/-- Find worlds where two theories diverge. -/
def divergingWorlds (T₁ T₂ : ModalTheory) (f : ModalForce) (p : Proposition) : List World :=
  allWorlds'.filter λ w => !theoriesAgreeAt T₁ T₂ f p w

/-- Do two theories agree on all modal forces for proposition `p`? -/
def theoriesAgreeOnProposition (T₁ T₂ : ModalTheory) (p : Proposition) : Bool :=
  theoriesAgreeOn T₁ T₂ .necessity p && theoriesAgreeOn T₁ T₂ .possibility p

end ComparisonFunctions

section CoreEquivalence

/-- Minimal Kratzer = Universal Simple for necessity on raining. -/
theorem minimal_kratzer_equals_universal_simple_necessity :
    ∀ (w : World), KratzerMinimal.eval .necessity raining w = SimpleUniversal.eval .necessity raining w := by
  intro w
  cases w <;> native_decide

theorem minimal_kratzer_equals_universal_simple_possibility :
    ∀ (w : World), KratzerMinimal.eval .possibility raining w = SimpleUniversal.eval .possibility raining w := by
  intro w
  cases w <;> native_decide

/-- Agreement on trivially true. -/
theorem agree_on_trivially_true :
    theoriesAgreeOnProposition KratzerMinimal SimpleUniversal triviallyTrue = true := by
  native_decide

/-- Agreement on trivially false. -/
theorem agree_on_trivially_false :
    theoriesAgreeOnProposition KratzerMinimal SimpleUniversal triviallyFalse = true := by
  native_decide

end CoreEquivalence

section Divergence

/-- Epistemic and minimal Kratzer differ on some proposition and world. -/
theorem epistemic_vs_minimal_differ :
    ∃ (p : Proposition) (w : World),
    KratzerEpistemic.eval .necessity p w ≠ KratzerMinimal.eval .necessity p w := by
  use groundWet, .w0
  native_decide

/-- Different conversational backgrounds yield different truth values. -/
theorem kratzer_context_dependence :
    KratzerEpistemic.eval .necessity groundWet .w0 = true ∧
    KratzerMinimal.eval .necessity groundWet .w0 = false := by
  native_decide

end Divergence

section DualityComparison

/-- Both Kratzer and Simple satisfy duality. -/
theorem both_satisfy_duality
    (params : KratzerParams)
    (R : World → World → Bool)
    (p : Proposition)
    (w : World) :
    (KratzerTheory params).dualityHolds p w = true ∧
    (Simple R).dualityHolds p w = true := by
  constructor
  · exact kratzer_duality params p w
  · exact simple_duality R p w

end DualityComparison

section SpecificExamples

/-- Agreement: Minimal Kratzer and Universal Simple agree on necessity for trivially true. -/
theorem agree_on_trivially_true_necessity :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .necessity triviallyTrue = true := by
  native_decide

/-- Agreement: Both agree on possibility for trivially true. -/
theorem agree_on_trivially_true_possibility :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .possibility triviallyTrue = true := by
  native_decide

/-- Agreement: Both agree on necessity for trivially false. -/
theorem agree_on_trivially_false_necessity :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .necessity triviallyFalse = true := by
  native_decide

end SpecificExamples

end IntensionalSemantics.Modal
