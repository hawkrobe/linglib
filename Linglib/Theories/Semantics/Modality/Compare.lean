/-
Modal Theory Comparison: Kratzer vs Simple semantics.

Kratzer with empty ordering source is equivalent to Simple; they diverge
when the ordering source is non-empty.

- @cite{kratzer-1991}
- Portner, P. (2009). Modality. Oxford University Press.
-/

import Linglib.Theories.Semantics.Modality.Kratzer.Flavor
import Linglib.Theories.Semantics.Modality.Simple

namespace Semantics.Modality

open Semantics.Attitudes.Intensional
open Semantics.Modality.Kratzer

section TestFixtures

/-- Proposition: the ground is wet. True at w0, w1, w3; false at w2. -/
def groundWet : World → Prop := fun w =>
  match w with
  | .w0 | .w1 | .w3 => True
  | .w2 => False

instance : DecidablePred groundWet := fun w => by unfold groundWet; cases w <;> infer_instance

-- Concrete Kratzer configurations for comparison examples

def concreteEpistemicBase : ModalBase World := fun _ => [groundWet]

def concreteEpistemicParams : KratzerParams World where
  base := concreteEpistemicBase
  ordering := emptyBackground

def KratzerEpistemic : ModalTheory := KratzerTheory concreteEpistemicParams

def concreteCircumstantialBase : ModalBase World := fun _ => []
def concreteDeonticOrdering : OrderingSource World := fun _ => [johnHome]

def concreteDeonticParams : KratzerParams World where
  base := concreteCircumstantialBase
  ordering := concreteDeonticOrdering

def KratzerDeontic : ModalTheory := KratzerTheory concreteDeonticParams

end TestFixtures

section ComparisonFunctions

/-- Do two theories agree on modal force `f` for proposition `p` at world `w`? -/
def theoriesAgreeAt (T₁ T₂ : ModalTheory) (f : ModalForce) (p : World → Prop) (w : World) : Prop :=
  T₁.eval f p w ↔ T₂.eval f p w

instance (T₁ T₂ : ModalTheory) (f : ModalForce) (p : World → Prop) [DecidablePred p] (w : World) :
    Decidable (theoriesAgreeAt T₁ T₂ f p w) := by
  unfold theoriesAgreeAt; infer_instance

/-- Do two theories agree on modal force `f` for proposition `p` across all worlds? -/
def theoriesAgreeOn (T₁ T₂ : ModalTheory) (f : ModalForce) (p : World → Prop) : Prop :=
  ∀ w : World, theoriesAgreeAt T₁ T₂ f p w

instance (T₁ T₂ : ModalTheory) (f : ModalForce) (p : World → Prop) [DecidablePred p] :
    Decidable (theoriesAgreeOn T₁ T₂ f p) := by
  unfold theoriesAgreeOn; infer_instance

/-- Find worlds where two theories diverge. -/
def divergingWorlds (T₁ T₂ : ModalTheory) (f : ModalForce) (p : World → Prop) [DecidablePred p] :
    List World :=
  Core.Proposition.FiniteWorlds.worlds.filter
    (fun w => !decide (theoriesAgreeAt T₁ T₂ f p w))

/-- Do two theories agree on all modal forces for proposition `p`? -/
def theoriesAgreeOnProposition (T₁ T₂ : ModalTheory) (p : World → Prop) : Prop :=
  theoriesAgreeOn T₁ T₂ .necessity p ∧
  theoriesAgreeOn T₁ T₂ .weakNecessity p ∧
  theoriesAgreeOn T₁ T₂ .possibility p

instance (T₁ T₂ : ModalTheory) (p : World → Prop) [DecidablePred p] :
    Decidable (theoriesAgreeOnProposition T₁ T₂ p) := by
  unfold theoriesAgreeOnProposition; infer_instance

end ComparisonFunctions

section CoreEquivalence

/-- Minimal Kratzer = Universal Simple for necessity on raining. -/
theorem minimal_kratzer_equals_universal_simple_necessity :
    ∀ (w : World), KratzerMinimal.eval .necessity raining w ↔ SimpleUniversal.eval .necessity raining w := by
  intro w
  cases w <;> decide

theorem minimal_kratzer_equals_universal_simple_possibility :
    ∀ (w : World), KratzerMinimal.eval .possibility raining w ↔ SimpleUniversal.eval .possibility raining w := by
  intro w
  cases w <;> decide

/-- Agreement on trivially true. -/
theorem agree_on_trivially_true :
    theoriesAgreeOnProposition KratzerMinimal SimpleUniversal triviallyTrue := by
  decide

/-- Agreement on trivially false. -/
theorem agree_on_trivially_false :
    theoriesAgreeOnProposition KratzerMinimal SimpleUniversal triviallyFalse := by
  decide

end CoreEquivalence

section Divergence

/-- Epistemic and minimal Kratzer differ on some proposition and world. -/
theorem epistemic_vs_minimal_differ :
    ∃ (p : World → Prop) (w : World),
    KratzerEpistemic.eval .necessity p w ≠ KratzerMinimal.eval .necessity p w := by
  refine ⟨groundWet, .w0, ?_⟩
  intro h
  have h1 : KratzerEpistemic.eval .necessity groundWet .w0 := by decide
  have h2 : ¬ KratzerMinimal.eval .necessity groundWet .w0 := by decide
  exact h2 (h ▸ h1)

/-- Different conversational backgrounds yield different truth values. -/
theorem kratzer_context_dependence :
    KratzerEpistemic.eval .necessity groundWet .w0 ∧
    ¬ KratzerMinimal.eval .necessity groundWet .w0 := by
  decide

end Divergence

section DualityComparison

/-- Both Kratzer and Simple satisfy duality. -/
theorem both_satisfy_duality
    (params : KratzerParams World)
    (R : Core.IntensionalLogic.RestrictedModality.AccessRel World) [DecidableRel R]
    (p : World → Prop)
    (w : World) :
    (KratzerTheory params).dualityHolds p w ∧
    (Simple R).dualityHolds p w := by
  refine ⟨kratzerTheory_duality params p w, simple_duality R p w⟩

end DualityComparison

section SpecificExamples

/-- Agreement: Minimal Kratzer and Universal Simple agree on necessity for trivially true. -/
theorem agree_on_trivially_true_necessity :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .necessity triviallyTrue := by
  decide

/-- Agreement: Both agree on possibility for trivially true. -/
theorem agree_on_trivially_true_possibility :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .possibility triviallyTrue := by
  decide

/-- Agreement: Both agree on necessity for trivially false. -/
theorem agree_on_trivially_false_necessity :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .necessity triviallyFalse := by
  decide

end SpecificExamples

end Semantics.Modality
