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
open Core.IntensionalLogic.RestrictedModality

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

noncomputable def KratzerEpistemic : ModalTheory := KratzerTheory concreteEpistemicParams

def concreteCircumstantialBase : ModalBase World := fun _ => []
def concreteDeonticOrdering : OrderingSource World := fun _ => [johnHome]

def concreteDeonticParams : KratzerParams World where
  base := concreteCircumstantialBase
  ordering := concreteDeonticOrdering

noncomputable def KratzerDeontic : ModalTheory := KratzerTheory concreteDeonticParams

end TestFixtures

section ComparisonFunctions

/-- Do two theories agree on modal force `f` for proposition `p` at world `w`? -/
def theoriesAgreeAt (T₁ T₂ : ModalTheory) (f : ModalForce) (p : World → Prop) (w : World) : Prop :=
  T₁.eval f p w ↔ T₂.eval f p w

/-- Do two theories agree on modal force `f` for proposition `p` across all worlds? -/
def theoriesAgreeOn (T₁ T₂ : ModalTheory) (f : ModalForce) (p : World → Prop) : Prop :=
  ∀ w : World, theoriesAgreeAt T₁ T₂ f p w

/-- Do two theories agree on all modal forces for proposition `p`? -/
def theoriesAgreeOnProposition (T₁ T₂ : ModalTheory) (p : World → Prop) : Prop :=
  theoriesAgreeOn T₁ T₂ .necessity p ∧
  theoriesAgreeOn T₁ T₂ .weakNecessity p ∧
  theoriesAgreeOn T₁ T₂ .possibility p

end ComparisonFunctions

section CoreEquivalence

/-- KratzerMinimal necessity reduces to ∀-quantification over all worlds. -/
private theorem kratzerMinimal_necessity_iff (p : World → Prop) (w : World) :
    KratzerMinimal.eval .necessity p w ↔ ∀ w' : World, p w' := by
  show Kratzer.necessity (W := World) emptyBackground emptyBackground p w ↔ _
  rw [Kratzer.necessity_iff_all, Kratzer.empty_ordering_emptyBackground,
      Kratzer.empty_base_universal_access]
  exact ⟨fun h w' => h w' (Set.mem_univ _), fun h w' _ => h w'⟩

/-- KratzerMinimal possibility reduces to ∃-quantification over all worlds. -/
private theorem kratzerMinimal_possibility_iff (p : World → Prop) (w : World) :
    KratzerMinimal.eval .possibility p w ↔ ∃ w' : World, p w' := by
  show Kratzer.possibility (W := World) emptyBackground emptyBackground p w ↔ _
  rw [Kratzer.possibility_iff_any, Kratzer.empty_ordering_emptyBackground,
      Kratzer.empty_base_universal_access]
  exact ⟨fun ⟨w', _, h⟩ => ⟨w', h⟩, fun ⟨w', h⟩ => ⟨w', Set.mem_univ _, h⟩⟩

/-- KratzerMinimal weak-necessity coincides with necessity. -/
private theorem kratzerMinimal_weakNec_iff (p : World → Prop) (w : World) :
    KratzerMinimal.eval .weakNecessity p w ↔ ∀ w' : World, p w' :=
  kratzerMinimal_necessity_iff p w

/-- Minimal Kratzer = Universal Simple for necessity on raining. -/
theorem minimal_kratzer_equals_universal_simple_necessity :
    ∀ (w : World), KratzerMinimal.eval .necessity raining w ↔
      SimpleUniversal.eval .necessity raining w := fun w =>
  (kratzerMinimal_necessity_iff raining w).trans (simple_universal_necessity raining w).symm

theorem minimal_kratzer_equals_universal_simple_possibility :
    ∀ (w : World), KratzerMinimal.eval .possibility raining w ↔
      SimpleUniversal.eval .possibility raining w := fun w =>
  (kratzerMinimal_possibility_iff raining w).trans (simple_universal_possibility raining w).symm

/-- Agreement on trivially true. -/
theorem agree_on_trivially_true :
    theoriesAgreeOnProposition KratzerMinimal SimpleUniversal triviallyTrue := by
  refine ⟨?_, ?_, ?_⟩ <;> intro w <;> show _ ↔ _
  · exact (kratzerMinimal_necessity_iff _ w).trans (simple_universal_necessity _ w).symm
  · exact (kratzerMinimal_weakNec_iff _ w).trans (simple_universal_necessity _ w).symm
  · exact (kratzerMinimal_possibility_iff _ w).trans (simple_universal_possibility _ w).symm

/-- Agreement on trivially false. -/
theorem agree_on_trivially_false :
    theoriesAgreeOnProposition KratzerMinimal SimpleUniversal triviallyFalse := by
  refine ⟨?_, ?_, ?_⟩ <;> intro w <;> show _ ↔ _
  · exact (kratzerMinimal_necessity_iff _ w).trans (simple_universal_necessity _ w).symm
  · exact (kratzerMinimal_weakNec_iff _ w).trans (simple_universal_necessity _ w).symm
  · exact (kratzerMinimal_possibility_iff _ w).trans (simple_universal_possibility _ w).symm

end CoreEquivalence

section Divergence

/-- KratzerEpistemic necessity reduces to ∀-quantification over groundWet worlds. -/
private theorem kratzerEpistemic_necessity_iff (p : World → Prop) (w : World) :
    KratzerEpistemic.eval .necessity p w ↔ ∀ w' : World, groundWet w' → p w' := by
  show Kratzer.necessity (W := World) concreteEpistemicBase emptyBackground p w ↔ _
  rw [Kratzer.necessity_iff_all, Kratzer.empty_ordering_emptyBackground]
  constructor
  · intro h w' hw
    apply h w'
    intro q hq
    simp [concreteEpistemicBase] at hq
    rcases hq with rfl
    exact hw
  · intro h w' hw'
    apply h w'
    have : groundWet ∈ concreteEpistemicBase w := by simp [concreteEpistemicBase]
    exact hw' groundWet this

/-- Epistemic and minimal Kratzer differ on some proposition and world. -/
theorem epistemic_vs_minimal_differ :
    ∃ (p : World → Prop) (w : World),
    KratzerEpistemic.eval .necessity p w ≠ KratzerMinimal.eval .necessity p w := by
  refine ⟨groundWet, .w0, ?_⟩
  intro h
  have h1 : KratzerEpistemic.eval .necessity groundWet .w0 :=
    (kratzerEpistemic_necessity_iff _ _).mpr (fun _ hw => hw)
  have h2 : ¬ KratzerMinimal.eval .necessity groundWet .w0 := by
    intro hAll
    exact (kratzerMinimal_necessity_iff _ _).mp hAll .w2
  exact h2 (h ▸ h1)

/-- Different conversational backgrounds yield different truth values. -/
theorem kratzer_context_dependence :
    KratzerEpistemic.eval .necessity groundWet .w0 ∧
    ¬ KratzerMinimal.eval .necessity groundWet .w0 := by
  refine ⟨?_, ?_⟩
  · exact (kratzerEpistemic_necessity_iff _ _).mpr (fun _ hw => hw)
  · intro hAll
    exact (kratzerMinimal_necessity_iff _ _).mp hAll .w2

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
    theoriesAgreeOn KratzerMinimal SimpleUniversal .necessity triviallyTrue := fun w =>
  (kratzerMinimal_necessity_iff _ w).trans (simple_universal_necessity _ w).symm

/-- Agreement: Both agree on possibility for trivially true. -/
theorem agree_on_trivially_true_possibility :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .possibility triviallyTrue := fun w =>
  (kratzerMinimal_possibility_iff _ w).trans (simple_universal_possibility _ w).symm

/-- Agreement: Both agree on necessity for trivially false. -/
theorem agree_on_trivially_false_necessity :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .necessity triviallyFalse := fun w =>
  (kratzerMinimal_necessity_iff _ w).trans (simple_universal_necessity _ w).symm

end SpecificExamples

end Semantics.Modality
