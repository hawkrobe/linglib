/-
Simple (Kripke) Modal Semantics.

`(Simple R).eval .necessity p w = ∀ v, R w v → p v`;
`(Simple R).eval .possibility p w = ∃ v, R w v ∧ p v`.
Accessibility is a primitive Prop-valued relation; this is a thin
wrapper over `Core.IntensionalLogic.RestrictedModality.boxR`/`diamondR`,
which is the single source of truth for accessibility-restricted modal logic.

- @cite{kripke-1963}
-/

import Linglib.Theories.Semantics.Modality.Basic
import Linglib.Core.IntensionalLogic.RestrictedModality

namespace Semantics.Modality

open Semantics.Attitudes.Intensional
open Core.IntensionalLogic.RestrictedModality

/-- Construct a simple modal theory from accessibility relation `R`.
    Necessity = `boxR R`, possibility = `diamondR R`. -/
def Simple (R : AccessRel World) [DecidableRel R] : ModalTheory where
  name := "Simple"
  citation := "Kripke 1963"
  eval := fun force p w =>
    match force with
    | .necessity | .weakNecessity => boxR R p w
    | .possibility => diamondR R p w
  decEval := fun force p _ w => by
    cases force <;> · unfold boxR diamondR <;> infer_instance

section AccessibilityRelations

/-- Sample epistemic accessibility: w0↔w2, w1↔w3. -/
def sampleEpistemicR : AccessRel World := fun w w' =>
  match w, w' with
  | .w0, .w0 | .w0, .w2 | .w2, .w0 | .w2, .w2
  | .w1, .w1 | .w1, .w3 | .w3, .w1 | .w3, .w3 => True
  | _, _ => False

instance : DecidableRel sampleEpistemicR := fun w w' => by
  unfold sampleEpistemicR
  cases w <;> cases w' <;> infer_instance

/-- Sample deontic accessibility: ideal worlds w0, w2 accessible from anywhere. -/
def sampleDeonticR : AccessRel World := fun _ w' => w' = .w0 ∨ w' = .w2

instance : DecidableRel sampleDeonticR := fun _ w' => by
  unfold sampleDeonticR; infer_instance

instance : DecidableRel (universalR (W := World)) := fun _ _ => isTrue trivial
instance : DecidableRel (emptyR (W := World)) := fun _ _ => isFalse (fun h => h)
instance : DecidableRel (identityR (W := World)) := fun w v => decEq w v

end AccessibilityRelations

section InstantiatedTheories

/-- Simple theory with universal accessibility (S5-like). -/
def SimpleUniversal : ModalTheory := Simple universalR

/-- Simple theory with reflexive-only accessibility (T-like). -/
def SimpleReflexive : ModalTheory := Simple identityR

/-- Simple epistemic theory. -/
def SimpleEpistemic : ModalTheory := Simple sampleEpistemicR

/-- Simple deontic theory. -/
def SimpleDeontic : ModalTheory := Simple sampleDeonticR

end InstantiatedTheories

section TestPropositions

/-- Proposition: it is raining. True at w0, w1; false at w2, w3. -/
def raining : World → Prop := fun w =>
  match w with
  | .w0 | .w1 => True
  | .w2 | .w3 => False

instance : DecidablePred raining := fun w => by unfold raining; cases w <;> infer_instance

/-- Proposition: John is home. True at w0, w2; false at w1, w3. -/
def johnHome : World → Prop := fun w =>
  match w with
  | .w0 | .w2 => True
  | .w1 | .w3 => False

instance : DecidablePred johnHome := fun w => by unfold johnHome; cases w <;> infer_instance

/-- A trivially true proposition (true at all worlds). -/
def triviallyTrue : World → Prop := fun _ => True

instance : DecidablePred triviallyTrue := fun _ => by unfold triviallyTrue; infer_instance

/-- A trivially false proposition (false at all worlds). -/
def triviallyFalse : World → Prop := fun _ => False

instance : DecidablePred triviallyFalse := fun _ => by unfold triviallyFalse; infer_instance

end TestPropositions

section KeyProperties

/-- With universal accessibility, necessity means truth at all worlds. -/
theorem simple_universal_necessity (p : World → Prop) (w : World) :
    SimpleUniversal.eval .necessity p w ↔ ∀ w' : World, p w' := by
  show boxR universalR p w ↔ ∀ w' : World, p w'
  unfold boxR universalR
  exact ⟨fun h v => h v trivial, fun h v _ => h v⟩

/-- With universal accessibility, possibility means truth at some world. -/
theorem simple_universal_possibility (p : World → Prop) (w : World) :
    SimpleUniversal.eval .possibility p w ↔ ∃ w' : World, p w' := by
  show diamondR universalR p w ↔ ∃ w' : World, p w'
  unfold diamondR universalR
  exact ⟨fun ⟨v, _, h⟩ => ⟨v, h⟩, fun ⟨v, h⟩ => ⟨v, trivial, h⟩⟩

/-- With reflexive-only accessibility, □p at w → p w (for concrete propositions). -/
theorem simple_reflexive_necessity_raining (w : World) :
    SimpleReflexive.eval .necessity raining w → raining w := by
  cases w <;> decide

theorem simple_reflexive_necessity_johnHome (w : World) :
    SimpleReflexive.eval .necessity johnHome w → johnHome w := by
  cases w <;> decide

end KeyProperties

section Duality

/-- Simple theories satisfy modal duality: □p ↔ ¬◇¬p.
    Inherited directly from `boxR_neg_diamondR`. -/
theorem simple_duality (R : AccessRel World) [DecidableRel R]
    (p : World → Prop) (w : World) :
    (Simple R).dualityHolds p w := by
  show (Simple R).necessity p w ↔ ¬ (Simple R).possibility _ w
  unfold ModalTheory.necessity ModalTheory.possibility Simple
  exact iff_of_eq (boxR_neg_diamondR R p w)

end Duality

section Examples

#guard decide (¬ SimpleUniversal.eval .necessity raining .w0)
#guard decide (SimpleUniversal.eval .possibility raining .w0)
#guard decide (SimpleReflexive.eval .necessity raining .w0)
#guard decide (¬ SimpleReflexive.eval .necessity raining .w2)

/-- Consistency (□p → ◇p) holds with universal accessibility. -/
theorem simple_universal_consistent_raining (w : World) :
    SimpleUniversal.necessityEntailsPossibility raining w := by
  cases w <;> decide

theorem simple_universal_consistent_johnHome (w : World) :
    SimpleUniversal.necessityEntailsPossibility johnHome w := by
  cases w <;> decide

theorem simple_universal_consistent_triviallyTrue (w : World) :
    SimpleUniversal.necessityEntailsPossibility triviallyTrue w := by
  cases w <;> decide

end Examples

section Normality

/-- All Simple theories are normal modal logics. -/
theorem simple_isNormal (R : AccessRel World) [DecidableRel R] : (Simple R).isNormal :=
  fun p w => simple_duality R p w

/-- Corollary: SimpleUniversal is normal. -/
theorem simpleUniversal_isNormal : SimpleUniversal.isNormal :=
  simple_isNormal universalR

/-- Corollary: SimpleReflexive is normal. -/
theorem simpleReflexive_isNormal : SimpleReflexive.isNormal :=
  simple_isNormal identityR

end Normality

/-! Kripke correspondence: R properties correspond to modal axioms.
    Derived from `boxR_T`/`boxR_D`/`boxR_K` in `Core.IntensionalLogic.RestrictedModality`. -/

section TAxiom

/-- T Axiom: reflexive R implies □p → p. -/
theorem T_axiom_from_reflexivity (R : AccessRel World) [DecidableRel R] (hRefl : Refl R)
    (p : World → Prop) (w : World)
    (hNec : (Simple R).eval .necessity p w) : p w :=
  boxR_T R hRefl p w hNec

/-- Reflexive accessibility gives T axiom: □p → p. -/
theorem reflexive_implies_T (R : AccessRel World) [DecidableRel R] (hRefl : Refl R) :
    ∀ (p : World → Prop) (w : World),
    (Simple R).eval .necessity p w → p w :=
  fun p w => T_axiom_from_reflexivity R hRefl p w

end TAxiom

section DAxiom

/-- D Axiom: serial R implies □p → ◇p. -/
theorem D_axiom_from_seriality (R : AccessRel World) [DecidableRel R] (hSerial : Serial R)
    (p : World → Prop) (w : World)
    (hNec : (Simple R).eval .necessity p w) :
    (Simple R).eval .possibility p w :=
  boxR_D R hSerial p w hNec

/-- Serial accessibility gives D axiom: □p → ◇p. -/
theorem serial_implies_D (R : AccessRel World) [DecidableRel R] (hSerial : Serial R) :
    ∀ (p : World → Prop) (w : World),
    (Simple R).eval .necessity p w → (Simple R).eval .possibility p w :=
  fun p w => D_axiom_from_seriality R hSerial p w

end DAxiom

section ConsistencyFromD

/-- Universal accessibility gives consistency via D axiom. -/
theorem simple_universal_isConsistent_from_D (p : World → Prop) (w : World) :
    SimpleUniversal.necessityEntailsPossibility p w :=
  D_axiom_from_seriality universalR universalR_serial p w

end ConsistencyFromD

section KAxiom

/-- Material implication as a proposition. -/
def pImpl (p q : World → Prop) : World → Prop := fun w => p w → q w

instance (p q : World → Prop) [DecidablePred p] [DecidablePred q] :
    DecidablePred (pImpl p q) :=
  fun w => by unfold pImpl; infer_instance

/-- K Axiom: □(p → q) → (□p → □q). Holds for any R.
    Derived from `boxR_K`. -/
theorem K_axiom (R : AccessRel World) [DecidableRel R] (p q : World → Prop) (w : World)
    (hImpl : (Simple R).eval .necessity (pImpl p q) w)
    (hP : (Simple R).eval .necessity p w) :
    (Simple R).eval .necessity q w :=
  boxR_K R p q w hImpl hP

/-- K axiom holds for all Simple theories unconditionally. -/
theorem simple_K_axiom (R : AccessRel World) [DecidableRel R] :
    ∀ (p q : World → Prop) (w : World),
    (Simple R).eval .necessity (pImpl p q) w →
    (Simple R).eval .necessity p w →
    (Simple R).eval .necessity q w :=
  fun p q w => K_axiom R p q w

end KAxiom

end Semantics.Modality
