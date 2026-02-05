/-
Simple (Kripke) Modal Semantics.

□p at w = ∀w'. R(w,w') -> p(w'); ◇p at w = ∃w'. R(w,w') ∧ p(w').
Accessibility is a primitive relation, unlike Kratzer's derived approach.

- Kripke, S. (1963). Semantical Considerations on Modal Logic.
- Hughes, G.E. & Cresswell, M.J. (1996). A New Introduction to Modal Logic.
-/

import Linglib.Theories.Montague.Modal.Basic
import Linglib.Core.ModalLogic

namespace Montague.Modal

open Montague.Verb.Attitude.Examples
open Core.ModalLogic (Refl Serial Trans Symm Eucl)

/-- Construct a simple modal theory from accessibility relation R. -/
def Simple (R : World → World → Bool) : ModalTheory where
  name := "Simple"
  citation := "Kripke 1963"
  eval := λ force p w =>
    let accessible := allWorlds'.filter (R w)
    match force with
    | .necessity => accessible.all p
    | .possibility => accessible.any p

section AccessibilityRelations

/-- Universal accessibility: every world is accessible from every world.
Matches `Core.ModalLogic.universalR`. -/
def universalR : World → World → Bool := Core.ModalLogic.universalR

/-- Reflexive accessibility: each world is accessible from itself.
Matches `Core.ModalLogic.identityR`. -/
def reflexiveR : World → World → Bool := Core.ModalLogic.identityR

/-- Empty accessibility: no world is accessible from any world.
Matches `Core.ModalLogic.emptyR`. -/
def emptyR : World → World → Bool := Core.ModalLogic.emptyR

/-- Sample epistemic accessibility: w0↔w2, w1↔w3. -/
def sampleEpistemicR : World → World → Bool := λ w w' =>
  match w, w' with
  | .w0, .w0 => true | .w0, .w2 => true
  | .w2, .w0 => true | .w2, .w2 => true
  | .w1, .w1 => true | .w1, .w3 => true
  | .w3, .w1 => true | .w3, .w3 => true
  | _, _ => false

/-- Sample deontic accessibility: ideal worlds w0, w2 accessible from anywhere. -/
def sampleDeonticR : World → World → Bool := λ _ w' =>
  w' == .w0 || w' == .w2

end AccessibilityRelations

section InstantiatedTheories

/-- Simple theory with universal accessibility (S5-like). -/
def SimpleUniversal : ModalTheory := Simple universalR

/-- Simple theory with reflexive-only accessibility (T-like). -/
def SimpleReflexive : ModalTheory := Simple reflexiveR

/-- Simple epistemic theory. -/
def SimpleEpistemic : ModalTheory := Simple sampleEpistemicR

/-- Simple deontic theory. -/
def SimpleDeontic : ModalTheory := Simple sampleDeonticR

end InstantiatedTheories

section KeyProperties

/-- With universal accessibility, necessity means truth at all worlds. -/
theorem simple_universal_necessity :
    ∀ (p : Proposition) (w : World),
    SimpleUniversal.eval .necessity p w = allWorlds'.all p := by
  intro p w
  unfold SimpleUniversal Simple universalR allWorlds'
  rfl

/-- With universal accessibility, possibility means truth at some world. -/
theorem simple_universal_possibility :
    ∀ (p : Proposition) (w : World),
    SimpleUniversal.eval .possibility p w = allWorlds'.any p := by
  intro p w
  unfold SimpleUniversal Simple universalR allWorlds'
  rfl

/-- With reflexive-only accessibility, □p at w = p w (for concrete propositions). -/
theorem simple_reflexive_necessity_raining :
    ∀ (w : World), SimpleReflexive.eval .necessity raining w = raining w := by
  intro w
  cases w <;> native_decide

theorem simple_reflexive_necessity_johnHome :
    ∀ (w : World), SimpleReflexive.eval .necessity johnHome w = johnHome w := by
  intro w
  cases w <;> native_decide

end KeyProperties

section Duality

/-- Helper: duality holds for any list. -/
private theorem list_duality (L : List World) (p : Proposition) :
    (L.all p == !L.any λ w' => !p w') = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

/-- Simple theories satisfy modal duality: □p ↔ ¬◇¬p. -/
theorem simple_duality (R : World → World → Bool) (p : Proposition) (w : World) :
    (Simple R).dualityHolds p w = true := by
  unfold ModalTheory.dualityHolds Simple ModalTheory.necessity ModalTheory.possibility
  exact list_duality (allWorlds'.filter (R w)) p

end Duality

section Examples

#eval SimpleUniversal.eval .necessity raining .w0  -- false
#eval SimpleUniversal.eval .possibility raining .w0  -- true
#eval SimpleReflexive.eval .necessity raining .w0  -- true
#eval SimpleReflexive.eval .necessity raining .w2  -- false

/-- Consistency (□p -> ◇p) holds with universal accessibility. -/
theorem simple_universal_consistent_raining :
    ∀ (w : World), (SimpleUniversal.necessityEntailsPossibility raining w) = true := by
  intro w
  cases w <;> native_decide

theorem simple_universal_consistent_johnHome :
    ∀ (w : World), (SimpleUniversal.necessityEntailsPossibility johnHome w) = true := by
  intro w
  cases w <;> native_decide

theorem simple_universal_consistent_triviallyTrue :
    ∀ (w : World), (SimpleUniversal.necessityEntailsPossibility triviallyTrue w) = true := by
  intro w
  cases w <;> native_decide

end Examples

section Normality

/-- All Simple theories are normal modal logics. -/
theorem simple_isNormal (R : World → World → Bool) : (Simple R).isNormal :=
  λ p w => simple_duality R p w

/-- Corollary: SimpleUniversal is normal. -/
theorem simpleUniversal_isNormal : SimpleUniversal.isNormal :=
  simple_isNormal universalR

/-- Corollary: SimpleReflexive is normal. -/
theorem simpleReflexive_isNormal : SimpleReflexive.isNormal :=
  simple_isNormal reflexiveR

end Normality

/-! Kripke correspondence: R properties correspond to modal axioms (Kripke 1963). -/

section TAxiom

/-- Reflexivity of R: every world accesses itself. Alias for `Core.ModalLogic.Refl`. -/
abbrev isReflexive (R : World → World → Bool) : Prop := Refl R

/-- T Axiom: reflexive R implies □p -> p.
Uses `Core.ModalLogic.T_of_refl` under the hood. -/
theorem T_axiom_from_reflexivity (R : World → World → Bool) (hRefl : isReflexive R)
    (p : Proposition) (w : World)
    (hNec : (Simple R).eval .necessity p w = true) : p w = true := by
  unfold Simple at hNec
  simp only at hNec
  have hWIn : R w w = true := hRefl w
  have hWFiltered : w ∈ allWorlds'.filter (R w) := by
    simp only [List.mem_filter, allWorlds']
    exact ⟨Core.Proposition.FiniteWorlds.complete w, hWIn⟩
  exact List.all_eq_true.mp hNec w hWFiltered

/-- Reflexive accessibility gives T axiom: □p -> p. -/
theorem reflexive_implies_T (R : World → World → Bool) (hRefl : isReflexive R) :
    ∀ (p : Proposition) (w : World),
    (Simple R).eval .necessity p w = true → p w = true :=
  λ p w => T_axiom_from_reflexivity R hRefl p w

end TAxiom

section DAxiom

/-- Seriality of R: every world accesses at least one world. Alias for `Core.ModalLogic.Serial`. -/
abbrev isSerial (R : World → World → Bool) : Prop := Serial R

/-- D Axiom: serial R implies □p -> ◇p.
Uses `Core.ModalLogic.D_of_serial` under the hood. -/
theorem D_axiom_from_seriality (R : World → World → Bool) (hSerial : isSerial R)
    (p : Proposition) (w : World)
    (hNec : (Simple R).eval .necessity p w = true) :
    (Simple R).eval .possibility p w = true := by
  unfold Simple at hNec ⊢
  simp only at hNec ⊢
  obtain ⟨w', hW'Acc⟩ := hSerial w
  have hW'In : w' ∈ allWorlds'.filter (R w) := by
    simp only [List.mem_filter, allWorlds']
    exact ⟨Core.Proposition.FiniteWorlds.complete w', hW'Acc⟩
  have hPw' : p w' = true := List.all_eq_true.mp hNec w' hW'In
  exact List.any_eq_true.mpr ⟨w', hW'In, hPw'⟩

/-- Serial accessibility gives D axiom: □p -> ◇p. -/
theorem serial_implies_D (R : World → World → Bool) (hSerial : isSerial R) :
    ∀ (p : Proposition) (w : World),
    (Simple R).eval .necessity p w = true → (Simple R).eval .possibility p w = true :=
  λ p w => D_axiom_from_seriality R hSerial p w

end DAxiom

section ConsistencyFromD

/-- Universal R is serial. Uses `Core.ModalLogic.universalR_serial`. -/
theorem universalR_isSerial : isSerial universalR := Core.ModalLogic.universalR_serial

/-- Reflexive R is serial (reflexivity implies seriality). -/
theorem reflexiveR_isSerial : isSerial reflexiveR :=
  Core.ModalLogic.refl_serial Core.ModalLogic.identityR_refl

/-- Universal accessibility gives consistency via D axiom. -/
theorem simple_universal_isConsistent_from_D :
    ∀ (p : Proposition) (w : World),
    SimpleUniversal.necessityEntailsPossibility p w = true := by
  intro p w
  unfold ModalTheory.necessityEntailsPossibility ModalTheory.necessity ModalTheory.possibility
  cases hNec : SimpleUniversal.eval .necessity p w with
  | false =>
      simp only [SimpleUniversal, Simple, Bool.not_false, Bool.true_or]
  | true =>
      simp only [Bool.not_true, Bool.false_or]
      exact D_axiom_from_seriality universalR universalR_isSerial p w hNec

end ConsistencyFromD

section KAxiom

/-- Material implication as a proposition. -/
def pImpl (p q : Proposition) : Proposition := λ w => !p w || q w

/-- K Axiom: □(p -> q) -> (□p -> □q). Holds for any R. -/
theorem K_axiom (R : World → World → Bool) (p q : Proposition) (w : World)
    (hImpl : (Simple R).eval .necessity (pImpl p q) w = true)
    (hP : (Simple R).eval .necessity p w = true) :
    (Simple R).eval .necessity q w = true := by
  unfold Simple at hImpl hP ⊢
  simp only at hImpl hP ⊢
  apply List.all_eq_true.mpr
  intro w' hW'Acc
  have hImplW' : pImpl p q w' = true := List.all_eq_true.mp hImpl w' hW'Acc
  have hPW' : p w' = true := List.all_eq_true.mp hP w' hW'Acc
  unfold pImpl at hImplW'
  cases hp : p w' with
  | false => simp [hp] at hPW'
  | true => simp [hp] at hImplW'; exact hImplW'

/-- K axiom holds for all Simple theories unconditionally. -/
theorem simple_K_axiom (R : World → World → Bool) :
    ∀ (p q : Proposition) (w : World),
    (Simple R).eval .necessity (pImpl p q) w = true →
    (Simple R).eval .necessity p w = true →
    (Simple R).eval .necessity q w = true :=
  λ p q w => K_axiom R p q w

end KAxiom

end Montague.Modal
