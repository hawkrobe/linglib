/-
# PLA Embedding into Dynamic Ty2

PLA embeds into Dynamic Ty2 using a sum type for the assignment domain.

## The Key Issue

PLA distinguishes variables (VarIdx) from pronouns (PronIdx).
Dynamic Ty2 has a single dref type S → E.

Solution: Use `(VarIdx ⊕ PronIdx) → E` as the S parameter.
This provides type-safe separation without magic numbers.

## References

- Dekker (2012). Dynamic Semantics.
- Muskens (1996). Combining Montague Semantics and Discourse Representation.
-/

import Linglib.Theories.DynamicSemantics.Core.DynamicTy2
import Linglib.Theories.DynamicSemantics.Core.Translation
import Linglib.Theories.DynamicSemantics.PLA.Semantics

namespace Theories.DynamicSemantics.PLA

open Theories.DynamicSemantics.Core
open Theories.DynamicSemantics.Core.DynamicTy2


/--
PLA assignment merges variable and pronoun assignments via sum type.
- `.inl i` accesses variable i
- `.inr i` accesses pronoun i
-/
abbrev MergedAssignment (E : Type*) := (VarIdx ⊕ PronIdx) → E

/-- Variable dref: projection at .inl i -/
def varDref {E : Type*} (i : VarIdx) : Dref (MergedAssignment E) E := λ g => g (.inl i)

/-- Pronoun dref: projection at .inr i -/
def pronDref {E : Type*} (i : PronIdx) : Dref (MergedAssignment E) E := λ g => g (.inr i)


/--
Interpret a PLA term as a Dynamic Ty2 dref.
-/
def termToDref {E : Type*} : Term → Dref (MergedAssignment E) E
  | .var i => varDref i
  | .pron i => pronDref i


/--
Convert PLAPoss to merged assignment.
-/
def plaPossToMerged {E : Type*} (p : PLAPoss E) : MergedAssignment E
  | .inl i => p.assignment i
  | .inr i => p.witnesses i

/--
Convert merged assignment to PLAPoss.
-/
def mergedToPLAPoss {E : Type*} (g : MergedAssignment E) : PLAPoss E :=
  { assignment := λ i => g (.inl i)
  , witnesses := λ i => g (.inr i) }

theorem plaPoss_roundtrip {E : Type*} (p : PLAPoss E) :
    mergedToPLAPoss (plaPossToMerged p) = p := by
  simp only [mergedToPLAPoss, plaPossToMerged]

theorem merged_roundtrip {E : Type*} (g : MergedAssignment E) :
    plaPossToMerged (mergedToPLAPoss g) = g := by
  funext x
  cases x <;> rfl


variable {E : Type*} [Nonempty E]

/-- Functional update for merged assignments (only affects variables) -/
def extend (g : MergedAssignment E) (i : VarIdx) (e : E) : MergedAssignment E :=
  λ x => match x with
    | .inl j => if j = i then e else g (.inl j)
    | .inr j => g (.inr j)

/-- Evaluate a term given a merged assignment -/
def evalTerm (g : MergedAssignment E) : Term → E
  | .var i => g (.inl i)
  | .pron i => g (.inr i)

/--
Translate a PLA formula to a Dynamic Ty2 condition.

This captures when a merged assignment satisfies the formula.
Note: PLA existentials check for EXISTENCE of a witness, but
don't actually extend the assignment (eliminative semantics).
-/
def formulaToCondition (M : Model E) : Formula → Condition (MergedAssignment E)
  | .atom name ts => λ g => M.interp name (ts.map (evalTerm g))
  | .neg φ => λ g => ¬(formulaToCondition M φ g)
  | .conj φ ψ => λ g => formulaToCondition M φ g ∧ formulaToCondition M ψ g
  | .exists_ x φ => λ g => ∃ e : E, formulaToCondition M φ (extend g x e)

/--
Translate a PLA formula to a Dynamic Ty2 DRS.

PLA updates are eliminative (they only filter, never extend assignments).
This means every PLA formula translates to a TEST in Dynamic Ty2.
-/
def formulaToDRS (M : Model E) (φ : Formula) : DRS (MergedAssignment E) :=
  test (formulaToCondition M φ)


/-- Atom translation: predicate applied to evaluated terms -/
theorem formulaToDRS_atom (M : Model E) (name : String) (ts : List Term) :
    formulaToDRS M (.atom name ts) = test (λ g => M.interp name (ts.map (evalTerm g))) := rfl

/-- Negation translation: test of negated condition -/
theorem formulaToDRS_neg (M : Model E) (φ : Formula) :
    formulaToDRS M (∼φ) = test (λ g => ¬formulaToCondition M φ g) := rfl

/-- Conjunction translation: test of conjoined conditions -/
theorem formulaToDRS_conj (M : Model E) (φ ψ : Formula) :
    formulaToDRS M (φ ⋀ ψ) = test (λ g => formulaToCondition M φ g ∧ formulaToCondition M ψ g) := rfl

/-- Existential translation: test for existence of witness -/
theorem formulaToDRS_exists (M : Model E) (x : VarIdx) (φ : Formula) :
    formulaToDRS M (.exists_ x φ) = test (λ g => ∃ e : E, formulaToCondition M φ (extend g x e)) := rfl


/-- Split a merged assignment into variable and witness components -/
def splitAssignment (g : MergedAssignment E) : Assignment E × WitnessSeq E :=
  (λ i => g (.inl i), λ i => g (.inr i))

/-- Term evaluation agrees with PLA semantics -/
theorem evalTerm_eq_Term_eval (g : MergedAssignment E) (t : Term) :
    evalTerm g t = t.eval (splitAssignment g).1 (splitAssignment g).2 := by
  cases t with
  | var i => rfl
  | pron i => rfl

/-- extend and Assignment.update align on the variable component -/
theorem extend_fst_eq_update (g : MergedAssignment E) (x : VarIdx) (e : E) :
    (splitAssignment (extend g x e)).1 = (splitAssignment g).1[x ↦ e] := by
  ext n
  simp only [splitAssignment, extend, Assignment.update]

/-- extend doesn't affect the pronoun component -/
theorem extend_snd_eq (g : MergedAssignment E) (x : VarIdx) (e : E) :
    (splitAssignment (extend g x e)).2 = (splitAssignment g).2 := by
  ext n
  simp only [splitAssignment, extend]

/-- Formula condition agrees with PLA satisfaction -/
theorem formulaToCondition_eq_sat (M : Model E) (φ : Formula) (g : MergedAssignment E) :
    formulaToCondition M φ g ↔ φ.sat M (splitAssignment g).1 (splitAssignment g).2 := by
  induction φ generalizing g with
  | atom name ts =>
    simp only [formulaToCondition, Formula.sat, splitAssignment]
    have h : ts.map (evalTerm g) = ts.map (Term.eval (λ i => g (.inl i)) λ i => g (.inr i)) := by
      apply List.map_congr_left
      intro t _
      exact evalTerm_eq_Term_eval g t
    rw [h]
  | neg φ ih =>
    simp only [formulaToCondition, Formula.sat]
    exact not_congr (ih g)
  | conj φ ψ ih1 ih2 =>
    simp only [formulaToCondition, Formula.sat]
    exact and_congr (ih1 g) (ih2 g)
  | exists_ x φ ih =>
    simp only [formulaToCondition, Formula.sat]
    constructor
    · intro ⟨e, he⟩
      use e
      rw [ih (extend g x e)] at he
      rw [extend_fst_eq_update, extend_snd_eq] at he
      exact he
    · intro ⟨e, he⟩
      use e
      rw [ih (extend g x e)]
      rw [extend_fst_eq_update, extend_snd_eq]
      exact he

/--
PLA formula semantics corresponds to Dynamic Ty2 DRS.

A merged assignment g satisfies the DRS iff the split assignment satisfies
the original PLA formula.
-/
theorem formulaToDRS_correct (M : Model E) (φ : Formula) (g h : MergedAssignment E) :
    formulaToDRS M φ g h ↔ (g = h ∧ φ.sat M (splitAssignment g).1 (splitAssignment g).2) := by
  simp only [formulaToDRS, test]
  constructor
  · intro ⟨heq, hcond⟩
    subst heq
    exact ⟨rfl, (formulaToCondition_eq_sat M φ g).mp hcond⟩
  · intro ⟨heq, hsat⟩
    subst heq
    exact ⟨rfl, (formulaToCondition_eq_sat M φ g).mpr hsat⟩

end Theories.DynamicSemantics.PLA
