import Linglib.Theories.Semantics.Composition.Tree
import Linglib.Theories.Semantics.Montague.Variables
import Linglib.Theories.Semantics.Lexical.Determiner.Quantifier

/-!
# Quantifier Composition via Predicate Abstraction

Demonstrates that `interpTreeG` composes quantificational sentences
end-to-end: lexicon → syntax tree (with QR traces and binders) →
truth conditions.

## H&K Pipeline (@cite{heim-kratzer-1998} Ch. 5)

After Quantifier Raising moves a DP to a higher position, it leaves a
trace `tₙ` and creates a binder node `n`. Predicate Abstraction (PA)
converts the binder + body into `λx. ⟦body⟧^{g[n↦x]}`, producing a
predicate that the raised quantifier takes as its scope argument.

"Every student sleeps" after QR:
```
[S [DP [D every] [N student]] [1 [S [t₁] [VP sleeps]]]]
```

Evaluated as:
1. `⟦t₁⟧^g = g(1)` (Traces rule)
2. `⟦sleeps⟧ = sleeps'` (TN)
3. `⟦[t₁ sleeps]⟧^g = sleeps'(g(1))` (FA)
4. `⟦[1 [t₁ sleeps]]⟧^g = λx. sleeps'(x)` (PA)
5. `⟦every student⟧ = every'(student')` (FA)
6. `⟦S⟧ = every'(student')(λx. sleeps'(x))` (FA)

## Scope Ambiguity

"Everybody loves somebody" yields two readings from two QR structures:
- Surface scope (∀>∃): every person scopes above some person
- Inverse scope (∃>∀): some person scopes above every person

The two trees differ only in which quantifier is raised higher.
-/

namespace Semantics.Composition.QuantifierComposition

open Semantics.Montague
open Core.Tree
open Semantics.Composition.Tree
open Semantics.Montague.Variables
open Semantics.Lexical.Determiner.Quantifier

-- ════════════════════════════════════════════════════════════════════
-- § Model and Lexicon
-- ════════════════════════════════════════════════════════════════════

def quantLex : Lexicon toyModel := λ word =>
  match word with
  | "every" => some ⟨Ty.det, every_sem toyModel⟩
  | "some" => some ⟨Ty.det, some_sem toyModel⟩
  | "student" => some ⟨.e ⇒ .t, student_sem⟩
  | "person" => some ⟨.e ⇒ .t, person_sem⟩
  | "sleeps" => some ⟨.e ⇒ .t, ToyLexicon.sleeps_sem⟩
  | "laughs" => some ⟨.e ⇒ .t, ToyLexicon.laughs_sem⟩
  | "sees" => some ⟨.e ⇒ .e ⇒ .t, ToyLexicon.sees_sem⟩
  | _ => none

def g₀ : Assignment toyModel := λ _ => .john

-- ════════════════════════════════════════════════════════════════════
-- § Basic: "Every student sleeps"
-- ════════════════════════════════════════════════════════════════════

/-- QR tree: `[S [DP every student] [1 [S t₁ sleeps]]]` -/
def tree_everyStudentSleeps : Tree Unit String :=
  .bin
    (.bin (.leaf "every") (.leaf "student"))
    (.binder 1 (.bin (.tr 1) (.leaf "sleeps")))

/-- Every student sleeps = false (Mary is a student but doesn't sleep). -/
theorem every_student_sleeps_false :
    evalTree quantLex g₀ tree_everyStudentSleeps = some false := by
  native_decide

/-- Grounding: tree interpretation = direct application of GQ. -/
theorem every_student_sleeps_grounding :
    evalTree quantLex g₀ tree_everyStudentSleeps =
    some (every_sem toyModel student_sem ToyLexicon.sleeps_sem) := by
  native_decide

/-- QR tree: `[S [DP some student] [1 [S t₁ sleeps]]]` -/
def tree_someStudentSleeps : Tree Unit String :=
  .bin
    (.bin (.leaf "some") (.leaf "student"))
    (.binder 1 (.bin (.tr 1) (.leaf "sleeps")))

/-- Some student sleeps = true (John is a student and sleeps). -/
theorem some_student_sleeps_true :
    evalTree quantLex g₀ tree_someStudentSleeps = some true := by
  native_decide

/-- Grounding: tree interpretation = direct application. -/
theorem some_student_sleeps_grounding :
    evalTree quantLex g₀ tree_someStudentSleeps =
    some (some_sem toyModel student_sem ToyLexicon.sleeps_sem) := by
  native_decide

-- ════════════════════════════════════════════════════════════════════
-- § Scope Ambiguity: "Every person sees some person"
-- ════════════════════════════════════════════════════════════════════

/-! Two QR structures yield two scope readings. The trees differ only in
which quantifier occupies the higher position. -/

/-- Surface scope (∀>∃):
```
[S [DP every person] [1 [S [DP some person] [2 [S t₁ [VP sees t₂]]]]]]
```
∀x[person(x) → ∃y[person(y) ∧ sees(x,y)]] -/
def tree_surface : Tree Unit String :=
  .bin
    (.bin (.leaf "every") (.leaf "person"))
    (.binder 1
      (.bin
        (.bin (.leaf "some") (.leaf "person"))
        (.binder 2
          (.bin (.tr 1) (.bin (.leaf "sees") (.tr 2))))))

/-- Inverse scope (∃>∀):
```
[S [DP some person] [2 [S [DP every person] [1 [S t₁ [VP sees t₂]]]]]]
```
∃y[person(y) ∧ ∀x[person(x) → sees(x,y)]] -/
def tree_inverse : Tree Unit String :=
  .bin
    (.bin (.leaf "some") (.leaf "person"))
    (.binder 2
      (.bin
        (.bin (.leaf "every") (.leaf "person"))
        (.binder 1
          (.bin (.tr 1) (.bin (.leaf "sees") (.tr 2))))))

/-- Surface scope is true in the toy model.
(John sees Mary and Mary sees John — each person sees some person.) -/
theorem surface_scope_true :
    evalTree quantLex g₀ tree_surface = some true := by
  native_decide

/-- Inverse scope is also true.
(John is seen by everyone: both John and Mary see John? No —
 Mary sees John ✓, John sees Mary ✓, but John doesn't see John ✗.
 Check: is there ONE person that everyone sees?) -/
theorem inverse_scope_value :
    evalTree quantLex g₀ tree_inverse = some false := by
  native_decide

/-- The two scope readings differ: proof of genuine ambiguity. -/
theorem scope_readings_differ :
    evalTree quantLex g₀ tree_surface ≠ evalTree quantLex g₀ tree_inverse := by
  native_decide

/-- Surface scope tree = manual ∀>∃ computation. -/
theorem surface_scope_grounding :
    evalTree quantLex g₀ tree_surface =
    some (every_sem toyModel person_sem
      (λ x => some_sem toyModel person_sem (λ y => ToyLexicon.sees_sem y x))) := by
  native_decide

/-- Inverse scope tree = manual ∃>∀ computation. -/
theorem inverse_scope_grounding :
    evalTree quantLex g₀ tree_inverse =
    some (some_sem toyModel person_sem
      (λ y => every_sem toyModel person_sem (λ x => ToyLexicon.sees_sem y x))) := by
  native_decide

-- ════════════════════════════════════════════════════════════════════
-- § Assignment Independence
-- ════════════════════════════════════════════════════════════════════

/-- A different initial assignment yields the same result:
closed sentences don't depend on the assignment. -/
def g₁ : Assignment toyModel := λ _ => .mary

theorem assignment_independent :
    evalTree quantLex g₀ tree_everyStudentSleeps =
    evalTree quantLex g₁ tree_everyStudentSleeps := by
  native_decide

-- ════════════════════════════════════════════════════════════════════
-- § Unified Tree: Same Sentence with UD Categories
-- ════════════════════════════════════════════════════════════════════

/-! The same QR tree built as `Tree Cat String` — carrying real UD-grounded
categories on every node. `interpTreeG` ignores the categories and produces
identical truth conditions to the category-free `Tree Unit String` version. -/

/-- QR tree with UD categories:
`[S [DP [Det every] [N student]] [1 [S [t₁:NP] [VP sleeps]]]]` -/
def synTree_everyStudentSleeps : Tree Cat String :=
  .node .S
    (.node .DP (.terminal .Det "every" :: .terminal .N "student" :: []) ::
     .bind 1 .S
       (.node .S (.trace 1 .NP :: .node .VP (.terminal .V "sleeps" :: []) :: [])) :: [])

/-- Category-bearing tree yields the same result as category-free tree. -/
theorem synTree_every_student_sleeps_false :
    evalTree quantLex g₀ synTree_everyStudentSleeps = some false := by
  native_decide

/-- Tree Cat String agrees with Tree Unit String. -/
theorem catTree_agrees_with_unitTree :
    evalTree quantLex g₀ synTree_everyStudentSleeps =
    evalTree quantLex g₀ tree_everyStudentSleeps := by
  native_decide

end Semantics.Composition.QuantifierComposition
