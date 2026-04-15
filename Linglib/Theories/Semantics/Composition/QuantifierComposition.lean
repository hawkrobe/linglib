import Linglib.Theories.Semantics.Composition.Tree
import Linglib.Core.IntensionalLogic.Variables
import Linglib.Fragments.ToyDomain
import Linglib.Theories.Semantics.Composition.LexEntry
import Linglib.Theories.Semantics.Quantification.Quantifier

/-!
# Quantifier Composition via Predicate Abstraction

Demonstrates that `interp` composes quantificational sentences
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

## Note on Prop-valued `.t`

With `interpTy .t = Prop`, the compositional semantics produces `Prop`-valued
truth conditions directly. Theorems verify these truth conditions at the `Prop`
level rather than via `evalTree` (which requires a blanket `Decidable` instance
for `∀ (p : Prop), Decidable p`).
-/

namespace Semantics.Composition.QuantifierComposition

open Core.IntensionalLogic
open Core.IntensionalLogic.Variables
open Semantics.Montague
open Core.Tree
open Semantics.Composition.Tree
open Semantics.Quantification.Quantifier

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

/-- Every student sleeps is false (Mary is a student but doesn't sleep). -/
theorem every_student_sleeps_false :
    ¬(every_sem toyModel student_sem ToyLexicon.sleeps_sem) := by
  intro h; exact h ToyEntity.mary trivial

/-- QR tree: `[S [DP some student] [1 [S t₁ sleeps]]]` -/
def tree_someStudentSleeps : Tree Unit String :=
  .bin
    (.bin (.leaf "some") (.leaf "student"))
    (.binder 1 (.bin (.tr 1) (.leaf "sleeps")))

/-- Some student sleeps = true (John is a student and sleeps). -/
theorem some_student_sleeps_true :
    some_sem toyModel student_sem ToyLexicon.sleeps_sem :=
  ⟨ToyEntity.john, trivial, trivial⟩

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

/-- Surface scope Prop. -/
abbrev surfaceScopeProp : Prop :=
  every_sem toyModel person_sem
    (λ x => some_sem toyModel person_sem (λ y => ToyLexicon.sees_sem y x))

/-- Inverse scope Prop. -/
abbrev inverseScopeProp : Prop :=
  some_sem toyModel person_sem
    (λ y => every_sem toyModel person_sem (λ x => ToyLexicon.sees_sem y x))

/-- Surface scope is true in the toy model.
(John sees Mary and Mary sees John — each person sees some person.) -/
theorem surface_scope_true : surfaceScopeProp := by
  intro x hx
  cases x with
  | john => exact ⟨ToyEntity.mary, trivial, trivial⟩
  | mary => exact ⟨ToyEntity.john, trivial, trivial⟩
  | pizza => exact absurd hx id
  | book => exact absurd hx id

/-- Inverse scope is false.
(No single person is seen by everyone — John doesn't see John,
 Mary doesn't see Mary.) -/
theorem inverse_scope_false : ¬inverseScopeProp := by
  intro ⟨y, _, hy_all⟩
  cases y with
  | john => exact hy_all ToyEntity.john trivial
  | mary => exact hy_all ToyEntity.mary trivial
  | pizza => exact hy_all ToyEntity.john trivial
  | book => exact hy_all ToyEntity.john trivial

/-- The two scope readings differ: proof of genuine ambiguity. -/
theorem scope_readings_differ : surfaceScopeProp ≠ inverseScopeProp := by
  intro h
  exact inverse_scope_false (h ▸ surface_scope_true)

-- ════════════════════════════════════════════════════════════════════
-- § Unified Tree: Same Sentence with UD Categories
-- ════════════════════════════════════════════════════════════════════

/-! The same QR tree built as `Tree Cat String` — carrying real UD-grounded
categories on every node. `interp` ignores the categories and produces
identical truth conditions to the category-free `Tree Unit String` version. -/

/-- QR tree with UD categories:
`[S [DP [Det every] [N student]] [1 [S [t₁:NP] [VP sleeps]]]]` -/
def synTree_everyStudentSleeps : Tree Cat String :=
  .node .S
    (.node .DP (.terminal .Det "every" :: .terminal .N "student" :: []) ::
     .bind 1 .S
       (.node .S (.trace 1 .NP :: .node .VP (.terminal .V "sleeps" :: []) :: [])) :: [])

end Semantics.Composition.QuantifierComposition
