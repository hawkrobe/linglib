import Linglib.Syntax.Tree.Cat
import Linglib.Semantics.Composition.Tree
import Linglib.Core.Logic.Intensional.Variables
import Linglib.Fragments.English.Toy
import Linglib.Semantics.Composition.LexEntry
import Linglib.Semantics.Quantification.Quantifier

/-!
# [heim-kratzer-1998]: Type-Driven Composition of Quantifiers

End-to-end verification that the H&K engine (`Composition/Tree.lean`)
composes quantificational sentences as advertised in Ch. 5: lexicon →
QR-syntax tree (with traces and binders) → truth conditions. The engine
implements TN/NN/FA/IFA/PM/PA; this file feeds it the textbook examples
and checks the predictions over a toy model.

## H&K Pipeline (Ch. 5)

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

## Scope ambiguity

"Everybody loves somebody" yields two readings from two QR structures —
surface scope (∀>∃) and inverse scope (∃>∀) — that differ only in which
quantifier is raised higher. `scope_readings_differ` certifies that the
two trees compute genuinely distinct propositions in the toy model.

## Note on `Prop`-valued `.t`

With `interpTy .t = Prop`, the engine produces `Prop`-valued truth
conditions directly. Theorems verify these at the `Prop` level rather
than via `evalTree` (which would demand a blanket
`Decidable (∀ p : Prop, p)` instance).
-/

namespace HeimKratzer1998

open Core.Logic.Intensional
open Core.Logic.Intensional.Variables
open Semantics.Montague
open Syntax
open Semantics.Composition.Tree
open Semantics.Quantification.Quantifier
open Semantics.Montague.ToyLexicon (student_sem person_sem)

/-! ### Model and lexicon -/

def quantLex : Lexicon ToyEntity Unit := λ word =>
  match word with
  | "every" => some ⟨Ty.det, (every_sem : Denot ToyEntity Unit Ty.det)⟩
  | "some" => some ⟨Ty.det, (some_sem : Denot ToyEntity Unit Ty.det)⟩
  | "student" => some ⟨.e ⇒ .t, student_sem⟩
  | "person" => some ⟨.e ⇒ .t, person_sem⟩
  | "sleeps" => some ⟨.e ⇒ .t, ToyLexicon.sleeps_sem⟩
  | "laughs" => some ⟨.e ⇒ .t, ToyLexicon.laughs_sem⟩
  | "sees" => some ⟨.e ⇒ .e ⇒ .t, ToyLexicon.sees_sem⟩
  | _ => none

def g₀ : Core.Assignment ToyEntity := λ _ => .john

/-! ### "Every student sleeps" -/

/-- QR tree: `[S [DP every student] [1 [S t₁ sleeps]]]` -/
def tree_everyStudentSleeps : Tree Unit String :=
  .bin
    (.bin (.leaf "every") (.leaf "student"))
    (.binder 1 (.bin (.tr 1) (.leaf "sleeps")))

/-- Every student sleeps is false (Mary is a student but doesn't sleep). -/
theorem every_student_sleeps_false :
    ¬(every_sem student_sem ToyLexicon.sleeps_sem) := by
  intro h; exact h ToyEntity.mary trivial

/-- QR tree: `[S [DP some student] [1 [S t₁ sleeps]]]` -/
def tree_someStudentSleeps : Tree Unit String :=
  .bin
    (.bin (.leaf "some") (.leaf "student"))
    (.binder 1 (.bin (.tr 1) (.leaf "sleeps")))

/-- Some student sleeps = true (John is a student and sleeps). -/
theorem some_student_sleeps_true :
    some_sem student_sem ToyLexicon.sleeps_sem :=
  ⟨ToyEntity.john, trivial, trivial⟩

/-! ### Scope ambiguity: "Every person sees some person"

Two QR structures yield two scope readings. The trees differ only in
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
  every_sem person_sem
    (λ x => some_sem person_sem (λ y => ToyLexicon.sees_sem y x))

/-- Inverse scope Prop. -/
abbrev inverseScopeProp : Prop :=
  some_sem person_sem
    (λ y => every_sem person_sem (λ x => ToyLexicon.sees_sem y x))

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

/-! ### The engine computes the readings

The QR trees and the hand-written `surfaceScopeProp`/`inverseScopeProp` are linked
by `interp`: running the engine on a tree yields exactly the corresponding reading.
So the scope-ambiguity result is a fact about the *engine's* output, not a parallel
re-implementation alongside it. -/

/-- Surface scope: the engine computes the hand-written reading. -/
theorem interp_computes_surface :
    interp ToyEntity Unit quantLex g₀ tree_surface = some ⟨Ty.t, surfaceScopeProp⟩ := rfl

/-- Inverse scope: likewise. -/
theorem interp_computes_inverse :
    interp ToyEntity Unit quantLex g₀ tree_inverse = some ⟨Ty.t, inverseScopeProp⟩ := rfl

/-- Scope ambiguity, stated about the engine: the two QR derivations interpret to
genuinely different meanings. -/
theorem scope_ambiguity_computed :
    interp ToyEntity Unit quantLex g₀ tree_surface ≠ interp ToyEntity Unit quantLex g₀ tree_inverse := by
  rw [interp_computes_surface, interp_computes_inverse]
  intro h
  have : surfaceScopeProp = inverseScopeProp := by injection h with h'; injection h'
  exact scope_readings_differ this

/-! ### Unified tree: the same sentence with UD categories

The QR tree as `Tree Cat String` — carrying real UD-grounded categories
on every node. `interp` ignores the categories and produces identical
truth conditions to the category-free `Tree Unit String` version. -/

/-- QR tree with UD categories:
`[S [DP [Det every] [N student]] [1 [S [t₁:NP] [VP sleeps]]]]` -/
def synTree_everyStudentSleeps : Tree Cat String :=
  .node .S
    (.node .DP (.terminal .Det "every" :: .terminal .N "student" :: []) ::
     .bind 1 .S
       (.node .S (.trace 1 .NP :: .node .VP (.terminal .V "sleeps" :: []) :: [])) :: [])

/-! ### First-order reduction

The textbook trees are in the compiled FO fragment
(`Composition/Reduction.lean`): they compile to mathlib
`FirstOrder.Language.Formula`s, and by the agreement theorem the engine's
truth conditions *are* model-theoretic realization over `toyModel`. -/

section Reduction

open Semantics.Composition

/-- The textbook trees compile. -/
example : (compileFO {} toyNaming tree_everyStudentSleeps).isSome = true := rfl
example : (compileFO {} toyNaming tree_someStudentSleeps).isSome = true := rfl

/-- The agreement theorem instantiated at the toy model: for any tree in the
fragment, engine truth conditions are `Realize` of the compiled formula. -/
theorem interp_eq_realize {t : Tree Unit String} {φ : toyLang.Formula ℕ}
    (h : compileFO {} toyNaming t = some φ) (g : Core.Assignment ToyEntity) :
    Tree.interp ToyEntity Unit (toyModel.lexiconFO {} toyNaming ()) g t
      = some ⟨.t, toyModel.realizeAt () φ g⟩ :=
  interp_compileFO toyModel {} toyNaming () FOWords.nodup_default
    toyNaming_freshFor toyNaming_disjoint t g h

/-- "Some student sleeps" holds in the toy model, via the engine. -/
theorem someStudentSleeps_holds (g : Core.Assignment ToyEntity) :
    HoldsAt toyModel (toyModel.lexiconFO {} toyNaming ()) g
      tree_someStudentSleeps :=
  ⟨_, rfl, ⟨ToyEntity.john, trivial, trivial⟩⟩

/-- "John sleeps and Mary laughs". -/
def tree_conj : Tree Unit String :=
  .bin (.bin (.leaf "John") (.leaf "sleeps"))
       (.bin (.leaf "and") (.bin (.leaf "Mary") (.leaf "laughs")))

/-- **Consequence transfer**: conjunction elimination is a first-order
consequence, so the entailment holds in the toy model — and by the same
theorem in *every* composition model interpreting the signature. -/
theorem conj_entails_first (g : Core.Assignment ToyEntity) :
    HoldsAt toyModel (toyModel.lexiconFO {} toyNaming ()) g tree_conj →
      HoldsAt toyModel (toyModel.lexiconFO {} toyNaming ()) g
        (.bin (.leaf "John") (.leaf "sleeps")) :=
  holdsAt_of_models toyModel {} toyNaming () FOWords.nodup_default
    toyNaming_freshFor toyNaming_disjoint rfl rfl
    (fun _ S v h => by
      letI := S
      exact (FirstOrder.Language.Formula.realize_inf.mp h).1) g

end Reduction

end HeimKratzer1998
