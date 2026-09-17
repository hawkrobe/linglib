import Linglib.Syntax.Tree.Cat
import Linglib.Semantics.Composition.Tree
import Linglib.Semantics.Composition.Assignment
import Linglib.Fragments.English.Toy
import Linglib.Semantics.Composition.Reduction
import Linglib.Semantics.Composition.Lexicon
import Linglib.Semantics.Quantification.NP
import Linglib.Semantics.Quantification.Polyadic
import Linglib.Semantics.Quantification.Terminal
import Linglib.Fragments.English.Determiners
import Linglib.Data.Examples.HeimKratzer1998

/-!
# Heim and Kratzer (1998): Semantics in Generative Grammar

This file formalizes the treatment of quantifiers in Chapter 7 of [heim-kratzer-1998]: a
quantificational DP in object position creates a type mismatch (§7.1) that Quantifier
Raising repairs by movement (§7.3), leaving a trace interpreted by the Traces and Pronouns
Rule (Ch. 5 (9)) and a binder index interpreted by Predicate Abstraction (§5.2.3, as revised
in Chapter 7), so that the raised quantifier takes the abstracted predicate as its scope.
The substrate's composition engine implements those rules; here it is fed QR trees whose
quantifier leaves are the English fragment's words, read through the terminals of their
available readings, and whose other leaves are the toy fragment's, and its output is checked:
"every student sleeps" and "some student sleeps"
compose to the expected truth conditions, and the two QR derivations of a doubly
quantified sentence, the book's (2) "Some publisher offended every linguist", compute the
two scope readings of `Quantifier.Polyadic`, which differ in the toy model
(`scope_ambiguity_computed`) and are nested (`inverse_entails_surface`). The trees also
compile to first-order formulas, so the engine's truth conditions are model-theoretic
realization (`interp_eq_realize`) and first-order consequence transfers
(`conj_entails_first`).

## Implementation notes

The toy fragment's "every person sees some person" stands in for the book's (2); the
readings are the surface and inverse iterations of `Quantifier.Polyadic`. With
`interpTy .t = Prop` the engine produces `Prop`-valued truth conditions, verified at the
`Prop` level rather than by evaluation. The categorised tree `synTree_everyStudentSleeps`
carries UD categories that the engine ignores.

## References

* [heim-kratzer-1998]
-/

namespace HeimKratzer1998

open Semantics.Composition
open scoped Assignment
open Semantics.Montague
open Syntax
open Semantics.Composition.Tree
open Quantifier Quantifier.GQ
open Quantifier.Polyadic (surfaceScope inverseScope iterate_every_some_of_some_every)
open Semantics.Montague.ToyLexicon (student_sem person_sem)
open English.Determiners (QuantityWord)
open scoped Semantics

/-! ### Model and lexicon -/

/-- The study's stand on the quantifier words: the one reading each of *every* and *some* makes
available, as a terminal on the toy domain. -/
def quantifierReading : QuantityWord → Option (Denotation ToyEntity Unit)
  | .every => some (Family.every.toDenotation ToyEntity Unit)
  | .some_ => some (Family.some.toDenotation ToyEntity Unit)
  | _ => none

/-- Each chosen terminal is among the terminals of the word's available readings. -/
theorem quantifierReading_mem {w : QuantityWord} {d : Denotation ToyEntity Unit}
    (h : quantifierReading w = some d) : d ∈ terminals ⟦w⟧ ToyEntity Unit := by
  cases w <;> simp only [quantifierReading, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    exact toDenotation_mem_terminals (Set.mem_singleton _) _ _

/-- The leaf interpretation: the quantifier words through their readings, and the toy
fragment's nouns and verbs through the toy lexicon. -/
def lex : QuantityWord ⊕ String → Option (Denotation ToyEntity Unit) :=
  Sum.elim quantifierReading toyLexicon

def g₀ : Assignment ToyEntity := λ _ => .john

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
def tree_surface : Tree Unit (QuantityWord ⊕ String) :=
  .bin
    (.bin (.leaf (.inl .every)) (.leaf (.inr "person")))
    (.binder 1
      (.bin
        (.bin (.leaf (.inl .some_)) (.leaf (.inr "person")))
        (.binder 2
          (.bin (.tr 1) (.bin (.leaf (.inr "sees")) (.tr 2))))))

/-- Inverse scope (∃>∀):
```
[S [DP some person] [2 [S [DP every person] [1 [S t₁ [VP sees t₂]]]]]]
```
∃y[person(y) ∧ ∀x[person(x) → sees(x,y)]] -/
def tree_inverse : Tree Unit (QuantityWord ⊕ String) :=
  .bin
    (.bin (.leaf (.inl .some_)) (.leaf (.inr "person")))
    (.binder 2
      (.bin
        (.bin (.leaf (.inl .every)) (.leaf (.inr "person")))
        (.binder 1
          (.bin (.tr 1) (.bin (.leaf (.inr "sees")) (.tr 2))))))

/-- The surface-scope reading, `∀ > ∃`: `every` over `some`, with `x sees y`. -/
abbrev surfaceScopeProp : Prop :=
  surfaceScope every_sem some_sem person_sem person_sem λ x y => ToyLexicon.sees_sem y x

/-- The inverse-scope reading, `∃ > ∀`. -/
abbrev inverseScopeProp : Prop :=
  inverseScope every_sem some_sem person_sem person_sem λ x y => ToyLexicon.sees_sem y x

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

/-- The readings are nested: the inverse reading entails the surface one (`∃∀ ⊨ ∀∃`), so a
model can separate them only in the direction the toy model does. -/
theorem inverse_entails_surface : inverseScopeProp → surfaceScopeProp :=
  iterate_every_some_of_some_every _ _ _

/-! ### The engine computes the readings

The QR trees and the readings `surfaceScopeProp`/`inverseScopeProp` are linked by
`interp`: running the engine on a tree yields exactly the corresponding reading. So the
scope-ambiguity result is a fact about the *engine's* output, not a parallel
re-implementation alongside it. -/

/-- Surface scope: the engine computes the hand-written reading. -/
theorem interp_computes_surface :
    interp lex g₀ tree_surface = some ⟨Ty.t, surfaceScopeProp⟩ := rfl

/-- Inverse scope: likewise. -/
theorem interp_computes_inverse :
    interp lex g₀ tree_inverse = some ⟨Ty.t, inverseScopeProp⟩ := rfl

/-- Scope ambiguity, stated about the engine: the two QR derivations interpret to
genuinely different meanings. -/
theorem scope_ambiguity_computed :
    interp lex g₀ tree_surface ≠
      interp lex g₀ tree_inverse := by
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

/-! ### The book's rules as a reference

[heim-kratzer-1998]'s composition principles for the extensional fragment, transcribed as an
interpretation relation with one constructor per rule: Terminal Nodes, Non-Branching Nodes,
Functional Application with either daughter the function, Predicate Modification, the Traces
and Pronouns Rule, and Predicate Abstraction, which asks the body to denote under every
modification of the assignment. The engine at `M = Id` extends the relation
(`interp_of_denotes`): where the book assigns a denotation, the engine computes it, and the
engine also interprets the event-identification configurations the book leaves undefined. The
relation is therefore functional (`Denotes.unique`), and the surface-scope reading is a
derivation in the book's own rules (`denotes_surface`). -/

section Reference

variable {C L E W : Type}

/-- The book's interpretation relation, relative to a leaf interpretation and an assignment. -/
inductive Denotes (lex : L → Option (Denotation E W)) :
    Assignment E → Tree C L → Denotation E W → Prop
  /-- Terminal Nodes: a leaf denotes what the lexicon gives it. -/
  | tn {g : Assignment E} {c : C} {w : L} {d : Denotation E W} (h : lex w = some d) :
      Denotes lex g (.terminal c w) d
  /-- Non-Branching Nodes: a node denotes what its only daughter does. -/
  | nn {g : Assignment E} {c : C} {t : Tree C L} {d : Denotation E W} (h : Denotes lex g t d) :
      Denotes lex g (.node c (t :: [])) d
  /-- Functional Application, the left daughter the function. -/
  | faLeft {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {σ τ : Ty} {f : Ty.Domain E W (σ ⇒ τ)}
      {a : Ty.Domain E W σ} (h₁ : Denotes lex g t₁ ⟨σ ⇒ τ, f⟩) (h₂ : Denotes lex g t₂ ⟨σ, a⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: [])) ⟨τ, f a⟩
  /-- Functional Application, the right daughter the function. -/
  | faRight {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {σ τ : Ty} {a : Ty.Domain E W σ}
      {f : Ty.Domain E W (σ ⇒ τ)} (h₁ : Denotes lex g t₁ ⟨σ, a⟩)
      (h₂ : Denotes lex g t₂ ⟨σ ⇒ τ, f⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: [])) ⟨τ, f a⟩
  /-- Predicate Modification: two predicates conjoin. -/
  | pm {g : Assignment E} {c : C} {t₁ t₂ : Tree C L} {P Q : Ty.Domain E W (.e ⇒ .t)}
      (h₁ : Denotes lex g t₁ ⟨.e ⇒ .t, P⟩) (h₂ : Denotes lex g t₂ ⟨.e ⇒ .t, Q⟩) :
      Denotes lex g (.node c (t₁ :: t₂ :: [])) ⟨.e ⇒ .t, fun x ↦ P x ∧ Q x⟩
  /-- The Traces and Pronouns Rule: a trace denotes the value of its index. -/
  | trace {g : Assignment E} {n : ℕ} {c : C} : Denotes lex g (.trace n c) ⟨.e, g n⟩
  /-- Predicate Abstraction: a binder abstracts over its index in the body. -/
  | pa {g : Assignment E} {n : ℕ} {c : C} {body : Tree C L} {τ : Ty} {F : E → Ty.Domain E W τ}
      (h : ∀ x, Denotes lex (g[n ↦ x]) body ⟨τ, F x⟩) : Denotes lex g (.bind n c body) ⟨.e ⇒ τ, F⟩

/-- Where the book assigns a denotation, the engine at `M = Id` computes it; the book's
standing assumption that the domain of individuals is nonempty is the hypothesis. -/
theorem interp_of_denotes [Nonempty E] {lex : L → Option (Denotation E W)} {g : Assignment E}
    {t : Tree C L} {d : Denotation E W} (h : Denotes lex g t d) : interp lex g t = some d := by
  induction h with
  | tn h => exact h
  | nn _ ih => exact ih
  | faLeft _ _ ih₁ ih₂ =>
    simp only [interp_node_binary, ih₁, ih₂, Option.bind_some, interpBinary, tryFA_forward]; rfl
  | faRight _ _ ih₁ ih₂ =>
    simp only [interp_node_binary, ih₁, ih₂, Option.bind_some, interpBinary, tryFA_backward]; rfl
  | pm _ _ ih₁ ih₂ =>
    simp only [interp_node_binary, ih₁, ih₂, Option.bind_some, interpBinary_pm]; rfl
  | trace => rfl
  | @pa g n c body τ F h ih =>
    obtain ⟨x₀⟩ := ‹Nonempty E›
    have hty := interp_map_fst_congr lex g (g[n ↦ x₀]) body
    rw [ih x₀] at hty
    obtain ⟨v, hv⟩ : ∃ v, interp lex g body = some ⟨τ, v⟩ := by
      rcases hg : interp lex g body with _ | ⟨τ', v⟩
      · simp [hg] at hty
      · simp only [hg, Option.map_some, Option.some.injEq] at hty; subst hty; exact ⟨v, rfl⟩
    simp only [interp_bind, hv, Option.bind_some]
    show (some ⟨.e ⇒ τ, fun x ↦ valueAt τ v (interp lex (g[n ↦ x]) body)⟩ :
      Option (Denotation E W)) = _
    congr 2
    funext x
    rw [ih x]
    simp [valueAt]

/-- The book's rules are deterministic. -/
theorem Denotes.unique [Nonempty E] {lex : L → Option (Denotation E W)} {g : Assignment E}
    {t : Tree C L} {d d' : Denotation E W} (h : Denotes lex g t d) (h' : Denotes lex g t d') :
    d = d' :=
  Option.some.inj ((interp_of_denotes h).symm.trans (interp_of_denotes h'))

/-- The surface-scope reading is a derivation in the book's rules: Functional Application
around two Predicate Abstractions, with the quantifier words as terminals. -/
theorem denotes_surface : Denotes lex g₀ tree_surface ⟨Ty.t, surfaceScopeProp⟩ := by
  show Denotes lex g₀ tree_surface
    ⟨Ty.t, every_sem person_sem fun x ↦ some_sem person_sem fun y ↦ ToyLexicon.sees_sem y x⟩
  refine .faLeft (lex := lex) (σ := .e ⇒ .t) (τ := .t) (f := every_sem person_sem) ?_
    (.pa (τ := .t) fun x ↦ ?_)
  · exact .faLeft (lex := lex) (σ := .e ⇒ .t) (τ := (.e ⇒ .t) ⇒ .t) (f := every_sem)
      (a := person_sem) (.tn rfl) (.tn rfl)
  · refine .faLeft (lex := lex) (σ := .e ⇒ .t) (τ := .t) (f := some_sem person_sem) ?_
      (.pa (τ := .t) fun y ↦ ?_)
    · exact .faLeft (lex := lex) (σ := .e ⇒ .t) (τ := (.e ⇒ .t) ⇒ .t) (f := some_sem)
        (a := person_sem) (.tn rfl) (.tn rfl)
    · exact .faRight (lex := lex) (σ := .e) (τ := .t) (a := x) (f := ToyLexicon.sees_sem y) .trace
        (.faLeft (lex := lex) (σ := .e) (τ := .e ⇒ .t) (f := ToyLexicon.sees_sem) (a := y)
          (.tn rfl) .trace)

end Reference

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
    (h : compileFO {} toyNaming t = some φ) (g : Assignment ToyEntity) :
    Tree.interp (toyModel.lexiconFO {} toyNaming ()) g t
      = some ⟨.t, toyModel.realizeAt () φ g⟩ :=
  interp_compileFO toyModel {} toyNaming () FOWords.nodup_default
    toyNaming_freshFor toyNaming_disjoint t g h

/-- "Some student sleeps" holds in the toy model, via the engine. -/
theorem someStudentSleeps_holds (g : Assignment ToyEntity) :
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
theorem conj_entails_first (g : Assignment ToyEntity) :
    HoldsAt toyModel (toyModel.lexiconFO {} toyNaming ()) g tree_conj →
      HoldsAt toyModel (toyModel.lexiconFO {} toyNaming ()) g
        (.bin (.leaf "John") (.leaf "sleeps")) :=
  holdsAt_of_models toyModel {} toyNaming () FOWords.nodup_default
    toyNaming_freshFor toyNaming_disjoint rfl rfl
    (λ _ S v h => by
      let _inst := S
      exact (FirstOrder.Language.Formula.realize_inf.mp h).1) g

end Reduction

end HeimKratzer1998
