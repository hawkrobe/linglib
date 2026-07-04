/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Fragments.English.Toy
import Linglib.Semantics.Intensional.CategoryType
import Linglib.Semantics.Quantification.Basic
import Linglib.Semantics.Quantification.Polyadic
import Linglib.Semantics.Composition.Scope

/-!
# Montague (1973): The Proper Treatment of Quantification in Ordinary English

[montague-1973], with the category-to-type correspondence in the form adopted
by [dowty-wall-peters-1981] (Ch. 7, Bennett's simplification).

PTQ's two central moves, exercised over the shared `Semantics.Montague` toy
fragment:

* **Compositional truth conditions.** Each predication receives its truth
  value from the `ToyLexicon` denotations alone (`§ Predication`).
* **Term phrases denote generalized quantifiers** (PTQ's category `T`), and a
  single English string can be assigned more than one meaning by quantifying a
  term in at one position or another (PTQ's rule S14). This is the source of
  quantifier scope ambiguity — handled *in the grammar*, not by a post-hoc
  scope-assignment rule (`§ Category-to-type correspondence`, `§ Scope
  ambiguity`).

## Grounding, not restipulation

The category-to-type function `f` and the named PTQ categories come from the
canonical `Intensional.CategoryType` (`PtqCat`/`catToTy`), so the IL types here
are the paper's — verbs and common nouns take **individual concepts** `⟨s,e⟩`,
not bare entities. The two scope readings are the shared GQ-level operators
`Quantification.Polyadic.surfaceScope`/`inverseScope` over the propositional
denotations `every_sem`/`some_sem`, and the ambiguous string is a
`Semantics.Scope.ScopeDerivation`. This makes PTQ's quantifying-in directly
comparable to the QR (`HeimKratzer1998`), Glue (`Asudeh2022`), and RSA
(`ScontrasPearl2021`) treatments of the same ambiguity, which
target the same substrate.

PTQ's distinctive intensional payload — individual concepts doing semantic work
in the temperature/price puzzle ("the temperature is ninety but it is rising")
and the de dicto/de re ambiguity of "John seeks a unicorn" — needs a model with
a nontrivial index set and is left to a dedicated intensional study; the toy
fragment here is extensional (`W = Unit`), so the "sees" example exercises only
the quantificational, not the intensional, side of PTQ.
-/

namespace Montague1973

open Semantics.Montague
open ToyLexicon
open Quantification (every_sem some_sem)
open Quantification.Polyadic (surfaceScope inverseScope)
open Semantics.Scope (ScopeConfig ScopeDerivation ScopeEntailment classifyScopeEntailment)

/-! ## Predication

Compositional truth conditions by direct function application over the toy
fragment. -/

theorem john_sleeps : sleeps_sem john_sem := trivial
theorem mary_not_sleeps : ¬sleeps_sem mary_sem := id
theorem john_laughs : laughs_sem john_sem := trivial
theorem mary_laughs : laughs_sem mary_sem := trivial

theorem john_sees_mary : sees_sem mary_sem john_sem := trivial
theorem mary_sees_john : sees_sem john_sem mary_sem := trivial
theorem john_not_sees_john : ¬sees_sem john_sem john_sem := id
theorem john_eats_pizza : eats_sem ToyEntity.pizza john_sem := trivial
theorem john_not_eats_mary : ¬eats_sem mary_sem john_sem := id
theorem mary_eats_pizza : eats_sem ToyEntity.pizza mary_sem := trivial
theorem john_reads_book : reads_sem ToyEntity.book john_sem := trivial

/-- Predication discriminates individuals in vs. out of the extension. -/
theorem intransitive_contrast :
    sleeps_sem john_sem ∧ ¬sleeps_sem mary_sem :=
  ⟨trivial, id⟩

/-- Transitive predication discriminates ordered pairs. -/
theorem transitive_contrast :
    sees_sem mary_sem john_sem ∧ ¬sees_sem john_sem john_sem :=
  ⟨trivial, id⟩

/-! ## Category-to-type correspondence

PTQ assigns every syntactic category a unique IL type via `f` (`catToTy` in
`Intensional.CategoryType`). The facts below anchor the categories relevant to
quantification; the general machinery lives in the substrate. -/

section Categories
open Intensional.CategoryType

/-- A **term phrase** (category `T`, e.g. "every student", "John") denotes a
    generalized quantifier over property-intensions of individual concepts:
    `f(T) = ⟨⟨s, ⟨⟨s,e⟩, t⟩⟩, t⟩`. Treating "every student" as a function on
    (intensions of) VP-meanings rather than as an entity is exactly what lets
    scope be assigned by the grammar. -/
theorem termPhrase_denotes_gq :
    catToTy PtqCat.T = .fn (.intens (.fn (.intens .e) .t)) .t :=
  catToTy_T

/-- A **determiner** (category `T/CN`, e.g. "every", "a") combines with a
    common-noun intension to yield a term-phrase meaning. -/
theorem determiner_type :
    catToTy PtqCat.DET
      = .fn (.intens (.fn (.intens .e) .t))
            (.fn (.intens (.fn (.intens .e) .t)) .t) :=
  catToTy_DET

/-- Common nouns and intransitive verbs share the IL type of **sets of
    individual concepts** `⟨⟨s,e⟩, t⟩` — PTQ's device for the
    temperature/price puzzle, where a verb predicates of a concept whose value
    varies, not of a fixed individual. -/
theorem cn_iv_same_type : catToTy PtqCat.CN = catToTy PtqCat.IV :=
  catToTy_CN_eq_IV

end Categories

/-! ## Scope ambiguity via quantifying-in (S14)

"Every student sees a person" has two readings, generated by quantifying the
two term phrases in at different points (PTQ's S14). They are the two linear
`Polyadic` readings of an `every`/`some` pair:

* **surface** (∀∃): every student `x` sees *some* person — possibly a different
  one for each `x`;
* **inverse** (∃∀): there is *one* person whom every student sees.

The paper's own non-intensional illustration is "a woman loves every man"
(§4), introduced precisely to show "that ambiguity can arise even when there is
no element of intensionality, simply because quantifying terms may be
introduced in more than one order." -/

/-- The toy "sees" relation as a subject-first binary predicate `x sees y`,
    read off the (object-first) fragment denotation `sees_sem`. `abbrev` so the
    `Decidable (sees_sem _ _)` instance below transports to `seesRel`. -/
abbrev seesRel (x y : ToyEntity) : Prop := sees_sem y x

/-- Each concrete `sees_sem a b` reduces to `True`/`False`, mirroring the
    fragment's own `DecidablePred` pattern. -/
instance (a b : ToyEntity) : Decidable (sees_sem a b) := by
  cases a <;> cases b <;> first | exact isTrue trivial | exact isFalse id

/-- **Surface reading is true** on the fragment: every student sees some
    person (John sees Mary, Mary sees John). -/
theorem everyStudentSeesAPerson_surface :
    surfaceScope every_sem some_sem student_sem person_sem seesRel := by
  intro x hx
  cases x
  · exact ⟨.mary, trivial, trivial⟩  -- John sees Mary
  · exact ⟨.john, trivial, trivial⟩  -- Mary sees John
  · exact absurd hx (by decide)      -- pizza is not a student
  · exact absurd hx (by decide)      -- book is not a student

/-- **Inverse reading is false** on the fragment: no single person is seen by
    every student (John sees only Mary; Mary sees only John). -/
theorem everyStudentSeesAPerson_inverse_false :
    ¬ inverseScope every_sem some_sem student_sem person_sem seesRel := by
  rintro ⟨y, hy, hall⟩
  cases y
  · exact hall .john trivial  -- John would have to see John
  · exact hall .mary trivial  -- Mary would have to see Mary
  · exact absurd hy (by decide)
  · exact absurd hy (by decide)

/-- The string is genuinely **ambiguous**: true on its surface reading, false
    on its inverse reading. -/
theorem everyStudentSeesAPerson_ambiguous :
    surfaceScope every_sem some_sem student_sem person_sem seesRel ∧
    ¬ inverseScope every_sem some_sem student_sem person_sem seesRel :=
  ⟨everyStudentSeesAPerson_surface, everyStudentSeesAPerson_inverse_false⟩

/-- **∃∀ ⊨ ∀∃.** For an `every`/`some` pair, the inverse (wide-existential)
    reading entails the surface (wide-universal) reading, over *any* domain,
    restrictors, and relation. PTQ's S14 generates both readings; this is the
    one-directional entailment between them, and it is why a context can never
    make the inverse reading true without the surface reading being true too. -/
theorem every_some_inverse_entails_surface {α : Type*} (A B : α → Prop)
    (R : α → α → Prop) :
    inverseScope every_sem some_sem A B R → surfaceScope every_sem some_sem A B R := by
  rintro ⟨y, hy, hall⟩ x hx
  exact ⟨y, hy, hall x hx⟩

/-- "Every student sees a person" as a single syntactic form carrying both
    scope-indexed meanings, in the shared `ScopeDerivation` representation —
    the same type targeted by `HeimKratzer1998` (QR), `Asudeh2022` (Glue), and
    `ScontrasPearl2021` (RSA). -/
def everyStudentSeesAPerson : ScopeDerivation ToyEntity Unit .t where
  surface := "every student sees a person"
  meaningAt
    | .surface => surfaceScope every_sem some_sem student_sem person_sem seesRel
    | .inverse => inverseScope every_sem some_sem student_sem person_sem seesRel

/-- Truth of the surface (∀∃) reading over the single extensional world. The
    `Prop` is written explicitly (rather than as `everyStudentSeesAPerson.meaningAt
    .surface`) so `Decidable` synthesises over `ToyEntity`; `surfaceTruth_iff`
    certifies it is the same reading. -/
def surfaceTruth (_ : Unit) : Bool :=
  decide (∀ x : ToyEntity, student_sem x → ∃ y : ToyEntity, person_sem y ∧ seesRel x y)

/-- Truth of the inverse (∃∀) reading; `inverseTruth_iff` ties it to the
    `ScopeDerivation`. -/
def inverseTruth (_ : Unit) : Bool :=
  decide (∃ y : ToyEntity, person_sem y ∧ ∀ x : ToyEntity, student_sem x → seesRel x y)

/-- The `Bool` surface truth function reflects the `ScopeDerivation`'s surface
    meaning — certifying that the explicitly-written `Prop` in `surfaceTruth` is
    `everyStudentSeesAPerson.meaningAt .surface`, not merely asserted to be. -/
theorem surfaceTruth_iff :
    surfaceTruth () = true ↔ everyStudentSeesAPerson.meaningAt .surface :=
  decide_eq_true_iff

/-- The `Bool` inverse truth function reflects the `ScopeDerivation`'s inverse
    meaning. -/
theorem inverseTruth_iff :
    inverseTruth () = true ↔ everyStudentSeesAPerson.meaningAt .inverse :=
  decide_eq_true_iff

/-- In the shared `ScopeEntailment` vocabulary (cf.
    `ScontrasPearl2021.every_not_scope_entailment`, which gets
    `surfaceEntailsInverse` for "every…not"), the `every`/`some` pair
    classifies as `inverseEntailsSurface`: inverse ⊨ surface (held across the
    checked world), surface ⊭ inverse (the toy world makes surface true and
    inverse false). The general direction is `every_some_inverse_entails_surface`. -/
theorem everyStudentSeesAPerson_scope_entailment :
    classifyScopeEntailment [()] surfaceTruth inverseTruth
      = ScopeEntailment.inverseEntailsSurface := by
  decide

end Montague1973
