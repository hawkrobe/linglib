import Linglib.Features.NounCategorization.Basic
import Linglib.Syntax.Tree.Cat
import Linglib.Core.Logic.Assignment
import Linglib.Semantics.Intensional.Defs
import Linglib.Semantics.Composition.Tree
import Linglib.Studies.Chierchia1998
import Linglib.Fragments.Mayan.Chol.ClassifierSystem
import Linglib.Fragments.Shan.ClassifierSystem

/-!
# Little, Moroney & Royer (2022)
[little-moroney-royer-2022]

Classifiers can be for numerals *or* nouns: Two strategies for numeral
modification. *Glossa* 7(1). 1–35.

Numeral classifiers form a heterogeneous class. Ch'ol (CLF-for-NUM, the
classifier is a measure function required by the numeral) and Shan
(CLF-for-N, the classifier atomizes the noun denotation) take different
compositional paths to the same denotation for "two dogs". This file
exercises that claim against linglib's type-driven composition
machinery: two `Tree String` derivations, distinct lexicons, identical
extension at the root.

## Main declarations

* `cholStrategy`, `shanStrategy` — LMR's per-language assignments
* `Predictions` — LMR's four-diagnostic battery (Table 8)
* `cholTree`, `cholLex`, `shanTree`, `shanLex` — derivations (51), (52)
  driven through `Semantics.Composition.Tree.interp`
* `cholTree_interprets`, `shanTree_interprets` — `rfl` witnesses that
  Heim-Kratzer FA composes the lexicons through the trees
* `section5_extensionally_equal` — LMR §5 main result: the two trees
  evaluate to extensionally-equal predicates of type `⟨e,t⟩`

## Implementation notes

The semantic carrier is `Finset Dog` (atomic powerset model with `∅`
excluded by `.Nonempty`). The Heim-Kratzer Ty system (`e`, `t`, `fn`,
`intens`) lacks a number type, so LMR's measure function `μ_# : ⟨e,n⟩`
is folded into the numeral's denotation as a `Finset.card`-via-`Prop`
constraint rather than realized as a stand-alone constituent of type
`⟨e,n⟩`. The constituency contrast — `[[Num Clf] N]` vs `[Num [Clf N]]`
— is faithful; only the type of the measure is encoded indirectly.
-/

namespace LittleMoroneyRoyer2022

open NounCategorization
open Intensional (Ty)
open Semantics.Montague (LexEntry Lexicon)
open Semantics.Composition.Tree (interp)
open Syntax (Tree)

abbrev chol := Chol.classifierSystem
abbrev shan := Shan.classifierSystem

/-! ### Predictions (Table 8) -/

structure Predictions where
  numeralIdiosyncrasies : Prop
  nounIdiosyncrasies : Prop
  clfBeyondNumerals : Prop
  clfInCounting : Prop

def clfForNumPredictions : Predictions where
  numeralIdiosyncrasies := True
  nounIdiosyncrasies := False
  clfBeyondNumerals := False
  clfInCounting := True

def clfForNounPredictions : Predictions where
  numeralIdiosyncrasies := False
  nounIdiosyncrasies := True
  clfBeyondNumerals := True
  clfInCounting := False

def cholStrategy : ClassifierStrategy := .forNumeral
def shanStrategy : ClassifierStrategy := .forNoun

theorem profiles_distinct : clfForNumPredictions ≠ clfForNounPredictions := fun h =>
  cast (congrArg Predictions.numeralIdiosyncrasies h) trivial

/-! ### Plural co-occurrence (§3.4)

[little-moroney-royer-2022] §3.4 refines [borer-2005]'s
complementarity intuition: CLF and PL share a functional projection in
CLF-for-N languages, separate projections in CLF-for-NUM languages. -/

theorem complementarity_refined_by_strategy :
    cholStrategy = .forNumeral ∧ chol.PluralClfCooccur ∧
      shanStrategy = .forNoun ∧ ¬ shan.PluralClfCooccur := by decide

/-! ### Compositional derivation (§2.3, §5)

Worked example on three dogs. The two trees compose under
`Semantics.Composition.Tree.interp` against per-language lexicons; the
§5 main result is established as extensional equivalence of the root
denotations. -/

inductive Dog | a | b | c
  deriving DecidableEq, Repr, Fintype

/-! LMR's semantic carrier is `Finset Dog` (Link-style sums of dog-atoms with
`∅` excluded downstream by `.Nonempty`), with `Unit` indices (extensional). -/

/-- Empty variable assignment; the §2.3 trees contain no traces. -/
def emptyAssign : Core.Assignment (Finset Dog) := fun _ => ∅

/-- Ch'ol lexicon. cha' is the measure-loaded numeral
`λκ λP λx. P x ∧ κ x ∧ |x| = 2`; kojty contributes a (semantically
vacuous) sortal restriction; ts'i' is the dog predicate. The
`⟨e,n⟩` measure type is folded into cha'. -/
def cholLex : Lexicon (Finset Dog) Unit
  | "cha'" => some
      { ty := .fn (.fn .e .t) (.fn (.fn .e .t) (.fn .e .t))
        denot := fun (κ : Finset Dog → Prop) (P : Finset Dog → Prop)
                     (x : Finset Dog) => P x ∧ κ x ∧ x.card = 2 }
  | "kojty" => some
      { ty := .fn .e .t
        denot := fun (_ : Finset Dog) => True }
  | "ts'i'" => some
      { ty := .fn .e .t
        denot := fun (x : Finset Dog) => x.Nonempty }
  | _ => none

/-- Shan lexicon. tǒ atomizes the noun predicate (`λP λx. P x ∧ |x| = 1`);
sǒŋ selects 2-element joins of distinct atoms from an atomized predicate;
mǎa is the dog predicate. -/
def shanLex : Lexicon (Finset Dog) Unit
  | "sǒŋ" => some
      { ty := .fn (.fn .e .t) (.fn .e .t)
        denot := fun (P : Finset Dog → Prop) (x : Finset Dog) =>
          ∃ d₁ d₂ : Dog, d₁ ≠ d₂ ∧ P {d₁} ∧ P {d₂} ∧ x = {d₁, d₂} }
  | "tǒ" => some
      { ty := .fn (.fn .e .t) (.fn .e .t)
        denot := fun (P : Finset Dog → Prop) (x : Finset Dog) =>
          P x ∧ x.card = 1 }
  | "mǎa" => some
      { ty := .fn .e .t
        denot := fun (x : Finset Dog) => x.Nonempty }
  | _ => none

/-- Ch'ol derivation (51): `[[cha' kojty] ts'i']`. Num+CLF form a
constituent that then applies to the noun. -/
def cholTree : Tree Unit String :=
  .bin (.bin (.leaf "cha'") (.leaf "kojty")) (.leaf "ts'i'")

/-- Shan derivation (52): `[sǒŋ [tǒ mǎa]]`. CLF+N form a constituent
that the numeral then selects from. -/
def shanTree : Tree Unit String :=
  .bin (.leaf "sǒŋ") (.bin (.leaf "tǒ") (.leaf "mǎa"))

/-- Ch'ol composition: `cha'(kojty)(ts'i')` = `λx. ts'i'(x) ∧ kojty(x) ∧
|x| = 2` after two rounds of FA. -/
def cholDenot : Finset Dog → Prop :=
  fun x => x.Nonempty ∧ True ∧ x.card = 2

/-- Shan composition: `sǒŋ(tǒ(mǎa))` = `λx. ∃ d₁ d₂, d₁ ≠ d₂ ∧
(tǒ(mǎa)) {d₁} ∧ (tǒ(mǎa)) {d₂} ∧ x = {d₁,d₂}` after two rounds of FA. -/
def shanDenot : Finset Dog → Prop :=
  fun x => ∃ d₁ d₂ : Dog, d₁ ≠ d₂ ∧
    (({d₁} : Finset Dog).Nonempty ∧ ({d₁} : Finset Dog).card = 1) ∧
    (({d₂} : Finset Dog).Nonempty ∧ ({d₂} : Finset Dog).card = 1) ∧
    x = {d₁, d₂}

/-- The Ch'ol tree interprets to `cholDenot` via two FA steps under the
Ch'ol lexicon. -/
theorem cholTree_interprets :
    interp (Finset Dog) Unit cholLex emptyAssign cholTree =
      some ⟨.fn .e .t, cholDenot⟩ := rfl

/-- The Shan tree interprets to `shanDenot` via two FA steps under the
Shan lexicon. -/
theorem shanTree_interprets :
    interp (Finset Dog) Unit shanLex emptyAssign shanTree =
      some ⟨.fn .e .t, shanDenot⟩ := rfl

/-- LMR §5 main result: despite different constituency and different
per-word lexical entries, the two derivations yield extensionally
equivalent root denotations on the count-noun case. The proof discharges
the trivial conjuncts and reduces to `Finset.card_eq_two`. -/
theorem section5_extensionally_equal (x : Finset Dog) :
    cholDenot x ↔ shanDenot x := by
  simp only [cholDenot, shanDenot]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, hcard⟩
    obtain ⟨d₁, d₂, hne, rfl⟩ := Finset.card_eq_two.mp hcard
    refine ⟨d₁, d₂, hne, ?_, ?_, rfl⟩
    · exact ⟨⟨d₁, Finset.mem_singleton.mpr rfl⟩, Finset.card_singleton d₁⟩
    · exact ⟨⟨d₂, Finset.mem_singleton.mpr rfl⟩, Finset.card_singleton d₂⟩
  · rintro ⟨d₁, d₂, hne, _, _, rfl⟩
    exact ⟨⟨d₁, Finset.mem_insert_self d₁ {d₂}⟩, trivial, Finset.card_pair hne⟩

/-! ### Cross-paper consistency with Chierchia 1998 -/

/-- Shan agrees with [chierchia-1998]'s NMP prediction for
Mandarin/Japanese — all three are CLF-for-N. -/
theorem shan_agrees_with_chierchia :
    shanStrategy = NMP.mandarinStrategy ∧ shanStrategy = NMP.japaneseStrategy :=
  ⟨rfl, rfl⟩

/-- Ch'ol is CLF-for-NUM, *not* the CLF-for-N predicted for
Mandarin/Japanese under NMP. -/
theorem chol_differs_from_chierchia : cholStrategy ≠ NMP.mandarinStrategy := by decide

end LittleMoroneyRoyer2022
