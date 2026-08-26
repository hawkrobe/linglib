import Mathlib.Data.Finset.Grade
import Linglib.Core.Order.Valuation
import Linglib.Semantics.Classifier
import Linglib.Semantics.Composition.Tree
import Linglib.Studies.Chierchia1998
import Linglib.Studies.IoninMatushansky2006
import Linglib.Fragments.Mayan.Chol.Classifiers
import Linglib.Fragments.Shan.Classifiers

/-!
# Little, Moroney & Royer (2022)

Numeral classifiers are not one thing. In a classifier-for-numeral
language the classifier is the measure function the numeral demands; in a
classifier-for-noun language it atomizes the noun so that a partition
numeral can count. Ch'ol takes the first path and Shan the second, with
constituency `[[Num Clf] N]` versus `[Num [Clf N]]`, yet both reach the
same denotation for *two dogs*.

The two lexicons `cholLex` and `shanLex` are driven through
`Semantics.Composition.Tree.interp` over the substrate's own classifier
denotations: the Ch'ol root is `Semantics.Classifier.clfForNum`
(`cholTree_interp`), the Shan root is `IoninMatushansky2006.cardMod` over
`Semantics.Classifier.clfForNoun` (`shanTree_interp`), and the two agree
(`forNumeral_iff_forNoun`). The distributional diagnostics of the paper's
§4 then follow from the lexical types alone — what composes without a noun
(`chol_numClf_composes`, `shan_numClf_fails`) and what composes without a
numeral (`shan_clfNoun_composes`, `chol_clfNoun_fails`, `chol_ocho`).

Pluralities are `Finset α`, the atoms and their sums with `∅` excluded by
`Finset.Nonempty`, so the measure function μ# is `Finset.card` at type
`⟨e,n⟩` — the grade of the plurality lattice (`Finset.grade_eq`) and a
positive valuation on it, which is all quantization needs
(`clfForNum_dogs_qua`). Prediction 2 of §4 (nouns that need no classifier)
rests on Vietnamese rather than Ch'ol or Shan data and is not formalized.

## References

* [little-moroney-royer-2022], §2.3 (6)–(13), §3.4, §4, §4.5 (51)–(52)
* [ionin-matushansky-2006]
* [chierchia-1998]
* [bale-coon-2014]
* [borer-2005]
* [krifka-1995b]
-/

namespace LittleMoroneyRoyer2022

open Intensional (Ty Denot)
open Semantics.Classifier (clfForNum clfForNoun)
open Semantics.Composition.Tree (interp)
open Semantics.Montague (Lexicon)
open Syntax (Tree)
open IoninMatushansky2006 (cardMod IsAtomOf cardMod_atoms_iff)
/-! ### The two strategies -/

/-- Ch'ol is classifier-for-numeral (Table 8). -/
def cholStrategy : Classifier.Strategy := .forNumeral

/-- Shan is classifier-for-noun (Table 8). -/
def shanStrategy : Classifier.Strategy := .forNoun

variable {α : Type} (g : Assignment (Finset α))

/-! ### Count nouns, measured and atomized -/

/-- A count noun denotes the atoms and their sums ((6)). -/
def dogs (x : Finset α) : Prop := x.Nonempty

theorem clfForNum_dogs_iff (x : Finset α) : clfForNum dogs Finset.card 2 x ↔ x.card = 2 := by
  simp only [clfForNum, Mereology.QMOD, dogs, ← Finset.card_pos]
  omega

/-- Atomizing a count noun yields the atoms of the plurality lattice
(`Mereology.atomize_ne_bot`), the singletons `IoninMatushansky2006.IsAtomOf`. -/
theorem clfForNoun_dogs : (clfForNoun dogs : Finset α → Prop) = IsAtomOf (λ _ => True) := by
  have h : (dogs : Finset α → Prop) = (· ≠ ⊥) :=
    funext λ _ => propext Finset.nonempty_iff_ne_empty
  rw [show (clfForNoun dogs : Finset α → Prop) = Mereology.atomize (· ≠ ⊥) from
    congrArg Mereology.atomize h, Mereology.atomize_ne_bot]
  funext x
  simp [Finset.isAtom_iff, IsAtomOf]

/-! ### Ch'ol: classifier-for-numeral -/

/-- *cha'* 'two' takes a measure function and then a predicate ((7)), the
classifier *-kojty* is μ# ((8)) keyed on `Chol.Classifiers.kojty`, the
Spanish loan *ocho* 'eight' has its measure built in ((34b)), and *ts'i'*
is 'dog'. -/
def cholLex : Lexicon (Finset α) Unit := λ w =>
  if w = "cha'" then some ⟨(.e ⇒ .n) ⇒ (.e ⇒ .t) ⇒ .e ⇒ .t,
    show (Finset α → ℕ) → (Finset α → Prop) → Finset α → Prop from
      λ m P x => P x ∧ m x = 2⟩
  else if w = Chol.Classifiers.kojty.form then some ⟨.e ⇒ .n, Finset.card⟩
  else if w = "ocho" then some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t,
    show (Finset α → Prop) → Finset α → Prop from λ P x => P x ∧ x.card = 8⟩
  else if w = "ts'i'" then some ⟨.e ⇒ .t, dogs⟩
  else none

/-- *cha'-kojty*: numeral and classifier form a constituent ((23a)). -/
def cholNumClf : Tree Unit String := .bin (.leaf "cha'") (.leaf Chol.Classifiers.kojty.form)

/-- `[[cha' -kojty] ts'i']` ((51)). -/
def cholTree : Tree Unit String := .bin cholNumClf (.leaf "ts'i'")

/-- The Ch'ol root is the measure-modified noun `λx. dogs x ∧ μ# x = 2` ((51)). -/
theorem cholTree_interp :
    interp (Finset α) Unit cholLex g cholTree = some ⟨.e ⇒ .t, clfForNum dogs Finset.card 2⟩ :=
  rfl

/-- Numeral and classifier compose without a noun, into the measure phrase
`λP λx. P x ∧ μ# x = 2` ((45)–(46), Prediction 4). -/
theorem chol_numClf_composes :
    interp (Finset α) Unit cholLex g cholNumClf =
      some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t, λ P => clfForNum P Finset.card 2⟩ :=
  rfl

/-- The classifier, a measure of type `⟨e,n⟩`, cannot compose with the noun
without the numeral ((43a)). -/
theorem chol_clfNoun_fails :
    interp (Finset α) Unit cholLex g (.bin (.leaf Chol.Classifiers.kojty.form) (.leaf "ts'i'")) =
      none :=
  rfl

/-- *ocho* composes with the noun directly and rejects the classifier
((33)–(34), Prediction 1). -/
theorem chol_ocho :
    interp (Finset α) Unit cholLex g (.bin (.leaf "ocho") (.leaf "ts'i'")) =
        some ⟨.e ⇒ .t, clfForNum dogs Finset.card 8⟩ ∧
      interp (Finset α) Unit cholLex g (.bin (.leaf "ocho") (.leaf Chol.Classifiers.kojty.form)) =
        none :=
  ⟨rfl, rfl⟩

section

variable [DecidableEq α]

/-! ### Shan: classifier-for-noun -/

/-- *sɔ̌ŋ* 'two' is the partition numeral ((10), `IoninMatushansky2006.cardMod`),
the classifier *tǒ* atomizes ((13), `Semantics.Classifier.clfForNoun`) keyed
on `Shan.Classifiers.to`, and *mǎa* is 'dog'. -/
def shanLex : Lexicon (Finset α) Unit := λ w =>
  if w = "sɔ̌ŋ" then some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t, cardMod 2⟩
  else if w = Shan.Classifiers.to.form then some ⟨(.e ⇒ .t) ⇒ .e ⇒ .t,
    show (Finset α → Prop) → Finset α → Prop from clfForNoun⟩
  else if w = "mǎa" then some ⟨.e ⇒ .t, dogs⟩
  else none

/-- *tǒ mǎa*: classifier and noun form a constituent ((23b)). -/
def shanClfNoun : Tree Unit String := .bin (.leaf Shan.Classifiers.to.form) (.leaf "mǎa")

/-- `[sɔ̌ŋ [tǒ mǎa]]` ((52)), abstracting from the surface order *mǎa sɔ̌ŋ tǒ*
((25)) as the paper does. -/
def shanTree : Tree Unit String := .bin (.leaf "sɔ̌ŋ") shanClfNoun

/-- The Shan root is the partition numeral over the atomized noun ((52)). -/
theorem shanTree_interp :
    interp (Finset α) Unit shanLex g shanTree = some ⟨.e ⇒ .t, cardMod 2 (clfForNoun dogs)⟩ :=
  rfl

/-- Classifier and noun compose without a numeral, yielding the atoms
((42), Prediction 3). -/
theorem shan_clfNoun_composes :
    interp (Finset α) Unit shanLex g shanClfNoun =
      some ⟨.e ⇒ .t, (clfForNoun dogs : Finset α → Prop)⟩ :=
  rfl

/-- Numeral and classifier, both `⟨⟨e,t⟩,⟨e,t⟩⟩`, do not compose without the
noun ((48)–(49)). -/
theorem shan_numClf_fails :
    interp (Finset α) Unit shanLex g (.bin (.leaf "sɔ̌ŋ") (.leaf Shan.Classifiers.to.form)) =
      none :=
  rfl

/-! ### One denotation for *two dogs* -/

/-- Measure modification by the atom count is quantized: `Finset.card` is a
positive valuation, and strict monotonicity is all `qua_pullback` needs. -/
theorem clfForNum_dogs_qua : Mereology.QUA (clfForNum dogs Finset.card 2 : Finset α → Prop) := by
  refine (Mereology.qua_pullback ?_ (Mereology.singleton_qua 2)).subset λ _ h => h.2
  exact IsPositiveValuation.strictMono (v := (Finset.card : Finset α → ℕ))

/-- Derivationally distinct, the two strategies denote the same two-dog
pluralities (§4.5). -/
theorem forNumeral_iff_forNoun (x : Finset α) :
    clfForNum dogs Finset.card 2 x ↔ cardMod 2 (clfForNoun dogs) x := by
  simp [clfForNum_dogs_iff, clfForNoun_dogs, cardMod_atoms_iff]

/-- Three dogs ((6)). -/
inductive Dog | a | b | c
  deriving DecidableEq, Fintype

-- *two dogs* denotes `{ab, ac, bc}` ((51)–(52)).
example (x : Finset Dog) :
    clfForNum dogs Finset.card 2 x ↔
      x ∈ ({{.a, .b}, {.a, .c}, {.b, .c}} : Finset (Finset Dog)) :=
  (clfForNum_dogs_iff x).trans (by revert x; decide)

end

/-! ### Plural marking -/

/-- [borer-2005]'s classifier–plural complementarity holds in Shan, where
both occupy one projection, and lifts in Ch'ol ((30), §3.4). -/
theorem plural_cooccurrence :
    Chol.pluralClassifierCooccur = true ∧ Shan.pluralClassifierCooccur = false := ⟨rfl, rfl⟩

/-! ### Against a uniform classifier semantics -/

/-- [chierchia-1998]'s classifier-for-noun analysis of Mandarin extends to
Shan but not to Ch'ol. -/
theorem chierchia_covers_shan_not_chol :
    shanStrategy = NMP.mandarinStrategy ∧ cholStrategy ≠ NMP.mandarinStrategy := by
  decide

end LittleMoroneyRoyer2022
