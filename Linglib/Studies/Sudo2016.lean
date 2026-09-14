import Linglib.Semantics.Plurality.Algebra
import Linglib.Semantics.Presupposition.Defs
import Linglib.Semantics.Reference.Rigidity
import Linglib.Fragments.Japanese.Classifiers
import Linglib.Studies.Chierchia1998
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card

/-!
# Sudo (2016): The Semantic Role of Classifiers in Japanese

This file formalizes [sudo-2016]'s account of why Japanese numerals require classifiers: not
the semantics of nouns, as in [chierchia-1998] and [krifka-2008], but the semantics of
numerals. Numerals in every language denote singular terms of type `n`, constant intensions
(`numeral`, `numeral_isRigid`), which cannot modify or predicate on their own. A classifier
turns such a term into a property: a sortal classifier presupposes the plural closure of its
sortal predicate and counts the sortal atoms of its argument (`Sortal.apply`), the paper's
(4) and (8), and a non-atomic classifier such as *-kumi* 'pair' counts non-overlapping
groups of a fixed size (`groupApply`), so that four books form two pairs and never six
(`groupApply_card`, `four_books_two_pairs`, `four_books_not_six_pairs`). Non-classifier
languages reach the same properties through the silent ∪-operator, which maps a numeral to
the property of having that many atomic parts (`up`); by the Blocking Principle its use is
unavailable in a language whose lexicon has overt items with the same function, the
classifiers. The ways a numeral becomes a predicate are therefore the ∪-operator where no
classifier blocks it and an overt classifier otherwise (`PredicateOf`): with classifiers in
the lexicon, as the Japanese fragment has (`japanese_has_classifiers`), every predicate use
of a numeral goes through a classifier and carries its sortal presupposition
(`predicateOf_iff_of_hasClassifiers`), the paper's contrast between the ungrammatical bare
predicative numeral of (15) and its classifier-suffixed counterpart (16). The inverse
∩-operator maps a property of having a fixed number of atoms back to its numeral (`IsDown`,
`isDown_up`), has no overt counterpart and so is available in Japanese, where it returns
the type-`n` correlate of a numeral-plus-classifier phrase (`isDown_sortal`), the paper's
(22) to (25). The disagreement with [chierchia-1998] over Japanese is a difference in the
strategy assigned to the language (`sudo_disagrees_with_chierchia_on_japanese`).

## Implementation notes

Type `n` is `ℕ`, and the paper's extension of the type-`n` domain to the correlates of
classifier phrases is represented by stating ∩ relative to the classifier's sortal. The
∪-shifted composition rules (11), (19) and (26) are represented by the derivation relation
`PredicateOf` rather than as rules with domain conditions, and the paper's observation that
English numerals fail in some predicative constructions is not modelled. The witnesses use
the set-based ontology of the plural algebra, an individual being its singleton and sum
union, on which the atom count of a plurality is its cardinality (`atomCount_finset`).

## References

* [sudo-2016]
* [chierchia-1998]
* [rothstein-2013]
* [link-1983]
* [heim-kratzer-1998]
* [krifka-2008]
-/

namespace Sudo2016

open Plurality.Algebra Mereology Presupposition

section General

variable {W E : Type*} [SemilatticeSup E]

/-! ### Numerals and classifiers -/

/-- A numeral denotes a singular term of type `n`, the constant intension of the paper's (2). -/
def numeral (n : ℕ) : W → ℕ := λ _ => n

theorem numeral_isRigid (n : ℕ) : Reference.IsRigid (numeral (W := W) n) :=
  Reference.isRigid_const n

/-- The number of atomic `P`-parts of `x` at a world. -/
noncomputable def atomCount (P : W → E → Prop) (w : W) (x : E) : ℕ := {y | y ≤ x ∧ P w y}.ncard

/-- A sortal predicate of atoms, indexed by worlds: the metalanguage predicates *flower*,
*human* of the paper's (4) and (8). -/
abbrev Sortal (W E : Type*) := W → E → Prop

/-- A sortal classifier applied to a numeral, the paper's (4) and (7b): at each world, a
partial property presupposing the plural closure of the sortal and asserting that the
argument has the numeral's number of sortal atoms. -/
def Sortal.apply (c : Sortal W E) (n : W → ℕ) (w : W) : PartialProp E where
  presup := star (c w)
  assertion x := atomCount c w x = n w

/-- The ∪-operator, the paper's (10): the property correlate of a numeral, having that many
atomic parts. -/
def up (atomic : Sortal W E) (n : W → ℕ) : W → E → Prop := λ w x => atomCount atomic w x = n w

/-- The classifier's assertion is the ∪-correlate of the numeral counted over the sortal. -/
theorem apply_assertion (c : Sortal W E) (n : W → ℕ) (w : W) :
    (c.apply n w).assertion = up c n w := rfl

/-- Predicate Modification with a presupposed modifier, the paper's (6): the noun is
conjoined with the assertion and the presupposition projects. -/
def modify (P : PartialProp E) (N : E → Prop) : PartialProp E where
  presup := P.presup
  assertion x := P.assertion x ∧ N x

/-- Modifying the noun whose denotation is the plural closure of the classifier's own
sortal, the paper's (7c): the presupposition is then entailed by the noun. -/
theorem modify_sortal_presup (c : Sortal W E) (n : W → ℕ) (w : W) (x : E)
    (h : (modify (c.apply n w) (star (c w))).assertion x) :
    (modify (c.apply n w) (star (c w))).presup x :=
  h.2

/-! ### The ∩-operator -/

/-- `IsDown atomic P n`: the property `P` is the ∪-correlate of the numeral `n`, so that ∩
maps it back to `n`, the paper's (24). -/
def IsDown (atomic : Sortal W E) (P : W → E → Prop) (n : W → ℕ) : Prop :=
  ∀ w x, P w x ↔ atomCount atomic w x = n w

theorem isDown_up (atomic : Sortal W E) (n : W → ℕ) : IsDown atomic (up atomic n) n :=
  λ _ _ => Iff.rfl

/-- ∩ is a partial inverse: a property with a type-`n` correlate has only one, provided every
count is instantiated. -/
theorem IsDown.unique {atomic : Sortal W E} {P : W → E → Prop} {n m : W → ℕ}
    (hn : IsDown atomic P n) (hm : IsDown atomic P m)
    (hsurj : ∀ w, ∃ x, atomCount atomic w x = n w) : n = m := by
  funext w
  obtain ⟨x, hx⟩ := hsurj w
  exact hx.symm.trans ((hm w x).mp ((hn w x).mpr hx))

/-- A numeral-plus-classifier phrase has a type-`n` correlate relative to the classifier's
sortal, the paper's (25): ∩ applies in Japanese to *juu-ni-nin* and returns twelve. -/
theorem isDown_sortal (c : Sortal W E) (n : W → ℕ) :
    IsDown c (λ w x => (c.apply n w).assertion x) n :=
  λ _ _ => Iff.rfl

/-! ### Blocking -/

/-- The ways a numeral becomes a predicate: the silent ∪-operator, available only when no
overt classifier is in the lexicon, or an overt classifier, which adds its sortal
presupposition. -/
inductive PredicateOf (hasClassifiers : Prop) (atomic : Sortal W E) (n : W → ℕ) :
    (W → E → Prop) → Prop
  | up (h : ¬ hasClassifiers) : PredicateOf hasClassifiers atomic n (up atomic n)
  | classifier (c : Sortal W E) :
      PredicateOf hasClassifiers atomic n
        λ w x => (c.apply n w).presup x ∧ (c.apply n w).assertion x

/-- With classifiers in the lexicon every predicate use of a numeral goes through a
classifier and carries its sortal presupposition: the paper's (15) against (16). -/
theorem predicateOf_iff_of_hasClassifiers {hasClassifiers : Prop} (h : hasClassifiers)
    (atomic : Sortal W E) (n : W → ℕ) (P : W → E → Prop) :
    PredicateOf hasClassifiers atomic n P ↔
      ∃ c : Sortal W E, P = λ w x => (c.apply n w).presup x ∧ (c.apply n w).assertion x := by
  constructor
  · rintro (⟨hno⟩ | ⟨c⟩)
    · exact absurd h hno
    · exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact .classifier c

/-- Without classifiers the bare ∪-shift is available, the paper's (18) for English. -/
theorem predicateOf_up (atomic : Sortal W E) (n : W → ℕ) :
    PredicateOf False atomic n (up atomic n) :=
  .up id

end General

/-- The Japanese lexicon has classifiers, as the fragment records. -/
theorem japanese_has_classifiers : Japanese.Classifier.all ≠ [] := by decide

/-- Sudo's strategy assignment for Japanese: the classifier blocks the silent ∪-operator on
numerals. -/
def japaneseStrategy : Classifier.Strategy := .sudoBlocking

/-- Sudo and Chierchia assign Japanese different strategies: the classifier atomizes a
kind-denoting noun for [chierchia-1998], and blocks the ∪-operator on numerals here. -/
theorem sudo_disagrees_with_chierchia_on_japanese :
    japaneseStrategy ≠ NMP.japaneseStrategy := by decide

/-! ### Witnesses on the set-based ontology -/

section Model

variable {α : Type*} [DecidableEq α]

/-- An individual as its singleton: the sortal predicate `P` of atoms lifted to pluralities. -/
def singletonSortal (P : α → Prop) : Sortal Unit (Finset α) :=
  λ _ y => ∃ a, y = {a} ∧ P a

/-- The atom count of a plurality is the number of its members satisfying the sortal. -/
theorem atomCount_finset (P : α → Prop) [DecidablePred P] (x : Finset α) :
    atomCount (singletonSortal P) () x = (x.filter P).card := by
  have : {y : Finset α | y ≤ x ∧ singletonSortal P () y} =
      ↑((x.filter P).image ({·} : α → Finset α)) := by
    ext y
    simp only [Set.mem_ofPred_eq, singletonSortal, Finset.coe_image, Finset.coe_filter,
      Set.mem_image]
    constructor
    · rintro ⟨hle, a, rfl, hP⟩
      exact ⟨a, ⟨Finset.singleton_subset_iff.mp hle, hP⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hP⟩, rfl⟩
      exact ⟨Finset.singleton_subset_iff.mpr ha, a, rfl, hP⟩
  rw [atomCount, this, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ Finset.singleton_injective]

/-- The presupposition of a sortal classifier on the set-based ontology: a nonempty
plurality of sortal individuals. -/
theorem presup_finset (P : α → Prop) (n : Unit → ℕ) (x : Finset α) :
    ((singletonSortal P).apply n ()).presup x ↔ x.Nonempty ∧ ∀ a ∈ x, P a := by
  show star (singletonSortal P ()) x ↔ _
  rw [star_iff_of_subset_range_singleton λ y hy => by obtain ⟨a, hy, _⟩ := hy; exact ⟨a, hy.symm⟩]
  simp [singletonSortal]

/-- A non-atomic classifier counting groups of `k` atoms, the paper's (9): the argument is
the sum of `n` non-overlapping pluralities of `k` members each. -/
def groupApply (k n : ℕ) (x : Finset α) : Prop :=
  ∃ s : Finset (Finset α), s.card = n ∧ s.biUnion id = x ∧ (∀ y ∈ s, y.card = k) ∧
    ∀ y ∈ s, ∀ z ∈ s, y ≠ z → Disjoint y z

/-- Non-overlap makes the count exact: `n` groups of `k` have `n * k` atoms. -/
theorem groupApply_card {k n : ℕ} {x : Finset α} (h : groupApply k n x) : x.card = n * k := by
  obtain ⟨s, hs, rfl, hk, hd⟩ := h
  rw [Finset.card_biUnion (t := id) hd]
  simp only [id_eq]
  rw [Finset.sum_congr rfl λ y hy => hk y hy, Finset.sum_const, hs]
  rfl

/-- The individuals of the witnesses: three flowers, two humans, four books. -/
inductive Ind
  | f1 | f2 | f3 | h1 | h2 | b1 | b2 | b3 | b4
  deriving DecidableEq, Repr

def Ind.flower : Ind → Prop
  | .f1 | .f2 | .f3 => True
  | _ => False

instance : DecidablePred Ind.flower := λ a => by cases a <;> unfold Ind.flower <;> infer_instance

/-- *-rin* counts flowers. -/
def rin : Sortal Unit (Finset Ind) := singletonSortal Ind.flower

/-- *san-rin* holds of three flowers, its presupposition met, and fails of two of them. -/
theorem rin_three :
    (rin.apply (numeral 3) ()).presup {.f1, .f2, .f3} ∧
      (rin.apply (numeral 3) ()).assertion {.f1, .f2, .f3} ∧
      ¬ (rin.apply (numeral 3) ()).assertion {.f1, .f2} := by
  refine ⟨(presup_finset _ _ _).mpr (by decide), ?_, ?_⟩ <;>
    simp only [Sortal.apply, rin, atomCount_finset, numeral] <;> decide

/-- The sortal presupposition fails of a human: *-rin* does not count people. -/
theorem rin_not_human : ¬ (rin.apply (numeral 1) ()).presup {.h1} := by
  rw [rin, presup_finset]; decide

/-- Four books form two pairs, the paper's remark on (9). -/
theorem four_books_two_pairs : groupApply 2 2 ({.b1, .b2, .b3, .b4} : Finset Ind) :=
  ⟨{{.b1, .b2}, {.b3, .b4}}, by decide, by decide, by decide, by decide⟩

/-- Four books never form six pairs: overlapping pairs are not counted. -/
theorem four_books_not_six_pairs (x : Finset Ind) (hx : x.card = 4) : ¬ groupApply 2 6 x :=
  λ h => by have := groupApply_card h; omega

end Model

end Sudo2016
