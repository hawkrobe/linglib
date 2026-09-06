import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Agreement.Profile
import Linglib.Fragments.Slavic.Russian.Agreement
import Linglib.Fragments.Slavic.Russian.Gender
import Linglib.Fragments.Somali.Gender
import Linglib.Fragments.Latin.Gender
import Linglib.Fragments.Chichewa.Gender
import Linglib.Fragments.CoastalMarind.Gender
import Linglib.Studies.Corbett1991
import Linglib.Data.Examples.Corbett1998

/-!
# Corbett's morphology of agreement

Agreement is the systematic covariance of one element's form with properties of another,
and it is asymmetric: the controller determines the target. Gender, number and person are
the indisputable agreement features because their values originate on the controller, gender
inherent to the noun, person to the pronoun, and number relating primarily to the noun; case
covaries within the noun phrase too, but is imposed on noun and modifier alike by a governor
outside it, and definiteness is imposed on the phrase as a whole, so neither is agreement.
The exponents of agreement are affixes before, after and inside the stem, and a target may
carry several for one controller; the features constrain one another, Russian distinguishing
gender only in the singular in conformity with Greenberg's universal, and their joint
expression may be fusional and syncretic, at its most spectacular in polarity, where the
Somali article of one gender in one number is that of the other gender in the other number.
The target then shapes agreement twice over. The forms available depend on its word class
and even its lexical class, Upper Sorbian finite verbs and participles agreeing in different
features and Latin adjective classes distinguishing three genders, two or none; and the form
selected may depend on
another target or on syncretism, conjoined Chichewa plurals taking the target form they share
rather than the resolved one. The chapter's examples are the rows of
`Data/Examples/Corbett1998.json`.

## Implementation notes

* The asymmetry criterion is read off where a covarying feature's value originates, the
  chapter's classification of the five dimensions carried as data; the substrate profile
  records covariance in the wide sense, and what a target agrees in is the covarying
  dimensions whose origin is the controller.
* Polarity is defined for any exponent of two features and shown to need two-valued
  features, each of which it keeps fully distinct within the other; Somali's article is
  polar and its verbal prefix is not, the plural prefix coinciding with the masculine
  singular's instead.
* Number-conditioned gender distinctions are the convergent maps of Corbett's typology of
  gender, whose agreement classes, resolution rules and Latin carrier this file reuses;
  Chichewa's coordination rules are its rules over fragment nouns, one per target form
  before the semantic rule.
* The agreement slots of a target, their controllers and their bound of four are described
  in the rows and not modelled.

## TODO

* Nichols's hierarchy of the three features by their propensity to be marked only by
  agreement, the default-or-ungrammaticality outcomes of missing morphology, and the
  dependence of one target's form on another in Tigre, in Somali focus constructions and in
  German noun phrases are prose only.
* The Chichewa nouns carry no number, so the restriction of the shared-form rule to plural
  conjuncts, and the triggering of gender resolution by number resolution, are not stated.
* The syncretism claims are not stated over the cell-to-exponent tables of
  `Syntax/Agreement/Paradigm.lean`, whose cells are UD-typed where the carriers here are
  the languages' own.

## References

* [G. G. Corbett, *Morphology and agreement* (1998)][corbett-1998]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [J. H. Greenberg, *Some universals of grammar* (1963)][greenberg-1963]
* [G. G. Corbett, A. D. Mtenje, *Gender agreement in Chichewa* (1987)][corbett-mtenje-1987]
-/

namespace Corbett1998

open Agreement

/-! ### Agreement features (§§1–2) -/

/-- Where the value of a covarying feature originates: on the controller, inherent to it or
relating primarily to it; on a governor outside the phrase; or on the phrase as a whole. -/
inductive Origin where
  | controller
  | governor
  | phrase
  deriving DecidableEq, Repr, Fintype

/-- The chapter's classification: gender is inherent to the noun and person to the pronoun,
number relates primarily to the noun, case is imposed by government and definiteness on the
phrase as a whole. -/
def origin : Dimension → Origin
  | .gender | .number | .person => .controller
  | .case => .governor
  | .definiteness => .phrase

/-- Covariance is agreement when it is asymmetric: the value originates on the controller. -/
abbrev IsAgreementFeature (d : Dimension) : Prop := origin d = .controller

/-- The three indisputable agreement features, read off the classification. -/
theorem isAgreementFeature_iff (d : Dimension) :
    IsAgreementFeature d ↔ d = .gender ∨ d = .number ∨ d = .person := by
  cases d <;> decide

/-- What a target agrees in: the dimensions it covaries in that are agreement features. -/
def agreementFeatures (p : Profile) (t : Target) : Finset Dimension :=
  (p t).filter IsAgreementFeature

namespace Russian

open _root_.Russian.Gender

/-- Case covaries on the attributive adjective, (5). -/
theorem case_mem_profile_attributive :
    .case ∈ _root_.Russian.Agreement.profile .attributive := by decide

/-- But it is imposed by government: covariance without asymmetry. -/
theorem not_isAgreementFeature_case : ¬ IsAgreementFeature .case := by decide

/-- The attributive adjective agrees in number and gender, (1)–(4). -/
theorem agreementFeatures_attributive :
    agreementFeatures _root_.Russian.Agreement.profile .attributive = {.number, .gender} := by
  decide

end Russian

/-! ### The exponents of agreement (§3.1) -/

namespace CoastalMarind

open _root_.CoastalMarind

/-- The infixed vowel of *ak-k* 'light' distinguishes all four genders, (6)–(9). -/
theorem faithful_light : Function.Injective light := by decide

/-- The demonstrative does not: genders I and III share *e-pe*. -/
theorem not_faithful_demonstrative : ¬ Function.Injective demonstrative := by decide

end CoastalMarind

/-! ### Constraints on the co-occurrence of features (§3.2) -/

namespace Russian

open _root_.Russian.Gender

/-- Adjectives distinguish gender only in the singular, (1)–(4): a convergent system. -/
theorem convergent :
    Corbett1991.Convergent (Value.adjEnding · false) (Value.adjEnding · true) := by decide

/-- Greenberg's Universal 37 as its corollary. -/
theorem card_adjEnding_pl_le :
    Nat.card (Set.range (Value.adjEnding · true)) ≤
      Nat.card (Set.range (Value.adjEnding · false)) :=
  convergent.1.card_range_le

/-- The tenses the verb's agreement distinguishes. -/
inductive Tense where
  | nonpast
  | past
  deriving DecidableEq, Repr, Fintype

/-- Verbs agree in person and number, in the past tense in gender and number. -/
def verbFeatures : Tense → Finset Dimension
  | .nonpast => {.person, .number}
  | .past => {.gender, .number}

/-- Gender agreement on the verb is confined to the past tense. -/
theorem gender_mem_verbFeatures_iff (t : Tense) : .gender ∈ verbFeatures t ↔ t = .past := by
  cases t <;> decide

/-- The fragment's verb profile is the union over the tenses. -/
theorem profile_verb :
    _root_.Russian.Agreement.profile .verb = verbFeatures .nonpast ∪ verbFeatures .past := by
  decide

end Russian

section Polar

variable {G N F : Type*}

/-- An exponent of two features is polar when changing either value alone changes the form
and changing both leaves it unchanged. -/
def Polar (f : G → N → F) : Prop :=
  ∀ ⦃g g'⦄ ⦃n n'⦄, g ≠ g' → n ≠ n' → f g n = f g' n' ∧ f g n ≠ f g' n ∧ f g n ≠ f g n'

variable {f : G → N → F}

instance [Fintype G] [Fintype N] [DecidableEq G] [DecidableEq N] [DecidableEq F] :
    Decidable (Polar f) := by
  unfold Polar; infer_instance

/-- Polarity is symmetric in the two features. -/
theorem Polar.flip (h : Polar f) : Polar (flip f) :=
  λ _ _ _ _ hn hg => (h hg hn).imp_right And.comm.mp

/-- Polarity needs two-valued features: with three values of one feature, two of them would
share a form. -/
theorem Polar.card_le_two [Fintype G] [Nontrivial N] (h : Polar f) : Fintype.card G ≤ 2 := by
  by_contra hc
  obtain ⟨g₁, g₂, g₃, h₁₂, h₁₃, h₂₃⟩ := Fintype.two_lt_card_iff.mp (not_le.mp hc)
  obtain ⟨n, n', hn⟩ := exists_pair_ne N
  exact (h h₁₂ hn).2.1 ((h h₁₃ hn).1.trans (h h₂₃ hn).1.symm)

/-- The other feature likewise. -/
theorem Polar.card_le_two' [Fintype N] [Nontrivial G] (h : Polar f) : Fintype.card N ≤ 2 :=
  h.flip.card_le_two

/-- Polar features are two-valued. -/
theorem Polar.card_eq_two [Fintype G] [Nontrivial G] [Nontrivial N] (h : Polar f) :
    Fintype.card G = 2 :=
  le_antisymm h.card_le_two Fintype.one_lt_card

/-- Within one value of the other feature, a polar exponent keeps every distinction. -/
theorem Polar.injective [Nontrivial N] (h : Polar f) (n : N) : Function.Injective (f · n) :=
  λ _ _ e => by
    by_contra hg
    obtain ⟨n', hn⟩ := exists_ne n
    exact (h hg hn.symm).2.1 e

/-- Polarity is syncretism across the numbers and none within them: in Corbett's typology, a
parallel system. -/
theorem Polar.parallel [Nontrivial N] (h : Polar f) (n n' : N) :
    Corbett1991.Parallel (f · n) (f · n') :=
  ⟨λ _ _ e => congrArg (f · n') (h.injective n e), λ _ _ e => congrArg (f · n) (h.injective n' e)⟩

end Polar

namespace Somali

open _root_.Somali.Gender

/-- Table 9.1: the article is polar. -/
theorem polar_article : Polar Value.article := by decide

/-- The verbal prefix is not, (11)–(14): the plural prefix of either gender is the masculine
singular's, another syncretism. -/
theorem not_polar_verbPrefix : ¬ Polar Value.verbPrefix := by decide

/-- The plural prefix of either gender is the masculine singular's. -/
theorem verbPrefix_plural (g : Value) : g.verbPrefix true = Value.masc.verbPrefix false := by
  cases g <;> rfl

/-- Nor are all nouns in the polarity system: *nin* 'man' keeps *-kii* in the plural. -/
theorem article_nin : nin.article true = nin.article false := rfl

/-- In the typology of gender the article is a parallel system and the verb a convergent
one. -/
theorem parallel_article :
    Corbett1991.Parallel (Value.article · false) (Value.article · true) :=
  polar_article.parallel false true

/-- The verbal prefix converges on one plural form. -/
theorem convergent_verbPrefix :
    Corbett1991.Convergent (Value.verbPrefix · false) (Value.verbPrefix · true) := by decide

end Somali

/-! ### The effect of the target on the forms available (§4) -/

namespace UpperSorbian

/-- The two verbal targets of (17). -/
inductive Item where
  | finiteVerb
  | participle
  deriving DecidableEq, Repr, Fintype

/-- The row key of each target. -/
def Item.key : Item → String
  | .finiteVerb => "finiteVerb"
  | .participle => "participle"

/-- The finite verb agrees in number and person, the participle in number and gender. -/
def features : Item → Finset Dimension
  | .finiteVerb => {.number, .person}
  | .participle => {.number, .gender}

/-- Agreement features cannot be stated at the level of the language. -/
theorem not_uniform : ¬ ∃ D, ∀ i, features i = D :=
  λ ⟨_, h⟩ => absurd ((h .finiteVerb).trans (h .participle).symm) (by decide)

end UpperSorbian

namespace Latin

open _root_.Latin.Gender

/-- Table 9.2: *facilis* distinguishes only part of what *acer* does, and *felix* nothing of
what *facilis* does: each class's forms factor through the previous, never conversely. -/
theorem facilis_factorsThrough_acer :
    Function.FactorsThrough facilis.nomSg acer.nomSg ∧
      ¬ Function.FactorsThrough acer.nomSg facilis.nomSg := by decide

/-- And *felix* distinguishes nothing of what *facilis* does. -/
theorem felix_factorsThrough_facilis :
    Function.FactorsThrough felix.nomSg facilis.nomSg ∧
      ¬ Function.FactorsThrough facilis.nomSg felix.nomSg := by decide

end Latin

/-! ### The effect of the target on the form selected (§5) -/

namespace Chichewa

open _root_.Chichewa.Gender Corbett1991

/-- Coordinated plural nouns that would take one target form take it. -/
def sharedFormRules : List (Rule Chichewa.Gender.Noun SubjPrefix) :=
  [⟨.all, (·.gender.plSubjPrefix = .a), .a⟩, ⟨.all, (·.gender.plSubjPrefix = .zi), .zi⟩]

/-- The regular rule: humans take the plural of gender 1/2 and the rest the plural of 7/8. -/
def semanticRules : List (Rule Chichewa.Gender.Noun SubjPrefix) :=
  [⟨.all, (·.human = true), .a⟩, Rule.otherwise .zi]

/-- The shared form is preferred; the regular rule applies where there is none. -/
def rules : List (Rule Chichewa.Gender.Noun SubjPrefix) := sharedFormRules ++ semanticRules

/-- Syncretism licenses agreement, (18) and (19): conjuncts sharing a form take it. -/
theorem resolve_of_shared {cs : List Chichewa.Gender.Noun} (hne : cs ≠ []) {f : SubjPrefix}
    (h : ∀ c ∈ cs, c.gender.plSubjPrefix = f) : resolve rules cs = some f := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil cs hne
  simp only [rules, sharedFormRules, List.cons_append, List.nil_append]
  cases f
  · exact resolve_cons_of_applies _ _ _ h
  · rw [resolve_cons_of_not_applies]
    · exact resolve_cons_of_applies _ _ _ h
    · exact λ h' => absurd ((h' c hc).symm.trans (h c hc)) (by decide)

/-- Were the forms not syncretic, the regular rule would apply. -/
theorem resolve_of_ne {cs : List Chichewa.Gender.Noun} (ha : ∃ c ∈ cs, c.gender.plSubjPrefix ≠ .a)
    (hz : ∃ c ∈ cs, c.gender.plSubjPrefix ≠ .zi) : resolve rules cs = resolve semanticRules cs := by
  obtain ⟨a, ha, ha'⟩ := ha
  obtain ⟨z, hz, hz'⟩ := hz
  have h₁ : ¬ ∀ c ∈ cs, c.gender.plSubjPrefix = .a := λ h => ha' (h a ha)
  have h₂ : ¬ ∀ c ∈ cs, c.gender.plSubjPrefix = .zi := λ h => hz' (h z hz)
  simp [rules, sharedFormRules, resolve, Rule.Applies, h₁, h₂]

/-- The regular rule on its own: gender 1/2 for humans, 7/8 for the rest. -/
theorem resolve_semanticRules (cs : List Chichewa.Gender.Noun) :
    resolve semanticRules cs = some (if ∀ c ∈ cs, c.human = true then .a else .zi) := by
  unfold semanticRules
  split_ifs with hh
  · exact resolve_cons_of_applies _ _ _ hh
  · rw [resolve_cons_of_not_applies]
    · exact resolve_cons_of_applies _ _ _ (Rule.otherwise_applies _ _)
    · exact hh

/-- Corbett's *Gender* adds the cats and dogs, and the children and oranges, humans and not,
both by the shared form. -/
theorem resolve_mphaka_galu_ana_lalanje :
    resolve rules [mphaka, galu] = some .a ∧ resolve rules [ana, lalanje] = some .a := by decide

end Chichewa

/-! ### The chapter's examples -/

/-- Russian adjectives, (1)–(4): the ending is the fragment's by gender and number. -/
theorem russian_rows : ∀ row ∈ Examples.all, row.language = "russ1263" →
    ∀ g ∈ row.parse? "gender"
      [("masc", _root_.Russian.Gender.Value.masc), ("fem", .fem), ("neut", .neut)],
    ∀ pl ∈ row.parse? "number" [("sg", false), ("pl", true)],
    ∀ e ∈ row.parse? "ending"
      [("yj", _root_.Russian.Gender.AdjEnding.yj), ("aja", .aja), ("oe", .oe), ("ye", .ye)],
      e = g.adjEnding pl := by
  decide +kernel

/-- Marind, (6)–(9): the adjective and the demonstrative are the fragment's by gender. -/
theorem marind_rows : ∀ row ∈ Examples.all, row.language = "nucl1622" →
    ∀ g ∈ row.parse? "gender"
      [("I", CoastalMarind.Gender.gI), ("II", .gII), ("III", .gIII), ("IV", .gIV)],
      (∀ a ∈ row.feature? "adjective", a = CoastalMarind.light g) ∧
        ∀ d ∈ row.feature? "demonstrative", d = CoastalMarind.demonstrative g := by
  decide +kernel

/-- Upper Sorbian, (17): each target agrees in the features the row records for it. -/
theorem upperSorbian_rows : ∀ row ∈ Examples.all, row.language = "uppe1395" →
    ∀ i : UpperSorbian.Item, ∀ D ∈ row.parse? i.key
      [("number,person", ({.number, .person} : Finset Dimension)),
        ("number,gender", {.number, .gender})],
      UpperSorbian.features i = D := by
  decide +kernel

/-- Somali, (11)–(14) and *nin*: the article is the noun's by number and the verbal prefix
the gender's. -/
theorem somali_rows : ∀ row ∈ Examples.all, row.language = "soma1255" →
    ∀ n ∈ row.parse? "noun" (_root_.Somali.Gender.allNouns.map λ n => (n.form, n)),
    ∀ pl ∈ row.parse? "number" [("sg", false), ("pl", true)],
      (∀ a ∈ row.parse? "article" [("kii", _root_.Somali.Gender.Article.kii), ("tii", .tii)],
        a = n.article pl) ∧
      ∀ v ∈ row.parse? "verb" [("y", _root_.Somali.Gender.VerbPrefix.y), ("t", .t)],
        v = n.gender.verbPrefix pl := by
  decide +kernel

/-- Chichewa, (18) and (19): the verb's prefix is the rules' resolution of the conjuncts. -/
theorem chichewa_rows : ∀ row ∈ Examples.all, row.language = "nyan1308" →
    ∀ a ∈ row.parse? "conjunct1" (_root_.Chichewa.Gender.allNouns.map λ n => (n.form, n)),
    ∀ b ∈ row.parse? "conjunct2" (_root_.Chichewa.Gender.allNouns.map λ n => (n.form, n)),
    ∀ p ∈ row.parse? "prefix" [("a", _root_.Chichewa.Gender.SubjPrefix.a), ("zi", .zi)],
      Corbett1991.resolve Chichewa.rules [a, b] = some p := by
  decide +kernel

end Corbett1998
