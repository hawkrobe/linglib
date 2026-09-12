import Linglib.Data.WALS.Features.F113A
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Japanese.Negation
import Linglib.Fragments.Turkish.Negation
import Linglib.Fragments.Burmese.Negation
import Linglib.Fragments.Mandarin.Negation
import Linglib.Fragments.English.Negation
import Linglib.Fragments.Maori.Negation
import Linglib.Fragments.Hixkaryana.Negation

/-!
# Miestamo (2005): Standard Negation

This file formalizes the typology of [miestamo-2005]. The negation of a declarative verbal
main clause is symmetric when the negative merely adds a marker to the affirmative and
asymmetric when further structural changes accompany it, and the distinction applies to
constructions and to paradigms separately: a paradigm is symmetric when its affirmative and
negative members correspond one to one (`IsSymmetricParadigm`) and neutralizes when
distinct affirmative forms share a negative counterpart (`Neutralizes`). A language is of
type Sym when neither its constructions nor its paradigms show asymmetry, of type Asy when
every construction is asymmetric, and of type SymAsy otherwise (`languageType`), so the
definitional cells of the book's fourth table follow (`languageType_eq_symmetric_iff`,
`languageType_eq_asymmetric_iff`). The subtypes of asymmetry (`AsymmetrySubtype`) are
instantiated on the fragments: the Finnish negative auxiliary inflects for every
person–number cell and is the finite element, the Japanese lexical verb loses its tense
marking, Mandarin and Turkish mix symmetric and asymmetric constructions, Maori and
Hixkaryana negate only asymmetrically, Burmese neutralizes its three postverbal
tense–aspect markers into one negative form, and English, whose auxiliary construction is
symmetric with the emphatic affirmative, neutralizes the emphatic distinction of the
simple tenses in the paradigm.

## Implementation notes

A construction's symmetry is a judgment recorded on the fragment entries, so the derived
content is the paradigmatic level and the language type. The English fragment codes the
do-support constructions as asymmetric, the atlas's reading; the book compares the
simple-tense negatives with the emphatic affirmatives and locates the asymmetry in the
paradigm, and `englishSimpleTenses` follows the book. The representative sample, its
frequency tables, and the further subtypes of the finiteness and category asymmetries are
not represented.

## References

* [miestamo-2005]
-/

namespace Miestamo2005

variable {α β : Type*}

/-- The domains of asymmetry: the finiteness of verbal elements, the marking of a
non-realized category, the marking of emphasis, and other grammatical categories. -/
inductive AsymmetrySubtype where
  | fin
  | nonReal
  | emph
  | cat
  deriving DecidableEq

/-- A paradigm of affirmative–negative pairs is symmetric when its members correspond one to
one: distinct affirmative forms have distinct negative counterparts. -/
def IsSymmetricParadigm (p : List α) (aff neg : α → β) : Prop :=
  ∀ e₁ ∈ p, ∀ e₂ ∈ p, neg e₁ = neg e₂ → aff e₁ = aff e₂

/-- Paradigmatic neutralization: distinct affirmative forms with one negative counterpart. -/
def Neutralizes (p : List α) (aff neg : α → β) : Prop :=
  ∃ e₁ ∈ p, ∃ e₂ ∈ p, aff e₁ ≠ aff e₂ ∧ neg e₁ = neg e₂

instance [DecidableEq β] (p : List α) (aff neg : α → β) :
    Decidable (IsSymmetricParadigm p aff neg) :=
  inferInstanceAs (Decidable (∀ e₁ ∈ p, ∀ e₂ ∈ p, neg e₁ = neg e₂ → aff e₁ = aff e₂))

instance [DecidableEq β] (p : List α) (aff neg : α → β) : Decidable (Neutralizes p aff neg) :=
  inferInstanceAs (Decidable (∃ e₁ ∈ p, ∃ e₂ ∈ p, aff e₁ ≠ aff e₂ ∧ neg e₁ = neg e₂))

theorem neutralizes_iff_not_isSymmetricParadigm (p : List α) (aff neg : α → β) :
    Neutralizes p aff neg ↔ ¬ IsSymmetricParadigm p aff neg := by
  unfold Neutralizes IsSymmetricParadigm
  push Not
  exact ⟨λ ⟨e₁, h₁, e₂, h₂, ha, hn⟩ => ⟨e₁, h₁, e₂, h₂, hn, ha⟩,
    λ ⟨e₁, h₁, e₂, h₂, hn, ha⟩ => ⟨e₁, h₁, e₂, h₂, ha, hn⟩⟩

/-- The three types of language, from the symmetry of each construction and whether some
paradigm is asymmetric: symmetric negation when no asymmetry is found, asymmetric when every
construction is asymmetric, and both otherwise. -/
def languageType (constructions : List Bool) (paradigmAsymmetric : Prop)
    [Decidable paradigmAsymmetric] : Data.WALS.F113A.NegationSymmetry :=
  if constructions.all id ∧ ¬ paradigmAsymmetric then .symmetric
  else if constructions.all (!·) then .asymmetric
  else .both

section LanguageType

variable (cs : List Bool) (P : Prop) [Decidable P]

theorem languageType_eq_symmetric_iff :
    languageType cs P = .symmetric ↔ (∀ c ∈ cs, c = true) ∧ ¬ P := by
  unfold languageType
  split_ifs with h₁ h₂ <;> simp_all [List.all_eq_true]

/-- A language with only asymmetric constructions is of type Asy whatever its paradigms. -/
theorem languageType_eq_asymmetric_iff (hne : cs ≠ []) :
    languageType cs P = .asymmetric ↔ ∀ c ∈ cs, c = false := by
  unfold languageType
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
  split_ifs with h₁ h₂ <;> simp_all [List.all_eq_true]

/-- Type SymAsy has a symmetric construction by definition, together with some asymmetry. -/
theorem languageType_eq_both_iff :
    languageType cs P = .both ↔ (∃ c ∈ cs, c = true) ∧ ((∃ c ∈ cs, c = false) ∨ P) := by
  unfold languageType
  split_ifs with h₁ h₂ <;> simp_all [List.all_eq_true]
  exact (em (false ∈ cs)).elim Or.inl (λ hf => Or.inr (h₁ hf))

end LanguageType

/-! ### Finiteness asymmetry: Finnish, Japanese, Maori, Hixkaryana -/

/-- The Finnish negative auxiliary inflects for every person–number cell, so it is the finite
element of the negative clause and the lexical verb is nonfinite, the negative-verb variety of
the finiteness asymmetry. -/
theorem finnish_negVerb :
    ∀ p ∈ [1, 2, 3], ∀ n ∈ ["sg", "pl"],
      ∃ f ∈ Finnish.Negation.negParadigm, f.person = p ∧ f.number = n := by
  decide

/-- Under negation the Japanese lexical verb loses its tense marking to the adjectival negative
suffix, the lexical-verb variety of the finiteness asymmetry. -/
theorem japanese_tense_leaves_stem :
    .tense ∈ Japanese.Negation.japaneseNegDistribution.affirmativeOnStem ∧
      .tense ∉ Japanese.Negation.japaneseNegDistribution.negativeOnStem := by
  decide

/-- The asymmetry is constructional only: the Japanese paradigm is symmetric. -/
theorem japanese_paradigm_symmetric :
    IsSymmetricParadigm Japanese.Negation.taberuParadigm (·.affirmative) (·.negative) := by
  decide

/-- Maori negates only with the finite negative verb, so it is of type Asy. -/
theorem maori_asymmetric :
    languageType (Maori.Negation.allExamples.map (·.symmetric)) False = .asymmetric := by
  decide

/-- Hixkaryana negates only by deverbalizing the lexical verb under a copula that carries the
finite inflection, so it is of type Asy. -/
theorem hixkaryana_asymmetric :
    languageType (Hixkaryana.Negation.allExamples.map (·.symmetric)) False = .asymmetric ∧
      ∀ e ∈ Hixkaryana.Negation.allExamples, e.copulaFinite = true := by
  decide

/-! ### Mixed languages: Mandarin and Turkish -/

/-- Mandarin negates non-perfectives symmetrically with *bù* and perfectives with *méi*, which
introduces the existential verb as the finite element or is itself the finite negative verb,
so it is of type SymAsy. -/
theorem mandarin_both :
    languageType (Mandarin.Negation.allExamples.map (·.symmetric)) False = .both := by
  decide

/-- Turkish negation is symmetric except in the aorist, whose marker changes or drops in the
negative, a category asymmetry; the paradigm stays one to one. -/
theorem turkish_both :
    languageType (Turkish.Negation.gelParadigm.map (·.symmetric))
      (Neutralizes Turkish.Negation.gelParadigm (·.affirmative) (·.negative)) = .both := by
  decide

/-! ### Paradigmatic neutralization: Burmese and English -/

/-- The Burmese negative suffix replaces the postverbal tense–aspect markers, so one negative
form corresponds to three affirmative forms. -/
theorem burmese_neutralizes :
    Neutralizes Burmese.Negation.saParadigm (·.affirmative) (·.negative) := by
  decide

/-- The English simple tenses with their emphatic periphrastic affirmatives: the negative is
symmetric with the emphatic affirmative, and the paradigm loses the emphatic distinction. -/
def englishSimpleTenses : List (String × String) :=
  [(English.Negation.lexicalPresent.affirmative, English.Negation.lexicalPresent.negative),
   ("he does eat", English.Negation.lexicalPresent.negative),
   (English.Negation.lexicalPast.affirmative, English.Negation.lexicalPast.negative),
   ("he did eat", English.Negation.lexicalPast.negative)]

/-- English negation is symmetric in construction and asymmetric in paradigm, of the emphasis
subtype, so it is of type SymAsy. -/
theorem english_both :
    Neutralizes englishSimpleTenses Prod.fst Prod.snd ∧
      languageType [true] (Neutralizes englishSimpleTenses Prod.fst Prod.snd) = .both := by
  decide

end Miestamo2005
