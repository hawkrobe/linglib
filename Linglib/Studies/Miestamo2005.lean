import Linglib.Data.WALS.Features.F113A
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Japanese.Negation
import Linglib.Fragments.Turkish.Negation
import Linglib.Fragments.Burmese.Negation
import Linglib.Fragments.Mandarin.Negation
import Linglib.Fragments.English.Negation
import Linglib.Fragments.Maori.Negation
import Linglib.Fragments.Hixkaryana.Negation
import Linglib.Fragments.German.Negation
import Linglib.Fragments.Romance.Italian.Negation
import Linglib.Fragments.Romance.French.Negation
import Linglib.Fragments.Slavic.Russian.Negation
import Linglib.Fragments.Romance.Spanish.Negation

/-!
# Miestamo (2005): Standard Negation

This file formalizes the typology of [miestamo-2005]. The negation of a declarative verbal
main clause is symmetric when the negative differs from the affirmative only by the presence
of the negative marker and asymmetric when further structural differences accompany it
(`IsSymmetric`): removing the marker from the negative leaves the affirmative, differences of
phonological shape apart. The distinction applies to constructions and to paradigms
separately: a paradigm is symmetric when its affirmative and negative members correspond one
to one (`IsSymmetricParadigm`) and neutralizes when distinct affirmative forms share a negative
counterpart (`Neutralizes`). A language is of type Sym when neither its constructions nor its
paradigms show asymmetry, of type Asy when every construction is asymmetric, and of type SymAsy
otherwise (`languageType`), so the definitional cells of the book's fourth table follow
(`languageType_eq_symmetric_iff`, `languageType_eq_asymmetric_iff`). The types are
instantiated on the book's own examples, entered in the fragments. Spanish, German, Italian,
French and Russian are of type Sym. The Finnish negative auxiliary takes the ending of the
finite verb and leaves the lexical verb without it; the Japanese negative inflects as an
adjective, so tense leaves the verb; Maori negates with an initial negative verb, and
Hixkaryana deverbalizes the lexical verb under an added copula: finiteness asymmetries, and
type Asy. Mandarin and Turkish mix symmetric and asymmetric constructions. Burmese replaces its
three postverbal tense–aspect markers with one negative suffix, asymmetric in construction and
neutralizing in paradigm. The English negative is symmetric with the emphatic affirmative, not
with the plain one, to which it adds *do*, and the paradigm loses the emphatic distinction of
the simple tenses.

## Implementation notes

A pair cites each morph in one form across its two members, which is how phonologically
conditioned differences are set aside, as the book sets them aside for the Turkish future.
The Mandarin constructions are compared through what each negator adds and excludes, the book
giving no minimal pairs for them. The subtypes of asymmetry (`AsymmetrySubtype`) are not
derived: `Adds` identifies an added element, the mark of the finite-element constructions, but
which category a lost or changed marker belongs to is not represented in a pair. The
representative sample and its frequency tables are not represented.

## References

* [miestamo-2005]
-/

namespace Miestamo2005

open Negation

variable {α β : Type*}

/-- The domains of asymmetry: the finiteness of verbal elements, the marking of a
non-realized category, the marking of emphasis, and other grammatical categories. -/
inductive AsymmetrySubtype where
  | fin
  | nonReal
  | emph
  | cat
  deriving DecidableEq

/-! ### Constructions -/

/-- A construction is symmetric when the negative is the affirmative with the negative marker
added: removing the marker's morphs from the negative leaves the affirmative. -/
def IsSymmetric (m : Marker) (p : Pair) : Prop :=
  p.negative.filter (· ∉ m.morphs) = p.affirmative

instance (m : Marker) : DecidablePred (IsSymmetric m) := fun p ↦
  inferInstanceAs (Decidable (p.negative.filter (· ∉ m.morphs) = p.affirmative))

/-- The negative contains an element, other than the marker, that the affirmative lacks: the
finite element of the constructions that add one. -/
def Adds (m : Marker) (p : Pair) : Prop :=
  ∃ x ∈ p.negative, x ∉ m.morphs ∧ x ∉ p.affirmative

instance (m : Marker) : DecidablePred (Adds m) := fun p ↦
  inferInstanceAs (Decidable (∃ x ∈ p.negative, x ∉ m.morphs ∧ x ∉ p.affirmative))

/-- A construction that adds an element is asymmetric. -/
theorem not_isSymmetric_of_adds {m : Marker} {p : Pair} (h : Adds m p) : ¬ IsSymmetric m p := by
  obtain ⟨x, hx, hm, ha⟩ := h
  intro hs
  exact ha (hs ▸ List.mem_filter.2 ⟨hx, by simpa using hm⟩)

/-! ### Paradigms -/

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
  exact ⟨fun ⟨e₁, h₁, e₂, h₂, ha, hn⟩ ↦ ⟨e₁, h₁, e₂, h₂, hn, ha⟩,
    fun ⟨e₁, h₁, e₂, h₂, hn, ha⟩ ↦ ⟨e₁, h₁, e₂, h₂, ha, hn⟩⟩

/-! ### Language types -/

/-- The three types of language, from the symmetry of each construction and whether some
paradigm is asymmetric: symmetric negation when no asymmetry is found, asymmetric when every
construction is asymmetric, and both otherwise. -/
def languageType (cs : List α) (sym : α → Prop) [DecidablePred sym] (paradigmAsymmetric : Prop)
    [Decidable paradigmAsymmetric] : Data.WALS.F113A.NegationSymmetry :=
  if (∀ c ∈ cs, sym c) ∧ ¬ paradigmAsymmetric then .symmetric
  else if ∀ c ∈ cs, ¬ sym c then .asymmetric
  else .both

section LanguageType

variable (cs : List α) (sym : α → Prop) [DecidablePred sym] (P : Prop) [Decidable P]

theorem languageType_eq_symmetric_iff :
    languageType cs sym P = .symmetric ↔ (∀ c ∈ cs, sym c) ∧ ¬ P := by
  unfold languageType
  split_ifs <;> simp_all

/-- A language with only asymmetric constructions is of type Asy whatever its paradigms. -/
theorem languageType_eq_asymmetric_iff (hne : cs ≠ []) :
    languageType cs sym P = .asymmetric ↔ ∀ c ∈ cs, ¬ sym c := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold languageType
  split_ifs with h₁ h₂
  · exact iff_of_false (by simp) fun h ↦ h c List.mem_cons_self (h₁.1 c List.mem_cons_self)
  · exact iff_of_true rfl h₂
  · exact iff_of_false (by simp) h₂

/-- Type SymAsy has a symmetric construction by definition, together with some asymmetry. -/
theorem languageType_eq_both_iff :
    languageType cs sym P = .both ↔ (∃ c ∈ cs, sym c) ∧ ((∃ c ∈ cs, ¬ sym c) ∨ P) := by
  unfold languageType
  split_ifs with h₁ h₂
  · exact iff_of_false (by simp) fun ⟨_, h⟩ ↦
      h.elim (fun ⟨c, hc, hn⟩ ↦ hn (h₁.1 c hc)) h₁.2
  · exact iff_of_false (by simp) fun ⟨⟨c, hc, hs⟩, _⟩ ↦ h₂ c hc hs
  · refine iff_of_true rfl ⟨by simpa using h₂, ?_⟩
    by_contra h
    push Not at h
    exact h₁ ⟨h.1, h.2⟩

end LanguageType

/-! ### Symmetric negation: Spanish, German, Italian, French, Russian -/

theorem spanish_symmetric :
    languageType Spanish.Negation.pairs (IsSymmetric Spanish.Negation.no) False = .symmetric := by
  decide

theorem german_symmetric :
    languageType German.Negation.pairs (IsSymmetric German.Negation.nicht) False =
      .symmetric := by
  decide

theorem italian_symmetric :
    languageType Italian.Negation.pairs (IsSymmetric Italian.Negation.non) False =
      .symmetric := by
  decide

/-- Both members of the French double marker are removed. -/
theorem french_symmetric :
    languageType French.Negation.pairs (IsSymmetric French.Negation.nePas) False =
      .symmetric := by
  decide

theorem russian_symmetric :
    languageType Russian.Negation.pairs (IsSymmetric Russian.Negation.ne) False = .symmetric := by
  decide

/-! ### Finiteness asymmetry: Finnish, Japanese, Maori, Hixkaryana -/

/-- The Finnish negative auxiliary has an ending for every person and number, and in the
negative of a stem with its ending the auxiliary takes the ending and the stem follows bare:
the negative verb is the finite element of the clause, and the language is of type Asy. -/
theorem finnish_negVerb :
    (∀ p ∈ [Person.first, .second, .third], ∀ n ∈ [Number.singular, .plural],
      (Finnish.Negation.ending p n).isSome) ∧
    (∀ p ∈ Finnish.Negation.present,
      p.negative = Finnish.Negation.e.morphs ++ p.affirmative.reverse) ∧
    languageType Finnish.Negation.present (IsSymmetric Finnish.Negation.e) False =
      .asymmetric := by
  decide

/-- Under negation the Japanese lexical verb loses its tense marking to the adjectival negative
suffix, the lexical-verb variety of the finiteness asymmetry. -/
theorem japanese_tense_leaves_stem :
    .tense ∈ Japanese.Negation.japaneseNegDistribution.affirmativeOnStem ∧
      .tense ∉ Japanese.Negation.japaneseNegDistribution.negativeOnStem := by
  decide

/-- The plain and the polite negatives are asymmetric, the polite past adding the copula, while
the paradigm stays one to one. -/
theorem japanese_asymmetric :
    (∀ p ∈ Japanese.Negation.plain, ¬ IsSymmetric Japanese.Negation.na p) ∧
    (∀ p ∈ Japanese.Negation.polite, ¬ IsSymmetric Japanese.Negation.en p) ∧
    (∃ p ∈ Japanese.Negation.polite, Adds Japanese.Negation.en p) ∧
    IsSymmetricParadigm (Japanese.Negation.plain ++ Japanese.Negation.polite)
      (·.affirmative) (·.negative) := by
  decide

/-- Maori negates only with the initial negative verb, after which the subject precedes the
tense particle and the verb, so it is of type Asy. -/
theorem maori_asymmetric :
    languageType Maori.Negation.pairs (IsSymmetric Maori.Negation.kaore) False =
      .asymmetric := by
  decide

/-- Hixkaryana negates only by deverbalizing the lexical verb under an added copula, so it is
of type Asy. -/
theorem hixkaryana_asymmetric :
    (∀ p ∈ Hixkaryana.Negation.pairs, Adds Hixkaryana.Negation.hira p) ∧
    languageType Hixkaryana.Negation.pairs (IsSymmetric Hixkaryana.Negation.hira) False =
      .asymmetric := by
  decide

/-! ### Mixed languages: Mandarin and Turkish -/

/-- A Mandarin negator's construction is symmetric when it adds nothing but the negator: no verb
comes with it and no aspect particle of the affirmative is excluded. -/
def IsSymmetricNegator (n : Mandarin.Negation.Negator) : Prop := n.verb = none ∧ n.excludes = []

instance : DecidablePred IsSymmetricNegator := fun n ↦
  inferInstanceAs (Decidable (n.verb = none ∧ n.excludes = []))

/-- Mandarin negates non-perfectives symmetrically with *bù* and perfectives with *méi*, which
brings in the existential verb *yǒu* as the finite element of the negative clause, or is itself
the negative existential verb, and loses the perfective *le*: a finiteness asymmetry, so the
language is of type SymAsy. -/
theorem mandarin_both :
    IsSymmetricNegator Mandarin.Negation.bu ∧ ¬ IsSymmetricNegator Mandarin.Negation.mei ∧
      languageType Mandarin.Negation.negators IsSymmetricNegator False = .both := by
  decide

/-- Turkish negation is symmetric except in the aorist, whose marker changes or drops in the
negative, a category asymmetry; the paradigm stays one to one. -/
theorem turkish_both :
    (∀ p ∈ Turkish.Negation.nonAorist, IsSymmetric Turkish.Negation.mA p) ∧
    (∀ p ∈ Turkish.Negation.aorist, ¬ IsSymmetric Turkish.Negation.mA p) ∧
    languageType (Turkish.Negation.nonAorist ++ Turkish.Negation.aorist)
      (IsSymmetric Turkish.Negation.mA)
      (Neutralizes (Turkish.Negation.nonAorist ++ Turkish.Negation.aorist)
        (·.affirmative) (·.negative)) = .both := by
  decide

/-! ### Paradigmatic neutralization: Burmese and English -/

/-- The Burmese negative suffix replaces the postverbal tense–aspect markers, so the
construction is asymmetric and one negative form corresponds to three affirmative forms. -/
theorem burmese_neutralizes :
    Neutralizes Burmese.Negation.goParadigm (·.affirmative) (·.negative) ∧
    languageType Burmese.Negation.goParadigm (IsSymmetric Burmese.Negation.maBu)
      (Neutralizes Burmese.Negation.goParadigm (·.affirmative) (·.negative)) = .asymmetric := by
  decide

/-- The English negative is symmetric with the compound tenses and with the emphatic
affirmatives of the simple tenses; to the plain simple tenses it adds *do*. -/
theorem english_symmetric_with_emphatic :
    (∀ p ∈ English.Negation.compoundTenses ++ English.Negation.emphaticTenses,
      IsSymmetric English.Negation.not p) ∧
    ∀ p ∈ English.Negation.simpleTenses, Adds English.Negation.not p := by
  decide

/-- English negation is symmetric in construction and asymmetric in paradigm, the plain and the
emphatic affirmative of a simple tense sharing one negative, so it is of type SymAsy. -/
theorem english_both :
    languageType (English.Negation.compoundTenses ++ English.Negation.emphaticTenses)
      (IsSymmetric English.Negation.not)
      (Neutralizes (English.Negation.simpleTenses ++ English.Negation.emphaticTenses)
        (·.affirmative) (·.negative)) = .both := by
  decide

end Miestamo2005
