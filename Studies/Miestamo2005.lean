module

public import Linglib.Data.WALS.Features.F113A
public import Linglib.Fragments.Finnish.Negation
public import Linglib.Fragments.Japanese.Negation
public import Linglib.Fragments.Turkish.Negation
public import Linglib.Fragments.Burmese.Negation
public import Linglib.Fragments.Mandarin.Negation
public import Linglib.Fragments.English.Negation
public import Linglib.Fragments.Maori.Negation
public import Linglib.Fragments.Hixkaryana.Negation
public import Linglib.Fragments.German.Negation
public import Linglib.Fragments.Romance.Italian.Negation
public import Linglib.Fragments.Romance.French.Negation
public import Linglib.Fragments.Slavic.Russian.Negation
public import Linglib.Fragments.Romance.Spanish.Negation
public import Linglib.Fragments.Quechua.Negation
public import Linglib.Fragments.Tunica.Negation

/-!
# Miestamo (2005): Standard Negation

This file formalizes Miestamo's typology of standard negation. The negation of a declarative verbal
main clause is symmetric when the negative differs from an affirmative only by the presence of
the negative marker and asymmetric when further structural differences accompany it. A pair is
symmetric when its negative is its affirmative with the marker inserted, differences of
phonological shape apart (`IsSymmetric`), and a construction is symmetric in its paradigm when
its negative is some affirmative of the paradigm with the marker inserted (`IsSymmetricIn`), as
the English negative of a simple tense is symmetric with the emphatic affirmative. Paradigms are
asymmetric by the asymmetries found in them, symmetric paradigms being identified only by their
absence (`ParadigmAsymmetric`): a paradigm neutralizes when distinct affirmatives share their
negative (`Neutralizes`) and displaces when the negative of one member is built on the
affirmative of another while the negatives stay distinct (`Displaces`). Paradigmatic asymmetry is
therefore not neutralization: Tunica builds the negative of the habitual on the semelfactive and
keeps the two apart by their markers (`exists_paradigmAsymmetric_not_neutralizes`). A language is
of type Sym when neither its constructions nor its paradigms show asymmetry, of type Asy when
every construction is asymmetric, and of type SymAsy otherwise (`languageType`), so the
definitional cells of the book's fourth table follow (`languageType_eq_symmetric_iff`,
`languageType_eq_asymmetric_iff`).

The types are instantiated on the book's own examples, entered in the fragments. Spanish, German,
Italian, French and Russian are of type Sym. The Finnish negative auxiliary takes the ending of
the finite verb and leaves the lexical verb without it; the plain Japanese negative inflects as
an adjective, a less finite form than the verb; Maori negates with an initial negative verb, and
Hixkaryana deverbalizes the lexical verb under an added copula: finiteness asymmetries, and type
Asy. Mandarin and Turkish mix symmetric and asymmetric constructions. Burmese replaces its three
postverbal tense–aspect markers with one negative suffix, asymmetric in construction and
neutralizing in paradigm. The English negative is symmetric with the emphatic affirmative, not
with the plain one, to which it adds *do*, and the paradigm loses the emphatic distinction of the
simple tenses. The Imbabura Quechua negative is the polar interrogative with *mana* added, and
carries the interrogative's *-chu*, which the declarative lacks.

## Implementation notes

A pair cites each morph in one form across its two members, which is how phonologically
conditioned differences are set aside, as the book sets them aside for the Turkish future and the
Tunica semelfactive. The Mandarin constructions are compared through what each negator adds and
excludes, the book giving no minimal pairs for them. The subtypes of asymmetry, finiteness,
non-realized category, emphasis and other categories, are not represented: `Adds` identifies an
added element, the mark of the finite-element constructions, but which category a lost or changed
marker belongs to is not recorded in a pair. Different-system asymmetry and paradigmatic gaps are
not represented either, and nor are the representative sample and its frequency tables.

## TODO

The Quechua asymmetry is paradigmatic displacement onto the interrogative, A/NonReal/Displc; its
statement as `Displaces` needs an affirmative declarative and a negative interrogative of one
predicate, which the book's (63) does not give.

## References

* [miestamo-2005]
-/

@[expose] public section

namespace Miestamo2005

open Negation

variable {α : Type*}

/-! ### Constructions -/

/-- A construction is symmetric when the negative is the affirmative with the negative marker
inserted: the affirmative is a sublist of the negative, and the two differ by exactly the
marker's morphs. -/
def IsSymmetric (p : Pair) : Prop :=
  p.affirmative.Sublist p.negative ∧ p.negative.Perm (p.affirmative ++ p.marker.morphs)

instance : DecidablePred IsSymmetric := fun p ↦
  inferInstanceAs (Decidable (p.affirmative.Sublist p.negative ∧
    p.negative.Perm (p.affirmative ++ p.marker.morphs)))

/-- A construction is symmetric in a paradigm when its negative is some affirmative of the
paradigm with its marker inserted. -/
def IsSymmetricIn (ps : List Pair) (p : Pair) : Prop :=
  ∃ q ∈ ps, IsSymmetric { p with affirmative := q.affirmative }

instance (ps : List Pair) : DecidablePred (IsSymmetricIn ps) := fun p ↦
  inferInstanceAs (Decidable (∃ q ∈ ps, IsSymmetric { p with affirmative := q.affirmative }))

theorem IsSymmetric.isSymmetricIn {ps : List Pair} {p : Pair} (hp : p ∈ ps)
    (h : IsSymmetric p) : IsSymmetricIn ps p :=
  ⟨p, hp, h⟩

/-- The negative contains an element, other than the marker, that the affirmative lacks, as the
constructions that add a finite element do. -/
def Adds (p : Pair) : Prop :=
  ∃ x ∈ p.negative, x ∉ p.marker.morphs ∧ x ∉ p.affirmative

instance : DecidablePred Adds := fun p ↦
  inferInstanceAs (Decidable (∃ x ∈ p.negative, x ∉ p.marker.morphs ∧ x ∉ p.affirmative))

/-- A construction that adds an element is asymmetric. -/
theorem not_isSymmetric_of_adds {p : Pair} (h : Adds p) : ¬ IsSymmetric p := by
  obtain ⟨x, hx, hm, ha⟩ := h
  exact fun hs ↦ by simpa [ha, hm] using hs.2.subset hx

/-! ### Paradigms -/

/-- A paradigm neutralizes when distinct affirmatives share their negative. -/
def Neutralizes (ps : List Pair) : Prop :=
  ∃ p ∈ ps, ∃ q ∈ ps, p.affirmative ≠ q.affirmative ∧ p.negative = q.negative

/-- A paradigm displaces when the negative of one member is the affirmative of another with the
first member's marker inserted, while the two negatives stay distinct. -/
def Displaces (ps : List Pair) : Prop :=
  ∃ p ∈ ps, ∃ q ∈ ps, p.affirmative ≠ q.affirmative ∧ p.negative ≠ q.negative ∧
    IsSymmetric { p with affirmative := q.affirmative }

/-- A paradigm is asymmetric when it neutralizes or displaces: symmetric paradigms are those in
which no asymmetry is found. -/
def ParadigmAsymmetric (ps : List Pair) : Prop := Neutralizes ps ∨ Displaces ps

instance (ps : List Pair) : Decidable (Neutralizes ps) :=
  inferInstanceAs (Decidable
    (∃ p ∈ ps, ∃ q ∈ ps, p.affirmative ≠ q.affirmative ∧ p.negative = q.negative))

instance (ps : List Pair) : Decidable (Displaces ps) :=
  inferInstanceAs (Decidable (∃ p ∈ ps, ∃ q ∈ ps, p.affirmative ≠ q.affirmative ∧
    p.negative ≠ q.negative ∧ IsSymmetric { p with affirmative := q.affirmative }))

instance (ps : List Pair) : Decidable (ParadigmAsymmetric ps) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ### Language types -/

/-- The three types of language, from the symmetry of each construction and whether some
paradigm is asymmetric: symmetric negation when no asymmetry is found, asymmetric when every
construction is asymmetric, and both otherwise. -/
def languageType (cs : List α) (sym : α → Prop) [DecidablePred sym] (paradigmAsymmetric : Prop)
    [Decidable paradigmAsymmetric] : Data.WALS.F113A.NegationSymmetry :=
  if (∀ c ∈ cs, sym c) ∧ ¬ paradigmAsymmetric then .symmetric
  else if ∀ c ∈ cs, ¬ sym c then .asymmetric
  else .both

/-- The type of a language whose constructions form the paradigm `ps`. -/
abbrev pairsType (ps : List Pair) : Data.WALS.F113A.NegationSymmetry :=
  languageType ps (IsSymmetricIn ps) (ParadigmAsymmetric ps)

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

/-! ### Paradigmatic displacement: Tunica -/

/-- Tunica negates the habitual on the semelfactive form, (5): each construction is symmetric in
the paradigm, and the paradigm displaces without neutralizing, the two negative markers keeping
the aspects apart. -/
theorem tunica_displaces :
    (∀ p ∈ Tunica.Negation.run, IsSymmetricIn Tunica.Negation.run p) ∧
      Displaces Tunica.Negation.run ∧ ¬ Neutralizes Tunica.Negation.run := by
  decide

/-- Paradigmatic asymmetry does not always lead to neutralization. -/
theorem exists_paradigmAsymmetric_not_neutralizes :
    ∃ ps, ParadigmAsymmetric ps ∧ ¬ Neutralizes ps :=
  ⟨_, .inr tunica_displaces.2.1, tunica_displaces.2.2⟩

/-! ### Symmetric negation: Spanish, German, Italian, French, Russian -/

theorem spanish_symmetric : pairsType Spanish.Negation.pairs = .symmetric := by decide

theorem german_symmetric : pairsType German.Negation.pairs = .symmetric := by decide

theorem italian_symmetric : pairsType Italian.Negation.pairs = .symmetric := by decide

/-- Both members of the French double marker are removed. -/
theorem french_symmetric : pairsType French.Negation.pairs = .symmetric := by decide

theorem russian_symmetric : pairsType Russian.Negation.pairs = .symmetric := by decide

/-! ### Finiteness asymmetry: Finnish, Japanese, Maori, Hixkaryana -/

/-- The Finnish negative auxiliary has an ending for every person and number, and in the
negative of a stem with its ending the auxiliary takes the ending and the stem follows bare:
the negative verb is the finite element of the clause, and the language is of type Asy. -/
theorem finnish_negVerb :
    Finnish.Negation.ending.cells = Agreement.Bundle.personNumberCells ∧
    (∀ p ∈ Finnish.Negation.present, p.negative = p.marker.morphs ++ p.affirmative.reverse) ∧
    pairsType Finnish.Negation.present = .asymmetric := by
  decide

/-- The plain Japanese negative is the verb root, the negator *-na-* and an adjectival tense
ending, where the affirmative has a verbal one: the verb becomes an adjective, less finite than
the verb, which the book files, as an atypical member, under the finiteness asymmetry with a
nonfinite lexical verb. -/
theorem japanese_negative_adjectival :
    ∀ p ∈ Japanese.Negation.plain, ∃ e ∈ Japanese.Negation.adjectivalEndings,
      p.negative = p.affirmative.take 1 ++ Japanese.Negation.na.morphs ++ [e] ∧
        ∀ m ∈ p.affirmative.drop 1, m ∉ Japanese.Negation.adjectivalEndings := by
  decide

/-- The plain and the polite negatives are asymmetric, the polite past adding the copula, while
the paradigm shows no asymmetry. -/
theorem japanese_asymmetric :
    (∃ p ∈ Japanese.Negation.polite, Adds p) ∧
    ¬ ParadigmAsymmetric (Japanese.Negation.plain ++ Japanese.Negation.polite) ∧
    pairsType (Japanese.Negation.plain ++ Japanese.Negation.polite) = .asymmetric := by
  decide

/-- Maori negates only with the initial negative verb, after which the subject precedes the
tense particle and the verb, so it is of type Asy. -/
theorem maori_asymmetric : pairsType Maori.Negation.pairs = .asymmetric := by decide

/-- Hixkaryana negates only by deverbalizing the lexical verb under an added copula, so it is
of type Asy. -/
theorem hixkaryana_asymmetric :
    (∀ p ∈ Hixkaryana.Negation.pairs, Adds p) ∧
    pairsType Hixkaryana.Negation.pairs = .asymmetric := by
  decide

/-! ### Mixed languages: Mandarin and Turkish -/

/-- A Mandarin negator's construction is symmetric when it adds nothing but the negator, so that
no verb comes with it and no aspect particle of the affirmative is excluded. -/
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
negative, a category asymmetry; the paradigm shows no asymmetry. -/
theorem turkish_both :
    (∀ p ∈ Turkish.Negation.nonAorist, IsSymmetric p) ∧
    (∀ p ∈ Turkish.Negation.aorist, ¬ IsSymmetric p) ∧
    ¬ ParadigmAsymmetric (Turkish.Negation.nonAorist ++ Turkish.Negation.aorist) ∧
    pairsType (Turkish.Negation.nonAorist ++ Turkish.Negation.aorist) = .both := by
  decide

/-! ### Paradigmatic neutralization: Burmese and English -/

/-- The Burmese negative suffix replaces the postverbal tense–aspect markers, so the
construction is asymmetric and one negative form corresponds to three affirmative forms. -/
theorem burmese_neutralizes :
    Neutralizes Burmese.Negation.goParadigm ∧
    pairsType Burmese.Negation.goParadigm = .asymmetric := by
  decide

/-- The English negative is symmetric with the compound tenses and with the emphatic
affirmatives of the simple tenses, while to the plain simple tenses it adds *do*; the plain and
the emphatic affirmative of a simple tense share one negative, so English is of type SymAsy. -/
theorem english_both :
    (∀ p ∈ English.Negation.simpleTenses, Adds p) ∧
    Neutralizes (English.Negation.simpleTenses ++ English.Negation.emphaticTenses) ∧
    pairsType (English.Negation.compoundTenses ++ English.Negation.simpleTenses ++
      English.Negation.emphaticTenses) = .both := by
  decide

/-! ### Non-realized marking: Imbabura Quechua -/

/-- The Imbabura Quechua negative is the polar interrogative with *mana* inserted, the two
compared without their possessors *ñuka* 'my' and *kan-paj* 'your', (63c, d); the enclitic
*-chu* it shares with the interrogative is absent from the declarative, (63b). -/
theorem quechua_symmetric_with_interrogative :
    IsSymmetric ⟨Quechua.Negation.mana, Quechua.Negation.interrogative.drop 2,
      Quechua.Negation.negative.drop 1⟩ ∧
    Quechua.Negation.chu ∈ Quechua.Negation.negative ∧
    Quechua.Negation.chu ∉ Quechua.Negation.declarative := by
  decide

end Miestamo2005
