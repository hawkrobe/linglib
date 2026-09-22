import Linglib.Fragments.Latin.Case
import Linglib.Fragments.Latin.Gender
import Linglib.Morphology.Paradigm.Basic

/-!
# Latin noun declension

Latin nouns inflect for six cases and two numbers, and the endings fuse case and number, and in
the first two declensions gender as well. Five declensions are traditionally recognised, named
for historical stem classes that are no longer transparent: ā-stems, o-stems, the third
declension with its consonant stems and i-stems, u-stems and ē-stems. The paradigms here are
the seven of Blake's table of Latin case paradigms.

No paradigm distinguishes all six cases. Two syncretisms predominate: nominative and accusative
fall together in every neuter and in many plurals, and dative and ablative fall together in
every plural, in the singular of the second declension and in the singular of the i-stems. The
vocative differs from the nominative only in the singular of non-neuter second-declension
nouns.

## Main declarations

* `Latin.Declension.Cell`, `forms`: the cells of a number, the cases of `Latin.Case.inventory`, and
  the forms of the six in the order of the school paradigms.
* `Latin.Declension.Noun`: a noun with its declension, genders and the form of each cell.
* `nom_acc_syncretic_of_neuter`, `plural_dat_abl_syncretic`, `singular_dat_abl_syncretic_iff`,
  `singular_nom_voc_syncretic_iff`: the syncretisms, read off the forms.

## Implementation notes

Blake's table gives two forms for the ablative singular and the accusative plural of *cīvis*.
`Noun.singular` and `Noun.plural` hold the first, the i-stem form, and `civis.variant` the second.
The genders of the four nouns whose columns the table leaves unlabelled are the dictionary ones.

## References

* [blake-1994]
-/

namespace Latin.Declension

open Morphology

/-- The declensions, the third split into consonant stems and i-stems. -/
inductive Class where
  | first
  | second
  | thirdConsonant
  | thirdI
  | fourth
  | fifth
  deriving DecidableEq, Repr

/-- The cells of a number, the six cases. -/
abbrev Cell : Type := Latin.Case.inventory

/-- The cell of a case. -/
abbrev cell (c : Case) (h : c ∈ Latin.Case.inventory := by decide) : Cell := ⟨c, h⟩

/-- The forms of the six cells, in the order of the school paradigms. -/
def forms (nom voc acc gen dat abl : String) : Cell → String
  | ⟨.nom, _⟩ => nom
  | ⟨.voc, _⟩ => voc
  | ⟨.acc, _⟩ => acc
  | ⟨.gen, _⟩ => gen
  | ⟨.dat, _⟩ => dat
  | ⟨.abl, _⟩ => abl
  | ⟨.inst, h⟩ | ⟨.loc, h⟩ | ⟨.erg, h⟩ | ⟨.abs, h⟩ | ⟨.part, h⟩ | ⟨.ess, h⟩ | ⟨.transl, h⟩
  | ⟨.com, h⟩ | ⟨.ade, h⟩ | ⟨.ine, h⟩ | ⟨.ill, h⟩ | ⟨.ela, h⟩ | ⟨.all, h⟩ | ⟨.sub, h⟩ | ⟨.sup, h⟩
  | ⟨.del, h⟩ | ⟨.ter, h⟩ | ⟨.tem, h⟩ | ⟨.caus, h⟩ | ⟨.ben, h⟩ | ⟨.perl, h⟩ | ⟨.abess, h⟩ =>
    absurd h (by decide)

/-- A noun by the form of each of its twelve cells. -/
structure Noun where
  /-- The gloss. -/
  gloss : String
  /-- The declension. -/
  cls : Class
  /-- The genders the noun takes, two for a noun of common gender. -/
  genders : Finset Gender.Value
  /-- The singular form in each case. -/
  singular : Cell → String
  /-- The plural form in each case. -/
  plural : Cell → String

/-- The noun is neuter. -/
def Noun.IsNeuter (n : Noun) : Prop := n.genders = {.neut}

instance (n : Noun) : Decidable n.IsNeuter := inferInstanceAs (Decidable (_ = _))

/-- *domina* 'mistress', first declension. -/
def domina : Noun where
  gloss := "mistress"
  cls := .first
  genders := {.fem}
  singular := forms "domina" "domina" "dominam" "dominae" "dominae" "dominā"
  plural := forms "dominae" "dominae" "dominās" "dominārum" "dominīs" "dominīs"

/-- *dominus* 'master', second declension. -/
def dominus : Noun where
  gloss := "master"
  cls := .second
  genders := {.masc}
  singular := forms "dominus" "domine" "dominum" "dominī" "dominō" "dominō"
  plural := forms "dominī" "dominī" "dominōs" "dominōrum" "dominīs" "dominīs"

/-- *bellum* 'war', second declension neuter. -/
def bellum : Noun where
  gloss := "war"
  cls := .second
  genders := {.neut}
  singular := forms "bellum" "bellum" "bellum" "bellī" "bellō" "bellō"
  plural := forms "bella" "bella" "bella" "bellōrum" "bellīs" "bellīs"

/-- *cōnsul* 'consul', third declension consonant stem. -/
def consul : Noun where
  gloss := "consul"
  cls := .thirdConsonant
  genders := {.masc}
  singular := forms "cōnsul" "cōnsul" "cōnsulem" "cōnsulis" "cōnsulī" "cōnsule"
  plural := forms "cōnsulēs" "cōnsulēs" "cōnsulēs" "cōnsulum" "cōnsulibus" "cōnsulibus"

/-- *cīvis* 'citizen', third declension i-stem, of common gender. -/
def civis : Noun where
  gloss := "citizen"
  cls := .thirdI
  genders := {.masc, .fem}
  singular := forms "cīvis" "cīvis" "cīvem" "cīvis" "cīvī" "cīvī"
  plural := forms "cīvēs" "cīvēs" "cīvīs" "cīvium" "cīvibus" "cīvibus"

/-- The consonant-stem forms *cīvis* also takes: *cīve* in the ablative singular and *cīvēs* in
the accusative plural. -/
def civis.variant : Noun :=
  { civis with
    singular := Function.update civis.singular (cell .abl) "cīve"
    plural := Function.update civis.plural (cell .acc) "cīvēs" }

/-- *manus* 'hand', fourth declension. -/
def manus : Noun where
  gloss := "hand"
  cls := .fourth
  genders := {.fem}
  singular := forms "manus" "manus" "manum" "manūs" "manuī" "manū"
  plural := forms "manūs" "manūs" "manūs" "manuum" "manibus" "manibus"

/-- *diēs* 'day', fifth declension, masculine, and feminine of an appointed day. -/
def dies : Noun where
  gloss := "day"
  cls := .fifth
  genders := {.masc, .fem}
  singular := forms "diēs" "diēs" "diem" "diēī" "diēī" "diē"
  plural := forms "diēs" "diēs" "diēs" "diērum" "diēbus" "diēbus"

/-- The nouns of Blake's table. -/
def nouns : List Noun := [domina, dominus, bellum, consul, civis, manus, dies]

/-! ### Syncretism -/

/-- A neuter does not distinguish nominative and accusative in either number. -/
theorem nom_acc_syncretic_of_neuter :
    ∀ n ∈ nouns, n.IsNeuter →
      syncretism n.singular (cell .nom) (cell .acc) ∧
        syncretism n.plural (cell .nom) (cell .acc) := by
  decide

/-- No plural distinguishes dative and ablative. -/
theorem plural_dat_abl_syncretic : ∀ n ∈ nouns, syncretism n.plural (cell .dat) (cell .abl) := by
  decide

/-- The singular fails to distinguish dative and ablative in the second declension and the
i-stems, and nowhere else. -/
theorem singular_dat_abl_syncretic_iff :
    ∀ n ∈ nouns,
      syncretism n.singular (cell .dat) (cell .abl) ↔ n.cls = .second ∨ n.cls = .thirdI := by
  decide

/-- The vocative singular differs from the nominative in the non-neuters of the second
declension, and nowhere else. -/
theorem singular_nom_voc_syncretic_iff :
    ∀ n ∈ nouns,
      syncretism n.singular (cell .nom) (cell .voc) ↔ ¬ (n.cls = .second ∧ ¬ n.IsNeuter) := by
  decide

/-- No plural distinguishes nominative and vocative. -/
theorem plural_nom_voc_syncretic : ∀ n ∈ nouns, syncretism n.plural (cell .nom) (cell .voc) := by
  decide

/-- The plurals of the consonant stems, the u-stems and the ē-stems do not distinguish
nominative and accusative, and with its consonant-stem accusative neither does *cīvis*. -/
theorem plural_nom_acc_syncretic :
    (∀ n ∈ nouns, n.cls = .thirdConsonant ∨ n.cls = .fourth ∨ n.cls = .fifth →
      syncretism n.plural (cell .nom) (cell .acc)) ∧
    syncretism civis.variant.plural (cell .nom) (cell .acc) := by
  decide

end Latin.Declension
