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

/-- A noun by the form of each of its twelve cells. -/
structure Noun where
  /-- The gloss. -/
  gloss : String
  /-- The declension. -/
  cls : Class
  /-- The genders the noun takes, two for a noun of common gender. -/
  genders : Finset Gender.Value
  /-- The singular form in each case. -/
  singular : Case.Value → String
  /-- The plural form in each case. -/
  plural : Case.Value → String

/-- The noun is neuter. -/
def Noun.IsNeuter (n : Noun) : Prop := n.genders = {.neut}

instance (n : Noun) : Decidable n.IsNeuter := inferInstanceAs (Decidable (_ = _))

/-- *domina* 'mistress', first declension. -/
def domina : Noun where
  gloss := "mistress"
  cls := .first
  genders := {.fem}
  singular
    | .nom => "domina" | .voc => "domina" | .acc => "dominam"
    | .gen => "dominae" | .dat => "dominae" | .abl => "dominā"
  plural
    | .nom => "dominae" | .voc => "dominae" | .acc => "dominās"
    | .gen => "dominārum" | .dat => "dominīs" | .abl => "dominīs"

/-- *dominus* 'master', second declension. -/
def dominus : Noun where
  gloss := "master"
  cls := .second
  genders := {.masc}
  singular
    | .nom => "dominus" | .voc => "domine" | .acc => "dominum"
    | .gen => "dominī" | .dat => "dominō" | .abl => "dominō"
  plural
    | .nom => "dominī" | .voc => "dominī" | .acc => "dominōs"
    | .gen => "dominōrum" | .dat => "dominīs" | .abl => "dominīs"

/-- *bellum* 'war', second declension neuter. -/
def bellum : Noun where
  gloss := "war"
  cls := .second
  genders := {.neut}
  singular
    | .nom => "bellum" | .voc => "bellum" | .acc => "bellum"
    | .gen => "bellī" | .dat => "bellō" | .abl => "bellō"
  plural
    | .nom => "bella" | .voc => "bella" | .acc => "bella"
    | .gen => "bellōrum" | .dat => "bellīs" | .abl => "bellīs"

/-- *cōnsul* 'consul', third declension consonant stem. -/
def consul : Noun where
  gloss := "consul"
  cls := .thirdConsonant
  genders := {.masc}
  singular
    | .nom => "cōnsul" | .voc => "cōnsul" | .acc => "cōnsulem"
    | .gen => "cōnsulis" | .dat => "cōnsulī" | .abl => "cōnsule"
  plural
    | .nom => "cōnsulēs" | .voc => "cōnsulēs" | .acc => "cōnsulēs"
    | .gen => "cōnsulum" | .dat => "cōnsulibus" | .abl => "cōnsulibus"

/-- *cīvis* 'citizen', third declension i-stem, of common gender. -/
def civis : Noun where
  gloss := "citizen"
  cls := .thirdI
  genders := {.masc, .fem}
  singular
    | .nom => "cīvis" | .voc => "cīvis" | .acc => "cīvem"
    | .gen => "cīvis" | .dat => "cīvī" | .abl => "cīvī"
  plural
    | .nom => "cīvēs" | .voc => "cīvēs" | .acc => "cīvīs"
    | .gen => "cīvium" | .dat => "cīvibus" | .abl => "cīvibus"

/-- The consonant-stem forms *cīvis* also takes: *cīve* in the ablative singular and *cīvēs* in
the accusative plural. -/
def civis.variant : Noun :=
  { civis with
    singular := Function.update civis.singular .abl "cīve"
    plural := Function.update civis.plural .acc "cīvēs" }

/-- *manus* 'hand', fourth declension. -/
def manus : Noun where
  gloss := "hand"
  cls := .fourth
  genders := {.fem}
  singular
    | .nom => "manus" | .voc => "manus" | .acc => "manum"
    | .gen => "manūs" | .dat => "manuī" | .abl => "manū"
  plural
    | .nom => "manūs" | .voc => "manūs" | .acc => "manūs"
    | .gen => "manuum" | .dat => "manibus" | .abl => "manibus"

/-- *diēs* 'day', fifth declension, masculine, and feminine of an appointed day. -/
def dies : Noun where
  gloss := "day"
  cls := .fifth
  genders := {.masc, .fem}
  singular
    | .nom => "diēs" | .voc => "diēs" | .acc => "diem"
    | .gen => "diēī" | .dat => "diēī" | .abl => "diē"
  plural
    | .nom => "diēs" | .voc => "diēs" | .acc => "diēs"
    | .gen => "diērum" | .dat => "diēbus" | .abl => "diēbus"

/-- The nouns of Blake's table. -/
def nouns : List Noun := [domina, dominus, bellum, consul, civis, manus, dies]

/-! ### Syncretism -/

/-- A neuter does not distinguish nominative and accusative in either number. -/
theorem nom_acc_syncretic_of_neuter :
    ∀ n ∈ nouns, n.IsNeuter →
      syncretism n.singular .nom .acc ∧ syncretism n.plural .nom .acc := by
  decide

/-- No plural distinguishes dative and ablative. -/
theorem plural_dat_abl_syncretic : ∀ n ∈ nouns, syncretism n.plural .dat .abl := by decide

/-- The singular fails to distinguish dative and ablative in the second declension and the
i-stems, and nowhere else. -/
theorem singular_dat_abl_syncretic_iff :
    ∀ n ∈ nouns, syncretism n.singular .dat .abl ↔ n.cls = .second ∨ n.cls = .thirdI := by
  decide

/-- The vocative singular differs from the nominative in the non-neuters of the second
declension, and nowhere else. -/
theorem singular_nom_voc_syncretic_iff :
    ∀ n ∈ nouns, syncretism n.singular .nom .voc ↔ ¬ (n.cls = .second ∧ ¬ n.IsNeuter) := by
  decide

/-- No plural distinguishes nominative and vocative. -/
theorem plural_nom_voc_syncretic : ∀ n ∈ nouns, syncretism n.plural .nom .voc := by decide

/-- The plurals of the consonant stems, the u-stems and the ē-stems do not distinguish
nominative and accusative, and with its consonant-stem accusative neither does *cīvis*. -/
theorem plural_nom_acc_syncretic :
    (∀ n ∈ nouns, n.cls = .thirdConsonant ∨ n.cls = .fourth ∨ n.cls = .fifth →
      syncretism n.plural .nom .acc) ∧
    syncretism civis.variant.plural .nom .acc := by
  decide

end Latin.Declension
