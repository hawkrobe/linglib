import Linglib.Syntax.Category.Classifier.Basic

/-!
# Ch'ol Numeral Classifier Lexicon

Typed classifier entries for Ch'ol (Cholan, Mayan), a classifier-for-numeral
language ([little-moroney-royer-2022]; [bale-coon-2014]). Classifiers in
Ch'ol are bound morphemes suffixed to the numeral stem, obligatory with all
Mayan-based numerals (1–6 and the vigesimal system); Spanish-borrowed
numerals (7+) already encode a measure function and take no classifier.

## Main declarations

* `Chol.Classifiers.pej`, `kojty`, `tyikil`, `kej`, `tsijty`, `bujch`: the
  classifier entries ([little-moroney-royer-2022] Table 4).
* `Chol.Classifiers.allClassifiers`, `defaultClassifier`: the inventory and
  its generic default (*-p'ej*).

## Implementation notes

Ch'ol classifiers are largely derived from positional and transitive verb
roots ([arcos-lopez-2009]; [bale-et-al-2019]); the position or shape of the
noun is relevant, so the same noun can be counted with different classifiers
depending on its configuration (e.g. one long tree vs. one fallen tree).
[arcos-lopez-2009] identifies at least 180 classifiers.

In the CLF-for-NUM analysis ([little-moroney-royer-2022] §4;
[bale-coon-2014]), each classifier denotes a measure function μ that the
numeral requires as its first argument:

  ⟦ux⟧ = λm λP λx. [P(x) ∧ m(x) = 3]
  ⟦-kojty⟧ = μ_# (atom-counting measure for animals)

The typological parameters follow [bale-coon-2014], [bale-et-al-2019] and
[little-moroney-royer-2022]: numeral classifiers suffixed to the numeral stem, obligatory with
native numerals (Spanish loan numerals reject them), with *-p'ej* as the generic default and
attested co-occurrence with plural marking.
-/

namespace Chol.Classifiers

/-! ### Numeral classifiers ([little-moroney-royer-2022] Table 4) -/

/-- -p'ej — inanimate/generic default classifier. Semantically bleached
    for inanimates; also the base of vigesimal classifiers (-k'al for 20,
    -bajk for 400, -pijk for 8000). -/
def pej : Classifier :=
  { form := "-p'ej", gloss := "inanimate/generic", isDefault := true }

/-- -kojty — animals. Derived from positional root *koty* 'standing on
    four legs'. -/
def kojty : Classifier :=
  { form := "-kojty", gloss := "animal"
  , semantics := [.animacy] }

/-- -tyikil — people/humans. -/
def tyikil : Classifier :=
  { form := "-tyikil", gloss := "human"
  , semantics := [.humanness] }

/-- -k'ej — flat round objects (tortillas, tables). -/
def kej : Classifier :=
  { form := "-k'ej", gloss := "flat.round"
  , semantics := [.shape], dimension := some .twoD }

/-- -ts'ijty — long things (trees, ropes). -/
def tsijty : Classifier :=
  { form := "-ts'ijty", gloss := "long"
  , semantics := [.shape], dimension := some .oneD }

/-- -bujch — seated/propped up things (bottles propped up, seated objects).
    Derived from positional root *buch* 'seated'. -/
def bujch : Classifier :=
  { form := "-bujch", gloss := "seated/propped"
  , semantics := [.arrangement] }

/-! ### Inventory -/

def allClassifiers : List Classifier :=
  [pej, kojty, tyikil, kej, tsijty, bujch]

def defaultClassifier : Classifier := pej

/-! ### Verification -/

/-- The default classifier is marked as default. -/
theorem default_is_default : defaultClassifier.isDefault = true := rfl

/-- All non-default classifiers carry at least one semantic parameter. -/
theorem specific_classifiers_motivated :
    (allClassifiers.filter (!·.isDefault)).all
      (·.semantics.length > 0) = true := by decide

/-- Ch'ol classifiers are bound morphemes (suffixes on the numeral stem).
    All forms begin with a hyphen, indicating bound status. -/
theorem classifiers_are_bound :
    allClassifiers.all (·.form.startsWith "-") = true := by native_decide

end Chol.Classifiers

/-! ### Typological parameters -/

namespace Chol

/-- Classifiers occur in the numeral phrase and characterize the head noun. -/
def classifierLocus : Classifier.Scope := .numeralNP

def classifierConstituent : Classifier.Constituent := .headNoun

/-- The kind of device, read off its locus and the constituent it characterizes. -/
abbrev classifierKind : Option Classifier.Kind :=
  Classifier.kind classifierLocus classifierConstituent

/-- Every environment the device operates in. -/
def classifierScopes : List Classifier.Scope := [.numeralNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : Classifier.Assignment := .semantic

/-- Suffixes on the numeral stem. -/
def classifierRealizations : List Classifier.Realization := [.suffix]

def classifierAgreement : Bool := false

/-- Obligatory with native numerals. -/
def classifierObligatory : Bool := true

/-- Whether the inventory has a general classifier. -/
def classifierDefault : Bool := Classifiers.allClassifiers.any (·.isDefault)

def classifierSemantics : List Classifier.Parameter :=
  Classifier.parameters Classifiers.allClassifiers

def obligatoryNumber : Bool := false

/-- Whether classifiers and plural marking co-occur. -/
def pluralClassifierCooccur : Bool := true

end Chol
