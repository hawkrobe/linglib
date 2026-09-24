module

public import Linglib.Syntax.Category.Classifier.Basic

/-!
# Ch'ol numeral classifiers

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

Following [bale-coon-2014], [bale-et-al-2019] and [little-moroney-royer-2022], the classifiers are
suffixes on the numeral stem, obligatory with native numerals, which Spanish loan numerals
reject, with *-p'ej* as the generic default, and they co-occur with plural marking.

## References

* [little-moroney-royer-2022]
* [bale-coon-2014]
* [bale-et-al-2019]
* [arcos-lopez-2009]
-/

@[expose] public section

namespace Chol.Classifiers

/-! ### Numeral classifiers ([little-moroney-royer-2022] Table 4) -/

/-- -p'ej — inanimate/generic default classifier. Semantically bleached
    for inanimates; also the base of vigesimal classifiers (-k'al for 20,
    -bajk for 400, -pijk for 8000). -/
def pej : Classifier := { form := "-p'ej", gloss := "inanimate/generic" }

/-- -kojty — animals. Derived from positional root *koty* 'standing on
    four legs'. -/
def kojty : Classifier := { form := "-kojty", gloss := "animal" }

/-- -tyikil — people/humans. -/
def tyikil : Classifier := { form := "-tyikil", gloss := "human" }

/-- -k'ej — flat round objects (tortillas, tables). -/
def kej : Classifier := { form := "-k'ej", gloss := "flat.round" }

/-- -ts'ijty — long things (trees, ropes). -/
def tsijty : Classifier := { form := "-ts'ijty", gloss := "long" }

/-- -bujch — seated/propped up things (bottles propped up, seated objects).
    Derived from positional root *buch* 'seated'. -/
def bujch : Classifier := { form := "-bujch", gloss := "seated/propped" }

/-! ### Inventory -/

def allClassifiers : List Classifier :=
  [pej, kojty, tyikil, kej, tsijty, bujch]

def defaultClassifier : Classifier := pej

end Chol.Classifiers

namespace Chol

/-- Whether classifiers and plural marking co-occur. -/
def pluralClassifierCooccur : Bool := true

end Chol
