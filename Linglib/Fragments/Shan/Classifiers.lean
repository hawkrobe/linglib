module

public import Linglib.Syntax.Category.Classifier.Basic

/-!
# Shan numeral classifiers

Typed classifier entries for Shan (Southwestern Tai, Kra-Dai), a
classifier-for-noun language spoken in Myanmar and surrounding countries
by approximately 4.6 million speakers.

Unlike Ch'ol classifiers, which are bound to the numeral, Shan classifiers
are free morphemes derived from nominal elements. The classifier for
animals, *tǒ*, also means 'body'; the classifier for plants, *ton*, is
the head of the compound *ton-mâj* 'tree'.

## CLF-for-N semantics

In the CLF-for-N analysis ([little-moroney-royer-2022] §4;
[chierchia-1998]; [jenks-2011]), the classifier atomizes the
noun denotation:
  ⟦CLF⟧ = λPλx.[P(x) ∧ ¬∃y[P(y) ∧ y < x]]

Because the classifier is semantically connected to the noun (not the
numeral), it appears in contexts beyond numerals: with quantifiers (*ku*
'every'), demonstratives (*nâj* 'this'), and relative clauses.

## Word order

Shan word order is [N Num CLF], with the noun preceding the numeral and
classifier. [moroney-2021] analyzes this as NP-movement from a base
position below ClfP to a position above the numeral and classifier.

Following [moroney-2021] and [little-moroney-royer-2022], the classifiers are free morphemes
derived from nominal elements, required uniformly by numerals and extending to quantifiers,
demonstratives and relative clauses, with a generic classifier, and they do not co-occur with
plural marking.

## References

* [little-moroney-royer-2022]
* [moroney-2021]
* [chierchia-1998]
-/

@[expose] public section

namespace Shan.Classifiers

/-! ### Numeral classifiers ([little-moroney-royer-2022] Table 6) -/

/-- ʔǎn — inanimates (generic/default classifier for inanimate objects). -/
def an : Classifier := { form := "ʔǎn", gloss := "inanimate/generic" }

/-- tǒ — animals. Also means 'body' as a free noun. -/
def to : Classifier := { form := "tǒ", gloss := "animal" }

/-- kǒ — people/humans. -/
def ko : Classifier := { form := "kǒ", gloss := "human" }

/-- hòj — round objects (fruits, jujubes). -/
def hoj : Classifier := { form := "hòj", gloss := "round" }

/-- ton — plants, trees. Head of compound *ton-mâj* 'tree'. -/
def ton : Classifier := { form := "ton", gloss := "plant" }

/-- lǎŋ — buildings, houses. -/
def lang : Classifier := { form := "lǎŋ", gloss := "building" }

/-! ### Inventory -/

def allClassifiers : List Classifier :=
  [an, to, ko, hoj, ton, lang]

def defaultClassifier : Classifier := an

end Shan.Classifiers

namespace Shan

/-- Whether classifiers and plural marking co-occur. -/
def pluralClassifierCooccur : Bool := false

end Shan
