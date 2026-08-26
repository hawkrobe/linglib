import Linglib.Syntax.Category.Classifier.Basic

/-!
# Shan Numeral Classifier Lexicon
[little-moroney-royer-2022] [moroney-2021] [cushing-1887]

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

The typological parameters follow [moroney-2021] and [little-moroney-royer-2022]: free-morpheme
numeral classifiers derived from nominal elements (*tǒ* 'body'), required uniformly by numerals
and extending to quantifiers, demonstratives and relative clauses, with a generic classifier and
no co-occurrence with plural marking.
-/

namespace Shan.Classifiers

-- ============================================================================
-- Numeral classifiers (Table 6 of [little-moroney-royer-2022])
-- ============================================================================

/-- ʔǎn — inanimates (generic/default classifier for inanimate objects). -/
def an : Classifier :=
  { form := "ʔǎn", gloss := "inanimate/generic", isDefault := true }

/-- tǒ — animals. Also means 'body' as a free noun. -/
def to : Classifier :=
  { form := "tǒ", gloss := "animal"
  , semantics := [.animacy] }

/-- kǒ — people/humans. -/
def ko : Classifier :=
  { form := "kǒ", gloss := "human"
  , semantics := [.humanness] }

/-- hòj — round objects (fruits, jujubes). -/
def hoj : Classifier :=
  { form := "hòj", gloss := "round"
  , semantics := [.shape], dimension := some .threeD }

/-- ton — plants, trees. Head of compound *ton-mâj* 'tree'. -/
def ton : Classifier :=
  { form := "ton", gloss := "plant"
  , semantics := [.shape], dimension := some .oneD }

/-- lǎŋ — buildings, houses. -/
def lang : Classifier :=
  { form := "lǎŋ", gloss := "building"
  , semantics := [.function] }

-- ============================================================================
-- Inventory
-- ============================================================================

def allClassifiers : List Classifier :=
  [an, to, ko, hoj, ton, lang]

def defaultClassifier : Classifier := an

-- ============================================================================
-- Verification
-- ============================================================================

/-- The default classifier is marked as default. -/
theorem default_is_default : defaultClassifier.isDefault = true := rfl

/-- All non-default classifiers carry at least one semantic parameter. -/
theorem specific_classifiers_motivated :
    (allClassifiers.filter (!·.isDefault)).all
      (·.semantics.length > 0) = true := by decide

/-- Shan classifiers are free morphemes (no leading hyphen). -/
theorem classifiers_are_free :
    allClassifiers.all (!·.form.startsWith "-") = true := by native_decide

end Shan.Classifiers

/-! ### Typological parameters -/

namespace Shan

/-- Classifiers occur in the numeral phrase and characterize the head noun. -/
def classifierLocus : Classifier.Scope := .numeralNP

def classifierConstituent : Classifier.Constituent := .headNoun

/-- The kind of device, read off its locus and the constituent it characterizes. -/
abbrev classifierKind : Option Classifier.Kind :=
  Classifier.kind classifierLocus classifierConstituent

/-- Every environment the device operates in. -/
def classifierScopes : List Classifier.Scope := [.numeralNP, .attributiveNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : Classifier.Assignment := .semantic

/-- Free morphemes. -/
def classifierRealizations : List Classifier.Realization := [.freeForm]

def classifierAgreement : Bool := false

def classifierObligatory : Bool := true

/-- Whether the inventory has a general classifier. -/
def classifierDefault : Bool := Classifiers.allClassifiers.any (·.isDefault)

def classifierSemantics : List Classifier.Parameter :=
  Classifier.parameters Classifiers.allClassifiers

def obligatoryNumber : Bool := false

/-- Whether classifiers and plural marking co-occur. -/
def pluralClassifierCooccur : Bool := false

end Shan
