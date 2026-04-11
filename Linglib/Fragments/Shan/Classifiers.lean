import Linglib.Core.Lexical.NounCategorization

/-!
# Shan Numeral Classifier Lexicon
@cite{little-moroney-royer-2022} @cite{moroney-2021} @cite{cushing-1887}

Typed classifier entries for Shan (Southwestern Tai, Kra-Dai), a
classifier-for-noun language spoken in Myanmar and surrounding countries
by approximately 4.6 million speakers.

Unlike Ch'ol classifiers, which are bound to the numeral, Shan classifiers
are free morphemes derived from nominal elements. The classifier for
animals, *tǒ*, also means 'body'; the classifier for plants, *ton*, is
the head of the compound *ton-mâj* 'tree'.

## CLF-for-N semantics

In the CLF-for-N analysis (@cite{little-moroney-royer-2022} §4;
@cite{chierchia-1998}; @cite{jenks-2011}), the classifier atomizes the
noun denotation:
  ⟦CLF⟧ = λPλx.[P(x) ∧ ¬∃y[P(y) ∧ y < x]]

Because the classifier is semantically connected to the noun (not the
numeral), it appears in contexts beyond numerals: with quantifiers (*ku*
'every'), demonstratives (*nâj* 'this'), and relative clauses.

## Word order

Shan word order is [N Num CLF], with the noun preceding the numeral and
classifier. @cite{moroney-2021} analyzes this as NP-movement from a base
position below ClfP to a position above the numeral and classifier.
-/

namespace Fragments.Shan.Classifiers

open Core.NounCategorization (ClassifierEntry SemanticParameter ShapeDimension)

-- ============================================================================
-- Numeral classifiers (Table 6 of @cite{little-moroney-royer-2022})
-- ============================================================================

/-- ʔǎn — inanimates (generic/default classifier for inanimate objects). -/
def an : ClassifierEntry :=
  { form := "ʔǎn", gloss := "inanimate/generic", isDefault := true }

/-- tǒ — animals. Also means 'body' as a free noun. -/
def to : ClassifierEntry :=
  { form := "tǒ", gloss := "animal"
  , semantics := [.animacy] }

/-- kǒ — people/humans. -/
def ko : ClassifierEntry :=
  { form := "kǒ", gloss := "human"
  , semantics := [.humanness] }

/-- hòj — round objects (fruits, jujubes). -/
def hoj : ClassifierEntry :=
  { form := "hòj", gloss := "round"
  , semantics := [.shape], shapeDimension := some .threeD }

/-- ton — plants, trees. Head of compound *ton-mâj* 'tree'. -/
def ton : ClassifierEntry :=
  { form := "ton", gloss := "plant"
  , semantics := [.shape], shapeDimension := some .oneD }

/-- lǎŋ — buildings, houses. -/
def lang : ClassifierEntry :=
  { form := "lǎŋ", gloss := "building"
  , semantics := [.function] }

-- ============================================================================
-- Inventory
-- ============================================================================

def allClassifiers : List ClassifierEntry :=
  [an, to, ko, hoj, ton, lang]

def defaultClassifier : ClassifierEntry := an

-- ============================================================================
-- Verification
-- ============================================================================

/-- The default classifier is marked as default. -/
theorem default_is_default : defaultClassifier.isDefault = true := rfl

/-- All non-default classifiers carry at least one semantic parameter. -/
theorem specific_classifiers_motivated :
    (allClassifiers.filter (!·.isDefault)).all
      (·.semantics.length > 0) = true := by native_decide

/-- Shan classifiers are free morphemes (no leading hyphen). -/
theorem classifiers_are_free :
    allClassifiers.all (!·.form.startsWith "-") = true := by native_decide

end Fragments.Shan.Classifiers
