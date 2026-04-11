import Linglib.Core.Lexical.NounCategorization

/-!
# Ch'ol Numeral Classifier Lexicon
@cite{little-moroney-royer-2022} @cite{bale-coon-2014} @cite{arcos-lopez-2009}

Typed classifier entries for Ch'ol (Cholan, Mayan), a classifier-for-numeral
language. Classifiers in Ch'ol are bound morphemes suffixed to the numeral
stem and are obligatory with all Mayan-based numerals (1–6 and vigesimal
system). Spanish-borrowed numerals (7+) already encode a measure function
and do not take classifiers.

## Classifier selection

Ch'ol classifiers are largely derived from positional and transitive verb
roots (@cite{arcos-lopez-2009}; @cite{bale-et-al-2019}). The position or
shape of the noun is relevant: the same noun can be counted with different
classifiers depending on its configuration (e.g., one long tree vs. one
fallen tree). @cite{arcos-lopez-2009} identifies at least 180 classifiers.

## CLF-for-NUM semantics

In the CLF-for-NUM analysis (@cite{little-moroney-royer-2022} §4;
@cite{bale-coon-2014}), each classifier denotes a measure function μ
that the numeral requires as its first argument:
  ⟦ux⟧ = λm λP λx. [P(x) ∧ m(x) = 3]
  ⟦-kojty⟧ = μ_# (atom-counting measure for animals)
-/

namespace Fragments.Mayan.Chol.Classifiers

open Core.NounCategorization (ClassifierEntry SemanticParameter ShapeDimension)

-- ============================================================================
-- Numeral classifiers (Table 4 of @cite{little-moroney-royer-2022})
-- ============================================================================

/-- -p'ej — inanimate/generic default classifier. Semantically bleached
    for inanimates; also the base of vigesimal classifiers (-k'al for 20,
    -bajk for 400, -pijk for 8000). -/
def pej : ClassifierEntry :=
  { form := "-p'ej", gloss := "inanimate/generic", isDefault := true }

/-- -kojty — animals. Derived from positional root *koty* 'standing on
    four legs'. -/
def kojty : ClassifierEntry :=
  { form := "-kojty", gloss := "animal"
  , semantics := [.animacy] }

/-- -tyikil — people/humans. -/
def tyikil : ClassifierEntry :=
  { form := "-tyikil", gloss := "human"
  , semantics := [.humanness] }

/-- -k'ej — flat round objects (tortillas, tables). -/
def kej : ClassifierEntry :=
  { form := "-k'ej", gloss := "flat.round"
  , semantics := [.shape], shapeDimension := some .twoD }

/-- -ts'ijty — long things (trees, ropes). -/
def tsijty : ClassifierEntry :=
  { form := "-ts'ijty", gloss := "long"
  , semantics := [.shape], shapeDimension := some .oneD }

/-- -bujch — seated/propped up things (bottles propped up, seated objects).
    Derived from positional root *buch* 'seated'. -/
def bujch : ClassifierEntry :=
  { form := "-bujch", gloss := "seated/propped"
  , semantics := [.arrangement] }

-- ============================================================================
-- Inventory
-- ============================================================================

def allClassifiers : List ClassifierEntry :=
  [pej, kojty, tyikil, kej, tsijty, bujch]

def defaultClassifier : ClassifierEntry := pej

-- ============================================================================
-- Verification
-- ============================================================================

/-- The default classifier is marked as default. -/
theorem default_is_default : defaultClassifier.isDefault = true := rfl

/-- All non-default classifiers carry at least one semantic parameter. -/
theorem specific_classifiers_motivated :
    (allClassifiers.filter (!·.isDefault)).all
      (·.semantics.length > 0) = true := by native_decide

/-- Ch'ol classifiers are bound morphemes (suffixes on the numeral stem).
    All forms begin with a hyphen, indicating bound status. -/
theorem classifiers_are_bound :
    allClassifiers.all (·.form.startsWith "-") = true := by native_decide

end Fragments.Mayan.Chol.Classifiers
