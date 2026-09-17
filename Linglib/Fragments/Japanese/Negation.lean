import Linglib.Morphology.Morphotactics.RelevanceHierarchy
import Linglib.Syntax.Negation

/-!
# Japanese negation

Japanese negates a verb with the suffix *-nai* on its stem, and *-nai* inflects as an
adjective in *-i*: the past of *tabe-nai* 'does not eat' is *tabe-nakatta*, with the
adjectival past, not the verbal *-ta* of *tabe-ta* 'ate'. Tense, mood and politeness thus
leave the verb stem for the negative suffix, the asymmetry of finiteness and of category in
Miestamo's typology, while the paradigm itself is symmetric, each affirmative form having its
own negative counterpart.

## Main definitions

* `Japanese.Negation.negSuffix` — the negative suffix
* `Japanese.Negation.taberuParadigm`, `Japanese.Negation.yomuParadigm` — the affirmative and
  negative forms of a vowel-stem and a consonant-stem verb
* `Japanese.Negation.japaneseNegDistribution` — the categories marked on the stem and on the
  suffix in the affirmative and the negative

## References

* [dryer-haspelmath-2013]
* [haspelmath-2013]
* [miestamo-2005]
-/

namespace Japanese.Negation

open Morphology (MorphCategory)
open Syntax.Negation

/-- The negative suffix *-nai*. -/
def negSuffix : Marker := { pieces := [[.suff "nai"]] }

/-- The forms of the verb paradigm. -/
inductive Form where
  | nonpast
  | past
  | gerund
  | conditional
  | volitional
  deriving DecidableEq, Repr

/-- A cell of a negation paradigm: a form's affirmative and negative. -/
structure Cell where
  /-- The form. -/
  form : Form
  /-- The affirmative. -/
  affirmative : String
  /-- The negative. -/
  negative : String
  deriving DecidableEq, Repr

/-- The paradigm of the vowel-stem verb *taberu* 'eat'. -/
def taberuParadigm : List Cell :=
  [ ⟨.nonpast, "taberu", "tabenai"⟩,
    ⟨.past, "tabeta", "tabenakatta"⟩,
    ⟨.gerund, "tabete", "tabenakute"⟩,
    ⟨.conditional, "tabereba", "tabenakereba"⟩,
    ⟨.volitional, "tabeyō", "tabenai darō"⟩ ]

/-- The paradigm of the consonant-stem verb *yomu* 'read'. -/
def yomuParadigm : List Cell :=
  [ ⟨.nonpast, "yomu", "yomanai"⟩,
    ⟨.past, "yonda", "yomanakatta"⟩ ]

/-- Where the inflectional categories are marked: on the stem in the affirmative, and in the
negative on the negative suffix. -/
structure NegInflDistribution where
  /-- The categories on the verb stem in the affirmative. -/
  affirmativeOnStem : Finset MorphCategory
  /-- The categories on the verb stem in the negative. -/
  negativeOnStem : Finset MorphCategory
  /-- The categories on the negative suffix. -/
  negativeOnSuffix : Finset MorphCategory
  deriving DecidableEq

/-- Tense, mood and agreement leave the stem for the suffix under negation. -/
def japaneseNegDistribution : NegInflDistribution :=
  { affirmativeOnStem := {.tense, .aspect, .mood, .agreement .subj},
    negativeOnStem := {.aspect},
    negativeOnSuffix := {.negation, .tense, .mood} }

end Japanese.Negation
