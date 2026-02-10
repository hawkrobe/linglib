import Linglib.Core.NounCategorization

/-!
# Japanese Classifier Lexicon

Typed classifier entries for Japanese (josūshi 助数詞).

Japanese numeral classifiers are suffixed to the numeral (e.g. san-biki
三匹 "three-CL:small.animal"). Like Mandarin, selection is semantically
motivated, encoding animacy, shape, and function.

## References

- Aikhenvald, A. Y. (2000). Classifiers, Ch 4, Table 1.1.
- Downing, P. (1996). Numeral Classifier Systems: The Case of Japanese.
- Lakoff, G. (1987). Women, Fire, and Dangerous Things (on Japanese classifiers).
-/

namespace Fragments.Japanese.Classifiers

open Core.NounCategorization (ClassifierEntry SemanticParameter)

-- ============================================================================
-- Sortal classifiers
-- ============================================================================

/-- つ tsu — general/default counter (native Japanese numerals).
    Semantically bleached default. -/
def tsu : ClassifierEntry :=
  { form := "つ", gloss := "general", isDefault := true }

/-- 匹 hiki — small/medium animals (dogs, cats, insects, fish).
    Encodes: animacy + size. -/
def hiki : ClassifierEntry :=
  { form := "匹", gloss := "small.animal"
  , semantics := [.animacy, .size] }

/-- 冊 satsu — bound volumes (books, magazines).
    Encodes: shape (flat, bound). -/
def satsu : ClassifierEntry :=
  { form := "冊", gloss := "bound.volume"
  , semantics := [.shape] }

/-- 台 dai — machines, vehicles (cars, computers, pianos).
    Encodes: function (mechanical). -/
def dai : ClassifierEntry :=
  { form := "台", gloss := "machine/vehicle"
  , semantics := [.function] }

/-- 羽 wa — birds (and rabbits, by cultural extension).
    Encodes: animacy (avian). -/
def wa : ClassifierEntry :=
  { form := "羽", gloss := "bird"
  , semantics := [.animacy] }

/-- 本 hon' — long, thin objects (pens, bottles, flowers, umbrellas).
    Encodes: shape (1D, elongated). -/
def hon' : ClassifierEntry :=
  { form := "本", gloss := "long.thin"
  , semantics := [.shape] }

/-- 人 nin — people (neutral register).
    Encodes: humanness. -/
def nin : ClassifierEntry :=
  { form := "人", gloss := "person"
  , semantics := [.humanness] }

/-- 枚 mai — flat, thin objects (paper, stamps, plates, shirts).
    Encodes: shape (2D, flat). -/
def mai : ClassifierEntry :=
  { form := "枚", gloss := "flat.thin"
  , semantics := [.shape] }

/-- 頭 tou — large animals (horses, cattle, elephants).
    Encodes: animacy + large size. -/
def tou : ClassifierEntry :=
  { form := "頭", gloss := "large.animal"
  , semantics := [.animacy, .size] }

-- ============================================================================
-- Inventory
-- ============================================================================

def allClassifiers : List ClassifierEntry :=
  [tsu, hiki, satsu, dai, wa, hon', nin, mai, tou]

def defaultClassifier : ClassifierEntry := tsu

def lookup (form : String) : Option ClassifierEntry :=
  allClassifiers.find? (·.form == form)

-- ============================================================================
-- Verification
-- ============================================================================

/-- つ is the default classifier. -/
theorem tsu_is_default : tsu.isDefault = true := rfl

/-- 匹 encodes animacy. -/
theorem hiki_encodes_animacy : hiki.encodes .animacy = true := by native_decide

/-- 人 encodes humanness. -/
theorem nin_encodes_humanness : nin.encodes .humanness = true := by native_decide

/-- All non-default classifiers have at least one semantic parameter. -/
theorem specific_classifiers_have_semantics :
    (allClassifiers.filter (!·.isDefault)).all (·.semantics.length > 0) = true := by
  native_decide

end Fragments.Japanese.Classifiers
