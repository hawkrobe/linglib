import Linglib.Core.NounCategorization

/-!
# Mandarin Chinese Classifier Lexicon

Typed classifier entries for Mandarin Chinese, replacing unstructured
string representations with semantically annotated `ClassifierEntry` values.

Mandarin has a large numeral classifier system (~100+ classifiers in common
use). This fragment covers the classifiers attested in the noun lexicon.

## Classifier selection

Classifier selection in Mandarin is semantically motivated (Aikhenvald 2000
§11.2.3). Sortal classifiers encode inherent properties (animacy, shape,
function); the general classifier 个 serves as a default/residue.

## References

- Aikhenvald, A. Y. (2000). Classifiers, Ch 4, §11.2.3.
- Chao, Y. R. (1968). A Grammar of Spoken Chinese.
- Erbaugh, M. S. (1986). Taking Stock: The Development of Chinese Noun Classifiers.
-/

namespace Fragments.Mandarin.Classifiers

open Core.NounCategorization (ClassifierEntry SemanticParameter)

-- ============================================================================
-- Sortal classifiers (inherent properties)
-- ============================================================================

/-- 个 gè — general/default classifier. Semantically bleached; used when no
    specific classifier applies, or as an informal substitute. -/
def ge : ClassifierEntry :=
  { form := "个", gloss := "general", isDefault := true }

/-- 只 zhī — small animals (birds, cats, dogs, insects).
    Encodes: animacy + small size. -/
def zhi : ClassifierEntry :=
  { form := "只", gloss := "small.animal"
  , semantics := [.animacy, .size] }

/-- 本 běn — bound volumes (books, magazines, notebooks).
    Encodes: shape (flat, bound objects). -/
def ben : ClassifierEntry :=
  { form := "本", gloss := "bound.volume"
  , semantics := [.shape] }

/-- 辆 liàng — wheeled vehicles (cars, bicycles, carts).
    Encodes: function (transport). -/
def liang : ClassifierEntry :=
  { form := "辆", gloss := "vehicle"
  , semantics := [.function] }

/-- 朵 duǒ — flowers, clouds (small, delicate, clustered).
    Encodes: shape (small, round/clustered). -/
def duo : ClassifierEntry :=
  { form := "朵", gloss := "flower/cloud"
  , semantics := [.shape, .size] }

/-- 位 wèi — persons (honorific/polite register).
    Encodes: humanness + social status. -/
def wei : ClassifierEntry :=
  { form := "位", gloss := "person.HON"
  , semantics := [.humanness, .socialStatus] }

/-- 条 tiáo — long, thin, flexible objects (rivers, roads, snakes, fish).
    Encodes: shape (1D, elongated). -/
def tiao : ClassifierEntry :=
  { form := "条", gloss := "long.thin"
  , semantics := [.shape] }

/-- 张 zhāng — flat objects with a surface (paper, tables, beds, maps).
    Encodes: shape (2D, flat surface). -/
def zhang : ClassifierEntry :=
  { form := "张", gloss := "flat.surface"
  , semantics := [.shape] }

/-- 把 bǎ — objects with a handle (knives, chairs, umbrellas).
    Encodes: shape (graspable handle) + function. -/
def ba : ClassifierEntry :=
  { form := "把", gloss := "handled"
  , semantics := [.shape, .function] }

/-- 头 tóu — large animals (cattle, elephants, pigs).
    Encodes: animacy + large size. -/
def tou : ClassifierEntry :=
  { form := "头", gloss := "large.animal"
  , semantics := [.animacy, .size] }

/-- 棵 kē — plants, trees (rooted, standing).
    Encodes: shape (upright, rooted). -/
def ke : ClassifierEntry :=
  { form := "棵", gloss := "plant/tree"
  , semantics := [.shape] }

-- ============================================================================
-- Inventory
-- ============================================================================

def allClassifiers : List ClassifierEntry :=
  [ge, zhi, ben, liang, duo, wei, tiao, zhang, ba, tou, ke]

def defaultClassifier : ClassifierEntry := ge

/-- Look up a classifier by form. -/
def lookup (form : String) : Option ClassifierEntry :=
  allClassifiers.find? (·.form == form)

-- ============================================================================
-- Verification
-- ============================================================================

/-- 个 is the default classifier. -/
theorem ge_is_default : ge.isDefault = true := rfl

/-- 只 encodes animacy. -/
theorem zhi_encodes_animacy : zhi.encodes .animacy = true := by native_decide

/-- 位 encodes humanness. -/
theorem wei_encodes_humanness : wei.encodes .humanness = true := by native_decide

/-- 本 encodes shape. -/
theorem ben_encodes_shape : ben.encodes .shape = true := by native_decide

/-- All non-default classifiers have at least one semantic parameter. -/
theorem specific_classifiers_have_semantics :
    (allClassifiers.filter (!·.isDefault)).all (·.semantics.length > 0) = true := by
  native_decide

/-- No classifier is mensural (all are sortal in this fragment). -/
theorem all_sortal :
    allClassifiers.all (!·.isMensural) = true := by native_decide

end Fragments.Mandarin.Classifiers
