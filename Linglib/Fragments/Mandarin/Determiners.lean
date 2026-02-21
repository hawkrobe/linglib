import Linglib.Core.Word
import Linglib.Core.NounCategorization
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.Mandarin.Classifiers

/-! # Mandarin Chinese Quantifier Fragment

Mandarin has no articles. Quantification is expressed through:
- Pre-nominal quantifiers: měi 每 (every), suǒyǒu 所有 (all), yǒu-de 有的 (some)
- Bare nouns in argument position (generic/existential/universal by context)
- Classifiers required for counting: sān-gè xuéshēng 三个学生 (three-CL students)

Key typological properties:
- No definiteness-marked quantifiers (no "the")
- Conservativity expected to hold (universal)
- měi requires classifiers; suǒyǒu does not
- yǒu-de is proportional-weak, not pure existential

## References
- Li, Y.-H. A. (1998). Argument determiner phrases and number phrases.
- Cheng, L. L.-S. & Sybesma, R. (1999). Bare and not-so-bare nouns.
-/

namespace Fragments.Mandarin.Determiners

open Fragments.English.Determiners (QForce Monotonicity Strength)
open Core.NounCategorization (ClassifierEntry)
open Fragments.Mandarin.Classifiers (ge)

/-- Mandarin quantifier entry. Extends the English pattern with
    classifier requirements (Mandarin-specific morphosyntax). -/
structure MandarinQuantEntry where
  /-- Hànzì form -/
  hanzi : String
  /-- Pīnyīn romanization -/
  pinyin : String
  /-- English gloss -/
  gloss : String
  /-- Quantificational force -/
  qforce : QForce
  /-- Monotonicity -/
  monotonicity : Monotonicity := .increasing
  /-- Weak/strong (there-insertion diagnostic adapted to existential yǒu 有) -/
  strength : Strength := .weak
  /-- Requires a classifier (liàngcí 量词) between determiner and noun -/
  requiresClassifier : Bool := false
  /-- Typical classifier used with this quantifier (个 gè by default) -/
  typicalClassifier : Option ClassifierEntry := none
  deriving Repr, BEq

-- ============================================================================
-- Entries
-- ============================================================================

/-- 每 měi "every" — universal, singular-like, requires classifier.
    měi-gè xuéshēng 每个学生 "every-CL student" -/
def mei : MandarinQuantEntry :=
  { hanzi := "每"
  , pinyin := "měi"
  , gloss := "every"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , requiresClassifier := true
  , typicalClassifier := some ge }

/-- 所有 suǒyǒu "all" — universal, plural-like, no classifier required.
    suǒyǒu xuéshēng 所有学生 "all students" -/
def suoyou : MandarinQuantEntry :=
  { hanzi := "所有"
  , pinyin := "suǒyǒu"
  , gloss := "all"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong }

/-- 有的 yǒu-de "some" — proportional-weak, increasing.
    yǒu-de xuéshēng 有的学生 "some students" -/
def youde : MandarinQuantEntry :=
  { hanzi := "有的"
  , pinyin := "yǒu-de"
  , gloss := "some"
  , qforce := .existential
  , monotonicity := .increasing
  , strength := .weak }

/-- 没有 méi-yǒu "no/not-have" — negative, decreasing, weak.
    méi-yǒu xuéshēng 没有学生 "no students" -/
def meiyou : MandarinQuantEntry :=
  { hanzi := "没有"
  , pinyin := "méi-yǒu"
  , gloss := "no"
  , qforce := .negative
  , monotonicity := .decreasing
  , strength := .weak }

/-- 几 jǐ "several/how-many" — existential, increasing, requires classifier.
    jǐ-gè xuéshēng 几个学生 "several-CL students" -/
def ji : MandarinQuantEntry :=
  { hanzi := "几"
  , pinyin := "jǐ"
  , gloss := "several"
  , qforce := .existential
  , monotonicity := .increasing
  , strength := .weak
  , requiresClassifier := true
  , typicalClassifier := some ge }

/-- 大部分 dà-bùfèn "most/the greater part" — proportional, increasing, strong.
    dà-bùfèn xuéshēng 大部分学生 "most students" -/
def dabufen : MandarinQuantEntry :=
  { hanzi := "大部分"
  , pinyin := "dà-bùfèn"
  , gloss := "most"
  , qforce := .proportional
  , monotonicity := .increasing
  , strength := .strong }

/-- 两个都 liǎng-gè-dōu "both" — universal dual, strong.
    两个学生都来了 liǎng-gè xuéshēng dōu lái le "both students came".
    Requires classifier 个; 都 dōu is the universal adverb.
    Presupposes exactly two referents.
    K&S: both = every restricted to dual sets. -/
def liang_dou : MandarinQuantEntry :=
  { hanzi := "两…都"
  , pinyin := "liǎng…dōu"
  , gloss := "both"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong
  , requiresClassifier := true
  , typicalClassifier := some ge }

-- ============================================================================
-- Lexicon
-- ============================================================================

def allQuantifiers : List MandarinQuantEntry :=
  [mei, suoyou, youde, meiyou, ji, dabufen, liang_dou]

def lookup (pinyin : String) : Option MandarinQuantEntry :=
  allQuantifiers.find? λ e => e.pinyin == pinyin

-- ============================================================================
-- Verification
-- ============================================================================

/-- měi is strong (no existential yǒu sentence). -/
theorem mei_strong : mei.strength = .strong := rfl

/-- yǒu-de is weak (OK in existential yǒu sentence). -/
theorem youde_weak : youde.strength = .weak := rfl

/-- měi requires a classifier. -/
theorem mei_requires_cl : mei.requiresClassifier = true := rfl

/-- suǒyǒu does not require a classifier. -/
theorem suoyou_no_cl : suoyou.requiresClassifier = false := rfl

/-- 两…都 is universal and strong (like English "both"). -/
theorem liang_dou_universal_strong :
    liang_dou.qforce = .universal ∧ liang_dou.strength = .strong :=
  ⟨rfl, rfl⟩

/-- 两…都 requires a classifier. -/
theorem liang_dou_requires_cl : liang_dou.requiresClassifier = true := rfl

/-- All quantifiers that require a classifier have a typicalClassifier set. -/
theorem requires_cl_has_typical :
    (allQuantifiers.filter (·.requiresClassifier)).all
      (·.typicalClassifier.isSome) = true := by native_decide

/-- All typical classifiers are 个 (the default). -/
theorem typical_classifier_is_default :
    (allQuantifiers.filterMap (·.typicalClassifier)).all
      (·.isDefault) = true := by native_decide

end Fragments.Mandarin.Determiners
