import Linglib.Core.Lexical.Word
import Linglib.Core.Lexical.NounCategorization
import Linglib.Fragments.English.Determiners
import Linglib.Fragments.Mandarin.Classifiers

/-! # Mandarin Chinese Quantifier Fragment
@cite{kuo-yu-2012} @cite{tsai-2015}

Quantifier phrases in Mandarin, following @cite{kuo-yu-2012}'s GQ-theoretic
inventory (§12.1) and @cite{tsai-2015}'s strong/weak classification (§5.3).

Existential (intersective) quantifiers — weak (@cite{kuo-yu-2012} §12.1.1):
- hěnduō 很多 (many)

Universal (co-intersective) quantifiers — strong (@cite{kuo-yu-2012} §12.1.2):
- měi 每 (every), suǒyǒu 所有 (all), quánbù 全部 (all)

Proportional quantifiers (@cite{kuo-yu-2012} §12.1.5):
- dà-bùfèn 大部分 (most)

Key typological properties:
- No definiteness-marked quantifiers (no "the")
- Conservativity expected to hold (universal)
- měi requires classifiers; suǒyǒu and quánbù do not (@cite{kuo-yu-2012} §12.1.6)

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

/-- 全部 quánbù "all" — universal, increasing, strong.
    quánbù xuéshēng 全部学生 "all students".
    Synonym of suǒyǒu; does not require a classifier. -/
def quanbu : MandarinQuantEntry :=
  { hanzi := "全部"
  , pinyin := "quánbù"
  , gloss := "all"
  , qforce := .universal
  , monotonicity := .increasing
  , strength := .strong }

/-- 很多 hěnduō "many" — existential/proportional, increasing, weak.
    hěnduō xuéshēng 很多学生 "many students".
    Can optionally co-occur with dōu but does not require it. -/
def henduo : MandarinQuantEntry :=
  { hanzi := "很多"
  , pinyin := "hěnduō"
  , gloss := "many"
  , qforce := .existential
  , monotonicity := .increasing
  , strength := .weak }

/-- 大部分 dà-bùfèn "most/the greater part" — proportional, increasing, strong.
    dà-bùfèn xuéshēng 大部分学生 "most students" -/
def dabufen : MandarinQuantEntry :=
  { hanzi := "大部分"
  , pinyin := "dà-bùfèn"
  , gloss := "most"
  , qforce := .proportional
  , monotonicity := .increasing
  , strength := .strong }

-- ============================================================================
-- Lexicon
-- ============================================================================

def allQuantifiers : List MandarinQuantEntry :=
  [mei, suoyou, quanbu, henduo, dabufen]

def lookup (pinyin : String) : Option MandarinQuantEntry :=
  allQuantifiers.find? λ e => e.pinyin == pinyin

-- ============================================================================
-- Verification
-- ============================================================================

/-- měi is strong (no existential yǒu sentence). -/
theorem mei_strong : mei.strength = .strong := rfl

/-- měi requires a classifier. -/
theorem mei_requires_cl : mei.requiresClassifier = true := rfl

/-- suǒyǒu does not require a classifier. -/
theorem suoyou_no_cl : suoyou.requiresClassifier = false := rfl

/-- hěnduō is weak; all others are strong QPs (@cite{tsai-2015} §5.3). -/
theorem henduo_weak : henduo.strength = .weak := rfl

theorem strong_qps_are_strong :
    (allQuantifiers.filter (·.pinyin != "hěnduō")).all
      (·.strength == .strong) = true := by native_decide

/-- All quantifiers that require a classifier have a typicalClassifier set. -/
theorem requires_cl_has_typical :
    (allQuantifiers.filter (·.requiresClassifier)).all
      (·.typicalClassifier.isSome) = true := by native_decide

/-- All typical classifiers are 个 (the default). -/
theorem typical_classifier_is_default :
    (allQuantifiers.filterMap (·.typicalClassifier)).all
      (·.isDefault) = true := by native_decide

end Fragments.Mandarin.Determiners
