import Linglib.Core.Lexical.NounCategorization

/-!
# Japanese Classifier Lexicon
@cite{aikhenvald-2000} @cite{downing-1996}

Typed classifier entries for Japanese (josūshi 助数詞).

Japanese numeral classifiers are suffixed to the numeral (e.g. san-biki
三匹 "three-CL:small.animal"). Selection is semantically motivated,
encoding animacy, shape (with 1D/2D/3D dimensionality), and function.

The inventory covers all 27 classifiers from @cite{downing-1996} Table 1.1
(Core Inventory), plus selected classifiers from Table 1.2 (Extended
Inventory): 竿 sao, 羽 wa, 振 furi, 膳 zen, 脚 kyaku, 杯 hai. Shape-based
classifiers are tagged by dimensionality per Ch. 5's analysis.

-/

namespace Fragments.Japanese.Classifiers

open Core.NounCategorization (ClassifierEntry SemanticParameter ShapeDimension)

-- ============================================================================
-- Sortal classifiers — animacy
-- ============================================================================

/-- 人 nin — people (neutral register).
    Encodes: humanness. -/
def nin : ClassifierEntry :=
  { form := "人", gloss := "person"
  , semantics := [.humanness] }

/-- 名 mei — people (formal/honorific register).
    Encodes: humanness + social status. -/
def mei : ClassifierEntry :=
  { form := "名", gloss := "person.HON"
  , semantics := [.humanness, .socialStatus] }

/-- 匹 hiki — small/medium animals (dogs, cats, insects, fish).
    Encodes: animacy + size. -/
def hiki : ClassifierEntry :=
  { form := "匹", gloss := "small.animal"
  , semantics := [.animacy, .size] }

/-- 頭 tou — large animals (horses, cattle, elephants).
    Encodes: animacy + large size. -/
def tou : ClassifierEntry :=
  { form := "頭", gloss := "large.animal"
  , semantics := [.animacy, .size] }

/-- 羽 wa — birds (and rabbits, by cultural extension).
    Encodes: animacy (avian).
    Extended inventory (@cite{downing-1996} Table 1.2). -/
def wa : ClassifierEntry :=
  { form := "羽", gloss := "bird"
  , semantics := [.animacy] }

-- ============================================================================
-- Sortal classifiers — shape (with dimensionality)
-- ============================================================================

/-- 本 hon' — long, thin objects (pens, bottles, flowers, umbrellas);
    also items following a trajectory (TV programs, telephone calls).
    Encodes: shape (1D, elongated). -/
def hon' : ClassifierEntry :=
  { form := "本", gloss := "long.thin"
  , semantics := [.shape], shapeDimension := some .oneD }

/-- 枚 mai — flat, thin objects (paper, stamps, plates, shirts).
    Encodes: shape (2D, flat). -/
def mai : ClassifierEntry :=
  { form := "枚", gloss := "flat.thin"
  , semantics := [.shape], shapeDimension := some .twoD }

/-- 個 ko — small, round/compact objects (eggs, apples, stones).
    General inanimate classifier for some speakers.
    Encodes: shape (3D, compact). -/
def ko : ClassifierEntry :=
  { form := "個", gloss := "small.round"
  , semantics := [.shape], shapeDimension := some .threeD }

/-- 竿 sao — poles, long rod-like objects.
    Encodes: shape (1D, rigid pole).
    Extended inventory (@cite{downing-1996} Table 1.2). -/
def sao : ClassifierEntry :=
  { form := "竿", gloss := "pole"
  , semantics := [.shape], shapeDimension := some .oneD }

/-- 冊 satsu — bound volumes (books, magazines).
    Encodes: shape (2D, flat bound). -/
def satsu : ClassifierEntry :=
  { form := "冊", gloss := "bound.volume"
  , semantics := [.shape], shapeDimension := some .twoD }

/-- 粒 tsubu — small, grainlike objects (grains of rice, grapes, gems,
    pills, drops of liquid).
    Encodes: shape (3D, granular). -/
def tsubu : ClassifierEntry :=
  { form := "粒", gloss := "grain"
  , semantics := [.shape], shapeDimension := some .threeD }

-- ============================================================================
-- Sortal classifiers — function
-- ============================================================================

/-- 台 dai — furniture, machines, land and air vehicles.
    Encodes: function (mechanical/vehicular). -/
def dai : ClassifierEntry :=
  { form := "台", gloss := "machine/vehicle"
  , semantics := [.function] }

/-- 軒 ken — buildings or parts of buildings acting in some functional
    capacity, such as a home or shop.
    Encodes: function (shelter/structure). -/
def ken : ClassifierEntry :=
  { form := "軒", gloss := "building"
  , semantics := [.function] }

/-- 件 ken' — incidents, occurrences (robberies, fires, accidents).
    Encodes: function (event/incident).
    Note: homophonous with 軒 ken (buildings) but distinct kanji. -/
def ken' : ClassifierEntry :=
  { form := "件", gloss := "incident"
  , semantics := [.function] }

/-- 機 ki — airplanes (other air vehicles such as helicopters, rockets, UFOs).
    Encodes: function (powered flight/engine). -/
def ki : ClassifierEntry :=
  { form := "機", gloss := "air.vehicle"
  , semantics := [.function] }

/-- 句 ku — haiku (17-syllable poems), other short poems.
    Encodes: function (poetic form). -/
def ku : ClassifierEntry :=
  { form := "句", gloss := "poem"
  , semantics := [.function] }

/-- 曲 kyoku — pieces of music.
    Encodes: function (musical work). -/
def kyoku : ClassifierEntry :=
  { form := "曲", gloss := "music.piece"
  , semantics := [.function] }

/-- 問 mon — questions, problems.
    Encodes: function (intellectual item). -/
def mon : ClassifierEntry :=
  { form := "問", gloss := "question"
  , semantics := [.function] }

/-- 棟 mune — buildings (whole structures with roofs).
    Encodes: function (roofed structure).
    Note: overlaps with 軒 ken (buildings as functional spaces). -/
def mune : ClassifierEntry :=
  { form := "棟", gloss := "building.roof"
  , semantics := [.function] }

/-- 隻 seki — large boats, ships.
    Encodes: function (large maritime vessel). -/
def seki : ClassifierEntry :=
  { form := "隻", gloss := "large.boat"
  , semantics := [.function] }

/-- 足 soku — pairs of footwear (shoes, socks, boots).
    Encodes: function (worn on feet). -/
def soku : ClassifierEntry :=
  { form := "足", gloss := "footwear.pair"
  , semantics := [.function] }

/-- 艘 soo — small boats.
    Encodes: function (small maritime vessel). -/
def soo : ClassifierEntry :=
  { form := "艘", gloss := "small.boat"
  , semantics := [.function] }

/-- 点 ten — points in a score, items in an inventory, works of art.
    Encodes: function (scoring/inventory/art). -/
def ten : ClassifierEntry :=
  { form := "点", gloss := "point/item"
  , semantics := [.function] }

/-- 通り toori — methods, opinions, ways.
    Encodes: function (abstract method/manner). -/
def toori : ClassifierEntry :=
  { form := "通り", gloss := "method/way"
  , semantics := [.function] }

/-- 通 tsuu — letters, postcards, documents; telephone calls.
    Encodes: function (passed/transmitted). -/
def tsuu : ClassifierEntry :=
  { form := "通", gloss := "letter/document"
  , semantics := [.function] }

/-- 振 furi — swords, bladed weapons.
    Encodes: function (swung/shaken).
    Extended inventory (@cite{downing-1996} Table 1.2). -/
def furi : ClassifierEntry :=
  { form := "振", gloss := "sword"
  , semantics := [.function] }

/-- 膳 zen — trays, pairs of chopsticks.
    Encodes: function (meal service).
    Extended inventory (@cite{downing-1996} Table 1.2). -/
def zen : ClassifierEntry :=
  { form := "膳", gloss := "tray/chopsticks"
  , semantics := [.function] }

/-- 脚 kyaku — legged furniture (chairs, desks, tables).
    Encodes: function (legged).
    Extended inventory (@cite{downing-1996} Table 1.2). -/
def kyaku : ClassifierEntry :=
  { form := "脚", gloss := "legged.furniture"
  , semantics := [.function] }

/-- 株 kabu — rooted plants, roots, bulbs; shares of stock.
    Encodes: function (rooted/planted). -/
def kabu : ClassifierEntry :=
  { form := "株", gloss := "rooted.plant"
  , semantics := [.function] }

-- ============================================================================
-- Default and mensural
-- ============================================================================

/-- つ tsu — general/default counter (native Japanese numerals).
    Semantically bleached default. -/
def tsu : ClassifierEntry :=
  { form := "つ", gloss := "general", isDefault := true }

/-- 杯 hai — cupfuls, glassfuls (mensural).
    Measures quantity by container volume.
    Extended inventory (@cite{downing-1996} Table 1.2). -/
def hai : ClassifierEntry :=
  { form := "杯", gloss := "cupful"
  , semantics := [.quanta], isMensural := true }

/-- 食 shoku — meals, servings of food (mensural).
    Measures quantity by meal portions. -/
def shoku : ClassifierEntry :=
  { form := "食", gloss := "meal"
  , semantics := [.quanta], isMensural := true }

/-- 滴 teki — drops of liquid (mensural).
    Measures quantity by drops. -/
def teki : ClassifierEntry :=
  { form := "滴", gloss := "drop"
  , semantics := [.quanta], isMensural := true }

-- ============================================================================
-- Inventory
-- ============================================================================

/-- Complete inventory: 27 core classifiers (@cite{downing-1996} Table 1.1)
    + 6 extended classifiers (Table 1.2: sao, wa, furi, zen, kyaku, hai). -/
def allClassifiers : List ClassifierEntry :=
  -- Core (Table 1.1)
  [ tsu, nin, mei, hiki, tou
  , hon', mai, ko, satsu, tsubu
  , dai, ken, ken', ki, ku, kyoku, mon, mune
  , seki, soku, soo, ten, toori, tsuu
  , kabu, shoku, teki
  -- Extended (Table 1.2)
  , sao, wa, furi, zen, kyaku, hai ]

/-- The 27 core classifiers from @cite{downing-1996} Table 1.1. -/
def coreClassifiers : List ClassifierEntry :=
  [ tsu, nin, mei, hiki, tou
  , hon', mai, ko, satsu, tsubu
  , dai, ken, ken', ki, ku, kyoku, mon, mune
  , seki, soku, soo, ten, toori, tsuu
  , kabu, shoku, teki ]

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

/-- 名 encodes humanness and social status. -/
theorem mei_encodes_honorific :
    mei.encodes .humanness = true ∧ mei.encodes .socialStatus = true := by
  constructor <;> native_decide

/-- Shape-based classifiers carry dimensionality tags. -/
theorem hon_is_1D : hon'.shapeDimension = some .oneD := rfl
theorem mai_is_2D : mai.shapeDimension = some .twoD := rfl
theorem ko_is_3D : ko.shapeDimension = some .threeD := rfl
theorem tsubu_is_3D : tsubu.shapeDimension = some .threeD := rfl

/-- All three shape dimensions are attested in the inventory. -/
theorem all_dimensions_attested :
    allClassifiers.any (·.shapeDimension == some .oneD) = true ∧
    allClassifiers.any (·.shapeDimension == some .twoD) = true ∧
    allClassifiers.any (·.shapeDimension == some .threeD) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- 杯 is mensural; all other classifiers are sortal. -/
theorem hai_is_mensural : hai.isMensural = true := rfl

/-- The core inventory has exactly 27 classifiers. -/
theorem core_inventory_size : coreClassifiers.length = 27 := by native_decide

/-- The full inventory has 33 classifiers (27 core + 6 extended). -/
theorem full_inventory_size : allClassifiers.length = 33 := by native_decide

theorem sortal_majority :
    (allClassifiers.filter (!·.isMensural)).length = 30 := by native_decide

/-- All non-default sortal classifiers have at least one semantic parameter. -/
theorem specific_classifiers_have_semantics :
    (allClassifiers.filter (λ c => !c.isDefault && !c.isMensural)).all
      (·.semantics.length > 0) = true := by
  native_decide

/-- 件 ken' (incidents) and 軒 ken (buildings) are distinct classifiers
    sharing the same romanization but different kanji forms. -/
theorem ken_ken'_distinct : ken.form ≠ ken'.form := by native_decide

end Fragments.Japanese.Classifiers
