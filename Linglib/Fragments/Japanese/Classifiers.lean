import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Category.Classifier.Basic

/-!
# Japanese numeral classifiers

Japanese counts with a classifier suffixed to the numeral and chosen by the semantics of the
noun: *-nin* for people, *-hiki* for small animals, *-hon* for long thin things, *-mai* for
flat ones, *-satsu* for bound volumes, and the general *-tsu*, which encodes nothing. Downing's
questionnaire gives the inventory: the twenty-seven classifiers every respondent used and six
more that a majority used, to which the textbook counter of cupfuls *-hai* and Sudo's
non-atomic *-kumi* 'pair' and *-daasu* 'dozen' are added, though Downing's definition sets
groupings, measures and containers aside. The typological parameters of Aikhenvald are read off
the inventory. Allomorphy (*ippon*, *sanbon*, *roppon*) and the native and Sino-Japanese
numeral series are not recorded.

## Main definitions

* `Japanese.Classifier` — the inventory, with `form`, `romaji`, `gloss`, the semantic
  parameters `encodes` and the shape dimension `shapeDim`
* `Japanese.Classifier.IsDefault`, `Japanese.Classifier.IsMensural` — the general classifier,
  which encodes no parameter, and the measure classifiers

## Main results

* `Japanese.Classifier.isDefault_iff` — *-tsu* is the one general classifier

## References

* [aikhenvald-2000]
* [allan-1977]
* [downing-1996]
* [sudo-2016]
-/

namespace Japanese

/-- The Japanese numeral classifiers, named by their romanization, the two *ken* told apart by
their kanji. -/
inductive Classifier where
  | tsu | nin | mei | hiki | tou
  | hon | mai | ko | satsu | tsubu
  | dai | kenBuilding | kenIncident | ki | ku | kyoku | mon | mune
  | seki | soku | soo | ten | toori | tsuu | kabu | shoku | teki
  | sao | wa | furi | zen | kyaku | rin
  | hai | kumi | daasu
  deriving DecidableEq, Repr, Fintype

namespace Classifier

/-- The twenty-seven classifiers every respondent of Downing's questionnaire used. -/
def core : List Classifier :=
  [.tsu, .nin, .mei, .hiki, .tou,
   .hon, .mai, .ko, .satsu, .tsubu,
   .dai, .kenBuilding, .kenIncident, .ki, .ku, .kyoku, .mon, .mune,
   .seki, .soku, .soo, .ten, .toori, .tsuu, .kabu, .shoku, .teki]

/-- The six further classifiers a majority of Downing's respondents used. -/
def extended : List Classifier := [.sao, .wa, .furi, .zen, .kyaku, .rin]

/-- The counters outside Downing's definition: *-hai*, and Sudo's *-kumi* and *-daasu*. -/
def additions : List Classifier := [.hai, .kumi, .daasu]

/-- The inventory in order of provenance. -/
def all : List Classifier := core ++ extended ++ additions

/-- The three provenance lists partition the inventory. -/
theorem mem_all (c : Classifier) : c ∈ all := by cases c <;> simp [all, core, extended, additions]

/-- The kanji, or kana for *-tsu*. -/
def form : Classifier → String
  | .tsu => "つ"
  | .nin => "人" | .mei => "名" | .hiki => "匹" | .tou => "頭"
  | .hon => "本" | .mai => "枚" | .ko => "個" | .satsu => "冊" | .tsubu => "粒"
  | .dai => "台" | .kenBuilding => "軒" | .kenIncident => "件"
  | .ki => "機" | .ku => "句" | .kyoku => "曲" | .mon => "問" | .mune => "棟"
  | .seki => "隻" | .soku => "足" | .soo => "艘" | .ten => "点"
  | .toori => "通り" | .tsuu => "通"
  | .kabu => "株" | .shoku => "食" | .teki => "滴"
  | .sao => "竿" | .wa => "羽" | .furi => "振" | .zen => "膳" | .kyaku => "脚"
  | .hai => "杯"
  | .rin => "輪" | .kumi => "組" | .daasu => "ダース"

/-- The romanization. -/
def romaji : Classifier → String
  | .tsu => "tsu"
  | .nin => "nin" | .mei => "mei" | .hiki => "hiki" | .tou => "tou"
  | .hon => "hon" | .mai => "mai" | .ko => "ko" | .satsu => "satsu" | .tsubu => "tsubu"
  | .dai => "dai" | .kenBuilding => "ken" | .kenIncident => "ken"
  | .ki => "ki" | .ku => "ku" | .kyoku => "kyoku" | .mon => "mon" | .mune => "mune"
  | .seki => "seki" | .soku => "soku" | .soo => "soo" | .ten => "ten"
  | .toori => "toori" | .tsuu => "tsuu"
  | .kabu => "kabu" | .shoku => "shoku" | .teki => "teki"
  | .sao => "sao" | .wa => "wa" | .furi => "furi" | .zen => "zen" | .kyaku => "kyaku"
  | .hai => "hai"
  | .rin => "rin" | .kumi => "kumi" | .daasu => "daasu"

/-- What the classifier selects for. -/
def gloss : Classifier → String
  | .tsu => "general"
  | .nin => "person" | .mei => "person.formal" | .hiki => "small.animal" | .tou => "large.animal"
  | .hon => "long.thin" | .mai => "flat.thin" | .ko => "small.round"
  | .satsu => "bound.volume" | .tsubu => "grain"
  | .dai => "machine/vehicle" | .kenBuilding => "building" | .kenIncident => "incident"
  | .ki => "air.vehicle" | .ku => "poem" | .kyoku => "music.piece"
  | .mon => "question" | .mune => "building.roof"
  | .seki => "large.boat" | .soku => "footwear.pair" | .soo => "small.boat"
  | .ten => "point/item" | .toori => "method/way" | .tsuu => "letter/document"
  | .kabu => "rooted.plant" | .shoku => "meal" | .teki => "drop"
  | .sao => "pole" | .wa => "bird" | .furi => "sword" | .zen => "tray/chopsticks"
  | .kyaku => "legged.furniture" | .hai => "cupful"
  | .rin => "flower" | .kumi => "pair/group" | .daasu => "dozen"

/-- The semantic parameters the classifier encodes, in Aikhenvald's vocabulary. -/
def encodes : Classifier → List Classifier.Parameter
  | .tsu => []
  | .nin => [.humanness]
  | .mei => [.humanness, .register]
  | .hiki => [.animacy, .size]
  | .tou => [.animacy, .size]
  | .wa => [.animacy]
  | .hon => [.shape]
  | .mai => [.shape]
  | .ko => [.shape]
  | .satsu => [.shape]
  | .tsubu => [.shape]
  | .sao => [.shape]
  | .rin => [.shape, .boundedness]
  | .dai => [.function]
  | .kenBuilding => [.function]
  | .kenIncident => [.function]
  | .ki => [.function]
  | .ku => [.function]
  | .kyoku => [.function]
  | .mon => [.function]
  | .mune => [.function]
  | .seki => [.function, .size]
  | .soku => [.function, .arrangement]
  | .soo => [.function, .size]
  | .ten => [.function]
  | .toori => [.function]
  | .tsuu => [.function]
  | .kabu => [.function]
  | .furi => [.function]
  | .zen => [.function]
  | .kyaku => [.function]
  | .hai => [.quanta]
  | .shoku => [.quanta]
  | .teki => [.quanta]
  | .daasu => [.quanta]
  | .kumi => [.arrangement, .quanta]

/-- The dimensionality of a shape classifier in Allan's scheme; *-rin*, which selects for the
ring shape of wheels and blossoms, has none. -/
def shapeDim : Classifier → Option Classifier.Dimension
  | .hon => some .oneD
  | .sao => some .oneD
  | .mai => some .twoD
  | .satsu => some .twoD
  | .ko => some .threeD
  | .tsubu => some .threeD
  | _ => none

/-- The general classifier encodes no parameter. -/
def IsDefault (c : Classifier) : Prop := c.encodes = []

instance : DecidablePred IsDefault := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- *-tsu* is the one general classifier. -/
theorem isDefault_iff (c : Classifier) : IsDefault c ↔ c = .tsu := by cases c <;> decide

/-- A measure classifier counts by cupfuls, portions, drops or dozens rather than by
individuals. -/
def IsMensural (c : Classifier) : Prop := c = .hai ∨ c = .shoku ∨ c = .teki ∨ c = .daasu

instance : DecidablePred IsMensural := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- The classifier encodes the parameter. -/
def Encodes (c : Classifier) (p : Classifier.Parameter) : Prop := p ∈ c.encodes

instance (c : Classifier) (p : Classifier.Parameter) : Decidable (Encodes c p) :=
  inferInstanceAs (Decidable (p ∈ c.encodes))

/-- The general classifier. -/
def defaultClassifier? : Option Classifier := all.find? fun c ↦ decide (IsDefault c)

/-- The parameters some classifier encodes. -/
def allEncodedParams : List Classifier.Parameter := (all.flatMap encodes).eraseDups

end Classifier

/-! ### Aikhenvald's parameters -/

/-- Classifiers occur in the numeral phrase and characterize the head noun. -/
def classifierLocus : Classifier.Scope := .numeralNP

def classifierConstituent : Classifier.Constituent := .headNoun

/-- The kind of device, read off its locus and the constituent it characterizes. -/
abbrev classifierKind : Option Classifier.Kind :=
  Classifier.kind classifierLocus classifierConstituent

/-- Every environment the device operates in. -/
def classifierScopes : List Classifier.Scope := [.numeralNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : Classifier.Assignment := .semantic

/-- Suffixes on numerals. -/
def classifierRealizations : List Classifier.Realization := [.suffix]

def classifierAgreement : Bool := false

def classifierObligatory : Bool := true

/-- Whether the inventory has a general classifier. -/
def classifierDefault : Bool := Classifier.defaultClassifier?.isSome

def classifierSemantics : List Classifier.Parameter := Classifier.allEncodedParams

def obligatoryNumber : Bool := false

end Japanese
