import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Linglib.Syntax.Category.Classifier.Basic

/-!
# Japanese Numeral Classifier Inventory
[aikhenvald-2000] [downing-1996] [sudo-2016]

The closed inventory of Japanese numeral classifiers (josūshi 助数詞) as a
finite inductive type. Properties (form, gloss, encoded semantic
parameters, dimensionality, mensural-vs-sortal, default flag) are
projection functions or `Decidable` predicates over the type, not fields
on a struct.

## Inventory provenance

- 27 core entries from [downing-1996] (UNVERIFIED: claimed to be
  Table 1.1 by the prior fragment file; cited tables/page numbers not
  cross-checked against the monograph).
- 6 extended entries from [downing-1996] (UNVERIFIED: claimed to be
  Table 1.2; same caveat).
- 3 additional entries (`rin`, `kumi`, `daasu`) from [sudo-2016]
  worked examples (eq. 4 for `-rin`, eq. 9a for `-kumi`, eq. 9b for
  `-daasu` — verified against the PDF).

## Out of scope

- Phonological allomorphy (rendaku/sokuon: ippon/sanbon/roppon for
  `-hon`, ippiki/sanbiki/roppiki for `-hiki`) — would belong with
  `Phonology/`.
- Native vs Sino-Japanese numeral series split (`tsu` selects native
  hitotsu/futatsu/...; Sino-classifiers select ichi/ni/san/...).
- Inventory expansion to high-frequency classifiers not in Downing's
  inventory (`-kai` 回, `-bai` 倍, `-ban` 番, `-do` 度, etc.).

The typological parameters follow [downing-1996] and [aikhenvald-2000]: numeral classifiers
suffixed to numerals, chosen on semantic grounds, with *tsu* as the general classifier; the
semantic parameters and the general classifier are read off the inventory.
-/

namespace Japanese

/-- The closed inventory of Japanese numeral classifiers. Constructors are
    named by Hepburn romanization, with kanji-distinct homophones
    disambiguated by content (e.g., `kenBuilding` 軒 vs `kenIncident` 件). -/
inductive Classifier where
  -- Downing 1996 core inventory — animacy
  | tsu | nin | mei | hiki | tou
  -- core — shape
  | hon | mai | ko | satsu | tsubu
  -- core — function
  | dai | kenBuilding | kenIncident | ki | ku | kyoku | mon | mune
  | seki | soku | soo | ten | toori | tsuu | kabu | shoku | teki
  -- Downing 1996 extended inventory
  | sao | wa | furi | zen | kyaku | hai
  -- Sudo 2016 worked examples (eqs. 4, 9a, 9b)
  | rin | kumi | daasu
  deriving DecidableEq, Repr, BEq

namespace Classifier

/-- The 27 core classifiers from [downing-1996] (UNVERIFIED: Table 1.1). -/
def core : List Classifier :=
  [.tsu, .nin, .mei, .hiki, .tou,
   .hon, .mai, .ko, .satsu, .tsubu,
   .dai, .kenBuilding, .kenIncident, .ki, .ku, .kyoku, .mon, .mune,
   .seki, .soku, .soo, .ten, .toori, .tsuu, .kabu, .shoku, .teki]

/-- The 6 extended classifiers from [downing-1996] (UNVERIFIED: Table 1.2). -/
def extended : List Classifier :=
  [.sao, .wa, .furi, .zen, .kyaku, .hai]

/-- The 3 additional classifiers from [sudo-2016]'s worked examples
    (eqs. 4, 9a, 9b): `-rin` (flowers), `-kumi` (pair), `-daasu` (dozen). -/
def sudoAdditions : List Classifier :=
  [.rin, .kumi, .daasu]

/-- The full inventory: Downing core ++ Downing extended ++ Sudo additions.
    Source-of-truth for consumer iteration (lookup, aggregations) and the
    `Fintype` instance. -/
def all : List Classifier := core ++ extended ++ sudoAdditions

theorem all_nodup : all.Nodup := by decide

theorem mem_all (c : Classifier) : c ∈ all := by cases c <;> simp [all, core, extended, sudoAdditions]

end Classifier

instance : Fintype Classifier where
  elems := Classifier.all.toFinset
  complete c := List.mem_toFinset.mpr (Classifier.mem_all c)

namespace Classifier

/-! ## §1: Surface form -/

/-- The kanji (or hiragana, for `-tsu`) form of the classifier. -/
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

/-- Hepburn romanization of the classifier. -/
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

/-- A short English gloss describing the classifier's selection criterion. -/
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

/-! ## §2: Semantic parameters and shape -/

/-- The semantic parameters this classifier encodes
    ([aikhenvald-2000] typological vocabulary).

    Every constructor has an explicit arm; no fall-through. Adding a
    classifier requires deciding what it encodes — the type checker
    enforces it. -/
def encodes : Classifier → List Classifier.Parameter
  -- animacy
  | .tsu => []
  | .nin => [.humanness]
  | .mei => [.humanness, .register]
  | .hiki => [.animacy, .size]
  | .tou => [.animacy, .size]
  | .wa => [.animacy]
  -- shape
  | .hon => [.shape]
  | .mai => [.shape]
  | .ko => [.shape]
  | .satsu => [.shape]
  | .tsubu => [.shape]
  | .sao => [.shape]
  | .rin => [.shape, .boundedness]
  -- function
  | .dai => [.function]
  | .kenBuilding => [.function]
  | .kenIncident => [.function]
  | .ki => [.function]
  | .ku => [.function]
  | .kyoku => [.function]
  | .mon => [.function]
  | .mune => [.function]
  | .seki => [.function]
  | .soku => [.function, .arrangement]
  | .soo => [.function]
  | .ten => [.function]
  | .toori => [.function]
  | .tsuu => [.function]
  | .kabu => [.function]
  | .furi => [.function]
  | .zen => [.function]
  | .kyaku => [.function]
  -- mensural
  | .hai => [.quanta]
  | .shoku => [.quanta]
  | .teki => [.quanta]
  | .daasu => [.quanta]
  -- arrangement
  | .kumi => [.arrangement, .quanta]

/-- Shape dimensionality sub-classification per [allan-1977]'s
    1D/2D/3D scheme (cf. [downing-1996]). Only meaningful when
    `encodes` includes `.shape`.

    `-rin` 輪 is left as `none`: although it encodes shape, it tracks
    boundedness/ring-form (wheels, single blossoms) rather than fitting
    cleanly on the 1D/2D/3D axis. See `encodes`, where `-rin` carries
    `.shape` and `.boundedness`. -/
def shapeDim : Classifier → Option Classifier.Dimension
  | .hon => some .oneD
  | .sao => some .oneD
  | .mai => some .twoD
  | .satsu => some .twoD
  | .ko => some .threeD
  | .tsubu => some .threeD
  | _ => none

/-! ## §3: Property predicates -/

/-- A classifier is *mensural* if it counts entities by a measure
    (containers, portions, drops, fixed-quantity multiples) rather than
    by atomic instances. `-daasu` ダース (← English "dozen") is mensural
    since it counts in fixed groups of 12. -/
def IsMensural (c : Classifier) : Prop :=
  c = .hai ∨ c = .shoku ∨ c = .teki ∨ c = .daasu

instance : DecidablePred IsMensural := fun c =>
  inferInstanceAs (Decidable (c = .hai ∨ c = .shoku ∨ c = .teki ∨ c = .daasu))

/-- A classifier is the *default* (semantically bleached, residue) classifier
    of the language. Japanese: `tsu`. -/
def IsDefault (c : Classifier) : Prop := c = .tsu

instance : DecidablePred IsDefault := fun c =>
  inferInstanceAs (Decidable (c = .tsu))

/-- `c` encodes the semantic parameter `p` iff `p ∈ c.encodes`. -/
def Encodes (c : Classifier) (p : Classifier.Parameter) : Prop := p ∈ c.encodes

instance (c : Classifier) (p : Classifier.Parameter) : Decidable (Encodes c p) :=
  inferInstanceAs (Decidable (p ∈ c.encodes))

/-! ## §4: Lookup and aggregations -/

/-- The default classifier of Japanese, derived from `IsDefault`. -/
def defaultClassifier? : Option Classifier :=
  all.find? fun c => decide (IsDefault c)

/-- Lookup a classifier by surface form. Returns `none` if the form is not
    in the inventory. -/
def lookup (s : String) : Option Classifier :=
  all.find? fun c => c.form = s

/-- The list of all semantic parameters encoded by some classifier in the
    inventory (with duplicates removed), the system's `classifierSemantics`. -/
def allEncodedParams : List Classifier.Parameter :=
  (all.flatMap encodes).eraseDups

/-! ## §6: Structural theorems -/

/-- The inventory has 36 classifiers (27 Downing core + 6 Downing extended +
    3 Sudo examples). -/
theorem inventory_size : all.length = 36 := by decide

/-- The default classifier exists and is `tsu`. -/
theorem default_eq_tsu : defaultClassifier? = some .tsu := by decide

/-- `tsu` is the only classifier flagged as default. -/
theorem isDefault_iff_tsu (c : Classifier) : IsDefault c ↔ c = .tsu := Iff.rfl

/-- Exactly four classifiers are mensural: `hai`, `shoku`, `teki`, `daasu`. -/
theorem mensural_count :
    (all.filter (fun c => decide (IsMensural c))).length = 4 := by decide

/-- Every non-default sortal classifier encodes at least one semantic parameter.
    The default `tsu` is the only semantically empty classifier. -/
theorem specific_classifiers_have_semantics :
    ∀ c : Classifier, ¬IsDefault c → ¬IsMensural c → c.encodes ≠ [] := by
  decide

/-- All three shape dimensions are attested in the inventory. -/
theorem all_dimensions_attested :
    (∃ c : Classifier, shapeDim c = some .oneD) ∧
    (∃ c : Classifier, shapeDim c = some .twoD) ∧
    (∃ c : Classifier, shapeDim c = some .threeD) :=
  ⟨⟨Classifier.hon, rfl⟩, ⟨Classifier.mai, rfl⟩, ⟨Classifier.ko, rfl⟩⟩

/-- 軒 `kenBuilding` and 件 `kenIncident` are distinct classifiers sharing
    the same Hepburn romanization but differing in kanji form. -/
theorem ken_disambiguation : kenBuilding.form ≠ kenIncident.form := by decide

/-- 軒 and 件 share their romanization (the homophony Downing flags). -/
theorem ken_homophony : kenBuilding.romaji = kenIncident.romaji := rfl

end Classifier

end Japanese

/-! ### Typological parameters -/

namespace Japanese

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
