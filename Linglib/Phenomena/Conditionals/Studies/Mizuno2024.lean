import Linglib.Theories.Semantics.Conditionals.Anderson
import Linglib.Fragments.Japanese.Conditionals

/-!
# @cite{mizuno-2024} — Crosslinguistic Data @cite{mizuno-2024}

Theory-neutral crosslinguistic data on Anderson conditional strategies from
@cite{mizuno-2024} "Strategies for Anderson Conditionals", *Semantics and @cite{iatridou-2000}
Pragmatics* 17(8): 1–14.

## Key Empirical Generalizations

1. **English requires X-marking**: O-marking (present tense) renders Anderson
   conditionals trivially true (ex. 2–3).
2. **Japanese requires O-marking**: X-marking (Past tense in consequent) yields
   a counterfactual reading, not an Anderson reading (ex. 4b, 5b).
3. **FLV correlation**: Languages that lack X-marking for Anderson conditionals
   also lack X-marking for Future Less Vivid conditionals (§4.2).

## Data Sources

- Examples (1)–(7) of @cite{mizuno-2024}
- Example (13a) for Mandarin
- §4.2 for FLV availability data
-/

namespace Phenomena.Conditionals.Studies.Mizuno2024

-- ════════════════════════════════════════════════════════════════
-- § Datum Structures
-- ════════════════════════════════════════════════════════════════

/-- A datum for Anderson conditional strategies.

Each datum records how a language expresses (or fails to express) an
Anderson conditional, and whether the resulting form is felicitous
for the Anderson reading. -/
structure AndersonDatum where
  /-- Language name -/
  language : String
  /-- Example number in @cite{mizuno-2024} -/
  exampleNumber : String
  /-- Morphological form of the antecedent -/
  antecedentForm : String
  /-- Morphological form of the consequent -/
  consequentForm : String
  /-- Whether this datum uses X-marking (counterfactual morphology).
      Where X-marking surfaces varies by language: in English, both
      antecedent and consequent; in Japanese/Mandarin, the consequent. -/
  hasXMarking : Bool
  /-- Whether the form is felicitous for an Anderson reading -/
  felicitousForAnderson : Bool
  /-- Gloss of the example -/
  gloss : String
  /-- English translation -/
  translation : String
  deriving Repr

/-- A datum for FLV X-marking availability per language. -/
structure FLVAvailabilityDatum where
  /-- Language name -/
  language : String
  /-- Whether X-marking is available for FLV conditionals -/
  xMarkingAvailable : Bool
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § English Data
-- ════════════════════════════════════════════════════════════════

/-- English Anderson conditional with X-marking (@cite{mizuno-2024}, ex. 1).
    @cite{anderson-1951}: "If Jones had taken arsenic, he would have shown
    exactly the symptoms he is actually showing."

    X-marking in antecedent (past perfect) + "actually" in consequent
    accesses the actual world. Felicitous for Anderson reading. -/
def english_xMarking : AndersonDatum where
  language := "English"
  exampleNumber := "1"
  antecedentForm := "had taken (past perfect)"
  consequentForm := "would have shown ... is actually showing"
  hasXMarking := true
  felicitousForAnderson := true
  gloss := "If Jones had taken arsenic, he would have shown exactly the symptoms he is actually showing."
  translation := "If Jones had taken arsenic, he would have shown exactly the symptoms he is actually showing."

/-- English Anderson conditional with O-marking (@cite{mizuno-2024}, ex. 2).
    "If Jones takes arsenic, he shows exactly the symptoms he is actually
    showing."

    O-marking (present tense) renders the conditional trivially true:
    the modal base is not expanded, so the consequent holds in all
    accessible worlds. Not felicitous for Anderson reading. -/
def english_oMarking : AndersonDatum where
  language := "English"
  exampleNumber := "2"
  antecedentForm := "takes (present)"
  consequentForm := "shows ... is actually showing"
  hasXMarking := false
  felicitousForAnderson := false
  gloss := "If Jones takes arsenic, he shows exactly the symptoms he is actually showing."
  translation := "If Jones takes arsenic, he shows exactly the symptoms he is actually showing."

-- ════════════════════════════════════════════════════════════════
-- § Japanese Data
-- ════════════════════════════════════════════════════════════════

/-- Japanese Anderson conditional with O-marking (@cite{mizuno-2024}, ex. 4a).
    Non-Past -ru in the consequent describes the actual world directly.
    Felicitous for Anderson reading.

    Jones-ga ototoi hiso-o nom-eba, [kare-no zissai-no syozyoo-to
    mattaku onazi syozyoo-o mise-ru] (hazuda).
    'If Jones had taken arsenic two days ago, he would have shown
    exactly the same symptoms as his actual symptoms.' -/
def japanese_oMarking : AndersonDatum where
  language := "Japanese"
  exampleNumber := "4a"
  antecedentForm := "nom-eba (COND)"
  consequentForm := "mise-ru (Non-Past) hazuda (MOD)"
  hasXMarking := false
  felicitousForAnderson := true
  gloss := "Jones-ga ototoi hiso-o nom-eba, kare-no zissai-no syozyoo-to mattaku onazi syozyoo-o mise-ru hazuda."
  translation := "If Jones had taken arsenic two days ago, he would have shown exactly the same symptoms as his actual symptoms."

/-- Japanese Anderson conditional with X-marking (@cite{mizuno-2024}, ex. 4b).
    Past -ta in the consequent gives a counterfactual reading, NOT an
    Anderson reading. The sentence describes counterfactual symptoms,
    not the actual symptoms Jones is showing.

    Jones-ga ototoi hiso-o nom-eba, [kare-no zissai-no syozyoo-to
    mattaku onazi syozyoo-o mise-ta] (hazuda).
    Same gloss but with Past -ta: yields CF reading only. -/
def japanese_xMarking : AndersonDatum where
  language := "Japanese"
  exampleNumber := "4b"
  antecedentForm := "nom-eba (COND)"
  consequentForm := "mise-ta (Past) hazuda (MOD)"
  hasXMarking := true
  felicitousForAnderson := false
  gloss := "Jones-ga ototoi hiso-o nom-eba, kare-no zissai-no syozyoo-to mattaku onazi syozyoo-o mise-ta hazuda."
  translation := "If Jones had taken arsenic two days ago, he would have shown exactly the same symptoms as his actual symptoms. (CF reading only)"

-- ════════════════════════════════════════════════════════════════
-- § Mandarin Data
-- ════════════════════════════════════════════════════════════════

/-- Mandarin Anderson conditional with O-marking (@cite{mizuno-2024}, ex. 13a).
    No perfective aspect le in the consequent → Anderson reading available.

    Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai
    shiji chuxian de zheyangde zhengzhuang.
    'If Jones had drunk arsenic yesterday, he would show exactly the
    symptoms he is actually showing.' -/
def mandarin_oMarking : AndersonDatum where
  language := "Mandarin"
  exampleNumber := "13a"
  antecedentForm := "ruguo ... he le (PERF) pishuang"
  consequentForm := "jiu hui chuxian ... (no final le)"
  hasXMarking := false
  felicitousForAnderson := true
  gloss := "Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang."
  translation := "If Jones had drunk arsenic yesterday, he would show exactly the symptoms he is actually showing."

/-- Mandarin Anderson conditional with X-marking (@cite{mizuno-2024}, ex. 13a).
    Perfective aspect le in the consequent blocks the Anderson reading.

    Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai
    shiji chuxian de zheyangde zhengzhuang #le.
    With final le: infelicitous for Anderson reading. -/
def mandarin_xMarking : AndersonDatum where
  language := "Mandarin"
  exampleNumber := "13a"
  antecedentForm := "ruguo ... he le (PERF) pishuang"
  consequentForm := "jiu hui chuxian ... le (PERF)"
  hasXMarking := true
  felicitousForAnderson := false
  gloss := "Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang le."
  translation := "If Jones had drunk arsenic yesterday, he would show exactly the symptoms he is actually showing. (#Anderson)"

-- ════════════════════════════════════════════════════════════════
-- § FLV Availability Data
-- ════════════════════════════════════════════════════════════════

/-- English: X-marking available for FLV. -/
def english_flv : FLVAvailabilityDatum where
  language := "English"
  xMarkingAvailable := true

/-- Japanese: X-marking NOT available for FLV. -/
def japanese_flv : FLVAvailabilityDatum where
  language := "Japanese"
  xMarkingAvailable := false

/-- Mandarin: X-marking NOT available for FLV. -/
def mandarin_flv : FLVAvailabilityDatum where
  language := "Mandarin"
  xMarkingAvailable := false

-- ════════════════════════════════════════════════════════════════
-- § Data-Level Theorems
-- ════════════════════════════════════════════════════════════════

/-- X-marking is felicitous for Anderson in English but not Japanese or Mandarin. -/
theorem xMarking_felicity :
    english_xMarking.felicitousForAnderson = true ∧
    japanese_xMarking.felicitousForAnderson = false ∧
    mandarin_xMarking.felicitousForAnderson = false :=
  ⟨rfl, rfl, rfl⟩

/-- O-marking is felicitous for Anderson in Japanese and Mandarin but not English. -/
theorem oMarking_felicity :
    english_oMarking.felicitousForAnderson = false ∧
    japanese_oMarking.felicitousForAnderson = true ∧
    mandarin_oMarking.felicitousForAnderson = true :=
  ⟨rfl, rfl, rfl⟩

/-- Each language has exactly one felicitous strategy for Anderson conditionals. -/
theorem complementary_strategies :
    english_xMarking.felicitousForAnderson ≠ english_oMarking.felicitousForAnderson ∧
    japanese_oMarking.felicitousForAnderson ≠ japanese_xMarking.felicitousForAnderson ∧
    mandarin_oMarking.felicitousForAnderson ≠ mandarin_xMarking.felicitousForAnderson := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § Per-Language Strategy Classification
-- ════════════════════════════════════════════════════════════════

open Semantics.Conditionals.Anderson (MarkingStrategy)

/-- English uses X-marking for Anderson conditionals:
    X-marking is felicitous (ex. 1), O-marking is not (ex. 2–3). -/
def english_strategy : MarkingStrategy := .xMarking

/-- Japanese uses O-marking for Anderson conditionals:
    O-marking is felicitous (ex. 4a), X-marking is not (ex. 4b). -/
def japanese_strategy : MarkingStrategy := .oMarking

/-- Mandarin uses O-marking for Anderson conditionals:
    O-marking is felicitous (ex. 13a without le), X-marking is not
    (ex. 13a with le). -/
def mandarin_strategy : MarkingStrategy := .oMarking

-- ════════════════════════════════════════════════════════════════
-- § Strategy–Datum Agreement
-- ════════════════════════════════════════════════════════════════

/-- English: strategy predicts X-marking = felicitous datum's marking. -/
theorem english_strategy_matches :
    english_strategy.hasXMarking = english_xMarking.hasXMarking := rfl

/-- Japanese: strategy predicts no X-marking = felicitous datum's marking. -/
theorem japanese_strategy_matches :
    japanese_strategy.hasXMarking = japanese_oMarking.hasXMarking := rfl

/-- Mandarin: strategy predicts no X-marking = felicitous datum's marking. -/
theorem mandarin_strategy_matches :
    mandarin_strategy.hasXMarking = mandarin_oMarking.hasXMarking := rfl

-- ════════════════════════════════════════════════════════════════
-- § Per-Datum Marking Verification
-- ════════════════════════════════════════════════════════════════

theorem english_xMarking_has_xMarking :
    english_xMarking.hasXMarking = true := rfl

theorem english_oMarking_no_xMarking :
    english_oMarking.hasXMarking = false := rfl

theorem japanese_oMarking_no_xMarking :
    japanese_oMarking.hasXMarking = false := rfl

theorem japanese_xMarking_has_xMarking :
    japanese_xMarking.hasXMarking = true := rfl

theorem mandarin_oMarking_no_xMarking :
    mandarin_oMarking.hasXMarking = false := rfl

theorem mandarin_xMarking_has_xMarking :
    mandarin_xMarking.hasXMarking = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § FLV Correlation Verification
-- ════════════════════════════════════════════════════════════════

/-- English: X-marking for Anderson ↔ X-marking for FLV. -/
theorem english_flv_correlation :
    english_strategy.flvXMarkingAvailable = english_flv.xMarkingAvailable := rfl

/-- Japanese: no X-marking for Anderson ↔ no X-marking for FLV. -/
theorem japanese_flv_correlation :
    japanese_strategy.flvXMarkingAvailable = japanese_flv.xMarkingAvailable := rfl

/-- Mandarin: no X-marking for Anderson ↔ no X-marking for FLV. -/
theorem mandarin_flv_correlation :
    mandarin_strategy.flvXMarkingAvailable = mandarin_flv.xMarkingAvailable := rfl

-- ════════════════════════════════════════════════════════════════
-- § Fragment Marker Connection
-- ════════════════════════════════════════════════════════════════

-- Japanese Anderson conditionals use -(r)eba, a marker that can mark
-- both HC and PC (unlike HC-only -ra). This connects the Anderson
-- data's antecedent form to the Fragment marker typology.
#guard Fragments.Japanese.Conditionals.eba.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

end Phenomena.Conditionals.Studies.Mizuno2024
