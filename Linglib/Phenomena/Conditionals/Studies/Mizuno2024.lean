import Linglib.Theories.Semantics.Modality.Exclusion
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.Mandarin.Conditionals
import Linglib.Phenomena.Conditionals.Studies.Iatridou2000

/-!
# @cite{mizuno-2024} — Anderson Conditionals Crosslinguistically
@cite{anderson-1951} @cite{condoravdi-2002} @cite{schlenker-2004} @cite{von-fintel-iatridou-2023}

Teruyuki Mizuno (2024). "Strategies for Anderson Conditionals: Their
Implications for the Typology of O-Marking and X-Marking."
*Semantics and Pragmatics* 17(8): 1–14.

## Key Empirical Generalizations

1. **English requires X-marking**: O-marking (present tense) renders Anderson
   conditionals trivially true — the consequent holds throughout the
   non-expanded domain D (ex. 2).
2. **Japanese requires O-marking**: X-marking (Past -ta in the consequent)
   yields a counterfactual reading, contradicting the Anderson follow-up
   (ex. 4a with #ta). O-marking (Non-Past -ru) is felicitous because
   Historical Present expands D without CF morphology (ex. 4a with ru).
3. **Mandarin patterns with Japanese**: perfective *le* functions as
   X-marking, blocking both Anderson and FLV readings (ex. 13a).
4. **FLV correlation**: X-marking availability for Anderson conditionals and
   for Future Less Vivid conditionals stand or fall together (§4.2).

## Data Sources

- Examples (1)–(2): English X-marking vs O-marking
- Example (4a): Japanese O-marking (ru) vs X-marking (#ta)
- Example (7a): Japanese radical HP case (indexicals *ototoi*, *kinoo*
  evaluate against utterance time)
- Example (13a): Mandarin O-marking (no *le*) vs X-marking (#*le*)
- §4.2 (8)–(10): English vs Japanese FLV
- §4.2 (11)–(13): Mandarin FLV and Anderson

-/

namespace Mizuno2024

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
      antecedent and consequent; in Japanese, Past -ta in consequent;
      in Mandarin, perfective *le* in consequent. -/
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

/-- English Anderson conditional with X-marking (@cite{mizuno-2024}, ex. 1a).

    @cite{anderson-1951}: "If Jones had taken arsenic, he would show
    exactly those symptoms which he does in fact show."

    X-marking in antecedent (past perfect). The consequent describes
    observed reality ("is now showing"), recovering the actual world
    despite counterfactual morphology. Felicitous for Anderson reading. -/
def english_xMarking : AndersonDatum where
  language := "English"
  exampleNumber := "1a"
  antecedentForm := "had taken (past perfect)"
  consequentForm := "would show ... is now showing"
  hasXMarking := true
  felicitousForAnderson := true
  gloss := "If Jones had taken arsenic last night, he would show those symptoms which he is now showing."
  translation := "If Jones had taken arsenic last night, he would show those symptoms which he is now showing."

/-- English Anderson conditional with O-marking (@cite{mizuno-2024}, ex. 2).

    O-marking (present tense) renders the conditional trivially true:
    the domain is not expanded, so the consequent (an observed fact)
    holds in all accessible worlds. Infelicitous for Anderson reading
    (@cite{stalnaker-1975}, @cite{von-fintel-1999-subjunctive}). -/
def english_oMarking : AndersonDatum where
  language := "English"
  exampleNumber := "2"
  antecedentForm := "takes (present)"
  consequentForm := "shows ... does in fact show"
  hasXMarking := false
  felicitousForAnderson := false
  gloss := "#If Jones takes arsenic, he shows just exactly those symptoms which he does in fact show."
  translation := "#If Jones takes arsenic, he shows just exactly those symptoms which he does in fact show."

-- ════════════════════════════════════════════════════════════════
-- § Japanese Data
-- ════════════════════════════════════════════════════════════════

/-- Japanese Anderson conditional with O-marking (@cite{mizuno-2024}, ex. 4a, -ru variant).
    Non-Past -ru in the consequent triggers Historical Present: the
    evaluation time shifts backward, expanding the domain under branching
    time (@cite{schlenker-2004}, @cite{condoravdi-2002}). Felicitous
    for Anderson reading.

    Tasikani, Jones-si-ga sakuya hiso-o nom-eba, kare-ga ima mise-tei-ru
    syoozyoo-to mattaku onazi syoozyoo-o ima mise-**ru** hazuda.
    'You're right. If Jones took arsenic last night, he would show exactly
    the same symptoms as he is now showing.' -/
def japanese_oMarking : AndersonDatum where
  language := "Japanese"
  exampleNumber := "4a"
  antecedentForm := "nom-eba (COND)"
  consequentForm := "mise-ru (Non-Past) hazuda (MOD)"
  hasXMarking := false
  felicitousForAnderson := true
  gloss := "Tasikani, Jones-si-ga sakuya hiso-o nom-eba, ... syoozyoo-o ima mise-ru hazuda."
  translation := "If Jones took arsenic last night, he would show exactly the same symptoms as he is now showing."

/-- Japanese Anderson conditional with X-marking (@cite{mizuno-2024}, ex. 4a, #ta variant).
    Past -ta in the consequent gives a counterfactual reading that
    implies the falsity of the antecedent, contradicting the Anderson
    follow-up (4b). The entire sequence is infelicitous.

    Tasikani, Jones-si-ga sakuya hiso-o nom-eba, ... syoozyoo-o ima
    mise-**#ta** hazuda. Soosuruto, kare-wa hontooni hiso-o non-da no daroo.
    With Past -ta: infelicitous for Anderson reading. -/
def japanese_xMarking : AndersonDatum where
  language := "Japanese"
  exampleNumber := "4a (#ta)"
  antecedentForm := "nom-eba (COND)"
  consequentForm := "mise-ta (Past) hazuda (MOD)"
  hasXMarking := true
  felicitousForAnderson := false
  gloss := "Tasikani, Jones-si-ga sakuya hiso-o nom-eba, ... syoozyoo-o ima mise-#ta hazuda."
  translation := "If Jones took arsenic last night, he would show exactly the same symptoms. (#Anderson, counterfactual reading only)"

/-- Japanese radical HP case (@cite{mizuno-2024}, ex. 7a).
    The consequent event clearly lies in the past, forced by the temporal
    adverbial *kinoo* 'yesterday'. Non-Past is still required — Past
    makes the sentence counterfactual. Temporal indexicals *ototoi*
    'two days ago' and *kinoo* 'yesterday' evaluate against the utterance
    time (θ = origin), paralleling @cite{schlenker-2004}'s HP analysis. -/
def japanese_radicalHP : AndersonDatum where
  language := "Japanese"
  exampleNumber := "7a"
  antecedentForm := "ototoi Manila-o syuppatusu-reba (COND)"
  consequentForm := "kinoo-no ... tuukas-{uru / #ita} (hazuda)"
  hasXMarking := false
  felicitousForAnderson := true
  gloss := "Tasikani, Jones-ga ototoi Manila-o syuppatusu-reba, ... kinoo ... tuukas-uru hazuda."
  translation := "If Jones had left Manila two days ago, he would have passed exactly the same immigration gate yesterday."

-- ════════════════════════════════════════════════════════════════
-- § Mandarin Data
-- ════════════════════════════════════════════════════════════════

/-- Mandarin Anderson conditional with O-marking (@cite{mizuno-2024}, ex. 13a, no final *le*).
    No perfective *le* in the consequent → Anderson reading available.

    Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai
    shiji chuxian de zheyangde zhengzhuang.
    'If Jones had drunk arsenic yesterday, he would show exactly the
    symptoms he is actually showing.' -/
def mandarin_oMarking : AndersonDatum where
  language := "Mandarin"
  exampleNumber := "13a"
  antecedentForm := "ruguo ... he le (PERF in antecedent)"
  consequentForm := "jiu hui chuxian ... (no final le)"
  hasXMarking := false
  felicitousForAnderson := true
  gloss := "Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang."
  translation := "If Jones had drunk arsenic yesterday, he would show exactly the symptoms he is actually showing."

/-- Mandarin Anderson conditional with X-marking (@cite{mizuno-2024}, ex. 13a, #*le*).
    Perfective *le* in the consequent blocks the Anderson reading.
    Like Japanese Past -ta, Mandarin *le* induces strong counterfactuality,
    contradicting the Anderson follow-up.

    Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai
    shiji chuxian de zheyangde zhengzhuang #**le**.
    With final *le*: infelicitous for Anderson reading. -/
def mandarin_xMarking : AndersonDatum where
  language := "Mandarin"
  exampleNumber := "13a (#le)"
  antecedentForm := "ruguo ... he le (PERF in antecedent)"
  consequentForm := "jiu hui chuxian ... le (PERF in consequent)"
  hasXMarking := true
  felicitousForAnderson := false
  gloss := "Ruguo Jones zuotian he le pishuang, jiu hui chuxian ta xianzai shiji chuxian de zheyangde zhengzhuang #le."
  translation := "If Jones had drunk arsenic yesterday, he would show exactly the symptoms he is actually showing. (#Anderson)"

-- ════════════════════════════════════════════════════════════════
-- § FLV Availability Data
-- ════════════════════════════════════════════════════════════════

/-- English: X-marking available for FLV (@cite{mizuno-2024}, ex. 8a).
    "If John came tomorrow, the party would be fun, ...
     but he probably won't come tomorrow, I think." -/
def english_flv : FLVAvailabilityDatum where
  language := "English"
  xMarkingAvailable := true

/-- Japanese: X-marking NOT available for FLV (@cite{mizuno-2024}, ex. 9–10).
    Past -ta in FLV induces strong counterfactuality (10a),
    contradicting the follow-up (10b). O-marking (Non-Past -u) is
    required (9a). -/
def japanese_flv : FLVAvailabilityDatum where
  language := "Japanese"
  xMarkingAvailable := false

/-- Mandarin: X-marking NOT available for FLV (@cite{mizuno-2024}, ex. 11–12).
    Perfective *le* in FLV blocks the unlikeliness follow-up (12b).
    O-marking (no *le*) is required (11a). -/
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

open Semantics.Modality.Exclusion (MarkingStrategy)

/-- English uses X-marking for Anderson conditionals:
    X-marking is felicitous (ex. 1a), O-marking is not (ex. 2). -/
def english_strategy : MarkingStrategy := .xMarking

/-- Japanese uses O-marking for Anderson conditionals:
    O-marking is felicitous (ex. 4a -ru), X-marking is not (ex. 4a #ta). -/
def japanese_strategy : MarkingStrategy := .oMarking

/-- Mandarin uses O-marking for Anderson conditionals:
    O-marking is felicitous (ex. 13a without *le*), X-marking is not
    (ex. 13a with #*le*). -/
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
-- § Language Profiles and FLV Correlation
-- ════════════════════════════════════════════════════════════════

/-- A language profile bundles the Anderson marking strategy with
    independently recorded FLV X-marking availability.

    The FLV availability is an empirical observation, not derived from
    the Anderson strategy. The correlation between the two is a theorem
    over the attested data, not a definitional identity. -/
structure LanguageProfile where
  language : String
  andersonStrategy : MarkingStrategy
  flvXMarkingAvailable : Bool
  deriving Repr

def english_profile : LanguageProfile where
  language := "English"
  andersonStrategy := .xMarking
  flvXMarkingAvailable := true

def japanese_profile : LanguageProfile where
  language := "Japanese"
  andersonStrategy := .oMarking
  flvXMarkingAvailable := false

def mandarin_profile : LanguageProfile where
  language := "Mandarin"
  andersonStrategy := .oMarking
  flvXMarkingAvailable := false

/-- @cite{mizuno-2024} §4.2: X-marking for Anderson conditionals and
    X-marking for FLV conditionals stand or fall together.

    This is an empirical generalization over English, Japanese, and Mandarin —
    not a logical necessity. The correlation could be explained by a Blocking
    Principle (@cite{chierchia-1998}): covert HP expansion is blocked when
    overt X-marking is available, but further research is needed. -/
theorem flv_anderson_correlation :
    english_profile.flvXMarkingAvailable = english_profile.andersonStrategy.hasXMarking ∧
    japanese_profile.flvXMarkingAvailable = japanese_profile.andersonStrategy.hasXMarking ∧
    mandarin_profile.flvXMarkingAvailable = mandarin_profile.andersonStrategy.hasXMarking :=
  ⟨rfl, rfl, rfl⟩

/-- The FLV data agrees with the language profiles. -/
theorem flv_data_matches_profiles :
    english_profile.flvXMarkingAvailable = english_flv.xMarkingAvailable ∧
    japanese_profile.flvXMarkingAvailable = japanese_flv.xMarkingAvailable ∧
    mandarin_profile.flvXMarkingAvailable = mandarin_flv.xMarkingAvailable :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § Fragment Marker Connection
-- ════════════════════════════════════════════════════════════════

-- Japanese Anderson conditionals use -(r)eba, a marker that can mark
-- both HC and PC (unlike HC-only -ra). This connects the Anderson
-- data's antecedent form to the Fragment marker typology.
#guard Fragments.Japanese.Conditionals.eba.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

-- Mandarin Anderson conditionals use ruguo, a general-purpose
-- conditional marker. The O-marking/X-marking distinction is carried
-- by consequent-final *le*, not by the conditional marker.
#guard Fragments.Mandarin.Conditionals.ruguo.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

-- ════════════════════════════════════════════════════════════════
-- § Iatridou 2000 Cross-Reference
-- ════════════════════════════════════════════════════════════════

open Iatridou2000
open Semantics.Modality.Exclusion (MarkingStrategy)
open Semantics.Modality.Exclusion (ExclDimension)
open Iatridou2000 (CounterfactualType)

/-- English X-marking for Anderson conditionals uses the same number of
    past layers as Iatridou's FLV type: 1 layer = 1 modal ExclF.

    @cite{mizuno-2024} §4.2 predicts this correlation: X-marking availability
    for Anderson conditionals and for FLV stand or fall together (English
    has both). @cite{iatridou-2000} provides the independent morphological
    count. -/
theorem english_xMarking_layers_match_flv :
    Iatridou2000.english_flv.pastLayers =
    CounterfactualType.flv.exclFCount := rfl

/-- English X-marking strategy maps to modal ExclDimension, consistent
    with @cite{iatridou-2000}'s analysis of counterfactual past as
    modal exclusion. -/
theorem english_strategy_is_modal_excl :
    english_strategy.exclDimension = some .modal := rfl

/-- Japanese O-marking strategy has no ExclDimension — no counterfactual
    morphology. The domain expansion comes from HP backward time shift,
    not from world exclusion. -/
theorem japanese_strategy_no_excl :
    japanese_strategy.exclDimension = none := rfl

/-- Mandarin O-marking strategy has no ExclDimension, paralleling
    Japanese. -/
theorem mandarin_strategy_no_excl :
    mandarin_strategy.exclDimension = none := rfl

end Mizuno2024
