import Linglib.Semantics.Modality.Exclusion
import Linglib.Semantics.Conditionals.Basic
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.Mandarin.Conditionals
import Linglib.Studies.Iatridou2000
import Linglib.Data.Examples.Mizuno2024

/-!
# [mizuno-2024] — Strategies for Anderson Conditionals

Teruyuki Mizuno (2024), "Strategies for Anderson Conditionals: Their Implications for
the Typology of O-Marking and X-Marking", *Semantics and Pragmatics* 17(8): 1–14.
[anderson-1951] [schlenker-2004] [von-fintel-iatridou-2023] [iatridou-2000]

Anderson conditionals ([anderson-1951]) argue *for* the truth of their antecedent
("If Jones had taken arsenic, he would show exactly the symptoms he is showing — so he
took arsenic"). Mizuno shows that English must X-mark them (O-marking is trivial),
whereas Japanese and Mandarin must O-mark them: their X-marking — the Fake Past -ta
([ogihara-2014], [mizuno-kaufmann-2019]) and perfective le — forces a counterfactual
reading. Both strategies avoid triviality by **expanding** the modal domain `D ⊂ D⁺`;
Mizuno adopts the *expansion* analysis of X-marking (fn 6, citing [mackay-2015],
[mackay-2019] against the [iatridou-2000] / [schulz-2014] exclusion analysis), and
analyzes Japanese O-marking as a Historical-Present perspectival shift ([schlenker-2004],
[anand-toosarvandani-2018a], [anand-toosarvandani-2018b]) that expands `D` by shifting
the evaluation time backward under branching time.

## Main results

* `english_japanese_discrepancy` — English X-marks, Japanese O-marks: the typological twist.
* `attested_felicity_matches_strategy` — the attested judgments fit the per-language strategy.
* `flv_anderson_correlation` — Anderson X-marking ⇔ Future-Less-Vivid X-marking (§4.2).
* `oMarking_anderson_trivial` / `xMarking_resolves_anderson` / `expanded_anderson_informative`
  — the triviality puzzle and its resolution by domain expansion, on the Jones-arsenic scenario.
* `hp_expands_jones_domain` / `hp_resolves_anderson` — Japanese HP: the backward index
  shift enlarges the live-possibility domain, achieving the same semantic effect as
  X-marking — Mizuno's take (§4.1) on [von-fintel-iatridou-2023]'s uniformity hypothesis.

The glossed stimuli live in `Data/Examples/Mizuno2024.json` (generated module
`Mizuno2024.Examples`). The semantics is `Semantics.Conditionals.strictImp` over a
`HistoricalAlternatives` modal base; `Semantics.Modality.Exclusion` (which cites
[mizuno-2024]) supplies the X/O marking typology.
-/

namespace Mizuno2024

open Semantics.Modality.Exclusion (MarkingStrategy)
open Semantics.Conditionals (strictImp mem_strictImp_of_subset not_subset_of_mem_strictImp)
open HistoricalAlternatives (histEquiv_mono)
open Intensional (WorldTimeIndex)
open Data.Examples (LinguisticExample)

/-! ### Languages and Anderson-conditional strategies

The X-marking / O-marking labels are [von-fintel-iatridou-2023]'s typological vocabulary
(the theory-neutral `MarkingStrategy` substrate enum). Mizuno's claim is *which* of the two
each language uses for a felicitous Anderson conditional. -/

/-- The three languages in [mizuno-2024]. -/
inductive Language where
  | english | japanese | mandarin
  deriving DecidableEq, Repr

/-- The marking strategy each language uses for *felicitous* Anderson conditionals:
    English X-marks (§2, ex. 1a); Japanese O-marks (§3, ex. 4a -ru); Mandarin O-marks
    (§4.2, ex. 13a without final le). -/
def andersonStrategy : Language → MarkingStrategy
  | .english => .xMarking
  | .japanese => .oMarking
  | .mandarin => .oMarking

/-- Whether X-marking is available for Future-Less-Vivid conditionals ([mizuno-2024], §4.2).
    English allows it (ex. 8); Japanese Past -ta (ex. 10) and Mandarin perfective le
    (ex. 12) instead induce strong counterfactuality, blocking the FLV reading. -/
def flvXMarkingAvailable : Language → Bool
  | .english => true
  | .japanese => false
  | .mandarin => false

/-- A marking is felicitous for an Anderson conditional in a language iff it is that
    language's Anderson strategy — so exactly one of the two markings is felicitous per
    language. Derived from `andersonStrategy`, not stipulated: English requires X-marking
    (O-marking is trivial, ex. 2); Japanese/Mandarin require O-marking (X-marking is
    counterfactual, ex. 4a #ta / ex. 13a #le). -/
abbrev felicitousForAnderson (lang : Language) (m : MarkingStrategy) : Prop :=
  m = andersonStrategy lang

/-- The core typological twist ([mizuno-2024], §3): English and Japanese pick *opposite*
    strategies for Anderson conditionals. -/
theorem english_japanese_discrepancy :
    andersonStrategy .english ≠ andersonStrategy .japanese := by decide

/-! ### Attested minimal pairs (the empirical anchor)

The glossed stimuli live in `Data/Examples/Mizuno2024.json` → generated module
`Mizuno2024.Examples` (ex. 1a, 2, 4a, 7a, 13a for Anderson; 8, 9, 11 for FLV). The X/O
minimal pairs within one numbered example (4a's -ru / -ta, 13a's ∅ / le) are recorded as
the felicitous `primaryText` plus the infelicitous `alternatives` entry; the realized
strategy is tagged in `paperFeatures`. The adapters below are interpretation-light: they
read the `strategy` / `construction` tags and the recorded judgments, never parsing the
surface forms. -/

/-- Felicity as a Bool: an Anderson conditional counts as felicitous iff fully acceptable. -/
def isFelicitous : Features.Judgment → Bool
  | .acceptable => true
  | _ => false

/-- Map a Glottocode to the [mizuno-2024] `Language` (English, Japanese, Mandarin). -/
def ofGlottocode : String → Option Language
  | "stan1293" => some .english
  | "nucl1643" => some .japanese
  | "mand1415" => some .mandarin
  | _ => none

/-- Parse the `strategy` tag into a `MarkingStrategy`. -/
def ofStrategyTag : String → Option MarkingStrategy
  | "x-marking" => some .xMarking
  | "o-marking" => some .oMarking
  | _ => none

/-- Project the Anderson rows from an example: the `primaryText`'s (strategy, felicity),
    plus — for a minimal-pair example — the complementary strategy (`MarkingStrategy.other`,
    per §2's "O-marking [is] generally defined as the absence of X-marking") paired with
    the alternative's judgment. Non-Anderson examples and unrecognized language/strategy
    tags yield no rows. -/
def andersonRows (e : LinguisticExample) : List (Language × MarkingStrategy × Bool) :=
  match ofGlottocode e.language, e.feature? "construction",
        (e.feature? "strategy").bind ofStrategyTag with
  | some lang, some "anderson", some m =>
      (lang, m, isFelicitous e.judgment) ::
        e.alternatives.map (λ a => (lang, m.other, isFelicitous a.2))
  | _, _, _ => []

/-- All attested Anderson rows, projected from the generated example data. -/
def attestedAndersonRows : List (Language × MarkingStrategy × Bool) :=
  Examples.all.flatMap andersonRows

/-- The attested judgments fit the per-language strategy: every projected row is
    felicitous iff its marking is `felicitousForAnderson` in its language. -/
theorem attested_felicity_matches_strategy :
    ∀ r ∈ attestedAndersonRows, (r.2.2 = true ↔ felicitousForAnderson r.1 r.2.1) := by
  decide

/-- The projection is non-vacuous and covers all six cells: both markings are attested in
    every language (English via ex. 1a / 2, Japanese and Mandarin via the 4a / 13a minimal
    pairs and 7a). -/
theorem attestedAndersonRows_complete :
    (.english, .xMarking, true) ∈ attestedAndersonRows ∧
    (.english, .oMarking, false) ∈ attestedAndersonRows ∧
    (.japanese, .oMarking, true) ∈ attestedAndersonRows ∧
    (.japanese, .xMarking, false) ∈ attestedAndersonRows ∧
    (.mandarin, .oMarking, true) ∈ attestedAndersonRows ∧
    (.mandarin, .xMarking, false) ∈ attestedAndersonRows := by decide

/-! ### The Future-Less-Vivid correlation (§4.2) -/

/-- [mizuno-2024], §4.2: X-marking for Anderson conditionals and X-marking for FLV
    conditionals stand or fall together. Across English / Japanese / Mandarin, a language
    X-marks Anderson conditionals iff X-marking is available for its FLV conditionals.
    An empirical generalization (Mizuno speculates a [chierchia-1998] Blocking Principle:
    covert HP is blocked where overt X-marking is available, fn 14), not a definitional
    identity — the two functions are recorded independently. -/
theorem flv_anderson_correlation (lang : Language) :
    (andersonStrategy lang).hasXMarking = flvXMarkingAvailable lang := by
  cases lang <;> rfl

/-- Cross-reference to [iatridou-2000]: English has X-marking available for FLV
    ([mizuno-2024], §4.2), and Iatridou independently classifies the FLV as carrying a
    single ExclF (past) layer. The morphological count is Iatridou's; Mizuno cites
    [iatridou-2000] for the FLV connection without adopting her exclusion analysis. -/
theorem english_flv_matches_iatridou :
    flvXMarkingAvailable .english = true ∧ Iatridou2000.CounterfactualType.flv.exclFCount = 1 :=
  ⟨rfl, rfl⟩

/-- FLV X-marking availability read from the example data (`flv_xmarking` tag). -/
def flvAvailableTag (e : LinguisticExample) : Option Bool :=
  match e.feature? "flv_xmarking" with
  | some "available"   => some true
  | some "unavailable" => some false
  | _                  => none

/-- The recorded FLV availability (ex. 8 English, ex. 9–10 Japanese, ex. 11–12 Mandarin)
    matches the `flvXMarkingAvailable` generalization the §4.2 correlation runs on. -/
theorem flv_examples_match_generalization :
    flvAvailableTag Examples.en8 = some (flvXMarkingAvailable .english) ∧
    flvAvailableTag Examples.ja9 = some (flvXMarkingAvailable .japanese) ∧
    flvAvailableTag Examples.ma11 = some (flvXMarkingAvailable .mandarin) := by decide

/-! ### The triviality puzzle and its resolution by domain expansion

[mizuno-2024]'s core semantic argument (§2): an Anderson consequent is an observed *fact*,
true at every world in the non-expanded domain `D` of live possibilities, so over `D` the
conditional is trivially true and uninformative. Both strategies fix this by expanding `D`
to a `D⁺` containing a world where the consequent fails. Mizuno adopts the *expansion*
analysis of X-marking (fn 6, citing [mackay-2015] against [iatridou-2000] exclusion).

The Jones-arsenic scenario as a strict conditional (`Semantics.Conditionals.strictImp`)
over a historical modal base: worlds are `Bool` (`true` = Jones shows the symptoms),
evaluation points are ⟨world, time⟩ indices, and the domain at an index is its set of
live alternatives. The paper's `D` is the domain at the utterance index; `D⁺` is its
expansion — reached by X-marking (a larger base, same index) or by the Japanese HP
shift (same base, earlier index). -/

/-- The Anderson consequent: Jones shows the (arsenic) symptoms. -/
def showsSymptoms : Set Bool := {w | w = true}

/-- A backward-closed history: a world is a live alternative to `s` iff it is `s`'s own
    world, or `s`'s time is at or before `0`. Earlier times have strictly more
    alternatives. -/
def historyJones : HistoricalAlternatives Bool ℤ :=
  λ s => { w | w = s.world ∨ s.time ≤ 0 }

theorem historyJones_backwardsClosed : historyJones.backwardsClosed :=
  λ _ _ _ _ hle hmem => Or.imp id (le_trans hle) hmem

/-- The utterance index: the symptom world, at a time (`1`) after the facts are settled.
    Its domain is the paper's `D`. -/
def utteranceIdx : WorldTimeIndex Bool ℤ := ⟨true, 1⟩

/-- The HP-shifted index ([mizuno-2024], §3.3): same world, evaluation time moved
    backward to `0`. Its domain is the paper's `D⁺` on the O-marking route. -/
def hpIdx : WorldTimeIndex Bool ℤ := ⟨true, 0⟩

/-- Over `D`, the consequent is trivial: at the utterance index only the symptom world
    is live, and it is an observed fact there ([mizuno-2024], §2). -/
theorem consequent_trivial_at_utterance :
    historyJones utteranceIdx ⊆ showsSymptoms :=
  λ _ hw => Or.resolve_right hw (by decide)

/-- O-marking without expansion: at the utterance index the Anderson conditional is
    trivially true for *any* antecedent — Mizuno's triviality puzzle, the infelicity of
    ex. (2). -/
theorem oMarking_anderson_trivial (antecedent : Set Bool) :
    utteranceIdx ∈ strictImp historyJones antecedent showsSymptoms :=
  mem_strictImp_of_subset consequent_trivial_at_utterance

/-- The X-marked base: counterfactual morphology makes every world live at every index
    ([mizuno-2024], §2's expansion analysis, fn 6) — the miniature's `D⁺` on the
    X-marking route. -/
def xMarkedBase : HistoricalAlternatives Bool ℤ := λ _ => Set.univ

/-- The symptom-absent world is not live at the utterance index. -/
theorem false_not_live : false ∉ historyJones utteranceIdx :=
  λ h => absurd (Or.resolve_left h (by decide)) (by decide)

/-- X-marking resolves triviality: the expansion is strict (the paper's `D ⊂ D⁺`) and
    the consequent fails at the newly live symptom-absent world, so it is no longer
    trivial over `D⁺` ([mizuno-2024], §2). -/
theorem xMarking_resolves_anderson :
    historyJones utteranceIdx ⊂ xMarkedBase utteranceIdx ∧
      ¬ xMarkedBase utteranceIdx ⊆ showsSymptoms :=
  ⟨(Set.ssubset_iff_of_subset (Set.subset_univ _)).mpr
      ⟨false, Set.mem_univ _, false_not_live⟩,
    λ h => Bool.false_ne_true (h (Set.mem_univ false))⟩

/-! ### Japanese O-marking: HP expansion under branching time

Why Japanese O-marking (Non-Past) escapes triviality without X-marking ([mizuno-2024],
§3.3): the Historical-Present shift moves the evaluation index backward, and since live
possibilities monotonically shrink as time develops (Mizuno's assumption; the substrate's
`backwardsClosed`, anchored on [condoravdi-2002]), the earlier index has a larger
domain — domain expansion without counterfactual morphology. -/

/-- The HP backward shift strictly enlarges the live domain: every world live at the
    utterance index stays live at the earlier index (the substrate's `histEquiv_mono`),
    and the symptom-absent world becomes newly live ([mizuno-2024], §3.3). -/
theorem hp_expands_jones_domain :
    historyJones utteranceIdx ⊂ historyJones hpIdx :=
  (Set.ssubset_iff_of_subset
      (λ _ hw => histEquiv_mono historyJones_backwardsClosed true _ (by decide) hw)).mpr
    ⟨false, Or.inr le_rfl, false_not_live⟩

/-- O-marking resolves triviality the HP way ([mizuno-2024], §3.3): over the shifted
    domain the consequent is non-trivial — the same conclusion
    `xMarking_resolves_anderson` reaches by enlarging the base. Same operator
    (`strictImp`), same semantic effect; X-marking moves the *base* argument, the HP
    shift moves the *index* argument. Together with `english_japanese_discrepancy`,
    this renders §4.1's take on [von-fintel-iatridou-2023]'s uniformity hypothesis:
    what varies across languages is which route may be deployed, not what the
    expansion does. -/
theorem hp_resolves_anderson :
    historyJones utteranceIdx ⊂ historyJones hpIdx ∧
      ¬ historyJones hpIdx ⊆ showsSymptoms :=
  ⟨hp_expands_jones_domain, λ h => Bool.false_ne_true (h (Or.inr le_rfl))⟩

/-- The payoff ([mizuno-2024], §2: "one can make a meaningful, contingent claim"): a
    true Anderson conditional at the HP-shifted index is informative — its antecedent
    excludes a live world (`Set.not_subset` gives the ∃-witness form). -/
theorem expanded_anderson_informative (antecedent : Set Bool)
    (h : hpIdx ∈ strictImp historyJones antecedent showsSymptoms) :
    ¬ historyJones hpIdx ⊆ antecedent :=
  not_subset_of_mem_strictImp h hp_resolves_anderson.2

/-! ### Fragment marker connection -/

-- Japanese Anderson conditionals use -(e)ba, which marks both HC and PC (unlike HC-only
-- -ra): with Non-Past consequent → Anderson, with Past consequent → counterfactual.
#guard Japanese.Conditionals.eba.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

-- Mandarin Anderson conditionals use the general-purpose marker ruguo; the X/O-marking
-- distinction is carried by consequent-final le, not by the conditional marker.
#guard Mandarin.Conditionals.ruguo.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

end Mizuno2024
