import Linglib.Semantics.Modality.Exclusion
import Linglib.Semantics.Conditionals.Basic
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.Mandarin.Conditionals
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

The glossed stimuli live in `Data/Examples/Mizuno2024.json` (generated module
`Mizuno2024.Examples`); per-pair `#guard`s check the observed directions on the named
examples, and the row theorems quantify over `Examples.all`. The semantics is
`Semantics.Conditionals.strictImp` over a `HistoricalAlternatives` modal base;
`Semantics.Modality.Exclusion` (which cites [mizuno-2024]) supplies the X/O typology.

## Main results

* `english_japanese_discrepancy` — English X-marks, Japanese O-marks: the typological twist.
* `anderson_judgments_match_strategy` — every recorded Anderson judgment (primary text and
  minimal-pair alternative) matches the per-language strategy record.
* `flv_anderson_correlation` — Anderson X-marking ⇔ Future-Less-Vivid X-marking, per
  sample row (§4.2).
* `oMarking_anderson_trivial` / `xMarking_expands` / `consequent_open_over_xMarkedBase` /
  `expanded_anderson_informative` — the triviality puzzle and its resolution by domain
  expansion, on the Jones-arsenic scenario.
* `hp_expands_jones_domain` / `consequent_open_after_hp` — the Japanese HP route to the
  same two conclusions: Mizuno's take (§4.1) on [von-fintel-iatridou-2023]'s uniformity
  hypothesis.
-/

namespace Mizuno2024

open Semantics.Modality.Exclusion (MarkingStrategy)
open Semantics.Conditionals (strictImp mem_strictImp_of_subset not_subset_of_mem_strictImp)
open HistoricalAlternatives (histEquiv_mono)
open Intensional (WorldTimeIndex)
open Data.Examples (LinguisticExample Glottocode)

/-! ### The per-language strategy record (§2–§4.2)

The X-marking / O-marking labels are [von-fintel-iatridou-2023]'s typological vocabulary
(the theory-neutral `MarkingStrategy` substrate enum). Mizuno's finding is *which* of the
two each language uses for a felicitous Anderson conditional; the record is keyed by the
data rows' own Glottocodes and checked against every row below. -/

/-- The felicitous Anderson-conditional marking per language: English X-marks (§2,
    ex. 1a); Japanese O-marks (§3, ex. 4a -ru); Mandarin O-marks (§4.2, ex. 13a without
    final le). `none` for languages outside the paper's sample. -/
def andersonStrategy : Glottocode → Option MarkingStrategy
  | "stan1293" => some .xMarking
  | "nucl1643" => some .oMarking
  | "mand1415" => some .oMarking
  | _ => none

/-- Whether X-marking is available for Future-Less-Vivid conditionals ([mizuno-2024],
    §4.2). English allows it (ex. 8); Japanese Past -ta (ex. 10) and Mandarin perfective
    le (ex. 12) instead induce strong counterfactuality, blocking the FLV reading. -/
def flvXMarkingAvailable : Glottocode → Option Bool
  | "stan1293" => some true
  | "nucl1643" => some false
  | "mand1415" => some false
  | _ => none

/-- The core typological twist ([mizuno-2024], §3): English and Japanese pick *opposite*
    strategies for Anderson conditionals. -/
theorem english_japanese_discrepancy :
    andersonStrategy "stan1293" ≠ andersonStrategy "nucl1643" := by decide

/-! ### The attested minimal pairs (the empirical anchor)

The X/O minimal pairs within one numbered example (4a's -ru / -ta, 13a's ∅ / le) are
recorded as the felicitous `primaryText` plus the infelicitous `alternatives` entry; the
realized strategy is tagged in `paperFeatures`. The `#guard`s check the observed
directions on the named examples; `anderson_judgments_match_strategy` states the
generalization over all rows. -/

/-- Felicity as a Bool: an Anderson conditional counts as felicitous iff fully acceptable. -/
def isFelicitous : Features.Judgment → Bool
  | .acceptable => true
  | _ => false

/-- Parse the `strategy` tag into a `MarkingStrategy`. -/
def ofStrategyTag? : String → Option MarkingStrategy
  | "x-marking" => some .xMarking
  | "o-marking" => some .oMarking
  | _ => none

-- Ex. (1a) / (2): the English pair — X-marked felicitous, O-marked counterpart not.
#guard isFelicitous Examples.en1a.judgment && !isFelicitous Examples.en2.judgment
-- Ex. (4a): Japanese O-marked -ru felicitous; the X-marked -ta alternative is not.
#guard isFelicitous Examples.ja4a.judgment &&
  Examples.ja4a.alternatives.all (λ a => !isFelicitous a.2)
-- Ex. (7a), the radical-HP case: Non-Past required even with an overtly past consequent.
#guard isFelicitous Examples.ja7a.judgment &&
  Examples.ja7a.alternatives.all (λ a => !isFelicitous a.2)
-- Ex. (13a): Mandarin without consequent-final le felicitous; with le not.
#guard isFelicitous Examples.ma13a.judgment &&
  Examples.ma13a.alternatives.all (λ a => !isFelicitous a.2)
-- The sample has five Anderson rows (ex. 1a, 2, 4a, 7a, 13a), covering all six
-- language × marking cells, and every row's language is in the strategy record.
#guard (Examples.all.filter (·.feature? "construction" == some "anderson")).length == 5
#guard Examples.all.all (λ e => (andersonStrategy e.language).isSome)

/-- Check one Anderson row against the strategy record: the primary text (realizing the
    tagged strategy `m`) is judged felicitous iff `m` is the language's strategy, and
    each minimal-pair alternative (realizing `m.other`, per §2's "O-marking [is]
    generally defined as the absence of X-marking") is judged felicitous iff `m.other`
    is. Non-Anderson rows pass vacuously. -/
def andersonRowOK (e : LinguisticExample) : Bool :=
  match e.feature? "construction", (e.feature? "strategy").bind ofStrategyTag? with
  | some "anderson", some m =>
      (isFelicitous e.judgment == (andersonStrategy e.language == some m)) &&
        e.alternatives.all (λ a =>
          isFelicitous a.2 == (andersonStrategy e.language == some m.other))
  | _, _ => true

/-- Every recorded Anderson judgment matches the per-language strategy record. -/
theorem anderson_judgments_match_strategy :
    ∀ e ∈ Examples.all, andersonRowOK e = true := by decide

/-! ### The Future-Less-Vivid correlation (§4.2) -/

/-- FLV X-marking availability read from the example data (`flv_xmarking` tag). -/
def flvAvailableTag (e : LinguisticExample) : Option Bool :=
  match e.feature? "flv_xmarking" with
  | some "available"   => some true
  | some "unavailable" => some false
  | _                  => none

-- The FLV availability record is grounded in ex. 8 (English), 9–10 (Japanese),
-- 11–12 (Mandarin).
#guard flvAvailableTag Examples.en8 == some true
#guard flvAvailableTag Examples.ja9 == some false
#guard flvAvailableTag Examples.ma11 == some false

/-- [mizuno-2024], §4.2: X-marking for Anderson conditionals and X-marking for FLV
    conditionals stand or fall together — for every sampled language, the Anderson
    strategy X-marks iff FLV X-marking is available. An empirical generalization
    (Mizuno speculates a [chierchia-1998] Blocking Principle: covert HP is blocked
    where overt X-marking is available, fn 14), not a definitional identity — the two
    records are kept independently. [iatridou-2000] independently classifies the FLV
    as carrying a single ExclF layer (`Iatridou2000.CounterfactualType.flv`). -/
theorem flv_anderson_correlation :
    ∀ e ∈ Examples.all,
      (andersonStrategy e.language).map MarkingStrategy.hasXMarking =
        flvXMarkingAvailable e.language := by decide

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
expansion — reached by X-marking (a larger base, same index: `xMarkedBase`) or by the
Japanese HP shift (same base, earlier index: `hpIdx`). Same operator, same two
conclusions on each route (strict expansion, consequent left open) — [mizuno-2024]'s
take (§4.1) on [von-fintel-iatridou-2023]'s uniformity hypothesis: what varies across
languages is which route may be deployed, not what the expansion does. -/

/-- The Anderson consequent: Jones shows the (arsenic) symptoms. -/
def showsSymptoms : Set Bool := {w | w = true}

/-- A backward-closed history: a world is a live alternative to `s` iff it is `s`'s own
    world, or `s`'s time is at or before `0`. Earlier times have strictly more
    alternatives. -/
def historyJones : HistoricalAlternatives Bool ℤ :=
  λ s => { w | w = s.world ∨ s.time ≤ 0 }

@[simp]
theorem mem_historyJones {w : Bool} {s : WorldTimeIndex Bool ℤ} :
    w ∈ historyJones s ↔ w = s.world ∨ s.time ≤ 0 := Iff.rfl

theorem historyJones_backwardsClosed : historyJones.backwardsClosed :=
  λ _ _ _ _ hle hmem => Or.imp id (le_trans hle) hmem

/-- The utterance index: the symptom world, at a time (`1`) after the facts are settled.
    Its domain is the paper's `D`. -/
def utteranceIdx : WorldTimeIndex Bool ℤ := ⟨true, 1⟩

/-- The HP-shifted index ([mizuno-2024], §3.3): same world, evaluation time moved
    backward to `0`. Its domain is the paper's `D⁺` on the O-marking route. -/
def hpIdx : WorldTimeIndex Bool ℤ := ⟨true, 0⟩

/-- The X-marked base: counterfactual morphology makes every world live at every index
    ([mizuno-2024], §2's expansion analysis, fn 6) — the paper's `D⁺` on the X-marking
    route. -/
def xMarkedBase : HistoricalAlternatives Bool ℤ := λ _ => Set.univ

/-- Over `D`, the consequent is trivial: at the utterance index only the symptom world
    is live, and it is an observed fact there ([mizuno-2024], §2). -/
theorem consequent_trivial_at_utterance :
    historyJones utteranceIdx ⊆ showsSymptoms :=
  λ _ hw => Or.resolve_right hw (by decide)

/-- The symptom-absent world is not live at the utterance index. -/
theorem false_not_live : false ∉ historyJones utteranceIdx :=
  λ h => absurd (Or.resolve_left h Bool.false_ne_true) (by decide)

/-- O-marking without expansion: at the utterance index the Anderson conditional is
    trivially true for *any* antecedent — Mizuno's triviality puzzle, the infelicity of
    ex. (2). -/
theorem oMarking_anderson_trivial (antecedent : Set Bool) :
    utteranceIdx ∈ strictImp historyJones antecedent showsSymptoms :=
  mem_strictImp_of_subset consequent_trivial_at_utterance

/-- X-marking's expansion is strict — the paper's `D ⊂ D⁺` (§2). -/
theorem xMarking_expands :
    historyJones utteranceIdx ⊂ xMarkedBase utteranceIdx :=
  (Set.ssubset_iff_of_subset (Set.subset_univ _)).mpr
    ⟨false, Set.mem_univ _, false_not_live⟩

/-- Over the X-marked `D⁺` the consequent is left open — no longer trivial (§2:
    "the new domain signaled by X-marking leaves open ... the truth of the
    consequent"). -/
theorem consequent_open_over_xMarkedBase :
    ¬ xMarkedBase utteranceIdx ⊆ showsSymptoms :=
  λ h => Bool.false_ne_true (h (Set.mem_univ false))

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
      (λ _ hw => histEquiv_mono historyJones_backwardsClosed true _ zero_le_one hw)).mpr
    ⟨false, Or.inr le_rfl, false_not_live⟩

/-- Over the HP-shifted domain the consequent is left open — the same conclusion
    `consequent_open_over_xMarkedBase` reaches by enlarging the base ([mizuno-2024],
    §3.3; §4.1 on the uniformity of the two routes). -/
theorem consequent_open_after_hp :
    ¬ historyJones hpIdx ⊆ showsSymptoms :=
  λ h => Bool.false_ne_true (h (Or.inr le_rfl))

/-- The payoff ([mizuno-2024], §2: "one can make a meaningful, contingent claim"): a
    true Anderson conditional at the HP-shifted index is informative — its antecedent
    excludes a live world (`Set.not_subset` gives the ∃-witness form). -/
theorem expanded_anderson_informative (antecedent : Set Bool)
    (h : hpIdx ∈ strictImp historyJones antecedent showsSymptoms) :
    ¬ historyJones hpIdx ⊆ antecedent :=
  not_subset_of_mem_strictImp h consequent_open_after_hp

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
