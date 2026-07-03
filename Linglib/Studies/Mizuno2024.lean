import Linglib.Semantics.Modality.Exclusion
import Linglib.Semantics.Conditionals.Basic
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Fragments.English.Conditionals
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.Mandarin.Conditionals
import Linglib.Data.Examples.Mizuno2024

/-!
# [mizuno-2024] — Strategies for Anderson Conditionals

Teruyuki Mizuno (2024), "Strategies for Anderson Conditionals: Their Implications for
the Typology of O-Marking and X-Marking", *Semantics and Pragmatics* 17(8): 1–14.
[anderson-1951] [schlenker-2004] [von-fintel-iatridou-2023] [iatridou-2000]

Anderson conditionals ([anderson-1951]) argue *for* the truth of their antecedent.
English must X-mark them (O-marking is trivial); Japanese and Mandarin must O-mark
them — their X-marking (Fake Past -ta: [ogihara-2014], [mizuno-kaufmann-2019];
perfective le) forces a counterfactual reading. Both strategies expand the modal
domain `D ⊂ D⁺`; Mizuno adopts the *expansion* analysis (fn 6, [mackay-2015],
[mackay-2019] contra [iatridou-2000] / [schulz-2014] exclusion) and analyzes Japanese
O-marking as a Historical-Present shift ([schlenker-2004], [anand-toosarvandani-2018a],
[anand-toosarvandani-2018b]) expanding `D` backward under branching time.

Stimuli: `Data/Examples/Mizuno2024.json` (module `Mizuno2024.Examples`); `#guard`s
check observed directions on the named examples, row theorems quantify over
`Examples.all`. Semantics: `Semantics.Conditionals.strictImp` over a
`HistoricalAlternatives` base; `Semantics.Modality.Exclusion` supplies the X/O
typology and exponent inventory.

## Main results

* `english_japanese_discrepancy` — English X-marks, Japanese O-marks.
* `inventory_prediction_fails_japanese` — the §3.1 puzzle: Japanese has X-marking
  (ex. 3) yet must not deploy it; English validates the inventory prediction.
* `anderson_judgments_match_strategy` — every recorded judgment matches the strategy
  record.
* `flv_anderson_correlation` — Anderson X-marking ⇔ FLV X-marking, per row (§4.2).
* `oMarking_anderson_trivial` / `xMarking_expands` / `consequent_open_over_xMarkedBase` /
  `expanded_anderson_informative` — the triviality puzzle and its resolution.
* `hp_expands_jones_domain` / `consequent_open_after_hp` — the HP route to the same
  conclusions: §4.1 on [von-fintel-iatridou-2023]'s uniformity hypothesis.
-/

namespace Mizuno2024

open Semantics.Modality.Exclusion (MarkingStrategy XMarkingExponent)
open Semantics.Conditionals (strictImp mem_strictImp_of_subset not_subset_of_mem_strictImp)
open HistoricalAlternatives (histEquiv_mono)
open Intensional (WorldTimeIndex)
open Data.Examples (LinguisticExample Glottocode)

/-! ### The per-language strategy record (§2–§4.2) -/

/-- The felicitous Anderson marking per language: English X (§2, ex. 1a), Japanese O
    (§3, ex. 4a -ru), Mandarin O (§4.2, ex. 13a without le); `none` outside the sample. -/
def andersonStrategy : Glottocode → Option MarkingStrategy
  | "stan1293" => some .xMarking
  | "nucl1643" => some .oMarking
  | "mand1415" => some .oMarking
  | _ => none

/-- FLV X-marking availability (§4.2): English yes (ex. 8); Japanese -ta (ex. 10) and
    Mandarin le (ex. 12) induce strong counterfactuality instead. -/
def flvXMarkingAvailable : Glottocode → Option Bool
  | "stan1293" => some true
  | "nucl1643" => some false
  | "mand1415" => some false
  | _ => none

/-- English and Japanese pick opposite Anderson strategies (§3). -/
theorem english_japanese_discrepancy :
    andersonStrategy "stan1293" ≠ andersonStrategy "nucl1643" := by decide

/-! ### The §3.1 puzzle: available X-marking that must not be deployed

Japanese has X-marking (Fake Past -ta, ex. 3; `Japanese.Conditionals.xMarking`), and §2
predicts it in Anderson conditionals — "strikingly, this is not borne out". Uniformity
(§4.1) survives as a meaning/use split: uniform semantics, blocked deployment. -/

/-- X-marking exponents, routed from the Fragment inventory. Mandarin le is
    study-local: fn 15's single consultant is below the Fragment consensus bar. -/
def xExponentOf : Glottocode → Option XMarkingExponent
  | "stan1293" => English.Conditionals.xMarking
  | "nucl1643" => Japanese.Conditionals.xMarking
  | "mand1415" => some ⟨"le", [.perfective]⟩
  | _ => none

/-- The inventory-driven prediction: X-mark wherever the inventory provides X-marking
    (§2; a fortiori under fn 14's [chierchia-1998]-style blocking). -/
def inventoryPrediction (lang : Glottocode) : Option MarkingStrategy :=
  (xExponentOf lang).map (λ _ => .xMarking)

/-- English validates the inventory prediction. -/
theorem inventory_prediction_holds_english :
    inventoryPrediction "stan1293" = andersonStrategy "stan1293" := by decide

/-- The §3.1 puzzle: Japanese has the X resource yet must not deploy it. -/
theorem inventory_prediction_fails_japanese :
    inventoryPrediction "nucl1643" ≠ andersonStrategy "nucl1643" := by decide

/-- Mandarin patterns with Japanese (§4.2). -/
theorem inventory_prediction_fails_mandarin :
    inventoryPrediction "mand1415" ≠ andersonStrategy "mand1415" := by decide

-- Ex. (3) grounds the inventory entry: tagged exponent = the Fragment's -ta; acceptable.
#guard Examples.ja3.feature? "x_exponent" == Japanese.Conditionals.xMarking.map (·.form)
#guard Examples.ja3.judgment == Features.Judgment.acceptable

/-! ### The attested minimal pairs

Pairs live inside one numbered example: the felicitous `primaryText` (strategy `m`)
plus the infelicitous `alternatives` entry (realizing `m.other`). -/

/-- Felicitous iff fully acceptable. -/
def isFelicitous : Features.Judgment → Bool
  | .acceptable => true
  | _ => false

/-- Parse the `strategy` tag. -/
def ofStrategyTag? : String → Option MarkingStrategy
  | "x-marking" => some .xMarking
  | "o-marking" => some .oMarking
  | _ => none

-- Ex. (1a) / (2): English X-marked felicitous, O-marked counterpart not.
#guard isFelicitous Examples.en1a.judgment && !isFelicitous Examples.en2.judgment
-- Ex. (4a): Japanese -ru felicitous; the -ta alternative not.
#guard isFelicitous Examples.ja4a.judgment &&
  Examples.ja4a.alternatives.all (λ a => !isFelicitous a.2)
-- Ex. (7a), radical HP: Non-Past required even with an overtly past consequent.
#guard isFelicitous Examples.ja7a.judgment &&
  Examples.ja7a.alternatives.all (λ a => !isFelicitous a.2)
-- Ex. (13a): Mandarin without le felicitous; with le not.
#guard isFelicitous Examples.ma13a.judgment &&
  Examples.ma13a.alternatives.all (λ a => !isFelicitous a.2)
-- Five Anderson rows (ex. 1a, 2, 4a, 7a, 13a); every row's language is in the record.
#guard (Examples.all.filter (·.feature? "construction" == some "anderson")).length == 5
#guard Examples.all.all (λ e => (andersonStrategy e.language).isSome)

/-- One Anderson row against the record: primary judgment matches strategy `m`, each
    alternative matches `m.other` (§2: O-marking = absence of X-marking). Non-Anderson
    rows pass vacuously. -/
def andersonRowOK (e : LinguisticExample) : Bool :=
  match e.feature? "construction", (e.feature? "strategy").bind ofStrategyTag? with
  | some "anderson", some m =>
      (isFelicitous e.judgment == (andersonStrategy e.language == some m)) &&
        e.alternatives.all (λ a =>
          isFelicitous a.2 == (andersonStrategy e.language == some m.other))
  | _, _ => true

/-- Every recorded Anderson judgment matches the strategy record. -/
theorem anderson_judgments_match_strategy :
    ∀ e ∈ Examples.all, andersonRowOK e = true := by decide

/-! ### The Future-Less-Vivid correlation (§4.2) -/

/-- The `flv_xmarking` tag. -/
def flvAvailableTag (e : LinguisticExample) : Option Bool :=
  match e.feature? "flv_xmarking" with
  | some "available"   => some true
  | some "unavailable" => some false
  | _                  => none

-- The FLV record is grounded in ex. 8 (English), 9–10 (Japanese), 11–12 (Mandarin).
#guard flvAvailableTag Examples.en8 == some true
#guard flvAvailableTag Examples.ja9 == some false
#guard flvAvailableTag Examples.ma11 == some false

/-- §4.2: Anderson X-marking and FLV X-marking stand or fall together, for every
    sampled language. An empirical correlation of two independent records, not a
    definition; cf. `Iatridou2000.CounterfactualType.flv` (one ExclF layer). -/
theorem flv_anderson_correlation :
    ∀ e ∈ Examples.all,
      (andersonStrategy e.language).map MarkingStrategy.hasXMarking =
        flvXMarkingAvailable e.language := by decide

/-! ### The triviality puzzle and its resolution by domain expansion

§2: an Anderson consequent is an observed fact, true throughout the live domain `D`,
so over `D` the conditional is trivial; both strategies expand `D` to a `D⁺` containing
a consequent-failing world. The Jones scenario as `strictImp` over a historical base:
worlds are `Bool` (`true` = symptoms shown), the domain at an index is its live
alternatives. `D` = the domain at `utteranceIdx`; `D⁺` via X-marking (larger base, same
index: `xMarkedBase`) or via HP (same base, earlier index: `hpIdx`) — same operator,
same two conclusions on each route: §4.1's uniformity of meaning under varying use. -/

/-- The Anderson consequent: Jones shows the symptoms. -/
def showsSymptoms : Set Bool := {w | w = true}

/-- A backward-closed history: live iff the index's own world, or its time is ≤ 0. -/
def historyJones : HistoricalAlternatives Bool ℤ :=
  λ s => { w | w = s.world ∨ s.time ≤ 0 }

@[simp]
theorem mem_historyJones {w : Bool} {s : WorldTimeIndex Bool ℤ} :
    w ∈ historyJones s ↔ w = s.world ∨ s.time ≤ 0 := Iff.rfl

theorem historyJones_backwardsClosed : historyJones.backwardsClosed :=
  λ _ _ _ _ hle hmem => Or.imp id (le_trans hle) hmem

/-- The utterance index; its domain is the paper's `D`. -/
def utteranceIdx : WorldTimeIndex Bool ℤ := ⟨true, 1⟩

/-- The HP-shifted index (§3.3); its domain is `D⁺` on the O-marking route. -/
def hpIdx : WorldTimeIndex Bool ℤ := ⟨true, 0⟩

/-- The X-marked base: every world live at every index (§2, fn 6) — `D⁺` on the
    X-marking route. -/
def xMarkedBase : HistoricalAlternatives Bool ℤ := λ _ => Set.univ

/-- Over `D` the consequent is trivial: only the symptom world is live (§2). -/
theorem consequent_trivial_at_utterance :
    historyJones utteranceIdx ⊆ showsSymptoms :=
  λ _ hw => Or.resolve_right hw (by decide)

/-- The symptom-absent world is not live at the utterance index. -/
theorem false_not_live : false ∉ historyJones utteranceIdx :=
  λ h => absurd (Or.resolve_left h Bool.false_ne_true) (by decide)

/-- O-marking without expansion: trivially true for any antecedent — the infelicity
    of ex. (2). -/
theorem oMarking_anderson_trivial (antecedent : Set Bool) :
    utteranceIdx ∈ strictImp historyJones antecedent showsSymptoms :=
  mem_strictImp_of_subset consequent_trivial_at_utterance

/-- X-marking's expansion is strict — the paper's `D ⊂ D⁺` (§2). -/
theorem xMarking_expands :
    historyJones utteranceIdx ⊂ xMarkedBase utteranceIdx :=
  (Set.ssubset_iff_of_subset (Set.subset_univ _)).mpr
    ⟨false, Set.mem_univ _, false_not_live⟩

/-- Over the X-marked `D⁺` the consequent is left open (§2). -/
theorem consequent_open_over_xMarkedBase :
    ¬ xMarkedBase utteranceIdx ⊆ showsSymptoms :=
  λ h => Bool.false_ne_true (h (Set.mem_univ false))

/-! ### Japanese O-marking: HP expansion under branching time

§3.3: the HP shift moves the evaluation index backward; live possibilities shrink
monotonically over time (the substrate's `backwardsClosed`, anchored on
[condoravdi-2002]), so the earlier index has a larger domain. -/

/-- The HP shift strictly enlarges the live domain (§3.3): subset by `histEquiv_mono`,
    strictness by the newly live symptom-absent world. -/
theorem hp_expands_jones_domain :
    historyJones utteranceIdx ⊂ historyJones hpIdx :=
  (Set.ssubset_iff_of_subset
      (λ _ hw => histEquiv_mono historyJones_backwardsClosed true _ zero_le_one hw)).mpr
    ⟨false, Or.inr le_rfl, false_not_live⟩

/-- Over the HP-shifted domain the consequent is left open — the conclusion
    `consequent_open_over_xMarkedBase` reaches by enlarging the base (§3.3, §4.1). -/
theorem consequent_open_after_hp :
    ¬ historyJones hpIdx ⊆ showsSymptoms :=
  λ h => Bool.false_ne_true (h (Or.inr le_rfl))

/-- The payoff (§2: "one can make a meaningful, contingent claim"): a true Anderson
    conditional at the HP index excludes a live world (`Set.not_subset` for the
    witness form). -/
theorem expanded_anderson_informative (antecedent : Set Bool)
    (h : hpIdx ∈ strictImp historyJones antecedent showsSymptoms) :
    ¬ historyJones hpIdx ⊆ antecedent :=
  not_subset_of_mem_strictImp h consequent_open_after_hp

/-! ### Fragment marker connection -/

-- Japanese Anderson conditionals use -(e)ba (both HC and PC, unlike HC-only -ra).
#guard Japanese.Conditionals.eba.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

-- Mandarin uses general-purpose ruguo; X/O is carried by consequent-final le.
#guard Mandarin.Conditionals.ruguo.markerType ==
  Semantics.Conditionals.ConditionalMarkerType.both

end Mizuno2024
