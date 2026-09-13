import Linglib.Semantics.Modality.Exclusion
import Linglib.Semantics.Conditionals.Basic
import Linglib.Semantics.Modality.HistoricalAlternatives
import Linglib.Fragments.English.Conditionals
import Linglib.Fragments.Japanese.Conditionals
import Linglib.Fragments.Mandarin.Conditionals
import Linglib.Data.Examples.Mizuno2024

/-!
# Mizuno (2024): Strategies for Anderson Conditionals

This file formalizes the account in [mizuno-2024] of Anderson conditionals, conditionals
whose consequent is an observed fact and which therefore argue for their antecedent
([anderson-1951]). English must X-mark them, since over the live domain the consequent is
trivially true and O-marking says nothing, while Japanese and Mandarin must O-mark them:
their X-marking, the fake past *-ta* and the perfective *le*, forces a counterfactual
reading. The typological record and its attested minimal pairs are transferred from the
paper's examples (`andersonStrategy`, `anderson_judgments_match_strategy`), and the
correlation with future-less-vivid conditionals holds row by row
(`flv_anderson_correlation`). Both strategies enlarge the modal domain to one containing a
consequent-failing world, after the expansion analysis of [mackay-2015] and [mackay-2019]:
X-marking by enlarging the base (`xMarking_expands`), Japanese O-marking by a
historical-present shift of the evaluation index backward under branching time
([schlenker-2004a]; `hp_expands_jones_domain`), and on either route the consequent is left
open and a true Anderson conditional excludes a live world (`expanded_anderson_informative`).

## Implementation notes

The Jones scenario is a strict conditional over a historical base whose worlds record
whether the symptoms are shown; the marking typology and exponent inventory are those of
`Semantics/Modality/Exclusion`, and the Mandarin exponent *le* is study-local, resting on
the paper's single consultant.

## References

* [mizuno-2024]
* [anderson-1951]
* [schlenker-2004a]
* [von-fintel-iatridou-2023]
* [iatridou-2000]
* [mackay-2015]
* [mackay-2019]
* [condoravdi-2002]
-/

namespace Mizuno2024

open Modality.Exclusion (MarkingStrategy XMarkingExponent)
open Conditionals (strictImp mem_strictImp_of_subset not_subset_of_mem_strictImp)
open HistoricalAlternatives (histEquiv_mono)
open Reference
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

/-! ### The attested minimal pairs

Pairs live inside one numbered example: the felicitous `primaryText` (strategy `m`)
plus the infelicitous `alternatives` entry (realizing `m.other`). -/

/-- Felicitous when fully acceptable. -/
def IsFelicitous (j : Features.Judgment) : Prop := j = .acceptable

/-- Parse the `strategy` tag. -/
def ofStrategyTag? : String → Option MarkingStrategy
  | "x-marking" => some .xMarking
  | "o-marking" => some .oMarking
  | _ => none

/-- An Anderson row against the record: the primary judgment matches strategy `m` and each
alternative matches the other strategy, O-marking being the absence of X-marking. -/
def AndersonRowOK (e : LinguisticExample) : Prop :=
  e.feature? "construction" = some "anderson" →
    ∀ m ∈ (e.feature? "strategy").bind ofStrategyTag?,
      (IsFelicitous e.judgment ↔ andersonStrategy e.language = some m) ∧
        ∀ a ∈ e.alternatives, (IsFelicitous a.2 ↔ andersonStrategy e.language = some m.other)

instance : DecidablePred AndersonRowOK := by
  unfold AndersonRowOK IsFelicitous; infer_instance

/-- Every recorded Anderson judgment matches the strategy record. -/
theorem anderson_judgments_match_strategy : ∀ e ∈ Examples.all, AndersonRowOK e := by decide

/-! ### The Future-Less-Vivid correlation (§4.2) -/

/-- The `flv_xmarking` tag. -/
def flvAvailableTag (e : LinguisticExample) : Option Bool :=
  match e.feature? "flv_xmarking" with
  | some "available"   => some true
  | some "unavailable" => some false
  | _                  => none

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
theorem mem_historyJones {w : Bool} {s : Index Bool ℤ} :
    w ∈ historyJones s ↔ w = s.world ∨ s.time ≤ 0 := Iff.rfl

theorem historyJones_backwardsClosed : historyJones.backwardsClosed :=
  λ _ _ _ _ hle hmem => Or.imp id (le_trans hle) hmem

/-- The utterance index; its domain is the paper's `D`. -/
def utteranceIdx : Index Bool ℤ := ⟨true, 1⟩

/-- The HP-shifted index (§3.3); its domain is `D⁺` on the O-marking route. -/
def hpIdx : Index Bool ℤ := ⟨true, 0⟩

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

end Mizuno2024
