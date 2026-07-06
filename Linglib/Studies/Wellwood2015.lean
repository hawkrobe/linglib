import Linglib.Semantics.Degree.Measurement
import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Degree.Comparative
import Linglib.Data.Examples.Wellwood2015
import Linglib.Studies.Bresnan1973

/-!
# [wellwood-2015]: On the Semantics of Comparison Across Categories

Nominal ("more coffee"), verbal ("ran more"), and adjectival ("hotter")
comparatives share one DegP pipeline: covert `much` denotes an
assignment-supplied monotonic measure function (eqs. 7/28) and `-er`
compares strictly against the maximal than-clause degree (eq. 38;
[von-stechow-1984], [rullmann-1995]), yielding the same truth condition
in all three domains (eqs. 42/48/65). Felicity with `much` tracks
mereological status; dimension availability tracks the measured domain,
not lexical category (§3.4).

## Main declarations

* `comparativeTruth`: the shared truth condition, an instance of
  `Degree.maxComparative`; `derivation_eq_comparativeTruth` proves the
  paper's step-by-step composition (`matrixDegP`, `absDegP`, `predMod`,
  `thanClause`) yields it, and `comparativeTruth_max` collapses it to
  direct measure comparison under unique eventualities.
* `nominalComparative`, `verbalComparative`, `adjectivalComparative`:
  the three domain instantiations (role × extraction).
* `felicity_matches_data`: `much`-felicity predicted from mereological
  status across the §§2–3 data; `qua_measures_vacuously_admissible` and
  `cum_thanDegrees_no_max` give the mereological reason (antichains
  trivialize monotone measurement; cumulative supply keeps the scale
  maximless).
* `model_restricted_iff` / `dimension_tracks_domain` /
  `dimension_not_category`: §3.4 as order theory — exactly the state
  domain's model is `DimensionallyRestricted`, matching the intensive
  dimensions of exs. 82–89, while the category-based rival is refuted.
* `very_tracks_much_deletion`: the §6.3 `very` asymmetry derived from
  [bresnan-1973] Much Deletion.

## Implementation notes

Monotonicity of `A(μ)` is a felicity condition on the assignment, not
part of the denotation. Example rows are generated from
`Data/Examples/Wellwood2015.json` and projected into typed data via
`paperFeatures` adapters.
-/

namespace Wellwood2015

open ArgumentStructure (ThematicFrame)
open Semantics.Measurement
open Features
open Degree (maxComparative maxComparative_unique)

/-! ### Lexical categories -/

/-- Lexical categories relevant to the cross-categorial analysis. -/
inductive LexCat where
  | massNoun       -- coffee, rock, gold
  | countNoun      -- cup, idea
  | atelicVP       -- ran, slept, ran in the park
  | telicVP        -- ran to the park, graduated high school
  | gradableAdj    -- hot, tall, heavy
  | nonGradableAdj -- wooden, triangular
  deriving DecidableEq, Repr

/-- Observed felicity of `much`/`more` with a lexical category (§§2–3). -/
structure MuchFelicityDatum where
  category : LexCat
  felicitousWithMuch : Bool
  deriving DecidableEq, Repr

/-- The ontological domain a comparative measures; dimension type tracks
    this, not the lexical category (§3.4). -/
inductive MeasuredDomain where
  | entity  -- physical objects (coffee, plastic, glass)
  | event   -- events/processes (driving, singing)
  | state   -- states (heat, hardness, speed, loudness)
  deriving DecidableEq, Repr

/-- A §3.4 dimension observation (exs. 82–89): form, category, measured
    domain, and dimension type. -/
structure DimensionReversalDatum where
  form : String
  category : LexCat
  measuredDomain : MeasuredDomain
  intensive : Bool
  deriving DecidableEq, Repr

/-! ### Example data

Typed rows projected from `Data.Examples.Wellwood2015` via
`paperFeatures`; the anonymous `example`s guard against a silently empty
adapter image. -/

open Data.Examples (LinguisticExample)

/-- Parse a `category` paper-feature. -/
def lexCatOfFeature : String → Option LexCat
  | "massNoun"       => some .massNoun
  | "countNoun"      => some .countNoun
  | "atelicVP"       => some .atelicVP
  | "telicVP"        => some .telicVP
  | "gradableAdj"    => some .gradableAdj
  | "nonGradableAdj" => some .nonGradableAdj
  | _                => none

/-- Parse a `measuredDomain` paper-feature. -/
def measuredDomainOfFeature : String → Option MeasuredDomain
  | "entity" => some .entity
  | "event"  => some .event
  | "state"  => some .state
  | _        => none

/-- Project a `muchFelicity` example; felicity is an `acceptable` judgment. -/
def MuchFelicityDatum.ofExample (e : LinguisticExample) : Option MuchFelicityDatum := do
  guard (e.feature? "dataset" = some "muchFelicity")
  let c ← lexCatOfFeature (← e.feature? "category")
  return ⟨c, e.judgment == .acceptable⟩

/-- The six felicity observations of §§2–3. -/
def muchFelicityData : List MuchFelicityDatum :=
  Examples.all.filterMap MuchFelicityDatum.ofExample

example : (⟨.massNoun, true⟩ : MuchFelicityDatum) ∈ muchFelicityData := by decide

/-- Project a `dimension` example (exs. 82–89). -/
def DimensionReversalDatum.ofExample (e : LinguisticExample) :
    Option DimensionReversalDatum := do
  guard (e.feature? "dataset" = some "dimension")
  let c ← lexCatOfFeature (← e.feature? "category")
  let m ← measuredDomainOfFeature (← e.feature? "measuredDomain")
  return ⟨e.primaryText, c, m, e.feature? "intensive" == some "true"⟩

/-- The ten dimension observations of §3.4. -/
def dimensionReversalData : List DimensionReversalDatum :=
  Examples.all.filterMap DimensionReversalDatum.ofExample

example : (⟨"fuller", .gradableAdj, .entity, false⟩ : DimensionReversalDatum) ∈
    dimensionReversalData := by decide

/-! ### The comparative truth condition (§§2.1–3.2) -/

/-- The truth condition shared by eqs. 42/48/65: some role-`a`
    eventuality satisfies `P` and measures strictly above the maximal
    than-clause degree. The domains differ only in role (Agent/Holder)
    and extraction (`themeOf`/`id`). -/
def comparativeTruth {Ent α Measured : Type*}
    (role : Ent → α → Prop) (P : α → Prop)
    (extract : α → Measured) (μ : Measured → ℚ)
    (a b : Ent) : Prop :=
  maxComparative (fun e => role a e ∧ P e) (fun e => role b e ∧ P e)
    (fun e => μ (extract e))

/-- Unique matrix and than eventualities collapse the comparative to
    direct measure comparison. -/
theorem comparativeTruth_max {Ent α Measured : Type*}
    {role : Ent → α → Prop} {P : α → Prop}
    {extract : α → Measured} {μ : Measured → ℚ}
    {a b : Ent} {ea eb : α}
    (ha : role a ea ∧ P ea)
    (ha_unique : ∀ e, role a e → P e → e = ea)
    (hb : role b eb ∧ P eb)
    (hb_unique : ∀ e, role b e → P e → e = eb) :
    comparativeTruth role P extract μ a b ↔
      μ (extract eb) < μ (extract ea) :=
  maxComparative_unique ha (fun e he => ha_unique e he.1 he.2)
    hb (fun e he => hb_unique e he.1 he.2)

/-! ### The compositional derivation (§§2.1–3.2)

The paper's derivation steps as combinators, proven to compose to
`comparativeTruth`. -/

section Derivation
variable {Ent α : Type*}

/-- ⟦much_μ⟧^A = A(μ) composed with ⟦-er⟧: a strict degree threshold
    (37.i/45.i). -/
def matrixDegP (μ : α → ℚ) (δ : ℚ) (e : α) : Prop := μ e > δ

/-- ABS (38.ii): the weak degree threshold of the than-clause. -/
def absDegP (μ : α → ℚ) (d : ℚ) (e : α) : Prop := μ e ≥ d

/-- Predicate Modification: intersective conjunction (37.iii/45.iii). -/
def predMod (P Q : α → Prop) (e : α) : Prop := P e ∧ Q e

/-- The than-clause (39–41/47): degree abstraction over the ∃-closed
    ABS-composed clause. -/
def thanClause (role : Ent → α → Prop) (P : α → Prop) (μ : α → ℚ)
    (b : Ent) : Set ℚ :=
  {d | ∃ e, role b e ∧ predMod P (absDegP μ d) e}

/-- The matrix clause (37.viii/45.vi): ∃-closure over the PM of the base
    predicate with the DegP at standard δ. -/
def matrixClause (role : Ent → α → Prop) (P : α → Prop) (μ : α → ℚ)
    (a : Ent) (δ : ℚ) : Prop :=
  ∃ e, role a e ∧ predMod P (matrixDegP μ δ) e

/-- The derivation composes: max-selecting the than-clause standard for
    the matrix clause is `comparativeTruth` (eqs. 42/48/65). -/
theorem derivation_eq_comparativeTruth {Measured : Type*}
    (role : Ent → α → Prop) (P : α → Prop)
    (extract : α → Measured) (μ : Measured → ℚ) (a b : Ent) :
    (∃ δ, IsGreatest (thanClause role P (fun e => μ (extract e)) b) δ ∧
        matrixClause role P (fun e => μ (extract e)) a δ) ↔
      comparativeTruth role P extract μ a b := by
  simp only [comparativeTruth, maxComparative, Degree.thanDegrees, thanClause,
    matrixClause, predMod, matrixDegP, absDegP, ge_iff_le, gt_iff_lt, and_assoc]

end Derivation

/-! ### Three domain instantiations -/

section Domains
variable {Entity Time : Type*} [LinearOrder Time]

/-- Nominal comparative (§2.1, eq. 42): Agent role, entities measured via
    `themeOf`. -/
def nominalComparative (frame : ThematicFrame Entity Time)
    (P : Event Time → Prop) (themeOf : Event Time → Entity)
    (μ : Entity → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P themeOf μ a b

/-- Verbal comparative (§2.2, eq. 48): Agent role, events measured directly. -/
def verbalComparative (frame : ThematicFrame Entity Time)
    (P : Event Time → Prop) (μ : Event Time → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P id μ a b

/-- Adjectival comparative (§3.2, eq. 65): Holder role, states measured
    directly. -/
def adjectivalComparative (frame : ThematicFrame Entity Time)
    (P : Event Time → Prop) (μ : Event Time → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.holder P id μ a b

/-- Nominal comparative under maximality: `μ(theme(eb)) < μ(theme(ea))`. -/
theorem nominal_max_reduces {frame : ThematicFrame Entity Time}
    {P : Event Time → Prop} {themeOf : Event Time → Entity} {μ : Entity → ℚ}
    {a b : Entity} {ea eb : Event Time}
    (ha : frame.agent a ea ∧ P ea)
    (ha_unique : ∀ e, frame.agent a e → P e → e = ea)
    (hb : frame.agent b eb ∧ P eb)
    (hb_unique : ∀ e, frame.agent b e → P e → e = eb) :
    nominalComparative frame P themeOf μ a b ↔ μ (themeOf eb) < μ (themeOf ea) :=
  comparativeTruth_max ha ha_unique hb hb_unique

/-- Verbal comparative under maximality: `μ(eb) < μ(ea)`. -/
theorem verbal_max_reduces {frame : ThematicFrame Entity Time}
    {P : Event Time → Prop} {μ : Event Time → ℚ}
    {a b : Entity} {ea eb : Event Time}
    (ha : frame.agent a ea ∧ P ea)
    (ha_unique : ∀ e, frame.agent a e → P e → e = ea)
    (hb : frame.agent b eb ∧ P eb)
    (hb_unique : ∀ e, frame.agent b e → P e → e = eb) :
    verbalComparative frame P μ a b ↔ μ eb < μ ea :=
  comparativeTruth_max ha ha_unique hb hb_unique

/-- Adjectival comparative under maximality: `μ(sb) < μ(sa)`. -/
theorem adjectival_max_reduces {frame : ThematicFrame Entity Time}
    {P : Event Time → Prop} {μ : Event Time → ℚ}
    {a b : Entity} {sa sb : Event Time}
    (ha : frame.holder a sa ∧ P sa)
    (ha_unique : ∀ s, frame.holder a s → P s → s = sa)
    (hb : frame.holder b sb ∧ P sb)
    (hb_unique : ∀ s, frame.holder b s → P s → s = sb) :
    adjectivalComparative frame P μ a b ↔ μ sb < μ sa :=
  comparativeTruth_max ha ha_unique hb hb_unique

/-- Under maximality, every domain's comparative is
    `Degree.comparativeSem` ([schwarzschild-2008]) on measured values. -/
theorem max_eq_comparativeSem {Measured : Type*}
    {role : Entity → Event Time → Prop}
    {P : Event Time → Prop}
    {extract : Event Time → Measured}
    {μ : Measured → ℚ}
    {a b : Entity} {ea eb : Event Time}
    (ha : role a ea ∧ P ea)
    (ha_unique : ∀ e, role a e → P e → e = ea)
    (hb : role b eb ∧ P eb)
    (hb_unique : ∀ e, role b e → P e → e = eb) :
    comparativeTruth role P extract μ a b ↔
      Degree.comparativeSem (μ ∘ extract) ea eb .positive :=
  comparativeTruth_max ha ha_unique hb hb_unique

end Domains

/-! ### Theory–data bridges (§§2–3) -/

/-- Map `LexCat` to `MereologicalStatus` using the theory's bridges. -/
def lexCatToStatus : LexCat → MereologicalStatus
  | .massNoun       => numberToStatus .mass
  | .countNoun      => numberToStatus .sg
  | .atelicVP       => telicityToStatus .atelic
  | .telicVP        => telicityToStatus .telic
  | .gradableAdj    => gradableToStatus
  | .nonGradableAdj => nonGradableToStatus

/-- `much` is predicted felicitous exactly with cumulative status. -/
def predictsFelicitous (s : MereologicalStatus) : Prop := s = .cumulative

instance : DecidablePred predictsFelicitous :=
  fun s => inferInstanceAs (Decidable (s = .cumulative))

/-- Predicted felicity matches the observed judgment for all six
    categories (§§2–3). -/
theorem felicity_matches_data :
    ∀ d ∈ muchFelicityData,
      (predictsFelicitous (lexCatToStatus d.category) ↔
        d.felicitousWithMuch = true) := by
  decide

/-- Why quantized reference blocks `much`: a quantized extension is an
    antichain, so every measure is vacuously admissible on it — monotone
    measurement cannot discriminate, leaving only counting (`many`). -/
theorem qua_measures_vacuously_admissible {α : Type*} [PartialOrder α]
    {P : α → Prop} (hQ : Mereology.QUA P) (μ : α → ℚ) :
    StrictMonoOn μ {x | P x} :=
  fun _ hx _ hy hlt => absurd hlt.le (hQ hx hy hlt.ne)

/-- Why cumulative reference keeps the `much` scale open: with disjoint
    supply, the degree set of an extensively measured cumulative predicate
    has no maximum (via `Mereology.cum_measure_unbounded`). -/
theorem cum_thanDegrees_no_max {α : Type*} [SemilatticeSup α]
    {μ : α → ℚ} [Mereology.ExtMeasure α μ] {P : α → Prop}
    (hCum : Mereology.CUM P) {δ : ℚ} (hδ : 0 < δ)
    (hSupply : ∀ x, P x → ∃ y, P y ∧ ¬ Mereology.Overlap x y ∧ δ ≤ μ y)
    {x₀ : α} (hx₀ : P x₀) :
    ¬ ∃ M, IsGreatest (Degree.thanDegrees P μ) M := by
  rintro ⟨M, _, hub⟩
  obtain ⟨z, hz, hgt⟩ :=
    Mereology.DimensionChain.cum_measure_unbounded hCum hδ hSupply x₀ hx₀ M
  exact absurd (hub ⟨z, hz, le_refl _⟩) (not_le.mpr hgt)

/-- Mass/atelic/GA share cumulative status and count/telic/non-GA
    quantized, via independent substrate routes (§§2–3). -/
theorem cross_categorial_parallel :
    lexCatToStatus .massNoun = lexCatToStatus .atelicVP ∧
    lexCatToStatus .atelicVP = lexCatToStatus .gradableAdj ∧
    lexCatToStatus .countNoun = lexCatToStatus .telicVP ∧
    lexCatToStatus .telicVP = lexCatToStatus .nonGradableAdj :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Dimensional restriction (§3.4) -/

/-- Order model of a measured domain: states are linearly ordered;
    entity and event domains have incomparable parts (weight × volume,
    distance × duration). -/
abbrev MeasuredDomain.Model : MeasuredDomain → Type
  | .state  => ℚ
  | .entity => ℚ × ℚ
  | .event  => ℚ × ℚ

instance : (m : MeasuredDomain) → Preorder m.Model
  | .state  => inferInstanceAs (Preorder ℚ)
  | .entity => inferInstanceAs (Preorder (ℚ × ℚ))
  | .event  => inferInstanceAs (Preorder (ℚ × ℚ))

/-- §3.4 as order theory: exactly the state domain is dimensionally
    restricted. -/
theorem model_restricted_iff : ∀ m : MeasuredDomain,
    DimensionallyRestricted m.Model ↔ m = .state
  | .state  => iff_of_true (linearOrder_dimensionallyRestricted (α := ℚ)) rfl
  | .entity => iff_of_false prod_not_dimensionallyRestricted (by decide)
  | .event  => iff_of_false prod_not_dimensionallyRestricted (by decide)

/-- Admissible measures agree exactly on the state-measuring comparatives
    (exs. 82–89): the observed dimension is intensive iff the measured
    domain's order model is dimensionally restricted. -/
theorem dimension_tracks_domain :
    ∀ d ∈ dimensionReversalData,
      (DimensionallyRestricted d.measuredDomain.Model ↔ d.intensive = true) := by
  intro d hd
  rw [model_restricted_iff]
  revert d hd
  decide

/-- The lexicalist rival: dimension fixed iff the category is GA. -/
def categoryRestricted (c : LexCat) : Prop := c = .gradableAdj

instance : DecidablePred categoryRestricted :=
  fun c => inferInstanceAs (Decidable (c = .gradableAdj))

/-- The category predictor fails on the reversal data (`fuller`, ex. 84a). -/
theorem dimension_not_category :
    ¬ ∀ d ∈ dimensionReversalData,
      (categoryRestricted d.category ↔ d.intensive = true) := by
  decide

/-! ### Grammar shifts measurement (§5) -/

/-- Ex. (104): the plural morpheme shifts cumulative to quantized. -/
theorem rock_shift_status :
    numberToStatus .mass = .cumulative ∧ numberToStatus .pl = .quantized :=
  ⟨rfl, rfl⟩

/-- Ex. (105): telicization (the directional PP) shifts cumulative to
    quantized. -/
theorem run_shift_via_telicize :
    let p : AspectualProfile := activityProfile
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  telicize_shifts_status _ rfl

/-- Atelicization (the progressive) reverses the (105) shift. -/
theorem build_shift_via_atelicize :
    let p : AspectualProfile := accomplishmentProfile
    telicityToStatus p.telicity = .quantized ∧
    telicityToStatus p.atelicize.telicity = .cumulative :=
  atelicize_shifts_status _ rfl

/-! ### Bresnan's decomposition (§3.3) -/

/-- [bresnan-1973]'s QP `-er` + `much`, underlying `more` in all domains;
    adjectives differ only by Much Deletion (Wellwood's (74)). -/
def crossCategorialQP : Bresnan1973.QP := ⟨.er, .much⟩

/-- The surface form "more" derives from Bresnan's suppletion. -/
theorem crossCategorial_more_from_suppletion :
    Bresnan1973.suppletion crossCategorialQP = some "more" := rfl

/-- Covert `much` on GAs (§6.3) is Much Deletion: `much` → ∅ before an
    adjective. -/
theorem covert_much_is_bresnan_deletion :
    Bresnan1973.muchDeletionApplies .much (adjFollows := true) = true := rfl

/-- N/V retain overt `much`: Much Deletion only applies before an adjective. -/
theorem overt_much_no_deletion :
    Bresnan1973.muchDeletionApplies .much (adjFollows := false) = false := rfl

/-! ### `very` distribution (§6.3) -/

/-- Whether `very` requires overt `much` (§6.3, exs. 117–118). -/
structure VeryDistributionDatum where
  category : LexCat
  requiresOvertMuch : Bool
  deriving DecidableEq, Repr

/-- Project a `very` example. -/
def VeryDistributionDatum.ofExample (e : LinguisticExample) :
    Option VeryDistributionDatum := do
  guard (e.feature? "dataset" = some "very")
  let c ← lexCatOfFeature (← e.feature? "category")
  return ⟨c, e.feature? "requiresOvertMuch" == some "true"⟩

/-- The three `very` observations of §6.3. -/
def veryDistributionData : List VeryDistributionDatum :=
  Examples.all.filterMap VeryDistributionDatum.ofExample

example : (⟨.gradableAdj, false⟩ : VeryDistributionDatum) ∈ veryDistributionData := by
  decide

/-- The `very` asymmetry follows from Much Deletion: only GAs host
    covert `much`. -/
theorem very_tracks_much_deletion :
    ∀ d ∈ veryDistributionData,
      d.requiresOvertMuch =
        !(Bresnan1973.muchDeletionApplies .much
            (adjFollows := d.category == .gradableAdj)) := by
  decide

end Wellwood2015
