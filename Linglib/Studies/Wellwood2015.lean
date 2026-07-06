import Linglib.Semantics.Degree.Measure
import Linglib.Semantics.Degree.Comparative
import Linglib.Semantics.Mereology
import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Kinds.MeaningPreservation
import Linglib.Features.Aktionsart
import Linglib.Core.Order.Boundedness
import Linglib.Fragments.English.Nouns
import Linglib.Fragments.English.Predicates.Verbal
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

* `comparativeTruth` / `equativeTruth`: the shared truth conditions for
  `-er` and `as` (eq. 27), instances of `Degree.maxComparative` /
  `Degree.maxEquative`; `derivation_eq_comparativeTruth` proves the
  paper's step-by-step composition (`matrixDegP`, `absDegP`, `predMod`,
  `thanClause`) yields the former.
* `nominalComparative`, `verbalComparative`, `adjectivalComparative`:
  the three domain instantiations (role × extraction).
* `coffee_much_matches` … `wooden_much_matches`: the §§2–3 felicity
  judgments predicted per-lexeme from fragment entries and substrate
  status maps; `qua_measures_vacuously_admissible` gives the
  mereological reason (antichains trivialize monotone measurement).
* `model_restricted_iff` / `dimension_tracks_domain` /
  `dimension_not_category`: §3.4 as order theory — exactly the state
  domain's model is `DimensionallyRestricted`, matching the intensive
  dimensions of exs. 82–89, while the category-based rival is refuted.
* `very_tracks_much_deletion`: the §6.3 `very` asymmetry derived from
  [bresnan-1973] Much Deletion.

## Implementation notes

Monotonicity of `A(μ)` is a felicity condition on the assignment, not
part of the denotation. Example sentences and judgments are generated
from `Data/Examples/Wellwood2015.json`; theorems consume them directly,
with lexical categories derived from `Fragments/English` entries rather
than annotated.
-/

namespace Wellwood2015

open ArgumentStructure (ThematicFrame)
open Features
open Degree
open Semantics.Kinds.MeaningPreservation (NumberFeature)

/-! ### The measured domain (§3.4) -/

/-- What a comparative measures — the ontological domain whose
    mereological structure determines the available dimensions.
    The key §3.4 insight: dimension type (intensive vs extensive)
    tracks the measured domain, not lexical category. -/
inductive MeasuredDomain where
  | entity  -- physical objects (coffee, plastic, glass)
  | event   -- events/processes (driving, singing)
  | state   -- states (heat, hardness, speed, loudness)
  deriving DecidableEq, Repr

/-- Parse a `measuredDomain` paper-feature of a generated example. -/
def measuredDomainOfFeature : String → Option MeasuredDomain
  | "entity" => some .entity
  | "event"  => some .event
  | "state"  => some .state
  | _        => none

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

/-- The equative truth condition (eq. 27.ii): `as much` compares weakly —
    some role-`a` eventuality satisfies `P` and measures at least the
    maximal as-clause degree. The same pipeline as `comparativeTruth`
    with `⪰` for `≻` ([bresnan-1973]'s `as` filling the same Det slot). -/
def equativeTruth {Ent α Measured : Type*}
    (role : Ent → α → Prop) (P : α → Prop)
    (extract : α → Measured) (μ : Measured → ℚ)
    (a b : Ent) : Prop :=
  maxEquative (fun e => role a e ∧ P e) (fun e => role b e ∧ P e)
    (fun e => μ (extract e))

/-- `-er` is strictly stronger than `as` (eq. 27.i ⇒ 27.ii). -/
theorem comparativeTruth_entails_equativeTruth {Ent α Measured : Type*}
    (role : Ent → α → Prop) (P : α → Prop)
    (extract : α → Measured) (μ : Measured → ℚ) (a b : Ent) :
    comparativeTruth role P extract μ a b → equativeTruth role P extract μ a b :=
  maxComparative_entails_maxEquative _ _ _

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

end Domains

/-! ### Mereological status (§§2–3)

The paper's two-way cross-categorial classification and its bridges to
the feature substrate. Interpretive notes: the paper does not label GA
state domains "cumulative" in Krifka's technical sense — it argues they
"form mereologies" (ordered domains with proper parts); we classify them
`.cumulative` because the structural consequence (monotonic
measurability) is the same. -/

/-- Cross-categorial mereological classification (§§2–3): `cumulative`
    domains have proper-part structure enabling monotonic measurement by
    `much` (mass nouns, atelic VPs, GA state domains); `quantized`
    domains lack it (count nouns, telic VPs, non-GA states). -/
inductive MereologicalStatus where
  | cumulative
  | quantized
  deriving DecidableEq, Repr

/-- Telicity determines status: atelic VPs are CUM, telic VPs QUA. -/
def telicityToStatus : Telicity → MereologicalStatus
  | .atelic => .cumulative
  | .telic  => .quantized

/-- Number determines status: mass CUM; count (sg/pl/neutral) QUA at the
    lexical level (plural CUM-at-plurality measures only NUMBER). -/
def numberToStatus : NumberFeature → MereologicalStatus
  | .mass    => .cumulative
  | .sg      => .quantized
  | .pl      => .quantized
  | .neutral => .quantized

/-- GA state domains form mereologies (see the section note). -/
def gradableToStatus : MereologicalStatus := .cumulative

/-- Non-GA states are atomic and unordered — QUA as the closest label. -/
def nonGradableToStatus : MereologicalStatus := .quantized

/-- Telicization (§5) shifts status from cumulative to quantized. -/
theorem telicize_shifts_status (p : AspectualProfile) (h : p.telicity = .atelic) :
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  ⟨by rw [h]; rfl, rfl⟩

/-! ### Felicity from the lexicon (§§2–3)

Each felicity observation predicted from shared substrate: fragment
entries where the lexicon has them (`coffee`, `idea`, `run`, `hot`),
the paper's feature assignment otherwise. -/

/-- `much` is predicted felicitous exactly with cumulative status. -/
def predictsFelicitous (s : MereologicalStatus) : Prop := s = .cumulative

instance : DecidablePred predictsFelicitous :=
  fun s => inferInstanceAs (Decidable (s = .cumulative))

/-- The lexical-level number feature of a fragment noun entry. -/
def nounNumber (e : English.Nouns.NounEntry) : NumberFeature :=
  match e.countable with
  | .mass  => .mass
  | .count => .sg

/-- "Al bought more coffee than Bill did" (§2.1): the fragment's mass
    entry gives cumulative status, predicting the recorded judgment. -/
theorem coffee_much_matches :
    predictsFelicitous (numberToStatus (nounNumber English.Nouns.coffee)) ↔
      Examples.felicity_mass.judgment = .acceptable := by decide

/-- "?Al has more idea than Bill does" (§2.1): count entry ⇒ quantized ⇒
    anomalous. -/
theorem idea_much_matches :
    predictsFelicitous (numberToStatus (nounNumber English.Nouns.idea)) ↔
      Examples.felicity_count.judgment = .acceptable := by decide

/-- "Al ran more than Bill did" (§2.2): `run` is an activity in the
    fragment; atelic status predicts the recorded judgment. -/
theorem run_much_matches :
    English.Predicates.Verbal.run.vendlerClass = some .activity ∧
    (predictsFelicitous (telicityToStatus .atelic) ↔
      Examples.felicity_atelic.judgment = .acceptable) :=
  ⟨rfl, by decide⟩

/-- "?Al graduated high school more than Bill did" (§2.2): telic ⇒
    quantized ⇒ anomalous. -/
theorem telic_much_matches :
    predictsFelicitous (telicityToStatus .telic) ↔
      Examples.felicity_telic.judgment = .acceptable := by decide

/-- "Al's coffee is hotter than Bill's" (§3.1): GA state domains form
    mereologies (`English.Predicates.Adjectival.hot` carries a scalar
    dimension). -/
theorem hot_much_matches :
    predictsFelicitous gradableToStatus ↔
      Examples.felicity_ga.judgment = .acceptable := by decide

/-- "?This piece of wood is more wooden than that one" (ex. 53a):
    non-GA states are atomic and unordered ⇒ anomalous. -/
theorem wooden_much_matches :
    predictsFelicitous nonGradableToStatus ↔
      Examples.felicity_nonga.judgment = .acceptable := by decide

/-- Why quantized reference blocks `much`: a quantized extension is an
    antichain, so every measure is vacuously admissible on it — monotone
    measurement cannot discriminate, leaving only counting (`many`). -/
theorem qua_measures_vacuously_admissible {α : Type*} [PartialOrder α]
    {P : α → Prop} (hQ : Mereology.QUA P) (μ : α → ℚ) :
    StrictMonoOn μ {x | P x} :=
  fun _ hx _ hy hlt => absurd hlt.le (hQ hx hy hlt.ne)

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

/-- §3.4 verified over the example annotations (exs. 82–89): the
    measured domain's order model is dimensionally restricted iff the
    observed dimension is intensive. -/
theorem dimension_tracks_domain :
    ∀ e ∈ Examples.all, ∀ m : MeasuredDomain,
      (e.feature? "measuredDomain").bind measuredDomainOfFeature = some m →
        (DimensionallyRestricted m.Model ↔
          e.feature? "intensive" = some "true") := by
  intro e he m hm
  rw [model_restricted_iff]
  revert e he m hm
  decide

example : Examples.dim_84a_fuller.feature? "measuredDomain" = some "entity" := rfl

/-- The lexicalist rival §3.4 argues against — dimension fixed by
    category — fails on the reversal data (`fuller`, ex. 84a; `more
    heat`, ex. 85a). -/
theorem dimension_not_category :
    ¬ ∀ e ∈ Examples.all, e.feature? "dataset" = some "dimension" →
      (e.feature? "category" = some "gradableAdj" ↔
        e.feature? "intensive" = some "true") := by
  decide

/-! ### Grammar shifts measurement (§5) -/

/-- Ex. (105): telicization (the directional PP) shifts cumulative to
    quantized. -/
theorem run_shift_via_telicize :
    let p : AspectualProfile := activityProfile
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  telicize_shifts_status _ rfl

/-! ### Bresnan's decomposition (§3.3) -/

/-- [bresnan-1973]'s QP `-er` + `much`, underlying `more` in all domains;
    adjectives differ only by Much Deletion (Wellwood's (74)). -/
def crossCategorialQP : Bresnan1973.QP := ⟨.er, .much⟩

/-- The surface form "more" derives from Bresnan's suppletion. -/
theorem crossCategorial_more_from_suppletion :
    Bresnan1973.suppletion crossCategorialQP = some "more" := rfl

/-! ### `very` distribution (§6.3) -/

/-- The §6.3 `very` asymmetry (exs. 117–118) follows from Much
    Deletion: `much` deletes exactly before adjectives, so only GAs host
    covert `much`, and `very` requires overt `much` everywhere else. -/
theorem very_tracks_much_deletion :
    ∀ e ∈ Examples.all, e.feature? "dataset" = some "very" →
      (e.feature? "requiresOvertMuch" = some "true" ↔
        Bresnan1973.muchDeletionApplies .much
          (adjFollows := e.feature? "category" == some "gradableAdj") = false) := by
  decide

example : Examples.very_ga.feature? "dataset" = some "very" := rfl

end Wellwood2015
