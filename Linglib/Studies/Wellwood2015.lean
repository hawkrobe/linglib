import Linglib.Semantics.Degree.Measurement
import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Degree.Comparative
import Linglib.Data.Examples.Wellwood2015
import Linglib.Studies.Bresnan1973

/-!
# [wellwood-2015]: On the Semantics of Comparison Across Categories

Data and verification theorems from [wellwood-2015]. All comparative
sentences — nominal, verbal, and adjectival — share a uniform DegP
pipeline in which `much` introduces a monotonic measure function μ.
The cross-categorial parallel (mass/atelic/GA vs count/telic/non-GA)
follows from mereological status, and dimension availability (§3.4)
tracks what is measured (states vs entities/events), not lexical
category.

## Data sources

- §2.1: nominal comparatives (mass vs count nouns)
- §2.2: verbal comparatives (atelic vs telic VPs)
- §3.1–3.2: adjectival comparatives (gradable vs non-gradable adjectives)
- §3.3: morphosyntax — `more` = `much` + `-er` ([bresnan-1973])
- §3.4: dimension availability tracks the measured domain (exs. 82–89)
- §5: grammar shifts measurement (exs. 104–105)
- §6.3: `very` distribution and covert `much` (exs. 117–118)

## Compositional pieces

1. `⟦much_μ⟧^A = A(μ)` — the measure function comes from the variable
   assignment (eqs. 7/28); its monotonicity is a felicity condition on
   the assignment, not part of the denotation
2. `⟦-er⟧` — strict comparison (>) against a standard
3. `⟦than⟧ = λD. max(D)` — the standard is the maximal degree of the
   than-clause degree set (eq. 38.i; [von-stechow-1984], [rullmann-1995])
4. `⟦ABS⟧ = λg.λd.λα. g(α) ≥ d` — links degrees to eventuality
   predicates in the than-clause (eq. 38.ii): matrix `>`, standard `≥`
5. Predicate Modification conjoins DegP with the base predicate;
   existential closure applies to the matrix eventuality

The result, for all three domains (eqs. 42, 48, 65):

    ∃α. role(a, α) ∧ P(α) ∧ μ(extract(α)) >
        max{d | ∃α'. role(b, α') ∧ P(α') ∧ μ(extract(α')) ≥ d}

formalized as `comparativeTruth` via the substrate's
`Degree.maxComparative`. Under unique-eventuality assumptions it
collapses to `μ(extract(α_a)) > μ(extract(α_b))` (`comparativeTruth_max`),
the direct comparison `Degree.comparativeSem` ([schwarzschild-2008]).
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

/-! ### Felicity with `much`/`more` (§2.1, §2.2, §3.1–3.2) -/

/-- Observed felicity of `much`/`more` with a lexical category.

    - "Al bought more coffee than Bill did." ✓ (mass)
    - "?Al has more idea than Bill does." ✗ (count)
    - "Al ran more than Bill did." ✓ (atelic)
    - "?Al graduated high school more than Bill did." ✗ (telic)
    - "Al's coffee is hotter than Bill's." ✓ (gradable)
    - "?This piece of wood is more wooden than that one." ✗ (non-gradable, ex. 53a) -/
structure MuchFelicityDatum where
  category : LexCat
  felicitousWithMuch : Bool
  deriving DecidableEq, Repr

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

/-- A dimension datum (§3.4, exs. 82–89): a comparative form, its lexical
    category, the domain it measures, and whether the available dimension
    is intensive. The reversal cases — `fuller`/`heavier` (GAs measuring
    entities → extensive, ex. 84) and `more heat`/`more firmness` (nouns
    measuring states → intensive, ex. 85) — cross category against domain. -/
structure DimensionReversalDatum where
  form : String
  category : LexCat
  measuredDomain : MeasuredDomain
  intensive : Bool
  deriving DecidableEq, Repr

/-! ### Example data

The paper's examples live in `Data/Examples/Wellwood2015.json` (generated
module `Data.Examples.Wellwood2015`); the adapters below project the
`paperFeatures` of each dataset into the typed rows the verification
theorems quantify over. Positive-witness examples guard against a
silently empty adapter image. -/

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

/-- Adapter: a `muchFelicity` example as a typed row; felicity is an
    `acceptable` judgment. -/
def MuchFelicityDatum.ofExample (e : LinguisticExample) : Option MuchFelicityDatum := do
  guard (e.feature? "dataset" = some "muchFelicity")
  let c ← lexCatOfFeature (← e.feature? "category")
  return ⟨c, e.judgment == .acceptable⟩

/-- The six felicity observations of §§2–3. -/
def muchFelicityData : List MuchFelicityDatum :=
  Examples.all.filterMap MuchFelicityDatum.ofExample

example : (⟨.massNoun, true⟩ : MuchFelicityDatum) ∈ muchFelicityData := by decide

/-- Adapter: a `dimension` example (exs. 82–89) as a typed row. -/
def DimensionReversalDatum.ofExample (e : LinguisticExample) :
    Option DimensionReversalDatum := do
  guard (e.feature? "dataset" = some "dimension")
  let c ← lexCatOfFeature (← e.feature? "category")
  let m ← measuredDomainOfFeature (← e.feature? "measuredDomain")
  return ⟨e.primaryText, c, m, e.feature? "intensive" == some "true"⟩

/-- The ten dimension observations of §3.4 (exs. 82–89). -/
def dimensionReversalData : List DimensionReversalDatum :=
  Examples.all.filterMap DimensionReversalDatum.ofExample

example : (⟨"fuller", .gradableAdj, .entity, false⟩ : DimensionReversalDatum) ∈
    dimensionReversalData := by decide

/-! ### Comparative derivations (§2.1–2.3, §3.2)

### Nominal comparative derivation (§2.1, eqs. 36–42)

    "Al drank more coffee than Bill did"

    Bottom-up composition (eq. 37):

    1. ⟦Deg'⟧^A = λd.λα. A(μ)(α) > d                     (eq. 37.i: IE, FA)
    2. ⟦DegP⟧^A = λα. A(μ)(α) > δ                         (eq. 37.ii: FA with δ)
    3. ⟦NP⟧^A = λy. coffee(y) ∧ A(μ)(y) > δ               (eq. 37.iii: PM)
    4. ⟦eP⟧^A = εy[coffee(y) ∧ A(μ)(y) > δ]               (eq. 37.iv: ε)
    5. ⟦VP⟧^A = λe. drink(e)(εy[...])                      (eq. 37.v: FA)
    6. ⟦vP⟧^A = λx.λe. Agent(e)(x) ∧ VP(e)                (eq. 37.vi: EI)
    7. ⟦S⟧^A = λe. Agent(e)(a) ∧ VP(e)                     (eq. 37.vii: FA)
    8. = ⊤ iff ∃e[Agent(e)(a) ∧ ...]                       (eq. 37.viii: ∃-closure)

    Than-clause (eqs. 39–41):
    δ = max(λd.∃e[Agent(e)(b) ∧ drink(e)(εy[coffee(y) ∧ A(μ)(y) ≥ d])])

    Full truth conditions (eq. 42):
    ∃e[Agent(e)(a) ∧ drink(e)(εx[coffee(x) ∧ A(μ)(x) >
      max(λd.∃e'[Agent(e')(b) ∧ drink(e')(εy[coffee(y) ∧ A(μ)(y) ≥ d])])])]

    Abstracting away ε, with `themeOf` extracting the measured entity:
    ∃ea. Agent(a, ea) ∧ P(ea) ∧ μ(theme(ea)) >
      max{d | ∃eb. Agent(b, eb) ∧ P(eb) ∧ μ(theme(eb)) ≥ d}

### Verbal comparative derivation (§2.2, eqs. 43–48)

    "Al ran more than Bill did"

    1. ⟦Deg'⟧^A = λd.λα. A(μ)(α) > d                     (eq. 45.i)
    2. ⟦DegP⟧^A = λα. A(μ)(α) > δ                         (eq. 45.ii)
    3. ⟦VP⟧^A = λe. run(e) ∧ A(μ)(e) > δ                  (eq. 45.iii: PM)
    4. ⟦vP⟧^A = λx.λe. Agent(e)(x) ∧ run(e) ∧ A(μ)(e) > δ (eq. 45.iv: EI)
    5. ⟦S⟧^A = λe. Agent(e)(a) ∧ run(e) ∧ A(μ)(e) > δ     (eq. 45.v: FA)
    6. = ⊤ iff ∃e[Agent(e)(a) ∧ run(e) ∧ A(μ)(e) > δ]     (eq. 45.vi: ∃-closure)

    Than-clause (eq. 47):
    δ = max(λd.∃e[Agent(e)(b) ∧ run(e) ∧ A(μ)(e) ≥ d])

    Full truth conditions (eq. 48):
    ∃e'[Agent(e')(a) ∧ run(e') ∧ A(μ)(e') >
      max(λd.∃e[Agent(e)(b) ∧ run(e) ∧ A(μ)(e) ≥ d])]

### Adjectival comparative derivation (§3.2, eqs. 57–65)

    "Al's coffee is hotter than Bill's"

    1. ⟦hot⟧ = λs.hot(s)                                   (eq. 57a)
    2. `-er` composes with `much` first, and the resulting
       Deg' = λd.λs. A(μ)(s) > d combines with the GA by PM
    3. ⟦AP⟧ = λs. hot(s) ∧ A(μ)(s) > δ                    (eq. 61.iii)
    4. ∃s[Holder(s)(a) ∧ hot(s) ∧ A(μ)(s) > δ]             (eq. 65)
-/

/-! ### The comparative truth condition -/

/-- The compositional comparative truth condition (eqs. 42, 48, 65):
    "a V-s more P than b does" is true iff some a-eventuality satisfies
    `P` and its measured value strictly exceeds the maximum of the
    than-clause degree set — `Degree.maxComparative` with role-restricted
    matrix and than-clause predicates and measure `μ ∘ extract`.

    The three domains differ only in the thematic role, extraction
    function, and measured ontological sort:

    | Domain     | role   | extract  | Measured | Example            |
    |------------|--------|----------|----------|--------------------|
    | Nominal    | Agent  | themeOf  | Entity   | "more coffee than" |
    | Verbal     | Agent  | id       | Event    | "ran more than"    |
    | Adjectival | Holder | id       | State    | "hotter than"      | -/
def comparativeTruth {Ent α Measured : Type*}
    (role : Ent → α → Prop) (P : α → Prop)
    (extract : α → Measured) (μ : Measured → ℚ)
    (a b : Ent) : Prop :=
  maxComparative (fun e => role a e ∧ P e) (fun e => role b e ∧ P e)
    (fun e => μ (extract e))

/-- Maximality reduction: when `a` and `b` each have a unique
    P-eventuality, the comparative reduces to direct measure comparison
    (`Degree.maxComparative_unique`). -/
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

/-! ### Three domain instantiations -/

section Domains
variable {Entity Time : Type*} [LinearOrder Time]

/-- Nominal comparative (§2.1, eq. 42):
    "Al bought more coffee than Bill did."

    Measured domain: entities (via `themeOf`). Role: Agent. -/
def nominalComparative (frame : ThematicFrame Entity Time)
    (P : Event Time → Prop) (themeOf : Event Time → Entity)
    (μ : Entity → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P themeOf μ a b

/-- Verbal comparative (§2.2, eq. 48):
    "Al ran more than Bill did."

    Measured domain: events directly (extract = id). Role: Agent. -/
def verbalComparative (frame : ThematicFrame Entity Time)
    (P : Event Time → Prop) (μ : Event Time → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P id μ a b

/-- Adjectival comparative (§3.2, eq. 65):
    "This coffee is hotter than that coffee."

    Measured domain: states directly (extract = id). Role: Holder. -/
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

/-- Under maximality, every domain's comparative is the direct comparison
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

/-- The theory's felicity prediction: `much` requires mereological
    structure, i.e. cumulative status. -/
def predictsFelicitous (s : MereologicalStatus) : Prop := s = .cumulative

instance : DecidablePred predictsFelicitous :=
  fun s => inferInstanceAs (Decidable (s = .cumulative))

/-- §§2–3 verified: the predicted felicity matches the observed judgment
    for all six lexical categories. -/
theorem felicity_matches_data :
    ∀ d ∈ muchFelicityData,
      (predictsFelicitous (lexCatToStatus d.category) ↔
        d.felicitousWithMuch = true) := by
  decide

/-- The cross-categorial parallel (§§2–3): mass nouns, atelic VPs, and
    GAs share cumulative status; count nouns, telic VPs, and non-GAs
    share quantized status — each derived through an independent
    substrate route (number, telicity, gradability). -/
theorem cross_categorial_parallel :
    lexCatToStatus .massNoun = lexCatToStatus .atelicVP ∧
    lexCatToStatus .atelicVP = lexCatToStatus .gradableAdj ∧
    lexCatToStatus .countNoun = lexCatToStatus .telicVP ∧
    lexCatToStatus .telicVP = lexCatToStatus .nonGradableAdj :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Dimensional restriction (§3.4)

§3.4's generalization: available dimensions track the measured domain.
State domains afford exactly one dimension; entity/event domains afford
several (weight, volume; distance, duration). Order-theoretically:
state domains are linearly ordered, so any two admissible measures
agree (`Semantics.Measurement.linearOrder_dimensionallyRestricted`);
entity/event domains have incomparable parts, over which admissible
measures can disagree (`Semantics.Measurement.prod_not_dimensionallyRestricted`). -/

/-- The domain-based §3.4 predictor: the dimension is intensive (fixed)
    iff the measured domain is a state domain. Backed by
    `linearOrder_dimensionallyRestricted` (states) and
    `prod_not_dimensionallyRestricted` (entities/events). -/
def domainRestricted (m : MeasuredDomain) : Prop := m = .state

instance : DecidablePred domainRestricted :=
  fun m => inferInstanceAs (Decidable (m = .state))

/-- §3.4 verified: across all ten dimension data (exs. 82–89), intensive
    dimensions occur exactly in state-measuring comparatives. -/
theorem dimension_tracks_domain :
    ∀ d ∈ dimensionReversalData,
      (domainRestricted d.measuredDomain ↔ d.intensive = true) := by
  decide

/-- The lexicalist rival §3.4 argues against: dimension fixed by lexical
    category (GAs and only GAs have a lexically fixed dimension). -/
def categoryRestricted (c : LexCat) : Prop := c = .gradableAdj

instance : DecidablePred categoryRestricted :=
  fun c => inferInstanceAs (Decidable (c = .gradableAdj))

/-- §3.4's argument-by-reversal: the category-based predictor fails on
    the reversal data — `fuller` is a GA measuring entities (extensive,
    ex. 84a), `more heat` a noun measuring states (intensive, ex. 85a). -/
theorem dimension_not_category :
    ¬ ∀ d ∈ dimensionReversalData,
      (categoryRestricted d.category ↔ d.intensive = true) := by
  decide

/-! ### Grammar shifts measurement (§5)

(104) "more rock" (WEIGHT/VOLUME, *NUMBER) vs "more rocks"
(*WEIGHT/*VOLUME, NUMBER): the plural shifts mass to count.
(105) "ran in the park more" (DISTANCE/DURATION/NUMBER) vs "ran to the
park more" (*DISTANCE/*DURATION, NUMBER): the directional PP shifts
atelic to telic. Both shifts flip mereological status, blocking the
extensive dimensions. -/

/-- Ex. (104): the plural morpheme shifts cumulative to quantized. -/
theorem rock_shift_status :
    numberToStatus .mass = .cumulative ∧ numberToStatus .pl = .quantized :=
  ⟨rfl, rfl⟩

/-- Ex. (105): telicization (the directional PP) shifts cumulative to
    quantized, via `AspectualProfile.telicize` on the activity profile. -/
theorem run_shift_via_telicize :
    let p : AspectualProfile := activityProfile
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  telicize_shifts_status _ rfl

/-- Atelicization (e.g. the progressive) shifts quantized back to
    cumulative, via `AspectualProfile.atelicize` on the accomplishment
    profile — the reverse of the (105) shift. -/
theorem build_shift_via_atelicize :
    let p : AspectualProfile := accomplishmentProfile
    telicityToStatus p.telicity = .quantized ∧
    telicityToStatus p.atelicize.telicity = .cumulative :=
  atelicize_shifts_status _ rfl

/-! ### Bresnan's decomposition (§3.3) -/

/-- [bresnan-1973] decomposition: `more` = `-er` + `much`. The SAME QP
    underlies `more` across nominal ("more coffee"), verbal ("ran more"),
    and adverbial ("more quickly") domains; adjectival comparatives
    ("taller") differ only by Much Deletion — `much` → ∅ before an
    adjective (Wellwood's (74)). The QP structure and suppletion are in
    `Bresnan1973`. -/
def crossCategorialQP : Bresnan1973.QP := ⟨.er, .much⟩

/-- The surface form "more" derives from Bresnan's suppletion. -/
theorem crossCategorial_more_from_suppletion :
    Bresnan1973.suppletion crossCategorialQP = some "more" := rfl

/-- Covert `much` on GAs (§6.3) is Much Deletion: `much` → ∅ before an
    adjective (Wellwood's (74)). -/
theorem covert_much_is_bresnan_deletion :
    Bresnan1973.muchDeletionApplies .much (adjFollows := true) = true := rfl

/-- N/V retain overt `much` because Much Deletion only applies before
    an adjective. -/
theorem overt_much_no_deletion :
    Bresnan1973.muchDeletionApplies .much (adjFollows := false) = false := rfl

/-! ### `very` distribution (§6.3) -/

/-- §6.3 (exs. 117–118): whether `very` requires overt `much`.

    - GAs: `much` is covert → `very` combines directly
      ("very hot", *"very much hot")
    - N/V: `much` must be overt → `very` requires overt `much`
      ("very much coffee", *"very coffee"; "ran very much") -/
structure VeryDistributionDatum where
  category : LexCat
  requiresOvertMuch : Bool
  deriving DecidableEq, Repr

/-- Adapter: a `very` example as a typed row. -/
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

/-- The `very` asymmetry follows from Much Deletion: `much` deletes
    exactly before adjectives, so only GAs host covert `much`, and
    `very` requires overt `much` everywhere else. -/
theorem very_tracks_much_deletion :
    ∀ d ∈ veryDistributionData,
      d.requiresOvertMuch =
        !(Bresnan1973.muchDeletionApplies .much
            (adjFollows := d.category == .gradableAdj)) := by
  decide

end Wellwood2015
