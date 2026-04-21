import Linglib.Theories.Semantics.Measurement
import Linglib.Theories.Semantics.Events.ThematicRoles
import Linglib.Theories.Semantics.Events.Krifka1998
import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Phenomena.Comparison.Studies.Bresnan1973

/-!
# @cite{wellwood-2015}: On the Semantics of Comparison Across Categories

@cite{wellwood-2015}

Data, compositional derivation, and verification theorems from
@cite{wellwood-2015}. All comparative sentences — nominal, verbal, and
adjectival — share a uniform DegP pipeline in which `much` introduces a
monotonic measure function μ. The cross-categorial parallel
(mass/atelic/GA vs count/telic/non-GA) follows from mereological status,
and dimensional restriction (§3.4) follows from whether the measured
domain is linearly ordered.

## Data Sources

- §2.1: Nominal comparatives (mass vs count nouns)
- §2.2: Verbal comparatives (atelic vs telic VPs)
- §3.1–3.2: Adjectival comparatives (gradable vs non-gradable adjectives)
- §3.3: Morphosyntactic evidence (`more` = `much` + `-er`, @cite{bresnan-1973})
- §3.4: Dimensional restriction patterns
- §5: Number morphology and measurement (grammar shifts measurement)
- §6.3: `very` distribution and covert `much`

## Compositional Derivation (§2.3, §3.2)

The comparative is derived compositionally via the DegP:

1. `⟦much_μ⟧^A = A(μ)` — introduces the measure function from the
   variable assignment (eq. 37)
2. `⟦-er⟧` — introduces strict comparison (>) against a standard
3. `⟦Deg'⟧ = ⟦much_μ + -er⟧ = λd.λα. μ(α) > d` (eq. 37.i, 45.i)
4. `⟦ABS⟧ = λg.λd.λα. g(α) ≥ d` — links degrees to predicates in the
   than-clause (eq. 38.ii)
5. `⟦than⟧ = λD. max(D)` — selects maximal degree (eq. 38.i)
6. Predicate Modification conjoins DegP with the base predicate
7. Existential closure over the matrix eventuality

The result for all three domains (eqs. 42, 48, 65):

    ∃α. role(a, α) ∧ P(α) ∧ μ(extract(α)) >
        max{d | ∃α'. role(b, α') ∧ P(α') ∧ μ(extract(α')) ≥ d}

Under unique-event assumptions, this reduces to `μ(extract(α_a)) > μ(extract(α_b))`,
bridging to `comparativeSem` (@cite{schwarzschild-2008}) and
`statesComparativeSem` (@cite{cariani-santorio-wellwood-2024}).

-/

namespace Wellwood2015

-- ════════════════════════════════════════════════════
-- § 1. Lexical Category
-- ════════════════════════════════════════════════════

/-- Lexical categories relevant to the cross-categorial analysis. -/
inductive LexCat where
  | massNoun       -- coffee, rock, gold
  | countNoun      -- cup, idea
  | atelicVP       -- ran, slept, ran in the park
  | telicVP        -- ran to the park, graduated high school
  | gradableAdj    -- hot, tall, heavy
  | nonGradableAdj -- wooden, triangular
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Felicity with `much`/`more` (§2.1, §2.2, §3.1–3.2)
-- ════════════════════════════════════════════════════

/-- Observed felicity of `much`/`more` with different lexical categories.

    Mass nouns and atelic VPs are felicitous with `much` and allow multiple
    measurement dimensions. Count nouns and telic VPs are anomalous.
    GAs are felicitous but lexically fix a single dimension.
    Non-GAs are anomalous (not comparable).

    Examples from the paper:
    - "Al bought more coffee than Bill did." ✓ (VOLUME or WEIGHT)
    - "? Al has more idea than Bill does." ✗
    - "Al ran more than Bill did." ✓ (DURATION or DISTANCE)
    - "? Al graduated high school more than Bill did." ✗
    - "Al's coffee is hotter than Bill's." ✓ (TEMPERATURE)
    - "? This table is more wooden than that one." ✗ -/
structure MuchFelicityDatum where
  category : LexCat
  felicitousWithMuch : Bool
  multipleDimensions : Bool
  deriving DecidableEq, Repr

def massNounDatum : MuchFelicityDatum :=
  { category := .massNoun, felicitousWithMuch := true, multipleDimensions := true }

def countNounDatum : MuchFelicityDatum :=
  { category := .countNoun, felicitousWithMuch := false, multipleDimensions := false }

def atelicVPDatum : MuchFelicityDatum :=
  { category := .atelicVP, felicitousWithMuch := true, multipleDimensions := true }

def telicVPDatum : MuchFelicityDatum :=
  { category := .telicVP, felicitousWithMuch := false, multipleDimensions := false }

def gradableAdjDatum : MuchFelicityDatum :=
  { category := .gradableAdj, felicitousWithMuch := true, multipleDimensions := false }

def nonGradableAdjDatum : MuchFelicityDatum :=
  { category := .nonGradableAdj, felicitousWithMuch := false, multipleDimensions := false }

-- ════════════════════════════════════════════════════
-- § 3. Grammar Shifts Measurement (§5)
-- ════════════════════════════════════════════════════

/-- Number morphology and telicity shifts affect available dimensions (§5).

    (104) a. "Al found more rock than Bill did." (WEIGHT, VOLUME, *NUMBER)
          b. "Al found more rocks than Bill did." (*WEIGHT, *VOLUME, NUMBER)

    (105) a. "Al ran in the park more than Bill did." (DIST, DUR, NUMBER)
          b. "Al ran to the park more than Bill did." (*DIST, *DUR, NUMBER)

    Shifting from mass → count (plural morpheme) or atelic → telic
    restricts measurement to NUMBER, blocking extensive dimensions. -/
structure GrammarShiftDatum where
  baseForm : String
  shiftedForm : String
  baseExtensive : Bool
  shiftedExtensive : Bool
  deriving Repr

/-- Ex. 104: mass → count via plural morpheme. -/
def rockShift : GrammarShiftDatum :=
  { baseForm := "more rock"
  , shiftedForm := "more rocks"
  , baseExtensive := true
  , shiftedExtensive := false }

/-- Ex. 105: atelic → telic via directional PP. -/
def runShift : GrammarShiftDatum :=
  { baseForm := "ran in the park more"
  , shiftedForm := "ran to the park more"
  , baseExtensive := true
  , shiftedExtensive := false }

-- The cross-categorial parallel (§2–3) — mass nouns pattern with atelic VPs
-- (CUM class), count nouns with telic VPs (QUA class), GAs with CUM,
-- non-GAs with QUA — is derived by `lexCatToStatus` in § 17 below,
-- not stipulated as data.

-- The `much`/`many` distribution (§3.3, @cite{bresnan-1973}) — `much` with
-- CUM predicates, `many` as suppletive for QUA — follows from the
-- `statusPredictsFelicitous` bridge in § 14.

-- ════════════════════════════════════════════════════
-- § 4. Measured Domain (§3.4)
-- ════════════════════════════════════════════════════

/-- What is actually measured in a comparative — the ontological domain
    whose mereological structure determines available dimensions.

    The key §3.4 insight: dimension type (intensive vs extensive)
    tracks the measured domain, not lexical category. -/
inductive MeasuredDomain where
  | entity  -- physical objects (coffee, plastic, glass)
  | event   -- events/processes (driving, singing)
  | state   -- states (heat, hardness, speed, loudness)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 5. Dimension Reversal Data (§3.4)
-- ════════════════════════════════════════════════════

/-- Dimension reversal: the same syntactic category can measure different
    ontological domains, and the available dimensions follow from the
    measured domain, not from the syntactic category. -/
structure DimensionReversalDatum where
  form : String
  category : LexCat
  dimensionName : String
  measuredDomain : MeasuredDomain
  intensive : Bool
  deriving Repr

/-- (82a): GA measuring states → intensive. -/
def hotterDatum : DimensionReversalDatum :=
  { form := "hotter", category := .gradableAdj, dimensionName := "temperature"
  , measuredDomain := .state, intensive := true }

/-- (82b): GA measuring states → intensive. -/
def harderDatum : DimensionReversalDatum :=
  { form := "harder", category := .gradableAdj, dimensionName := "hardness"
  , measuredDomain := .state, intensive := true }

/-- (83a): Mass noun measuring entities → extensive. -/
def moreCoffeeDatum : DimensionReversalDatum :=
  { form := "more coffee", category := .massNoun, dimensionName := "volume"
  , measuredDomain := .entity, intensive := false }

/-- (83b): Mass noun measuring entities → extensive. -/
def morePlasticDatum : DimensionReversalDatum :=
  { form := "more plastic", category := .massNoun, dimensionName := "weight"
  , measuredDomain := .entity, intensive := false }

/-- (84a): **Reversal** — GA but extensive, because measured domain is entity. -/
def fullerDatum : DimensionReversalDatum :=
  { form := "fuller", category := .gradableAdj, dimensionName := "volume"
  , measuredDomain := .entity, intensive := false }

/-- (84b): **Reversal** — GA but extensive, because measured domain is entity. -/
def heavierDatum : DimensionReversalDatum :=
  { form := "heavier", category := .gradableAdj, dimensionName := "weight"
  , measuredDomain := .entity, intensive := false }

/-- (85a): **Reversal** — noun but intensive, because measured domain is state. -/
def moreHeatDatum : DimensionReversalDatum :=
  { form := "more heat", category := .massNoun, dimensionName := "temperature"
  , measuredDomain := .state, intensive := true }

/-- (85b): **Reversal** — noun but intensive, because measured domain is state. -/
def moreFirmnessDatum : DimensionReversalDatum :=
  { form := "more firmness", category := .massNoun, dimensionName := "hardness"
  , measuredDomain := .state, intensive := true }

/-- (89a): **Reversal** — verb but intensive, because measured domain is state. -/
def spedUpMoreDatum : DimensionReversalDatum :=
  { form := "sped up more", category := .atelicVP, dimensionName := "speed"
  , measuredDomain := .state, intensive := true }

/-- (87a): Atelic VP measuring events → extensive. -/
def droveMoreDatum : DimensionReversalDatum :=
  { form := "drove more", category := .atelicVP, dimensionName := "distance"
  , measuredDomain := .event, intensive := false }

def dimensionReversalData : List DimensionReversalDatum :=
  [ hotterDatum, harderDatum, moreCoffeeDatum, morePlasticDatum
  , fullerDatum, heavierDatum, moreHeatDatum, moreFirmnessDatum
  , spedUpMoreDatum, droveMoreDatum ]

-- ════════════════════════════════════════════════════
-- § 6. State Modification Data (§3.2, §3.5)
-- ════════════════════════════════════════════════════

/-- States support predicate modification via conjunction (§3.5).

    "happy in the morning" = ∃s. happy(s) ∧ Holder(x, s) ∧ in-the-morning(s) -/
structure StateModificationDatum where
  adjective : String
  modifier : String
  form : String
  deriving Repr

def happyMorningDatum : StateModificationDatum :=
  { adjective := "happy", modifier := "in the morning"
  , form := "happy in the morning" }

def patientPlaygroundDatum : StateModificationDatum :=
  { adjective := "patient", modifier := "with Mary on the playground"
  , form := "patient with Mary on the playground" }

-- ════════════════════════════════════════════════════
-- § 7. Compositional Pieces (§2.1 eqs. 37–38)
-- ════════════════════════════════════════════════════

open Semantics.Events (Ev EvPred)
open Semantics.Events.ThematicRoles (ThematicFrame EventModifier
  modifiedStativeLogicalForm stativeLogicalForm modify modified_stative_is_pm)
open Semantics.Measurement
open Core.Verbs

/-- Deg' = much_μ + -er: the comparative degree head.

    ⟦Deg'⟧^A = λd.λα. A(μ)(α) > d

    `much_μ` introduces the measure function A(μ) from the variable
    assignment (⟦much_μ⟧^A = A(μ), eq. 37); `-er` introduces the
    strict comparison (>). Their combination is the semantic core
    shared by all comparatives: a degree-parameterized predicate
    that holds of α iff its measure exceeds d.

    Note: the denotation of `much_μ` is simply A(μ) — a variable
    assignment lookup — not a predicate. The monotonicity condition
    (that A(μ) be StrictMono on a part-whole ordering) is a felicity
    condition on the assignment, not part of the denotation.

    (§2.1 eq. 37.i, §2.2 eq. 45.i) -/
def Deg' {α : Type*} (μ : α → ℚ) (d : ℚ) (a : α) : Prop :=
  μ a > d

/-- ABS: type-shifter linking degrees to eventuality predicates.

    ⟦ABS⟧^A = λg.λd.λα. g(α) ≥ d

    Used in the than-clause to create a set of degrees from a
    measure function. The weak inequality (≥) in ABS contrasts
    with the strict inequality (>) in Deg': the matrix uses >,
    the standard uses ≥, following @cite{von-stechow-1984}.

    (§2.1 eq. 38.ii) -/
def ABS {α : Type*} (μ : α → ℚ) (d : ℚ) (a : α) : Prop :=
  μ a ≥ d

/-- ⟦than⟧ = λD. max(D): a degree δ is the maximum of a degree set
    iff it belongs to the set and no element exceeds it.

    (§2.1 eq. 38.i; @cite{von-stechow-1984}, @cite{heim-2001}) -/
def IsMaxDeg (S : Set ℚ) (δ : ℚ) : Prop :=
  δ ∈ S ∧ ∀ d ∈ S, d ≤ δ

-- ════════════════════════════════════════════════════
-- § 8. Comparative Derivations (§2.1–2.3, §3.2)
-- ════════════════════════════════════════════════════

/-! ### Nominal comparative derivation (§2.1, eqs. 36–42)

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

### Adjectival comparative derivation (§3.2, eqs. 58–65)

    "Al's coffee is hotter than Bill's"

    1. ⟦hot⟧ = λs.hot(s)                                   (eq. 58)
    2. ⟦much_μ hot⟧^A = λd.λs. hot(s) ∧ A(μ)(s) ≥ d       (eq. 60)
    3. After -er: λd.λs. hot(s) ∧ A(μ)(s) > d              (eq. 61)
    4. ⟦DegP⟧ = λs. hot(s) ∧ A(μ)(s) > δ                  (eq. 62)
    5. ∃s[Holder(s)(a) ∧ hot(s) ∧ A(μ)(s) > δ]             (eq. 65)

    Tree (97) — adjectival with modifiers via PM:
    ⟦more patient with Mary on the playground⟧ =
      λs. A(μ)(s) > δ ∧ patient(s) ∧ with(s)(m) ∧ on(s)(p)
-/

-- ════════════════════════════════════════════════════
-- § 9. Universal Comparative Truth Condition
-- ════════════════════════════════════════════════════

/-- The than-clause degree set: the set of degrees d such that some
    b-eventuality satisfying P has a measured value at least d.

    {d | ∃α'. role(b, α') ∧ P(α') ∧ μ(extract(α')) ≥ d}

    This is the ABS-mediated degree set from the than-clause
    (eq. 40 for nominal, eq. 47 for verbal, eq. 63 for adjectival). -/
def thanDegrees {Ent α Measured : Type*}
    (role : Ent → α → Prop) (P : α → Prop)
    (extract : α → Measured) (μ : Measured → ℚ)
    (b : Ent) : Set ℚ :=
  {d | ∃ eb, role b eb ∧ P eb ∧ μ (extract eb) ≥ d}

/-- The paper's compositional comparative truth condition (eqs. 42, 48, 65).

    "a V-s more P than b does" is true iff there exists an a-eventuality
    ea satisfying P, and a degree δ that is the max of the than-clause
    degree set, such that μ(extract(ea)) > δ.

    This is the result of composing:
    (1) `much_μ` introduces the measure function A(μ)
    (2) `-er` introduces strict comparison (>) against the standard δ
    (3) The than-clause provides δ = max{d | ∃eb. role(b,eb) ∧ P(eb) ∧ μ(extract(eb)) ≥ d}
    (4) Predicate Modification conjoins the degree condition with the base predicate
    (5) Existential closure over the matrix eventuality

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
  ∃ ea, role a ea ∧ P ea ∧
    ∃ δ, IsMaxDeg (thanDegrees role P extract μ b) δ ∧ μ (extract ea) > δ

-- ════════════════════════════════════════════════════
-- § 10. Three Domain Instantiations
-- ════════════════════════════════════════════════════

/-- Nominal comparative (§2.1, eq. 42):
    "Al bought more coffee than Bill did."

    Measured domain: entities (via `themeOf`).
    Role: Agent. Extract: themeOf (the consumed/affected entity). -/
def nominalComparative {Entity Time : Type*} [LinearOrder Time]
    (frame : ThematicFrame Entity Time)
    (P : EvPred Time) (themeOf : Ev Time → Entity)
    (μ : Entity → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P themeOf μ a b

/-- Verbal comparative (§2.2, eq. 48):
    "Al ran more than Bill did."

    Measured domain: events directly (extract = id). Role: Agent. -/
def verbalComparative {Entity Time : Type*} [LinearOrder Time]
    (frame : ThematicFrame Entity Time)
    (P : EvPred Time) (μ : Ev Time → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.agent P id μ a b

/-- Adjectival comparative (§3.2, eq. 65):
    "This coffee is hotter than that coffee."

    Measured domain: states directly (extract = id). Role: Holder. -/
def adjectivalComparative {Entity Time : Type*} [LinearOrder Time]
    (frame : ThematicFrame Entity Time)
    (P : EvPred Time) (μ : Ev Time → ℚ) (a b : Entity) : Prop :=
  comparativeTruth frame.holder P id μ a b

-- ════════════════════════════════════════════════════
-- § 11. Maximality Reduction
-- ════════════════════════════════════════════════════

/-- Under unique-event assumptions, the max of the than-clause degree set
    is μ(extract(eb)), and the comparative reduces to direct comparison.

    When b has a unique P-eventuality eb, the than-clause degree set
    {d | μ(extract(eb)) ≥ d} has max = μ(extract(eb)), so the
    comparative becomes μ(extract(ea)) > μ(extract(eb)). -/
theorem comparativeTruth_max {Ent α Measured : Type*}
    {role : Ent → α → Prop}
    {P : α → Prop}
    {extract : α → Measured}
    {μ : Measured → ℚ}
    {a b : Ent}
    {ea eb : α}
    (ha : role a ea ∧ P ea)
    (ha_unique : ∀ e, role a e → P e → e = ea)
    (hb : role b eb ∧ P eb)
    (hb_unique : ∀ e, role b e → P e → e = eb) :
    comparativeTruth role P extract μ a b ↔
      μ (extract eb) < μ (extract ea) := by
  constructor
  · -- Forward: max-based → direct comparison
    rintro ⟨ea', ha_role, ha_P, δ, ⟨hδ_in, hδ_max⟩, hgt⟩
    have h_ea_eq := ha_unique ea' ha_role ha_P; subst h_ea_eq
    -- δ = μ(extract eb): the max of {d | ∃eb'. role b eb' ∧ P eb' ∧ μ(extract eb') ≥ d}
    obtain ⟨eb', hb_role', hb_P', hge⟩ := hδ_in
    have h_eb_eq := hb_unique eb' hb_role' hb_P'
    rw [h_eb_eq] at hge
    have hδ_eq : δ = μ (extract eb) :=
      le_antisymm hge (hδ_max _ ⟨eb, hb.1, hb.2, le_refl _⟩)
    rw [hδ_eq] at hgt; exact hgt
  · -- Backward: direct comparison → max-based
    intro hlt
    exact ⟨ea, ha.1, ha.2, μ (extract eb),
      ⟨⟨eb, hb.1, hb.2, le_refl _⟩,
       fun d ⟨eb', hr, hp, hge⟩ => by rw [hb_unique eb' hr hp] at hge; exact hge⟩,
      hlt⟩

-- ════════════════════════════════════════════════════
-- § 12. Bridges to Existing Infrastructure
-- ════════════════════════════════════════════════════

/-- Adjectival comparative under maximality reduces to `μ(sb) < μ(sa)`. -/
theorem adjectival_max_reduces {Entity Time : Type*} [LinearOrder Time]
    {frame : ThematicFrame Entity Time}
    {P : EvPred Time} {μ : Ev Time → ℚ}
    {a b : Entity} {sa sb : Ev Time}
    (ha : frame.holder a sa ∧ P sa)
    (ha_unique : ∀ s, frame.holder a s → P s → s = sa)
    (hb : frame.holder b sb ∧ P sb)
    (hb_unique : ∀ s, frame.holder b s → P s → s = sb) :
    adjectivalComparative frame P μ a b ↔ μ sb < μ sa :=
  comparativeTruth_max ha ha_unique hb hb_unique

/-- CSW's `statesComparativeSem` is definitionally `μ sb < μ sa`. -/
theorem statesComparativeSem_is_lt {S D : Type*} [Preorder S] [Preorder D]
    (μ : S → D) (sa sb : S) :
    Semantics.Gradability.StatesBased.statesComparativeSem μ sa sb ↔
      μ sb < μ sa :=
  Iff.rfl

/-- All comparative domains under maximality = `comparativeSem`
    (Rett/Schwarzschild) on measured values. -/
theorem max_eq_comparativeSem {Entity Time Measured : Type*} [LinearOrder Time]
    {role : Entity → Ev Time → Prop}
    {P : EvPred Time}
    {extract : Ev Time → Measured}
    {μ : Measured → ℚ}
    {a b : Entity} {ea eb : Ev Time}
    (ha : role a ea ∧ P ea)
    (ha_unique : ∀ e, role a e → P e → e = ea)
    (hb : role b eb ∧ P eb)
    (hb_unique : ∀ e, role b e → P e → e = eb) :
    comparativeTruth role P extract μ a b ↔
      Semantics.Degree.Comparative.comparativeSem
        (μ ∘ extract) ea eb .positive :=
  comparativeTruth_max ha ha_unique hb hb_unique

-- ════════════════════════════════════════════════════
-- § 13. Dimensional Restriction Connection
-- ════════════════════════════════════════════════════

/-- State domains are dimensionally restricted when linearly ordered. -/
theorem state_domain_restricted {S : Type*} [LinearOrder S] :
    DimensionallyRestricted S :=
  linearOrder_dimensionallyRestricted

-- `statesBasedEntry_restricted` is in `Measurement.lean` (not duplicated here).

/-- If two admissible measures disagree on some pair, the domain is NOT
    dimensionally restricted. -/
theorem not_restricted_of_disagreement {α : Type*} [Preorder α]
    {μ₁ μ₂ : α → ℚ} (hμ₁ : StrictMono μ₁) (hμ₂ : StrictMono μ₂)
    {a b : α} (h₁ : μ₁ a < μ₁ b) (h₂ : ¬ μ₂ a < μ₂ b) :
    ¬ DimensionallyRestricted α := by
  intro hDR
  exact h₂ ((hDR μ₁ μ₂ hμ₁ hμ₂ a b).mp h₁)

-- ════════════════════════════════════════════════════
-- § 14. Theory–Data Bridges
-- ════════════════════════════════════════════════════

/-- Map `LexCat` to `MereologicalStatus` using the theory's bridges. -/
def lexCatToStatus : LexCat → MereologicalStatus
  | .massNoun       => numberToStatus .mass
  | .countNoun      => numberToStatus .sg
  | .atelicVP       => telicityToStatus .atelic
  | .telicVP        => telicityToStatus .telic
  | .gradableAdj    => gradableToStatus
  | .nonGradableAdj => nonGradableToStatus

def statusPredictsFelicitous : MereologicalStatus → Bool
  | .cumulative => true
  | .quantized  => false

-- Per-datum felicity verification

theorem massNoun_felicity :
    statusPredictsFelicitous (lexCatToStatus .massNoun) =
      massNounDatum.felicitousWithMuch := rfl

theorem countNoun_felicity :
    statusPredictsFelicitous (lexCatToStatus .countNoun) =
      countNounDatum.felicitousWithMuch := rfl

theorem atelicVP_felicity :
    statusPredictsFelicitous (lexCatToStatus .atelicVP) =
      atelicVPDatum.felicitousWithMuch := rfl

theorem telicVP_felicity :
    statusPredictsFelicitous (lexCatToStatus .telicVP) =
      telicVPDatum.felicitousWithMuch := rfl

theorem gradableAdj_felicity :
    statusPredictsFelicitous (lexCatToStatus .gradableAdj) =
      gradableAdjDatum.felicitousWithMuch := rfl

theorem nonGradableAdj_felicity :
    statusPredictsFelicitous (lexCatToStatus .nonGradableAdj) =
      nonGradableAdjDatum.felicitousWithMuch := rfl

-- Cross-categorial parallel

theorem massNoun_atelicVP_same_status :
    lexCatToStatus .massNoun = lexCatToStatus .atelicVP := rfl

theorem countNoun_telicVP_same_status :
    lexCatToStatus .countNoun = lexCatToStatus .telicVP := rfl

theorem gradableAdj_patterns_with_cum :
    lexCatToStatus .gradableAdj = lexCatToStatus .massNoun := rfl

theorem nonGradableAdj_patterns_with_qua :
    lexCatToStatus .nonGradableAdj = lexCatToStatus .countNoun := rfl

-- Grammar shift bridges

theorem run_shift_via_telicize :
    let p : AspectualProfile := activityProfile
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  telicize_shifts_status _ rfl

theorem build_shift_via_atelicize :
    let p : AspectualProfile := accomplishmentProfile
    telicityToStatus p.telicity = .quantized ∧
    telicityToStatus p.atelicize.telicity = .cumulative :=
  atelicize_shifts_status _ rfl

theorem rock_shift_status :
    lexCatToStatus .massNoun = .cumulative ∧
    lexCatToStatus .countNoun = .quantized := ⟨rfl, rfl⟩

-- Boundedness bridge

theorem massNoun_open_scale :
    (lexCatToStatus .massNoun).toBoundedness = .open_ := rfl

theorem countNoun_closed_scale :
    (lexCatToStatus .countNoun).toBoundedness = .closed := rfl

theorem atelicVP_open_scale :
    (lexCatToStatus .atelicVP).toBoundedness = .open_ := rfl

theorem telicVP_closed_scale :
    (lexCatToStatus .telicVP).toBoundedness = .closed := rfl

-- Dimension reversal bridges (§3.4)

def measuredDomainRestricted : MeasuredDomain → Bool
  | .state  => true
  | .entity => false
  | .event  => false

theorem hotter_restricted :
    measuredDomainRestricted hotterDatum.measuredDomain = hotterDatum.intensive := rfl

theorem harder_restricted :
    measuredDomainRestricted harderDatum.measuredDomain = harderDatum.intensive := rfl

theorem moreCoffee_not_restricted :
    measuredDomainRestricted moreCoffeeDatum.measuredDomain = moreCoffeeDatum.intensive := rfl

theorem morePlastic_not_restricted :
    measuredDomainRestricted morePlasticDatum.measuredDomain = morePlasticDatum.intensive := rfl

theorem fuller_not_restricted :
    measuredDomainRestricted fullerDatum.measuredDomain = fullerDatum.intensive := rfl

theorem heavier_not_restricted :
    measuredDomainRestricted heavierDatum.measuredDomain = heavierDatum.intensive := rfl

theorem moreHeat_restricted :
    measuredDomainRestricted moreHeatDatum.measuredDomain = moreHeatDatum.intensive := rfl

theorem moreFirmness_restricted :
    measuredDomainRestricted moreFirmnessDatum.measuredDomain = moreFirmnessDatum.intensive := rfl

theorem spedUpMore_restricted :
    measuredDomainRestricted spedUpMoreDatum.measuredDomain = spedUpMoreDatum.intensive := rfl

theorem droveMore_not_restricted :
    measuredDomainRestricted droveMoreDatum.measuredDomain = droveMoreDatum.intensive := rfl

-- State modification bridge (§3.5)

theorem state_mod_pm_bridge {Entity Time : Type*} [LinearOrder Time]
    (P : EvPred Time) (frame : ThematicFrame Entity Time)
    (x : Entity) (M : EventModifier Time) :
    modifiedStativeLogicalForm P frame x M ↔
      stativeLogicalForm (modify P M) frame x :=
  modified_stative_is_pm P frame x M

-- ════════════════════════════════════════════════════
-- § 15. `very` Distribution (§6.3)
-- ════════════════════════════════════════════════════

/-- §6.3: `very` distribution tracks overt vs covert `much`.

    - GAs: `much` is covert → `very` combines directly ("very hot", *"very much hot")
    - N/V: `much` must be overt → `very` requires overt `much` ("very much coffee", *"very coffee") -/
structure VeryDistributionDatum where
  category : LexCat
  requiresOvertMuch : Bool
  felicitousExample : String
  infelicitousExample : String
  deriving Repr

def veryWithGA : VeryDistributionDatum :=
  { category := .gradableAdj
  , requiresOvertMuch := false
  , felicitousExample := "very hot"
  , infelicitousExample := "*very much hot" }

def veryWithNoun : VeryDistributionDatum :=
  { category := .massNoun
  , requiresOvertMuch := true
  , felicitousExample := "very much coffee"
  , infelicitousExample := "*very coffee" }

def veryWithVerb : VeryDistributionDatum :=
  { category := .atelicVP
  , requiresOvertMuch := true
  , felicitousExample := "very much ran"
  , infelicitousExample := "*very ran" }

/-- The `very` distribution follows from whether `much` is overt or covert:
    GAs have covert `much`, so `very` combines directly (eq. 118).
    N/V require overt `much`, so `very` must co-occur with `much` (eq. 117). -/
theorem very_requires_much_iff_not_ga :
    veryWithGA.requiresOvertMuch = false ∧
    veryWithNoun.requiresOvertMuch = true ∧
    veryWithVerb.requiresOvertMuch = true := ⟨rfl, rfl, rfl⟩

/-- `very` without overt `much` correlates with CUM (felicitous with `much`):
    GAs are CUM and don't require overt `much`; N/V are CUM but require it.
    The asymmetry: GAs have *covert* `much`, N/V need *overt* `much`. -/
theorem very_ga_is_cum :
    lexCatToStatus veryWithGA.category = .cumulative := rfl

-- ════════════════════════════════════════════════════
-- § 16. Krifka 1998 Bridge: CUM/QUA Propagation
-- ════════════════════════════════════════════════════

/-! ### Connection to @cite{krifka-1998}'s CUM/QUA propagation

@cite{wellwood-2015}'s cross-categorial parallel — mass nouns pattern with atelic
VPs, count nouns with telic VPs — is *explained* by @cite{krifka-1998}'s
telicity-through-quantization theory. Krifka shows that the VP inherits
its mereological status from the NP via the incremental theme role:

- **CUM propagation**: CumTheta(θ) ∧ CUM(OBJ) → CUM(VP θ OBJ)
  "eat apples" is CUM because APPLES is CUM and EAT's theme is cumulative.

- **QUA propagation**: UP(θ) ∧ SINC(θ) ∧ QUA(OBJ) → QUA(VP θ OBJ)
  "eat two apples" is QUA because TWO-APPLES is QUA and EAT's theme is SINC.

Wellwood's claim that `much`-felicity tracks mereological status then
follows compositionally: an atelic VP is felicitous with `much` because
it *inherits* CUM from its mass-noun object; a telic VP is infelicitous
because it *inherits* QUA from its quantized object.

The bridge theorems below connect Krifka's formal CUM/QUA predicates
(on VP denotations) to Wellwood's `MereologicalStatus` classification
and `statusPredictsFelicitous`.
-/

open Semantics.Events.Krifka1998

/-- CUM(VP) → VP is measurable by `much` (cumulative status).

    If @cite{krifka-1998}'s CUM propagation gives us CUM(VP θ OBJ), the VP's
    mereological status is `.cumulative`, predicting felicity with
    `much` and availability of multiple measurement dimensions
    (DURATION, DISTANCE, etc.). -/
theorem cum_vp_measurable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    {θ : α → β → Prop} {OBJ : α → Prop}
    (hCum : CumTheta θ) (hObj : Mereology.CUM OBJ) :
    statusPredictsFelicitous (telicityToStatus .atelic) = true ∧
    Mereology.CUM (VP θ OBJ) :=
  ⟨rfl, cum_propagation hCum hObj⟩

/-- QUA(VP) → VP is NOT measurable by `much` (quantized status).

    If @cite{krifka-1998}'s QUA propagation gives us QUA(VP θ OBJ), the VP's
    mereological status is `.quantized`, predicting infelicity with
    `much`. Only NUMBER remains as a measurement dimension. -/
theorem qua_vp_not_measurable {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {θ : α → β → Prop} {OBJ : α → Prop}
    (hUP : UP θ) (hSinc : SINC θ) (hQua : Mereology.QUA OBJ) :
    statusPredictsFelicitous (telicityToStatus .telic) = false ∧
    Mereology.QUA (VP θ OBJ) :=
  ⟨rfl, qua_propagation_sinc hUP hSinc hQua⟩

/-- Grammar shifts measurement (§5): telicization of a CUM VP yields a QUA VP.

    @cite{wellwood-2015} ex. 105: "ran in the park more" (atelic, CUM, extensive
    dimensions) vs "ran to the park more" (telic, QUA, NUMBER only).

    @cite{krifka-1998}'s theory explains *why*: the directional PP introduces a
    quantized path argument, and QUA propagation through SINC transmits
    QUA to the VP, blocking extensive measurement.

    This theorem connects the two accounts: given a CUM VP (from CUM
    propagation) and a QUA VP (from QUA propagation with a different
    object), the measurement status shifts from cumulative to quantized. -/
theorem grammar_shifts_via_krifka {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {θ : α → β → Prop} {OBJ_cum OBJ_qua : α → Prop}
    (hCumTheta : CumTheta θ) (hCumObj : Mereology.CUM OBJ_cum)
    (hUP : UP θ) (hSinc : SINC θ) (hQuaObj : Mereology.QUA OBJ_qua) :
    Mereology.CUM (VP θ OBJ_cum) ∧ Mereology.QUA (VP θ OBJ_qua) :=
  ⟨cum_propagation hCumTheta hCumObj, qua_propagation_sinc hUP hSinc hQuaObj⟩

-- ════════════════════════════════════════════════════
-- § 17. Cross-Categorial Construction Data
-- ════════════════════════════════════════════════════

/-- A cross-categorial comparison construction template:
    the same DegP shell applies across syntactic categories.
    @cite{wellwood-2015} §2, @cite{bresnan-1973} -/
structure CrossCategorialDatum where
  /-- Syntactic domain (nominal, verbal, adjectival) -/
  domain : String
  /-- Example comparative sentence -/
  comparativeExample : String
  /-- Example equative sentence -/
  equativeExample : String
  /-- The degree word used -/
  degreeWord : String
  deriving Repr

def crossCategorialExamples : List CrossCategorialDatum :=
  [ { domain := "adjectival"
    , comparativeExample := "Kim is taller than Lee"
    , equativeExample := "Kim is as tall as Lee"
    , degreeWord := "-er / as...as" }
  , { domain := "nominal"
    , comparativeExample := "Kim bought more coffee than Lee"
    , equativeExample := "Kim bought as much coffee as Lee"
    , degreeWord := "more / as much...as" }
  , { domain := "verbal"
    , comparativeExample := "Kim ran more than Lee"
    , equativeExample := "Kim ran as much as Lee"
    , degreeWord := "more / as much...as" }
  , { domain := "adverbial"
    , comparativeExample := "Kim ran faster than Lee"
    , equativeExample := "Kim ran as fast as Lee"
    , degreeWord := "-er / as...as" }
  ]

-- ════════════════════════════════════════════════════
-- § 18. Bresnan's Decomposition (Morphosyntax)
-- ════════════════════════════════════════════════════

/-- @cite{bresnan-1973} decomposition: `more` = `-er` + `much`.

    Wellwood's cross-categorial claim: the SAME QP underlies `more`
    across nominal ("more coffee"), verbal ("ran more"), and adverbial
    ("more quickly") domains. The adjectival domain ("taller") differs
    only by Much Deletion (Rule 10): `much` deletes before adjectives.

    The formal QP structure and suppletion are in `Bresnan1973`. -/
def crossCategorialQP : Bresnan1973.QP := ⟨.er, .much⟩

/-- The surface form "more" derives from Bresnan's suppletion. -/
theorem crossCategorial_more_from_suppletion :
    Bresnan1973.suppletion crossCategorialQP = some "more" := rfl

-- ════════════════════════════════════════════════════
-- § 19. Much Deletion Bridge (§6.3 ↔ Bresnan Rule 10)
-- ════════════════════════════════════════════════════

/-- Wellwood §6.3: GAs have "covert `much`" — `very` combines directly
    with the adjective without overt `much` ("very hot", *"very much hot").

    This is exactly Bresnan's Rule 10 (Much Deletion): `much → ∅` before
    an adjective. The formal `muchDeletionApplies` predicate from
    `Bresnan1973` captures when the deletion fires. -/
theorem covert_much_is_bresnan_deletion :
    Bresnan1973.muchDeletionApplies .much (adjFollows := true) = true := rfl

/-- N/V retain overt `much` because Much Deletion only applies before A.
    `adjFollows = false` → Much Deletion does not apply. -/
theorem overt_much_no_deletion :
    Bresnan1973.muchDeletionApplies .much (adjFollows := false) = false := rfl

end Wellwood2015
