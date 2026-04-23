import Linglib.Theories.Semantics.Tense.MaximalInformativity
import Linglib.Theories.Semantics.Events.DimensionBridge
import Linglib.Core.Scales.Scale
import Linglib.Core.Time.Boundedness
import Linglib.Fragments.English.TemporalExpressions

/-!
# Rouillard 2026: Temporal *in*-Adverbials — Empirical Data
@cite{rouillard-2026} @cite{kennedy-2007} @cite{vendler-1957} @cite{ladusaw-1979}

Empirical distributional data and verification theorems for English
temporal *in*-adverbials, following @cite{rouillard-2026} "Maximal
informativity accounts for the distribution of temporal *in*-adverbials".

Rouillard's analysis distinguishes two readings of *in*-adverbials:

- **E-TIA** (Event TIA): "Mary wrote up a paper *in three days*" — measures
  the runtime of a telic event from onset to telos. Selects telic VPs.
- **G-TIA** (Gap TIA): "Mary hasn't been sick *in three days*" — measures
  the gap between the right boundary of the perfect time span and the most
  recent witnessing event. Strong NPI; requires negation + perfect.

The lexical entries `inTelic` (= Rouillard's E-TIA) and `inGap` (= Rouillard's
G-TIA) are defined in `Fragments/English/TemporalExpressions.lean` with
**consensus typological metadata** (Vendler selection, IAI 2001 classification,
polarity-item status). The Rouillard-specific reanalysis — the `TIAType`
labels and the eventLevel / perfectLevel `AdverbialPosition` distinction —
lives below in this file as a **partial projection from the consensus
entries** (`DurationExprEntry.rouillardClassification?`), not as
Fragment-level fields. The map-function dimension (M = τ vs M = id) is
redundant with TIA type and is omitted from the projection.

## Data Points

### E-TIAs (Event TIAs): measure event durations
- (1a) "Mary wrote up a paper in three days." ✓ — telic VP (accomplishment)
- (1b) "*Mary was sick in three days." ✗ — atelic VP (state)
- (88) "The climber reached the summit in three days." ✓ — telic (achievement)

### G-TIAs (Gap TIAs): measure gap durations, NPIs
- (2a) "Mary hasn't been sick in three days." ✓ — negative perfect
- (2b) "*Mary has been sick in three days." ✗ — positive perfect
- (48) "*Mary wasn't sick in three days." ✗ — simple past, no perfect

### E‑ and U‑Perfect Ambiguity
- (53) "Mary hasn't written up a paper in three days." — ambiguous E-TIA / G-TIA
- (54) "Mary has been sick for three days." — ambiguous E-perfect / U-perfect

## Architectural Role

This file is a **Phenomena/Studies** file: it imports Theories + Fragments
and verifies that theoretical predictions match empirical observations.
The Rouillard-specific apparatus (`TIAType`, `AdverbialPosition`,
`RouillardClassification`) is co-located here rather than in a Fragment
file because it is paper-specific analytical machinery, not consensus
typological metadata.

-/

namespace Phenomena.TenseAspect.TemporalAdverbials.Rouillard2026

open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Semantics.Tense.MaximalInformativity
open Core.Scale
open Fragments.English.TemporalExpressions

-- ════════════════════════════════════════════════════
-- § 0. Rouillard 2026 Analytical Apparatus
-- ════════════════════════════════════════════════════

/-- Rouillard's TIA-type classification.
    Derived from a `DurationExprEntry` via `rouillardClassification?` below;
    this enum is paper-specific apparatus, not consensus Fragment metadata. -/
inductive TIAType where
  | eTIA   -- Event TIA: measures event durations
  | gTIA   -- Gap TIA: measures gap durations
  deriving DecidableEq, Repr

/-- Rouillard's syntactic position for the *in*-adverbial.
    E-TIAs are VP-adjacent (event-level); G-TIAs are AspP-adjacent
    (perfect-level). -/
inductive AdverbialPosition where
  | eventLevel
  | perfectLevel
  deriving DecidableEq, Repr

/-- Bundle of Rouillard's analytical labels for an *in*-adverbial:
    TIA type (E-TIA / G-TIA) and syntactic position (event-level vs
    perfect-level). The map-function dimension (M = τ vs M = id) is
    redundant with TIA type and is omitted; consumers reconstruct it
    from `tiaType` if needed. -/
structure RouillardClassification where
  tiaType : TIAType
  position : AdverbialPosition
  deriving DecidableEq, Repr

/-- Project a `DurationExprEntry` to Rouillard's analytical labels.
    Returns `none` for entries outside the *in*-adverbial paradigm
    (`forDur`, `ago`). Defined in the `DurationExprEntry` namespace so
    that consumers can use dot notation (`e.rouillardClassification?`). -/
def _root_.Fragments.English.TemporalExpressions.DurationExprEntry.rouillardClassification?
    (e : DurationExprEntry) : Option RouillardClassification :=
  match e.kind with
  | .telicCompletion => some ⟨.eTIA, .eventLevel⟩
  | .npiGap          => some ⟨.gTIA, .perfectLevel⟩
  | _                => none

-- ════════════════════════════════════════════════════
-- § 1. E-TIA Distribution Data
-- ════════════════════════════════════════════════════

/-- E-TIA acceptability datum: VP class → acceptable with E-TIA? -/
structure ETIADatum where
  /-- Description of the VP -/
  vp : String
  /-- Vendler class of the VP -/
  vendlerClass : VendlerClass
  /-- Whether "VP in three days" is acceptable -/
  acceptable : Bool
  deriving Repr

/-- (1a) "Mary wrote up a paper in three days." — accomplishment, ✓ -/
def datum_1a : ETIADatum :=
  { vp := "write up a paper", vendlerClass := .accomplishment, acceptable := true }

/-- (1b) "*Mary was sick in three days." — state, ✗ -/
def datum_1b : ETIADatum :=
  { vp := "be sick", vendlerClass := .state, acceptable := false }

/-- (88) "The climber reached the summit in three days." — achievement, ✓ -/
def datum_88 : ETIADatum :=
  { vp := "reach the summit", vendlerClass := .achievement, acceptable := true }

/-- (84) "*The dancers waltzed in one hour." — activity, ✗ -/
def datum_84 : ETIADatum :=
  { vp := "waltz", vendlerClass := .activity, acceptable := false }

def eTIAData : List ETIADatum :=
  [datum_1a, datum_1b, datum_88, datum_84]

-- ════════════════════════════════════════════════════
-- § 2. E-TIA Verification: telicity predicts acceptability
-- ════════════════════════════════════════════════════

/-- E-TIA acceptability is predicted by telicity:
    telic VPs accept E-TIAs, atelic VPs reject them. -/
def eTIA_predicted_by_telicity (d : ETIADatum) : Bool :=
  (d.vendlerClass.telicity == .telic) == d.acceptable

/-- All E-TIA data points are predicted by telicity. -/
theorem eTIA_all_predicted : eTIAData.all eTIA_predicted_by_telicity = true := by
  decide

/-- (1a) Accomplishment → telic → E-TIA acceptable. -/
theorem datum_1a_telic : datum_1a.vendlerClass.telicity = .telic := rfl

/-- (1b) State → atelic → E-TIA unacceptable. -/
theorem datum_1b_atelic : datum_1b.vendlerClass.telicity = .atelic := rfl

/-- (88) Achievement → telic → E-TIA acceptable. -/
theorem datum_88_telic : datum_88.vendlerClass.telicity = .telic := rfl

/-- (84) Activity → atelic → E-TIA unacceptable. -/
theorem datum_84_atelic : datum_84.vendlerClass.telicity = .atelic := rfl

-- ════════════════════════════════════════════════════
-- § 3. Bridge: Telicity → Scale Boundedness → Licensing
-- ════════════════════════════════════════════════════

/-- E-TIA licensing follows from the Kennedy–Rouillard isomorphism:
    telic VPs map to closed/bounded scales, predicting licensing. -/
theorem accomplishment_licensed :
    (scaleBoundedness .accomplishment).isLicensed = true := rfl

theorem achievement_licensed :
    (scaleBoundedness .achievement).isLicensed = true := rfl

/-- Atelic VPs map to open/unbounded scales, predicting blocking. -/
theorem state_blocked :
    (scaleBoundedness .state).isLicensed = false := rfl

theorem activity_blocked :
    (scaleBoundedness .activity).isLicensed = false := rfl

/-- The prediction matches the data for every datum. -/
def eTIA_predicted_by_boundedness (d : ETIADatum) : Bool :=
  (scaleBoundedness d.vendlerClass).isLicensed == d.acceptable

theorem eTIA_boundedness_all_predicted :
    eTIAData.all eTIA_predicted_by_boundedness = true := by decide

-- ════════════════════════════════════════════════════
-- § 4. G-TIA Distribution Data
-- ════════════════════════════════════════════════════

/-- G-TIA datum: polarity × perfect → acceptable? -/
structure GTIADatum where
  /-- Description of the sentence -/
  sentence : String
  /-- Is the sentence negative? -/
  isNegative : Bool
  /-- Does the sentence contain a perfect? -/
  hasPerfect : Bool
  /-- Whether the G-TIA is acceptable -/
  acceptable : Bool
  deriving Repr

/-- (2a) "Mary hasn't been sick in three days." — negative perfect, ✓ -/
def datum_2a : GTIADatum :=
  { sentence := "Mary hasn't been sick in three days"
    isNegative := true, hasPerfect := true, acceptable := true }

/-- (2b) "*Mary has been sick in three days." — positive perfect, ✗ -/
def datum_2b : GTIADatum :=
  { sentence := "Mary has been sick in three days"
    isNegative := false, hasPerfect := true, acceptable := false }

/-- (48) "*Mary wasn't sick in three days." — negative, no perfect, ✗ -/
def datum_48 : GTIADatum :=
  { sentence := "Mary wasn't sick in three days"
    isNegative := true, hasPerfect := false, acceptable := false }

def gTIAData : List GTIADatum :=
  [datum_2a, datum_2b, datum_48]

-- ════════════════════════════════════════════════════
-- § 5. G-TIA Verification: polarity + perfect predicts acceptability
-- ════════════════════════════════════════════════════

/-- G-TIA acceptability predicted by: requires BOTH negative polarity AND perfect.
    @cite{rouillard-2026} Table 1: only NEG + G-TIA + PFV reading is acceptable. -/
def gTIA_predicted (d : GTIADatum) : Bool :=
  (d.isNegative && d.hasPerfect) == d.acceptable

/-- All G-TIA data points match the polarity + perfect prediction. -/
theorem gTIA_all_predicted : gTIAData.all gTIA_predicted = true := by
  decide

-- ════════════════════════════════════════════════════
-- § 5b. Fragment Bridges: derive predictions from Fragment entries
-- ════════════════════════════════════════════════════

/-- G-TIA licensing is derived from Fragment fields: the consensus
    `inGap` entry records `requiresNegation` and `requiresPerfect`. -/
theorem gTIA_licensing_from_fragment :
    inGap.requiresNegation ∧ inGap.requiresPerfect :=
  ⟨trivial, trivial⟩

/-- E-TIA licensing is derived from Fragment: requires telic VP selection,
    not polarity. -/
theorem eTIA_licensing_from_fragment :
    inTelic.vendlerSelection = some .telic ∧ ¬ inTelic.requiresNegation :=
  ⟨rfl, not_false⟩

/-- Polarity-sensitivity status from Fragment: the gap reading is an NPI,
    the telic-completion reading is not. -/
theorem polarity_status_from_fragment :
    inGap.polaritySensitive ∧ ¬ inTelic.polaritySensitive :=
  ⟨trivial, not_false⟩

/-- The Rouillard projection assigns the expected analytical labels:
    E-TIA at event-level for telic-completion *in*; G-TIA at perfect-level
    for the NPI-gap *in*. Stacking acceptability follows: the inner TIA
    must be event-level, the outer must be perfect-level. -/
theorem rouillard_classification :
    inTelic.rouillardClassification? = some ⟨.eTIA, .eventLevel⟩ ∧
    inGap.rouillardClassification?    = some ⟨.gTIA, .perfectLevel⟩ :=
  ⟨rfl, rfl⟩

/-- Out-of-paradigm entries return `none` from the Rouillard projection:
    *for* and *ago* are duration adverbials but not *in*-adverbials, so
    Rouillard's E-TIA / G-TIA dichotomy doesn't apply to them. -/
theorem rouillard_partial :
    forDur.rouillardClassification? = none ∧
    ago.rouillardClassification?    = none :=
  ⟨rfl, rfl⟩

/-- E-TIA and G-TIA share the preposition *in*. -/
theorem shared_preposition_from_fragment :
    inTelic.form = inGap.form := rfl

-- ════════════════════════════════════════════════════
-- § 6. The Perfect Readings (Table 1)
-- ════════════════════════════════════════════════════

/-- @cite{rouillard-2026} Table 1: readings for "*Mary has been sick in three days"
    and its negation, crossed with aspect and TIA type. -/
structure Table1Entry where
  polarity : Bool    -- true = positive, false = negative
  tiaType : Bool     -- true = E-TIA, false = G-TIA
  aspect : Bool      -- true = PFV (E-perfect), false = IMPV (U-perfect)
  mipBlocks : Bool   -- true = MIP blocks this reading
  deriving Repr, DecidableEq

/-- All 8 cells of Table 1 (sentence (112)) "*Mary has been sick in 3 days"). -/
def table1 : List Table1Entry :=
  [ -- Positive readings (all blocked)
    { polarity := true, tiaType := true,  aspect := true,  mipBlocks := true }   -- POS, E-TIA, PFV
  , { polarity := true, tiaType := true,  aspect := false, mipBlocks := true }   -- POS, E-TIA, IMPV
  , { polarity := true, tiaType := false, aspect := true,  mipBlocks := true }   -- POS, G-TIA, PFV
  , { polarity := true, tiaType := false, aspect := false, mipBlocks := true }   -- POS, G-TIA, IMPV
    -- Negative readings (only NEG + G-TIA + PFV survives)
  , { polarity := false, tiaType := true,  aspect := true,  mipBlocks := true }  -- NEG, E-TIA, PFV
  , { polarity := false, tiaType := true,  aspect := false, mipBlocks := true }  -- NEG, E-TIA, IMPV
  , { polarity := false, tiaType := false, aspect := true,  mipBlocks := false } -- NEG, G-TIA, PFV ✓
  , { polarity := false, tiaType := false, aspect := false, mipBlocks := true }  -- NEG, G-TIA, IMPV
  ]

/-- Exactly one reading survives: NEG + G-TIA + PFV (E-perfect). -/
theorem exactly_one_survives :
    (table1.filter (fun e => !e.mipBlocks)).length = 1 := by decide

/-- The surviving reading is the negative G-TIA with perfective aspect. -/
theorem surviving_is_neg_gtia_pfv :
    table1.filter (fun e => !e.mipBlocks) =
    [{ polarity := false, tiaType := false, aspect := true, mipBlocks := false }] := by
  decide

-- ════════════════════════════════════════════════════
-- § 7. Cross-Domain Bridge: Homogeneity ↔ Scale Openness
-- ════════════════════════════════════════════════════

/-- The subinterval property (homogeneity) corresponds to open-scale
    boundedness in the Kennedy–Rouillard isomorphism.
    `homogeneous_iff_durative_atelic` (from LexicalAspect.lean) +
    `atelic_open` (from MaximalInformativity.lean) form the bridge chain:
    homogeneous → state ∨ activity → atelic → open scale → E-TIA blocked. -/
theorem homogeneous_implies_open_scale (p : AspectualProfile)
    (h : p.isHomogeneous = true) :
    scaleBoundedness p.toVendlerClass = .open_ := by
  have hvc := (homogeneous_iff_durative_atelic p).mp h
  rcases hvc with hc | hc <;> rw [hc] <;> decide

/-- Telic → closed scale → E-TIA licensed.
    Note: non-homogeneous alone is insufficient — semelfactives are
    non-homogeneous (punctual) but atelic, mapping to open scale. -/
theorem telic_implies_closed_scale (p : AspectualProfile)
    (h : p.toVendlerClass.telicity = .telic) :
    scaleBoundedness p.toVendlerClass = .closed := by
  exact telic_closed p.toVendlerClass h

-- ════════════════════════════════════════════════════
-- § 8. NPI Bridge: G-TIAs as NPIs Licensed by MIP
-- ════════════════════════════════════════════════════

/-! @cite{rouillard-2026} §6.1 — argues that G-TIAs are NPIs licensed by maximal
    informativity, NOT by downward entailment. The key evidence:

    1. DE-based accounts (@cite{hoeksema-2006}, @cite{gajewski-2005}/2007) incorrectly predict
       E-TIAs should also be polarity-sensitive (they aren't — E-TIAs are aspect-
       sensitive, not polarity-sensitive).
    2. The MIP accounts for BOTH E-TIA (aspect) and G-TIA (polarity) restrictions
       from a single principle.
    3. G-TIAs pattern with strong NPIs (anti-additive, not merely DE), but their
       licensing condition is orthogonal to the DE hierarchy. -/

/-- NPI licensing mechanism: DE vs MIP.
    Rouillard argues MIP subsumes DE for G-TIAs. -/
inductive LicensingMechanism where
  | downwardEntailment   -- @cite{ladusaw-1979}, @cite{hoeksema-2006}, @cite{gajewski-2005}
  | maximalInformativity  -- @cite{rouillard-2026}: MIP
  deriving DecidableEq, Repr

/-- NPI prediction: does a licensing mechanism correctly predict
    both E-TIA and G-TIA distributions? -/
structure NPIPrediction where
  mechanism : LicensingMechanism
  /-- Correctly predicts E-TIA distribution (aspect-sensitive, not polarity)? -/
  predictsETIA : Bool
  /-- Correctly predicts G-TIA polarity sensitivity? -/
  predictsGTIA : Bool
  deriving Repr

/-- DE incorrectly restricts E-TIAs by polarity (Rouillard §6.1, p. 49–50):
    a condition like (144) would block E-TIAs in ALL non-DE environments,
    but E-TIAs are fine in positive telic sentences. -/
def dePrediction : NPIPrediction :=
  { mechanism := .downwardEntailment
    predictsETIA := false   -- ✗ wrongly blocks "wrote a paper in 3 days"
    predictsGTIA := true }  -- ✓ correctly blocks positive G-TIAs

/-- MIP correctly handles both E-TIAs (via telicity/informativity)
    and G-TIAs (via open PTS/information collapse). -/
def mipPrediction : NPIPrediction :=
  { mechanism := .maximalInformativity
    predictsETIA := true    -- ✓ telicity → upward scalar → max⊨ exists
    predictsGTIA := true }  -- ✓ open PTS → no smallest including → collapse

/-- MIP is strictly more explanatory: it handles both distributions.
    DE handles only G-TIAs and makes wrong predictions for E-TIAs. -/
theorem mip_subsumes_de :
    (mipPrediction.predictsETIA && mipPrediction.predictsGTIA = true) ∧
    (dePrediction.predictsETIA = false) := by decide

-- ════════════════════════════════════════════════════
-- § 9. Since-When Questions (§5.2)
-- ════════════════════════════════════════════════════

-- @cite{rouillard-2026} Sect. 5.2: "since when" questions disambiguate E/U-perfect.
--
-- (131) "Since when has Mary been sick?"
--
-- This question lacks the E- vs U-perfect ambiguity of its declarative
-- counterpart.  It has only a U-perfect reading.  The E-perfect reading
-- is blocked: the E-perfect Hamblin set (eq. 137) has no maximally
-- informative true answer (by the open-PTS / closed-runtime argument).
-- The U-perfect Hamblin set (eq. 132) DOES have one.

/-- Since-when question datum: which perfect readings are available? -/
structure SinceWhenDatum where
  sentence : String
  /-- U-perfect reading available? -/
  uPerfect : Bool
  /-- E-perfect reading available? -/
  ePerfect : Bool
  /-- Reason E-perfect is blocked (if blocked) -/
  reason : String
  deriving Repr

/-- (131) "Since when has Mary been sick?" -- U-perfect only.
    @cite{von-fintel-iatridou-2019}: since-when Qs lack E- vs U-perfect ambiguity. -/
def sinceWhen_131 : SinceWhenDatum :=
  { sentence := "Since when has Mary been sick?"
    uPerfect := true
    ePerfect := false
    reason := "E-perfect Hamblin set has no max-informative true answer (open PTS, closed runtime)" }

/-- Since-when questions always lack the E-perfect reading.
    This is predicted by the MIP applied to Hamblin answerhood (eq. 135):
    ANS requires a maximally informative true answer in the Hamblin set,
    but the E-perfect Hamblin set can never have one (by density). -/
theorem sinceWhen_blocks_ePerfect :
    sinceWhen_131.ePerfect = false ∧ sinceWhen_131.uPerfect = true := by
  decide

/-- Fragment bridge: *since* is veridical (presupposes its complement)
    and pins the PTS left boundary (IAI 2001 durative classification),
    matching the since-when question's presupposition structure. The
    perfect-requirement is not a Fragment-level field on `since_conn`
    (which is a connective entry, not a duration adverbial); see the
    discussion in @cite{von-fintel-iatridou-2019}. -/
theorem since_fragment_bridge :
    since_conn.complementVeridical = true ∧
    since_conn.order = TemporalOrder.since_ := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 10. TIA Stacking Constraint (§3.2, ex. 60)
-- ════════════════════════════════════════════════════

/-! @cite{rouillard-2026} §3.2, ex. (60) — when two TIAs are stacked, the inner
    (VP-adjacent) one must be an E-TIA and the outer one a G-TIA. The reverse
    order is ungrammatical.

    (60a) "Mary hasn't written up a paper in three days in two weeks." ✓
           inner = "in three days" (E-TIA, modifies VP)
           outer = "in two weeks" (G-TIA, modifies AspP)

    (60b) "#Mary hasn't written up a paper in two weeks in three days." ✗
           inner = "in two weeks" (G-TIA?), outer = "in three days" (E-TIA?)
           — violates the syntactic position constraint -/

/-- TIA stacking datum: inner and outer adverbial types. -/
structure StackingDatum where
  sentence : String
  /-- Is the inner (VP-adjacent) TIA an E-TIA? -/
  innerIsETIA : Bool
  /-- Is the outer TIA a G-TIA? -/
  outerIsGTIA : Bool
  acceptable : Bool
  deriving Repr

/-- (60a) Inner E-TIA + outer G-TIA: acceptable. -/
def stacking_60a : StackingDatum :=
  { sentence := "Mary hasn't written up a paper in three days in two weeks"
    innerIsETIA := true, outerIsGTIA := true, acceptable := true }

/-- (60b) Reversed order: unacceptable. -/
def stacking_60b : StackingDatum :=
  { sentence := "#Mary hasn't written up a paper in two weeks in three days"
    innerIsETIA := false, outerIsGTIA := false, acceptable := false }

def stackingData : List StackingDatum := [stacking_60a, stacking_60b]

/-- Stacking acceptability = inner is E-TIA ∧ outer is G-TIA.
    Derives from syntactic positions: E-TIAs are event-level (VP-adjacent),
    G-TIAs are perfect-level (AspP-adjacent). Proximity to VP determines
    reading (Rouillard §3.2, schemata (57), (61)). -/
def stacking_predicted (d : StackingDatum) : Bool :=
  (d.innerIsETIA && d.outerIsGTIA) == d.acceptable

theorem stacking_all_predicted :
    stackingData.all stacking_predicted = true := by decide

-- ════════════════════════════════════════════════════
-- § 11. LicensingPipeline Extension
-- ════════════════════════════════════════════════════

/-! ### Connecting E-TIA data to the universal LicensingPipeline

The E-TIA data (§1–3) is verified against `scaleBoundedness` (§3) and
`telicity` (§2). Here we extend the bridge to `LicensingPipeline`, the
universal interface that connects adjective licensing, path licensing,
mereological licensing, and temporal licensing through a single mechanism. -/

/-- Every E-TIA datum is predicted by `LicensingPipeline.isLicensed`. -/
def eTIA_predicted_by_pipeline (d : ETIADatum) : Bool :=
  LicensingPipeline.isLicensed d.vendlerClass == d.acceptable

theorem eTIA_pipeline_all_predicted :
    eTIAData.all eTIA_predicted_by_pipeline = true := by decide

/-- Pipeline agrees with direct scaleBoundedness on all four Vendler classes.
    With compositional chains, the pipeline instance and `scaleBoundedness`
    both route through `VendlerClass →.telicity Telicity →.toMereoTag
    MereoTag →.toBoundedness Boundedness`, so agreement is definitional. -/
theorem pipeline_agrees_with_boundedness :
    (∀ c : VendlerClass,
      LicensingPipeline.isLicensed c =
      (scaleBoundedness c).isLicensed) :=
  fun _ => rfl

-- ════════════════════════════════════════════════════
-- § 12. SituationBoundedness Bridge
-- ════════════════════════════════════════════════════

/-- Atelic (state/activity) collapses like open adjective (tall):
    SituationBoundedness.unbounded ↔ Boundedness.open_. -/
theorem atelic_collapses_like_open_adj :
    LicensingPipeline.isLicensed Core.Time.SituationBoundedness.unbounded =
    LicensingPipeline.isLicensed Boundedness.open_ := rfl

/-- Bounded situations license like closed adjectives (full):
    SituationBoundedness.bounded ↔ Boundedness.closed. -/
theorem bounded_licenses_like_closed_adj :
    LicensingPipeline.isLicensed Core.Time.SituationBoundedness.bounded =
    LicensingPipeline.isLicensed Boundedness.closed := rfl

end Phenomena.TenseAspect.TemporalAdverbials.Rouillard2026
