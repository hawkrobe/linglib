import Linglib.Theories.Semantics.Degree.Comparative
import Linglib.Theories.Semantics.Degree.Intervals
import Linglib.Theories.Semantics.Degree.Intensional
import Linglib.Phenomena.Comparison.Studies.VonStechow1984

/-!
# Büring 2007: Cross-Polar Nomalies
@cite{buring-2007}

Daniel Büring. Cross-Polar Nomalies. SALT 17 (2007).

## Core Puzzle

Cross-polar *anomalies* — comparisons pairing A⁺ with its direct
antonym A⁻ — are ungrammatical: *"John is shorter than Mary is tall."
But cross-polar *nomalies* — comparisons pairing A⁻ with a
non-antonymous A⁺ from a different spatial dimension — are perfectly
acceptable: "The ladder was shorter than the house was high."

## Analysis

LITTLE is a degree negation operator (@cite{heim-2006}):
short = LITTLE long, less = LITTLE -er. Formally, LITTLE complements
a degree predicate: ⟦LITTLE⟧ = λi.λd. i(d) = 0,
mapping positive extents to negative extents (@cite{kennedy-1999}).

Cross-polar nomalies work because MORE LITTLE-A in the main clause
can be reinterpreted as LITTLE-er A. This reinterpretation is blocked
for direct antonyms by comparative deletion (MaxElide) and for inverse
configurations by the requirement that LITTLE license ellipsis only
in its own clause.

Three-way pattern:
- **Cross-polar anomaly**: *A⁺-er than A⁻ / *A⁻-er than A⁺ (direct antonyms) — BAD
- **Cross-polar nomaly**: A⁻-er than A⁺ (different dimensions) — OK
- **Inverse nomaly**: *A⁺-er than A⁻ (different dimensions) — BAD

## Two Competing Analyses (§3 vs §5)

- **Analysis 1** (§3–4, preferred): LITTLE sits with -er in the main
  clause. "shorter than high" = LITTLE-er long than HOW the house is high.
  The degree negation scopes with the comparative morpheme.

- **Analysis 2** (§5): A second LITTLE appears in the than-clause,
  turning high into LITTLE-high (= low). The main-clause LITTLE is then
  elided under identity with the than-clause LITTLE (comparative subdeletion).

Both predict the same truth conditions for basic cases. §6 uses modal
scope as a diagnostic: universal/existential modals in the than-clause
disambiguate the two, favoring Analysis 1.

## Formal Connections

- **LITTLE as extent complement**: `littlePred` maps `posExt` to `negExt`,
  connecting to @cite{kennedy-1999}'s extent algebra in `Core.Scale`.
- **Cross-polar anomaly = algebraic impossibility**: same-dimension
  cross-polar comparison requires `crossExtentInclusion`, which
  `crossExtent_always_false` proves is impossible on any linear order.
- **Cross-polar nomaly = subcomparative**: different-dimension comparison
  is `subcomparative` from @cite{schwarzschild-wilkinson-2002}.
- **Klein limitation bridge**: @cite{von-stechow-1984}'s Klein limitation 3
  ("Ede is more tall than broad") is exactly a `subcomparative`.
-/

namespace Phenomena.Comparison.Studies.Buring2007

open Semantics.Degree.Comparative (comparativeSem ScaleDirection littlePred
  little_posExt_eq_negExt little_involution little_reverses_comparison
  taller_shorter_antonymy)
open Semantics.Degree.Intervals (subcomparative negativeInterval)
open Core.Scale (posExt negExt crossExtentInclusion crossExtent_always_false)

-- ════════════════════════════════════════════════════
-- § 1. LITTLE: Degree Negation on Extents
-- ════════════════════════════════════════════════════

-- LITTLE is now in the theory layer (Theories/Semantics/Degree/Comparative.lean):
--   littlePred, little_posExt_eq_negExt, little_involution,
--   little_reverses_comparison.
-- This section re-exports the key results and adds Büring-specific bridges.

/-- LITTLE maps positive intervals to negative intervals
    (@cite{buring-2007} §4, def. 22): the positive interval [⊥, μ(x)]
    becomes the negative interval [μ(x), ⊤]. This is the interval-level
    counterpart of `little_posExt_eq_negExt` (which operates on extent sets).

    The bridge connects the interval framework (Schwarzschild) to the
    extent framework (Kennedy) via LITTLE. -/
theorem little_positive_to_negative {Entity D : Type*}
    [LinearOrder D] [BoundedOrder D]
    (μ : Entity → D) (x : Entity) :
    (negativeInterval μ x).lower = (Semantics.Degree.Intervals.positiveInterval μ x).upper := by
  simp [negativeInterval, Semantics.Degree.Intervals.positiveInterval]

-- ════════════════════════════════════════════════════
-- § 2. Cross-Polar Anomaly: Algebraic Impossibility
-- ════════════════════════════════════════════════════

/-- **Cross-polar anomaly** = attempting to compare a positive extent
    with a negative extent on the same dimension.

    "?*John is shorter than Mary is tall" requires posExt(Mary) ⊆
    negExt(John), but `crossExtent_always_false` from
    @cite{kennedy-1999}'s extent algebra proves this is impossible on
    any linear order: the boundary degree μ(a) belongs to posExt but
    not negExt, so posExt can never be a subset of negExt.

    Note: @cite{buring-2007}'s explanation is syntactic (MaxElide §3.2),
    not algebraic. The algebraic impossibility is a stronger claim:
    even if the LF were syntactically available, the semantics would
    be vacuous. Büring's account is compatible — MaxElide blocks
    the LF before semantics applies. -/
theorem crossPolar_anomaly_impossible {Entity D : Type*} [LinearOrder D]
    (μ : Entity → D) (a b : Entity) :
    ¬ crossExtentInclusion μ a b :=
  crossExtent_always_false μ a b

-- ════════════════════════════════════════════════════
-- § 3. Cross-Polar Pattern (Data)
-- ════════════════════════════════════════════════════

/-- Classification of cross-polar configurations (p. 3). -/
inductive CrossPolarType where
  | anomaly       -- *A⁺-er than A⁻ / *A⁻-er than A⁺ (direct antonyms)
  | nomaly        -- A⁻-er than A⁺ (different dimensions) — OK
  | inverseNomaly -- *A⁺-er than A⁻ (different dimensions) — BAD
  deriving DecidableEq, Repr

structure CrossPolarDatum where
  sentence : String
  classification : CrossPolarType
  grammatical : Bool
  deriving Repr

def crossPolarData : List CrossPolarDatum :=
  -- Cross-polar anomalies (direct antonyms, same dimension)
  [ ⟨"?*John is shorter than Mary is tall", .anomaly, false⟩
  , ⟨"*Mary is taller than John is short", .anomaly, false⟩
  -- Cross-polar nomalies (different dimensions, A⁻ in main clause)
  , ⟨"The ladder was shorter than the house was high", .nomaly, true⟩
  , ⟨"My yacht is shorter than yours is wide", .nomaly, true⟩
  , ⟨"Your dinghy should be shorter than your boat is wide", .nomaly, true⟩
  -- Inverse cross-polar nomalies (different dimensions, A⁺ in main)
  , ⟨"*The house is higher than the ladder is short", .inverseNomaly, false⟩
  ]

-- Nomalies are the only grammatical cross-polar configuration.
#guard crossPolarData.all (λ d =>
  d.grammatical == (d.classification == .nomaly))

-- ════════════════════════════════════════════════════
-- § 4. Cross-Polar Nomalies = Subcomparatives
-- ════════════════════════════════════════════════════

-- Cross-polar nomalies are subcomparatives (@cite{schwarzschild-wilkinson-2002}):
-- comparing two different measure functions on a shared spatial extent
-- scale (p. 1–2, footnote 2).
--
-- "The ladder is shorter(length) than the house is high(height)"
-- means: the house's height exceeds the ladder's length.
--
-- Unlike cross-polar *anomalies*, which attempt to compare positive
-- and negative extents on the SAME dimension (impossible by
-- `crossPolar_anomaly_impossible`), nomalies compare positive extents
-- on DIFFERENT dimensions via `subcomparative`. Since the two measure
-- functions are distinct (length ≠ height), no cross-extent
-- contradiction arises — the comparison reduces to a simple
-- inequality μ₂(b) > μ₁(a) on the shared spatial extent scale.
--
-- This is the formal core of @cite{buring-2007}'s analysis:
-- the "more-to-less metamorphosis" reinterprets a comparison of
-- negative extents (via LITTLE) across dimensions as a comparison
-- of positive extents — which is just `subcomparative`.
section Nomalies

  /-- When both dimensions use the same measure function, the
      subcomparative collapses to the standard comparative:
      "a is shorter than b" = "b is taller than a". -/
  theorem subcomparative_same_dimension {Entity D : Type*} [LinearOrder D]
      (μ : Entity → D) (a b : Entity) :
      subcomparative μ μ a b ↔ comparativeSem μ a b .positive :=
    Iff.rfl

end Nomalies

-- ════════════════════════════════════════════════════
-- § 5. Concrete Example
-- ════════════════════════════════════════════════════

section LadderHouse

  private inductive Thing | ladder | house
    deriving DecidableEq, Repr

  private def height : Thing → ℚ | .ladder => 5 | .house => 20
  private def length : Thing → ℚ | .ladder => 15 | .house => 40

  /-- "The ladder was shorter(length=15) than the house was high(height=20)":
      a subcomparative on the shared spatial extent scale.
      height(house) > length(ladder). -/
  example : subcomparative height length .house .ladder := by
    simp [subcomparative, height, length]; norm_num

end LadderHouse

-- ════════════════════════════════════════════════════
-- § 6. Why Anomalies Are Blocked
-- ════════════════════════════════════════════════════

/-- @cite{buring-2007}'s syntactic explanation for why direct-antonym
    cross-polar constructions are anomalous (§3.2): when A⁻ and
    A⁺ ARE direct antonyms (same dimension), comparative deletion
    (ellipsis of the whole A in the than-clause) produces a competing
    form. MaxElide (Takahashi and Fox 2005) prefers this deletion,
    blocking the cross-polar LF.

    For nomalies, deletion is unavailable because the adjectives differ
    (long ≠ high), so no competition arises (§3.3).

    Inverse nomalies (*A⁺-er than A⁻, different dimensions) are blocked
    because LITTLE in the main clause cannot license ellipsis in the
    than-clause (§3.4): the LF "the house is MORE high [than
    HOW the ladder is LITTLE-long]" cannot be reinterpreted as
    "LITTLE-er high" because LITTLE and MORE are in separate clauses. -/
structure AnomalyBlockingDatum where
  sentence : String
  whyBlocked : String
  competingForm : String
  deriving Repr

def anomalyBlocking : List AnomalyBlockingDatum :=
  [ ⟨"?*John is shorter than Mary is tall"
   , "comparative deletion: 'shorter than Mary (is tall)' → 'shorter than Mary'"
   , "John is shorter than Mary"⟩
  , ⟨"*The house is higher than the ladder is short"
   , "inverse: LITTLE in main clause cannot license than-clause ellipsis"
   , "(no well-formed competitor)"⟩
  ]

-- ════════════════════════════════════════════════════
-- § 7. Bridge to Von Stechow's Klein Limitation
-- ════════════════════════════════════════════════════

/-- @cite{von-stechow-1984}'s Klein limitation 3: "Ede is more tall
    than broad" is a cross-dimensional comparison that Klein's
    degree-free framework cannot express.

    @cite{buring-2007}'s cross-polar nomalies are the same phenomenon:
    "shorter(length) than high(height)" compares different dimensions
    on a shared spatial extent scale. Both require degree ontology
    (specifically, `subcomparative` from @cite{schwarzschild-wilkinson-2002}).

    Definitionally: comparing two dimensions of the same entity is
    `subcomparative μ₁ μ₂ a a`, which unfolds to `μ₁ a > μ₂ a`. -/
theorem klein_limitation_is_subcomparative {Entity D : Type*} [LinearOrder D]
    (μ₁ μ₂ : Entity → D) (a : Entity) :
    subcomparative μ₁ μ₂ a a ↔ (μ₁ a > μ₂ a) :=
  Iff.rfl

-- ════════════════════════════════════════════════════
-- § 8. Modal Scope Diagnostic (§6)
-- ════════════════════════════════════════════════════

-- @cite{buring-2007} §6: modals in the than-clause disambiguate the
-- two competing analyses. The key test case (p. 11, ex. 29):
--
-- "The existing drawbridge is shorter than the new moat has to be wide."
--
-- **Analysis 1** (LITTLE in main clause, preferred):
-- LF: [LITTLE-more [λd than MUST the moat be d-wide] [λd the bridge is d-long]]
-- = the min-required width of the moat > the actual length of the bridge.
--
-- **Analysis 2** (LITTLE in than-clause):
-- LF: [more [λd than MUST the moat be d-LITTLE-wide] [λd the bridge is d-LITTLE-long]]
-- = the max-permitted narrowness of the moat > the actual shortness of the bridge.
--
-- The modal scopes between -er and the adjective in the than-clause.
-- Under Analysis 1, HAS-TO scopes over the positive A (wide), yielding
-- "min required width." Under Analysis 2, HAS-TO scopes over the
-- negative A (LITTLE-wide = narrow), yielding "max permitted narrowness."
-- Only Analysis 1 matches native speaker intuitions.
section ModalDiagnostic

  -- Scenario from p. 11: drawbridge (length 15ft), moat must be ≥ 30ft wide
  private inductive CastlePart | bridge | moat
    deriving DecidableEq, Repr

  -- Three deontic worlds: moat widths 30, 35, 40 (all ≥ 30ft minimum)
  private inductive PermittedWorld | w30 | w35 | w40
    deriving DecidableEq, Repr

  private def moatWidth : PermittedWorld → ℚ
    | .w30 => 30 | .w35 => 35 | .w40 => 40

  private def bridgeLength : ℚ := 15

  /-- **Analysis 1** (preferred): LITTLE scopes with -er in main clause.
      The than-clause denotes {d | ∀w ∈ Deon(@). d ≤ WIDTH_w(moat)},
      whose max is the minimum required width (= 30).
      The comparative asserts: min-required-width > bridge-length.

      Truth conditions: the bridge is shorter than the moat's minimum
      required width. This is correct — the bridge (15ft) can't span
      a moat that must be at least 30ft wide. -/
  def analysis1_minRequiredWidth : ℚ :=
    min (min (moatWidth .w30) (moatWidth .w35)) (moatWidth .w40)

  theorem analysis1_correct :
      analysis1_minRequiredWidth > bridgeLength := by
    simp [analysis1_minRequiredWidth, moatWidth, bridgeLength]; norm_num

  /-- **Analysis 2**: LITTLE scopes in the than-clause (with the adjective).
      HAS-TO scopes over LITTLE-wide (= narrow). The than-clause denotes
      {d | ∀w ∈ Deon(@). NARROWNESS_w(moat) ≥ d}, whose max is the
      min narrowness across permitted worlds — i.e., the narrowness in
      the world where the moat is widest (= 40ft → narrowness is minimal).

      On a bounded scale [0, maxWidth], narrowness = maxWidth - width.
      Min narrowness = maxWidth - max(width) = maxWidth - 40.
      For any reasonable maxWidth, this is smaller than bridge shortness.

      Truth conditions: we could (but don't have to) build a moat narrow
      enough that the bridge would span it. This does NOT match the
      intuition of (29), which asserts the bridge is too short, period. -/
  def analysis2_maxPermittedNarrowness (maxWidth : ℚ) : ℚ :=
    maxWidth - max (max (moatWidth .w30) (moatWidth .w35)) (moatWidth .w40)

  /-- Analysis 2 predicts narrowness of (maxWidth - 40). For any
      reasonable maxWidth (e.g. 50), this is 10 — less than the bridge
      length of 15. So Analysis 2 would predict the sentence is FALSE
      (the bridge IS long enough for the widest-possible moat-narrowness).
      This is the wrong prediction. -/
  theorem analysis2_wrong_at_50 :
      ¬ (analysis2_maxPermittedNarrowness 50 > bridgeLength) := by
    simp [analysis2_maxPermittedNarrowness, moatWidth, bridgeLength]; norm_num

  /-- The two analyses diverge: Analysis 1 predicts TRUE (bridge too short),
      Analysis 2 predicts FALSE (bridge long enough). Native speakers
      judge the sentence true, confirming Analysis 1. -/
  theorem analyses_diverge :
      (analysis1_minRequiredWidth > bridgeLength) ∧
      ¬ (analysis2_maxPermittedNarrowness 50 > bridgeLength) :=
    ⟨analysis1_correct, analysis2_wrong_at_50⟩

end ModalDiagnostic

-- ════════════════════════════════════════════════════
-- § 9. Existential Modal Variant (§6.2)
-- ════════════════════════════════════════════════════

/-- @cite{buring-2007} §6.2 (p. 14, ex. 38): existential modals
    produce the same disambiguation.

    "The moat is narrower than drawbridges are allowed to be long."

    Analysis 1: moat width < max permitted bridge length.
    Paraphrase: "we can get a bridge that spans the moat."

    Analysis 2: moat narrowness < max permitted bridge shortness.
    Paraphrase: weaker — about permitted shortness, not length. -/
structure ModalNomalyDatum where
  sentence : String
  modalForce : String   -- "universal" or "existential"
  analysis1Reading : String
  analysis2Reading : String
  nativeSpeakerMatch : Bool  -- true = Analysis 1 matches
  deriving Repr

def modalDiagnosticData : List ModalNomalyDatum :=
  [ ⟨"The drawbridge is shorter than the moat has to be wide"
   , "universal"
   , "min-required width > bridge length"
   , "max-permitted narrowness > bridge shortness"
   , true⟩
  , ⟨"The moat is narrower than drawbridges are allowed to be long"
   , "existential"
   , "moat width < max-permitted bridge length"
   , "moat narrowness < max-permitted bridge shortness"
   , true⟩
  , ⟨"The new reservoir is less deep than church towers were allowed to be tall"
   , "existential"
   , "reservoir depth < max-permitted tower height"
   , "reservoir shallowness < max-permitted tower shortness"
   , true⟩
  ]

-- All modal diagnostic cases favor Analysis 1.
#guard modalDiagnosticData.all (·.nativeSpeakerMatch)

end Phenomena.Comparison.Studies.Buring2007
