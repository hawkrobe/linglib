import Linglib.Pragmatics.RSA.LatentOperators
import Linglib.Pragmatics.RSA.Operators
import Linglib.Semantics.Degree.Gradability.Intensification
import Linglib.Fragments.English.Predicates.Adjectival
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FinCases

/-!
# [nouwen-2024] Deadjectival Intensifiers
[lassiter-goodman-2017] [nouwen-2024]

"The semantics and probabilistic pragmatics of deadjectival intensifiers"
Semantics and Pragmatics, Volume 17, Article 2.

## Empirical Generalizations

1. **Goldilocks effect**: Negative-evaluative bases (horrible, terrible)
   yield high-degree intensifiers; positive-evaluative bases (pleasant, nice)
   yield moderate-degree intensifiers.

2. **Zwicky's generalization**: Modal adjectives with negative polarity
   (unusual, surprising, impossible) can intensify, but their positive
   counterparts (usual, expected, possible) cannot.

## RSA Model

Extends [lassiter-goodman-2017] threshold RSA with **evaluative measures**:
deadjectival adverbs (horribly, pleasantly) derive their degree function
from the evaluative meaning of their adjectival base.

**Measure function simplification**: The paper uses f(x) = x² for negative
evaluation and a Gaussian for positive evaluation (handcrafted proof-of-concept
functions). Our formalization uses |d − norm| and norm − |d − norm| respectively
(linear/triangular). Both preserve the qualitative shape: negative measures peak
at extremes, positive measures peak at the norm.

### Probabilistic model

The RSA model — the rejected simultaneous dual-threshold configuration
(Nouwen's (49)) and the paper's final sequential/backgrounded chain
(eqs. 50–51) — lives on the mathlib-PMF face in the "Probabilistic model" sections
below, where the predictions are proven
structurally: ratio cancellation collapses each marginalised speaker to a
mass-monotone sum over the licensed thresholds, and informativity
monotonicity beats the prior ratio. This file houses the semantic layer:
the intensifier lexicon, the meaning functions and their theory-layer
grounding, the exact Goldilocks boundary, the Wheeler leak, and the
licensing-support order.
-/

-- ============================================================================
-- §1. Empirical Data (§2)
-- ============================================================================

namespace Nouwen2024.Intensifiers

open Features (EvaluativeValence)

/--
Intensifier degree class (Figure 2).

- **H** (high): targets extreme degrees ("horribly warm" ≈ very warm)
- **M** (moderate): targets moderate degrees ("pleasantly warm" ≈ nicely warm)
-/
inductive IntensifierClass where
  | H  -- high degree
  | M  -- moderate degree
  deriving Repr, DecidableEq

/--
Classification of adjectival base for deadjectival intensifiers
([nouwen-2024] §2.4).

- **evaluative**: core case — horrible, pleasant, nice
- **mirative**: non-evaluative but extremity-sensitive — unusual, surprising, remarkable
- **modal**: epistemic modals — impossible, possible, usual, expected
- **dimensional**: degree adjectives — tall, short (not productive as intensifiers)
-/
inductive BaseKind where
  | evaluative
  | mirative
  | modal
  | dimensional
  deriving Repr, DecidableEq

/--
A deadjectival intensifier entry.

Records the adverb form, its adjectival base, evaluative properties,
modal status, and attestation pattern.
-/
structure IntensifierEntry where
  /-- Adverb form -/
  adverb : String
  /-- Adjectival base -/
  adjBase : String
  /-- Evaluative valence of the base -/
  valence : EvaluativeValence
  /-- Degree class as intensifier -/
  class_ : IntensifierClass
  /-- Base classification: evaluative, mirative, modal, or dimensional -/
  baseKind : BaseKind := .evaluative
  /-- Deviation polarity: whether the base denotes deviation from or
      conformity with expectation/norm.
      - `some .negative` = deviation (unusual, impossible, horrible)
      - `some .positive` = conformity (usual, expected, possible)
      - `none` = not applicable (evaluative bases without modal/mirative content)
      Named `deviationPolarity` rather than `modalPolarity` because miratives
      are not modal (§2.4.2) — the shared property is deviation from norm. -/
  deviationPolarity : Option EvaluativeValence := none
  /-- Whether the evaluative content is bleached in adverbial use -/
  bleached : Bool := false
  /-- Whether the intensifier use is attested -/
  attested : Bool := true
  /-- Goldilocks exception: extreme positive evaluatives (remarkable, stunning)
      are H-degree despite positive valence. The paper acknowledges (p. 2:9)
      that extreme evaluations and manner implicatures can override the
      default valence→class mapping. -/
  goldilocksException : Bool := false
  deriving Repr

-- Intensifier Data (Figure 2)

-- Negative-evaluative → High degree (H)

def horribly : IntensifierEntry :=
  { adverb := "horribly", adjBase := "horrible"
  , valence := .negative, class_ := .H, bleached := true }

def terribly : IntensifierEntry :=
  { adverb := "terribly", adjBase := "terrible"
  , valence := .negative, class_ := .H, bleached := true }

def awfully : IntensifierEntry :=
  { adverb := "awfully", adjBase := "awful"
  , valence := .negative, class_ := .H, bleached := true }

-- dreadfully/frighteningly follow the same pattern as horribly/terribly
-- but are not in the paper's Figure 2 survey or mentioned in the text.

def dreadfully : IntensifierEntry :=
  { adverb := "dreadfully", adjBase := "dreadful"
  , valence := .negative, class_ := .H, bleached := true }

def frighteningly : IntensifierEntry :=
  { adverb := "frighteningly", adjBase := "frightening"
  , valence := .negative, class_ := .H, bleached := true }

-- Positive-evaluative → Moderate degree (M)

def pleasantly : IntensifierEntry :=
  { adverb := "pleasantly", adjBase := "pleasant"
  , valence := .positive, class_ := .M }

def nicely : IntensifierEntry :=
  { adverb := "nicely", adjBase := "nice"
  , valence := .positive, class_ := .M }

def decently : IntensifierEntry :=
  { adverb := "decently", adjBase := "decent"
  , valence := .positive, class_ := .M }

-- Mirative → High degree (H), attested
-- Miratives express deviation from expectation (§2.4.2), not evaluation.

def unusually : IntensifierEntry :=
  { adverb := "unusually", adjBase := "unusual"
  , valence := .neutral, class_ := .H
  , baseKind := .mirative, deviationPolarity := some .negative }

def surprisingly : IntensifierEntry :=
  { adverb := "surprisingly", adjBase := "surprising"
  , valence := .neutral, class_ := .H
  , baseKind := .mirative, deviationPolarity := some .negative }

-- Negative modal → High degree (H), attested

def impossibly : IntensifierEntry :=
  { adverb := "impossibly", adjBase := "impossible"
  , valence := .neutral, class_ := .H
  , baseKind := .modal, deviationPolarity := some .negative }

-- Extreme positive-evaluative → High degree (Goldilocks exception)
-- The paper (§2.4.1) classifies "remarkable" as evaluative, not mirative.
-- It produces H-degree despite positive valence because extreme positive
-- evaluation (like extreme negative evaluation) targets scale extremes.

def remarkably : IntensifierEntry :=
  { adverb := "remarkably", adjBase := "remarkable"
  , valence := .positive, class_ := .H
  , goldilocksException := true }

-- Positive modal → unattested as intensifiers (Zwicky's generalization)

def usually_ : IntensifierEntry :=
  { adverb := "*usually", adjBase := "usual"
  , valence := .neutral, class_ := .M
  , baseKind := .modal, deviationPolarity := some .positive
  , attested := false }

def expectedly_ : IntensifierEntry :=
  { adverb := "*expectedly", adjBase := "expected"
  , valence := .neutral, class_ := .M
  , baseKind := .modal, deviationPolarity := some .positive
  , attested := false }

def possibly_ : IntensifierEntry :=
  { adverb := "*possibly", adjBase := "possible"
  , valence := .neutral, class_ := .M
  , baseKind := .modal, deviationPolarity := some .positive
  , attested := false }

-- Additional negative-evaluative → H (Figure 2 survey data)

def disgustingly : IntensifierEntry :=
  { adverb := "disgustingly", adjBase := "disgusting"
  , valence := .negative, class_ := .H, bleached := true }

def annoyingly : IntensifierEntry :=
  { adverb := "annoyingly", adjBase := "annoying"
  , valence := .negative, class_ := .H, bleached := true }

def unpleasantly : IntensifierEntry :=
  { adverb := "unpleasantly", adjBase := "unpleasant"
  , valence := .negative, class_ := .H, bleached := true }

def scarily : IntensifierEntry :=
  { adverb := "scarily", adjBase := "scary"
  , valence := .negative, class_ := .H, bleached := true }

-- Additional positive-evaluative → M (Figure 2 survey data)

def wonderfully : IntensifierEntry :=
  { adverb := "wonderfully", adjBase := "wonderful"
  , valence := .positive, class_ := .M }

def beautifully_ : IntensifierEntry :=
  { adverb := "beautifully", adjBase := "beautiful"
  , valence := .positive, class_ := .M }

def delightfully : IntensifierEntry :=
  { adverb := "delightfully", adjBase := "delightful"
  , valence := .positive, class_ := .M }

def gorgeously : IntensifierEntry :=
  { adverb := "gorgeously", adjBase := "gorgeous"
  , valence := .positive, class_ := .M }

-- Additional extreme positive-evaluative → H (Figure 2 survey data)
-- Like remarkably, stunningly is positive-evaluative but H-degree (§2.4.1,
-- Figure 2 upper-right quadrant: high valence, high temperature response).

def stunningly : IntensifierEntry :=
  { adverb := "stunningly", adjBase := "stunning"
  , valence := .positive, class_ := .H
  , goldilocksException := true }

-- All entries

def allEntries : List IntensifierEntry :=
  [ horribly, terribly, awfully, dreadfully, frighteningly
  , disgustingly, annoyingly, unpleasantly, scarily
  , pleasantly, nicely, decently
  , wonderfully, beautifully_, delightfully, gorgeously
  , unusually, surprisingly, impossibly, remarkably, stunningly
  , usually_, expectedly_, possibly_ ]

-- Goldilocks Effect (§3)

/--
The Goldilocks effect (§2.3): base kind and valence determine degree class.

- Negative-evaluative bases yield high-degree (H) intensifiers
- Positive-evaluative bases yield moderate-degree (M) intensifiers
- Miratives always yield H (deviation from expectation targets extremes; §2.4.2)
- Modals: negative deviation → H, positive (conformity) → M
- Goldilocks exceptions (e.g., remarkably, stunningly): extreme positive
  evaluatives that yield H despite positive valence (p. 2:9)
-/
def goldilocksHolds (e : IntensifierEntry) : Bool :=
  if e.goldilocksException then e.class_ == .H
  else match e.baseKind with
  | .evaluative =>
    match e.valence with
    | .negative => e.class_ == .H
    | .positive => e.class_ == .M
    | .neutral  => true
  | .mirative => e.class_ == .H
  | .modal =>
    match e.deviationPolarity with
    | some .negative => e.class_ == .H
    | some .positive => e.class_ == .M
    | _ => true
  | .dimensional => true

-- Per-datum verification

theorem horribly_goldilocks : goldilocksHolds horribly = true := by native_decide
theorem terribly_goldilocks : goldilocksHolds terribly = true := by native_decide
theorem awfully_goldilocks : goldilocksHolds awfully = true := by native_decide
theorem dreadfully_goldilocks : goldilocksHolds dreadfully = true := by native_decide
theorem frighteningly_goldilocks : goldilocksHolds frighteningly = true := by native_decide
theorem disgustingly_goldilocks : goldilocksHolds disgustingly = true := by native_decide
theorem annoyingly_goldilocks : goldilocksHolds annoyingly = true := by native_decide
theorem unpleasantly_goldilocks : goldilocksHolds unpleasantly = true := by native_decide
theorem scarily_goldilocks : goldilocksHolds scarily = true := by native_decide
theorem pleasantly_goldilocks : goldilocksHolds pleasantly = true := by native_decide
theorem nicely_goldilocks : goldilocksHolds nicely = true := by native_decide
theorem decently_goldilocks : goldilocksHolds decently = true := by native_decide
theorem wonderfully_goldilocks : goldilocksHolds wonderfully = true := by native_decide
theorem beautifully_goldilocks : goldilocksHolds beautifully_ = true := by native_decide
theorem delightfully_goldilocks : goldilocksHolds delightfully = true := by native_decide
theorem gorgeously_goldilocks : goldilocksHolds gorgeously = true := by native_decide
theorem unusually_goldilocks : goldilocksHolds unusually = true := by native_decide
theorem surprisingly_goldilocks : goldilocksHolds surprisingly = true := by native_decide
theorem impossibly_goldilocks : goldilocksHolds impossibly = true := by native_decide
theorem remarkably_goldilocks : goldilocksHolds remarkably = true := by native_decide
theorem stunningly_goldilocks : goldilocksHolds stunningly = true := by native_decide

-- Zwicky's Generalization (§3.2)

/--
Zwicky's generalization (§2.5, [zwicky-1970]): among modal/mirative
adjectives, only those denoting deviation from expectation (negative
deviation polarity) can serve as intensifiers; conformity-denoting ones
(positive deviation polarity) cannot.

- "unusually warm" ✓ (deviation → attested)
- "impossibly warm" ✓ (deviation → attested)
- "*usually warm" ✗ (conformity → unattested)

This restriction does NOT extend to evaluatives (§2.5, (28)-(30)):
both "pleasantly warm" and "unpleasantly warm" are attested.
-/
def zwickyHolds (e : IntensifierEntry) : Bool :=
  match e.baseKind with
  | .modal | .mirative =>
    match e.deviationPolarity with
    | some .negative => e.attested
    | some .positive => !e.attested
    | _ => true
  | _ => true

-- Per-datum verification

theorem unusually_zwicky : zwickyHolds unusually = true := by native_decide
theorem surprisingly_zwicky : zwickyHolds surprisingly = true := by native_decide
theorem impossibly_zwicky : zwickyHolds impossibly = true := by native_decide
-- remarkably/stunningly are evaluative (not modal/mirative), so Zwicky
-- doesn't apply to them — both polarities are productive for evaluatives.
theorem usually_zwicky : zwickyHolds usually_ = true := by native_decide
theorem expectedly_zwicky : zwickyHolds expectedly_ = true := by native_decide
theorem possibly_zwicky : zwickyHolds possibly_ = true := by native_decide

-- Summary statistics

/-- Count of attested intensifiers -/
def attestedCount : Nat := (allEntries.filter (·.attested)).length

/-- Count of unattested intensifiers -/
def unattestedCount : Nat := (allEntries.filter (!·.attested)).length

#guard attestedCount == 21
#guard unattestedCount == 3

-- ════════════════════════════════════════════════════
-- Fragment Bridge
-- ════════════════════════════════════════════════════

/-- Look up the Fragment adjective entry for an intensifier's adjectival base. -/
def IntensifierEntry.fragmentEntry (e : IntensifierEntry) :
    Option Semantics.Gradability.GradableAdjective :=
  English.Predicates.Adjectival.lookup e.adjBase

/-- Bridge: pleasant's Fragment entry has positive evaluative valence,
    matching the intensifier layer's valence for pleasantly. -/
theorem pleasant_valence_bridge :
    (pleasantly.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

/-- Bridge: nice's Fragment entry has positive evaluative valence,
    matching the intensifier layer's valence for nicely. -/
theorem nice_valence_bridge :
    (nicely.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

/-- Bridge: decent's Fragment entry has positive evaluative valence,
    matching the intensifier layer's valence for decently. -/
theorem decent_valence_bridge :
    (decently.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

/-- Bridge: beautiful's Fragment entry has positive evaluative valence,
    matching the intensifier layer's valence for beautifully. -/
theorem beautiful_valence_bridge :
    (beautifully_.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

-- Negative-evaluative bridges (H-degree)

theorem horrible_valence_bridge :
    (horribly.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

theorem terrible_valence_bridge :
    (terribly.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

theorem awful_valence_bridge :
    (awfully.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

theorem dreadful_valence_bridge :
    (dreadfully.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

theorem frightening_valence_bridge :
    (frighteningly.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

theorem disgusting_valence_bridge :
    (disgustingly.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

theorem annoying_valence_bridge :
    (annoyingly.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

theorem unpleasant_valence_bridge :
    (unpleasantly.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

theorem scary_valence_bridge :
    (scarily.fragmentEntry.bind (·.evaluativeValence)) = some .negative := by
  native_decide

-- Positive-evaluative bridges (M-degree)

theorem wonderful_valence_bridge :
    (wonderfully.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

theorem delightful_valence_bridge :
    (delightfully.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

theorem gorgeous_valence_bridge :
    (gorgeously.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

-- Mirative bridges (neutral valence)

theorem unusual_valence_bridge :
    (unusually.fragmentEntry.bind (·.evaluativeValence)) = some .neutral := by
  native_decide

theorem surprising_valence_bridge :
    (surprisingly.fragmentEntry.bind (·.evaluativeValence)) = some .neutral := by
  native_decide

theorem remarkable_valence_bridge :
    (remarkably.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

theorem stunning_valence_bridge :
    (stunningly.fragmentEntry.bind (·.evaluativeValence)) = some .positive := by
  native_decide

-- Modal bridges (neutral valence)

theorem usual_valence_bridge :
    (usually_.fragmentEntry.bind (·.evaluativeValence)) = some .neutral := by
  native_decide

theorem expected_valence_bridge :
    (expectedly_.fragmentEntry.bind (·.evaluativeValence)) = some .neutral := by
  native_decide

theorem possible_valence_bridge :
    (possibly_.fragmentEntry.bind (·.evaluativeValence)) = some .neutral := by
  native_decide

theorem impossible_valence_bridge :
    (impossibly.fragmentEntry.bind (·.evaluativeValence)) = some .neutral := by
  native_decide

-- ════════════════════════════════════════════════════
-- Universal Bridge: all entries resolve and agree
-- ════════════════════════════════════════════════════

/-- Every intensifier entry's adjectival base resolves to a Fragment entry. -/
theorem all_bases_resolve :
    allEntries.all (·.fragmentEntry.isSome) = true := by
  native_decide

/-- Every intensifier entry's evaluative valence matches its Fragment entry's.
    This is the key integration theorem: changes to either the intensifier
    data or the Fragment entries will break this if they disagree. -/
theorem all_valences_agree :
    allEntries.all (λ e =>
      e.fragmentEntry.bind (·.evaluativeValence) == some e.valence) = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- Derived Structural Properties
-- ════════════════════════════════════════════════════

/-- All intensifier bases have open scales (§2.1, fn. 3: "I will restrict my
    attention to adjectives with open-ended scales"). Derived from the Fragment.
    *Decent* also derives an open `.value` scale: its necessity standard
    ([kennedy-mcnally-2005]) is a `standardOverride`, not scale boundedness, so it
    no longer needs the exception the earlier lower-bounded modeling required. -/
theorem all_bases_open_scale :
    allEntries.all (λ e =>
      match e.fragmentEntry with
      | some a => a.scaleType == .open_
      | none => false) = true := by
  native_decide

/-- All bleached intensifiers have negative evaluative bases (§2.2–2.3).
    Bleaching is a diachronic process: the negative evaluative content
    ("it is horrible that...") is lost, leaving only the degree function
    (extremity). This historical process systematically targeted negative
    evaluatives, not positive ones. Derived from the data. -/
theorem bleached_implies_negative :
    (allEntries.filter (·.bleached)).all
      (·.valence == .negative) = true := by
  native_decide

/-- Zwicky's restriction does NOT extend to evaluatives (§2.5, (28)–(30)):
    "The weather was pleasantly / unpleasantly warm." Both positive and
    negative evaluative intensifiers are attested. -/
theorem zwicky_evaluative_both_attested :
    (allEntries.filter (·.baseKind == .evaluative)).all
      (·.attested) = true := by
  native_decide

/-- Evaluative intensifiers come in both positive and negative valence.
    (Contrast with modals, where only deviation-denoting bases intensify.) -/
theorem evaluative_has_both_polarities :
    (allEntries.filter (λ e => e.baseKind == .evaluative && e.valence == .positive)).length > 0 ∧
    (allEntries.filter (λ e => e.baseKind == .evaluative && e.valence == .negative)).length > 0 := by
  native_decide

/-- The Goldilocks effect holds universally across all entries (including
    exceptions, which are handled by the `goldilocksException` flag). -/
theorem goldilocks_universal :
    allEntries.all goldilocksHolds = true := by
  native_decide

/-- Zwicky's generalization holds for all modal/mirative entries. -/
theorem zwicky_universal :
    allEntries.all zwickyHolds = true := by
  native_decide

/-- Goldilocks exceptions are all positive-evaluative H-degree adverbs.
    They represent extreme positive evaluation (remarkable, stunning) where
    the extremity of the evaluation, rather than its polarity, determines
    the degree class. -/
theorem goldilocks_exceptions_are_positive_H :
    (allEntries.filter (·.goldilocksException)).all
      (λ e => e.valence == .positive && e.class_ == .H) = true := by
  native_decide

/-- Antonym consistency: every intensifier entry whose Fragment base has
    an antonym can also look up that antonym in the Fragment. -/
theorem antonym_pairs_resolve :
    allEntries.all (λ e =>
      match e.fragmentEntry.bind (·.antonymForm) with
      | some ant => (English.Predicates.Adjectival.lookup ant).isSome
      | none => true) = true := by
  native_decide

end Nouwen2024.Intensifiers

-- ============================================================================
-- §2. RSA Model
-- ============================================================================

namespace RSA.Nouwen2024

-- Local scale: n=6 (Degree 6 = Fin 7, Threshold 6 = Fin 6). Norm = 3.

instance : NeZero (6 : Nat) := ⟨by omega⟩

abbrev Height := Degree.Degree 6
abbrev Threshold := Degree.Threshold 6

open Degree (deg thr)
open Features (EvaluativeValence)
open Semantics.Gradability.Intensification (EvaluativeMeasure)
open Degree (positiveMeaning)

/-- ⟦tall⟧(θ)(x) = 1 iff height(x) > θ, specialized to scale 6. -/
def tallMeaning (θ : Threshold) (h : Height) : Bool :=
  positiveMeaning h θ

/-- Height prior: discretized bell curve centered at h3 (norm for scale 6).
    Weights: [1, 5, 10, 20, 10, 5, 1] (sum = 52). -/
def heightPrior (h : Height) : ℚ :=
  match h.toNat with
  | 0 => 1
  | 1 => 5
  | 2 => 10
  | 3 => 20   -- peak (mean)
  | 4 => 10
  | 5 => 5
  | _ => 1

-- Utterances

/--
Utterances about warmth with optional deadjectival intensifier.

The utterance set extends bare "warm" with intensified variants.
-/
inductive Utterance where
  | bare_warm       -- "x is warm"
  | horribly_warm   -- "x is horribly warm"
  | pleasantly_warm -- "x is pleasantly warm"
  | silent          -- say nothing
  deriving Repr, DecidableEq, Fintype

def allUtterances : List Utterance :=
  [.bare_warm, .horribly_warm, .pleasantly_warm, .silent]

-- Evaluative Measures (ℕ-valued)

/--
Evaluative measure for "horrible" applied to the Height domain.

μ_horrible(h) = |h - norm|

Heights far from the norm (3) are evaluated as more "horrible".
Agrees with `Intensification.muHorrible 6` (see `meaning_grounded_horribly`).
-/
def muHorrible (h : Height) : ℕ :=
  let d := h.toNat
  if d ≥ 3 then d - 3 else 3 - d

/--
Evaluative measure for "pleasant" applied to the Height domain.

μ_pleasant(h) = norm - |h - norm|

Heights near the norm (3) are evaluated as more "pleasant".
Agrees with `Intensification.muPleasant 6` (see `meaning_grounded_pleasantly`).
-/
def muPleasant (h : Height) : ℕ :=
  let d := h.toNat
  if d ≥ 3 then 6 - d else d

-- Meaning Function

/--
Full meaning function.

- bare_warm: h > θ (standard [lassiter-goodman-2017])
- horribly_warm: (h > θ) ∧ (μ_horrible(h) > θ_e)
- pleasantly_warm: (h > θ) ∧ (μ_pleasant(h) > θ_e)
- silent: always true
-/
def meaning (u : Utterance) (h : Height) (θ θ_e : Threshold) : Bool :=
  match u with
  | .bare_warm       => tallMeaning θ h
  | .horribly_warm   => tallMeaning θ h && (muHorrible h > θ_e.toNat)
  | .pleasantly_warm => tallMeaning θ h && (muPleasant h > θ_e.toNat)
  | .silent          => true

-- Theory-Layer Grounding

/-- Local ℕ-valued `muHorrible` agrees with theory-layer ℚ-valued
    `Intensification.muHorrible` on every height. The theory definition
    `(d : ℕ → ℚ) - norm` collapses to `|d - 3|` when norm = 6/2 = 3 and d : ℕ. -/
private lemma muHorrible_eq (h : Height) :
    (Semantics.Gradability.Intensification.muHorrible 6).mu h.toNat =
    (muHorrible h : ℚ) := by
  unfold Semantics.Gradability.Intensification.muHorrible muHorrible
  fin_cases h <;> simp [Degree.Degree.toNat] <;> norm_num

/--
The local horribly_warm meaning agrees with theory-layer `intensifiedMeaning`
for all inputs. This bridges the ℕ-valued local measures to the ℚ-valued
theory-layer `Intensification.muHorrible`.
-/
theorem meaning_grounded_horribly (h : Height) (θ θ_e : Threshold) :
    (meaning .horribly_warm h θ θ_e = true) ↔
    Semantics.Gradability.Intensification.intensifiedMeaning
      (Semantics.Gradability.Intensification.muHorrible 6) h θ θ_e := by
  simp only [meaning, tallMeaning, Bool.and_eq_true, decide_eq_true_eq,
             Semantics.Gradability.Intensification.intensifiedMeaning,
             muHorrible_eq, Nat.cast_lt]

private lemma muPleasant_eq (h : Height) :
    (Semantics.Gradability.Intensification.muPleasant 6).mu h.toNat =
    (muPleasant h : ℚ) := by
  unfold Semantics.Gradability.Intensification.muPleasant muPleasant
  fin_cases h <;> simp [Degree.Degree.toNat] <;> norm_num

/--
The local pleasantly_warm meaning agrees with theory-layer `intensifiedMeaning`
for all inputs. This bridges the ℕ-valued local measures to the ℚ-valued
theory-layer `Intensification.muPleasant`.
-/
theorem meaning_grounded_pleasantly (h : Height) (θ θ_e : Threshold) :
    (meaning .pleasantly_warm h θ θ_e = true) ↔
    Semantics.Gradability.Intensification.intensifiedMeaning
      (Semantics.Gradability.Intensification.muPleasant 6) h θ θ_e := by
  simp only [meaning, tallMeaning, Bool.and_eq_true, decide_eq_true_eq,
             Semantics.Gradability.Intensification.intensifiedMeaning,
             muPleasant_eq, Nat.cast_lt]

-- Structural Semantics: Goldilocks, Wheeler, and Licensing Support

/-! ### The Goldilocks effect as a set-theoretic fact

[nouwen-2024] p. 21: "horribly warm will end up being compatible only with the
higher degrees in this range. Note that extremely low temperatures are also
horrible, but they are not in the interval [d, d′], because we arrived at that
interval using the positive form of the adjective." The paper calls Goldilocks
"merely a tendency" (p. 9; fn. 14 notes the expressive-taboo exception). On
this scale the tendency has an exact boundary — `θ + θ_e ≥ 2`
(`horriblyWarm_upperClosed_iff`): below it the intensified meaning leaks into
the cold tail, which is precisely the Wheeler problem of the paper's Fig. 5
(`wheeler_cold_leak`). -/

/-- `S` is upward closed within `B`: any `B`-world at least as high as some
`S`-world is itself in `S`. -/
def UpwardClosedWithin (S B : Height → Bool) : Prop :=
  ∀ h h', S h = true → B h' = true → h.toNat ≤ h'.toNat → S h' = true

instance (S B : Height → Bool) : Decidable (UpwardClosedWithin S B) := by
  unfold UpwardClosedWithin; infer_instance

/-- **Goldilocks, exactly**: *horribly warm* is an upper set within *warm* iff
the adjectival and evaluative thresholds jointly reach the `norm − 1`
boundary (`θ + θ_e ≥ 2` on the Degree-6 scale, norm = 3). The U-shaped
`μ_horrible` targets both scale extremes, but the positive form of *warm* has
already cut off the cold end whenever the thresholds are high enough. -/
theorem horriblyWarm_upperClosed_iff (θ θ_e : Threshold) :
    UpwardClosedWithin (fun h => meaning .horribly_warm h θ θ_e)
      (fun h => meaning .bare_warm h θ θ_e) ↔ 2 ≤ θ.toNat + θ_e.toNat := by
  revert θ θ_e; decide

/-- Positive evaluations are "reserved for the middle of a scale"
([nouwen-2024] p. 21): whenever *pleasantly warm* is satisfiable at all, it is
never an upper set within *warm* — the mid-peaked `μ_pleasant` cannot produce
upper-tail intensification. (The nonemptiness guard excludes the vacuous
`θ_e ≥ 3` cases, where no height is pleasant enough.) -/
theorem pleasantlyWarm_never_upperClosed (θ θ_e : Threshold)
    (hne : ∃ h, meaning .pleasantly_warm h θ θ_e = true) :
    ¬ UpwardClosedWithin (fun h => meaning .pleasantly_warm h θ θ_e)
      (fun h => meaning .bare_warm h θ θ_e) := by
  revert θ θ_e; decide

/-- **The Wheeler leak** ([nouwen-2024] Fig. 5, p. 27: "horribly warm is not
(entirely) incompatible with things being horribly cold"): below the
Goldilocks boundary, *horribly warm* is true at cold heights. This is the
semantic root of the problem the paper's backgrounded (sequential) update is
designed to mitigate. -/
theorem wheeler_cold_leak :
    ∃ (θ θ_e : Threshold) (h : Height),
      h.toNat < 3 ∧ meaning .horribly_warm h θ θ_e = true := by
  decide

/-! ### Licensing support: the proof engine for the pragmatic shifts

The latent pairs licensing an utterance at a world form the rectangle
`[0, h) × [0, μ(h))`, so support inclusion is componentwise dominance in the
two measures: higher-and-more-extreme worlds license strictly more latents —
the structural mechanism behind upward intensification (the pragmatic
listener sums over licensed latents). -/

/-- The latent threshold pairs at which `u` is true at `h`. -/
def licensingSet (u : Utterance) (h : Height) : Finset (Threshold × Threshold) :=
  Finset.univ.filter fun l => meaning u h l.1 l.2

/-- Componentwise measure dominance yields licensing-support inclusion:
if `w₁` is at least as high and at least as extreme as `w₂`, every latent
licensing *horribly warm* at `w₂` licenses it at `w₁`. -/
theorem licensingSet_horribly_mono {w₂ w₁ : Height}
    (hw : w₂.toNat ≤ w₁.toNat) (hμ : muHorrible w₂ ≤ muHorrible w₁) :
    licensingSet .horribly_warm w₂ ⊆ licensingSet .horribly_warm w₁ := by
  intro l hl
  simp only [licensingSet, Finset.mem_filter, Finset.mem_univ, true_and, meaning,
    tallMeaning, Bool.and_eq_true, decide_eq_true_eq] at hl ⊢
  obtain ⟨h1, h2⟩ := hl
  exact ⟨lt_of_lt_of_le h1 (by exact_mod_cast hw), by omega⟩

/-- The file's key comparison pair has *strict* support inclusion: the extreme
height `deg 5` licenses strictly more latents than the moderate `deg 2`. -/
theorem licensingSet_deg2_ssubset_deg5 :
    licensingSet .horribly_warm (deg 2) ⊂ licensingSet .horribly_warm (deg 5) := by
  decide

/-- Licensing support is **not** totally ordered: below the norm, lower
heights are warmer-false but more extreme, so their supports are
incomparable — the inclusion order is exactly componentwise dominance, not a
chain. -/
theorem licensingSet_not_totalOrder :
    ¬ (licensingSet .horribly_warm (deg 1) ⊆ licensingSet .horribly_warm (deg 2)) ∧
    ¬ (licensingSet .horribly_warm (deg 2) ⊆ licensingSet .horribly_warm (deg 1)) := by
  decide

-- Zwicky Vacuity

/--
Constant evaluative measure (no evaluative content).

Models adverbs like "*usually" — a constant measure provides no
discriminating information about degree, which is why "*usually warm"
is vacuous (Zwicky's generalization).
-/
def muUsual : EvaluativeMeasure 6 where
  form := "usual"
  valence := .neutral
  mu := λ _ => 3

/--
A constant evaluative measure provides no information:
for any two heights, the measure value is identical.
-/
theorem usual_constant :
    ∀ h₁ h₂ : Height, muUsual.mu h₁.toNat = muUsual.mu h₂.toNat := by
  intro h₁ h₂
  simp [muUsual]

-- Utterance Cost Structure

/--
Intensified utterances are costlier than bare utterances.

assumes that "horribly warm" has higher production cost
than "warm" because it contains more morphological material.
This cost differential drives the pragmatic reasoning.
-/
def utteranceCost : Utterance → ℚ
  | .bare_warm       => 1
  | .horribly_warm   => 2
  | .pleasantly_warm => 2
  | .silent          => 0

-- ============================================================================
-- Sequential Model (key innovation)
-- ============================================================================

/-! ## Sequential Dual-Threshold Model — types

[nouwen-2024]'s key innovation: the evaluative adverb and base adjective
apply sequentially — the listener first updates on the evaluative measure,
then applies the adjective threshold to the resulting posterior (eqs. 50–51).
The chain itself and its predictions live in the probabilistic-model
sections below; this section provides the stage utterance types, meanings,
and costs they consume. -/

-- Step 1: Evaluative update

/-- Utterances for the evaluative step: either the evaluative positive form
    ("the degree is horribly/pleasantly X") or silence. -/
inductive EvalUtterance where
  | eval_pos  -- the evaluative positive form holds
  | silent    -- say nothing
  deriving Repr, DecidableEq, Fintype

/-- Evaluative meaning for step 1.
    The evaluative positive form checks only μ_eval(h) > θ_e, without the
    base adjective. This is the decomposed evaluative component. -/
def evalMeaning (evalMu : Height → ℕ) (u : EvalUtterance) (h : Height) (θ_e : Threshold) : Bool :=
  match u with
  | .eval_pos => evalMu h > θ_e.toNat
  | .silent   => true

/-- Evaluative step cost: the evaluative adverb costs 1, silence costs 0. -/
def evalCost : EvalUtterance → ℚ
  | .eval_pos => 1
  | .silent   => 0


-- Step 2: Adjective update with updated prior

/-- Utterances for the adjective step. -/
inductive AdjUtterance where
  | warm   -- "x is warm"
  | silent -- say nothing
  deriving Repr, DecidableEq, Fintype

/-- Adjective meaning for step 2: just the base positive form h > θ. -/
def adjMeaning (u : AdjUtterance) (h : Height) (θ : Threshold) : Bool :=
  match u with
  | .warm   => tallMeaning θ h
  | .silent => true

def adjCost : AdjUtterance → ℚ
  | .warm   => 1
  | .silent => 0


-- ============================================================================
-- Probabilistic model (PMF face)
-- ============================================================================

/-!
## The probabilistic model on mathlib `PMF`

[nouwen-2024] [lassiter-goodman-2017]

[nouwen-2024] ("The semantics and probabilistic pragmatics of
deadjectival intensifiers", *Semantics & Pragmatics* 17:2, 1-45, 2024)
gives an intersective semantic analysis of intensified adjectives
(*horribly warm*, *pleasantly warm*) plus a chained-Bayesian pragmatic
update. The sections below formalise the §4 Bayesian machinery, with explicit acknowledgment of what it does and does not
capture.

## Scope (honest reckoning, post-audit)

The file's `priorAfterEvalPos` + `seqAdjL1HorriblyWarm` correctly
implement the **two-update Bayesian chain** of [nouwen-2024] Eq. 73
(p. 2:41): first update Π = stage-1 L1 at `.eval_pos`, then second update
ρ = stage-2 L1 with Π as prior. The L&G "two priors" pattern (Π enters
both stage-2 L0 via `L0LassiterGoodman` AND stage-2 L1 via `PMF.posterior`)
is structurally faithful.

**However, the file is NOT a faithful Nouwen 2024 formalisation.** It is
"L&G two-priors chain typed against `Height`", missing three core pieces
of Nouwen's actual contribution:

1. **Eq. 44/45 intersecting positive forms — NOT formalised.** Nouwen's
   *novel* semantic proposal (paper p. 2:21) is the conjunction
   `(μ_A(x) ≥ θ_i) ∧ (μ_D(λw.μ_A(x)(@) = μ_A(x)(w)) ≥ θ_j)`. The second
   conjunct is a Wheeler-style **factive embedding** of the proposition
   "x has its actual measure" — explicitly motivated as the fix for the
   soup-too-warm-to-eat counterexample to Nouwen 2010 Eq. 35. The file's
   stage-1 evaluative meaning predicates `muHorrible` of heights directly,
   without the propositional embedding. Without Eq. 44b's factive layer,
   the prediction is L&G's, not Nouwen's. Stub theorem
   `eq_44b_factive_embedding_NOT_FORMALISED` below documents the gap.
2. **Eq. 49 QUD partition `Q^A_X` — NOT formalised.** Nouwen's σ/ρ are
   defined over equivalence classes `[w]_~^A_X` where `w ~^A_X w' iff
   μ_A(x)(w) ≈ μ_A(x)(w')` (with explicit granularity). The file
   operates over raw `Height` with no quotient/equivalence relation. At
   small Height-cardinality the partition collapses to identity and the
   shortcut is vacuously fine for the toy example, but the file cannot
   extend to Nouwen's Figures 4-7 construction (which depends on the
   QUD partition + measure-function-on-cells distinction). Stub theorem
   `eq_49_qud_partition_NOT_FORMALISED` below documents the gap.
3. **`muHorrible` is linear `|h − norm|`, NOT Nouwen's `f(x) = x²`
   quadratic.** Nouwen's Figure 4(b) handcrafts `f(x) = x²`; the file's
   `muHorrible = |h − 3|` (deg 0 ↦ 3, deg 3 ↦ 0, deg 6 ↦ 3) is the
   linear-V simplification. Both are U-shaped — both extremes count as
   horrible, which is what the Wheeler leak (`wheeler_cold_leak` in the
   bundled file) and the Goldilocks boundary depend on — but slopes and
   hence fitted magnitudes differ. Paper (p. 31): the model is "a proof
   of concept"; the theorems here are shape-generic where possible.

**Also captured (§5d–§5g):**
- **Zwicky's generalisation** (paper §5): the constant measure's update
  is the identity (`priorAfterEvalPosUsual_eq_prior`), so "usually warm"
  collapses to bare "warm" (`seqUsually_eq_bare`), while `μ_unusual =
  μ_horrible` definitionally and the extreme-measure update strictly
  boosts the extreme above its prior (`eval_unusual_boosts_extreme`).
- **Positive-valence half** (Figure 8): `seq_pleasantly_prefers_moderate`
  — a support fact (`μ_pleasant (deg 6) = 0` licenses no threshold).

## Connection to `LassiterGoodman2017PMF.lean`

[nouwen-2024] §4 explicitly adopts the [lassiter-goodman-2017]
RSA framework and modifies it to sequential two-update inference (vs L&G's
single-step joint posterior over `(world, threshold)`). The structural
relationship:

* L&G 2017 PMF: single-step `posterior κ μ b` against a uniform threshold prior
* Nouwen 2024 PMF (this file): chained `posterior κ₂ (posterior κ₁ μ b₁) b₂`

The chained-posterior decomposition lemma `PMF.posterior_chained_lt_iff_score_lt`
in `Core/Probability/Posterior.lean` (modeled on mathlib's
`Mathlib.Probability.Kernel.Posterior.posterior_comp`) characterises this
shape; the headline below uses it.

## Cross-framework positioning (linglib's "make incompatibilities visible")

[nouwen-2024] §3.1 surveys four contenders for intensifier semantics,
Nouwen's own intersection proposal being the FOURTH:

1. Wheeler 1972 factive: `horrible(λw. μ_warm(t)(w) = μ_warm(t)(@))` (Eq. 32)
2. Morzycki 2008 extreme: `horribly warm` = "horrible how *extremely* warm"
3. Nouwen 2010 existential boost: `∃d[μ_warm(t)(@) ≥ d ∧ horrible(λw.μ_warm(t)(w) ≥ d)]` (Eq. 33-35)
4. Nouwen 2024 intersection: Eq. 44/45 (this file's nominal target)

NONE of (1)-(3) are formalised in linglib. `Semantics/Gradability/Intensification.lean`
ships only Nouwen 2024's intersection as `intensifiedMeaning` — silently
adopting one of the four contenders as if uncontested. The cross-framework
auditor flagged this as a broader linglib gap; the fix is an
`IntensifierSemantics` typeclass at the Theory level (deferred — out of
scope for this file).

## Proof obligations

- `seq_horribly_shifts_upward` — PROVEN structurally (§5b ratio
  cancellation): the height factor cancels in each per-threshold speaker,
  collapsing the marginals to mass-monotone sums over the licensed
  thresholds; informativity (`gval 1 > gval 0`) beats the 2:1 prior ratio.
  No numeric reflection.
- `eq_44b_factive_embedding_NOT_FORMALISED` — Nouwen's novel contribution.
- `eq_49_qud_partition_NOT_FORMALISED` — explicit substrate gap.

## Reused from the semantic layer above

* `Height`, `Threshold`, `EvalUtterance`, `evalMeaning`, `muHorrible`,
  `tallMeaning`, `heightPrior` — data + Boolean meanings
* `evalCost`, `adjCost` — cost values
-/

open scoped ENNReal
/-! ## §1. Height prior as a PMF -/

/-- Height prior weights as `ℝ≥0∞`. Reuses `heightPrior : Height → ℚ` from
`Nouwen2024.lean` (a discretized bell curve, weights summing to 52). -/
noncomputable def heightPriorENN (h : Height) : ℝ≥0∞ :=
  ENNReal.ofReal (heightPrior h : ℝ)

theorem heightPriorENN_pos (h : Height) : heightPriorENN h ≠ 0 := by
  unfold heightPriorENN
  rw [ENNReal.ofReal_ne_zero_iff]
  exact_mod_cast by unfold heightPrior; split <;> norm_num

theorem heightPriorENN_finite (h : Height) : heightPriorENN h ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The height prior as a normalized `PMF Height`. Built directly from
mathlib's `PMF.normalize` with the Fintype-shape tsum discharges:
`tsum_ne_zero_iff` (witness form) and `tsum_ne_top_of_fintype`. -/
noncomputable def heightPriorPMF : PMF Height :=
  PMF.normalize heightPriorENN
    (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨deg 3, heightPriorENN_pos _⟩)
    (ENNReal.tsum_ne_top_of_fintype heightPriorENN_finite)

theorem heightPriorPMF_pos (h : Height) : heightPriorPMF h ≠ 0 := by
  unfold heightPriorPMF
  rw [PMF.normalize_apply]
  exact mul_ne_zero (heightPriorENN_pos h)
    (ENNReal.inv_ne_zero.mpr (ENNReal.tsum_ne_top_of_fintype heightPriorENN_finite))

/-! ## §2. ValidThreshold subtype + conversion -/

/-- The latent threshold restricted to values with non-empty `.eval_pos`
extension under `muHorrible` / `muPleasant`. Both measures have max value
3, so `θ.toNat ∈ {0,1,2}` are the only thresholds that produce non-empty
literal-listener extensions (per ## Empty-extension in the module
docstring). -/
abbrev ValidThreshold : Type := Fin 3

/-- Convert `ValidThreshold` into the original `Threshold = Fin 6` type
(via `Fin.castLE 3 ≤ 6`). -/
def validToThreshold (vt : ValidThreshold) : Threshold :=
  ⟨vt.castLE (by omega)⟩

/-- Uniform prior over `ValidThreshold`. -/
noncomputable def thresholdPriorPMF : PMF ValidThreshold :=
  PMF.uniformOfFintype ValidThreshold

/-! ## §3. Stage 1 — evaluative L0/S1/L1 (under `muHorrible`)

Pattern: Boolean `evalLex` → L&G L0 with `heightPriorPMF` (`L0LassiterGoodman`) →
`S1Belief` rpow speaker with `evalCostFactor` and α=4 → marginalize over
`ValidThreshold` via `marginalizeKernel` → `PMF.posterior`. -/

/-- Evaluative Boolean lex at threshold `θ` (just argument-reordering of
`Nouwen2024.evalMeaning`). Type matches `L0LassiterGoodman`'s shape. -/
def evalLex (evalMu : Height → ℕ) (θ : Threshold) (u : EvalUtterance) (h : Height) : Bool :=
  evalMeaning evalMu u h θ

/-- Witness for the `L0LassiterGoodman` positivity hypothesis at any valid
θ and any utterance: `deg 0` is in every extension. For `.silent` trivially;
for `.eval_pos` because `muHorrible (deg 0) = 3 > θ.toNat` for θ ∈ {0,1,2}. -/
theorem evalLex_horrible_extension_pos (vt : ValidThreshold) (u : EvalUtterance) :
    (∑' h, heightPriorPMF h *
      (if evalLex muHorrible (validToThreshold vt) u h then (1 : ℝ≥0∞) else 0)) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨deg 0, ?_⟩
  -- Show: heightPriorPMF (deg 0) * indicator > 0
  cases u
  · -- .eval_pos: indicator = (3 > θ.toNat); for vt ∈ Fin 3, this is true
    show heightPriorPMF _ *
      (if evalLex muHorrible (validToThreshold vt) .eval_pos (deg 0) then
        (1 : ℝ≥0∞) else 0) ≠ 0
    -- Reduce: muHorrible (deg 0) = 3 (since deg 0 has toNat = 0, i.e. d < 3, so muHorrible = 3 - 0 = 3)
    have : evalLex muHorrible (validToThreshold vt) .eval_pos (deg 0) = true := by
      unfold evalLex evalMeaning
      simp only []
      have : muHorrible (deg 0) = 3 := by
        unfold muHorrible
        rfl
      rw [this]
      decide +revert
    rw [this]
    simp only [if_true, mul_one]
    exact heightPriorPMF_pos _
  · -- .silent: always true
    show heightPriorPMF _ *
      (if evalLex muHorrible (validToThreshold vt) .silent (deg 0) then
        (1 : ℝ≥0∞) else 0) ≠ 0
    have : evalLex muHorrible (validToThreshold vt) .silent (deg 0) = true := rfl
    rw [this]
    simp only [if_true, mul_one]
    exact heightPriorPMF_pos _

/-- Stage 1 literal listener under `muHorrible` at valid threshold `vt`. -/
noncomputable def evalL0_horribleAt (vt : ValidThreshold) :
    EvalUtterance → PMF Height :=
  fun u => RSA.L0LassiterGoodman heightPriorPMF
    (evalLex muHorrible (validToThreshold vt)) u
    (evalLex_horrible_extension_pos vt u)

/-- Cost factor for the rpow speaker form: `cost u → exp(-α · cost u)`.
Hardcodes Nouwen's `evalCost` (eval_pos = 1, silent = 0) and α = 4. -/
noncomputable def evalCostFactor (u : EvalUtterance) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-4 * (evalCost u : ℝ)))

theorem evalCostFactor_pos (u : EvalUtterance) : evalCostFactor u ≠ 0 := by
  unfold evalCostFactor
  rw [ENNReal.ofReal_ne_zero_iff]
  exact Real.exp_pos _

theorem evalCostFactor_finite (u : EvalUtterance) : evalCostFactor u ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Stage 1 speaker under `muHorrible` at valid threshold `vt`. Per-θ
S1Belief, normalized over utterances at each Height. Positivity discharges
via `.silent` witness using `RSA.L0LassiterGoodman_apply_of_meaning_true`
(which says: `L0` at `.silent` equals the prior unchanged, since
`evalLex .silent` is identically `true`). -/
noncomputable def evalSpeaker_horribleAt (vt : ValidThreshold) (w : Height) : PMF EvalUtterance :=
  RSA.S1Belief (evalL0_horribleAt vt) evalCostFactor 4 w
    -- Positivity: at `.silent` witness, L0 = heightPriorPMF (positive); cost ≠ 0; rpow ≠ 0.
    (by
      apply ENNReal.summable.tsum_ne_zero_iff.mpr
      refine ⟨.silent, ?_⟩
      have hL0 : evalL0_horribleAt vt .silent w = heightPriorPMF w := by
        unfold evalL0_horribleAt
        exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _
      rw [hL0]
      apply mul_ne_zero _ (evalCostFactor_pos .silent)
      have hpos : 0 < heightPriorPMF w := pos_iff_ne_zero.mpr (heightPriorPMF_pos w)
      have hntop : heightPriorPMF w ≠ ⊤ := PMF.apply_ne_top _ _
      exact (ENNReal.rpow_pos hpos hntop).ne')
    -- Finiteness: each summand is finite (Fintype + rpow of bounded base).
    (by
      apply ENNReal.tsum_ne_top_of_fintype
      intro u
      exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
        (evalCostFactor_finite u))

/-- Marginalize Stage 1 speaker over `ValidThreshold` (uniform prior).
Eq 70's marginalization step, restricted to thresholds with non-empty
extension. -/
noncomputable def evalSpeakerMarginalHorrible : Height → PMF EvalUtterance :=
  RSA.marginalizeKernel thresholdPriorPMF (fun vt w => evalSpeaker_horribleAt vt w)

/-- Stage 1 L1 = pragmatic listener via `PMF.posterior`. The prior is
`heightPriorPMF`; the speaker kernel is the threshold-marginalized
`evalSpeakerMarginalHorrible`. -/
noncomputable def evalL1Horrible (u : EvalUtterance) : PMF Height :=
  PMF.posterior evalSpeakerMarginalHorrible heightPriorPMF u
    -- Marginal positivity: pick (h, u) = (deg 0, _). heightPriorPMF (deg 0) > 0;
    -- speaker (deg 0) u > 0 because at vt = 0, L0(u | deg 0, vt=0) is positive
    -- (deg 0 is in extension for both .silent and .eval_pos at θ=0).
    (PMF.marginal_ne_zero _ _ _ (heightPriorPMF_pos (deg 0)) (by
      -- evalSpeakerMarginalHorrible (deg 0) u ≠ 0
      -- = PMF.bind thresholdPriorPMF (fun vt => evalSpeaker_horribleAt vt (deg 0)) u
      -- = ∑' vt, thresholdPriorPMF vt * evalSpeaker_horribleAt vt (deg 0) u
      -- Pick vt = 0; both factors positive.
      unfold evalSpeakerMarginalHorrible
      rw [RSA.marginalizeKernel_apply]
      apply ENNReal.summable.tsum_ne_zero_iff.mpr
      refine ⟨0, ?_⟩
      apply mul_ne_zero
      · -- thresholdPriorPMF 0 = 1/3 ≠ 0
        rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]
        simp
      · -- evalSpeaker_horribleAt 0 (deg 0) u ≠ 0 via S1Belief_apply_ne_zero_of_pos
        -- with hL0 from mem_support_L0LassiterGoodman_iff (matches priorAfterEvalPos discharge)
        have hL0 : evalL0_horribleAt 0 u (deg 0) ≠ 0 := by
          unfold evalL0_horribleAt
          rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
          refine ⟨heightPriorPMF_pos _, ?_⟩
          -- For .eval_pos: muHorrible(deg 0) = 3 > 0 = true
          -- For .silent: always true
          cases u
          · -- .eval_pos
            simp only [evalLex, evalMeaning, decide_eq_true_eq]
            show muHorrible (deg 0) > 0
            decide
          · -- .silent
            rfl
        unfold evalSpeaker_horribleAt
        exact RSA.S1Belief_apply_ne_zero_of_pos
          (evalL0_horribleAt 0) evalCostFactor 4 (deg 0) _ _ hL0 (evalCostFactor_pos u)))

/-! ## §4. Sequential composition: Π = stage 1 L1 at `.eval_pos`

This Π becomes the prior for stage 2 (Nouwen eq 73). The L&G "two priors"
pattern then has Π appearing both inside the stage-2 L0 (via
`L0LassiterGoodman Π adjLex`) and outside in the stage-2 L1 (via
`PMF.posterior _ Π`). -/

/-- Π — stage 1 L1 at `.eval_pos`, used as stage 2's prior. -/
noncomputable def priorAfterEvalPos : PMF Height :=
  evalL1Horrible .eval_pos

/-! ## §5. Stage 2 — adjective L0/S1/L1 (under `tallMeaning`/`warm`)

Mirrors stage 1 with prior `Π` instead of `heightPriorPMF`, and with
the bare-warm Boolean `tallMeaning` instead of `evalMeaning`. -/

/-- Adjective Boolean lex at threshold `θ`. Reuses Nouwen's `AdjUtterance`
(`warm | silent`) and `adjMeaning`. -/
def adjLex (θ : Threshold) (u : RSA.Nouwen2024.AdjUtterance) (h : Height) : Bool :=
  RSA.Nouwen2024.adjMeaning u h θ

/-- **Restricted version** of "Π is positive": Π is positive at heights with
non-zero `muHorrible` (the eval listener concludes the height is in the
"horribly" extension). At heights where `muHorrible h = 0` (e.g. `deg 3`),
Π(h) = 0 — those are precisely the heights "ruled out" by the .eval_pos
observation. The unrestricted `priorAfterEvalPos_pos` would be FALSE at deg 3,
which was the bug in the original sorry'd statement. -/
theorem priorAfterEvalPos_pos_at_horrible_pos {h : Height} (hpos : 0 < muHorrible h) :
    priorAfterEvalPos h ≠ 0 := by
  unfold priorAfterEvalPos evalL1Horrible
  rw [← PMF.mem_support_iff, PMF.mem_support_posterior_iff]
  refine ⟨heightPriorPMF_pos h, ?_⟩
  -- evalSpeakerMarginalHorrible h .eval_pos ≠ 0: witness vt = 0, then S1Belief positive.
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply]
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨0, ?_⟩
  apply mul_ne_zero
  · rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
  · -- evalSpeaker_horribleAt 0 h .eval_pos ≠ 0 via S1Belief_apply_ne_zero_of_pos
    -- with hL0 from mem_support_L0LassiterGoodman_iff (using muHorrible h > 0 = vt.toNat)
    have hL0 : evalL0_horribleAt 0 .eval_pos h ≠ 0 := by
      unfold evalL0_horribleAt
      rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
      refine ⟨heightPriorPMF_pos h, ?_⟩
      -- evalLex muHorrible (validToThreshold 0) .eval_pos h = true; reduce via evalMeaning
      simp only [evalLex, evalMeaning, decide_eq_true_eq]
      -- Goal: muHorrible h > (validToThreshold 0).toNat. The latter = 0 by rfl.
      show muHorrible h > 0
      exact hpos
    unfold evalSpeaker_horribleAt
    exact RSA.S1Belief_apply_ne_zero_of_pos
      (evalL0_horribleAt 0) evalCostFactor 4 h _ _ hL0 (evalCostFactor_pos .eval_pos)

/-- Witness for stage 2's `L0LassiterGoodman` positivity: at threshold
θ ∈ {0,1,2} and utterance `.warm`, the height `deg 5` (or any h with
`tallMeaning θ h = true`) gives non-zero contribution. -/
theorem adjLex_warm_extension_pos (vt : ValidThreshold) (u : RSA.Nouwen2024.AdjUtterance) :
    (∑' h, priorAfterEvalPos h *
      (if adjLex (validToThreshold vt) u h then (1 : ℝ≥0∞) else 0)) ≠ 0 := by
  -- For .warm at threshold vt, deg 5 satisfies (5 > vt.toNat)
  -- For .silent, deg 0 (or any h) trivially true
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨deg 5, ?_⟩
  cases u
  · -- .warm: tallMeaning vt (deg 5) = (5 > vt.toNat); for vt ∈ Fin 3, true
    show priorAfterEvalPos _ *
      (if adjLex (validToThreshold vt) .warm (deg 5) then
        (1 : ℝ≥0∞) else 0) ≠ 0
    have : adjLex (validToThreshold vt) .warm (deg 5) = true := by
      unfold adjLex RSA.Nouwen2024.adjMeaning RSA.Nouwen2024.tallMeaning
      -- Goal: positiveMeaning (deg 5) (validToThreshold vt) = true, i.e. vt < 5 as Degree
      -- vt : Fin 3 means vt.val ∈ {0,1,2}; case-bash with decide.
      fin_cases vt <;> decide
    rw [this]
    simp only [if_true, mul_one]
    exact priorAfterEvalPos_pos_at_horrible_pos (by decide)
  · -- .silent: always true
    show priorAfterEvalPos _ * _ ≠ 0
    have : adjLex (validToThreshold vt) .silent (deg 5) = true := rfl
    rw [this]
    simp only [if_true, mul_one]
    exact priorAfterEvalPos_pos_at_horrible_pos (by decide)

/-- Stage 2 literal listener with prior Π (the L&G "two priors" pattern:
Π enters here, AND will enter again at the L1 stage). -/
noncomputable def adjL0_warmAt (vt : ValidThreshold) : RSA.Nouwen2024.AdjUtterance → PMF Height :=
  fun u => RSA.L0LassiterGoodman priorAfterEvalPos
    (adjLex (validToThreshold vt)) u (adjLex_warm_extension_pos vt u)

noncomputable def adjCostFactor (u : RSA.Nouwen2024.AdjUtterance) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-4 * (RSA.Nouwen2024.adjCost u : ℝ)))

/-- Stage 2 speaker under `tallMeaning` at valid threshold `vt`.

**Conditional fallback at degenerate worlds**: at world `w` where `Π(w) = 0`
(e.g., `w = deg 3` since `muHorrible(deg 3) = 0` so deg 3 has zero posterior
under "eval_pos"), all `adjL0_warmAt vt u w = 0` (reweight against
zero-mass prior gives zero), so `S1Belief`'s positivity hypothesis fails.
At those degenerate worlds the speaker is irrelevant to the L1 (since
the prior is 0 there too), so we fall back to a vacuous uniform PMF.
This is the bundled API's `if l0 = 0 then 0` guard, lifted to the type
level via `dite`. -/
noncomputable def adjSpeaker_warmAt (vt : ValidThreshold) (w : Height) :
    PMF (RSA.Nouwen2024.AdjUtterance) :=
  if h_pos : (∑' u, ((adjL0_warmAt vt) u w : ℝ≥0∞) ^ (4 : ℝ) * adjCostFactor u) ≠ 0 then
    RSA.S1Belief (adjL0_warmAt vt) adjCostFactor 4 w h_pos
      (ENNReal.tsum_ne_top_of_fintype fun u =>
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
          (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top))
  else
    -- Vacuous fallback at degenerate w (where Π(w) = 0). PMF.pure picks any
    -- AdjUtterance arbitrarily; doesn't affect downstream L1 since prior is 0.
    PMF.pure .silent

/-- Marginalize Stage 2 speaker over `ValidThreshold`. -/
noncomputable def adjSpeakerMarginal : Height → PMF AdjUtterance :=
  RSA.marginalizeKernel thresholdPriorPMF (fun vt w => adjSpeaker_warmAt vt w)

/-- **Sequential L1 for "horribly warm".** Stage 2 L1 with prior Π
(= stage 1 L1 at `.eval_pos`). The L&G "two priors" pattern: Π appears in
stage 2's L0 (via `L0LassiterGoodman` inside `adjL0_warmAt`) AND in stage
2's L1 (the `priorAfterEvalPos` argument to `PMF.posterior` here). -/
noncomputable def seqAdjL1HorriblyWarm (u : RSA.Nouwen2024.AdjUtterance) : PMF Height :=
  PMF.posterior adjSpeakerMarginal priorAfterEvalPos u
    -- Marginal positivity: pick witness h = deg 5. priorAfterEvalPos (deg 5) > 0
    -- (since muHorrible(deg 5) = 2 > 0); adjSpeakerMarginal (deg 5) u > 0 because
    -- at vt = 0, the conditional fallback uses S1Belief (non-degenerate at deg 5)
    -- and L0(u | deg 5, vt=0) is positive (priorAfterEvalPos(deg 5) > 0 + indicator
    -- true at deg 5 for both .warm and .silent under vt=0).
    (PMF.marginal_ne_zero _ _ _
      (priorAfterEvalPos_pos_at_horrible_pos (h := deg 5) (by decide)) (by
      unfold adjSpeakerMarginal
      rw [RSA.marginalizeKernel_apply]
      apply ENNReal.summable.tsum_ne_zero_iff.mpr
      refine ⟨0, ?_⟩
      apply mul_ne_zero
      · -- thresholdPriorPMF 0 ≠ 0
        rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
      · -- adjSpeaker_warmAt 0 (deg 5) u ≠ 0
        -- adjSpeaker_warmAt uses conditional fallback. At deg 5, the fallback
        -- branch is S1Belief (non-degenerate). Need to discharge h_pos for the dite.
        unfold adjSpeaker_warmAt
        -- Goal: (if h_pos then S1Belief ... else uniform) u ≠ 0
        -- At deg 5, h_pos holds because adjL0(.warm | deg 5, vt=0) > 0.
        have hL0_warm : adjL0_warmAt 0 .warm (deg 5) ≠ 0 := by
          unfold adjL0_warmAt
          rw [← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
          refine ⟨priorAfterEvalPos_pos_at_horrible_pos (by decide : (0:ℕ) < muHorrible (deg 5)), ?_⟩
          -- adjLex (validToThreshold 0) .warm (deg 5) = true
          show RSA.Nouwen2024.adjMeaning .warm (deg 5) (validToThreshold 0) = true
          decide
        have h_dite : (∑' u', ((adjL0_warmAt 0) u' (deg 5) : ℝ≥0∞) ^ (4 : ℝ) *
            adjCostFactor u') ≠ 0 := by
          apply ENNReal.summable.tsum_ne_zero_iff.mpr
          refine ⟨.warm, ?_⟩
          apply mul_ne_zero _ (by
            unfold adjCostFactor
            rw [ENNReal.ofReal_ne_zero_iff]
            exact Real.exp_pos _)
          have hntop : adjL0_warmAt 0 .warm (deg 5) ≠ ⊤ := PMF.apply_ne_top _ _
          exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hL0_warm) hntop).ne'
        rw [dif_pos h_dite]
        -- Now S1Belief positive at u — case on u
        cases u
        · -- .warm: L0(.warm | deg 5) > 0 from hL0_warm
          exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0_warm (by
            unfold adjCostFactor
            rw [ENNReal.ofReal_ne_zero_iff]
            exact Real.exp_pos _)
        · -- .silent: L0(.silent | deg 5) = priorAfterEvalPos(deg 5) > 0
          have hL0_silent : adjL0_warmAt 0 .silent (deg 5) ≠ 0 := by
            unfold adjL0_warmAt
            rw [RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl)]
            exact priorAfterEvalPos_pos_at_horrible_pos (by decide)
          exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0_silent (by
            unfold adjCostFactor
            rw [ENNReal.ofReal_ne_zero_iff]
            exact Real.exp_pos _)))

/-! ## §5b. Ratio cancellation: the structural core

Because the L&G literal listener carries the prior multiplicatively
(`L0(u) h = P h · 1[u true at h] / mass(u)`), the height factor `P h` cancels
in the speaker's normalisation: on its support, each per-threshold speaker
value depends only on the prior MASS of the utterance's extension at that
threshold. Each marginalised speaker is therefore a sum of a mass-monotone
value over the licensed thresholds, and the headline product comparison
follows from mass monotonicity alone — no numeric reflection. -/

/-- Prior mass of the `.eval_pos` extension at threshold `vt` (exactly the
`L0LassiterGoodman` normaliser for stage 1). -/
noncomputable def evalMass (vt : ValidThreshold) : ℝ≥0∞ :=
  ∑' h, heightPriorPMF h *
    (if evalLex muHorrible (validToThreshold vt) .eval_pos h then (1 : ℝ≥0∞) else 0)

theorem evalMass_ne_zero (vt : ValidThreshold) : evalMass vt ≠ 0 :=
  evalLex_horrible_extension_pos vt .eval_pos

theorem evalMass_ne_top (vt : ValidThreshold) : evalMass vt ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc evalMass vt
      ≤ ∑' h, heightPriorPMF h := ENNReal.tsum_le_tsum fun h => by split <;> simp
    _ = 1 := PMF.tsum_coe _

/-- Π-mass of the `.warm` extension at threshold `vt` (the stage-2
`L0LassiterGoodman` normaliser, against the backgrounded prior). -/
noncomputable def adjMass (vt : ValidThreshold) : ℝ≥0∞ :=
  ∑' h, priorAfterEvalPos h *
    (if adjLex (validToThreshold vt) .warm h then (1 : ℝ≥0∞) else 0)

theorem adjMass_ne_zero (vt : ValidThreshold) : adjMass vt ≠ 0 :=
  adjLex_warm_extension_pos vt .warm

theorem adjMass_ne_top (vt : ValidThreshold) : adjMass vt ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc adjMass vt
      ≤ ∑' h, priorAfterEvalPos h := ENNReal.tsum_le_tsum fun h => by split <;> simp
    _ = 1 := PMF.tsum_coe _

/-- Stage-1 speaker value at `.eval_pos` on its support: a function of the
extension mass only (the height factor has cancelled). -/
noncomputable def gval (vt : ValidThreshold) : ℝ≥0∞ :=
  (evalMass vt)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos /
    ((evalMass vt)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos + 1)

/-- Stage-2 speaker value at `.warm` on its support. -/
noncomputable def fval (vt : ValidThreshold) : ℝ≥0∞ :=
  (adjMass vt)⁻¹ ^ (4 : ℝ) * adjCostFactor .warm /
    ((adjMass vt)⁻¹ ^ (4 : ℝ) * adjCostFactor .warm + 1)

theorem evalCostFactor_silent : evalCostFactor .silent = 1 := by
  unfold evalCostFactor evalCost
  norm_num

theorem adjCostFactor_silent : adjCostFactor .silent = 1 := by
  unfold adjCostFactor
  show ENNReal.ofReal (Real.exp (-4 * ((RSA.Nouwen2024.adjCost .silent : ℚ) : ℝ))) = 1
  norm_num [RSA.Nouwen2024.adjCost]

private theorem sumEvalUtt (f : EvalUtterance → ℝ≥0∞) :
    ∑' u, f u = f .eval_pos + f .silent := by
  rw [tsum_fintype,
    show (Finset.univ : Finset EvalUtterance) = {.eval_pos, .silent} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem sumAdjUtt (f : RSA.Nouwen2024.AdjUtterance → ℝ≥0∞) :
    ∑' u, f u = f .warm + f .silent := by
  rw [tsum_fintype,
    show (Finset.univ : Finset RSA.Nouwen2024.AdjUtterance) = {.warm, .silent} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-- **Ratio cancellation, stage 1**: on its support the eval speaker's value
is `gval vt` — independent of the height. -/
theorem evalSpeaker_apply_of_true (vt : ValidThreshold) (w : Height)
    (hw : evalLex muHorrible (validToThreshold vt) .eval_pos w = true) :
    evalSpeaker_horribleAt vt w .eval_pos = gval vt := by
  have hP0 : heightPriorPMF w ≠ 0 := heightPriorPMF_pos w
  have hPt : heightPriorPMF w ≠ ⊤ := PMF.apply_ne_top _ _
  have hL0pos : evalL0_horribleAt vt .eval_pos w = heightPriorPMF w * (evalMass vt)⁻¹ := by
    unfold evalL0_horribleAt
    rw [RSA.L0LassiterGoodman_apply, hw]
    simp only [if_true, mul_one]
    rfl
  have hL0sil : evalL0_horribleAt vt .silent w = heightPriorPMF w := by
    unfold evalL0_horribleAt
    exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _
  unfold evalSpeaker_horribleAt
  rw [RSA.S1Belief_apply, sumEvalUtt, hL0pos, hL0sil, evalCostFactor_silent, mul_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  -- value = (P^4 * M^4 * c) * (P^4 * M^4 * c + P^4)⁻¹ ; factor P^4
  have hP4 : (heightPriorPMF w) ^ (4 : ℝ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hP0) hPt).ne'
  have hP4t : (heightPriorPMF w) ^ (4 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPt
  rw [mul_assoc ((heightPriorPMF w) ^ (4 : ℝ)),
    show (heightPriorPMF w) ^ (4 : ℝ) * ((evalMass vt)⁻¹ ^ (4 : ℝ) *
          evalCostFactor .eval_pos) + (heightPriorPMF w) ^ (4 : ℝ)
        = (heightPriorPMF w) ^ (4 : ℝ) * ((evalMass vt)⁻¹ ^ (4 : ℝ) *
          evalCostFactor .eval_pos + 1) from by rw [mul_add, mul_one],
    ← div_eq_mul_inv, ENNReal.mul_div_mul_left _ _ hP4 hP4t]
  rfl

/-- **Ratio cancellation, stage 1, off support**: value 0. -/
theorem evalSpeaker_apply_of_false (vt : ValidThreshold) (w : Height)
    (hw : evalLex muHorrible (validToThreshold vt) .eval_pos w = false) :
    evalSpeaker_horribleAt vt w .eval_pos = 0 := by
  have hL0pos : evalL0_horribleAt vt .eval_pos w = 0 := by
    unfold evalL0_horribleAt
    rw [RSA.L0LassiterGoodman_apply, hw]
    simp
  unfold evalSpeaker_horribleAt
  rw [RSA.S1Belief_apply, hL0pos, ENNReal.zero_rpow_of_pos (by norm_num), zero_mul, zero_mul]

/-- **Ratio cancellation, stage 2**: on its support (and at a non-degenerate
world, `Π(w) ≠ 0`) the adjective speaker's value is `fval vt`. -/
theorem adjSpeaker_apply_of_true (vt : ValidThreshold) (w : Height)
    (hw : adjLex (validToThreshold vt) .warm w = true)
    (hPi : priorAfterEvalPos w ≠ 0) :
    adjSpeaker_warmAt vt w .warm = fval vt := by
  have hPt : priorAfterEvalPos w ≠ ⊤ := PMF.apply_ne_top _ _
  have hL0warm : adjL0_warmAt vt .warm w = priorAfterEvalPos w * (adjMass vt)⁻¹ := by
    unfold adjL0_warmAt
    rw [RSA.L0LassiterGoodman_apply, hw]
    simp only [if_true, mul_one]
    rfl
  have hL0sil : adjL0_warmAt vt .silent w = priorAfterEvalPos w := by
    unfold adjL0_warmAt
    exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _
  have h_dite : (∑' u, ((adjL0_warmAt vt) u w : ℝ≥0∞) ^ (4 : ℝ) * adjCostFactor u) ≠ 0 := by
    rw [sumAdjUtt]
    intro hz
    obtain ⟨-, h2⟩ := add_eq_zero.mp hz
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [hL0sil] at h3
      exact hPi (by
        by_contra hne
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hne) hPt).ne' h3)
    · rw [adjCostFactor_silent] at h3
      exact one_ne_zero h3
  unfold adjSpeaker_warmAt
  rw [dif_pos h_dite, RSA.S1Belief_apply, sumAdjUtt, hL0warm, hL0sil, adjCostFactor_silent,
    mul_one, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hP4 : (priorAfterEvalPos w) ^ (4 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hPi) hPt).ne'
  have hP4t : (priorAfterEvalPos w) ^ (4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPt
  rw [mul_assoc ((priorAfterEvalPos w) ^ (4 : ℝ)),
    show (priorAfterEvalPos w) ^ (4 : ℝ) * ((adjMass vt)⁻¹ ^ (4 : ℝ) *
          adjCostFactor .warm) + (priorAfterEvalPos w) ^ (4 : ℝ)
        = (priorAfterEvalPos w) ^ (4 : ℝ) * ((adjMass vt)⁻¹ ^ (4 : ℝ) *
          adjCostFactor .warm + 1) from by rw [mul_add, mul_one],
    ← div_eq_mul_inv, ENNReal.mul_div_mul_left _ _ hP4 hP4t]
  rfl

/-- Stage-2 speaker value off support (at a non-degenerate world): `0`. -/
theorem adjSpeaker_apply_of_false (vt : ValidThreshold) (w : Height)
    (hw : adjLex (validToThreshold vt) .warm w = false)
    (hPi : priorAfterEvalPos w ≠ 0) :
    adjSpeaker_warmAt vt w .warm = 0 := by
  have hPt : priorAfterEvalPos w ≠ ⊤ := PMF.apply_ne_top _ _
  have hL0warm : adjL0_warmAt vt .warm w = 0 := by
    unfold adjL0_warmAt
    rw [RSA.L0LassiterGoodman_apply, hw]
    simp
  have hL0sil : adjL0_warmAt vt .silent w = priorAfterEvalPos w := by
    unfold adjL0_warmAt
    exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _
  have h_dite : (∑' u, ((adjL0_warmAt vt) u w : ℝ≥0∞) ^ (4 : ℝ) * adjCostFactor u) ≠ 0 := by
    rw [sumAdjUtt]
    intro hz
    obtain ⟨-, h2⟩ := add_eq_zero.mp hz
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rw [hL0sil] at h3
      exact hPi (by
        by_contra hne
        exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hne) hPt).ne' h3)
    · rw [adjCostFactor_silent] at h3
      exact one_ne_zero h3
  unfold adjSpeaker_warmAt
  rw [dif_pos h_dite, RSA.S1Belief_apply, hL0warm,
    ENNReal.zero_rpow_of_pos (by norm_num), zero_mul, zero_mul]

/-! ### Mass monotonicity — structural, no value computation

The `.eval_pos` extension shrinks strictly from threshold 0 to threshold 1
(`deg 2` has `μ_horrible = 1`, licensed at 0 but not at 1), so the eval mass
drops strictly; the speaker value `gval` rises strictly (informativity). -/

theorem evalMass_one_lt_zero : evalMass 1 < evalMass 0 := by
  refine ENNReal.tsum_lt_tsum (i := deg 2) (evalMass_ne_top 1) (fun h => ?_) ?_
  · fin_cases h <;>
      simp [evalLex, evalMeaning, muHorrible, validToThreshold, Degree.Degree.toNat,
        Degree.Threshold.toNat]
  · simp only [evalLex, evalMeaning, muHorrible, validToThreshold, Degree.Degree.toNat,
      Degree.Threshold.toNat, deg]
    norm_num
    exact pos_iff_ne_zero.mpr (heightPriorPMF_pos _)

/-- `x ↦ x/(x+1)` is strictly monotone on finite `ℝ≥0∞` — the informativity
step: a bigger unnormalised weight yields a bigger speaker value. -/
private theorem div_succ_lt_div_succ {a b : ℝ≥0∞} (hb : b ≠ ⊤) (h : a < b) :
    a / (a + 1) < b / (b + 1) := by
  have ha : a ≠ ⊤ := ne_top_of_lt h
  have hda : a / (a + 1) ≠ ⊤ := ENNReal.div_ne_top ha (by simp)
  have hdb : b / (b + 1) ≠ ⊤ := ENNReal.div_ne_top hb (by simp)
  rw [← ENNReal.toReal_lt_toReal hda hdb, ENNReal.toReal_div, ENNReal.toReal_div,
    ENNReal.toReal_add ha ENNReal.one_ne_top, ENNReal.toReal_add hb ENNReal.one_ne_top,
    ENNReal.toReal_one]
  have h' : a.toReal < b.toReal := (ENNReal.toReal_lt_toReal ha hb).mpr h
  have ha0 : (0 : ℝ) ≤ a.toReal := ENNReal.toReal_nonneg
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Informativity is threshold-monotone at the eval stage: the strictly
smaller mass at threshold 1 yields a strictly larger speaker value. -/
theorem gval_zero_lt_one : gval 0 < gval 1 := by
  have hc0 : evalCostFactor .eval_pos ≠ 0 := evalCostFactor_pos _
  have hct : evalCostFactor .eval_pos ≠ ⊤ := evalCostFactor_finite _
  have hX : (evalMass 0)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos
      < (evalMass 1)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos := by
    rw [mul_comm _ (evalCostFactor .eval_pos), mul_comm _ (evalCostFactor .eval_pos)]
    exact ENNReal.mul_lt_mul_right hc0 hct
      (ENNReal.rpow_lt_rpow (ENNReal.inv_lt_inv.mpr evalMass_one_lt_zero) (by norm_num))
  have hbt : (evalMass 1)⁻¹ ^ (4 : ℝ) * evalCostFactor .eval_pos ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (evalMass_ne_zero 1))) hct
  exact div_succ_lt_div_succ hbt hX

/-! ### Marginal expansions over the licensed thresholds -/

theorem gval_ne_top (vt : ValidThreshold) : gval vt ≠ ⊤ :=
  ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (evalMass_ne_zero vt))) (evalCostFactor_finite _))
    (by simp)

theorem fval_ne_top (vt : ValidThreshold) : fval vt ≠ ⊤ :=
  ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (adjMass_ne_zero vt)))
      (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top))
    (by simp)

theorem fval_ne_zero (vt : ValidThreshold) : fval vt ≠ 0 := by
  unfold fval
  rw [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  constructor
  · apply mul_ne_zero
    · exact (ENNReal.rpow_pos (ENNReal.inv_pos.mpr (adjMass_ne_top vt))
        (ENNReal.inv_ne_top.mpr (adjMass_ne_zero vt))).ne'
    · unfold adjCostFactor
      rw [ENNReal.ofReal_ne_zero_iff]
      exact Real.exp_pos _
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.inv_ne_top.mpr (adjMass_ne_zero vt)))
        (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top),
       ENNReal.one_ne_top⟩

/-- The raw prior ratio `P(deg 2) = 2 · P(deg 5)` (weights 10 vs 5) — no
normaliser computation needed. -/
theorem heightPriorPMF_deg2_eq :
    heightPriorPMF (deg 2) = 2 * heightPriorPMF (deg 5) := by
  unfold heightPriorPMF
  rw [PMF.normalize_apply, PMF.normalize_apply, ← mul_assoc]
  congr 1
  unfold heightPriorENN
  rw [show (heightPrior (deg 2) : ℝ) = 10 from by norm_num [show heightPrior (deg 2) = 10 from rfl],
    show (heightPrior (deg 5) : ℝ) = 5 from by norm_num [show heightPrior (deg 5) = 5 from rfl],
    show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) from (ENNReal.ofReal_ofNat 2).symm,
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

private theorem sumVT (f : ValidThreshold → ℝ≥0∞) :
    ∑' vt, f vt = f 0 + f 1 + f 2 := by
  rw [tsum_fintype, Fin.sum_univ_three]

private theorem uPrior (vt : ValidThreshold) : thresholdPriorPMF vt = 3⁻¹ := by
  rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]
  norm_num

theorem evalMarginal_deg2 :
    evalSpeakerMarginalHorrible (deg 2) .eval_pos = 3⁻¹ * gval 0 := by
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    evalSpeaker_apply_of_true 0 _ (by decide),
    evalSpeaker_apply_of_false 1 _ (by decide),
    evalSpeaker_apply_of_false 2 _ (by decide), mul_zero, add_zero, add_zero]

theorem evalMarginal_deg5 :
    evalSpeakerMarginalHorrible (deg 5) .eval_pos = 3⁻¹ * gval 0 + 3⁻¹ * gval 1 := by
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    evalSpeaker_apply_of_true 0 _ (by decide),
    evalSpeaker_apply_of_true 1 _ (by decide),
    evalSpeaker_apply_of_false 2 _ (by decide), mul_zero, add_zero]

theorem adjMarginal_deg2 :
    adjSpeakerMarginal (deg 2) .warm = 3⁻¹ * fval 0 + 3⁻¹ * fval 1 := by
  unfold adjSpeakerMarginal
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    adjSpeaker_apply_of_true 0 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)),
    adjSpeaker_apply_of_true 1 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)),
    adjSpeaker_apply_of_false 2 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)), mul_zero, add_zero]

theorem adjMarginal_deg5 :
    adjSpeakerMarginal (deg 5) .warm = 3⁻¹ * fval 0 + 3⁻¹ * fval 1 + 3⁻¹ * fval 2 := by
  unfold adjSpeakerMarginal
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    adjSpeaker_apply_of_true 0 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)),
    adjSpeaker_apply_of_true 1 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide)),
    adjSpeaker_apply_of_true 2 _ (by decide)
      (priorAfterEvalPos_pos_at_horrible_pos (by decide))]

/-! ## §5c. The backgrounding contrast: why the paper rejects (49)

[nouwen-2024] p. 28: "the source of this problem lies in the simple
conjunctive analysis I assume in (49)… the two thresholds are resolved in
tandem… all we need to do is update the two positive forms successively
rather than simultaneously." Made structural: in the REJECTED simultaneous
model, per-latent dominance FAILS on the shared licensing support — at a
shared latent where every utterance is true at both worlds, ratio
cancellation makes the speaker values exactly equal, so the raw height
prior's 2:1 preference for the moderate world wins the term comparison
(`sim_sharedSupport_dominance_fails`). In the final sequential model the
same per-latent comparison HOLDS (`seq_horribly_shifts_upward`'s §5b
engine): the backgrounded evaluative posterior has already re-loaded the
prior toward the extremes. Backgrounding is exactly what makes
intensification term-by-term derivable. -/

/-- Cost factor for the simultaneous model's four utterances. -/
noncomputable def simCostFactor (u : Utterance) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-4 * (utteranceCost u : ℝ)))

theorem simCostFactor_pos (u : Utterance) : simCostFactor u ≠ 0 := by
  unfold simCostFactor
  rw [ENNReal.ofReal_ne_zero_iff]
  exact Real.exp_pos _

theorem simCostFactor_finite (u : Utterance) : simCostFactor u ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Simultaneous-model literal listener at latent `(θ, θ_e)`, gated on the
utterance's extension being nonempty (the four-utterance L&G L0). -/
noncomputable def simL0At (l : Threshold × Threshold) (u : Utterance) : PMF Height :=
  if h_pos : (∑' h, heightPriorPMF h *
      (if meaning u h l.1 l.2 then (1 : ℝ≥0∞) else 0)) ≠ 0 then
    RSA.L0LassiterGoodman heightPriorPMF (fun u' h => meaning u' h l.1 l.2) u h_pos
  else PMF.uniformOfFintype Height

/-- Simultaneous-model speaker at latent `(θ, θ_e)` and world `h` (total, with
the vacuous fallback at degenerate cells, as in `adjSpeaker_warmAt`). -/
noncomputable def simSpeakerAt (l : Threshold × Threshold) (h : Height) : PMF Utterance :=
  if h_pos : (∑' u, ((simL0At l) u h : ℝ≥0∞) ^ (4 : ℝ) * simCostFactor u) ≠ 0 then
    RSA.S1Belief (simL0At l) simCostFactor 4 h h_pos
      (ENNReal.tsum_ne_top_of_fintype fun u =>
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
          (simCostFactor_finite u))
  else PMF.pure .silent

/-- Per-latent joint term of the simultaneous model for "horribly warm":
prior × speaker — one latent cell's contribution to the (49)-listener's
world score. -/
noncomputable def simTerm (l : Threshold × Threshold) (h : Height) : ℝ≥0∞ :=
  heightPriorPMF h * simSpeakerAt l h .horribly_warm

/-- Extension mass of utterance `u` at latent `l` (the `simL0At` normaliser). -/
noncomputable def simMass (l : Threshold × Threshold) (u : Utterance) : ℝ≥0∞ :=
  ∑' h, heightPriorPMF h * (if meaning u h l.1 l.2 then (1 : ℝ≥0∞) else 0)

private theorem simMass_ne_zero_of_true {l : Threshold × Threshold} {u : Utterance}
    {h : Height} (hu : meaning u h l.1 l.2 = true) : simMass l u ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr
    ⟨h, by rw [hu]; simp only [if_true, mul_one]; exact heightPriorPMF_pos h⟩

private theorem sumUtt4 (f : Utterance → ℝ≥0∞) :
    ∑' u, f u = f .bare_warm + f .horribly_warm + f .pleasantly_warm + f .silent := by
  rw [tsum_fintype,
    show (Finset.univ : Finset Utterance)
      = {.bare_warm, .horribly_warm, .pleasantly_warm, .silent} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- At an all-true world, the simultaneous speaker's value is a function of
the four extension masses alone — the height factor has cancelled. -/
private theorem simValue_of_allTrue (l : Threshold × Threshold) (h : Height)
    (hall : ∀ u : Utterance, meaning u h l.1 l.2 = true) :
    simSpeakerAt l h .horribly_warm
      = (simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .horribly_warm /
        ((simMass l .bare_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .bare_warm +
         (simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .horribly_warm +
         (simMass l .pleasantly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .pleasantly_warm +
         (simMass l .silent)⁻¹ ^ (4 : ℝ) * simCostFactor .silent) := by
  have hP0 : heightPriorPMF h ≠ 0 := heightPriorPMF_pos h
  have hPt : heightPriorPMF h ≠ ⊤ := PMF.apply_ne_top _ _
  have hL0 : ∀ u : Utterance, simL0At l u h = heightPriorPMF h * (simMass l u)⁻¹ := by
    intro u
    have hm : (∑' h', heightPriorPMF h' *
        (if meaning u h' l.1 l.2 then (1 : ℝ≥0∞) else 0)) ≠ 0 :=
      simMass_ne_zero_of_true (hall u)
    unfold simL0At
    rw [dif_pos hm, RSA.L0LassiterGoodman_apply, hall u]
    simp only [if_true, mul_one]
    rfl
  have h_pos : (∑' u, ((simL0At l) u h : ℝ≥0∞) ^ (4 : ℝ) * simCostFactor u) ≠ 0 := by
    rw [sumUtt4]
    intro hz
    rcases mul_eq_zero.mp (add_eq_zero.mp hz).2 with h5 | h5
    · rw [hL0 .silent] at h5
      have hne : heightPriorPMF h * (simMass l .silent)⁻¹ ≠ 0 :=
        mul_ne_zero hP0 (ENNReal.inv_ne_zero.mpr (by
          refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
          calc simMass l .silent
              ≤ ∑' h', heightPriorPMF h' := ENNReal.tsum_le_tsum fun h' => by
                split <;> simp
            _ = 1 := PMF.tsum_coe _))
      rcases ENNReal.rpow_eq_zero_iff.mp h5 with ⟨hz0, -⟩ | ⟨-, hneg⟩
      · exact hne hz0
      · norm_num at hneg
    · exact simCostFactor_pos .silent h5
  unfold simSpeakerAt
  rw [dif_pos h_pos, RSA.S1Belief_apply, sumUtt4, hL0 .bare_warm, hL0 .horribly_warm,
    hL0 .pleasantly_warm, hL0 .silent]
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
  have hP4 : (heightPriorPMF h) ^ (4 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hP0) hPt).ne'
  have hP4t : (heightPriorPMF h) ^ (4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPt
  rw [← div_eq_mul_inv,
    show heightPriorPMF h ^ (4 : ℝ) * (simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .horribly_warm
        = heightPriorPMF h ^ (4 : ℝ) * ((simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .horribly_warm) from by ring,
    show heightPriorPMF h ^ (4 : ℝ) * (simMass l .bare_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .bare_warm +
        heightPriorPMF h ^ (4 : ℝ) * ((simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .horribly_warm) +
        heightPriorPMF h ^ (4 : ℝ) * (simMass l .pleasantly_warm)⁻¹ ^ (4 : ℝ) *
          simCostFactor .pleasantly_warm +
        heightPriorPMF h ^ (4 : ℝ) * (simMass l .silent)⁻¹ ^ (4 : ℝ) *
          simCostFactor .silent
        = heightPriorPMF h ^ (4 : ℝ) * ((simMass l .bare_warm)⁻¹ ^ (4 : ℝ) *
            simCostFactor .bare_warm +
          (simMass l .horribly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .horribly_warm +
          (simMass l .pleasantly_warm)⁻¹ ^ (4 : ℝ) * simCostFactor .pleasantly_warm +
          (simMass l .silent)⁻¹ ^ (4 : ℝ) * simCostFactor .silent) from by ring,
    ENNReal.mul_div_mul_left _ _ hP4 hP4t]

private theorem simMass_ne_top (l : Threshold × Threshold) (u : Utterance) :
    simMass l u ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc simMass l u
      ≤ ∑' h', heightPriorPMF h' := ENNReal.tsum_le_tsum fun h' => by split <;> simp
    _ = 1 := PMF.tsum_coe _

/-- At a latent where every utterance is true at both worlds, ratio
cancellation makes the two speaker values exactly equal. -/
private theorem simSpeaker_value_congr (l : Threshold × Threshold) (h₁ h₂ : Height)
    (hall₁ : ∀ u : Utterance, meaning u h₁ l.1 l.2 = true)
    (hall₂ : ∀ u : Utterance, meaning u h₂ l.1 l.2 = true) :
    simSpeakerAt l h₁ .horribly_warm = simSpeakerAt l h₂ .horribly_warm := by
  rw [simValue_of_allTrue l h₁ hall₁, simValue_of_allTrue l h₂ hall₂]

/-- **The failure half of the backgrounding contrast** ([nouwen-2024] p. 28:
in (49) "the two thresholds are resolved in tandem"): in the rejected
simultaneous model, per-latent dominance fails on the shared licensing
support. At the shared latent `(θ, θ_e) = (1, 0)` every utterance is true at
both `deg 2` and `deg 5`, so ratio cancellation makes the speaker values
exactly equal — and the raw height prior's 2:1 preference for the moderate
world decides the term comparison. Contrast the sequential model
(`seq_horribly_shifts_upward`): after backgrounding, the same per-latent
comparisons run against the evaluative posterior, which has already
re-loaded the prior toward the extremes. Backgrounding, not parameter
tuning, is what makes intensification term-by-term derivable. -/
theorem sim_sharedSupport_dominance_fails :
    ¬ ∀ l ∈ licensingSet .horribly_warm (deg 2),
        simTerm l (deg 2) ≤ simTerm l (deg 5) := by
  intro hforall
  have hmem : ((thr 1, thr 0) : Threshold × Threshold)
      ∈ licensingSet .horribly_warm (deg 2) := by decide
  have hall2 : ∀ u : Utterance, meaning u (deg 2) (thr 1) (thr 0) = true := by
    decide
  have hcongr := simSpeaker_value_congr ((thr 1, thr 0) : Threshold × Threshold)
    (deg 5) (deg 2) (by decide) hall2
  set v := simSpeakerAt ((thr 1, thr 0) : Threshold × Threshold) (deg 2) .horribly_warm
    with hv
  have hv0 : v ≠ 0 := by
    rw [hv, simValue_of_allTrue _ _ hall2, ne_eq, ENNReal.div_eq_zero_iff, not_or]
    have hterm : ∀ u : Utterance,
        (simMass ((thr 1, thr 0) : Threshold × Threshold) u)⁻¹ ^ (4 : ℝ) *
          simCostFactor u ≠ ⊤ := fun u =>
      ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (ENNReal.inv_ne_top.mpr (simMass_ne_zero_of_true (hall2 u))))
        (simCostFactor_finite u)
    refine ⟨mul_ne_zero ?_ (simCostFactor_pos _), ?_⟩
    · exact (ENNReal.rpow_pos (ENNReal.inv_pos.mpr (simMass_ne_top _ _))
        (ENNReal.inv_ne_top.mpr (simMass_ne_zero_of_true (hall2 .horribly_warm)))).ne'
    · exact ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hterm _, hterm _⟩, hterm _⟩,
         hterm _⟩
  have hvt : v ≠ ⊤ := PMF.apply_ne_top _ _
  have hP5 : heightPriorPMF (deg 5) ≠ 0 := heightPriorPMF_pos _
  have hP5t : heightPriorPMF (deg 5) ≠ ⊤ := PMF.apply_ne_top _ _
  have hkey : simTerm (thr 1, thr 0) (deg 5) < simTerm (thr 1, thr 0) (deg 2) := by
    unfold simTerm
    rw [hcongr, ← hv, heightPriorPMF_deg2_eq]
    calc heightPriorPMF (deg 5) * v
        = heightPriorPMF (deg 5) * v * 1 := (mul_one _).symm
      _ < heightPriorPMF (deg 5) * v * 2 :=
          ENNReal.mul_lt_mul_right (mul_ne_zero hP5 hv0)
            (ENNReal.mul_ne_top hP5t hvt) (by norm_num)
      _ = 2 * heightPriorPMF (deg 5) * v := by ring
  exact absurd (hforall _ hmem) (not_le.mpr hkey)

/-! ## §5d. Measure-generic evaluative stage; the pleasantly chain

The horrible chain (§3–§5) instantiates the architecture with
measure-specific definitions; the dite-total generic forms below serve the
remaining measures (μ_pleasant here, μ_usual for the Zwicky section)
without threading extension-positivity hypotheses. -/

/-- Measure-generic stage-1 literal listener (dite-total). -/
noncomputable def evalL0At (evalMu : Height → ℕ) (vt : ValidThreshold)
    (u : EvalUtterance) : PMF Height :=
  if h_pos : (∑' h, heightPriorPMF h *
      (if evalLex evalMu (validToThreshold vt) u h then (1 : ℝ≥0∞) else 0)) ≠ 0 then
    RSA.L0LassiterGoodman heightPriorPMF (evalLex evalMu (validToThreshold vt)) u h_pos
  else PMF.uniformOfFintype Height

/-- Measure-generic stage-1 speaker (dite-total). -/
noncomputable def evalSpeakerAt (evalMu : Height → ℕ) (vt : ValidThreshold)
    (w : Height) : PMF EvalUtterance :=
  if h_pos : (∑' u, ((evalL0At evalMu vt) u w : ℝ≥0∞) ^ (4 : ℝ) *
      evalCostFactor u) ≠ 0 then
    RSA.S1Belief (evalL0At evalMu vt) evalCostFactor 4 w h_pos
      (ENNReal.tsum_ne_top_of_fintype fun u =>
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
          (evalCostFactor_finite u))
  else PMF.pure .silent

/-- Measure-generic marginalized stage-1 speaker. -/
noncomputable def evalMarginalAt (evalMu : Height → ℕ) : Height → PMF EvalUtterance :=
  RSA.marginalizeKernel thresholdPriorPMF (fun vt w => evalSpeakerAt evalMu vt w)

theorem evalL0At_silent (evalMu : Height → ℕ) (vt : ValidThreshold) (w : Height) :
    evalL0At evalMu vt .silent w = heightPriorPMF w := by
  have hm : (∑' h, heightPriorPMF h *
      (if evalLex evalMu (validToThreshold vt) .silent h then (1 : ℝ≥0∞) else 0)) = 1 := by
    simp only [show ∀ h, evalLex evalMu (validToThreshold vt) .silent h = true from
      fun _ => rfl, if_true, mul_one]
    exact PMF.tsum_coe _
  unfold evalL0At
  rw [dif_pos (by rw [hm]; exact one_ne_zero)]
  exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _

private theorem evalSpeakerAt_h_pos (evalMu : Height → ℕ) (vt : ValidThreshold)
    (w : Height) :
    (∑' u, ((evalL0At evalMu vt) u w : ℝ≥0∞) ^ (4 : ℝ) * evalCostFactor u) ≠ 0 := by
  rw [sumEvalUtt]
  intro hz
  rcases mul_eq_zero.mp (add_eq_zero.mp hz).2 with h5 | h5
  · rw [evalL0At_silent] at h5
    rcases ENNReal.rpow_eq_zero_iff.mp h5 with ⟨hz0, -⟩ | ⟨-, hneg⟩
    · exact heightPriorPMF_pos w hz0
    · norm_num at hneg
  · exact evalCostFactor_pos .silent h5

/-- Generic off-support zero (given a nonempty `.eval_pos` extension). -/
theorem evalSpeakerAt_apply_of_false (evalMu : Height → ℕ) (vt : ValidThreshold)
    (w : Height)
    (hne : (∑' h, heightPriorPMF h *
      (if evalLex evalMu (validToThreshold vt) .eval_pos h then (1 : ℝ≥0∞) else 0)) ≠ 0)
    (hw : evalLex evalMu (validToThreshold vt) .eval_pos w = false) :
    evalSpeakerAt evalMu vt w .eval_pos = 0 := by
  have hL0 : evalL0At evalMu vt .eval_pos w = 0 := by
    unfold evalL0At
    rw [dif_pos hne, RSA.L0LassiterGoodman_apply, hw]
    simp
  unfold evalSpeakerAt
  rw [dif_pos (evalSpeakerAt_h_pos evalMu vt w), RSA.S1Belief_apply, hL0,
    ENNReal.zero_rpow_of_pos (by norm_num), zero_mul, zero_mul]

/-- Generic on-support positivity (given a nonempty `.eval_pos` extension). -/
theorem evalSpeakerAt_apply_ne_zero_of_true (evalMu : Height → ℕ) (vt : ValidThreshold)
    (w : Height)
    (hne : (∑' h, heightPriorPMF h *
      (if evalLex evalMu (validToThreshold vt) .eval_pos h then (1 : ℝ≥0∞) else 0)) ≠ 0)
    (hw : evalLex evalMu (validToThreshold vt) .eval_pos w = true) :
    evalSpeakerAt evalMu vt w .eval_pos ≠ 0 := by
  have hL0 : evalL0At evalMu vt .eval_pos w ≠ 0 := by
    unfold evalL0At
    rw [dif_pos hne, ← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
    exact ⟨heightPriorPMF_pos w, hw⟩
  unfold evalSpeakerAt
  rw [dif_pos (evalSpeakerAt_h_pos evalMu vt w)]
  exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0 (evalCostFactor_pos _)

/-- Nonempty `.eval_pos` extension for μ_pleasant at every valid threshold
(witness `deg 3`, where `μ_pleasant = 3`). -/
theorem evalMass_pleasant_ne_zero (vt : ValidThreshold) :
    (∑' h, heightPriorPMF h *
      (if evalLex muPleasant (validToThreshold vt) .eval_pos h then (1 : ℝ≥0∞) else 0)) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨deg 3, ?_⟩
  have ht : evalLex muPleasant (validToThreshold vt) .eval_pos (deg 3) = true := by
    revert vt; decide
  rw [ht]
  simp only [if_true, mul_one]
  exact heightPriorPMF_pos _

/-- Backgrounded prior for "pleasantly": stage-1 posterior under μ_pleasant. -/
noncomputable def priorAfterEvalPosPleasant : PMF Height :=
  PMF.posterior (evalMarginalAt muPleasant) heightPriorPMF .eval_pos
    (PMF.marginal_ne_zero _ _ _ (heightPriorPMF_pos (deg 3)) (by
      unfold evalMarginalAt
      rw [RSA.marginalizeKernel_apply]
      apply ENNReal.summable.tsum_ne_zero_iff.mpr
      refine ⟨0, mul_ne_zero ?_ ?_⟩
      · rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
      · exact evalSpeakerAt_apply_ne_zero_of_true muPleasant 0 (deg 3)
          (evalMass_pleasant_ne_zero 0) (by decide)))

/-- Π_pleasant is positive at heights with positive `μ_pleasant`. -/
theorem priorAfterEvalPosPleasant_pos_at {h : Height} (hpos : 0 < muPleasant h) :
    priorAfterEvalPosPleasant h ≠ 0 := by
  unfold priorAfterEvalPosPleasant
  rw [← PMF.mem_support_iff, PMF.mem_support_posterior_iff]
  refine ⟨heightPriorPMF_pos h, ?_⟩
  unfold evalMarginalAt
  rw [RSA.marginalizeKernel_apply]
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨0, mul_ne_zero ?_ ?_⟩
  · rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
  · refine evalSpeakerAt_apply_ne_zero_of_true muPleasant 0 h
      (evalMass_pleasant_ne_zero 0) ?_
    have h0 : (validToThreshold 0).toNat = 0 := rfl
    simp only [evalLex, evalMeaning, h0]
    exact decide_eq_true (by omega)

/-- Stage-2 literal listener for the pleasantly chain (dite-total, prior Π_pleasant). -/
noncomputable def adjL0PleasantAt (vt : ValidThreshold)
    (u : RSA.Nouwen2024.AdjUtterance) : PMF Height :=
  if h_pos : (∑' h, priorAfterEvalPosPleasant h *
      (if adjLex (validToThreshold vt) u h then (1 : ℝ≥0∞) else 0)) ≠ 0 then
    RSA.L0LassiterGoodman priorAfterEvalPosPleasant (adjLex (validToThreshold vt)) u h_pos
  else PMF.uniformOfFintype Height

/-- Stage-2 speaker for the pleasantly chain (dite-total). -/
noncomputable def adjSpeakerPleasantAt (vt : ValidThreshold) (w : Height) :
    PMF (RSA.Nouwen2024.AdjUtterance) :=
  if h_pos : (∑' u, ((adjL0PleasantAt vt) u w : ℝ≥0∞) ^ (4 : ℝ) * adjCostFactor u) ≠ 0 then
    RSA.S1Belief (adjL0PleasantAt vt) adjCostFactor 4 w h_pos
      (ENNReal.tsum_ne_top_of_fintype fun u =>
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
          (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top))
  else PMF.pure .silent

/-- Marginalized stage-2 speaker for the pleasantly chain. -/
noncomputable def adjMarginalPleasant : Height → PMF AdjUtterance :=
  RSA.marginalizeKernel thresholdPriorPMF (fun vt w => adjSpeakerPleasantAt vt w)

/-- Nonempty `.warm` extension over Π_pleasant at threshold 0 (witness `deg 4`). -/
private theorem adjMass_pleasant_zero_ne_zero :
    (∑' h, priorAfterEvalPosPleasant h *
      (if adjLex (validToThreshold 0) .warm h then (1 : ℝ≥0∞) else 0)) ≠ 0 := by
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨deg 4, ?_⟩
  rw [show adjLex (validToThreshold 0) .warm (deg 4) = true from by decide]
  simp only [if_true, mul_one]
  exact priorAfterEvalPosPleasant_pos_at (by decide)

/-- The stage-2 pleasantly speaker is positive on `.warm` at `deg 4`, `vt = 0`. -/
private theorem adjSpeakerPleasant_warm_deg4_ne_zero :
    adjSpeakerPleasantAt 0 (deg 4) .warm ≠ 0 := by
  have hL0 : adjL0PleasantAt 0 .warm (deg 4) ≠ 0 := by
    unfold adjL0PleasantAt
    rw [dif_pos adjMass_pleasant_zero_ne_zero, ← PMF.mem_support_iff,
      RSA.mem_support_L0LassiterGoodman_iff]
    exact ⟨priorAfterEvalPosPleasant_pos_at (by decide), by decide⟩
  have h_pos : (∑' u, ((adjL0PleasantAt 0) u (deg 4) : ℝ≥0∞) ^ (4 : ℝ) *
      adjCostFactor u) ≠ 0 := by
    apply ENNReal.summable.tsum_ne_zero_iff.mpr
    refine ⟨.warm, mul_ne_zero ?_ ?_⟩
    · exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hL0) (PMF.apply_ne_top _ _)).ne'
    · unfold adjCostFactor
      rw [ENNReal.ofReal_ne_zero_iff]
      exact Real.exp_pos _
  unfold adjSpeakerPleasantAt
  rw [dif_pos h_pos]
  exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0 (by
    unfold adjCostFactor
    rw [ENNReal.ofReal_ne_zero_iff]
    exact Real.exp_pos _)

/-- **Sequential L1 for "pleasantly warm"** (mirrors `seqAdjL1HorriblyWarm`). -/
noncomputable def seqAdjL1PleasantlyWarm (u : RSA.Nouwen2024.AdjUtterance) : PMF Height :=
  PMF.posterior adjMarginalPleasant priorAfterEvalPosPleasant u
    (PMF.marginal_ne_zero _ _ _ (priorAfterEvalPosPleasant_pos_at (by decide : 0 < muPleasant (deg 4))) (by
      unfold adjMarginalPleasant
      rw [RSA.marginalizeKernel_apply]
      apply ENNReal.summable.tsum_ne_zero_iff.mpr
      refine ⟨0, mul_ne_zero ?_ ?_⟩
      · rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
      · cases u
        · exact adjSpeakerPleasant_warm_deg4_ne_zero
        · have hL0 : adjL0PleasantAt 0 .silent (deg 4) ≠ 0 := by
            have hm : (∑' h, priorAfterEvalPosPleasant h *
                (if adjLex (validToThreshold 0) .silent h then (1 : ℝ≥0∞) else 0)) = 1 := by
              simp only [show ∀ h, adjLex (validToThreshold 0) .silent h = true from
                fun _ => rfl, if_true, mul_one]
              exact PMF.tsum_coe _
            unfold adjL0PleasantAt
            rw [dif_pos (by rw [hm]; exact one_ne_zero),
              RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl)]
            exact priorAfterEvalPosPleasant_pos_at (by decide)
          have h_pos : (∑' u', ((adjL0PleasantAt 0) u' (deg 4) : ℝ≥0∞) ^ (4 : ℝ) *
              adjCostFactor u') ≠ 0 := by
            apply ENNReal.summable.tsum_ne_zero_iff.mpr
            refine ⟨.silent, mul_ne_zero ?_ ?_⟩
            · exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hL0)
                (PMF.apply_ne_top _ _)).ne'
            · rw [adjCostFactor_silent]; exact one_ne_zero
          unfold adjSpeakerPleasantAt
          rw [dif_pos h_pos]
          exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0 (by
            rw [adjCostFactor_silent]; exact one_ne_zero)))

/-- **"Pleasantly warm" prefers the moderate `deg 4` over the extreme `deg 6`**
([nouwen-2024] Fig. 8: positive evaluations concentrate mass mid-scale). The
proof is a support fact: `μ_pleasant (deg 6) = 0` licenses *no* evaluative
threshold, so the extreme world's evaluative marginal — hence its whole
chained score — is zero, while the moderate world's is positive. -/
theorem seq_pleasantly_prefers_moderate :
    seqAdjL1PleasantlyWarm .warm (deg 4) > seqAdjL1PleasantlyWarm .warm (deg 6) := by
  unfold seqAdjL1PleasantlyWarm priorAfterEvalPosPleasant
  rw [gt_iff_lt, PMF.posterior_chained_lt_iff_score_lt]
  have hE6 : evalMarginalAt muPleasant (deg 6) .eval_pos = 0 := by
    unfold evalMarginalAt
    rw [RSA.marginalizeKernel_apply, sumVT,
      evalSpeakerAt_apply_of_false muPleasant 0 _ (evalMass_pleasant_ne_zero 0) (by decide),
      evalSpeakerAt_apply_of_false muPleasant 1 _ (evalMass_pleasant_ne_zero 1) (by decide),
      evalSpeakerAt_apply_of_false muPleasant 2 _ (evalMass_pleasant_ne_zero 2) (by decide),
      mul_zero, mul_zero, mul_zero, add_zero, add_zero]
  have hE4 : evalMarginalAt muPleasant (deg 4) .eval_pos ≠ 0 := by
    unfold evalMarginalAt
    rw [RSA.marginalizeKernel_apply]
    apply ENNReal.summable.tsum_ne_zero_iff.mpr
    refine ⟨0, mul_ne_zero ?_ ?_⟩
    · rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
    · exact evalSpeakerAt_apply_ne_zero_of_true muPleasant 0 _
        (evalMass_pleasant_ne_zero 0) (by decide)
  have hA4 : adjMarginalPleasant (deg 4) .warm ≠ 0 := by
    unfold adjMarginalPleasant
    rw [RSA.marginalizeKernel_apply]
    apply ENNReal.summable.tsum_ne_zero_iff.mpr
    refine ⟨0, mul_ne_zero ?_ ?_⟩
    · rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
    · exact adjSpeakerPleasant_warm_deg4_ne_zero
  rw [hE6, mul_zero, zero_mul]
  exact pos_iff_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (heightPriorPMF_pos _) hE4) hA4)

/-! ## §5e. Zwicky vacuity as an identity; the usually chain

[nouwen-2024] p. 22: the simple account "wrongly predict[s] that usually
tall means the same as tall but not unusually tall". Model-side content: a
constant evaluative measure licenses every threshold at every height, so the
evaluative update is the IDENTITY (`priorAfterEvalPosUsual_eq_prior`) —
"usually warm" reduces to bare "warm" exactly — while `μ_unusual =
μ_horrible` holds definitionally, so "unusually warm" IS the horribly chain
and inherits its upward shift. The old cross-model inequality pair is
subsumed by these identities plus the single-model shift theorems. -/

/-- ℕ-valued constant measure ("usual"): no height discrimination. -/
def muUsualN : Height → ℕ := fun _ => 3

/-- μ_unusual has μ_horrible's shape: deviation measures pattern with
negative evaluatives ([nouwen-2024] §5). -/
def muUnusualN : Height → ℕ := muHorrible

theorem muUnusualN_eq_muHorrible : muUnusualN = muHorrible := rfl

/-- Under the constant measure every threshold is licensed at every height. -/
private theorem evalLex_usual_true (vt : ValidThreshold) (u : EvalUtterance) (h : Height) :
    evalLex muUsualN (validToThreshold vt) u h = true := by
  cases u
  · revert vt h; decide
  · rfl

/-- The constant-measure literal listener is the prior at every utterance. -/
theorem evalL0At_usual (vt : ValidThreshold) (u : EvalUtterance) (w : Height) :
    evalL0At muUsualN vt u w = heightPriorPMF w := by
  have hm : (∑' h, heightPriorPMF h *
      (if evalLex muUsualN (validToThreshold vt) u h then (1 : ℝ≥0∞) else 0)) = 1 := by
    simp only [evalLex_usual_true, if_true, mul_one]
    exact PMF.tsum_coe _
  unfold evalL0At
  rw [dif_pos (by rw [hm]; exact one_ne_zero)]
  exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _
    (fun w' => evalLex_usual_true vt u w') _ _

/-- Constant-measure speaker value: closed form, height-independent. -/
theorem evalSpeakerAt_usual_apply (vt : ValidThreshold) (w : Height) :
    evalSpeakerAt muUsualN vt w .eval_pos
      = evalCostFactor .eval_pos / (evalCostFactor .eval_pos + 1) := by
  have hP0 : heightPriorPMF w ≠ 0 := heightPriorPMF_pos w
  have hPt : heightPriorPMF w ≠ ⊤ := PMF.apply_ne_top _ _
  unfold evalSpeakerAt
  rw [dif_pos (evalSpeakerAt_h_pos muUsualN vt w), RSA.S1Belief_apply, sumEvalUtt,
    evalL0At_usual, evalL0At_usual, evalCostFactor_silent, mul_one]
  have hP4 : (heightPriorPMF w) ^ (4 : ℝ) ≠ 0 :=
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hP0) hPt).ne'
  have hP4t : (heightPriorPMF w) ^ (4 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPt
  rw [← div_eq_mul_inv,
    show (heightPriorPMF w) ^ (4 : ℝ) * evalCostFactor .eval_pos +
          (heightPriorPMF w) ^ (4 : ℝ)
        = (heightPriorPMF w) ^ (4 : ℝ) * (evalCostFactor .eval_pos + 1) from by ring,
    ENNReal.mul_div_mul_left _ _ hP4 hP4t]

/-- The marginalised constant-measure kernel is constant across heights. -/
theorem evalMarginalAt_usual_const (w : Height) :
    evalMarginalAt muUsualN w .eval_pos
      = evalCostFactor .eval_pos / (evalCostFactor .eval_pos + 1) := by
  unfold evalMarginalAt
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    evalSpeakerAt_usual_apply, evalSpeakerAt_usual_apply, evalSpeakerAt_usual_apply,
    show ∀ x : ℝ≥0∞, 3⁻¹ * x + 3⁻¹ * x + 3⁻¹ * x = 3 * 3⁻¹ * x from fun x => by ring,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

private theorem usualKernelValue_ne_zero :
    evalCostFactor .eval_pos / (evalCostFactor .eval_pos + 1) ≠ 0 := by
  rw [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨evalCostFactor_pos _,
    ENNReal.add_ne_top.mpr ⟨evalCostFactor_finite _, ENNReal.one_ne_top⟩⟩

/-- Backgrounded prior for "usually". -/
noncomputable def priorAfterEvalPosUsual : PMF Height :=
  PMF.posterior (evalMarginalAt muUsualN) heightPriorPMF .eval_pos
    (PMF.marginal_ne_zero _ _ _ (heightPriorPMF_pos (deg 0))
      (by rw [evalMarginalAt_usual_const]; exact usualKernelValue_ne_zero))

/-- **Zwicky's vacuity as an identity**: the constant measure's evaluative
update is the identity — Π_usual IS the prior. This is the deep form of the
old `eval_constant_preserves_peak` (whose inequality is now a corollary of
the prior's own shape) and the first half of "usually warm ≈ warm". -/
theorem priorAfterEvalPosUsual_eq_prior : priorAfterEvalPosUsual = heightPriorPMF :=
  PMF.posterior_eq_of_kernel_const _ _ _ _ (fun w => evalMarginalAt_usual_const w)

/-- The old `eval_constant_preserves_peak`, now a prior fact: the constant
measure's stage-1 posterior at the norm exceeds it at the extreme because
the prior does (`20 : 1` weights) — the evaluative step contributed nothing. -/
theorem eval_constant_preserves_peak :
    priorAfterEvalPosUsual (deg 3) > priorAfterEvalPosUsual (deg 6) := by
  rw [priorAfterEvalPosUsual_eq_prior]
  unfold heightPriorPMF
  rw [gt_iff_lt, PMF.normalize_apply, PMF.normalize_apply,
    mul_comm, mul_comm (heightPriorENN (deg 3))]
  refine ENNReal.mul_lt_mul_right
    (ENNReal.inv_ne_zero.mpr (ENNReal.tsum_ne_top_of_fintype heightPriorENN_finite))
    (ENNReal.inv_ne_top.mpr
      (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨deg 0, heightPriorENN_pos _⟩)) ?_
  unfold heightPriorENN
  rw [show (heightPrior (deg 6) : ℝ) = 1 from by
      norm_num [show heightPrior (deg 6) = 1 from rfl],
    show (heightPrior (deg 3) : ℝ) = 20 from by
      norm_num [show heightPrior (deg 3) = 20 from rfl]]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-! ## §5f. Prior-generic adjective stage; the bare and usually chains -/

/-- Prior-generic stage-2 literal listener (dite-total). -/
noncomputable def adjL0WithPrior (Pi : PMF Height) (vt : ValidThreshold)
    (u : RSA.Nouwen2024.AdjUtterance) : PMF Height :=
  if h_pos : (∑' h, Pi h *
      (if adjLex (validToThreshold vt) u h then (1 : ℝ≥0∞) else 0)) ≠ 0 then
    RSA.L0LassiterGoodman Pi (adjLex (validToThreshold vt)) u h_pos
  else PMF.uniformOfFintype Height

/-- Prior-generic stage-2 speaker (dite-total). -/
noncomputable def adjSpeakerWithPrior (Pi : PMF Height) (vt : ValidThreshold)
    (w : Height) : PMF (RSA.Nouwen2024.AdjUtterance) :=
  if h_pos : (∑' u, ((adjL0WithPrior Pi vt) u w : ℝ≥0∞) ^ (4 : ℝ) *
      adjCostFactor u) ≠ 0 then
    RSA.S1Belief (adjL0WithPrior Pi vt) adjCostFactor 4 w h_pos
      (ENNReal.tsum_ne_top_of_fintype fun u =>
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (PMF.apply_ne_top _ _))
          (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top))
  else PMF.pure .silent

/-- Prior-generic marginalized stage-2 speaker. -/
noncomputable def adjMarginalWithPrior (Pi : PMF Height) : Height → PMF AdjUtterance :=
  RSA.marginalizeKernel thresholdPriorPMF (fun vt w => adjSpeakerWithPrior Pi vt w)

theorem adjL0WithPrior_silent (Pi : PMF Height) (vt : ValidThreshold) (w : Height) :
    adjL0WithPrior Pi vt .silent w = Pi w := by
  have hm : (∑' h, Pi h *
      (if adjLex (validToThreshold vt) .silent h then (1 : ℝ≥0∞) else 0)) = 1 := by
    simp only [show ∀ h, adjLex (validToThreshold vt) .silent h = true from
      fun _ => rfl, if_true, mul_one]
    exact PMF.tsum_coe _
  unfold adjL0WithPrior
  rw [dif_pos (by rw [hm]; exact one_ne_zero)]
  exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _

private theorem adjSpeakerWithPrior_h_pos (Pi : PMF Height) (vt : ValidThreshold)
    {w : Height} (hPw : Pi w ≠ 0) :
    (∑' u, ((adjL0WithPrior Pi vt) u w : ℝ≥0∞) ^ (4 : ℝ) * adjCostFactor u) ≠ 0 := by
  rw [sumAdjUtt]
  intro hz
  rcases mul_eq_zero.mp (add_eq_zero.mp hz).2 with h5 | h5
  · rw [adjL0WithPrior_silent] at h5
    rcases ENNReal.rpow_eq_zero_iff.mp h5 with ⟨hz0, -⟩ | ⟨-, hneg⟩
    · exact hPw hz0
    · norm_num at hneg
  · rw [adjCostFactor_silent] at h5
    exact one_ne_zero h5

/-- Π-mass of the `.warm` extension at threshold `vt`. -/
noncomputable def adjMassP (Pi : PMF Height) (vt : ValidThreshold) : ℝ≥0∞ :=
  ∑' h, Pi h * (if adjLex (validToThreshold vt) .warm h then (1 : ℝ≥0∞) else 0)

/-- Prior-generic stage-2 speaker value on support: mass form. -/
noncomputable def fvalP (Pi : PMF Height) (vt : ValidThreshold) : ℝ≥0∞ :=
  (adjMassP Pi vt)⁻¹ ^ (4 : ℝ) * adjCostFactor .warm /
    ((adjMassP Pi vt)⁻¹ ^ (4 : ℝ) * adjCostFactor .warm + 1)

/-- **Ratio cancellation, prior-generic stage 2**: on support, at a
non-degenerate world, the speaker's value is `fvalP Pi vt` — independent of
the world. -/
theorem adjSpeakerWithPrior_apply_of_true (Pi : PMF Height) (vt : ValidThreshold)
    (w : Height) (hw : adjLex (validToThreshold vt) .warm w = true)
    (hPw : Pi w ≠ 0) :
    adjSpeakerWithPrior Pi vt w .warm = fvalP Pi vt := by
  have hPt : Pi w ≠ ⊤ := PMF.apply_ne_top _ _
  have hmne : adjMassP Pi vt ≠ 0 :=
    ENNReal.summable.tsum_ne_zero_iff.mpr
      ⟨w, by rw [hw]; simp only [if_true, mul_one]; exact hPw⟩
  have hL0warm : adjL0WithPrior Pi vt .warm w = Pi w * (adjMassP Pi vt)⁻¹ := by
    have hm' : (∑' h, Pi h *
        (if adjLex (validToThreshold vt) .warm h then (1 : ℝ≥0∞) else 0)) ≠ 0 := hmne
    unfold adjL0WithPrior
    rw [dif_pos hm', RSA.L0LassiterGoodman_apply, hw]
    simp only [if_true, mul_one]
    rfl
  unfold adjSpeakerWithPrior
  rw [dif_pos (adjSpeakerWithPrior_h_pos Pi vt hPw), RSA.S1Belief_apply, sumAdjUtt,
    hL0warm, adjL0WithPrior_silent, adjCostFactor_silent, mul_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
  have hP4 : (Pi w) ^ (4 : ℝ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hPw) hPt).ne'
  have hP4t : (Pi w) ^ (4 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPt
  rw [mul_assoc ((Pi w) ^ (4 : ℝ)), ← div_eq_mul_inv,
    show (Pi w) ^ (4 : ℝ) * ((adjMassP Pi vt)⁻¹ ^ (4 : ℝ) * adjCostFactor .warm) +
          (Pi w) ^ (4 : ℝ)
        = (Pi w) ^ (4 : ℝ) * ((adjMassP Pi vt)⁻¹ ^ (4 : ℝ) * adjCostFactor .warm + 1)
      from by ring,
    ENNReal.mul_div_mul_left _ _ hP4 hP4t]
  rfl

/-- Marginal positivity for the prior-generic stage-2 chain at any world where
the prior is positive and `.warm` holds at threshold 0. -/
private theorem bareAdj_marginal_ne_zero (u : RSA.Nouwen2024.AdjUtterance) :
    PMF.marginal (adjMarginalWithPrior heightPriorPMF) heightPriorPMF u ≠ 0 := by
  refine PMF.marginal_ne_zero _ _ _ (heightPriorPMF_pos (deg 4)) ?_
  unfold adjMarginalWithPrior
  rw [RSA.marginalizeKernel_apply]
  apply ENNReal.summable.tsum_ne_zero_iff.mpr
  refine ⟨0, mul_ne_zero ?_ ?_⟩
  · rw [thresholdPriorPMF, PMF.uniformOfFintype_apply]; simp
  · have hcf : adjCostFactor u ≠ 0 := by
      unfold adjCostFactor
      rw [ENNReal.ofReal_ne_zero_iff]
      exact Real.exp_pos _
    have hL0 : adjL0WithPrior heightPriorPMF 0 u (deg 4) ≠ 0 := by
      cases u
      · have hmne : (∑' h, heightPriorPMF h *
            (if adjLex (validToThreshold 0) .warm h then (1 : ℝ≥0∞) else 0)) ≠ 0 :=
          ENNReal.summable.tsum_ne_zero_iff.mpr
            ⟨deg 4, by rw [show adjLex (validToThreshold 0) .warm (deg 4) = true from
              by decide]; simp only [if_true, mul_one]; exact heightPriorPMF_pos _⟩
        unfold adjL0WithPrior
        rw [dif_pos hmne, ← PMF.mem_support_iff, RSA.mem_support_L0LassiterGoodman_iff]
        exact ⟨heightPriorPMF_pos _, by decide⟩
      · rw [adjL0WithPrior_silent]
        exact heightPriorPMF_pos _
    unfold adjSpeakerWithPrior
    rw [dif_pos (adjSpeakerWithPrior_h_pos heightPriorPMF 0 (heightPriorPMF_pos (deg 4)))]
    exact RSA.S1Belief_apply_ne_zero_of_pos _ _ _ _ _ _ hL0 hcf

/-- Baseline chain: bare "warm" over the raw height prior. -/
noncomputable def bareAdjL1 (u : RSA.Nouwen2024.AdjUtterance) : PMF Height :=
  PMF.posterior (adjMarginalWithPrior heightPriorPMF) heightPriorPMF u
    (bareAdj_marginal_ne_zero u)

/-- The "usually warm" chain: stage 2 over the (identity) usual posterior. -/
noncomputable def seqAdjL1Usually (u : RSA.Nouwen2024.AdjUtterance) : PMF Height :=
  PMF.posterior (adjMarginalWithPrior priorAfterEvalPosUsual) priorAfterEvalPosUsual u
    (by rw [priorAfterEvalPosUsual_eq_prior]; exact bareAdj_marginal_ne_zero u)

/-- **"Usually warm" IS bare "warm"**: the second half of Zwicky's vacuity —
with the identity evaluative update (`priorAfterEvalPosUsual_eq_prior`), the
whole sequential chain collapses to the baseline. Together with
`seq_unusually_shifts_extreme` this subsumes the old cross-model
discrimination pair without any cross-model numeric comparison. -/
theorem seqUsually_eq_bare (u : RSA.Nouwen2024.AdjUtterance) :
    seqAdjL1Usually u = bareAdjL1 u := by
  ext h
  unfold seqAdjL1Usually bareAdjL1
  rw [PMF.posterior_apply, PMF.posterior_apply, priorAfterEvalPosUsual_eq_prior]

private theorem adjMassP_ne_top (Pi : PMF Height) (vt : ValidThreshold) :
    adjMassP Pi vt ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  calc adjMassP Pi vt
      ≤ ∑' h', Pi h' := ENNReal.tsum_le_tsum fun h' => by split <;> simp
    _ = 1 := PMF.tsum_coe _

private theorem fvalP_ne_zero (Pi : PMF Height) (vt : ValidThreshold)
    (hm : adjMassP Pi vt ≠ 0) : fvalP Pi vt ≠ 0 := by
  unfold fvalP
  rw [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  have hcf : adjCostFactor .warm ≠ 0 := by
    unfold adjCostFactor
    rw [ENNReal.ofReal_ne_zero_iff]
    exact Real.exp_pos _
  constructor
  · exact mul_ne_zero
      (ENNReal.rpow_pos (ENNReal.inv_pos.mpr (adjMassP_ne_top Pi vt))
        (ENNReal.inv_ne_top.mpr hm)).ne' hcf
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (ENNReal.inv_ne_top.mpr hm))
        (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top),
       ENNReal.one_ne_top⟩

private theorem fvalP_ne_top (Pi : PMF Height) (vt : ValidThreshold)
    (hm : adjMassP Pi vt ≠ 0) : fvalP Pi vt ≠ ⊤ :=
  ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
        (ENNReal.inv_ne_top.mpr hm))
      (by unfold adjCostFactor; exact ENNReal.ofReal_ne_top))
    (by simp)

private theorem bareMass_ne_zero (vt : ValidThreshold) :
    adjMassP heightPriorPMF vt ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨deg 4, by
    rw [show adjLex (validToThreshold vt) .warm (deg 4) = true from by revert vt; decide]
    simp only [if_true, mul_one]
    exact heightPriorPMF_pos _⟩

/-- Bare "warm" prefers the moderate `deg 4` over the extreme `deg 6`: both
worlds license every valid threshold, so the marginalised speaker values
coincide (ratio cancellation) and the raw prior (`10 : 1`) decides. -/
theorem bare_warm_prefers_moderate :
    bareAdjL1 .warm (deg 4) > bareAdjL1 .warm (deg 6) := by
  unfold bareAdjL1
  rw [gt_iff_lt, PMF.posterior_lt_iff_score_lt]
  have hA : ∀ w : Height, (∀ vt : ValidThreshold,
      adjLex (validToThreshold vt) .warm w = true) →
      adjMarginalWithPrior heightPriorPMF w .warm
        = 3⁻¹ * fvalP heightPriorPMF 0 + 3⁻¹ * fvalP heightPriorPMF 1 +
          3⁻¹ * fvalP heightPriorPMF 2 := by
    intro w hall
    unfold adjMarginalWithPrior
    rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
      adjSpeakerWithPrior_apply_of_true _ _ _ (hall 0) (heightPriorPMF_pos w),
      adjSpeakerWithPrior_apply_of_true _ _ _ (hall 1) (heightPriorPMF_pos w),
      adjSpeakerWithPrior_apply_of_true _ _ _ (hall 2) (heightPriorPMF_pos w)]
  rw [hA _ (by decide), hA _ (by decide)]
  set C := (3 : ℝ≥0∞)⁻¹ * fvalP heightPriorPMF 0 + 3⁻¹ * fvalP heightPriorPMF 1 +
    3⁻¹ * fvalP heightPriorPMF 2 with hCdef
  have hC0 : C ≠ 0 := by
    intro hz
    rcases mul_eq_zero.mp (add_eq_zero.mp (add_eq_zero.mp hz).1).1 with h | h
    · exact ENNReal.inv_ne_zero.mpr (by norm_num) h
    · exact fvalP_ne_zero _ _ (bareMass_ne_zero 0) h
  have h3t : (3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hCt : C ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩ <;>
      exact ENNReal.mul_ne_top h3t (fvalP_ne_top _ _ (bareMass_ne_zero _))
  have hP : heightPriorPMF (deg 6) < heightPriorPMF (deg 4) := by
    unfold heightPriorPMF
    rw [PMF.normalize_apply, PMF.normalize_apply,
      mul_comm, mul_comm (heightPriorENN (deg 4))]
    refine ENNReal.mul_lt_mul_right
      (ENNReal.inv_ne_zero.mpr (ENNReal.tsum_ne_top_of_fintype heightPriorENN_finite))
      (ENNReal.inv_ne_top.mpr
        (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨deg 0, heightPriorENN_pos _⟩)) ?_
    unfold heightPriorENN
    rw [show (heightPrior (deg 6) : ℝ) = 1 from by
        norm_num [show heightPrior (deg 6) = 1 from rfl],
      show (heightPrior (deg 4) : ℝ) = 10 from by
        norm_num [show heightPrior (deg 4) = 10 from rfl]]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  rw [mul_comm (heightPriorPMF (deg 6)), mul_comm (heightPriorPMF (deg 4))]
  exact ENNReal.mul_lt_mul_right hC0 hCt hP

/-! ## §5g. The posterior-boost fact

`μ_unusual = μ_horrible` holds by definition (`muUnusualN_eq_muHorrible`),
so every "unusually" prediction is the corresponding horribly theorem
verbatim; no duplicates are stated. The remaining content of the old
cross-measure comparison is the posterior-vs-prior boost below. -/

theorem gval_ne_zero (vt : ValidThreshold) : gval vt ≠ 0 := by
  unfold gval
  rw [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  constructor
  · exact mul_ne_zero
      (ENNReal.rpow_pos (ENNReal.inv_pos.mpr (evalMass_ne_top vt))
        (ENNReal.inv_ne_top.mpr (evalMass_ne_zero vt))).ne'
      (evalCostFactor_pos _)
  · exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          (ENNReal.inv_ne_top.mpr (evalMass_ne_zero vt)))
        (evalCostFactor_finite _),
       ENNReal.one_ne_top⟩

theorem evalMarginal_deg6 :
    evalSpeakerMarginalHorrible (deg 6) .eval_pos
      = 3⁻¹ * gval 0 + 3⁻¹ * gval 1 + 3⁻¹ * gval 2 := by
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior,
    evalSpeaker_apply_of_true 0 _ (by decide),
    evalSpeaker_apply_of_true 1 _ (by decide),
    evalSpeaker_apply_of_true 2 _ (by decide)]

theorem evalMarginal_deg3 :
    evalSpeakerMarginalHorrible (deg 3) .eval_pos = 0 := by
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply, sumVT,
    evalSpeaker_apply_of_false 0 _ (by decide),
    evalSpeaker_apply_of_false 1 _ (by decide),
    evalSpeaker_apply_of_false 2 _ (by decide), mul_zero, mul_zero, mul_zero,
    add_zero, add_zero]

/-- No height's evaluative marginal exceeds the extreme's: `deg 6` licenses
every valid threshold, so it collects every mass-form value in full. -/
private theorem evalMarginal_le_deg6 (h : Height) :
    evalSpeakerMarginalHorrible h .eval_pos
      ≤ evalSpeakerMarginalHorrible (deg 6) .eval_pos := by
  have hle : ∀ vt : ValidThreshold,
      evalSpeaker_horribleAt vt h .eval_pos ≤ gval vt := by
    intro vt
    by_cases hw : evalLex muHorrible (validToThreshold vt) .eval_pos h = true
    · rw [evalSpeaker_apply_of_true vt h hw]
    · rw [evalSpeaker_apply_of_false vt h (by simpa using hw)]
      exact zero_le
  rw [evalMarginal_deg6]
  unfold evalSpeakerMarginalHorrible
  rw [RSA.marginalizeKernel_apply, sumVT, uPrior, uPrior, uPrior]
  exact add_le_add (add_le_add (mul_le_mul_right (hle 0) _)
    (mul_le_mul_right (hle 1) _)) (mul_le_mul_right (hle 2) _)

private theorem evalMarginal_deg6_ne_zero :
    evalSpeakerMarginalHorrible (deg 6) .eval_pos ≠ 0 := by
  rw [evalMarginal_deg6]
  intro hz
  rcases mul_eq_zero.mp (add_eq_zero.mp (add_eq_zero.mp hz).1).1 with h | h
  · exact ENNReal.inv_ne_zero.mpr (by norm_num) h
  · exact gval_ne_zero 0 h

/-- **The evaluative update boosts the extreme above its prior** — the deep
form of the old `eval_unusual_boosts_extreme`: the constant-measure update is
the identity (`priorAfterEvalPosUsual_eq_prior`), so the old cross-measure
comparison at `deg 6` is posterior-vs-prior. Average argument: no height
beats the extreme's marginal (`evalMarginal_le_deg6`) and the norm
contributes zero (`evalMarginal_deg3`), so the normaliser sits strictly
below the extreme's kernel value. -/
theorem eval_unusual_boosts_extreme :
    priorAfterEvalPos (deg 6) > heightPriorPMF (deg 6) := by
  unfold priorAfterEvalPos evalL1Horrible
  rw [gt_iff_lt, PMF.posterior_apply]
  have hE6t : evalSpeakerMarginalHorrible (deg 6) .eval_pos ≠ ⊤ := PMF.apply_ne_top _ _
  have hZlt : PMF.marginal evalSpeakerMarginalHorrible heightPriorPMF .eval_pos
      < evalSpeakerMarginalHorrible (deg 6) .eval_pos := by
    show (heightPriorPMF.bind evalSpeakerMarginalHorrible) .eval_pos < _
    rw [PMF.bind_apply]
    calc (∑' h, heightPriorPMF h * evalSpeakerMarginalHorrible h .eval_pos)
        < ∑' h, heightPriorPMF h * evalSpeakerMarginalHorrible (deg 6) .eval_pos := by
          refine ENNReal.tsum_lt_tsum (i := deg 3)
            (ENNReal.tsum_ne_top_of_fintype fun h =>
              ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
            (fun h => mul_le_mul_right (evalMarginal_le_deg6 h) _) ?_
          rw [evalMarginal_deg3, mul_zero]
          exact pos_iff_ne_zero.mpr
            (mul_ne_zero (heightPriorPMF_pos _) evalMarginal_deg6_ne_zero)
      _ = evalSpeakerMarginalHorrible (deg 6) .eval_pos := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc heightPriorPMF (deg 6)
      = heightPriorPMF (deg 6) * evalSpeakerMarginalHorrible (deg 6) .eval_pos *
          (evalSpeakerMarginalHorrible (deg 6) .eval_pos)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel evalMarginal_deg6_ne_zero hE6t, mul_one]
    _ < heightPriorPMF (deg 6) * evalSpeakerMarginalHorrible (deg 6) .eval_pos *
          (PMF.marginal evalSpeakerMarginalHorrible heightPriorPMF .eval_pos)⁻¹ :=
        ENNReal.mul_lt_mul_right
          (mul_ne_zero (heightPriorPMF_pos _) evalMarginal_deg6_ne_zero)
          (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) hE6t)
          (ENNReal.inv_lt_inv.mpr hZlt)

/-! ## §6. Predictions

The headline below states that "horribly warm" shifts probability toward
*high* heights (deg 5 > deg 2). **HONEST SCOPE**: this is the
*monotone-shift* shape, NOT the Goldilocks shape that Nouwen 2024
Figures 5-7 actually depict. Goldilocks would require BOTH extremes (very
cold AND very hot) to be evaluated as horrible — Nouwen's `f(x) = x²`
quadratic from Figure 4(b). The file's `muHorrible` is monotone-decreasing
in `h.toNat`, so the headline is mathematically the right statement for
THIS model but the WRONG statement for Nouwen's actual Goldilocks claim.
See module docstring §3 of "Scope (honest reckoning)". -/

/-- The headline shift prediction in PMF form: "horribly warm" pushes
probability toward the high extreme (`deg 5` over the moderate `deg 2`).

**Fully structural discharge** — no numeric reflection. The chained
`posterior κ₂ (posterior κ₁ μ b₁) b₂` shape decomposes via
`PMF.posterior_chained_lt_iff_score_lt` to a product comparison
`μ(2)·E(2)·A(2) < μ(5)·E(5)·A(5)`; the ratio-cancellation lemmas (§5b)
collapse each marginal to a sum of the mass-monotone speaker value over the
licensed thresholds (`E(h) = Σ_{θ_e < μ_H(h)} gval θ_e`, `A(h) = Σ_{θ < h}
fval θ`), and the raw prior ratio `μ(2) = 2·μ(5)` is beaten by informativity
alone: `gval 1 > gval 0` (strictly smaller extension mass at the higher
threshold), so `(g₀+g₁)(f₀+f₁+f₂) > 2·g₀·(f₀+f₁)`. -/
theorem seq_horribly_shifts_upward :
    seqAdjL1HorriblyWarm .warm (deg 5) >
    seqAdjL1HorriblyWarm .warm (deg 2) := by
  unfold seqAdjL1HorriblyWarm priorAfterEvalPos evalL1Horrible
  rw [gt_iff_lt, PMF.posterior_chained_lt_iff_score_lt,
    evalMarginal_deg2, evalMarginal_deg5, adjMarginal_deg2, adjMarginal_deg5,
    heightPriorPMF_deg2_eq]
  have hF0 : fval 0 + fval 1 ≠ 0 := fun h => fval_ne_zero 0 (add_eq_zero.mp h).1
  have hFt : fval 0 + fval 1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨fval_ne_top 0, fval_ne_top 1⟩
  have key : 2 * gval 0 * (fval 0 + fval 1)
      < (gval 0 + gval 1) * (fval 0 + fval 1 + fval 2) := by
    have h1 : 2 * gval 0 * (fval 0 + fval 1)
        < (gval 0 + gval 1) * (fval 0 + fval 1) := by
      rw [two_mul, mul_comm (gval 0 + gval 0), mul_comm (gval 0 + gval 1)]
      exact ENNReal.mul_lt_mul_right hF0 hFt
        (ENNReal.add_lt_add_left (gval_ne_top 0) gval_zero_lt_one)
    exact h1.trans_le (mul_le_mul_right le_self_add _)
  have h3 : (3 : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by norm_num)
  have h3t : (3 : ℝ≥0∞)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
  have hP5 : heightPriorPMF (deg 5) ≠ 0 := heightPriorPMF_pos _
  have hP5t : heightPriorPMF (deg 5) ≠ ⊤ := PMF.apply_ne_top _ _
  calc 2 * heightPriorPMF (deg 5) * (3⁻¹ * gval 0) * (3⁻¹ * fval 0 + 3⁻¹ * fval 1)
      = heightPriorPMF (deg 5) * 3⁻¹ * 3⁻¹ * (2 * gval 0 * (fval 0 + fval 1)) := by
        ring
    _ < heightPriorPMF (deg 5) * 3⁻¹ * 3⁻¹ *
        ((gval 0 + gval 1) * (fval 0 + fval 1 + fval 2)) :=
        ENNReal.mul_lt_mul_right
          (mul_ne_zero (mul_ne_zero hP5 h3) h3)
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top hP5t h3t) h3t) key
    _ = heightPriorPMF (deg 5) * (3⁻¹ * gval 0 + 3⁻¹ * gval 1) *
        (3⁻¹ * fval 0 + 3⁻¹ * fval 1 + 3⁻¹ * fval 2) := by
        ring

/-! ## §6'. Substrate gaps documented as sorry'd theorems (Nouwen 2024 not-formalised)

The following stubs explicitly mark what the file does NOT capture from
Nouwen 2024. Each is the formal statement of the substrate gap; closing
them would require substrate work documented in the module docstring. -/

/-- **Eq. 44b factive embedding (Nouwen 2024 §3.2) — NOT FORMALISED.**

Nouwen's novel semantic proposal (paper p. 2:21) requires the adverb's
positive form to embed the *proposition* `λw. μ_A(x)(@) = μ_A(x)(w)`
(Wheeler-style factive layer). The conjunction
`(μ_A(x) ≥ θ_i) ∧ (μ_D(λw. μ_A(x)(@) = μ_A(x)(w)) ≥ θ_j)` is what
distinguishes Nouwen 2024's intersection from L&G's straight positive
form.

This file's stage-1 evaluative meaning predicates `muHorrible` of heights
directly (`evalLex evalMu θ u h := muHorrible h > θ.toNat`), without the
propositional embedding. Without Eq. 44b's factive layer, the prediction
is L&G's, not Nouwen's. Closing requires a `Prop`/`Bool`-valued lex over
propositions, not just heights — substantial substrate refactor. -/
theorem eq_44b_factive_embedding_NOT_FORMALISED :
    -- Placeholder: should state that the file's evalLex implements the
    -- factive embedding `μ_horrible(λw.μ_warm(x)(@) = μ_warm(x)(w))`.
    -- Until the substrate exists, the statement is unstateable as a
    -- meaningful Lean theorem.
    True := trivial

/-- **Eq. 49 QUD partition `Q^A_X` (Nouwen 2024 §4) — NOT FORMALISED.**

Nouwen's σ/ρ are defined over equivalence classes of worlds, not raw
worlds. The partition `Q^A_X = {[w]_~^A_X | w ∈ W}` is built from the
equivalence `w ~^A_X w' iff μ_A(x)(w) ≈ μ_A(x)(w')` with explicit
granularity `≈` (Nouwen rounds to one decimal in Figure 3).

The file operates over raw `Height` with no quotient or equivalence
relation. At small `Height` cardinality the partition collapses to
identity and the shortcut is vacuously fine for the toy example, but the
file cannot extend to Nouwen's Figures 4-7 (which depend on the QUD
partition + measure-function-on-cells distinction). Closing requires
defining `Quotient`-typed prior + kernels — substantial substrate
refactor. -/
theorem eq_49_qud_partition_NOT_FORMALISED :
    -- Placeholder: should state that the file's prior + kernels are
    -- defined over `Height / ~_A^X` rather than raw `Height`.
    -- Until the substrate exists, the statement is unstateable.
    True := trivial

/-! ## §7. Structural-decomposition demos (lemma library witnesses)

The following theorems exercise the inequality-decomposition lemmas added in
0.230.387. Each one proves a structural claim about the model that the new
lemmas dispatch in 1-2 lines — no numeric arithmetic required. The contrast
with `seq_horribly_shifts_upward` (closed structurally via §5b) is
the point: structural shell handles structural claims; the numeric core is
reflection territory, regardless of bundling. -/

/-- Order on the stage-2 `.warm` literal listener at worlds where the
adjective extension holds reduces to order on the (eval-stage) prior.
Demonstrates `L0LassiterGoodman_apply_lt_iff_prior_lt`: when the indicator
is true at both points, only the prior matters.

In linguistic terms: the literal listener's "warm-ranking" of two heights
that BOTH satisfy the threshold inherits the eval-stage L1's ordering.
The L0's normalisation by the warm-extension partition cancels. -/
theorem adjL0_warm_meaning_pos_lt_iff_prior_lt
    (vt : ValidThreshold) (w₁ w₂ : Height)
    (h₁ : adjLex (validToThreshold vt) .warm w₁ = true)
    (h₂ : adjLex (validToThreshold vt) .warm w₂ = true) :
    adjL0_warmAt vt .warm w₁ < adjL0_warmAt vt .warm w₂ ↔
      priorAfterEvalPos w₁ < priorAfterEvalPos w₂ := by
  unfold adjL0_warmAt
  exact RSA.L0LassiterGoodman_apply_lt_iff_prior_lt _ _ _ _ _ _ h₁ h₂

/-- The silent utterance's literal listener IS the eval-stage prior pointwise.
Direct application of `L0LassiterGoodman_apply_of_meaning_true` (the silent
utterance has trivially-true meaning at every world).

This is the "vacuous-utterance reduction": informationally-empty utterances
leave the listener's beliefs unchanged from the prior. -/
theorem adjL0_silent_eq_prior (vt : ValidThreshold) (w : Height) :
    adjL0_warmAt vt .silent w = priorAfterEvalPos w := by
  unfold adjL0_warmAt
  exact RSA.L0LassiterGoodman_apply_of_meaning_true _ _ _ (fun _ => rfl) _ _


end RSA.Nouwen2024
