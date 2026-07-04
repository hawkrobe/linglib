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
(eqs. 50–51) — lives on the mathlib-PMF face in `Nouwen2024PMF`
(`Linglib.Studies.Nouwen2024PMF`), where the predictions are proven
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
The chain itself and its predictions live in `Nouwen2024PMF`; this section
provides the stage utterance types, meanings, and costs it consumes. -/

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

end RSA.Nouwen2024
