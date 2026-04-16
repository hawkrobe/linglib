import Mathlib.Order.Nat
import Linglib.Theories.Phonology.Features

/-!
# Syllable Structure

Syllable constituency (onset–nucleus–coda), sonority scale, the Sonority
Sequencing Principle, moraic weight, and OT markedness constraints.

## Substance-free sonority

The sonority hierarchy is represented as an abstract ordered type
(`SonorityRank`) rather than being defined by articulatory features.
Following @cite{berent-2026}, the synchronic grammar operates on the
ordering alone — the correlation with phonetic features ([±sonorant],
[±approximant], etc.) is a diachronic/evolutionary fact, not a
grammatical primitive. The grounding function `sonorityOf` maps
segments to ranks via their features, but the SSP and markedness
constraints see only `SonorityRank`.

Source: @cite{goldsmith-2011} "The Syllable" in *The Handbook of Phonological
Theory* (Ch 6, pp. 164–196). Cross-referenced with Hayes §4.6 and §15.

@cite{goldsmith-2011} @cite{berent-2026}
-/

namespace Phonology.Syllable

open Phonology (Segment Feature)

-- ============================================================================
-- § 1: Sonority Scale
-- ============================================================================

/-- The abstract sonority hierarchy: what the synchronic grammar operates on.

    Following @cite{berent-2026}, phonological constraints on syllable
    structure are *substance-free* — the grammar sees an ordered set of
    sonority categories, not the articulatory features that happen to
    correlate with them. The correlation is diachronic (shaped by cultural
    evolution and articulatory pressures), but the synchronic computation
    is algebraic.

    | Rank | Category  |
    |------|-----------|
    |  0   | Stop      |
    |  1   | Fricative |
    |  2   | Nasal     |
    |  3   | Liquid    |
    |  4   | Glide     |
    |  5   | Vowel     |

    The 6 levels follow @cite{clements-1990}'s refinement of the basic
    5-class hierarchy (splitting obstruents by [±continuant]). See
    `NatClass.parkerSonority` for the finer 8-level Parker scale. -/
inductive SonorityRank where
  | stop
  | fricative
  | nasal
  | liquid
  | glide
  | vowel
  deriving DecidableEq, Repr

namespace SonorityRank

/-- Numeric rank (0 = least sonorous). -/
def rank : SonorityRank → Nat
  | .stop => 0 | .fricative => 1 | .nasal => 2
  | .liquid => 3 | .glide => 4 | .vowel => 5

/-- `SonorityRank.rank` is injective: distinct ranks map to distinct Nats. -/
theorem rank_injective : Function.Injective SonorityRank.rank :=
  fun a b h => by cases a <;> cases b <;> simp_all [SonorityRank.rank]

/-- Linear order on sonority ranks, lifted from the numeric ranking.
    Enables `<`, `≤`, `max`, `min` on `SonorityRank` directly — used by
    SONCON and other sonority-sensitive constraints. Follows the same
    pattern as `Stratum` in `StratalOT.lean`. -/
instance : LinearOrder SonorityRank :=
  LinearOrder.lift' SonorityRank.rank rank_injective

end SonorityRank

/-- Substance-based grounding: classify a segment into the sonority
    hierarchy by its phonetic features.

    Following @cite{hayes-2009}, the hierarchy is decomposed by four
    features ([±sonorant] > [±approximant] > [±consonantal] > [±syllabic]),
    with @cite{clements-1990}'s refinement splitting obstruents by
    [±continuant].

    This function bridges phonetic substance and the abstract `SonorityRank`
    type. The SSP and other grammatical constraints operate on `SonorityRank`
    directly — they do not inspect articulatory features. -/
def sonorityOf (s : Segment) : SonorityRank :=
  if s.hasValue .sonorant false then
    -- Obstruent: stop vs fricative (@cite{clements-1990} refinement)
    if s.hasValue .continuant true then .fricative else .stop
  else if s.hasValue .approximant false then
    -- Nasal ([+sonorant, −approximant])
    .nasal
  else if s.hasValue .consonantal true then
    -- Liquid ([+sonorant, +approximant, +consonantal])
    .liquid
  else if s.hasValue .syllabic true then
    -- Vowel ([+sonorant, +approximant, −consonantal, +syllabic])
    .vowel
  else
    -- Glide ([+sonorant, +approximant, −consonantal, −syllabic])
    .glide

-- ============================================================================
-- § 2: Syllable Constituents
-- ============================================================================

/-- A syllable: onset, nucleus, coda. The rhyme (nucleus ++ coda) groups
    naturally in phonological processes. -/
structure Syllable where
  onset   : List Segment
  nucleus : List Segment
  coda    : List Segment

/-- The rhyme (rime): nucleus + coda. -/
def Syllable.rhyme (σ : Syllable) : List Segment := σ.nucleus ++ σ.coda

/-- All segments in linear order. -/
def Syllable.segments (σ : Syllable) : List Segment :=
  σ.onset ++ σ.nucleus ++ σ.coda

def Syllable.hasOnset (σ : Syllable) : Bool := !σ.onset.isEmpty
def Syllable.hasCoda (σ : Syllable) : Bool := !σ.coda.isEmpty
def Syllable.isOpen (σ : Syllable) : Bool := σ.coda.isEmpty
def Syllable.isClosed (σ : Syllable) : Bool := !σ.coda.isEmpty

-- ============================================================================
-- § 3: Sonority Sequencing Principle
-- ============================================================================

/-- Is a list of Nats monotonically non-decreasing? -/
def monotoneRising : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => (a ≤ b) && monotoneRising (b :: rest)

/-- Is a list of Nats monotonically non-increasing? -/
def monotoneFalling : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => (a ≥ b) && monotoneFalling (b :: rest)

/-- Does the onset obey SSP? Sonority rises toward the nucleus. -/
def Syllable.sspOnset (σ : Syllable) : Bool :=
  monotoneRising (σ.onset.map (λ s => (sonorityOf s).rank))

/-- Does the coda obey SSP? Sonority falls from the nucleus. -/
def Syllable.sspCoda (σ : Syllable) : Bool :=
  monotoneFalling (σ.coda.map (λ s => (sonorityOf s).rank))

/-- Full SSP: onset rises, coda falls. -/
def Syllable.sspValid (σ : Syllable) : Bool :=
  σ.sspOnset && σ.sspCoda

-- ============================================================================
-- § 4: Syllabified Form
-- ============================================================================

/-- A syllabified form: a word parsed into syllables. -/
structure SyllabifiedForm where
  syllables : List Syllable

/-- Total segment count. -/
def SyllabifiedForm.segmentCount (sf : SyllabifiedForm) : Nat :=
  sf.syllables.foldl (· + ·.segments.length) 0

/-- All segments in linear order. -/
def SyllabifiedForm.allSegments (sf : SyllabifiedForm) : List Segment :=
  sf.syllables.flatMap Syllable.segments

-- ============================================================================
-- § 5: Syllable Weight
-- ============================================================================

/-- Syllable weight: the mora count of a syllable.

    Instead of a lossy 3-value enum, `SyllWeight` wraps the actual mora
    count. The conventional names `.light` (1μ), `.heavy` (2μ),
    `.superheavy` (3μ) are abbreviations for the common values.

    This design ensures the prosodic pipeline is lossless:
    `MoraicSyllable → SyllWeight → PrWd` preserves exact mora counts,
    so bridge theorems between moraic and segmental views are trivial. -/
structure SyllWeight where
  /-- The mora count: 1μ = light (CV), 2μ = heavy (CVV, CVC),
      3μ = superheavy (CVVC, CVCC). -/
  morae : Nat
  deriving DecidableEq, Repr

namespace SyllWeight
abbrev light : SyllWeight := ⟨1⟩
abbrev heavy : SyllWeight := ⟨2⟩
abbrev superheavy : SyllWeight := ⟨3⟩
end SyllWeight

/-- Mora count. `codaMoraic = true` means coda consonants contribute weight
    (the "Weight-by-Position" parameter of @cite{hayes-1989}). -/
def Syllable.moraCount (σ : Syllable) (codaMoraic : Bool := true) : Nat :=
  σ.nucleus.length + if codaMoraic then σ.coda.length else 0

/-- Weight from mora count. -/
def Syllable.weight (σ : Syllable) (codaMoraic : Bool := true) : SyllWeight :=
  ⟨σ.moraCount codaMoraic⟩

-- ============================================================================
-- § 6: OT Markedness Constraints
-- ============================================================================

/-- ONSET: every syllable must have an onset.
    Returns count of onsetless syllables. -/
def onsetViolations (sf : SyllabifiedForm) : Nat :=
  sf.syllables.filter (fun σ => !σ.hasOnset) |>.length

/-- NOCODA: syllables should not have codas.
    Returns count of syllables with codas. -/
def noCodaViolations (sf : SyllabifiedForm) : Nat :=
  sf.syllables.filter Syllable.hasCoda |>.length

/-- *COMPLEXONSET: no complex (multi-segment) onsets.
    Returns count of syllables with onset length > 1. -/
def complexOnsetViolations (sf : SyllabifiedForm) : Nat :=
  sf.syllables.filter (fun σ => σ.onset.length > 1) |>.length

/-- *COMPLEXCODA: no complex (multi-segment) codas.
    Returns count of syllables with coda length > 1. -/
def complexCodaViolations (sf : SyllabifiedForm) : Nat :=
  sf.syllables.filter (fun σ => σ.coda.length > 1) |>.length

/-- SSP: every syllable obeys the Sonority Sequencing Principle.
    Returns count of syllables violating SSP. -/
def sspViolations (sf : SyllabifiedForm) : Nat :=
  sf.syllables.filter (fun σ => !σ.sspValid) |>.length

-- ============================================================================
-- § 7: Verification Theorems
-- ============================================================================

theorem monotoneRising_singleton (n : Nat) : monotoneRising [n] = true := rfl
theorem monotoneFalling_singleton (n : Nat) : monotoneFalling [n] = true := rfl

theorem cv_is_light (σ : Syllable) (h1 : σ.nucleus.length = 1)
    (h2 : σ.coda = []) :
    σ.weight = .light := by
  simp only [Syllable.weight, Syllable.moraCount, h2, List.length_nil, h1,
    ite_true, Nat.add_zero]

theorem cvc_is_heavy (σ : Syllable) (h1 : σ.nucleus.length = 1)
    (h2 : σ.coda.length = 1) :
    σ.weight = .heavy := by
  simp only [Syllable.weight, Syllable.moraCount, h1, h2, ite_true]

end Phonology.Syllable
