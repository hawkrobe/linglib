import Linglib.Theories.Phonology.Features

/-!
# Syllable Structure

Syllable constituency (onset–nucleus–coda), sonority scale, the Sonority
Sequencing Principle, moraic weight, and OT markedness constraints.

Source: @cite{goldsmith-2011} "The Syllable" in *The Handbook of Phonological
Theory* (Ch 6, pp. 164–196). Cross-referenced with Hayes §4.6 and §15.

@cite{goldsmith-2011}
-/

namespace Theories.Phonology.Syllable

open Theories.Phonology (Segment Feature)

-- ============================================================================
-- § 1: Sonority Scale
-- ============================================================================

/-- Sonority rank (0 = least sonorous). Following @cite{hayes-2009},
    the 5-level hierarchy is decomposed by four features:

    | Class     | son | approx | cons | syll | Rank |
    |-----------|-----|--------|------|------|------|
    | Obstruent |  −  |   −    |  +   |  −   |  0   |
    | Nasal     |  +  |   −    |  +   |  −   |  1   |
    | Liquid    |  +  |   +    |  +   |  −   |  2   |
    | Glide     |  +  |   +    |  −   |  −   |  3   |
    | Vowel     |  +  |   +    |  −   |  +   |  4   |

    Within obstruents, [±continuant] further splits stops (rank 0) from
    fricatives (rank 1) per @cite{clements-1990}, yielding a 6-level scale. -/
def sonorityOf (s : Segment) : Nat :=
  if s.hasValue .sonorant false then
    -- Obstruent: stop vs fricative (@cite{clements-1990} refinement)
    if s.hasValue .continuant true then 1 else 0
  else if s.hasValue .approximant false then
    -- Nasal ([+sonorant, −approximant])
    2
  else if s.hasValue .consonantal true then
    -- Liquid ([+sonorant, +approximant, +consonantal])
    3
  else if s.hasValue .syllabic true then
    -- Vowel ([+sonorant, +approximant, −consonantal, +syllabic])
    5
  else
    -- Glide ([+sonorant, +approximant, −consonantal, −syllabic])
    4

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
  monotoneRising (σ.onset.map sonorityOf)

/-- Does the coda obey SSP? Sonority falls from the nucleus. -/
def Syllable.sspCoda (σ : Syllable) : Bool :=
  monotoneFalling (σ.coda.map sonorityOf)

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

/-- Syllable weight classes. -/
inductive SyllWeight where
  | light       -- CV (1 mora)
  | heavy       -- CVC or CVV (2 morae)
  | superheavy  -- CVVC, CVCC (3+ morae)
  deriving DecidableEq, BEq, Repr

/-- Mora count. `codaMoraic = true` means coda consonants contribute weight
    (the "Weight-by-Position" parameter of @cite{hayes-1989}). -/
def Syllable.moraCount (σ : Syllable) (codaMoraic : Bool := true) : Nat :=
  σ.nucleus.length + if codaMoraic then σ.coda.length else 0

/-- Weight classification from mora count. -/
def Syllable.weight (σ : Syllable) (codaMoraic : Bool := true) : SyllWeight :=
  match σ.moraCount codaMoraic with
  | 0 | 1 => .light
  | 2 => .heavy
  | _ => .superheavy

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

end Theories.Phonology.Syllable
