import Linglib.Core.Prominence

/-!
# Form-Frequency Correspondence @cite{haspelmath-2021}
@cite{zipf-1935}

@cite{haspelmath-2021}'s deeper explanation of argument-coding splits:
the Role-Reference Association Universal (Universal 1) itself reduces to a
general cognitive tendency for frequent expressions to be short.

The key chain of explanation:

1. **Frequency asymmetry**: Some role-reference combinations are more
   frequent than others (e.g., "I saw him" is more frequent than "He saw
   me"; animate agents are more frequent than inanimate agents).

2. **Form-frequency correspondence**:
   More frequent expressions tend to get shorter forms. This is a
   diachronic process — frequent forms erode phonologically and resist
   analogical extension of explicit markers.

3. **Coding asymmetry**: The "usual" role-reference associations (which
   ARE the frequent ones) therefore get shorter (often zero) coding,
   while the "unusual" associations get longer (overt) coding.

This explains WHY the monotonicity patterns in DOM/DSM/differential
indexing exist: they track frequency gradients on the prominence scales.

-/

namespace Core.FormFrequency

open Core.Prominence

-- ============================================================================
-- § 1: Coding Length
-- ============================================================================

/-- Relative coding length of an argument expression.

    Haspelmath's claim is about *relative* length, not absolute morpheme
    counts. Zero marking is shorter than overt marking; shorter overt
    markers are shorter than longer ones. -/
inductive CodingLength where
  /-- Zero coding (no overt marker) -/
  | zero
  /-- Short overt coding (e.g., clitic, monosyllabic affix) -/
  | short
  /-- Long overt coding (e.g., full adposition, bisyllabic affix) -/
  | long
  deriving DecidableEq, BEq, Repr

/-- Numeric rank: zero (0) < short (1) < long (2). -/
def CodingLength.rank : CodingLength → Nat
  | .zero  => 0
  | .short => 1
  | .long  => 2

-- ============================================================================
-- § 2: Form-Frequency Correspondence
-- ============================================================================

/-- The form-frequency correspondence predicate: a coding system respects
    the form-frequency correspondence if more frequent role-reference
    combinations receive shorter (or equal) coding.

    `freq` returns relative frequency (higher = more frequent).
    `coding` returns the coding length for that combination.

    The predicate holds when: freq(x) > freq(y) → coding(x) ≤ coding(y). -/
def respectsFormFrequency {α : Type} [DecidableEq α]
    (domain : List α) (freq : α → Nat) (coding : α → CodingLength) : Bool :=
  domain.all λ x =>
    domain.all λ y =>
      if freq x > freq y then (coding x).rank ≤ (coding y).rank
      else true

/-- The form-frequency correspondence applied to argument coding:
    usual role-reference associations (high frequency) should get shorter
    coding than unusual ones (low frequency).

    This is the core claim of @cite{haspelmath-2021}: differential marking
    patterns are explained by frequency asymmetries, not by grammatical
    function per se. -/
def argumentCodingRespectsFrequency
    (_role : ArgumentRole)
    (freq : AnimacyLevel → DefinitenessLevel → Nat)
    (coding : AnimacyLevel → DefinitenessLevel → CodingLength)
    : Bool :=
  AnimacyLevel.all.all λ a₁ =>
    DefinitenessLevel.all.all λ d₁ =>
      AnimacyLevel.all.all λ a₂ =>
        DefinitenessLevel.all.all λ d₂ =>
          if freq a₁ d₁ > freq a₂ d₂
          then (coding a₁ d₁).rank ≤ (coding a₂ d₂).rank
          else true

-- ============================================================================
-- § 3: Connecting Frequency to Prominence
-- ============================================================================

/-- Haspelmath's bridge claim: for P/T arguments, prominence correlates
    positively with unusualness (and thus with coding length). That is,
    the frequency of a P with a given prominence is *inversely* related
    to prominence rank.

    For A/R arguments, the relationship is reversed: frequency is
    *directly* related to prominence rank.

    This function returns a frequency proxy based on prominence rank
    and role. It captures the claim that A-prominence is positively
    correlated with frequency while P-prominence is negatively correlated. -/
def frequencyProxy (role : ArgumentRole) (a : AnimacyLevel) (d : DefinitenessLevel) : Nat :=
  match role with
  | .A | .R => prominenceRank a d      -- high prominence = high frequency for A/R
  | .P | .T => 6 - prominenceRank a d  -- high prominence = LOW frequency for P/T
  | .S      => 3                        -- S is neutral

/-- The frequency proxy predicts that usual associations are more frequent. -/
theorem frequency_proxy_matches_default (role : ArgumentRole)
    (a : AnimacyLevel) (d : DefinitenessLevel) :
    (isDefaultZone role a d = true) →
    (frequencyProxy role a d ≥ 3) := by
  intro h
  cases role <;> simp [isDefaultZone, frequencyProxy, prominenceRank] at * <;> omega

-- ============================================================================
-- § 4: Voice Direction and Ditransitive Frames (Haspelmath 2021, §9)
-- ============================================================================

/-- Verb voice direction for direct/inverse systems.
    Direct forms mark downstream (usual) scenarios; inverse forms mark
    upstream (unusual) scenarios with morphologically more complex marking. -/
inductive VoiceDirection where
  | direct   -- downstream scenario, morphologically simpler
  | inverse  -- upstream scenario, morphologically more complex
  deriving DecidableEq, BEq, Repr

/-- Ditransitive frame alternation.
    Double-object construction is shorter; prepositional dative is longer. -/
inductive DitransitiveFrame where
  | doubleObject        -- V NP NP (shorter)
  | prepositionalDative -- V NP PP (longer)
  deriving DecidableEq, BEq, Repr

/-- Double-object is short coding; prepositional dative is long coding. -/
def DitransitiveFrame.codingLength : DitransitiveFrame → CodingLength
  | .doubleObject        => .short
  | .prepositionalDative => .long

-- ============================================================================
-- § 5: Scenario-Level Form-Frequency Correspondence
-- ============================================================================

/-- Scenario-level form-frequency correspondence: higher frequency-class
    scenarios should get shorter-or-equal coding. -/
def scenarioRespectsFormFrequency
    (scenarios : List Scenario) (coding : Scenario → CodingLength) : Bool :=
  scenarios.all λ s1 =>
    scenarios.all λ s2 =>
      if s1.frequencyClass > s2.frequencyClass
      then (coding s1).rank ≤ (coding s2).rank
      else true

end Core.FormFrequency
