import Linglib.Theories.Phonology.Syllable.Defs
import Linglib.Theories.Phonology.Syllable.Foot

/-!
# Accent Assignment and Tone Derivation
@cite{hayes-1995} @cite{kawahara-2015}

Language-general accent assignment rules and the accent-to-tone
derivation for pitch accent systems.

## Accent Assignment Rules

Two rules that derive default accent position from syllable weight:

- **Antepenultimate Accent Rule (AAR)**: accent falls on the syllable
  containing the antepenultimate (3rd-from-last) mora. This is the
  traditional characterization of the default accent pattern in Japanese
  (@cite{mccawley-1968}).

- **Latin Stress Rule (LSR)**: accent falls on the penultimate syllable
  if heavy, otherwise on the antepenultimate. @cite{kubozono-2008}
  argues the LSR better characterizes Japanese loanword accentuation,
  capitalizing on the cross-linguistic parallel with Latin stress
  (@cite{hayes-1995}).

## Accent-to-Tone Derivation

For pitch-accent languages like Japanese, surface tonal patterns are
fully determined by accent location. The derivation follows
@cite{kawahara-2015} §1.4:

1. **Accentual HL**: H on the accented mora, L on the following mora.
2. **Initial rise**: L on the first mora, H on the second (blocked when
   the first mora is accented).
3. **Spreading**: unspecified moras copy the rightmost specified tone.

## NonFinality

Two NonFinality constraints from @cite{prince-smolensky-1993}:

- **NonFinality(σ)**: penalizes accent on the word-final syllable.
- **NonFinality(Ft)**: penalizes the head foot in word-final position.
-/

namespace Phonology.Accent

open Phonology.Syllable (SyllWeight MetricalParse ParseElement footMorae)

-- ============================================================================
-- § 1: Syllable-from-Mora Lookup
-- ============================================================================

/-- Find the 0-indexed syllable containing the k-th mora (0-indexed).
    Returns `none` if the target mora exceeds the total mora count. -/
def findSyllable (weights : List SyllWeight) (targetMora : Nat) : Option Nat :=
  go weights targetMora 0
where
  go : List SyllWeight → Nat → Nat → Option Nat
    | [], _, _ => none
    | w :: ws, target, idx =>
      if target < w.morae then some idx
      else go ws (target - w.morae) (idx + 1)

-- ============================================================================
-- § 2: Antepenultimate Accent Rule (AAR)
-- ============================================================================

/-- **Antepenultimate Accent Rule** (@cite{mccawley-1968}): accent falls
    on the syllable containing the antepenultimate (3rd-from-last) mora.

    For words with fewer than 3 morae, accent falls on the initial
    syllable (the only possibility for bimoraic minimal words).

    Returns the 0-indexed syllable position. -/
def defaultAccentAAR (weights : List SyllWeight) : Option Nat :=
  match weights with
  | [] => none
  | _ =>
    let totalMorae := weights.foldl (· + ·.morae) 0
    let targetMora := if totalMorae ≥ 3 then totalMorae - 3 else 0
    findSyllable weights targetMora

-- ============================================================================
-- § 3: Latin Stress Rule (LSR)
-- ============================================================================

/-- **Latin Stress Rule** (@cite{hayes-1995}): accent the penultimate
    syllable if it is heavy (≥ 2μ), otherwise accent the antepenultimate.

    For monosyllables, accent the only syllable. For disyllables, always
    accent the penultimate (= initial) syllable.

    @cite{kubozono-2008} argues this rule better characterizes Japanese
    default accentuation than the AAR. -/
def latinStressRule : List SyllWeight → Option Nat
  | [] => none
  | [_] => some 0
  | [_, _] => some 0                    -- disyllable → always penult (= initial)
  | [_, ⟨0⟩, _] | [_, ⟨1⟩, _] => some 0  -- light penult → antepenult
  | [_, _, _] => some 1                 -- heavy+ penult → penult
  | _ :: rest@(_ :: _ :: _) =>           -- peel front, recurse, add 1
    (latinStressRule rest).map (· + 1)

-- ============================================================================
-- § 4: Accent-to-Tone Derivation
-- ============================================================================

/-- Level tone for pitch accent systems. Japanese uses only H and L at
    the lexical level (@cite{kawahara-2015} §1.3). -/
inductive LevelTone where
  | H  -- High
  | L  -- Low
  deriving DecidableEq, Repr, BEq

/-- Derive surface tones from accent position and mora count.

    Implements the 4-step derivation of @cite{kawahara-2015} §1.4:
    1. Accentual HL assignment (H on accented mora, L on next)
    2. Initial rise (L on mora 0, H on mora 1 — blocked by initial accent)
    3. Spreading (unspecified moras copy rightmost specified tone)

    Returns a list of `LevelTone` with one entry per mora. -/
def accentToTones (accentMora : Option Nat) (nMorae : Nat) : List LevelTone :=
  if nMorae == 0 then []
  else
    -- Steps 1+2: assign specified tones
    let specified : List (Option LevelTone) := (List.range nMorae).map λ i =>
      -- Step 1: accentual HL
      if accentMora == some i then some .H
      else if accentMora == some (i - 1) && i ≥ 1 then some .L
      -- Step 2: initial rise (only if not already specified by accent)
      else if i == 0 && accentMora != some 0 then some .L
      else if i == 1 && accentMora != some 1 &&
              accentMora != some 0 then some .H
      else none
    -- Step 3: spreading — fill nones from rightmost specified tone
    spread specified .H  -- default H (shouldn't be needed for well-formed inputs)
where
  spread : List (Option LevelTone) → LevelTone → List LevelTone
    | [], _ => []
    | some t :: rest, _ => t :: spread rest t
    | none :: rest, last => last :: spread rest last

-- ============================================================================
-- § 5: NonFinality Constraints
-- ============================================================================

/-- **NonFinality(σ)** (@cite{prince-smolensky-1993}): penalizes accent
    on the word-final syllable. Returns 1 if accent is final, 0 otherwise.

    Drives the avoidance of final accent observed in Japanese compound
    formation and loanword adaptation (@cite{kawahara-2015} §4). -/
def nonFinalitySigma (accentSyll : Option Nat) (nSyll : Nat) : Nat :=
  match accentSyll with
  | some pos => if pos + 1 == nSyll then 1 else 0
  | none => 0

/-- **NonFinality(Ft)** (@cite{prince-smolensky-1993}): penalizes the
    head foot in word-final position. Returns 1 if the rightmost foot
    in the parse is the head foot (contains the accent), 0 otherwise.

    Distinct from NonFinality(σ): accent on the final *syllable* may be
    tolerated if the final *foot* is not the head foot. -/
def nonFinalityFoot (parse : MetricalParse) (accentSyll : Option Nat) : Nat :=
  match parse.reverse.head? with
  | some (.foot ws) =>
    -- Check if any syllable in the final foot is accented
    let finalFootStart := parse.foldl (λ acc e => acc + match e with
      | .foot ws => ws.length | .unfooted _ => 1) 0 - ws.length
    match accentSyll with
    | some pos => if pos ≥ finalFootStart && pos < finalFootStart + ws.length
                  then 1 else 0
    | none => 0
  | _ => 0

-- ============================================================================
-- § 6: Compound Accent
-- ============================================================================

/-- **Short N2 compound accent**: when the second member of a compound
    (N2) is short (≤ 2 morae), accent may fall on the last syllable of
    N1 (pre-accenting pattern) or N2 may retain its own accent.

    @cite{kawahara-2015} §4.1: pre-accenting N2s are those that lose
    their accent to NonFinality(Ft) and receive new accent via a
    compound accent rule analogous to dominant pre-accenting suffixes. -/
def shortN2CompoundAccent (n1Morae : Nat) (n2Accent : Option Nat)
    (preAccenting : Bool) : Option Nat :=
  if preAccenting then
    -- Pre-accenting: accent on last mora of N1
    if n1Morae > 0 then some (n1Morae - 1) else none
  else
    -- Retain N2 accent (shifted by N1 length)
    n2Accent.map (· + n1Morae)

/-- **Long N2 compound accent**: when N2 is long (≥ 3 morae), if N2 is
    unaccented or has final accent, accent falls on N2-initial syllable.
    Otherwise, N2 accent is retained.

    @cite{kawahara-2015} §4.2. -/
def longN2CompoundAccent (n1Morae : Nat) (n2Accent : Option Nat)
    (n2Morae : Nat) : Option Nat :=
  match n2Accent with
  | none => some n1Morae  -- unaccented N2 → accent N2-initial
  | some pos =>
    if pos + 1 == n2Morae then some n1Morae  -- final accent → accent N2-initial
    else some (pos + n1Morae)                 -- retain N2 accent

-- ============================================================================
-- § 7: Verification Theorems — AAR
-- ============================================================================

-- Bimoraic words: accent the initial syllable

theorem aar_bimoraic_hl : defaultAccentAAR [.heavy, .light] = some 0 := rfl
theorem aar_bimoraic_ll : defaultAccentAAR [.light, .light] = some 0 := rfl

-- Trisyllabic words: the n+1 pattern

theorem aar_lll : defaultAccentAAR [.light, .light, .light] = some 0 := rfl
theorem aar_hll : defaultAccentAAR [.heavy, .light, .light] = some 0 := rfl

-- ============================================================================
-- § 8: Verification Theorems — LSR
-- ============================================================================

theorem lsr_heavy_penult :
    latinStressRule [.light, .heavy, .light] = some 1 := by
  unfold latinStressRule; rfl
theorem lsr_light_penult :
    latinStressRule [.light, .light, .light] = some 0 := by
  unfold latinStressRule; rfl
theorem lsr_disyllable :
    latinStressRule [.light, .light] = some 0 := by
  unfold latinStressRule; rfl

-- ============================================================================
-- § 9: Verification Theorems — Accent-to-Tone
-- ============================================================================

/-- Unaccented trisyllable → LHH (initial rise, H spreads). -/
theorem tones_unaccented_3 :
    accentToTones none 3 = [.L, .H, .H] := rfl

/-- Initial accent trisyllable → HLL (accent HL, L spreads). -/
theorem tones_initial_3 :
    accentToTones (some 0) 3 = [.H, .L, .L] := rfl

/-- Medial accent trisyllable → LHL (initial rise L, accent H, post-accent L). -/
theorem tones_medial_3 :
    accentToTones (some 1) 3 = [.L, .H, .L] := rfl

/-- Unaccented 4-mora → LHHH. Kawahara (7). -/
theorem tones_unaccented_4 :
    accentToTones none 4 = [.L, .H, .H, .H] := rfl

/-- Initial accent 4-mora → HLLL. Kawahara (8). -/
theorem tones_initial_4 :
    accentToTones (some 0) 4 = [.H, .L, .L, .L] := rfl

/-- Antepenultimate accent 4-mora → LHLL. -/
theorem tones_antepenult_4 :
    accentToTones (some 1) 4 = [.L, .H, .L, .L] := by decide

/-- Antepenultimate accent 5-mora → LHHLL. Kawahara (9). -/
theorem tones_antepenult_5 :
    accentToTones (some 2) 5 = [.L, .H, .H, .L, .L] := by decide

-- ============================================================================
-- § 10: Verification Theorems — NonFinality
-- ============================================================================

theorem nonfin_sigma_final :
    nonFinalitySigma (some 2) 3 = 1 := rfl
theorem nonfin_sigma_nonfinal :
    nonFinalitySigma (some 1) 3 = 0 := rfl
theorem nonfin_sigma_unaccented :
    nonFinalitySigma none 3 = 0 := rfl

end Phonology.Accent
