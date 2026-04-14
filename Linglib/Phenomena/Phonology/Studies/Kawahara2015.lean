import Linglib.Theories.Phonology.Accent
import Linglib.Theories.Phonology.Moraic.Defs
import Linglib.Fragments.Japanese.Prosody

/-!
# Kawahara (2015) @cite{kawahara-2015}

The phonology of Japanese accent. In Haruo Kubozono (ed.),
*The handbook of Japanese phonetics and phonology*, 445–492.
Berlin: De Gruyter Mouton.

This survey chapter provides a comprehensive overview of Tokyo Japanese
pitch accent, covering default accent assignment, compound accent,
verb/adjective paradigms, affix accent typology, and interactions with
epenthesis, rendaku, and vowel devoicing.

## Formalized contributions

1. **AAR vs LSR** (§2, Table 1): the two accent assignment rules agree
   on 6 of 8 trisyllabic weight conditions and diverge on HLH and LLH.
2. **Accent-to-tone derivation** (§1.4): surface tones are fully
   determined by accent location via accentual HL, initial rise, and
   tonal spreading.
3. **Eight affix accent types** (§6): the traditional dominant/recessive
   distinction is refined into an 8-way typology.
4. **Compound accent** (§4): short N2 (≤2μ) triggers pre-accenting or
   retention; long N2 (≥3μ) triggers N2-initial accent or retention.
-/

namespace Phenomena.Phonology.Studies.Kawahara2015

open Core.Prosody
open Theories.Phonology.Accent
open Theories.Phonology.Syllable (SyllWeight)
open Fragments.Japanese.Prosody

-- ============================================================================
-- § 1: AAR vs LSR — Table 1 Completeness
-- ============================================================================

/-- Table 1 completeness: exactly 2 of 8 conditions produce different
    predictions between AAR and LSR. The mismatches are HLH and LLH.

    In both mismatch cases, the AAR predicts accent on σ₂ (the syllable
    containing the antepenultimate mora) while the LSR predicts accent
    on σ₁ (the antepenultimate syllable, because the penult is light).

    @cite{kubozono-2008} argues that LSR-conforming pronunciations
    appear as variants even in the mismatch cases, suggesting the LSR
    may be the better characterization. -/
theorem table1_exactly_two_mismatches :
    -- The 6 matching cases (re-exported from fragment for completeness)
    defaultAccentAAR [.heavy, .heavy, .heavy] =
      latinStressRule [.heavy, .heavy, .heavy] ∧
    defaultAccentAAR [.heavy, .heavy, .light] =
      latinStressRule [.heavy, .heavy, .light] ∧
    defaultAccentAAR [.heavy, .light, .light] =
      latinStressRule [.heavy, .light, .light] ∧
    defaultAccentAAR [.light, .heavy, .heavy] =
      latinStressRule [.light, .heavy, .heavy] ∧
    defaultAccentAAR [.light, .heavy, .light] =
      latinStressRule [.light, .heavy, .light] ∧
    defaultAccentAAR [.light, .light, .light] =
      latinStressRule [.light, .light, .light] ∧
    -- The 2 mismatch cases
    defaultAccentAAR [.heavy, .light, .heavy] ≠
      latinStressRule [.heavy, .light, .heavy] ∧
    defaultAccentAAR [.light, .light, .heavy] ≠
      latinStressRule [.light, .light, .heavy] := by
  exact ⟨by unfold latinStressRule; rfl,
    by unfold latinStressRule; rfl,
    by unfold latinStressRule; rfl,
    by unfold latinStressRule; rfl,
    by unfold latinStressRule; rfl,
    by unfold latinStressRule; rfl,
    by intro h; unfold latinStressRule at h; exact absurd h (by decide),
    by intro h; unfold latinStressRule at h; exact absurd h (by decide)⟩

-- ============================================================================
-- § 2: Accent-to-Tone — the n+1 Pattern
-- ============================================================================

/-- For n-mora words, there are n+1 distinct accent patterns: accent can
    fall on any of the n moras, or the word can be unaccented.

    However, word-internally, final accent and unaccented produce the same
    tonal contour (both LHH for 3 morae), because the post-accent L falls
    off the word edge. They are distinguished only in phrasal context
    (e.g., followed by a particle).

    We verify that the first 3 patterns (unaccented, initial, medial) are
    pairwise distinct, and that final-accented = unaccented word-internally. -/
theorem trisyllabic_tone_patterns :
    -- Distinct pairs
    accentToTones none 3 ≠ accentToTones (some 0) 3 ∧
    accentToTones none 3 ≠ accentToTones (some 1) 3 ∧
    accentToTones (some 0) 3 ≠ accentToTones (some 1) 3 ∧
    -- Final accent = unaccented word-internally (post-accent L falls off)
    accentToTones none 3 = accentToTones (some 2) 3 := by
  exact ⟨by decide, by decide, by decide, rfl⟩

-- ============================================================================
-- § 3: Culminativity
-- ============================================================================

/-- Culminativity: Japanese allows at most one accent per prosodic word.
    We verify that `JProsodicEntry` structurally enforces this — accent
    is a single `Option Nat`, so there can be at most one accented mora
    by construction. -/
theorem culminativity_by_construction (e : JProsodicEntry) :
    (match e.accentMora with | none => 0 | some _ => 1) ≤ 1 := by
  cases e.accentMora <;> simp

-- ============================================================================
-- § 4: Affix Typology — Coarse Classification
-- ============================================================================

/-- The 8 affix types collapse to exactly two prosodic dominance classes:
    recessive (3 types) and dominant (5 types). -/
theorem affix_typology_coarse_partition :
    -- Recessive class (preserve root accent when present)
    tara_suffix.accentType.toProsodicDominance = .recessive ∧
    si_affix.accentType.toProsodicDominance = .recessive ∧
    mono_suffix.accentType.toProsodicDominance = .recessive ∧
    -- Dominant class (override root accent)
    ppoi_suffix.accentType.toProsodicDominance = .dominant ∧
    ke_suffix.accentType.toProsodicDominance = .dominant ∧
    o_prefix.accentType.toProsodicDominance = .dominant ∧
    teki_affix.accentType.toProsodicDominance = .dominant ∧
    zu_suffix.accentType.toProsodicDominance = .dominant :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Compound Accent — NonFinality Drives Pre-Accenting
-- ============================================================================

/-- Short N2 pre-accenting moves accent off the final syllable of the
    compound, consistent with NonFinality(σ). -/
theorem short_n2_preaccent_avoids_final :
    let result := shortN2CompoundAccent 3 (some 1) true  -- 3μ N1, pre-accenting
    let totalMorae := 3 + 2  -- N1 + short N2
    nonFinalitySigma result totalMorae = 0 := rfl

/-- Long N2 with unaccented N2 assigns accent to N2-initial syllable,
    which is never word-final (since N2 is ≥ 3μ). -/
theorem long_n2_initial_avoids_final :
    let result := longN2CompoundAccent 3 none 4  -- 3μ N1, 4μ unaccented N2
    let totalMorae := 3 + 4
    nonFinalitySigma result totalMorae = 0 := rfl

-- ============================================================================
-- § 6: Weight Sensitivity — Japanese as Weight-Sensitive
-- ============================================================================

/-- Japanese moraic structure: WBP is active (coda consonants are moraic).
    This means coda nasals (/N/), geminate first halves (/Q/), and long
    vowels all contribute to syllable weight. The weight sensitivity of
    accent assignment (AAR/LSR) operates on these moraic weights.

    @cite{kawahara-2015} §2.3: syllables with coda nasal, first part of
    geminate, long vowel, or diphthong are bimoraic (heavy). Open
    syllables with short vowels are monomoraic (light). -/
theorem japanese_wbp_active (o n c : Theories.Phonology.Segment) :
    -- CVC with WBP is heavy (e.g., /tan/ = 2μ)
    (Theories.Phonology.Moraic.syllableToMoraic { wbp := true }
      ⟨[o], [n], [c]⟩).toSyllWeight = .heavy := rfl

end Phenomena.Phonology.Studies.Kawahara2015
