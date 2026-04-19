import Linglib.Theories.Phonology.OptimalityTheory.Doubling

/-!
# Berent, Bat-El, Brentari, Dupuis & Vaknin-Nusbaum (2016) @cite{berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016}

The double identity of linguistic doubling.
*Proceedings of the National Academy of Sciences* 113(48). 13702--13707.

Twelve experiments demonstrating that the interpretation of doubled forms
(XX) depends on (i) morphological context and (ii) the speaker's L1
morphological system. The key finding is a 2x2 cross-linguistic
dissociation between English and Hebrew speakers:

|              | English (no productive redup) | Hebrew (redup for diminutives) |
|--------------|------------------------------|-------------------------------|
| **Plurality**  | Prefer XX (Exps 2, 4a, 8a)   | Weak/no XX pref (Exp 10a)     |
| **Diminutive** | No XX preference (Exp 12)    | Prefer XX (Exp 11a)           |

## Gradient vs. categorical

The experimental data are gradient: participants show *stronger* or *weaker*
XX preferences across conditions, measured by rating differences and
reaction times. The OT model here gives categorical predictions
(reduplication wins or XY wins). The categorical predictions capture the
*direction* of the preference in each cell — which condition shows an XX
advantage — not the continuous magnitude of the effect.

## Mechanism: positive and negative transfer

- **Positive transfer**: if the L1 expresses function *f* morphologically,
  the speaker can interpret XX as morphological reduplication for *f*,
  yielding a doubling preference (XX > XY).

- **Negative transfer**: if the L1 uses reduplication for *other* functions
  but specifically NOT for *f*, the speaker has positive evidence that
  reduplication != *f*. This blocks the reduplication interpretation for *f*,
  even if *f* is morphologically marked by other means (e.g., Hebrew marks
  plurality by suffixation, not reduplication — so Hebrew speakers do not
  interpret XX as plural reduplication).

## Formalization

The doubling framework (`DoublingParse`, `DoublingGrammar`,
`realizeMorphAvailable`) is defined in `Theories/Phonology/Doubling.lean`.
This file defines L1-specific `DoublingGrammar` instances for English and
Hebrew and proves the four cells of the dissociation table as OT theorems.

@cite{berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016}
-/

open Phonology.Doubling

namespace BerentEtAl2016

open Core.OT

-- ============================================================================
-- § 1: L1 Morphological Grammars
-- ============================================================================

/-- English morphological knowledge relevant to doubling.

    English marks plurality morphologically (dog-s) but does not have
    productive reduplication for any function, and does not have
    productive diminutive morphology (booklet, doggy are semi-productive
    at best). -/
def englishGrammar : DoublingGrammar :=
  { morphFor := fun | .plurality => true | .diminutive => false
    redupFor := fun | .plurality => false | .diminutive => false }

/-- Hebrew morphological knowledge relevant to doubling.

    Hebrew marks both plurality (sefer -> sfarim 'book -> books') and
    diminutives morphologically. Crucially, Hebrew uses reduplication
    specifically for diminutives (seleg -> slaglag 'snow -> puppy')
    but NOT for plurality (which uses suffixation). -/
def hebrewGrammar : DoublingGrammar :=
  { morphFor := fun | .plurality => true | .diminutive => true
    redupFor := fun | .plurality => false | .diminutive => true }

-- ============================================================================
-- § 2: Transfer Predictions
-- ============================================================================

/-- English: REALIZE-MORPH is available for plurality.
    English marks plurality morphologically and has no productive
    reduplication at all, so there is no negative transfer. -/
theorem english_plurality_available :
    realizeMorphAvailable englishGrammar .plurality = true := by decide

/-- English: REALIZE-MORPH is unavailable for diminutives.
    English does not productively mark diminutives morphologically,
    so the morphological interpretation of XX-as-diminutive is not
    available (regardless of reduplication status). -/
theorem english_diminutive_unavailable :
    realizeMorphAvailable englishGrammar .diminutive = false := by decide

/-- Hebrew: REALIZE-MORPH is unavailable for plurality.
    Hebrew marks plurality morphologically, but it also uses
    reduplication for diminutives — NOT for plurality. This creates
    negative transfer: Hebrew speakers have positive evidence that
    reduplication != plurality, blocking the reduplication parse. -/
theorem hebrew_plurality_unavailable :
    realizeMorphAvailable hebrewGrammar .plurality = false := by decide

/-- Hebrew: REALIZE-MORPH is available for diminutives.
    Hebrew uses reduplication specifically for diminutives. Positive
    transfer: Hebrew speakers interpret XX as diminutive reduplication. -/
theorem hebrew_diminutive_available :
    realizeMorphAvailable hebrewGrammar .diminutive = true := by decide

-- ============================================================================
-- § 3: OT Predictions — the 2×2 dissociation
-- ============================================================================

/-! The four cells of the dissociation table follow from the transfer
    predictions above. When REALIZE-MORPH is available, the morphological
    ranking applies and reduplication wins. When unavailable, the
    phonological ranking applies and XY (nonidentical) wins. -/

/-- English + plurality: reduplication wins (Exps 2, 4a, 8a).
    English speakers show a gradient XX preference (higher ratings,
    faster RTs) when signs are paired with homogeneous object sets
    in a plurality context. The categorical prediction captures the
    direction of this gradient effect. -/
theorem english_plurality_prefers_XX :
    (mkTableau
      (l1CandidatesFor englishGrammar .plurality)
      (l1RankingFor englishGrammar .plurality)
      (l1CandidatesFor_ne englishGrammar .plurality)).optimal
    = {.reduplication} := by decide

/-- English + diminutive: XY wins (Exp 12).
    English speakers show no XX advantage for diminutive signs
    because English lacks productive diminutive morphology. The model
    predicts XY wins categorically; the data show absence of the
    XX preference seen in the plurality condition. -/
theorem english_diminutive_prefers_XY :
    (mkTableau
      (l1CandidatesFor englishGrammar .diminutive)
      (l1RankingFor englishGrammar .diminutive)
      (l1CandidatesFor_ne englishGrammar .diminutive)).optimal
    = {.nonidentical} := by decide

/-- Hebrew + plurality: XY wins (Exp 10a).
    Hebrew speakers show weak/no XX advantage for plural signs
    because Hebrew uses reduplication for diminutives but NOT plurality —
    negative transfer blocks the reduplication parse. The model predicts
    XY categorically; the data show attenuation or absence of the
    XX preference relative to the diminutive condition. -/
theorem hebrew_plurality_prefers_XY :
    (mkTableau
      (l1CandidatesFor hebrewGrammar .plurality)
      (l1RankingFor hebrewGrammar .plurality)
      (l1CandidatesFor_ne hebrewGrammar .plurality)).optimal
    = {.nonidentical} := by decide

/-- Hebrew + diminutive: reduplication wins (Exp 11a).
    Hebrew speakers show a gradient XX preference for diminutive signs
    because Hebrew has productive reduplicative diminutives — positive
    transfer makes the reduplication parse available. The categorical
    prediction captures the direction of the effect. -/
theorem hebrew_diminutive_prefers_XX :
    (mkTableau
      (l1CandidatesFor hebrewGrammar .diminutive)
      (l1RankingFor hebrewGrammar .diminutive)
      (l1CandidatesFor_ne hebrewGrammar .diminutive)).optimal
    = {.reduplication} := by decide

-- ============================================================================
-- § 4: The full dissociation
-- ============================================================================

/-- The 2x2 cross-linguistic dissociation: English and Hebrew speakers
    show opposite patterns for plurality vs. diminutive contexts.

    This is the central result of
    @cite{berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016}:
    doubling preferences are not determined by sensorimotor demands
    (the stimuli are identical novel ASL signs) but by the interaction
    of morphological context and L1 morphological knowledge.

    The dissociation follows from `realizeMorphAvailable`, which
    encodes both positive and negative transfer from L1 morphology. -/
theorem doubling_dissociation :
    -- English: prefer XX for plurality, XY for diminutive
    (mkTableau
      (l1CandidatesFor englishGrammar .plurality)
      (l1RankingFor englishGrammar .plurality)
      (l1CandidatesFor_ne englishGrammar .plurality)).optimal
      = {.reduplication} ∧
    (mkTableau
      (l1CandidatesFor englishGrammar .diminutive)
      (l1RankingFor englishGrammar .diminutive)
      (l1CandidatesFor_ne englishGrammar .diminutive)).optimal
      = {.nonidentical} ∧
    -- Hebrew: prefer XY for plurality, XX for diminutive
    (mkTableau
      (l1CandidatesFor hebrewGrammar .plurality)
      (l1RankingFor hebrewGrammar .plurality)
      (l1CandidatesFor_ne hebrewGrammar .plurality)).optimal
      = {.nonidentical} ∧
    (mkTableau
      (l1CandidatesFor hebrewGrammar .diminutive)
      (l1RankingFor hebrewGrammar .diminutive)
      (l1CandidatesFor_ne hebrewGrammar .diminutive)).optimal
      = {.reduplication} := by
  exact ⟨english_plurality_prefers_XX, english_diminutive_prefers_XY,
         hebrew_plurality_prefers_XY, hebrew_diminutive_prefers_XX⟩

end BerentEtAl2016
