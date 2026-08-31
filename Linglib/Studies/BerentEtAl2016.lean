import Linglib.Phonology.OptimalityTheory.Doubling

/-!
# The double identity of linguistic doubling

Formalization of [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016] (PNAS 113). Twelve
experiments show that the parse of a doubled form XX — banned phonological identity vs.
preferred morphological reduplication — depends on morphological context and on the
speaker's L1. With novel English words, doubling is disliked in isolation (experiment 1)
and preferred once linked to plural meaning over homogeneous object sets (experiments 2,
4b, 8b); sign-naïve English speakers project the same shift onto novel ASL signs
(aversion in experiment 5, preference in 6a). The cross-linguistic 2×2 (Table 1,
experiments 6a and 10a–12a): English speakers prefer XX signs as plurals (6a) but not as
diminutives (12a); Hebrew speakers show no plural preference (10a — negative transfer:
Hebrew reduplication marks diminution, never plurality) but favor XX diminutives (11a),
with a reliable Language × Meaning interaction.

The OT predictions are categorical and capture the direction of each cell, not the
gradient magnitudes. The framework (`DoublingParse`, `DoublingGrammar`,
`realizeMorphAvailable`) lives in `Phonology/OptimalityTheory/Doubling.lean`; this file
instantiates the two L1 grammars and proves the four cells.

## Main definitions

* `englishGrammar`, `hebrewGrammar` — the two L1 `DoublingGrammar`s.

## Main results

* `english_plurality_available`, `english_diminutive_unavailable`,
  `hebrew_plurality_unavailable`, `hebrew_diminutive_available` — REALIZE-MORPH
  availability from positive and negative transfer.
* `doubling_dissociation` — the 2×2: reduplication wins exactly where the L1 licenses it.

## References

* [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016] — the paper.
* [berent-2026] — Argument 3 of the synthesis builds on this dissociation.
-/

open OptimalityTheory.Doubling

namespace BerentEtAl2016

open Constraints OptimalityTheory

-- ============================================================================
-- § 1: L1 Morphological Grammars
-- ============================================================================

/-- English morphological knowledge relevant to doubling: plurality is marked
    morphologically (dog-s), but there is no productive reduplication for any function
    and no productive diminutive morphology (booklet, piglet are attested; -let is not
    productive). -/
def englishGrammar : DoublingGrammar :=
  { morphFor := fun | .plurality => true | .diminutive => false
    redupFor := fun | .plurality => false | .diminutive => false }

/-- Hebrew morphological knowledge relevant to doubling: both plurality (*shir* →
    *shirim* 'song → songs') and diminutives are marked morphologically, and
    reduplication is used specifically for diminutives (*kelev* → *klavlav*
    'dog → puppy') but never for plurality, which uses suffixation. -/
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

/-- English + plurality: reduplication wins (experiment 6a; with spoken words,
    experiments 2, 4b, 8b). English speakers prefer XX when paired with homogeneous
    object sets in a plurality context; the heterogeneous controls (4a, 6b, 8a) show no
    preference or an aversion. -/
theorem english_plurality_prefers_XX :
    (Tableau.ofRanking
      (l1CandidatesFor englishGrammar .plurality)
      (l1RankingFor englishGrammar .plurality)
      (l1CandidatesFor_ne englishGrammar .plurality)).optimal
    = {.reduplication} := by decide

/-- English + diminutive: XY wins (experiment 12a). English speakers show no XX
    advantage for diminutive signs — English lacks productive diminutive morphology. -/
theorem english_diminutive_prefers_XY :
    (Tableau.ofRanking
      (l1CandidatesFor englishGrammar .diminutive)
      (l1RankingFor englishGrammar .diminutive)
      (l1CandidatesFor_ne englishGrammar .diminutive)).optimal
    = {.nonidentical} := by decide

/-- Hebrew + plurality: XY wins (experiment 10a). Hebrew speakers show no XX advantage
    for plural signs — Hebrew uses reduplication for diminutives, never plurality, so
    negative transfer blocks the reduplication parse. -/
theorem hebrew_plurality_prefers_XY :
    (Tableau.ofRanking
      (l1CandidatesFor hebrewGrammar .plurality)
      (l1RankingFor hebrewGrammar .plurality)
      (l1CandidatesFor_ne hebrewGrammar .plurality)).optimal
    = {.nonidentical} := by decide

/-- Hebrew + diminutive: reduplication wins (experiment 11a). Positive transfer from
    Hebrew's partly productive reduplicative diminutives makes the parse available; the
    preference is marginal by participants and reliable with items as the sole random
    effect, which the paper links to that partial productivity. -/
theorem hebrew_diminutive_prefers_XX :
    (Tableau.ofRanking
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
    [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016]:
    doubling preferences are not determined by sensorimotor demands
    (the stimuli are identical novel ASL signs) but by the interaction
    of morphological context and L1 morphological knowledge.

    The dissociation follows from `realizeMorphAvailable`, which
    encodes both positive and negative transfer from L1 morphology. -/
theorem doubling_dissociation :
    -- English: prefer XX for plurality, XY for diminutive
    (Tableau.ofRanking
      (l1CandidatesFor englishGrammar .plurality)
      (l1RankingFor englishGrammar .plurality)
      (l1CandidatesFor_ne englishGrammar .plurality)).optimal
      = {.reduplication} ∧
    (Tableau.ofRanking
      (l1CandidatesFor englishGrammar .diminutive)
      (l1RankingFor englishGrammar .diminutive)
      (l1CandidatesFor_ne englishGrammar .diminutive)).optimal
      = {.nonidentical} ∧
    -- Hebrew: prefer XY for plurality, XX for diminutive
    (Tableau.ofRanking
      (l1CandidatesFor hebrewGrammar .plurality)
      (l1RankingFor hebrewGrammar .plurality)
      (l1CandidatesFor_ne hebrewGrammar .plurality)).optimal
      = {.nonidentical} ∧
    (Tableau.ofRanking
      (l1CandidatesFor hebrewGrammar .diminutive)
      (l1RankingFor hebrewGrammar .diminutive)
      (l1CandidatesFor_ne hebrewGrammar .diminutive)).optimal
      = {.reduplication} := by
  exact ⟨english_plurality_prefers_XX, english_diminutive_prefers_XY,
         hebrew_plurality_prefers_XY, hebrew_diminutive_prefers_XX⟩

end BerentEtAl2016
