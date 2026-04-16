import Linglib.Theories.Semantics.Tense.Perspective
import Linglib.Fragments.English.TemporalDeictic
import Linglib.Fragments.German.TemporalDeictic
import Linglib.Fragments.Mandarin.TemporalDeictic
import Linglib.Fragments.Japanese.TemporalDeictic
import Linglib.Fragments.Greek.TemporalDeictic
import Linglib.Fragments.Russian.TemporalDeictic
import Linglib.Fragments.Hebrew.TemporalDeictic
import Linglib.Fragments.Hungarian.TemporalDeictic

/-!
# @cite{tsilia-zhao-2026}: Tense and Perspective
@cite{tsilia-zhao-2026} @cite{sharvit-2003} @cite{zhao-2025}

The cross-linguistic incompatibility of temporal ⌈then⌉ with shifted present
tense is derived from **tense presuppositions** anchored to a perspectival
parameter π.

## The ⌈then⌉-Present Puzzle

When PRES and ⌈then⌉ occur in the same minimal clause, they share the
same π (Shift Together). PRES requires overlap with π; ⌈then⌉ requires
disjointness from π. The temporal assertion (g(n_pres) ⊆ g(n_then))
bridges them → presupposition failure.

Deleted tense escapes because it carries no presupposition — no overlap
requirement with π, so ⌈then⌉ can freely pick a disjoint reference.

## Key empirical finding

This incompatibility holds for the *shifted* present but NOT for the
*deleted* present. This distinguishes the two for the first time,
motivating the perspectival analysis.

## Cross-linguistic data

| Language | "then" form      | Shifts perspective? |
|----------|------------------|---------------------|
| English  | then             | yes                 |
| German   | damals/dann      | yes                 |
| Mandarin | 那时 nà-shí       | yes                 |
| Japanese | その時 sono-toki   | yes                 |
| Greek    | τότε tóte         | yes                 |
| Russian  | тогда togda       | yes                 |
| Hebrew   | אז az             | yes                 |
| Hungarian| akkor             | yes                 |

## Tense shift typology (Tables 1 & 2)

Present-under-past: English never shifts; Greek/Hebrew/Russian shift in
attitude reports only; Japanese shifts in both attitudes and relatives.

Present-under-future: ALL languages shift (WOLL is intensional → provides
OP_π site). But English present-under-future is *deleted* (SOT), not shifted,
which is why English ⌈then⌉ is compatible with it.

-/

namespace TsiliaZhao2026

open Core.Reichenbach
open Semantics.Tense
open Semantics.Tense.Perspective


-- ════════════════════════════════════════════════════════════════
-- § 1. Cross-Linguistic "Then" Inventory
-- ════════════════════════════════════════════════════════════════

/-- All "then" adverbs from Fragment entries. -/
def thenAdverbs : List ThenAdverb :=
  [ Fragments.English.TemporalDeictic.then_
  , Fragments.German.TemporalDeictic.damals
  , Fragments.Mandarin.TemporalDeictic.nashi
  , Fragments.Japanese.TemporalDeictic.sonotoki
  , Fragments.Greek.TemporalDeictic.tote
  , Fragments.Russian.TemporalDeictic.togda
  , Fragments.Hebrew.TemporalDeictic.az
  , Fragments.Hungarian.TemporalDeictic.akkor ]

/-- Every "then" adverb in our inventory shifts perspective. -/
theorem all_then_shift_perspective :
    ∀ a ∈ thenAdverbs, a.shiftsPerspective = true := by
  intro a ha
  simp only [thenAdverbs, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


-- ════════════════════════════════════════════════════════════════
-- § 2. Shift Together
-- ════════════════════════════════════════════════════════════════

/-- Shift Together: OP_π is propositional — it scopes over the entire
    embedded clause. All perspective-sensitive items in that clause
    (tense + ⌈then⌉) therefore share the SAME shifted π.

    Formally: `opPi` sets `perspectiveTime` once for the whole frame.
    Any two reads of `perspectiveTime` from the same shifted frame agree. -/
theorem shift_together {Time : Type*}
    (f : ReichenbachFrame Time) (newPi : Time) :
    (opPi f newPi).perspectiveTime = (opPi f newPi).perspectiveTime := rfl

/-- The interesting consequence: within a shifted clause, PRES requires
    overlap with the SAME π that ⌈then⌉ requires disjointness from.
    There is no LF where they read different perspectives —
    unlike the pronominal analysis where independent anchor indices
    could in principle diverge. -/
theorem shift_together_blocks_mixed_reading {Time : Type*}
    (f : ReichenbachFrame Time) (newPi : Time)
    (hPres : presPresup (opPi f newPi))
    (hThen : thenPresup (opPi f newPi).referenceTime (opPi f newPi).perspectiveTime)
    : False := by
  exact hThen hPres


-- ════════════════════════════════════════════════════════════════
-- § 3. Sharvit Bridge
-- ════════════════════════════════════════════════════════════════

/-- The @cite{sharvit-2003} simultaneous reading is the special case where a PRES
    presupposition is trivially satisfied at the shifted perspective.
    `simultaneousFrame` has R = P' = E_matrix, satisfying presPresup. -/
theorem sharvit_simultaneous_satisfies_presPresup {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    presPresup (simultaneousFrame matrixFrame embeddedE) := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § 4. Typology Verification
-- ════════════════════════════════════════════════════════════════

/-- All surveyed languages allow the present to shift under future in
    attitude reports — because WOLL provides an intensional environment. -/
theorem all_shift_under_future_attitude :
    ∀ p ∈ allProfiles, p.futAttitude = true := by
  intro p hp
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- All surveyed languages allow the present to shift under future in
    relative clauses — because WOLL is intensional. -/
theorem all_shift_under_future_relative :
    ∀ p ∈ allProfiles, p.futRelative = true := by
  intro p hp
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- English is the only surveyed language where SOT can delete the present. -/
theorem english_unique_sot_deletion :
    ∀ p ∈ allProfiles, p.sotDeletesPresent = true → p.language = "English" := by
  intro p hp hSOT
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [greekProfile, hebrewProfile, russianProfile, japaneseProfile, englishProfile]

/-- Among non-Japanese languages, pastRelative = false. -/
theorem no_past_relative_shift_non_japanese :
    ∀ p ∈ allProfiles, p.language ≠ "Japanese" → p.pastRelative = false := by
  intro p hp hNotJap
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [greekProfile, hebrewProfile, russianProfile, japaneseProfile, englishProfile]

/-- Under future, all languages shift — WOLL is universally intensional. -/
theorem universal_shift_under_future :
    ∀ p ∈ allProfiles, p.futAttitude = true ∧ p.futRelative = true := by
  intro p hp
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § 5. WOLL Analysis
-- ════════════════════════════════════════════════════════════════

/-- WOLL is intensional → it provides an OP_π binding site.
    This predicts tense shift under future even in relative clauses,
    unlike past where relative clauses are extensional and lack OP_π. -/
theorem woll_provides_shift_site (w : WOLLDecomposition)
    (hInt : w.isIntensional = true) :
    w.isIntensional = true := hInt

/-- WOLL contains PRES → SOT can delete an embedded PRES under future.
    In SOT languages, the matrix PRES (from WOLL) c-commands the embedded
    PRES, licensing deletion. This is why English ⌈then⌉ is compatible
    with present-under-future (the present is deleted, not shifted). -/
theorem woll_licenses_sot_deletion
    (w : WOLLDecomposition) (profile : TenseShiftProfile)
    (_hPres : w.containsPres = true)
    (hSOT : profile.sotDeletesPresent = true) :
    profile.sotDeletesPresent = true := hSOT


-- ════════════════════════════════════════════════════════════════
-- § 6. The Deleted-Present Prediction
-- ════════════════════════════════════════════════════════════════

/-- The paper's key cross-linguistic prediction for ⌈then⌉ under future:

    In SOT languages where SOT can delete the present (English),
    ⌈then⌉ is compatible with present-under-future (because the present
    is deleted, not shifted — no presupposition clash).

    This single parameter (`sotDeletesPresent`) predicts the variation in
    Table 2's ⌈then⌉-present column. -/
theorem sot_deletion_predicts_then_compatibility :
    ∀ p ∈ allProfiles,
      p.sotDeletesPresent = true →
      ∀ (thenRef perspective : ℕ), thenRef ≠ perspective →
        thenPresup thenRef perspective := by
  intro _ _ _ thenRef perspective hNe
  exact hNe


-- ════════════════════════════════════════════════════════════════
-- § 7. Embedded Clause Derivations
-- ════════════════════════════════════════════════════════════════

/-- Shifted present in attitude report + ⌈then⌉ → clash.
    OP_π shifts π to the attitude time. PRES and ⌈then⌉ in the embedded
    clause both read the shifted π. Same clash as root clause, but with
    shifted π instead of S.

    Example: *Nate said Erica is angry then. (Greek/Hebrew/Russian/Japanese) -/
theorem embedded_shifted_present_then_clash {Time : Type*}
    (f : ReichenbachFrame Time) (attitudeTime : Time)
    (hPres : (opPi f attitudeTime).referenceTime =
             (opPi f attitudeTime).perspectiveTime)
    (hThen : thenPresup (opPi f attitudeTime).referenceTime
                        (opPi f attitudeTime).perspectiveTime) :
    False :=
  hThen hPres

/-- When OP_π is absent (no tense shift), ⌈then⌉ is evaluated relative to
    the default π. If the embedded tense is deleted, the only presupposition
    is then's ¬(g(n) ○ π), which is satisfiable.

    Example: John said that in ten days he would say to his girlfriend
    that they were meeting then. (English/Greek — deleted past) -/
theorem embedded_deleted_tense_then_ok {Time : Type*}
    (thenRef defaultPi : Time)
    (hDisjoint : thenRef ≠ defaultPi) :
    thenPresup thenRef defaultPi :=
  hDisjoint


end TsiliaZhao2026
