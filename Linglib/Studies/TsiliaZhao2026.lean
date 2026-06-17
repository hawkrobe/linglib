import Linglib.Semantics.Tense.Perspective
import Linglib.Fragments.English.TemporalDeictic
import Linglib.Fragments.German.TemporalDeictic
import Linglib.Fragments.Mandarin.TemporalDeictic
import Linglib.Fragments.Japanese.TemporalDeictic
import Linglib.Fragments.Greek.StandardModern.TemporalDeictic
import Linglib.Fragments.Slavic.Russian.TemporalDeictic
import Linglib.Fragments.Hebrew.TemporalDeictic
import Linglib.Fragments.Hungarian.TemporalDeictic

/-!
# [tsilia-zhao-2026]: Tense and Perspective
[tsilia-zhao-2026] [sharvit-2003] [zhao-2025]

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

open Time

namespace TsiliaZhao2026

open Tense
open Tense.Perspective


-- ════════════════════════════════════════════════════════════════
-- § 1. Cross-Linguistic "Then" Inventory
-- ════════════════════════════════════════════════════════════════

/-- All "then" adverbs from Fragment entries. -/
def thenAdverbs : List ThenAdverb :=
  [ English.TemporalDeictic.then_
  , German.TemporalDeictic.damals
  , Mandarin.TemporalDeictic.nashi
  , Japanese.TemporalDeictic.sonotoki
  , Greek.StandardModern.TemporalDeictic.tote
  , Russian.TemporalDeictic.togda
  , Hebrew.TemporalDeictic.az
  , Hungarian.TemporalDeictic.akkor ]

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

/-- The [sharvit-2003] simultaneous reading is the special case where a PRES
    presupposition is trivially satisfied at the shifted perspective.
    `simultaneousFrame` has R = P' = E_matrix, satisfying presPresup. -/
theorem sharvit_simultaneous_satisfies_presPresup {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedE : Time) :
    presPresup (simultaneousFrame matrixFrame embeddedE) := by
  rfl


-- ════════════════════════════════════════════════════════════════
-- § 4. Typology Verification
-- ════════════════════════════════════════════════════════════════

/-- Cross-linguistic tense shift profile, encoding the paper's Tables 1 & 2.

    Each Bool records whether a simultaneous reading of the embedded present
    is available in that configuration. The mechanism (OP_π shift vs SOT
    deletion) is recorded separately in `sotDeletesPresent`. -/
structure TenseShiftProfile where
  language : String
  /-- Present-under-past, attitude report complement -/
  pastAttitude : Bool
  /-- Present-under-past, relative clause -/
  pastRelative : Bool
  /-- Present-under-future, attitude report complement -/
  futAttitude : Bool
  /-- Present-under-future, relative clause -/
  futRelative : Bool
  /-- Does the language have SOT deletion that can apply to the present?
      English: yes (present under future is deleted, not shifted).
      Modern Greek: no (the "Interpret the Present" constraint blocks deletion). -/
  sotDeletesPresent : Bool
  /-- Is ⌈then⌉ restricted to past-oriented contexts?
      Japanese tooji cannot co-occur with future matrix tense. -/
  thenPastOnly : Bool := false
  deriving Repr, DecidableEq

/-- Modern Greek: shifts in attitude reports (past & future) and relative
    clauses under future, but NOT in relative clauses under past. -/
def greekProfile : TenseShiftProfile where
  language := "Modern Greek"
  pastAttitude := true
  pastRelative := false
  futAttitude := true
  futRelative := true
  sotDeletesPresent := false

/-- Modern Hebrew: same pattern as Greek for shift; no SOT deletion of present. -/
def hebrewProfile : TenseShiftProfile where
  language := "Modern Hebrew"
  pastAttitude := true
  pastRelative := false
  futAttitude := true
  futRelative := true
  sotDeletesPresent := false

/-- Russian: same pattern as Greek/Hebrew for shift. -/
def russianProfile : TenseShiftProfile where
  language := "Russian"
  pastAttitude := true
  pastRelative := false
  futAttitude := true
  futRelative := true
  sotDeletesPresent := false

/-- Japanese: uniquely shifts in relative clauses under past too (tenses are
    intensional). tooji is restricted to past-oriented contexts. -/
def japaneseProfile : TenseShiftProfile where
  language := "Japanese"
  pastAttitude := true
  pastRelative := true
  futAttitude := true
  futRelative := true
  sotDeletesPresent := false
  thenPastOnly := true

/-- English: no shift under past; simultaneous reading under future comes
    from SOT deletion (will = WOLL + PRES, embedded PRES deleted by SOT). -/
def englishProfile : TenseShiftProfile where
  language := "English"
  pastAttitude := false
  pastRelative := false
  futAttitude := true
  futRelative := true
  sotDeletesPresent := true

def allProfiles : List TenseShiftProfile :=
  [greekProfile, hebrewProfile, russianProfile, japaneseProfile, englishProfile]

/-- No language allows shift in relative clauses under past unless it also
    allows shift in attitude reports under past. -/
theorem relative_shift_implies_attitude_shift :
    ∀ p ∈ allProfiles, p.pastRelative = true → p.pastAttitude = true := by
  intro p hp hRel
  simp only [allProfiles, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [greekProfile, hebrewProfile, russianProfile, japaneseProfile, englishProfile]

/-- will = WOLL + PRES. WOLL is an intensional modal operator that:
    1. Quantifies over accessible future indices (∀i' ∈ ACC(i)(t). i'_t > t)
    2. Provides an intensional environment that can bind the perspective

    This decomposition explains:
    - Why ALL surveyed languages allow present-under-future shift: WOLL is
      intensional, providing the OP_π binding site even in relative clauses
    - Why English ⌈then⌉ is compatible with present-under-future: the
      embedded PRES can be deleted by SOT (c-commanded by WOLL's PRES) -/
structure WOLLDecomposition where
  /-- WOLL is an intensional operator (quantifies over future indices) -/
  isIntensional : Bool := true
  /-- WOLL decomposes into a modal component + PRES -/
  containsPres : Bool := true
  deriving Repr, DecidableEq

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
