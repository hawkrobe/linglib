import Linglib.Theories.Semantics.Tense.Kratzer

/-!
# German Tense Fragment (Kratzer 1998)

German tense paradigm entries following Kratzer's (1998) decomposition.
The key contrast with English: German Preterit is a genuine PAST pronoun
(anaphoric — requires discourse antecedent), while English "simple past"
has a covert PRESENT tense head.

## The Preterit Restriction

Modern German Preterit (Präteritum) cannot be used "out of the blue"
in most dialects; it requires a narrative context supplying a temporal
antecedent. This follows from the tense head being PAST (anaphoric).

  #"Ich schaltete den Herd nicht aus." (out of the blue — marginal)
  "Ich habe den Herd nicht ausgeschaltet." (present perfect — fine)

The present perfect (Perfekt) has replaced the Preterit in spoken German
for out-of-the-blue past reference, matching the prediction: Perfekt
has a PRESENT tense head (indexical-compatible).

## References

- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
  *SALT VIII*, 92-110.
-/

namespace Fragments.German.Tense

open Core.Tense
open Semantics.Tense.Kratzer

-- ════════════════════════════════════════════════════
-- § 1. Kratzer Decomposition Entries
-- ════════════════════════════════════════════════════

/-- German Preterit (Präteritum): genuine PAST pronoun.
    Anaphoric — requires a discourse-established temporal antecedent.
    No PERF aspect head intervenes; the pastness is in the tense itself. -/
def kratzerPreterit : KratzerDecomposition where
  language := "German"
  surfaceForm := "V-te"
  tensePronoun := kratzerGermanPreterit 1
  hasPerfect := false

/-- German Perfekt (present perfect): PRESENT tense + PERFECT aspect.
    Parallel structure to English simple past. Can be used deictically
    because the tense head is present (indexical). -/
def kratzerPerfekt : KratzerDecomposition where
  language := "German"
  surfaceForm := "hat/ist V-t"
  tensePronoun := { varIndex := 0, constraint := .present, mode := .indexical }
  hasPerfect := true

-- ════════════════════════════════════════════════════
-- § 2. Verification
-- ════════════════════════════════════════════════════

/-- German Preterit cannot be deictic. -/
theorem preterit_not_deictic :
    kratzerPreterit.canBeDeictic = false := rfl

/-- German Perfekt CAN be deictic. -/
theorem perfekt_deictic :
    kratzerPerfekt.canBeDeictic = true := rfl

/-- The Preterit–Perfekt contrast: different underlying tense heads.
    Preterit has a PAST head (anaphoric); Perfekt has PRESENT + PERF (indexical).
    Both can refer to past events, but only Perfekt is deictic-compatible.
    This explains why Perfekt has largely replaced Preterit in spoken German. -/
theorem preterit_perfekt_contrast :
    kratzerPreterit.tensePronoun.constraint = GramTense.past ∧
    kratzerPerfekt.tensePronoun.constraint = GramTense.present ∧
    kratzerPreterit.canBeDeictic = false ∧
    kratzerPerfekt.canBeDeictic = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- German Preterit is always overt (anaphoric = free). -/
theorem preterit_always_overt (localDomain : Bool) :
    kratzerPreterit.tenseOvertness localDomain = .overt := by
  cases localDomain <;> rfl

/-- German Perfekt tense head is always overt (indexical = free). -/
theorem perfekt_always_overt (localDomain : Bool) :
    kratzerPerfekt.tenseOvertness localDomain = .overt := by
  cases localDomain <;> rfl

end Fragments.German.Tense
