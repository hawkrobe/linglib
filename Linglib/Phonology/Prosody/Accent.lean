import Linglib.Phonology.Prosody.Syllable

/-!
# Accent assignment

Language-neutral default-accent rules over a syllable-weight profile, plus the
OT NonFinality constraint that penalizes word-final accent. Language-specific
machinery — the Japanese pitch-accent tonal melody and compound accent — lives
with its language in `Fragments/Japanese/Prosody`.

## Main definitions

* `defaultAccentAAR` — the Antepenultimate Accent Rule ([mccawley-1968]):
  accent the syllable holding the antepenultimate mora.
* `latinStressRule` — the Latin Stress Rule ([hayes-1995]): penult if heavy,
  else antepenult. [kubozono-2006] argues it fits Japanese loanword accent.
* `nonFinalitySigma` — the NonFinality(σ) constraint ([prince-smolensky-1993]):
  a violation for accent on the word-final syllable.
-/

namespace Prosody

/-! ### Syllable-from-mora lookup -/

/-- The 0-indexed syllable containing mora `targetMora` (0-indexed), or
    `none` if `targetMora` exceeds the total mora count. -/
private def findSyllable (weights : List Syllable.Weight) (targetMora : Nat) :
    Option Nat :=
  go weights targetMora 0
where
  go : List Syllable.Weight → Nat → Nat → Option Nat
    | [], _, _ => none
    | w :: ws, target, idx =>
      if target < w then some idx
      else go ws (target - w) (idx + 1)

/-! ### Antepenultimate Accent Rule -/

/-- The Antepenultimate Accent Rule ([mccawley-1968]): accent the syllable
    containing the antepenultimate (3rd-from-last) mora. Words with fewer than
    three morae accent the initial syllable. Returns the 0-indexed syllable. -/
def defaultAccentAAR (weights : List Syllable.Weight) : Option Nat :=
  match weights with
  | [] => none
  | _ =>
    let totalMorae := weights.foldl (· + ·) 0
    let targetMora := if totalMorae ≥ 3 then totalMorae - 3 else 0
    findSyllable weights targetMora

/-! ### Latin Stress Rule -/

/-- The Latin Stress Rule ([hayes-1995]): accent the penult if it is heavy
    (≥ 2μ), otherwise the antepenult. Monosyllables accent the only syllable;
    disyllables accent the penult (= initial). [kubozono-2006] argues this
    rule fits Japanese default accentuation better than `defaultAccentAAR`. -/
def latinStressRule : List Syllable.Weight → Option Nat
  | [] => none
  | [_] => some 0
  | [_, _] => some 0                    -- disyllable → always penult (= initial)
  | [_, 0, _] | [_, 1, _] => some 0      -- light penult → antepenult
  | [_, _, _] => some 1                 -- heavy+ penult → penult
  | _ :: rest@(_ :: _ :: _) =>           -- peel front, recurse, add 1
    (latinStressRule rest).map (· + 1)

/-! ### NonFinality -/

/-- NonFinality(σ) ([prince-smolensky-1993]): `1` if accent is on the
    word-final syllable, else `0`. Drives the avoidance of final accent in
    Japanese compound formation and loanword adaptation ([kawahara-2015]). -/
def nonFinalitySigma (accentSyll : Option Nat) (nSyll : Nat) : Nat :=
  match accentSyll with
  | some pos => if pos + 1 == nSyll then 1 else 0
  | none => 0

end Prosody
